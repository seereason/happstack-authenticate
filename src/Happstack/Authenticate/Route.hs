{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
module Happstack.Authenticate.Route where

import Control.Applicative ((<$>))
import Control.Concurrent.STM (atomically)
import Control.Concurrent.STM.TVar (TVar, newTVar, readTVar)
import Control.Monad.Trans (MonadIO(liftIO))
import Data.Acid (AcidState, update)
import Data.Acid.Local (openLocalStateFrom, createCheckpointAndClose)
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Lazy as LBS
import Data.Digest.Pure.SHA (sha256, showDigest)
import qualified Data.Map as Map (fromList, lookup)
import Data.Maybe (fromMaybe, Maybe(..))
import Data.Monoid (mconcat)
import Data.Traversable (sequence)
import Data.Unique (hashUnique, newUnique)
import Data.UserId (UserId)
import HSP.JMacro (IntegerSupply(..))
import Happstack.Authenticate.Core
import Happstack.Authenticate.Handlers
import Happstack.Server (getHeaderM, internalServerError, notFound, ok, method, resp, setHeaderM, toResponseBS, Method(POST), Response, ServerPartT, ToMessage(toResponse))
import Happstack.Server.JMacro ()
import Control.Monad                (MonadPlus)
import Happstack.Server             (ServerMonad(askRq), FilterMonad, rqInputsQuery)
import System.FilePath              (takeDirectory, (</>))
import Language.Javascript.JMacro (JStat)
import Prelude (($), (.), Bool(True), FilePath, fromIntegral, Functor(..), Integral(mod), IO, map, mapM, Monad(return), sequence_, unzip3)
import Prelude hiding (sequence)
import System.FilePath (combine)
import Web.Routes (RouteT)

------------------------------------------------------------------------------
-- route
------------------------------------------------------------------------------


-- | Serve a client script, or -- when the URL has a @wasm@ query
-- parameter, as the wasm build's all.js uses to fetch its program -- the
-- @all.wasm@ next to it. Both are served through 'serveClientFile' so
-- they get the same content-hash ETag caching.
serveClientScript :: String -> FilePath -> RouteT AuthenticateURL (ServerPartT IO) Response
serveClientScript contentType p =
  do rq <- askRq
     case lookup "wasm" (rqInputsQuery rq) of
       Just _  -> serveClientFile "application/wasm" (takeDirectory p </> "all.wasm")
       Nothing -> serveClientFile contentType p

route :: AuthenticationHandlers
      -> AcidState AuthenticateState
      -> TVar AuthenticateConfig
      -> AuthenticateURL
      -> RouteT AuthenticateURL (ServerPartT IO) Response
route authenticationHandlers authenticateState authenticateConfigTV url =
  do case url of
       (AuthenticationMethods (Just (authenticationMethod, pathInfo))) ->
         case Map.lookup authenticationMethod authenticationHandlers of
           (Just handler) -> handler pathInfo
           Nothing        -> notFound $ toJSONError (HandlerNotFound {- authenticationMethod-} ) --FIXME
       (AuthenticationMethods Nothing) -> notFound $ toJSONError HandlerNotFound
       HappstackAuthenticateClient ->
         do ac <- liftIO $ atomically $ readTVar authenticateConfigTV
            case _happstackAuthenticateClientPath ac of
              Nothing -> internalServerError $ toResponse "path to happstack-authenticate-client not configured"
              (Just p) -> serveClientScript "text/javascript" p
       Logout ->
         do method [POST]
            deleteTokenCookie
            ok $ toResponse ()
       AmAuthenticated ->
         do amAuthenticated authenticateState
       InitClient ->
         do ac <- liftIO $ atomically $ readTVar authenticateConfigTV
            clientInit ac authenticateState

-- | Serve the happstack-authenticate-client javascript file.
--
-- We can not rely on the file's modification time to detect changes
-- (as 'Happstack.Server.FileServe.serveFile' does) because on
-- systems like NixOS the file lives in the immutable,
-- content-addressed \/nix\/store, where every file's mtime is reset
-- to a fixed value. Two different versions of the file can
-- therefore have identical mtimes, so an mtime-based check -- and
-- the heuristic freshness a browser applies when no explicit
-- caching header is present -- can make a client believe a stale
-- copy is still current. Instead we hash the file contents into an
-- @ETag@ and mark the response @no-cache@, so clients always
-- revalidate with the server, which can cheaply answer 304 when the
-- hash still matches and a fresh body when it does not.
serveClientFile :: String -> FilePath -> RouteT AuthenticateURL (ServerPartT IO) Response
serveClientFile contentType p =
  do content <- liftIO $ LBS.readFile p
     let etag = B.pack ("\"" ++ clientFileHash content ++ "\"")
     setHeaderM "Cache-Control" "no-cache"
     setHeaderM "ETag" (B.unpack etag)
     mINM <- getHeaderM "if-none-match"
     if mINM == Just etag
       then resp 304 (toResponse ())
       else ok $ toResponseBS (B.pack contentType) content

clientFileHash :: LBS.ByteString -> String
clientFileHash content = showDigest (sha256 content)

-- | Compute a content hash for the currently configured
-- happstack-authenticate-client javascript file (see
-- '_happstackAuthenticateClientPath' and 'serveClientFile').
--
-- Applications that embed a @\<script\>@ tag or otherwise construct
-- the URL used to fetch 'HappstackAuthenticateClient' can pass this
-- hash along as a query parameter (e.g. @?etag=\<hash\>@). Because a
-- browser that already cached an old, incorrectly-cached copy of the
-- file has no reason to revalidate it with the server on its own
-- (see 'serveClientFile''s Haddock for why the old mtime-based
-- caching could leave it fresh for a very long time), the only
-- reliable way to make such a client fetch the current version is to
-- change the URL it requests. Returns 'Nothing' if no path is
-- configured.
happstackAuthenticateClientHash :: AuthenticateConfig -> IO (Maybe String)
happstackAuthenticateClientHash ac =
  case _happstackAuthenticateClientPath ac of
    Nothing -> return Nothing
    (Just p) -> Just . clientFileHash <$> LBS.readFile p

------------------------------------------------------------------------------
-- initAuthenticate
------------------------------------------------------------------------------

initAuthentication
  :: Maybe FilePath
  -> AuthenticateConfig
  -> [FilePath -> AcidState AuthenticateState -> TVar AuthenticateConfig -> IO (Bool -> IO (), (AuthenticationMethod, AuthenticationHandler)) ]
  -> IO (IO (), AuthenticateURL -> RouteT AuthenticateURL (ServerPartT IO) Response, AcidState AuthenticateState, TVar AuthenticateConfig)
initAuthentication mBasePath authenticateConfig initMethods =
  do let authenticatePath = combine (fromMaybe "state" mBasePath) "authenticate"
     authenticateState <- openLocalStateFrom (combine authenticatePath "core") initialAuthenticateState
     _ <- update authenticateState TrimUsernames
     authenticateConfigTV <- atomically $ newTVar authenticateConfig
     -- FIXME: need to deal with one of the initMethods throwing an exception
     (cleanupPartial, handlers) <- unzip <$> mapM (\initMethod -> initMethod authenticatePath authenticateState authenticateConfigTV) initMethods
     let cleanup = sequence_ $ createCheckpointAndClose authenticateState : (map (\c -> c True) cleanupPartial)
         h       = route (Map.fromList handlers) authenticateState authenticateConfigTV
     return (cleanup, h, authenticateState, authenticateConfigTV)

instance (Functor m, MonadIO m) => IntegerSupply (RouteT AuthenticateURL m) where
 nextInteger =
  fmap (fromIntegral . (`mod` 1024) . hashUnique) (liftIO newUnique)
