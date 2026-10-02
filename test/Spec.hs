{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Test suite for the username-whitespace migration and related username
-- validation.
--
-- Covers four layers:
--
--  1. 'usernamePolicy' rejects leading\/trailing whitespace in new usernames.
--
--  2. 'createUser' (exposed via the 'CreateUser' acid-state event) rejects
--     usernames that are confusingly similar to an existing username --
--     differing only in letter case, or substituting look-alike characters
--     from another script (see 'usernamesSimilar').
--
--  3. 'trimUsernames' (exposed via the 'TrimUsernames' acid-state event)
--     trims existing padded usernames, leaves clean ones alone, and safely
--     skips any trim that would collide with another user's username --
--     tested against an in-memory 'AcidState'.
--
--  4. The migration is actually wired up: it runs against real on-disk
--     acid-state data (simulating a server restart), and 'initAuthentication'
--     triggers it automatically on startup.
module Main (main) where

import Control.Exception (SomeException, catch, finally, try)
import Control.Lens ((^.))
import Control.Monad (unless)
import Data.Acid (query, update)
import Data.Maybe (isNothing)
import Data.Acid.Local (createCheckpointAndClose, openLocalStateFrom)
import Data.Acid.Memory (openMemoryState)
import qualified Data.Set as Set
import Data.Unique (hashUnique, newUnique)
import Data.UserId (UserId(..))
import System.Directory (getTemporaryDirectory, removeDirectoryRecursive)
import System.Exit (exitFailure)
import System.FilePath ((</>))

import Happstack.Authenticate.Core
  ( CoreError(..)
  , User(..)
  , Username(..)
  , UsernameProblem(..)
  , userId
  , username
  )
import Happstack.Authenticate.Handlers
  ( AuthenticateConfig(..)
  , CreateUser(..)
  , GetUserByUsername(..)
  , GetUsers(..)
  , TrimUsernames(..)
  , initialAuthenticateState
  , usernamePolicy
  )
import Happstack.Authenticate.Route (initAuthentication)

------------------------------------------------------------------------------
-- a tiny assertion/test-runner, so the suite has no extra test-framework
-- dependency beyond what the library already needs
------------------------------------------------------------------------------

type Check = Either String ()

pass :: Check
pass = Right ()

failure :: String -> Check
failure = Left

assertEqual :: (Eq a, Show a) => String -> a -> a -> Check
assertEqual label expected actual
  | expected == actual = pass
  | otherwise = failure (label ++ ": expected " ++ show expected ++ ", got " ++ show actual)

runCase :: String -> IO Check -> IO Bool
runCase name action =
  do outcome <- (try action :: IO (Either SomeException Check))
     let result = either (\e -> failure ("threw exception: " ++ show e)) id outcome
     case result of
       Right () -> putStrLn ("OK   " ++ name) >> return True
       Left  msg -> putStrLn ("FAIL " ++ name ++ " -- " ++ msg) >> return False

------------------------------------------------------------------------------
-- helpers
------------------------------------------------------------------------------

mkUser :: Username -> User
mkUser name = User (UserId 0) name Nothing

-- | a fresh, never-before-used directory to hold on-disk acid-state data
freshTempDir :: IO FilePath
freshTempDir =
  do tmp <- getTemporaryDirectory
     u   <- newUnique
     return (tmp </> ("happstack-authenticate-test-" ++ show (hashUnique u)))

cleanupDir :: FilePath -> IO ()
cleanupDir dir = removeDirectoryRecursive dir `catch` \(_ :: SomeException) -> return ()

testConfig :: AuthenticateConfig
testConfig = AuthenticateConfig
  { _isAuthAdmin                     = const (return False)
  , _usernameAcceptable              = usernamePolicy
  , _requireEmail                    = False
  , _systemFromAddress               = Nothing
  , _systemReplyToAddress            = Nothing
  , _systemSendmailPath              = Nothing
  , _postLoginRedirect               = Nothing
  , _postSignupRedirect              = Nothing
  , _createUserCallback              = Nothing
  , _happstackAuthenticateClientPath = Nothing
  }

------------------------------------------------------------------------------
-- usernamePolicy
------------------------------------------------------------------------------

usernamePolicyCases :: [(String, Username, Bool)] -- (label, candidate, isAcceptable)
usernamePolicyCases =
  [ ("empty username is rejected",             Username "",          False)
  , ("leading space is rejected",              Username " bob",      False)
  , ("trailing space is rejected",             Username "bob ",      False)
  , ("leading and trailing space is rejected", Username "  bob  ",   False)
  , ("leading/trailing tab is rejected",       Username "\tbob\t",   False)
  , ("plain username is accepted",             Username "bob",       True)
  , ("internal whitespace is accepted",        Username "bob smith", True)
  ]

testUsernamePolicyCases :: [(String, IO Check)]
testUsernamePolicyCases =
  [ ( "usernamePolicy: " ++ label
    , return (assertEqual label acceptable (isNothing (usernamePolicy candidate)))
    )
  | (label, candidate, acceptable) <- usernamePolicyCases
  ]

------------------------------------------------------------------------------
-- createUser: rejects usernames too similar to an existing username
------------------------------------------------------------------------------

testCreateUserCollisionCases :: [(String, Username, Bool)] -- (label, existing, secondUsername, isAcceptable)
testCreateUserCollisionCases =
  [ ("different case is rejected",                   Username "Bob",     False)
  , ("Greek look-alike is rejected",                  Username "\x0392\&ob", False) -- Greek capital Beta + "ob"
  , ("fullwidth look-alike is rejected",               Username "\xFF42\&ob", False) -- fullwidth 'b' + "ob"
  , ("unrelated username is accepted",                Username "carol",   True)
  ]

testCreateUserCollisions :: [(String, IO Check)]
testCreateUserCollisions =
  [ ( "createUser: " ++ label
    , do st <- openMemoryState initialAuthenticateState
         _  <- update st (CreateUser (mkUser (Username "bob")))
         eu <- update st (CreateUser (mkUser candidate))
         return $ case (acceptable, eu) of
           (True,  Right _)                                           -> pass
           (False, Left (UsernameNotAcceptable UsernameTooSimilarToExisting)) -> pass
           _ -> failure (label ++ ": got " ++ show eu)
    )
  | (label, candidate, acceptable) <- testCreateUserCollisionCases
  ]

------------------------------------------------------------------------------
-- TrimUsernames, against an in-memory AcidState
------------------------------------------------------------------------------

testTrimSingleUser :: IO Check
testTrimSingleUser =
  do st <- openMemoryState initialAuthenticateState
     eu <- update st (CreateUser (mkUser (Username "  alice  ")))
     case eu of
       Left e -> return (failure ("could not create user: " ++ show e))
       Right seeded ->
         do trimmedIds <- update st TrimUsernames
            mByTrimmed <- query st (GetUserByUsername (Username "alice"))
            mByPadded  <- query st (GetUserByUsername (Username "  alice  "))
            return $ do
              assertEqual "returns the id of the trimmed user" [seeded ^. userId] trimmedIds
              case mByTrimmed of
                Nothing -> failure "logging in with the trimmed username should find the user"
                Just u  -> assertEqual "stored username is now trimmed" (Username "alice") (u ^. username)
              case mByPadded of
                Nothing -> failure "logging in with the old padded username should still find the user"
                Just u  -> assertEqual "padded login resolves to the same user" (seeded ^. userId) (u ^. userId)

testCleanUsernameIsUnaffected :: IO Check
testCleanUsernameIsUnaffected =
  do st <- openMemoryState initialAuthenticateState
     eu <- update st (CreateUser (mkUser (Username "carol")))
     case eu of
       Left e -> return (failure ("could not create user: " ++ show e))
       Right seeded ->
         do trimmedIds <- update st TrimUsernames
            mByPadded <- query st (GetUserByUsername (Username "  carol  "))
            return $ do
              assertEqual "an already-clean username is not reported as trimmed" [] trimmedIds
              case mByPadded of
                Nothing -> failure "whitespace-padded login should still find a clean username"
                Just u  -> assertEqual "padded login resolves to the right user" (seeded ^. userId) (u ^. userId)

testInternalWhitespaceIsUnaffected :: IO Check
testInternalWhitespaceIsUnaffected =
  do st <- openMemoryState initialAuthenticateState
     eu <- update st (CreateUser (mkUser (Username "bob smith")))
     case eu of
       Left e -> return (failure ("could not create user: " ++ show e))
       Right _ ->
         do trimmedIds <- update st TrimUsernames
            mu <- query st (GetUserByUsername (Username "bob smith"))
            return $ do
              assertEqual "internal whitespace is not trimmed" [] trimmedIds
              case mu of
                Nothing -> failure "username with internal whitespace should still be found"
                Just u  -> assertEqual "username text is unchanged" (Username "bob smith") (u ^. username)

testCollidingTrimIsSkipped :: IO Check
testCollidingTrimIsSkipped =
  do st <- openMemoryState initialAuthenticateState
     r1 <- update st (CreateUser (mkUser (Username "dave")))
     r2 <- update st (CreateUser (mkUser (Username "  dave  ")))
     case (r1, r2) of
       (Right clean, Right padded) ->
         do trimmedIds <- update st TrimUsernames
            mClean     <- query st (GetUserByUsername (Username "dave"))
            mPadded    <- query st (GetUserByUsername (Username "  dave  "))
            allUsers   <- query st GetUsers
            return $ do
              assertEqual "a trim that would collide is skipped" [] trimmedIds
              assertEqual "both accounts still exist" 2 (Set.size allUsers)
              case mClean of
                Nothing -> failure "the clean username should still resolve"
                Just u  -> assertEqual "exact match for the clean username" (clean ^. userId) (u ^. userId)
              case mPadded of
                Nothing -> failure "the still-padded username should still resolve by exact match"
                Just u  -> assertEqual "exact match for the padded username" (padded ^. userId) (u ^. userId)
       _ -> return (failure "could not seed both users for the collision test")

testTrimIsIdempotent :: IO Check
testTrimIsIdempotent =
  do st <- openMemoryState initialAuthenticateState
     _  <- update st (CreateUser (mkUser (Username "  gina  ")))
     _  <- update st TrimUsernames
     secondRun <- update st TrimUsernames
     return (assertEqual "running the migration again finds nothing left to trim" [] secondRun)

------------------------------------------------------------------------------
-- migration against real on-disk acid-state data (server-restart simulation)
------------------------------------------------------------------------------

testDiskRoundTrip :: IO Check
testDiskRoundTrip =
  do dir <- freshTempDir
     let statePath = dir </> "authenticate" </> "core"
     (do st1 <- openLocalStateFrom statePath initialAuthenticateState
         eu  <- update st1 (CreateUser (mkUser (Username "  erin  ")))
         createCheckpointAndClose st1
         case eu of
           Left e -> return (failure ("could not seed user: " ++ show e))
           Right seeded ->
             do st2 <- openLocalStateFrom statePath initialAuthenticateState
                trimmedIds <- update st2 TrimUsernames
                mu <- query st2 (GetUserByUsername (Username "erin"))
                createCheckpointAndClose st2
                return $ do
                  assertEqual "restart-time migration trims the persisted username" [seeded ^. userId] trimmedIds
                  case mu of
                    Nothing -> failure "trimmed username not found after reopening from disk"
                    Just u  -> assertEqual "persisted username is trimmed" (Username "erin") (u ^. username)
       ) `finally` cleanupDir dir

testInitAuthenticationMigratesOnStartup :: IO Check
testInitAuthenticationMigratesOnStartup =
  do dir <- freshTempDir
     let statePath = dir </> "authenticate" </> "core"
     (do st0 <- openLocalStateFrom statePath initialAuthenticateState
         eu  <- update st0 (CreateUser (mkUser (Username "  frank  ")))
         createCheckpointAndClose st0
         case eu of
           Left e -> return (failure ("could not seed user: " ++ show e))
           Right _ ->
             do (cleanup, _route, authenticateState, _cfgTV) <- initAuthentication (Just dir) testConfig []
                mu <- query authenticateState (GetUserByUsername (Username "frank"))
                cleanup
                return $
                  case mu of
                    Nothing -> failure "initAuthentication did not migrate the padded username on startup"
                    Just u  -> assertEqual "startup migration trims the persisted username" (Username "frank") (u ^. username)
       ) `finally` cleanupDir dir

------------------------------------------------------------------------------
-- main
------------------------------------------------------------------------------

main :: IO ()
main =
  do let cases =
           testUsernamePolicyCases ++
           testCreateUserCollisions ++
           [ ("TrimUsernames: trims a single padded username, still reachable via padded or trimmed login", testTrimSingleUser)
           , ("TrimUsernames: leaves an already-clean username untouched", testCleanUsernameIsUnaffected)
           , ("TrimUsernames: leaves internal whitespace untouched", testInternalWhitespaceIsUnaffected)
           , ("TrimUsernames: skips a trim that would collide, keeping both accounts reachable", testCollidingTrimIsSkipped)
           , ("TrimUsernames: is idempotent", testTrimIsIdempotent)
           , ("disk round-trip: migration fixes a username persisted before validation existed", testDiskRoundTrip)
           , ("initAuthentication: runs the username migration automatically on startup", testInitAuthenticationMigratesOnStartup)
           ]
     results <- mapM (uncurry runCase) cases
     unless (and results) exitFailure
