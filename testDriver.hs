{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
import Shelly
import Data.Text.Lazy as LT
import Control.Monad
import Control.Exception.Base
default (LT.Text)

getTestFiles :: ShIO [Text]
getTestFiles = ls "./tests" >>= filterM test_d >>= mapM lsT >>= return . join

main = shelly $ escaping False $ print_stdout False $ do
   test_files <- getTestFiles
   out_files <- filterFiles ".core.out" test_files
   err_files <- filterFiles ".core.err" test_files
   removePrevious $ Prelude.map fromText (out_files ++ err_files)
   tests <- filterFiles ".core" test_files
   doTests tests
   displayErrors

removePrevious :: [Shelly.FilePath] -> ShIO [()]
removePrevious files = mapM rm_f files

doTests :: [Text] -> ShIO ()
doTests [] = return ()
doTests (test:tests) =
   do testresult <- catch_sh (run "./Core" [test]) error_handler
      err <- lastStderr
      if   LT.null err
      then writefile (output_file test ".out") testresult
      else writefile (output_file test ".err") err
      doTests tests
   where
   error_handler :: SomeException -> ShIO Text
   error_handler = return . pack . show
   output_file f ext = fromText $ f `append` ext

displayErrors :: ShIO ()
displayErrors = do
   test_files <- getTestFiles
   errors <- filterFiles ".err" test_files
   unless (Prelude.null errors) $ do echo "Errors:"
                                     echo $ LT.unlines errors

filterFiles :: Text -> [Text] -> ShIO [Text]
filterFiles ext files = return $ Prelude.filter (endswith ext) files

endswith :: Text -> Text -> Bool
endswith pattern search = endswith' (LT.reverse pattern) (LT.reverse search)
endswith' pat ss
   | LT.null pat = True
   | LT.head pat /= LT.head ss = False
   | otherwise = endswith' (LT.tail pat) (LT.tail ss)
