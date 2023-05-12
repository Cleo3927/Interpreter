import System.Environment ( getArgs )
import System.Exit        ( exitFailure, exitSuccess )
import Control.Monad      ( when )

import Grammar.Abs   (Prog)
import Grammar.Lex   ( Token, mkPosToken )
import Grammar.Par   ( pProg, myLexer )
import Grammar.Print ( Print, printTree )
import Grammar.Skel  ()
import Eval as E
import GHC.IO.FD (stderr)
import Data.ByteString.Char8

type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ Prelude.putStrLn s

runFile :: ParseFun Prog -> FilePath -> IO ()
runFile p f = Prelude.putStrLn f >> Prelude.readFile f >>= run p

runProg :: Prog -> IO ()
runProg tree = do
  res <- E.runEvalProgram tree
  case res of
    Right (Empt, _) -> exitSuccess
    Left msg -> do
      Prelude.putStrLn msg
      exitFailure
        -- _ -> exitFailure

run :: ParseFun Prog -> String -> IO ()
run p s =
  case p ts of
    Left err -> do
      Prelude.putStrLn "\nParse              Failed...\n"
      Prelude.putStrLn err
      exitFailure
    Right tree -> do
      runProg tree
  where
    ts = myLexer s

showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree = do
  putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

usage :: IO ()
usage = do
  Prelude.putStrLn $ Prelude.unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    []         -> Prelude.getContents >>= run pProg
    "-s":fs    -> mapM_ (runFile pProg) fs
    fs         -> mapM_ (runFile pProg) fs

