import System.Environment ( getArgs )
import System.Exit        ( exitFailure, exitSuccess )
import Control.Monad      ( when )

import Grammar.Abs   (Prog)
import Grammar.Lex   ( Token, mkPosToken )
import Grammar.Par   ( pProg, myLexer )
import Grammar.Print ( Print, printTree )
import Grammar.Skel  ()
import Eval as E ( Value(Empt), runEvalProgram )
import Checker as C ( runCheckProgram ) 
import System.IO (stderr, hPutStrLn)
import qualified Eval as C
import Checker

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
    Right (E.Empt, _) -> exitSuccess
    Right (_, _) -> do
      hPutStrLn stderr "Main couldn't return a value"
      exitFailure
    Left msg -> do
      hPutStrLn stderr msg
      exitFailure

runCheck :: Prog -> IO ()
runCheck tree = do 
  res <- C.runCheckProgram tree 
  case res of
    Left msg -> do
      hPutStrLn stderr ("Typechecker: " ++ msg)
      exitFailure
    Right EEmpty -> pure ()
    Right (EBreak pos) -> do
      hPutStrLn stderr ("Typechecker: Break may not be used outside of a loop" ++ printErr pos)
      exitFailure
    Right (EContinue pos) -> do
      hPutStrLn stderr ("Typechecker: Continue may not be used outside of a loop" ++ printErr pos)
      exitFailure
    Right _ -> do 
      hPutStrLn stderr "Typechecker: Main couldn't return a value"
      exitFailure

run :: ParseFun Prog -> String -> IO ()
run p s =
  case p ts of
    Left err -> do
      hPutStrLn stderr err 
      exitFailure
    Right tree -> do 
      runCheck tree
      runProg tree
  where
    ts = myLexer s

usage :: IO ()
usage = do
  Prelude.putStrLn $ Prelude.unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (file)         Parse content of file verbosely."
    ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    []         -> Prelude.getContents >>= run pProg
    fs         -> mapM_ (runFile pProg) fs

