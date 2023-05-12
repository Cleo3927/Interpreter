import System.Environment ( getArgs )
import System.Exit        ( exitFailure, exitSuccess )
import Control.Monad      ( when )

import Grammar.Abs   (Prog)
import Grammar.Lex   ( Token, mkPosToken )
import Grammar.Par   ( pProg, myLexer )
import Grammar.Print ( Print, printTree )
import Grammar.Skel  ()
import Eval as E

type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: ParseFun Prog -> FilePath -> IO ()
runFile p f = putStrLn f >> readFile f >>= run p

run :: ParseFun Prog -> String -> IO ()
run p s =
  case p ts of
    Left err -> do
      putStrLn "\nParse              Failed...\n"
      putStrLn err
      exitFailure
    Right tree -> do
      E.runEvalProgram tree
      exitSuccess
	--   case res of
        -- Right Empty     -> exitSuccess
        -- Right (Intgr x) -> if x /= 0 then exitWith (ExitFailure (fromInteger x)) else exitSuccess
        -- Left msg        -> do
    	--   hPutStrLn stderr ("Error: " ++ msg)
        -- --   exitFailure
        -- _ -> exitFailure
  where
	ts = myLexer s
	showPosToken ((l,c),t) = concat [ show l, ":", show c, "\t", show t ]

showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree = do
  putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

usage :: IO ()
usage = do
  putStrLn $ unlines
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
    []         -> getContents >>= run pProg
    "-s":fs    -> mapM_ (runFile pProg) fs
    fs         -> mapM_ (runFile pProg) fs

