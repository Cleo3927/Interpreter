{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Eval where

import qualified Prelude as C
import Grammar.Abs
import Grammar.Print
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import Data.Maybe(fromMaybe)
import qualified Data.Word
import Distribution.PackageDescription (GenericPackageDescription(condBenchmarks))
import System.Process (CreateProcess(env))
import Distribution.Simple.Utils (xargs)
import Distribution.Compat.ResponseFile (expandResponse)
import Prelude

data Value = Intgr Integer | Strln String | Bl Bool | Empt | Func TopDef
data BlokValue = EReturn Value | EBreak BNFC'Position | EContinue BNFC'Position | EEmpty

type Location = Int
type Env = M.Map Ident Location -- nazwa, lokacja
type Store = M.Map Location Value -- lokacja, wartość
type RSE a = ReaderT Env (StateT Store (ExceptT String IO)) a

takeName :: [Char] -> Type' a -> Ident -> Ident
takeName prefix typ name =
    case (typ, name) of
        (Int _, Ident s) -> Ident (prefix ++ "$" ++ s)
        (Bool _, Ident s) -> Ident (prefix ++ "'" ++ s)
        (Str _, Ident s) -> Ident (prefix ++ "#" ++ s)
        (Void _, Ident s) -> Ident (prefix ++ "@" ++ s)

evalMaybe :: String -> Maybe a -> RSE a
evalMaybe s Nothing = throwError s
evalMaybe s (Just a) = return a

evalExpr :: Expr -> RSE Value

printErr :: BNFC'Position -> String
printErr Nothing = ""
printErr (Just (line, col)) = " in line " ++ show line

setupArgs :: BNFC'Position -> [Arg] -> [Expr] -> Env -> RSE Env
setupArgs pos (a:args) (e:exprs) env = do
  case a of
    Argcopy _ typ name -> do
        v <- evalExpr e
        loc <- alloc
        modify (M.insert loc v)
        setupArgs pos args exprs (M.insert (takeName "" typ name) loc env)
    Argref _ typ nameArg -> do
        case e of
            EVar pos typ nameExpr -> do
                loc <- evalMaybe ("Variable doesn't exists" ++ printErr pos) (M.lookup (takeName "" typ nameExpr) env)
                setupArgs pos args exprs (M.insert (takeName "" typ nameArg) loc env)
            _ -> throwError ("Argument is not a reference" ++ printErr pos)
setupArgs pos (n:no) _ _ = do throwError ("Not enough arguments" ++ printErr pos)
setupArgs pos _ (e:eo) _ = do throwError ("Too many arguments" ++ printErr pos)
setupArgs _ _ _ env = do return env

unpackFunction :: TopDef -> ([Arg], [Stmt])
unpackFunction (FnDef pos typ name argsFn (Block _ blok)) = (argsFn, blok)

evalExpr (EVar pos typ name) = do
    env <- ask
    s   <- get
    loc <- evalMaybe ("Undefined variable" ++ printErr pos) (M.lookup (takeName "" typ name) env)
    evalMaybe ("Undefined variable" ++ printErr pos) (M.lookup loc s)
evalExpr (ELitInt _ n) = return (Intgr n)
evalExpr (ELitTrue _) = return (Bl True)
evalExpr (ELitFalse _) = return (Bl False)
evalExpr (EApp pos typ name args) = do
    env <- ask
    s   <- get
    loc <- evalMaybe ("Undefined function" ++ printErr pos) (M.lookup (takeName "Fun" typ name) env)
    fn  <- evalMaybe ("Undefined function" ++ printErr pos) (M.lookup loc s)
    case fn of
        Func x ->
            let (argsFn, blok) = unpackFunction x in
                do
                nenv <- setupArgs pos argsFn args env
                local (const nenv) (evalStmtFun blok)
        _ -> throwError ("Not a function" ++ printErr pos)

evalExpr (EString _ str) = return (Strln str)
evalExpr (Neg pos subexpr) = do
    val <- evalExpr subexpr
    case val of
        Intgr num -> return (Intgr (num * (-1)))
evalExpr (Not pos subexpr) = do
    val <- evalExpr subexpr
    case val of
         Bl num -> return (Bl (not num))
evalExpr (EMul pos expr1 mulop expr2) = do
    e1 <- evalExpr expr1
    e2 <- evalExpr expr2
    case (e1, e2, mulop) of
        (Intgr n1, Intgr n2, Times _) -> return (Intgr $ n1 * n2)
        (Intgr n1, Intgr n2, Div _) -> if n2 /= 0 then return (Intgr (div n1 n2)) else throwError ("Divide by 0" ++ printErr pos)
        (Intgr n1, Intgr n2, Mod _) -> if n2 /= 0 then return (Intgr $ mod n1 n2) else throwError ("Modulo 0" ++ printErr pos)
evalExpr (EAdd pos expr1 addop expr2) = do
    e1 <- evalExpr expr1
    e2 <- evalExpr expr2
    case (e1, e2, addop) of
        (Intgr n1, Intgr n2, Plus _) -> return (Intgr $ n1 + n2)
        (Intgr n1, Intgr n2, Minus _) -> return (Intgr $ n1 - n2)
        (Strln n1, Strln n2, Plus _) -> return (Strln $ n1 ++ n2)

evalExpr (ERel pos expr1 relop expr2) = do
    e1 <- evalExpr expr1
    e2 <- evalExpr expr2
    case (e1, e2, relop) of
        (Intgr n1, Intgr n2, LTH _) -> return (Bl $ n1 < n2)
        (Intgr n1, Intgr n2, LE _) -> return (Bl $ n1 <= n2)
        (Intgr n1, Intgr n2, GTH _) -> return (Bl $ n1 > n2)
        (Intgr n1, Intgr n2, GE _) -> return (Bl $ n1 >= n2)
        (Intgr n1, Intgr n2, EQU _) -> return (Bl $ n1 == n2)
        (Intgr n1, Intgr n2, NE _) -> return (Bl $ n1 /= n2)
        (Bl n1, Bl n2, EQU _) -> return (Bl $ n1 == n2)
        (Bl n1, Bl n2, NE _) -> return (Bl $ n1 /= n2)
        (Strln n1, Strln n2, EQU _) -> return (Bl (n1 == n2))
        (Strln n1, Strln n2, NE _) -> return (Bl $ (n1 /= n2))
evalExpr (EAnd pos expr1 expr2) = do
    e1 <- evalExpr expr1
    e2 <- evalExpr expr2
    case (e1, e2) of
        (Bl n1, Bl n2) -> return (Bl (n1 && n2))
evalExpr (EOr pos expr1 expr2) = do
    e1 <- evalExpr expr1
    e2 <- evalExpr expr2
    case (e1, e2) of
        (Bl n1, Bl n2) -> return (Bl (n1 || n2))

alloc :: RSE Location
alloc = do
  m <- get
  if M.null m then return 0
  else let (i, w) = M.findMax m in return (i+1)


evalStmt :: [Stmt] -> RSE BlokValue
evalStmt [] = return EEmpty
evalStmt ((Empty pos):others) = evalStmt others
evalStmt ((Decl pos typ name):others) = do
    loc <- alloc
    case typ of
        (Int _) -> do
                   modify (M.insert loc (Intgr 0))
                   local (M.insert (takeName "" typ name) loc) (evalStmt others)
        (Str _) -> do
                   modify (M.insert loc (Strln ""))
                   local (M.insert (takeName "" typ name) loc) (evalStmt others)
        (Bool _) -> do
                   modify (M.insert loc (Bl False))
                   local (M.insert (takeName "" typ name) loc) (evalStmt others)
evalStmt ((Ass pos typ name expr):others) = do
    env <- ask
    l <- evalMaybe ("Undefined variable" ++ printErr pos) (M.lookup (takeName "" typ name) env)
    e1 <- evalExpr expr
    modify (M.insert l e1)
    evalStmt others
evalStmt ((Incr pos typ name):others) = do
    env <- ask
    l   <- evalMaybe ("Undefined variable" ++ printErr pos) (M.lookup (takeName "" typ name) env)
    e1  <- gets (M.lookup l)
    case e1 of
        Just (Intgr n) -> do
                   modify (M.insert l (Intgr (n + 1)))
                   evalStmt others
        _ -> throwError ("Impossible to increase" ++ printErr pos)
evalStmt ((Decr pos typ name):others) = do
    env <- ask
    l   <- evalMaybe ("Undefined variable" ++ printErr pos) (M.lookup (takeName "" typ name) env)
    e1  <- gets (M.lookup l)
    case e1 of
        Just (Intgr n) -> do
                   modify (M.insert l (Intgr (n - 1)))
                   evalStmt others
        _ -> throwError ("Impossible to decrease" ++ printErr pos)
evalStmt ((Ret pos expr):others) = do
    e <- evalExpr expr
    return (EReturn e)
evalStmt ((Retv pos):others) = return (EReturn Empt)
evalStmt ((Cond pos cond ifstmt):others) = do
    e <- evalExpr cond
    case e of
        (Bl b) -> if b then evalStmt (ifstmt ++ others) else evalStmt others
evalStmt ((CondElse pos cond ifstmt elsestmt):others) = do
    e <- evalExpr cond
    case e of
        (Bl b) -> if b then evalStmt (ifstmt ++ others) else evalStmt (elsestmt ++ others)

evalStmt (WhileSuspended pos cond stmt:others) = do
    res <- evalStmt stmt
    case res of
        EReturn x -> return (EReturn x)
        EBreak _-> evalStmt others
        _ -> evalStmt (WhileContinued pos cond stmt:others)
evalStmt ((WhileContinued pos cond stmt):others) = do
  e <- evalExpr cond
  case e of
        (Bl True) -> evalStmt (WhileSuspended pos cond stmt:others)
        (Bl False) -> evalStmt others
evalStmt ((While pos cond stmt):others) = evalStmt (WhileContinued pos cond stmt:others)

evalStmt (SExp pos expr1:others) = do
    e <- evalExpr expr1
    evalStmt others
evalStmt (Continue pos:others) = do
    return (EContinue pos)
evalStmt (Break pos:others) = do
    return (EBreak pos)
evalStmt (Print pos expr:others) = do
    e <- evalExpr expr
    liftIO $ putStrLn $ showValueSimple e
    evalStmt others


showValueSimple :: Value -> String
showValueSimple (Intgr n) = show n
showValueSimple (Bl b) = show b
showValueSimple (Strln s) = show s
showValueSimple _ = ""


evalStmtFun :: [Stmt] -> RSE Value
evalStmtFun stmts = do
    v <- evalStmt stmts
    case v of
        EReturn x -> return x
        EBreak pos -> throwError ("Break may not be used outside of a loop" ++ printErr pos)
        EContinue pos -> throwError ("Continue may not be used outside of a loop" ++ printErr pos)
        EEmpty -> return Empt

createVarsList :: [TopDefVar' a] -> ([Ident], [Value])
createVarsList (x:list) =
    case x of
        VarDef pos (Int _) name -> (takeName "" (Int 0) name:ids, Intgr 0:vals)
        VarDef pos (Str _) name -> (takeName "" (Str 0) name:ids, Strln "":vals)
        VarDef pos (Bool _) name -> (takeName "" (Bool 0) name:ids, Bl False:vals)
    where (ids, vals) = createVarsList list
createVarsList [] = ([], [])
createFuncList :: [TopDef] -> ([Ident], [Value])
createFuncList (x:list) =
    case x of
        (FnDef pos typ name args block) -> (takeName "Fun" typ name:ids, Func x:vals)
    where (ids, vals) = createFuncList list
createFuncList [] = ([], [])

makeEnv :: Prog -> (Env, Store)
makeEnv (Program pos defVars defFunc block) =
    let (varsNames, valv) = createVarsList defVars in
        let (funcsNames, funcv) = createFuncList defFunc in
            (M.fromList (zip (varsNames ++ funcsNames) [1..]), M.fromList (zip [1..] (valv ++ funcv)))

runEval :: (r, s) -> ReaderT r (StateT s (ExceptT e m)) a -> m (Either e (a, s))
runEval (env, state) ev  =
    runExceptT (runStateT (runReaderT ev env) state)

runEvalProgram :: Prog' BNFC'Position -> IO (Either String (Value, Store))
runEvalProgram (Program pos var func (Block pos2 block)) = runEval (makeEnv (Program pos var func (Block pos2 block))) (evalStmtFun block)