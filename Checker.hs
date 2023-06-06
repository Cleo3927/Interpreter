{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Checker where

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
import Control.Exception (throw)

data ValueType = VIntgr | VStrln | VBl | VEmpt
data BlokValue = EReturn ValueType | EBreak BNFC'Position | EContinue BNFC'Position | EEmpty
data Store = Fun TopDef Env | Var

type Env = M.Map Ident Store -- nazwa, wartosc
type Check a = ReaderT Env (ExceptT String IO) a

takeName :: [Char] -> Type' a -> Ident -> Ident
takeName prefix typ name =
    case (typ, name) of
        (Int _, Ident s) -> Ident (prefix ++ "$" ++ s)
        (Bool _, Ident s) -> Ident (prefix ++ "'" ++ s)
        (Str _, Ident s) -> Ident (prefix ++ "#" ++ s)
        (Void _, Ident s) -> Ident (prefix ++ "@" ++ s)

evalMaybe :: String -> Maybe a -> Check a
evalMaybe s Nothing = throwError s
evalMaybe s (Just a) = return a


printErr :: BNFC'Position -> String
printErr Nothing = ""
printErr (Just (line, col)) = " ---> line " ++ show line

unpackFunction :: BNFC'Position -> Store -> Check [Arg' BNFC'Position]
unpackFunction pos2 (Fun (FnDef pos typ name argsFn (Block _ blok)) _) = return argsFn
unpackFunction pos _ = throwError ("Undeclared Function" ++ printErr pos)

cmpTypes :: BNFC'Position -> [Expr] -> [Arg' BNFC'Position] -> Check Bool
cmpTypes _ [] [] = return True
cmpTypes pos [] (f:func) = do throwError ("Not enough arguments" ++ printErr pos)
cmpTypes pos (e:expr) [] = do throwError ("Too many arguments" ++ printErr pos)
cmpTypes pos (e:expr) (f:func) = do
    e1 <- checkExpr e
    env <- ask
    case (f, e, e1) of
        (Argref _ (Int _) _, EVar _ (Int p) name, _) -> do
            evalMaybe ("Variable doesn't exists" ++ printErr pos) (M.lookup (takeName "" (Int p) name) env)
            cmpTypes pos expr func
        (Argref _ (Str _) _, EVar _ (Str p) name, _) -> do
            evalMaybe ("Variable doesn't exists" ++ printErr pos) (M.lookup (takeName "" (Str p) name) env)
            cmpTypes pos expr func
        (Argref _ (Bool _) _, EVar _ (Bool p) name, _) -> do
            evalMaybe ("Variable doesn't exists" ++ printErr pos) (M.lookup (takeName "" (Bool p) name) env)
            cmpTypes pos expr func
        (Argref {}, _, _) -> throwError ("Argument is not a reference" ++ printErr pos)

        (Argcopy _ (Int _) _, _, VIntgr) -> cmpTypes pos expr func
        (Argcopy _ (Bool _) _, _, VBl) -> cmpTypes pos expr func
        (Argcopy _ (Str _) _, _, VStrln) -> cmpTypes pos expr func
        _ -> throwError ("Incorrect value type applied to function" ++ printErr pos)


checkExpr :: Expr -> Check ValueType
checkExpr (EVar pos typ name) = do
    env <- ask
    evalMaybe ("Variable doesn't exists" ++ printErr pos) (M.lookup (takeName "" typ name) env)
    case typ of
        Int _ -> return VIntgr
        Str _ -> return VStrln
        Bool _ -> return VBl
        _ -> throwError ("Incorect variable type" ++ printErr pos)

checkExpr (ELitInt _ n) = return VIntgr

checkExpr (ELitTrue _) = return VBl

checkExpr (ELitFalse _) = return VBl

checkExpr (EApp pos typ name args) = do
    env <- ask
    fun <- evalMaybe ("Undeclare Function" ++ printErr pos) (M.lookup (takeName "Fun" typ name) env)
    f <- unpackFunction pos fun
    res <- cmpTypes pos args f
    case typ of
        Int _ -> return VIntgr
        Str _ -> return VStrln
        Bool _ -> return VBl
        Void _ -> return VEmpt

checkExpr (EString _ str) = return VStrln

checkExpr (Neg pos subexpr) = do
    val <- checkExpr subexpr
    case val of
        VIntgr -> return VIntgr
        _ -> throwError ("Negation of this expression is impossible" ++ printErr pos)

checkExpr (Not pos subexpr) = do
    val <- checkExpr subexpr
    case val of
         VBl -> return VBl
         _ -> throwError ("Boolean negation of this expression is impossible" ++ printErr pos)

checkExpr (EMul pos expr1 mulop expr2) = do
    e1 <- checkExpr expr1
    e2 <- checkExpr expr2
    case (e1, e2, mulop) of
        (VIntgr, VIntgr, _) -> return VIntgr
        _ -> throwError ("Impossible Mul Operation" ++ printErr pos)

checkExpr (EAdd pos expr1 addop expr2) = do
    e1 <- checkExpr expr1
    e2 <- checkExpr expr2
    case (e1, e2, addop) of
        (VIntgr, VIntgr, _) -> return VIntgr
        (VStrln, VStrln, Plus _) -> return VStrln
        _ -> throwError ("Impossible Add Operation" ++ printErr pos)

checkExpr (ERel pos expr1 relop expr2) = do
    e1 <- checkExpr expr1
    e2 <- checkExpr expr2
    case (e1, e2, relop) of
        (VIntgr, VIntgr, _) -> return VBl
        (VBl, VBl, EQU _) -> return VBl
        (VBl, VBl, NE _) -> return VBl
        (VStrln, VStrln, EQU _) -> return VBl
        (VStrln, VStrln, NE _) -> return VBl
        _ -> throwError ("Impossible Rel Operation" ++ printErr pos)

checkExpr (EAnd pos expr1 expr2) = do
    e1 <- checkExpr expr1
    e2 <- checkExpr expr2
    case (e1, e2) of
        (VBl, VBl) -> return VBl
        _ -> throwError ("Impossible And Operation" ++ printErr pos)

checkExpr (EOr pos expr1 expr2) = do
    e1 <- checkExpr expr1
    e2 <- checkExpr expr2
    case (e1, e2) of
        (VBl, VBl) -> return VBl
        _ -> throwError ("Impossible Or Operation" ++ printErr pos)


setupArgs :: BNFC'Position -> [Arg' a] -> Env -> Check Env
setupArgs pos (a:args) env = do
  case a of
    Argcopy _ typ name -> setupArgs pos args (M.insert (takeName "" typ name) Var env) 
    Argref _ typ nameArg -> setupArgs pos args (M.insert (takeName "" typ nameArg) Var env)
setupArgs _ [] env = return env

checkFunction :: TopDef' BNFC'Position -> [Stmt] -> Check BlokValue
checkFunction (FnDef pos typf (Ident name) args (Block pos2 block)) others = do
    env <- ask
    nenv <- setupArgs pos args env 
    res <- local (const nenv) (checkStmt block)
    case (res, typf) of
        (EReturn VIntgr, Int _) -> checkStmt others 
        (EReturn VBl, Bool _) -> checkStmt others 
        (EReturn VStrln, Str _) -> checkStmt others
        (EReturn _, Void _) -> throwError ("Void function couldn't return value" ++ printErr pos)
        (EEmpty, Void _) -> checkStmt others
        (EReturn _, _) -> throwError ("Function " ++ name ++ " return incorrect type of value" ++ printErr pos)
        _ ->  throwError ("Function " ++ name ++ " doesn't return always value" ++ printErr pos)



checkStmt :: [Stmt] -> Check BlokValue
checkStmt [] = return EEmpty

checkStmt ((Empty pos):others) = checkStmt others

checkStmt ((Decl pos (VarDef _ typ name)):others) = do
    case typ of
        Void _ -> throwError ("Incorect variable type" ++ printErr pos)
        _ -> local (M.insert (takeName "" typ name) Var) (checkStmt others)

checkStmt (DeclFun pos (FnDef posf typf name args (Block pos2 block)):others) = do
    env <- ask
    let f = FnDef posf typf name args (Block pos2 block)
    let nenv = M.insert (takeName "Fun" typf name) (Fun f env)
    local nenv (checkFunction f others)

checkStmt ((Ass pos typ name expr):others) = do
    env <- ask
    evalMaybe ("Undefined variable" ++ printErr pos) (M.lookup (takeName "" typ name) env)
    e1 <- checkExpr expr
    case (typ, e1) of
        (Int _, VIntgr) -> checkStmt others
        (Bool _, VBl) -> checkStmt others
        (Str _, VStrln) -> checkStmt others
        _ -> throwError ("Incorrect Assigment" ++ printErr pos)

checkStmt ((Incr pos typ name):others) = do
    env <- ask
    evalMaybe ("Undefined variable" ++ printErr pos) (M.lookup (takeName "" typ name) env)
    case typ of
        (Int _) -> checkStmt others
        _ -> throwError ("Impossible to increase" ++ printErr pos)

checkStmt ((Decr pos typ name):others) = do
    env <- ask
    evalMaybe ("Undefined variable" ++ printErr pos) (M.lookup (takeName "" typ name) env)
    case typ of
        (Int _) -> checkStmt others
        _ -> throwError ("Impossible to increase" ++ printErr pos)

checkStmt ((Ret pos expr):others) = do
    e <- checkExpr expr
    case e of
        VEmpt -> throwError ("Couldn't return void value" ++ printErr pos)
        _ -> return (EReturn e)

checkStmt ((Retv pos):others) = return EEmpty

checkStmt ((Cond pos cond ifstmt):others) = do
    e <- checkExpr cond
    checkStmt ifstmt
    case e of
        VBl -> checkStmt others
        _ -> throwError ("Condition doesn't have boolean type" ++ printErr pos)

checkStmt ((CondElse pos cond ifstmt elsestmt):others) = do
    e <- checkExpr cond
    res <- checkStmt ifstmt
    res2 <- checkStmt elsestmt
    case (e, res, res2) of
        (VBl, EEmpty, EEmpty) -> checkStmt others
        (VBl, EReturn VIntgr, EReturn VIntgr) -> return (EReturn VIntgr)
        (VBl, EReturn VBl, EReturn VBl) -> return (EReturn VBl)
        (VBl, EReturn VStrln, EReturn VStrln) -> return (EReturn VStrln)
        (VBl, _, _) -> throwError ("If return different types" ++ printErr pos)
        (_, _, _) -> throwError ("Condition doesn't have boolean type" ++ printErr pos)

checkStmt ((While pos cond stmt):others) = do
    e <- checkExpr cond
    checkStmt stmt

    case e of
        VBl -> checkStmt others
        _ -> throwError ("Condition doesn't have boolean type" ++ printErr pos)

checkStmt (SExp pos expr1:others) = do
    checkExpr expr1
    checkStmt others

checkStmt (Continue pos:others) = do
    return (EContinue pos)

checkStmt (Break pos:others) = do
    return (EBreak pos)

checkStmt (Print pos expr:others) = do
    checkExpr expr
    checkStmt others

createVarsList :: [TopDefVar' BNFC'Position] -> [Stmt]
createVarsList ((VarDef pos typ name):list) = Decl pos (VarDef pos typ name):createVarsList list
createVarsList [] = []

createFuncList :: [TopDef' BNFC'Position] -> [Stmt]
createFuncList ((FnDef pos typ name args block):list) = DeclFun pos (FnDef pos typ name args block):createFuncList list
createFuncList [] = []

runCheckProgram :: Prog' BNFC'Position -> IO (Either String BlokValue)
runCheckProgram (Program pos var func (Block pos2 block)) = runExceptT (runReaderT (checkStmt (createVarsList var ++ createFuncList func ++ block)) M.empty)
