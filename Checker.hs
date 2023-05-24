module Checker where

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
import GHC.Exts.Heap (GenClosure(fun))
import System.Console.Terminfo (functionKey)
import Distribution.Compat.ResponseFile (expandResponse)
import Eval (Value(Empt))
import GHC.RTS.Flags (DebugFlags(stm))

data ValueType = VIntgr | VStrln | VBl | VEmpt


type Location = Int
type FuncStore = M.Map Ident TopDef
type Check a = Except String a


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

unpackFunction :: BNFC'Position -> Maybe (TopDef' a) -> Check [Arg' a]
unpackFunction pos2 (Just (FnDef pos typ name argsFn (Block _ blok))) = return argsFn
unpackFunction pos Nothing = throwError ("Undeclared Function" ++ printErr pos)

cmpTypes :: BNFC'Position -> [Expr] -> [Arg' a] -> FuncStore -> Check Bool
cmpTypes _ [] [] _= return True
cmpTypes pos [] (f:func) functions = do throwError ("Not enough arguments" ++ printErr pos)
cmpTypes pos (a:args) [] functions = do throwError ("Too many arguments" ++ printErr pos)
cmpTypes pos (a:args) (f:func) functions = do
    e1 <- checkExpr a functions
    case (e1, f) of
        (VIntgr, Argcopy _ (Int _) _) -> cmpTypes pos args func functions
        (VIntgr, Argref _ (Int _) _) -> cmpTypes pos args func functions
        (VBl, Argcopy _ (Bool _) _) -> cmpTypes pos args func functions
        (VBl, Argref _ (Bool _) _) -> cmpTypes pos args func functions
        (VStrln, Argcopy _ (Str _) _) -> cmpTypes pos args func functions
        (VStrln, Argref _ (Str _) _) -> cmpTypes pos args func functions
        _ -> throwError ("Incorrect value type applied to function" ++ printErr pos)

checkExpr :: Expr -> FuncStore -> Check ValueType
checkExpr (EVar pos typ name) _ = do
    case typ of
        Int _ -> return VIntgr
        Str _ -> return VStrln
        Bool _ -> return VBl
        _ -> throwError ("Incorect variable type" ++ printErr pos)
checkExpr (ELitInt _ n) _ = return VIntgr
checkExpr (ELitTrue _) _ = return VBl
checkExpr (ELitFalse _) _ = return VBl
checkExpr (EApp pos typ name args) functions = do
    f <- unpackFunction pos (M.lookup (takeName "Fun" typ name) functions)
    res <- cmpTypes pos args f functions
    case typ of
        Int _ -> return VIntgr
        Str _ -> return VStrln
        Bool _ -> return VBl
        Void _ -> return VEmpt
checkExpr (EString _ str) _ = return VStrln
checkExpr (Neg pos subexpr) functions = do
    val <- checkExpr subexpr functions
    case val of
        VIntgr -> return VIntgr
        _ -> throwError ("Negation of this expression is impossible" ++ printErr pos)
checkExpr (Not pos subexpr) functions = do
    val <- checkExpr subexpr functions
    case val of
         VBl -> return VBl
         _ -> throwError ("Boolean negation of this expression is impossible" ++ printErr pos)
checkExpr (EMul pos expr1 mulop expr2) functions = do
    e1 <- checkExpr expr1 functions
    e2 <- checkExpr expr2 functions
    case (e1, e2, mulop) of
        (VIntgr, VIntgr, _) -> return VIntgr
        _ -> throwError ("Impossible Mul Operation" ++ printErr pos)
checkExpr (EAdd pos expr1 addop expr2) functions = do
    e1 <- checkExpr expr1 functions
    e2 <- checkExpr expr2 functions
    case (e1, e2, addop) of
        (VIntgr, VIntgr, _) -> return VIntgr
        (VStrln, VStrln, Plus _) -> return VStrln
        _ -> throwError ("Impossible Add Operation" ++ printErr pos)

checkExpr (ERel pos expr1 relop expr2) functions = do
    e1 <- checkExpr expr1 functions
    e2 <- checkExpr expr2 functions
    case (e1, e2, relop) of
        (VIntgr, VIntgr, _) -> return VBl
        (VBl, VBl, EQU _) -> return VBl
        (VBl, VBl, NE _) -> return VBl
        (VStrln, VStrln, EQU _) -> return VBl
        (VStrln, VStrln, NE _) -> return VBl
        _ -> throwError ("Impossible Rel Operation" ++ printErr pos)
checkExpr (EAnd pos expr1 expr2) functions = do
    e1 <- checkExpr expr1 functions
    e2 <- checkExpr expr2 functions
    case (e1, e2) of
        (VBl, VBl) -> return VBl
        _ -> throwError ("Impossible And Operation" ++ printErr pos)
checkExpr (EOr pos expr1 expr2) functions = do
    e1 <- checkExpr expr1 functions
    e2 <- checkExpr expr2 functions
    case (e1, e2) of
        (VBl, VBl) -> return VBl
        _ -> throwError ("Impossible Or Operation" ++ printErr pos)

checkStmt :: [Stmt' BNFC'Position] -> FuncStore -> Check ValueType
checkStmt [] _ = return VEmpt
checkStmt ((Empty pos):others) functions = checkStmt others functions
checkStmt ((Decl pos (VarDef _ typ name)):others) functions = do
    case typ of
        (Int _) -> checkStmt others functions
        (Str _) -> checkStmt others functions
        (Bool _) -> checkStmt others functions
        _ -> throwError ("Couldn't declare variable with this type" ++ printErr pos)
checkStmt (DeclFun pos (FnDef posf typf name args (Block pos2 block)):others) functions= do
    res <- checkFunction (FnDef posf typf name args (Block pos2 block)) (M.insert (takeName "Fun" typf name) (FnDef posf typf name args (Block pos2 block)) functions)
    if res then checkStmt others (M.insert (takeName "Fun" typf name) (FnDef posf typf name args (Block pos2 block)) functions)
    else throwError ("Incorrect declaration of function" ++ printErr pos)
checkStmt ((Ass pos typ name expr):others) functions = do
    e <- checkExpr expr functions
    case (typ, e) of
        (Int _, VIntgr) -> checkStmt others functions
        (Str _, VStrln) -> checkStmt others functions
        (Bool _, VBl) -> checkStmt others functions
        _ -> throwError ("Incorrect Assigment" ++ printErr pos)
checkStmt ((Incr pos typ name):others) functions = do
    case typ of
        Int _ -> checkStmt others functions
        _ -> throwError ("Impossible to increase" ++ printErr pos)
checkStmt ((Decr pos typ name):others) functions = do
    case typ of
        Int _ -> checkStmt others functions
        _ -> throwError ("Impossible to decrease" ++ printErr pos)
checkStmt ((Ret pos expr):others) functions = do
    e <- checkExpr expr functions
    case e of
        VEmpt -> throwError ("Couldn't return void value" ++ printErr pos)
        _ -> checkStmt others functions
checkStmt ((Retv pos):others) functions = checkStmt others functions
checkStmt ((Cond pos cond ifstmt):others) functions = do
    e <- checkExpr cond functions
    res <- checkStmt ifstmt functions
    case e of
        VBl -> checkStmt others functions
        _ -> throwError ("Condition doesn't have boolean type" ++ printErr pos)
checkStmt ((CondElse pos cond ifstmt elsestmt):others) functions = do
    e <- checkExpr cond functions
    res1 <- checkStmt ifstmt functions
    res2 <- checkStmt elsestmt functions
    case e of
        VBl -> checkStmt others functions
        _ -> throwError ("Condition doesn't have boolean type" ++ printErr pos)
checkStmt ((While pos cond loop):others) functions = do
    e <- checkExpr cond functions
    res <- checkStmt loop functions
    case e of
        VBl -> checkStmt others functions
        _ -> throwError ("Condition doesn't have boolean type" ++ printErr pos)

checkStmt (SExp pos expr1:others) functions = do
    e <- checkExpr expr1 functions
    checkStmt others functions
checkStmt (Continue pos:others) functions = do checkStmt others functions
checkStmt (Break pos:others) functions = do checkStmt others functions
checkStmt (Print pos expr:others) functions = do
    e <- checkExpr expr functions
    checkStmt others functions

-- compare return types
checkReturnValue :: BNFC'Position -> ValueType -> Expr -> FuncStore -> Check Bool
checkReturnValue pos typ expr functions = do
    e <- checkExpr expr functions
    case (typ, e) of
        (VIntgr, VIntgr) -> return True
        (VBl, VBl) -> return True
        (VStrln, VStrln) -> return True
        (_, _) -> throwError ("Incorrect value of returned function" ++ printErr pos)

-- check returns in functions
checkStmtRet :: ValueType -> [Stmt' BNFC'Position] -> FuncStore -> Check Bool
checkStmtRet val (s:stmts) functions = do
    case (val, s) of
        (VEmpt, Ret pos expr) -> throwError ("Void Function couldn't return value" ++ printErr pos)
        (VEmpt, Retv pos) -> checkStmtRet val stmts functions
        (_, Retv pos) -> throwError ("Function couldn't return void" ++ printErr pos)
        (_, Ret pos expr) -> do
            checkReturnValue pos val expr functions
            checkStmtRet val stmts functions
        (_, Cond _ cond ifstmt) -> do
            checkStmtRet val ifstmt functions
            checkStmtRet val stmts functions
        (_, CondElse _ cond ifstmt elsestmt) -> do
            checkStmtRet val ifstmt functions
            checkStmtRet val elsestmt functions
            checkStmtRet val stmts functions
        (_, While _ cond loop) -> do
            checkStmtRet val loop functions
            checkStmtRet val stmts functions
        _ -> checkStmtRet val stmts functions
checkStmtRet val [] functions = return True

-- check if function always return type
checkStmtFunCount :: [Stmt' a] -> Check Bool
checkStmtFunCount (s:stmts) = do
    case s of
        Ret _ _ -> return True
        CondElse pos cond ifstmt elsestmt -> do
            res1 <- checkStmtFunCount ifstmt
            res2 <- checkStmtFunCount elsestmt
            if res1 && res2 then return True else checkStmtFunCount stmts
        _ -> checkStmtFunCount stmts
checkStmtFunCount [] = return False

checkFunction :: TopDef' BNFC'Position -> FuncStore -> Check Bool
checkFunction (FnDef pos typ (Ident name) args (Block _ block)) functions = do
    checkStmt block functions
    case typ of
        (Int _) -> do
            checkStmtRet VIntgr block functions
            ret <- checkStmtFunCount block
            if not ret then throwError ("Function " ++ name ++ " doesn't return value" ++ printErr pos) else return True
        (Bool _) -> do
            checkStmtRet VBl block functions
            ret <- checkStmtFunCount block
            if not ret then throwError ("Function " ++ name ++ " doesn't return value" ++ printErr pos) else return True
        (Str _) -> do
            checkStmtRet VStrln block functions
            ret <- checkStmtFunCount block
            if not ret then throwError ("Function " ++ name ++ " doesn't return value" ++ printErr pos) else return True
        (Void _) -> do
            checkStmtRet VEmpt block functions
            return True

createVarsList :: [TopDefVar' BNFC'Position] -> [Stmt]
createVarsList ((VarDef pos typ name):list) = Decl pos (VarDef pos typ name):createVarsList list
createVarsList [] = []

createFuncList :: [TopDef' BNFC'Position] -> [Stmt]
createFuncList ((FnDef pos typ name args block):list) = DeclFun pos (FnDef pos typ name args block):createFuncList list
createFuncList [] = []

runCheckProgram :: Prog' BNFC'Position -> Either String ValueType
runCheckProgram (Program pos var func (Block pos2 block)) = runExcept (checkStmt (createVarsList var ++ createFuncList func ++ block) M.empty)
