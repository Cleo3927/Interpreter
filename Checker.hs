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

data ValueType = Intgr | Strln | Bl | Empt


type Location = Int
type FuncStore = M.Map Ident TopDef

evalExpr :: Expr -> FuncStore -> Except String ValueType

evalMaybe :: String -> Maybe a -> Except String a
evalMaybe s Nothing = throwError s
evalMaybe s (Just a) = return a

unpackFunction :: Maybe TopDef -> Except String [Arg]
unpackFunction (Just (FnDef pos typ name argsFn (Block _ blok))) = return argsFn
unpackFunction Nothing = throwError "Undeclared Function"

cmpTypes :: [Expr] -> [Arg' a] -> FuncStore -> ExceptT String Identity Bool
cmpTypes [] [] _= return True
cmpTypes [] (f:func) functions = do throwError "Not enough arguments"
cmpTypes (a:args) [] functions = do throwError "Too many arguments"
cmpTypes (a:args) (f:func) functions = do
    e1 <- evalExpr a functions
    case (e1, f) of
        (Intgr, Argcopy _ (Int _) _) -> cmpTypes args func functions
        (Intgr, Argref _ (Int _) _) -> cmpTypes args func functions
        (Bl, Argcopy _ (Bool _) _) -> cmpTypes args func functions
        (Bl, Argref _ (Bool _) _) -> cmpTypes args func functions
        (Strln, Argcopy _ (Str _) _) -> cmpTypes args func functions
        (Strln, Argref _ (Str _) _) -> cmpTypes args func functions
        _ -> throwError "Incorrect value type applied to function"

evalExpr (EVar pos typ name) _ = do
    case typ of
        Int _ -> return Intgr
        Str _ -> return Strln
        Bool _ -> return Bl
        _ -> throwError "Incorect variable type"
evalExpr (ELitInt _ n) _ = return Intgr
evalExpr (ELitTrue _) _ = return Bl
evalExpr (ELitFalse _) _ = return Bl
evalExpr (EApp pos typ name args) functions = do
    f <- unpackFunction (M.lookup name functions)
    res <- cmpTypes args f functions
    case typ of
        Int _ -> return Intgr
        Str _ -> return Strln
        Bool _ -> return Bl
        Void _ -> return Empt
evalExpr (EString _ str) _ = return Strln
evalExpr (Neg pos subexpr) functions = do
    val <- evalExpr subexpr functions
    case val of
        Intgr -> return Intgr
        _ -> throwError "Negation of this expression is impossible"
evalExpr (Not pos subexpr) functions = do
    val <- evalExpr subexpr functions
    case val of
         Bl -> return Bl
         _ -> throwError "Boolean negation of this expression is impossible"
evalExpr (EMul pos expr1 mulop expr2) functions = do
    e1 <- evalExpr expr1 functions
    e2 <- evalExpr expr2 functions
    case (e1, e2, mulop) of
        (Intgr, Intgr, _) -> return Intgr
        _ -> throwError "Impossible Mul Operation"
evalExpr (EAdd pos expr1 addop expr2) functions = do
    e1 <- evalExpr expr1 functions
    e2 <- evalExpr expr2 functions
    case (e1, e2, addop) of
        (Intgr, Intgr, _) -> return Intgr
        (Strln, Strln, Plus _) -> return Strln
        _ -> throwError "Impossible Add Operation"

evalExpr (ERel pos expr1 relop expr2) functions = do
    e1 <- evalExpr expr1 functions
    e2 <- evalExpr expr2 functions
    case (e1, e2, relop) of
        (Intgr, Intgr, _) -> return Bl
        (Bl, Bl, EQU _) -> return Bl
        (Bl, Bl, NE _) -> return Bl
        (Strln, Strln, EQU _) -> return Bl
        (Strln, Strln, NE _) -> return Bl
        _ -> throwError "Impossible Rel Operation"
evalExpr (EAnd pos expr1 expr2) functions = do
    e1 <- evalExpr expr1 functions
    e2 <- evalExpr expr2 functions
    case (e1, e2) of
        (Bl, Bl) -> return Bl
        _ -> throwError "Impossible And Operation"
evalExpr (EOr pos expr1 expr2) functions = do
    e1 <- evalExpr expr1 functions
    e2 <- evalExpr expr2 functions
    case (e1, e2) of
        (Bl, Bl) -> return Bl
        _ -> throwError "Impossible Or Operation"

evalStmt :: [Stmt' BNFC'Position] -> FuncStore -> ExceptT String Identity Bool
evalStmt [] _ = return True
evalStmt ((Empty pos):others) functions = evalStmt others functions
evalStmt ((Decl pos typ name):others) functions = do
    case typ of
        (Int _) -> evalStmt others functions
        (Str _) -> evalStmt others functions
        (Bool _) -> evalStmt others functions
        _ -> throwError "Couldn't declare variable with this type"
evalStmt ((Ass pos typ name expr):others) functions = do
    e <- evalExpr expr functions
    case (typ, e) of
        (Int _, Intgr) -> evalStmt others functions
        (Str _, Strln) -> evalStmt others functions
        (Bool _, Bl) -> evalStmt others functions
        _ -> throwError "Incorrect Assigment"
evalStmt ((Incr pos typ name):others) functions = do
    case typ of
        Int _ -> evalStmt others functions
        _ -> throwError "Impossible to increase"
evalStmt ((Decr pos typ name):others) functions = do
    case typ of
        Int _ -> evalStmt others functions
        _ -> throwError "Impossible to decrease"
evalStmt ((Ret pos expr):others) functions = do
    e <- evalExpr expr functions
    case e of
        Empt -> throwError "Couldn't retrun void value"
        _ -> evalStmt others functions
evalStmt ((Retv pos):others) functions = evalStmt others functions
evalStmt ((Cond pos cond ifstmt):others) functions = do
    e <- evalExpr cond functions
    case e of
        Bl -> evalStmt (ifstmt ++ others) functions
        _ -> throwError "Condition doesn't have boolean type"
evalStmt ((CondElse pos cond ifstmt elsestmt):others) functions = do
    e <- evalExpr cond functions
    case e of
        Bl -> evalStmt (ifstmt ++ elsestmt ++ others) functions
        _ -> throwError "Condition doesn't have boolean type"
evalStmt ((While pos cond loop):others) functions = do
    e <- evalExpr cond functions
    case e of
        Bl -> evalStmt (loop ++ others) functions
        _ -> throwError "Condition doesn't have boolean type"

evalStmt ((For pos typ name expr1 expr2 loop):others) functions = do
    e1 <- evalExpr expr1 functions
    e2 <- evalExpr expr2 functions
    case (typ, e1, e2) of
        (Int _, Intgr, Intgr) -> do evalStmt (loop ++ others) functions
        _ -> throwError "Incorrect types of variables in loop"
evalStmt (SExp pos expr1:others) functions = do evalStmt others functions
evalStmt (Continue pos:others) functions = do evalStmt others functions
evalStmt (Break pos:others) functions = do evalStmt others functions
evalStmt (Print pos expr:others) functions = do evalStmt others functions

checkReturnValue :: ValueType -> Expr -> FuncStore -> Except String Bool
checkReturnValue typ expr functions = do
    e <- evalExpr expr functions
    case (typ, e) of
        (Intgr, Intgr) -> return True
        (Bl, Bl) -> return True
        (Strln, Strln) -> return True
        (_, _) -> throwError "Incorrect value of returned function"

evalStmtFun :: ValueType -> [Stmt' BNFC'Position] -> FuncStore -> Except String Bool
evalStmtFun val (s:stmts) functions = do
    case (val, s) of
        (Intgr, Ret pos expr) -> do
            res <- checkReturnValue val expr functions
            evalStmtFun val stmts functions
        (Bl, Ret pos expr) -> do
            res <- checkReturnValue val expr functions
            evalStmtFun val stmts functions
        (Strln, Ret pos expr) -> do
            res <- checkReturnValue val expr functions
            evalStmtFun val stmts functions
        (Empt, Ret pos expr) -> throwError "Void Function couldn't return value"
        (_, _) -> evalStmtFun val stmts functions
evalStmtFun val [] functions = return True

checkStmtFunCount :: Monad m => ValueType -> [Stmt' a] -> t -> m Bool
checkStmtFunCount  val (s:stmts) functions = do
    case (val, s) of
        (Intgr, Ret pos expr) -> return True
        (Bl, Ret pos expr) -> return True
        (Strln, Ret pos expr) -> return True
        _ -> checkStmtFunCount val stmts functions
checkStmtFunCount val [] functions = return False

checkFunctions :: [TopDef' BNFC'Position] -> FuncStore -> Except String Bool
checkFunctions [] _ = return True
checkFunctions (FnDef pos typ name args (Block _ block):funcs) functions = do
    case typ of
        (Int _) -> do
            evalStmtFun Intgr block functions
            ret <- checkStmtFunCount Intgr block functions
            if not ret then throwError "Function doesn't return value" else checkFunctions funcs functions
        (Bool _) -> do
            evalStmtFun Bl block functions
            ret <- checkStmtFunCount Bl block functions
            if not ret then throwError "Function doesn't return value" else checkFunctions funcs functions
        (Str _) -> do
            evalStmtFun Strln block functions
            ret <- checkStmtFunCount Strln block functions
            if not ret then throwError "Function doesn't return value" else checkFunctions funcs functions
        (Void _) -> do
            evalStmtFun Strln block functions
            checkFunctions funcs functions

makeFunctionsRes :: [TopDef' a] -> [(Ident, TopDef' a)]
makeFunctionsRes [] = []
makeFunctionsRes (FnDef pos typ name args block:funcs) = (name, FnDef pos typ name args block):makeFunctionsRes funcs

runCheckProgram :: Prog' BNFC'Position -> Except String Bool
runCheckProgram (Program pos var func (Block pos2 block)) = do
    let f = makeFunctionsRes func in do
        let res = runExceptT (checkFunctions func (M.fromList f)) in do
            let res2 = runExceptT (evalStmt block (M.fromList f)) in do
                return True