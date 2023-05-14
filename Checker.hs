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

data ValueType = VIntgr | VStrln | VBl | VEmpt


type Location = Int
type FuncStore = M.Map Ident TopDef

evalExpr :: Expr -> FuncStore -> Except String ValueType

takeName :: [Char] -> Type' a -> Ident -> Ident
takeName prefix typ name =
    case (typ, name) of
        (Int _, Ident s) -> Ident (prefix ++ "$" ++ s)
        (Bool _, Ident s) -> Ident (prefix ++ "'" ++ s)
        (Str _, Ident s) -> Ident (prefix ++ "#" ++ s)
        (Void _, Ident s) -> Ident (prefix ++ "@" ++ s)


evalMaybe :: String -> Maybe a -> Except String a
evalMaybe s Nothing = throwError s
evalMaybe s (Just a) = return a

printErr :: BNFC'Position -> String
printErr Nothing = ""
printErr (Just (line, col)) = " in line " ++ show line

unpackFunction :: BNFC'Position -> Maybe (TopDef' a) -> Except String [Arg' a]
unpackFunction pos2 (Just (FnDef pos typ name argsFn (Block _ blok))) = return argsFn
unpackFunction pos Nothing = throwError ("Undeclared Function" ++ printErr pos)

cmpTypes :: BNFC'Position -> [Expr] -> [Arg' a] -> FuncStore -> ExceptT String Identity Bool
cmpTypes _ [] [] _= return True
cmpTypes pos [] (f:func) functions = do throwError ("Not enough arguments" ++ printErr pos)
cmpTypes pos (a:args) [] functions = do throwError ("Too many arguments" ++ printErr pos)
cmpTypes pos (a:args) (f:func) functions = do
    e1 <- evalExpr a functions
    case (e1, f) of
        (VIntgr, Argcopy _ (Int _) _) -> cmpTypes pos args func functions
        (VIntgr, Argref _ (Int _) _) -> cmpTypes pos args func functions
        (VBl, Argcopy _ (Bool _) _) -> cmpTypes pos args func functions
        (VBl, Argref _ (Bool _) _) -> cmpTypes pos args func functions
        (VStrln, Argcopy _ (Str _) _) -> cmpTypes pos args func functions
        (VStrln, Argref _ (Str _) _) -> cmpTypes pos args func functions
        _ -> throwError ("Incorrect value type applied to function" ++ printErr pos)

evalExpr (EVar pos typ name) _ = do
    case typ of
        Int _ -> return VIntgr
        Str _ -> return VStrln
        Bool _ -> return VBl
        _ -> throwError ("Incorect variable type" ++ printErr pos)
evalExpr (ELitInt _ n) _ = return VIntgr
evalExpr (ELitTrue _) _ = return VBl
evalExpr (ELitFalse _) _ = return VBl
evalExpr (EApp pos typ name args) functions = do
    f <- unpackFunction pos (M.lookup (takeName "Fun" typ name) functions)
    res <- cmpTypes pos args f functions
    case typ of
        Int _ -> return VIntgr
        Str _ -> return VStrln
        Bool _ -> return VBl
        Void _ -> return VEmpt
evalExpr (EString _ str) _ = return VStrln
evalExpr (Neg pos subexpr) functions = do
    val <- evalExpr subexpr functions
    case val of
        VIntgr -> return VIntgr
        _ -> throwError ("Negation of this expression is impossible" ++ printErr pos)
evalExpr (Not pos subexpr) functions = do
    val <- evalExpr subexpr functions
    case val of
         VBl -> return VBl
         _ -> throwError ("Boolean negation of this expression is impossible" ++ printErr pos)
evalExpr (EMul pos expr1 mulop expr2) functions = do
    e1 <- evalExpr expr1 functions
    e2 <- evalExpr expr2 functions
    case (e1, e2, mulop) of
        (VIntgr, VIntgr, _) -> return VIntgr
        _ -> throwError ("Impossible Mul Operation" ++ printErr pos)
evalExpr (EAdd pos expr1 addop expr2) functions = do
    e1 <- evalExpr expr1 functions
    e2 <- evalExpr expr2 functions
    case (e1, e2, addop) of
        (VIntgr, VIntgr, _) -> return VIntgr
        (VStrln, VStrln, Plus _) -> return VStrln
        _ -> throwError ("Impossible Add Operation" ++ printErr pos)

evalExpr (ERel pos expr1 relop expr2) functions = do
    e1 <- evalExpr expr1 functions
    e2 <- evalExpr expr2 functions
    case (e1, e2, relop) of
        (VIntgr, VIntgr, _) -> return VBl
        (VBl, VBl, EQU _) -> return VBl
        (VBl, VBl, NE _) -> return VBl
        (VStrln, VStrln, EQU _) -> return VBl
        (VStrln, VStrln, NE _) -> return VBl
        _ -> throwError ("Impossible Rel Operation" ++ printErr pos)
evalExpr (EAnd pos expr1 expr2) functions = do
    e1 <- evalExpr expr1 functions
    e2 <- evalExpr expr2 functions
    case (e1, e2) of
        (VBl, VBl) -> return VBl
        _ -> throwError ("Impossible And Operation" ++ printErr pos)
evalExpr (EOr pos expr1 expr2) functions = do
    e1 <- evalExpr expr1 functions
    e2 <- evalExpr expr2 functions
    case (e1, e2) of
        (VBl, VBl) -> return VBl
        _ -> throwError ("Impossible Or Operation" ++ printErr pos)

evalStmt :: [Stmt' BNFC'Position] -> FuncStore -> Except String Bool
evalStmt [] _ = return True
evalStmt ((Empty pos):others) functions = evalStmt others functions
evalStmt ((Decl pos typ name):others) functions = do
    case typ of
        (Int _) -> evalStmt others functions
        (Str _) -> evalStmt others functions
        (Bool _) -> evalStmt others functions
        _ -> throwError ("Couldn't declare variable with this type" ++ printErr pos)
evalStmt ((Ass pos typ name expr):others) functions = do
    e <- evalExpr expr functions
    case (typ, e) of
        (Int _, VIntgr) -> evalStmt others functions
        (Str _, VStrln) -> evalStmt others functions
        (Bool _, VBl) -> evalStmt others functions
        _ -> throwError ("Incorrect Assigment" ++ printErr pos)
evalStmt ((Incr pos typ name):others) functions = do
    case typ of
        Int _ -> evalStmt others functions
        _ -> throwError ("Impossible to increase" ++ printErr pos)
evalStmt ((Decr pos typ name):others) functions = do
    case typ of
        Int _ -> evalStmt others functions
        _ -> throwError ("Impossible to decrease" ++ printErr pos)
evalStmt ((Ret pos expr):others) functions = do
    e <- evalExpr expr functions
    case e of
        VEmpt -> throwError ("Couldn't retrun void value" ++ printErr pos)
        _ -> evalStmt others functions
evalStmt ((Retv pos):others) functions = evalStmt others functions
evalStmt ((Cond pos cond ifstmt):others) functions = do
    e <- evalExpr cond functions
    case e of
        VBl -> evalStmt (ifstmt ++ others) functions
        _ -> throwError ("Condition doesn't have boolean type" ++ printErr pos)
evalStmt ((CondElse pos cond ifstmt elsestmt):others) functions = do
    e <- evalExpr cond functions
    case e of
        VBl -> evalStmt (ifstmt ++ elsestmt ++ others) functions
        _ -> throwError ("Condition doesn't have boolean type" ++ printErr pos)
evalStmt ((While pos cond loop):others) functions = do
    e <- evalExpr cond functions
    case e of
        VBl -> evalStmt (loop ++ others) functions
        _ -> throwError ("Condition doesn't have boolean type" ++ printErr pos)

evalStmt (SExp pos expr1:others) functions = do
    e <- evalExpr expr1 functions
    evalStmt others functions
evalStmt (Continue pos:others) functions = do evalStmt others functions
evalStmt (Break pos:others) functions = do evalStmt others functions
evalStmt (Print pos expr:others) functions = do 
    e <- evalExpr expr functions
    evalStmt others functions

checkReturnValue :: BNFC'Position -> ValueType -> Expr -> FuncStore -> ExceptT String Identity Bool
checkReturnValue pos typ expr functions = do
    e <- evalExpr expr functions
    case (typ, e) of
        (VIntgr, VIntgr) -> return True
        (VBl, VBl) -> return True
        (VStrln, VStrln) -> return True
        (_, _) -> throwError ("Incorrect value of returned function" ++ printErr pos)

evalStmtFun :: ValueType -> [Stmt' BNFC'Position] -> FuncStore -> Except String Bool
evalStmtFun val (s:stmts) functions = do
    case (val, s) of
        (VIntgr, Ret pos expr) -> do
            res <- checkReturnValue pos val expr functions
            evalStmtFun val stmts functions
        (VBl, Ret pos expr) -> do
            res <- checkReturnValue pos val expr functions
            evalStmtFun val stmts functions
        (VStrln, Ret pos expr) -> do
            res <- checkReturnValue pos val expr functions
            evalStmtFun val stmts functions
        (VEmpt, Ret pos expr) -> throwError ("Void Function couldn't return value" ++ printErr pos)
        (_, _) -> evalStmtFun val stmts functions
evalStmtFun val [] functions = return True

checkStmtFunCount :: Monad m => ValueType -> [Stmt' a] -> t -> m Bool
checkStmtFunCount  val (s:stmts) functions = do
    case (val, s) of
        (VIntgr, Ret pos expr) -> return True
        (VBl, Ret pos expr) -> return True
        (VStrln, Ret pos expr) -> return True
        _ -> checkStmtFunCount val stmts functions
checkStmtFunCount val [] functions = return False

checkFunctions :: [TopDef' BNFC'Position] -> FuncStore -> Except String Bool
checkFunctions [] _ = return True
checkFunctions (FnDef pos typ name args (Block _ block):funcs) functions = do
    case typ of
        (Int _) -> do
            evalStmtFun VIntgr block functions
            ret <- checkStmtFunCount VIntgr block functions
            if not ret then throwError ("Function doesn't return value" ++ printErr pos) else checkFunctions funcs functions
        (Bool _) -> do
            evalStmtFun VBl block functions
            ret <- checkStmtFunCount VBl block functions
            if not ret then throwError ("Function doesn't return value" ++ printErr pos) else checkFunctions funcs functions
        (Str _) -> do
            evalStmtFun VStrln block functions
            ret <- checkStmtFunCount VStrln block functions
            if not ret then throwError ("Function doesn't return value" ++ printErr pos) else checkFunctions funcs functions
        (Void _) -> do
            evalStmtFun VEmpt block functions
            checkFunctions funcs functions

makeFunctionsRes :: [TopDef' a] -> [(Ident, TopDef' a)]
makeFunctionsRes [] = []
makeFunctionsRes (FnDef pos typ name args block:funcs) = (takeName "Fun" typ name, FnDef pos typ name args block):makeFunctionsRes funcs

runCheckProgram :: Prog' BNFC'Position -> Either String Bool
runCheckProgram (Program pos var func (Block pos2 block)) = do
    let f = makeFunctionsRes func in do
        let res = runExcept (checkFunctions func (M.fromList f)) in do
            let res2 = runExcept (evalStmt block (M.fromList f)) in do
                case (res, res2) of
                    (Right _, Right _) -> Right True
                    (Left mes, _) -> throwError mes
                    (_, Left mes) -> throwError mes
