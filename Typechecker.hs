module Grammar.Typechecker where

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

data ValueType = Intgr | Strln | Bl | Empt

evalExpr :: Expr -> M.Map Ident [ValueType] -> Except String ValueType
cmpTypes :: [ValueType] -> [ValueType] -> Bool
cmpTypes [] [] = True
cmpTypes [] (a:args) = False
cmpTypes (e:exprs) [] = False
cmpTypes (e:exprs) (a:args) =
    case (e, a) of
        (Intgr, Intgr) -> cmpTypes exprs args
        (Bl, Bl) -> cmpTypes exprs args
        (Strln, Strln) -> cmpTypes exprs args
        _ -> False

-- setupArgs :: BNFC'Position -> [Arg] -> [Expr] -> ValueType
-- setupArgs pos (a:args) (e:exprs) = do
--   case a of
    -- Argcopy _ typ name -> do
        -- v <- evalExpr e
        -- loc <- alloc
        -- modify (M.insert loc v)
        -- setupArgs pos args exprs (M.insert name loc env)
    -- Argref _ typ nameArg -> do
        -- case e of
            -- EVar pos typ nameExpr -> do
                -- loc <- evalMaybe "Variable doesn't exists" (M.lookup nameExpr env)
                -- setupArgs pos args exprs (M.insert nameArg loc env)
            -- _ -> throwError "Argument is not a reference"
-- setupArgs pos (n:no) _ _ = do throwError "Not enough arguments"
-- setupArgs pos _ (e:eo) _ = do throwError "Too many arguments"
-- setupArgs _ _ _ env = do return env


evalMaybe :: String -> Maybe a -> Except String a
evalMaybe s Nothing = throwError s
evalMaybe s (Just a) = return a

evalExpr (EVar pos typ name) _ =
    case typ of
        Int _ -> return Intgr
        Bool _ -> return Bl
        Str _ -> return Strln
        _ -> throwError "Incorrect variable typ"

evalExpr (ELitInt _ n) _ = return Intgr
evalExpr (ELitTrue _) _ = return Bl
evalExpr (ELitFalse _) _ = return Bl
evalExpr (EApp pos typ name args) functions = do
    let exprTypes = map (`evalExpr` functions) args in
        let argsTypes = evalMaybe "Function not declared" (M.lookup name functions) in
            let res = cmpTypes exprTypes argsTypes in
                case typ of
                    Int _ -> return Intgr
                    Bool _ -> return Bl
                    Str _ -> return Strln
                    Void _ -> return Empt

evalExpr (EString _ str) _ = return Strln
evalExpr (Neg pos subexpr) functions = do
    val <- evalExpr subexpr functions
    case val of
        Intgr -> return Intgr
        _ -> throwError "Negation of not integer type"
evalExpr (Not pos subexpr) functions = do
    val <- evalExpr subexpr functions
    case val of
         Bl -> return Bl
         _ -> throwError "Boolean negation of this expression is impossible"
evalExpr (EMul pos expr1 mulop expr2) functions = do
    e1 <- evalExpr expr1 functions
    e2 <- evalExpr expr2 functions
    case (e1, e2) of
        (Intgr, Intgr) -> return Intgr
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

evalStmt :: [Stmt] -> Except String ValueType
evalStmt [] = return Empt
evalStmt ((Empty pos):others) = evalStmt others
evalStmt ((Decl pos typ name):others) = evalStmt others
evalStmt ((Ass pos typ name expr):others) = do
    e1 <- evalExpr expr
    case (e1, typ) of
        (Intgr, Int pos) -> evalStmt others
        (Bl, Bool pos) -> evalStmt others
        (Strln, Str pos) -> evalStmt others
        (_, _) -> throwError "Incorrect type assigment"
evalStmt ((Incr pos typ name):others) = do
    case typ of
        (Int _) -> evalStmt others
        _ -> throwError "Impossible to increase"
evalStmt ((Decr pos typ name):others) = do
    case typ of
        (Int _) -> evalStmt others
        _ -> throwError "Impossible to increase"
evalStmt ((Ret pos expr):others) = evalStmt others
evalStmt ((Retv pos):others) = evalStmt others
evalStmt ((Cond pos cond ifstmt):others) = do
    e <- evalExpr cond
    case e of
        l -> evalStmt (ifstmt ++ others)
        _ -> throwError "Condition doesn't have boolean type"
evalStmt ((CondElse pos cond ifstmt elsestmt):others) = do
    e <- evalExpr cond
    case e of
        Bl -> evalStmt ifstmt ++ elsestmt ++ others
        _ -> throwError "Condition doesn't have boolean type"
evalStmt ((While pos cond loop):others) = do
    e <- evalExpr cond
    case e of
        Bl -> evalStmt loop:others
        _ -> throwError "Condition doesn't have boolean type"
evalStmt ((For pos typ name expr1 expr2 loop):others) = do
    e1 <- expr1
    e2 <- expr2
    case (typ, e1, e2) of
        (Int _, Intgr, Intgr) -> evalStmt loop ++ others
        _ -> throwError "Couldn't declare variable with this type in loop"

evalStmt ((SExp pos expr):others) = evalStmt others
evalStmt ((Continue pos):others) = evalStmt others
evalStmtm ((Break pos):others) = evalStmt others