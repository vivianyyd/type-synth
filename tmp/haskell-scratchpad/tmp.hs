{-# LANGUAGE FlexibleContexts #-}

import Language.Haskell.Exts
import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.SrcLoc
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Extension

-- Transform expressions: desugar do notation and infix expressions
desugar :: Exp SrcSpanInfo -> Exp SrcSpanInfo
desugar (Do l stmts) = foldr desugarStmt (Var l (UnQual l (Ident l "return"))) stmts
  where
    desugarStmt :: Stmt SrcSpanInfo -> Exp SrcSpanInfo -> Exp SrcSpanInfo
    desugarStmt (Generator _ pat expr) acc =
        InfixApp l expr (QVarOp l (UnQual l (Symbol l ">>="))) (Lambda l [pat] acc)
    desugarStmt (Qualifier _ expr) acc =
        InfixApp l expr (QVarOp l (UnQual l (Symbol l ">>"))) acc
    desugarStmt (LetStmt _ (BDecls _ decls)) acc =
        Let l (BDecls l decls) acc
    desugarStmt _ acc = acc

desugar (InfixApp l e1 op e2) =
    App l (App l (QVarOp l op) e1) e2
desugar (App l e1 e2) =
    App l (desugar e1) (desugar e2)
desugar (Lambda l pats e) =
    Lambda l pats (desugar e)
desugar (Let l binds e) =
    Let l binds (desugar e)
desugar (If l e1 e2 e3) =
    If l (desugar e1) (desugar e2) (desugar e3)
desugar (Case l e alts) =
    Case l (desugar e) (map desugarAlt alts)
  where
    desugarAlt (Alt l pat rhs mbinds) =
        Alt l pat (desugarRhs rhs) mbinds
    desugarRhs (UnGuardedRhs l e) = UnGuardedRhs l (desugar e)
    desugarRhs (GuardedRhss l grhss) =
        GuardedRhss l (map (\(GuardedRhs l gs e) -> GuardedRhs l gs (desugar e)) grhss)
desugar other = other

main :: IO ()
main = do
    let code = "main = do { x <- getLine; putStrLn x }"
    case parseExpWithMode defaultParseMode code of
        ParseOk expr -> putStrLn $ prettyPrint (desugar expr)
        ParseFailed loc msg -> putStrLn $ "Parse error at " ++ show loc ++ ": " ++ msg

