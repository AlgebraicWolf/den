module Spec

import Data.String

import Text.PrettyPrint.Prettyprinter

%default total


------------------------------------------------------------
-- Language specification
------------------------------------------------------------

||| A type for names of the variables.
||| For simplicity, they are natural numbers
public export
data Name = MkName Nat

||| Context a.k.a. a specialised list of names.
public export
data Context : Type where
  Nil : Context
  (::) : Name -> Context -> Context

||| de Brujin index of a name in a context.
public export
data Elem : Context -> Type where
  Here : (nm : Name) -> Elem (nm :: ctx)
  There : Elem ctx -> Elem (nm' :: ctx)

||| Binary operation on integers.
public export
data Op = Add | Sub | Mul

||| Arithmetic expressions that can reference names from context
public export
data Expression : Context -> Type where
  Literal : Int -> Expression ctx
  Variable : Elem ctx -> Expression ctx
  BinOp : Op -> Expression ctx -> Expression ctx -> Expression ctx

||| Language of sequences of assignments.
public export
data Lang : Context -> Type where
  Empty : Lang []
  Assign : (nm : Name) -> Expression ctx -> Lang ctx -> Lang (nm :: ctx)

------------------------------------------------------------
-- Value pretty-printing
------------------------------------------------------------

Pretty Name where
  pretty (MkName n) = "x" <+> pretty n where

Pretty Op where 
  pretty Add = "+"
  pretty Sub = "-"
  pretty Mul = "*"

Pretty (Elem ctx) where
  pretty (Here nm) = pretty nm
  pretty (There elem) = pretty elem

Pretty (Expression ctx) where
  pretty (Literal i) = pretty i
  pretty (Variable elem) = pretty elem
  pretty (BinOp op e e')   = parenIfNeeded (shouldParenLeft op e) (pretty e)
                        <++> pretty op
                        <++> parenIfNeeded (shouldParenRight op e') (pretty e') where
    shouldParenRight : Op -> Expression ctx -> Bool
    shouldParenRight Sub (BinOp Add _ _) = True
    shouldParenRight Sub (BinOp Sub _ _) = True
    shouldParenRight Mul (BinOp Add _ _) = True
    shouldParenRight Mul (BinOp Sub _ _) = True
    shouldParenRight _   (Literal i)     = i < 0
    shouldParenRight _   _               = False

    shouldParenLeft : Op -> Expression ctx -> Bool
    shouldParenLeft Mul (BinOp Add _ _) = True
    shouldParenLeft Mul (BinOp Sub _ _) = True
    shouldParenLeft _   (Literal i)     = i < 0
    shouldParenLeft _   _               = False

    parenIfNeeded : Bool -> Doc ann -> Doc ann
    parenIfNeeded b p = if b then "(" <+> p <+> ")"
                             else p

public export
Pretty (Lang ctx) where
  pretty lang = vsep $ reverse $ pretty' lang where
    pretty' : Lang ctx' -> List (Doc ann)
    pretty' Empty = []
    pretty' (Assign nm expr rest) = (pretty nm <++> "=" <++> pretty expr) :: pretty' rest

