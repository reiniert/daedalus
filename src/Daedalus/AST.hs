{-# Language OverloadedStrings, DeriveTraversable, RecordWildCards #-}
{-# Language DataKinds, GADTs, KindSignatures, ExistentialQuantification #-}
{-# LANGUAGE TemplateHaskell, DeriveLift #-} -- For deriving ord and eqs
{-# LANGUAGE TypeOperators #-}

module Daedalus.AST where

import Data.Word
import Data.ByteString(ByteString)
import qualified Data.ByteString.Char8 as BS8
import Data.Text(Text)
import qualified Data.Kind as HS
import Data.Function (on)

import Data.Type.Equality
import Data.Parameterized.Classes (OrdF(..)) 
import Data.Parameterized.TH.GADT
import Language.Haskell.TH.Syntax(Lift(..))

import Daedalus.PP
import Daedalus.SourceRange
import Daedalus.Rec
import Daedalus.GUID
import Daedalus.Panic


data Name = forall ctx.
  Name { nameScopedIdent :: ScopedIdent
       , nameContext     :: Context ctx
       , nameRange       :: SourceRange
       , nameID          :: !GUID
       }

type ModuleName = Text
type Ident = Text
type Label = Text

data ScopedIdent = Unknown Ident | Local Ident | ModScope ModuleName Ident
  deriving (Ord, Eq, Show, Lift)

isLocalName :: Name -> Bool
isLocalName n =
  case nameScopedIdent n of
    Local {} -> True
    _        -> False

primName :: Text -> Text -> Context c -> Name
primName m x c = Name (ModScope m x) c synthetic invalidGUID

instance PP ScopedIdent where
  pp x = case x of
           Unknown  n -> pp n
           Local    n -> pp n
           ModScope m n -> pp m <> "." <> pp n

instance Show Name where
  show Name { .. } =
    "Name { nameScopedIdent = " ++ show nameScopedIdent ++ ", " ++
           "nameContext = " ++ show nameContext ++ ", " ++
           "nameRange = " ++ show nameRange ++ ", " ++ 
           "nameID = " ++ show nameID ++ " }"

nameScopeAsUnknown :: Name -> Ident
nameScopeAsUnknown n =
  case nameScopedIdent n of
    Unknown t -> t
    _         -> panicRange n "Expecting an Unknown name scope." [] 

nameScopeAsLocal :: Name -> Ident
nameScopeAsLocal n =
  case nameScopedIdent n of
    Local  t -> t
    _         -> panicRange n "Expecting a Local name scope." [] 


nameScopeAsModScope :: Name -> (ModuleName, Ident)
nameScopeAsModScope n =
  case nameScopedIdent n of
    ModScope m t -> (m, t)
    _            -> panicRange n "Expecting an ModScope name scope." [] 


-- These instances are a bit odd as if either are invalid, then we
-- fall back to the idents.  This is a bit fragile, so we are assuming
-- that we only compare a name with an invalid GUID to noe with a
-- valid GUID for things like hand-rolled names (e.g. Main).
instance Eq Name where
  x == y
    | nameID x == invalidGUID || nameID y == invalidGUID = nameScopedIdent x == nameScopedIdent y
    | otherwise = nameID x == nameID y
      
instance Ord Name where
  compare x y 
    | nameID x == invalidGUID || nameID y == invalidGUID = compare (nameScopedIdent x) (nameScopedIdent y)
    | otherwise = compare (nameID x) (nameID y)

instance PP Name where
  pp = pp . nameScopedIdent


-- Name for an implcit parameter.  Note that these are not resolvd like
-- normal names as they are effectively global.
data IPName = forall ctx. IPName
  { ipName    :: Ident
  , ipContext :: Context ctx
  , ipRange   :: SourceRange
  }

instance Eq IPName where
  x == y = ipName x == ipName y

instance Ord IPName where
  compare x y = compare (ipName x) (ipName y)

instance PP IPName where
  pp = pp . ipName

instance Show IPName where
  show IPName { .. } =
    "IPName { ipName = "    ++ show ipName ++ ", " ++
             "ipContext = " ++ show ipContext ++ ", " ++
             "ipRange = "   ++ show ipContext ++ " }"

instance HasRange IPName where
  range = ipRange




data Module = Module { moduleName    :: ModuleName
                     , moduleImports :: [Located ModuleName]
                     , moduleBitData :: [BitData] -- ordered
                     , moduleRules   :: [Rec Rule]
                     } deriving Show

data Decl = DeclRule Rule | DeclBitData BitData

data Rule =
  Rule { ruleName     :: !Name
       , ruleParams   :: ![RuleParam]
       , ruleResTy    :: !(Maybe SrcType)
       , ruleDef      :: !(Maybe Expr)
       , ruleRange    :: !SourceRange
       } deriving Show

data RuleParam = RuleParam
  { paramName :: Name
  , paramType :: Maybe SrcType
  } deriving Show

instance HasRange RuleParam where
  range p = case paramType p of
              Nothing -> range (paramName p)
              Just t  -> paramName p <-> t

data BitData =
  BitData { bdName  :: !Name
          , bdCtors :: ![ (Located Label, [ Located BitDataField ] ) ]
          , bdRange :: !SourceRange
          } deriving Show

data BitDataField =
  BDFLiteral Integer       (Maybe SrcType)
  | BDFField Label         (Maybe SrcType)
  | BDFWildcard            (Maybe SrcType)
  deriving Show

data Ctx = Grammar | Value | Class
  deriving (Eq,Show)

type Grammar = 'Grammar
type Value   = 'Value
type Class   = 'Class

data Context :: Ctx -> HS.Type where
  AGrammar :: Context Grammar
  AValue   :: Context Value
  AClass   :: Context Class

-- XXX: use parametrized-utils classes?
sameContext :: Context a -> Context b -> Maybe (a :~: b)
sameContext x y =
  case (x,y) of
    (AGrammar,AGrammar) -> Just Refl
    (AValue,AValue)     -> Just Refl
    (AClass,AClass)     -> Just Refl
    _                   -> Nothing

instance Show (Context ctx) where
  show ctx =
    case ctx of
      AGrammar -> "AGrammar"
      AValue   -> "AValue"
      AClass   -> "AClass"



data ExprF e =
    ELiteral    !Literal
  | ENothing
  | EJust       !e
  | EStruct     ![StructField e]
  | EArray      ![e]
  | EChoiceU    !Commit !e !e
  | EChoiceT    !Commit [UnionField e]
  | EIn         !(UnionField e)    -- make a value of a union type
  | EApp        !Name [e]
  | EVar        !Name
  | EImplicit   !IPName
  | ETry        !e
  | ECase       !Expr [PatternCase e]

  | EMatch !e
  | EMatch1 !e
  | EAnyByte
  | EOptional !Commit  !e
  | EMany !Commit !(ManyBounds e) !e
  | EEnd
  | EOffset

  | EHasType !SigType !e !SrcType

  -- Modify semantic value
  | EQuiet      !e

  -- Maps
  | EMapEmpty
  | EMapInsert   !e !e !e
  | EMapLookup   !e !e

  -- Array operations
  | EArrayLength !e
  | EArrayIndex  !e !e  -- x[y], partial so a grammar

  | EPure !e
  | EFail !e

  | EFor !(FLoopFlav e) !(Maybe Name) !Name !e !e

  | EIf         !e !e !e

  | EInRange    !(Maybe e) !(Maybe e)
  | ETriOp      !TriOp !e !e !e
  | EBinOp      !BinOp !e !e
  | EUniOp      !UniOp !e
  | ESel        !e !Selector

  -- Stream
  | ECurrentStream
  | ESetStream !e
  | EStreamLen !e !e
  | EStreamOff !e !e
    deriving Show

-- | Different flavors of loop
data FLoopFlav e = FFold !Name e
                 | FMap
  deriving Show

data Commit = Commit | Backtrack
  deriving (Eq, Show, Lift)

data SigType = MatchType | CoerceSafe | CoerceCheck | CoerceForce
  deriving Show

data TriOp = RangeUp | RangeDown
  deriving (Show,Eq)

data BinOp = Add | Sub | Mul | Div | Mod
           | Lt | Eq | NotEq | Leq | Cat | LCat
           | LShift | RShift | BitwiseAnd | BitwiseOr | BitwiseXor
           | LogicAnd | LogicOr
           | ArrayStream
  deriving (Show, Eq)

data UniOp = Not | Neg | Concat | BitwiseComplement
  deriving (Show, Eq)

data Selector = SelStruct (Located Label)
              | SelUnion (Located Label)
              | SelTrue | SelFalse
              | SelNothing | SelJust
  deriving Show

data ManyBounds e =
    Exactly e
  | Between (Maybe e) (Maybe e)
    deriving (Show, Functor, Foldable, Traversable)

data UnionField e = !(Located Label) :> !e
                    deriving Show

data StructField e =
    Anon      !e
  | !Name :=  !e
  | !Name :@= !e
  | !IPName :?= !e
  | COMMIT SourceRange
    deriving (Show, Functor, Foldable, Traversable)

data Literal = 
    LNumber     !Integer
  | LBool       !Bool
  | LBytes      !ByteString
  | LByte       !Word8
    deriving (Show, Eq, Ord)


-- Non empty
data PatternCase e =
    PatternDefault e
  | PatternCase ![Pattern] !e
    -- ^ A union of patterns. The union should not be empty.
  deriving (Show, Functor)

data Pattern =
    LitPattern (Located Literal)
  | ConPattern (Located Con) Pattern
  | WildPattern SourceRange
  | VarPattern Name
  deriving Show

data Con =
    ConUser Label
  | ConNothing
  | ConJust
    deriving Show

newtype Expr = Expr (Located (ExprF Expr))
               deriving Show

exprValue :: Expr -> ExprF Expr
exprValue (Expr e) = thingValue e

pExprAt :: HasRange r => r -> ExprF Expr -> Expr
pExprAt r e = Expr Located { thingRange = range r, thingValue = e }


data Located a = Located { thingRange :: SourceRange
                         , thingValue :: a
                         } deriving (Show, Functor, Foldable, Traversable)

instance Eq a => Eq (Located a) where
  (==) = (==) `on` thingValue


data TypeF t =
    TGrammar !t
  | TFun t t
  | TStream
  | TByteClass
  | TNum !Integer
  | TUInt !t
  | TSInt !t
  | TInteger
  | TBool
  | TUnit
  | TArray !t
  | TMaybe !t
  | TMap   !t !t
    deriving (Eq,Show,Functor,Foldable,Traversable)

data SrcType = SrcVar Name
             | SrcType (Located (TypeF SrcType))
              deriving Show

--------------------------------------------------------------------------------
instance HasRange (Located a) where
  range = thingRange

instance HasRange Expr where
  range (Expr e) = range e

instance HasRange Name where
  range = nameRange

instance HasRange SrcType where
  range ty =
    case ty of
      SrcVar x -> range x
      SrcType x -> range x

instance HasRange Pattern where
  range pat =
    case pat of
      LitPattern l -> range l
      ConPattern c p -> range c <-> range p
      WildPattern r -> r
      VarPattern r -> range r

instance HasRange BitData where
  range = bdRange

--------------------------------------------------------------------------------

instance PP (Context ctx) where
  pp c =
    case c of
      AGrammar   -> "a grammar"
      AValue     -> "a semantic value"
      AClass     -> "a byte predicate"

instance PP Commit where
  pp c = case c of
           Commit    -> "biased"
           Backtrack -> "fair"


instance PP a => PP (Located a) where
  ppPrec n = ppPrec n . thingValue

instance PP e => PP (ManyBounds e) where
  pp bnds =
    case bnds of
      Exactly e -> brackets (pp e)
      Between Nothing Nothing -> "[]"
      Between a b -> "[" <+> ppMb a <+> ".." <+> ppMb b <+> "]"
        where ppMb = maybe empty pp

instance PP RuleParam where
  pp p = case paramType p of
           Nothing -> pp (paramName p)
           Just t -> parens (pp (paramName p) <+> ":" <+> pp t)

instance PP TriOp where
  pp op =
    case op of
      RangeUp -> "rangeUp"
      RangeDown -> "rangeDown"

instance PP BinOp where
  pp op =
    case op of
      Add -> "+"
      Sub -> "-"
      Mul -> "*"
      Div -> "/"
      Mod -> "%"
      Lt  -> "<"
      Eq ->  "=="
      NotEq -> "!="
      Leq -> "<="
      Cat -> "#"
      LCat -> "<#"
      LShift -> "<<"
      RShift -> ">>"
      BitwiseAnd -> ".&."
      BitwiseOr  -> ".|."
      BitwiseXor -> ".^."
      LogicAnd -> "&&"
      LogicOr  -> "||"
      ArrayStream -> "arrayStream"

instance PP UniOp where
  pp op =
    case op of
      Not    -> "!"
      Neg    -> "-"
      Concat -> "concat"
      BitwiseComplement -> "~"

instance PP Selector where
  pp sel = case sel of
             SelStruct x -> pp x
             SelUnion x -> pp x
             SelTrue -> "true"
             SelFalse -> "false"
             SelNothing -> "nothing"
             SelJust -> "just"

instance PP t => PP (TypeF t) where
  ppPrec n ty =
    case ty of
      TGrammar t -> wrapIf (n > 1) ("Grammar" <+> ppPrec 2 t)
      TFun t1 t2 -> wrapIf (n > 0) (fsep [ ppPrec 1 t1, "->", ppPrec 0 t2 ])
      TByteClass -> "ByteClass"
      TStream    -> "Stream"
      TNum t     -> pp t
      TUInt t    -> wrapIf (n > 1) ("uint" <+> ppPrec 2 t)
      TSInt t    -> wrapIf (n > 1) ("sint" <+> ppPrec 2 t)
      TInteger   -> "int"
      TBool      -> "bool"
      TUnit      -> "{}"
      TArray t   -> brackets (pp t)
      TMaybe t   -> wrapIf (n > 1) ("Maybe" <+> ppPrec 2 t)
      TMap kt vt -> wrapIf (n > 1) ("Map" <+> ppPrec 2 kt <+> ppPrec 2 vt)


instance PP Literal where
  pp lit =
    case lit of
      LByte b   -> text (show (toEnum (fromEnum b) :: Char))
      LNumber i -> integer i      
      LBool i   -> if i then "true" else "false"
      LBytes b  -> text (show (BS8.unpack b))
      

$(return [])

    -- case (c1, c2) of
    --   (AGrammar, AGrammar) -> Just Refl
    --   (AValue, AValue)     -> Just Refl
    --   (AClass, AClass)     -> Just Refl
    --   _                    -> Nothing

instance TestEquality Context where
  testEquality = $(structuralTypeEquality [t| Context |] [])

instance OrdF Context where
  compareF = $(structuralTypeOrd [t| Context |] [])

instance PP SrcType where
  ppPrec n ty = case ty of
                  SrcVar x -> ppPrec n x
                  SrcType l -> ppPrec n (thingValue l)



