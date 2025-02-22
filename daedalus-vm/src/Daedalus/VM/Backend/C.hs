{-# Language OverloadedStrings, BlockArguments #-}
{-# Language ImplicitParams, ConstraintKinds #-}
{-# Language ParallelListComp #-}
module Daedalus.VM.Backend.C where

import qualified Data.ByteString as BS
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import           Data.Word(Word64)
import           Data.Int(Int64)
import qualified Data.Set as Set
import           Data.Maybe(maybeToList,fromMaybe,mapMaybe)
import           Data.List(partition)
import qualified Data.Text as Text
import           Control.Applicative((<|>))

import Daedalus.PP
import Daedalus.Panic(panic)
import Daedalus.Rec(topoOrder,forgetRecs)

import Daedalus.VM
import qualified Daedalus.Core as Src
import Daedalus.VM.RefCountSane
import Daedalus.VM.TypeRep
import Daedalus.VM.Backend.C.Lang
import Daedalus.VM.Backend.C.Names
import Daedalus.VM.Backend.C.Types
import Daedalus.VM.Backend.C.UserDefined
import Daedalus.VM.Backend.C.Call


{- assumptions on all DDL types:
  * default constructors: for uninitialized block parameters
  * assignment: for passing block parameters
-}

-- XXX: separate output and parser state(input/threads)

-- | Currently returns the content for @(.h,.cpp)@ files.
cProgram :: String -> Program -> (Doc,Doc)
cProgram fileNameRoot prog =
  case checkProgram prog of
    Nothing -> (hpp,cpp)
    Just err -> panic "cProgram" err
  where
  module_marker = text fileNameRoot <.> "_H"

  hpp = vcat $
          [ "#ifndef" <+> module_marker
          , "#define" <+> module_marker
          , " "
          , includes
          , " "
          , let (ds,defs) = unzip (map cTypeGroup allTypes)
            in vcat' (ds ++ defs)
          , " "
          , "// --- Parsing Functions ---"
          , "namespace DDL { namespace ResultOf {"
          ] ++ map declareParserResult (pEntries prog) ++
          [ "}}" ] ++
          [ cStmt (cEntrySig ent) | ent <- pEntries prog ] ++
          primSigs ++
          [ ""
          , "#endif"
          ]

  declareParserResult ent =
    cStmt ("using" <+> nm <+> "=" <+> cSemType (entryType ent))
    where nm = ptext (Text.unpack (entryName ent)) -- Not escaped!

  (prims,noPrims) = flip partition noCapFun \fun ->
                    case vmfDef fun of
                      VMExtern {} -> True
                      VMDef {}    -> False

  primSigs = case prims of
               [] -> []
               _  -> " "
                   : "// --- External Primitives ---"
                   : map cFunSig prims


  cpp = vcat $ [ "#include" <+> doubleQuotes (text fileNameRoot <.> ".h")
               , " "
               ] ++

               map cFunSig noPrims ++
               (let ?allFuns = allFunMap in mapMaybe cFun noCapFun) ++

               [ parserSig <+> "{"
               , nest 2 parserDef
               , "}"
               ] ++
               zipWith cDefineEntry [0..] (pEntries prog)

  parserSig = "static void parser(DDL::Input i0, int entry, DDL::ParseError &err, void* out)"

  orderedModules = forgetRecs (topoOrder modDeps (pModules prog))
  modDeps m      = (mName m, Set.fromList (mImports m))

  allTypes       = concatMap mTypes orderedModules
  allFuns        = concatMap mFuns orderedModules
  allFunMap      = Map.fromList [ (vmfName f, f) | f <- allFuns ]

  (capFuns,noCapFun) = partition ((Capture ==) . vmfCaptures) allFuns

  allBlocks      = Map.unions (map entryBoot (pEntries prog) ++
                          [ vmfBlocks d | f <- capFuns, VMDef d <- [vmfDef f] ])
  doBlock b      = let ?allFuns = allFunMap
                       ?allBlocks = allBlocks
                       ?captures = Capture
                   in cBasicBlock b

  parserDef      = vcat [ "DDL::ParserState p;"
                        , "clang_bug_workaround: void *clang_bug = &&clang_bug_workaround;"
                        , params
                        , cDeclareRetVars capFuns
                        , cDeclareClosures (Map.elems allBlocks)
                        , " "
                        , "// --- States ---"
                        , " "
                        , cSwitch "entry"
                            [ cCase (int i) $ vcat
                                  [ cAssign (cArgUse b i0) "i0"
                                  , cGoto (cBlockLabel bn)
                                  ]
                            | (i,e) <- zip [0..] (pEntries prog)
                            , let bn = entryLabel e
                                  b  = entryBoot e Map.! bn
                                  i0 = head (blockArgs b)
                            ]
                        , " "
                        , vcat' (map doBlock (Map.elems allBlocks))
                        ]


  params         = vcat (map cDeclareBlockParams (Map.elems allBlocks))


  includes =
    vcat [ "#include <ddl/parser.h>"
         , "#include <ddl/input.h>"
         , "#include <ddl/unit.h>"
         , "#include <ddl/bool.h>"
         , "#include <ddl/number.h>"
         , "#include <ddl/integer.h>"
         , "#include <ddl/cast.h>"
         , "#include <ddl/maybe.h>"
         , "#include <ddl/array.h>"
         , "#include <ddl/map.h>"
         ]



type AllFuns    = (?allFuns   :: Map Src.FName VMFun)
type AllBlocks  = (?allBlocks :: Map Label Block)
type CurBlock   = (?curBlock  :: Block)
type Copies     = (?copies    :: Map BV E)
type CaptureFun = (?captures  :: Captures)

cEntrySig :: Entry -> Doc
cEntrySig ent =
  "void" <+> nm <.>
    vcat [ "( DDL::Input input"
         , ", DDL::ParseError &error"
         , "," <+> cInst "std::vector" [ ty ] <+> "&results"
         , ")"
         ]
  where
  nm = text (Text.unpack (entryName ent)) -- Not escaped!
  ty = cSemType (entryType ent)

cDefineEntry :: Int -> Entry -> Doc
cDefineEntry n ent = cEntrySig ent <+> "{" $$ nest 2 body $$ "}"
  where
  body = cStmt (cCall "parser" [ "input", int n, "error", "&results" ])


cDeclareBlockParams :: Block -> CStmt
cDeclareBlockParams b
  | null ps     = empty
  | otherwise   = vcat (header : ps)
  where
  header = "\n// Parameters for" <+> pp (blockName b)
  ps = [ cDeclareVar (cType (getType ba)) (cArgUse b ba) | ba <- blockArgs b ]

{- A function always returns 0 or 1 things, so it should be sufficient
to just have 1 varaible per type.
Alternatively, we could generate separate variables for each function.
-}
cDeclareRetVars :: [VMFun] -> CStmt
cDeclareRetVars funs = vcat (header : retInp : stmts)
  where
  header  = "\n// Varaibles used to return values from functions"
  stmts   = map decl $ Set.toList $ Set.fromList
                                  $ map (Src.fnameType . vmfName) funs
  decl t  = cDeclareVar (cSemType t) (cRetVar (TSem t))

  retInp  = cDeclareVar (cSemType Src.TStream) cRetInput


cDeclareClosures :: [Block] -> CStmt
cDeclareClosures bs =
    vcat' (header : map declareThr (Set.toList threadClos) ++
          map declareRet (Set.toList retClos))
  where
  header = "\n// Types for preserving variables across calls"

  (retClos,threadClos) = foldr addClo (Set.empty,Set.empty) bs

  addClo b (rets,threads) =
    let t  = blockType b
        n  = extraArgs t
        as = map getType (drop n (blockArgs b))
    in case t of
         NormalBlock    -> (rets,threads)
         ReturnBlock how ->
           case how of
             RetYes Capture -> (Set.insert as rets,threads)
             RetNo  Capture -> (Set.insert as rets,threads)
             _              -> (rets,threads)
         ThreadBlock    -> (rets, Set.insert as threads)

  declareRet ts = cClosureClass "DDL::Closure" (cReturnClassName ts) ts
  declareThr ts = cClosureClass "DDL::ThreadClosure"  (cThreadClassName ts) ts



--------------------------------------------------------------------------------

cFunSig :: VMFun -> CDecl
cFunSig fun = cDeclareFun res (cFName (vmfName fun)) args
  where
  res  = if vmfPure fun then retTy else "bool"
  args = if vmfPure fun then normalArgs else retArgs ++ normalArgs
  normalArgs = [ cType (getType x)
               | x <- case vmfDef fun of
                        VMDef d -> blockArgs (vmfBlocks d Map.! vmfEntry d)
                        VMExtern as -> as
               ]

  retTy   = cSemType (Src.fnameType (vmfName fun))
  retArgs = [ "DDL::ParserState&", cPtrT retTy, cPtrT (cSemType Src.TStream) ]

cFun :: (AllFuns) => VMFun -> Maybe CDecl
cFun fun =
  case vmfDef fun of
    VMExtern {} -> Nothing
    VMDef d -> Just (cDefineFun res (cFName (vmfName fun)) args body)
      where
      res  = if vmfPure fun then retTy else "bool"
      args = if vmfPure fun then normalArgs else retArgs ++ normalArgs

      entryBlock = vmfBlocks d Map.! vmfEntry d

      argName n = "a" <.> int n

      normalArgs = [ cType (getType x) <+> argName n
                   | (x,n) <- blockArgs entryBlock `zip` [ 1.. ]
                   ]

      retTy   = cSemType (Src.fnameType (vmfName fun))
      retArgs = [ "DDL::ParserState& p"
                , cPtrT retTy <+> cRetVarFun
                , cPtrT (cSemType Src.TStream) <+> cRetInputFun
                ]

      body   = let ?allBlocks = vmfBlocks d
                   ?captures  = NoCapture
               in map cDeclareBlockParams (Map.elems (vmfBlocks d))
                 ++ [ cAssign (cArgUse entryBlock x) (argName n)
                    | (x,n) <- blockArgs entryBlock `zip` [ 1.. ]
                    ]
                 ++ cGoto (cBlockLabel (vmfEntry d))
                  : [ cBasicBlock b | b <- Map.elems (vmfBlocks d) ]



--------------------------------------------------------------------------------


cBasicBlock :: (AllFuns,AllBlocks,CaptureFun) => Block -> CStmt
cBasicBlock b = "//" <+> text (show (blockType b))
             $$ cBlockLabel (blockName b) <.> ": {" $$ nest 2 body $$ "}"
  where
  body = let ?curBlock = b
             ?copies   = Map.fromList [ (x,v) | Let x v <- blockInstrs b ]
         in getArgs
         $$ vcat (map cBlockStmt (blockInstrs b))
         $$ vcat (cTermStmt (blockTerm b))

  getArgs = case blockType b of
              NormalBlock -> empty

              ReturnBlock how ->
                case how of
                  RetPure -> empty
                  RetNo NoCapture -> empty
                  RetYes NoCapture -> empty
                  bty ->
                    let rn = extraArgs (ReturnBlock bty)
                        (ras,cas) = splitAt rn (blockArgs b)
                        ty = cPtrT (cReturnClassName (map getType cas))
                        regN i v = case how of
                                     RetYes Capture
                                        | i == (0::Int) -> cRetVar (getType v)
                                        | i == 1        -> cRetInput
                                     _ -> panic "getArgs.regN" ["invalid arg"]
                        resultN i v =
                          cAssign (cArgUse b v) (regN i v)
                    in
                    cBlock $
                      zipWith resultN [ 0.. ] ras ++
                      [ cDeclareInitVar ty "clo" (parens ty <.> cCall "p.pop" [])
                      ] ++
                      [ cStmt (cCall ("clo->get" <.> cField n) [ cArgUse b v ])
                      | (v,n) <- cas `zip` [ 0 .. ]
                      ] ++
                      [ cStmt (cCall "clo->free" ["true"]) ]



              ThreadBlock
                | Capture <- ?captures ->
                  let x : xs = blockArgs b
                      ty = cPtrT (cThreadClassName (map getType xs))
                  in
                  cBlock
                    $ cDeclareInitVar ty "clo" (parens ty <.> cCall "p.pop" [])
                    : cAssign (cArgUse b x)(cCall "DDL::Bool" ["clo->notified"])
                    : [ cStmt (cCall ("clo->get" <.> cField n) [ cArgUse b v ])
                      | (v,n) <- xs `zip` [ 0 .. ]
                      ]
                   ++ [ cStmt (cCall "clo->free" ["true"]) ]

                | otherwise -> panic "getArgs" ["Thread block in no-capture?"]





--------------------------------------------------------------------------------

cVarDecl :: BV -> CExpr -> CStmt
cVarDecl v e = cStmt (cType (getType v) <+> cVarUse v <+> "=" <+> e)

cVMVar :: (Copies, CurBlock) => VMVar -> CExpr
cVMVar vmvar =
  case vmvar of
    ArgVar x   -> cArgUse ?curBlock x
    LocalVar x -> case Map.lookup x ?copies of
                    Just e  -> cExpr e
                    Nothing -> cVarUse x

cBlockStmt :: (Copies,CurBlock) => Instr -> CStmt
cBlockStmt cInstr =
  case cInstr of
    Say x           -> cStmt (cCall "p.say"      [ cString x ])
    Output e        -> let t = cPtrT (cInst "std::vector" [ cType (getType e) ])
                           o = parens (parens(t) <.> "out")
                       in cStmt (cCall (o <.> "->push_back") [ cExpr e ])
    Notify e        -> cStmt (cCall "p.notify"   [ cExpr e ])
    NoteFail e      -> cStmt (cCall "p.noteFail" [ cExpr e ])
    Spawn x l       -> cVarDecl x (cCall "p.spawn" [clo])
      where clo = "new" <+> cCall (cThreadClassName (map getType (jArgs l)))
                    ("&&" <.> cBlockLabel (jLabel l) : map cExpr (jArgs l))

    Free xs         -> vcat (cFree xs)

    Let _ e
      | Just v <- eIsVar e -> cStmt (cCall (cVMVar v <.> ".copy") [])
      | otherwise          -> empty

    CallPrim x p es ->
      case p of
        StructCon _ut ->
          let v = cVarUse x
          in vcat [ cDeclareVar (cType (getType x)) v
                  , cStmt (cCallMethod v structCon
                          [ cExpr e | e <- es, getType e /= TSem Src.TUnit ])
                  ]

        NewBuilder _ -> cDeclareVar (cType (getType x)) (cVarUse x)
        Integer n    -> cVarDecl x (cCall "DDL::Integer" [ cString (show n) ])
        ByteArray bs -> cVarDecl x
                              (cCallCon "DDL::Array<DDL::UInt<8>>"
                                ( cCallCon "size_t" [int (BS.length bs)]
                                : [ cCall "DDL::UInt<8>" [ text (show w) ]
                                  | w <- BS.unpack bs
                                  ]
                                ))
        Op1 op1      -> cOp1 x op1 es
        Op2 op2      -> cOp2 x op2 es
        Op3 op3      -> cOp3 x op3 es
        OpN opN      -> cOpN x opN es


cFree :: (CurBlock, Copies) => Set VMVar -> [CStmt]
cFree xs = [ cStmt (cCall (cVMVar y <.> ".free") [])
           | x <- Set.toList xs
           , y <- freeVar' x
           ]
  where
  freeVar' x =
    case x of
      LocalVar y | Just e <- Map.lookup y ?copies -> maybeToList (eIsVar e)
      _                                           -> [x]




cOp1 :: (Copies, CurBlock) => BV -> Src.Op1 -> [E] -> CStmt
cOp1 x op1 ~[e'] =
  case op1 of
    Src.CoerceTo tgtT -> cVarDecl x (cCall fun [e])
      where
      srcT = case getType e' of
               TSem t -> t
               _ -> bad "Expected a semantic type"

      bad :: String -> a
      bad msg = panic "cOp1" [ "Bad coercions"
                             , "from " ++ show (pp srcT)
                             , "to " ++ show (pp tgtT)
                             , msg
                             ]

      sz t = case t of
              Src.TSize i -> integer i
              _           -> bad "Size not an integer"

      fun =
        case srcT of

          Src.TUInt from ->
            case tgtT of
              Src.TInteger  -> cInst "DDL::uint_to_integer" [sz from]
              Src.TUInt to  -> cInst "DDL::uint_to_uint" [sz from, sz to]
              Src.TSInt to  -> cInst "DDL::uint_to_sint" [sz from, sz to]
              _             -> bad "Unexpected target type"

          Src.TSInt from ->
            case tgtT of
              Src.TInteger  -> cInst "DDL::sint_to_integer" [sz from]
              Src.TUInt to  -> cInst "DDL::sint_to_uint" [sz from, sz to]
              Src.TSInt to  -> cInst "DDL::sint_to_sint" [sz from, sz to]
              _             -> bad "Unexpected target type"

          Src.TInteger ->
            case tgtT of
              Src.TInteger  -> cInst "DDL::refl_cast" [cSemType tgtT]
              Src.TUInt to  -> cInst "DDL::integer_to_uint" [sz to]
              Src.TSInt to  -> cInst "DDL::integer_to_sint" [sz to]
              _             -> bad "Unexpected target type"

          _ | srcT == tgtT -> cInst "DDL::refl_cast" [cSemType tgtT]
            | otherwise    -> bad "Unexpected source type"

    Src.IsEmptyStream ->
      cVarDecl x $ cCallMethod e "length" [] <+> "==" <+> "0"

    Src.Head ->
      cVarDecl x $ cCall "DDL::UInt<8>" [ cCallMethod e "iHead" [] ]

    Src.StreamOffset ->
      cVarDecl x $ cCallMethod e "getOffset" []

    Src.StreamLen ->
      cVarDecl x $ cCallMethod e "length" []

    Src.OneOf bs ->
      let v     = cVarUse x
          true  = cAssign v (cCall "DDL::Bool" [ "true" ]) $$ cBreak
          false = cAssign v (cCall "DDL::Bool" [ "false" ])
      in
      vcat
        [ cDeclareVar (cType (getType x)) v
        , cSwitch (cCallMethod e "rep" [])
            $ [ cCase (int (fromEnum b)) true | b <- BS.unpack bs ]
           ++ [ cDefault false ]
        ]

    Src.Neg ->
      cVarDecl x $ "-" <> e

    Src.BitNot ->
      cVarDecl x $ "~" <> e

    Src.Not ->
      cVarDecl x $ "!" <> e

    Src.ArrayLen ->
      cVarDecl x $ cCall (e <.> ".size") []

    Src.Concat ->
      cVarDecl x $ cCall (cType (getType x)) [ e ]

    Src.FinishBuilder ->
      cVarDecl x (cCall (cType (getType x)) [ e ])

    Src.NewIterator  ->
      cVarDecl x $ cCall (cType (getType x)) [ e ]

    Src.IteratorDone ->
      cVarDecl x $ cCallMethod e "done" []

    Src.IteratorKey  ->
      cVarDecl x $ cCallMethod e "key" []

    Src.IteratorVal ->
      cVarDecl x $ cCallMethod e "value" []

    Src.IteratorNext ->
      cVarDecl x $ cCallMethod e "next" []

    Src.EJust ->
      cVarDecl x $ cCall (cType (getType x)) [e]

    Src.FromJust ->
      cVarDecl x $ cCallMethod e "getValue" []

    Src.SelStruct _t l ->
      cVarDecl x $ cCallMethod e (selName GenOwn l) []

    Src.InUnion _ut l ->
      vcat [ cDeclareVar (cType (getType x)) (cVarUse x)
           , cStmt $ cCallMethod (cVarUse x) (unionCon l)
                                      [ e | getType e' /= TSem Src.TUnit ]
           ]

    Src.FromUnion _t l ->
      cVarDecl x $ cCallMethod e (selName GenOwn l) []

  where
  e = cExpr e'


cOp2 :: (Copies,CurBlock) => BV -> Src.Op2 -> [E] -> CDecl
cOp2 x op2 ~[e1',e2'] =
  case op2 of
    Src.IsPrefix -> cVarDecl x (cCallMethod e2 "hasPrefix" [ e1 ])
    Src.Drop     -> cVarDecl x (cCallMethod e2 "iDrop"    [ e1 ])
    Src.Take     -> cVarDecl x (cCallMethod e2 "iTake"    [ e1 ])

    Src.Eq    -> cVarDecl x $ cCallCon "DDL::Bool" [e1 <+> "==" <+> e2]
    Src.NotEq -> cVarDecl x $ cCallCon "DDL::Bool" [e1 <+> "!=" <+> e2]
    Src.Leq   -> cVarDecl x $ cCallCon "DDL::Bool" [e1 <+> "<=" <+> e2]
    Src.Lt    -> cVarDecl x $ cCallCon "DDL::Bool" [e1 <+> "<"  <+> e2]

    Src.Add   -> cVarDecl x (e1 <+> "+" <+> e2)
    Src.Sub   -> cVarDecl x (e1 <+> "-" <+> e2)
    Src.Mul   -> cVarDecl x (e1 <+> "*" <+> e2)
    Src.Div   -> cVarDecl x (e1 <+> "/" <+> e2)
    Src.Mod   -> cVarDecl x (e1 <+> "%" <+> e2)

    Src.BitAnd  -> cVarDecl x (e1 <+> "&" <+> e2)
    Src.BitOr   -> cVarDecl x (e1 <+> "|" <+> e2)
    Src.BitXor  -> cVarDecl x (e1 <+> "^" <+> e2)
    Src.Cat     -> cVarDecl x (cCall (cType (getType x)) [ e1, e2 ])
    Src.LCat    -> cVarDecl x (cCall "DDL::lcat" [ e1, e2 ])
    Src.LShift  -> cVarDecl x (e1 <+> "<<" <+> e2)
    Src.RShift  -> cVarDecl x (e1 <+> ">>" <+> e2)

    Src.ArrayIndex  -> cVarDecl x (cArraySelect e1 e2)
    Src.ConsBuilder -> cVarDecl x (cCall (cType (getType x)) [ e1, e2 ])
    Src.ArrayStream -> cVarDecl x (cCall (cType (getType x)) [e1,e2])

    Src.MapLookup -> cVarDecl x (cCallMethod e1 "lookup" [e2])
    Src.MapMember ->
      cVarDecl x (cCallCon "DDL::Bool" [ cCallMethod e1 "contains" [e2] ])


  where
  e1   = cExpr e1'
  e2   = cExpr e2'


cOp3 :: (Copies,CurBlock) => BV -> Src.Op3 -> [E] -> CDecl
cOp3 x op es =
  case op of
    Src.RangeUp   -> range "rangeUp"
    Src.RangeDown -> range "rangeDown"
    Src.MapInsert -> cVarDecl x (cCallMethod e1 "insert" [ e2, e3 ])
  where
  range m = cVarDecl x (cCall (ty <.> "::" <.> m) [ e1, e2, e3 ])
  [e1,e2,e3] = map cExpr es
  ty = cType (getType x)



cOpN :: (Copies,CurBlock) => BV -> Src.OpN -> [E] -> CDecl
cOpN x op es =
  case op of
    Src.ArrayL t -> cVarDecl x (cCallCon con (len : map cExpr es))
      where con = cSemType (Src.TArray t)
            len = cCallCon "size_t" [ int (length es) ]

    Src.CallF _  -> panic "cOpN" ["CallF"]




--------------------------------------------------------------------------------


cExpr :: (CurBlock,Copies) => E -> CExpr
cExpr expr =
  case expr of
    EBlockArg x   -> cArgUse ?curBlock x
    EVar x        -> case Map.lookup x ?copies of
                       Just e  -> cExpr e
                       Nothing -> cVarUse x
    EUnit         -> cCall "DDL::Unit" []
    EBool b       -> cCall "DDL::Bool" [if b then "true" else "false"]
    ENum n ty     -> cCall f [ integer n ]
      where
      f = case ty of
            Src.TUInt sz -> cInst "DDL::UInt" [ cSizeType sz ]
            Src.TSInt sz -> cInst "DDL::SInt" [ cSizeType sz ]

            _ -> panic "cExpr" [ "Unexpected type for numeric constant"
                               , show (pp ty) ]

    EMapEmpty k v -> cCallCon (cInst "DDL::Map" [ cSemType k, cSemType v ]) []
    ENothing t  -> parens (cCall (cInst "DDL::Maybe" [cSemType t]) [])


--------------------------------------------------------------------------------

cTermStmt :: (AllFuns, AllBlocks, CurBlock, Copies, CaptureFun) =>
  CInstr -> [CStmt]
cTermStmt ccInstr =
  case ccInstr of
    Jump jp -> cJump jp

    JumpIf e (JumpCase opts) -> cDoCase e opts

    Yield ->
      [ cIf (cCall "p.hasSuspended" [])
          [ cGoto ("*" <.> cCall "p.yield" []) ]
          [ cAssign "err.offset" "p.getFailOffset()", "return;" ]
      ]

    ReturnNo ->
      case ?captures of
        Capture   -> [ cGoto ("*" <.> cCall "p.returnNo" []) ]
        NoCapture -> [ "return false;" ]

    ReturnYes e i ->
      case ?captures of
        Capture ->
          [ cAssign (cRetVar (getType e)) (cExpr e)
          , cAssign cRetInput (cExpr i)
          , cGoto ("*" <.> cCall "p.returnYes" [])
          ]
        NoCapture ->
          [ cAssign ("*" <.> cRetVarFun)   (cExpr e)
          , cAssign ("*" <.> cRetInputFun) (cExpr i)
          , "return true;"
          ]

    ReturnPure e ->
      case ?captures of
        Capture ->
          [ cAssign (cRetVar (getType e)) (cExpr e)
          , cGoto ("*" <.> cCall "p.returnPure" [])
          ]
        NoCapture ->
          [ cStmt ("return" <+> cExpr e) ]

    Call f captures no yes es ->
      case captures of
        Capture ->
            doPush no
          : doPush yes
          : case vmfDef (lkpFun f) of
              VMDef d -> cJump (JumpPoint (vmfEntry d) es)
              VMExtern {} -> panic "Capture call to extern" []

        NoCapture ->
          let JumpPoint lYes esYes = yes
              JumpPoint lNo esNo = no
              bYes = ?allBlocks Map.! lYes
              bNo  = ?allBlocks Map.! lNo
              a : i : _ = blockArgs bYes
              call = cCall (cFName f)
                   $ "p"
                   : ("&" <.> cArgUse bYes a)
                   : ("&" <.> cArgUse bYes i)
                   : map cExpr es
          in [ cIf call
                  (freeClo no  ++ cDoJump bYes esYes)
                  (freeClo yes ++ cDoJump bNo  esNo)
            ]

          where freeClo (JumpPoint _ vs) =
                   [ cStmt (cCallMethod (cExpr e) "free" [])
                   | e <- vs, typeRepOf e == HasRefs ]

    -- XXX: this one does not need to be terminal
    CallPure f (JumpPoint lab les) es ->
      case Map.lookup lab ?allBlocks of
        Just b -> zipWith assignP (blockArgs b) (doCall : map cExpr les) ++
                  [ cGoto (cBlockLabel (blockName b)) ]
          where assignP ba = cAssign (cArgUse b ba)
                doCall = cCall (cFName f) (map cExpr es)
        Nothing -> panic "CallPure" [ "Missing block: " ++ show (pp lab) ]


    TailCall f captures es ->
      let fun       = lkpFun f
          retT      = TSem (Src.fnameType f)
          doCall as = cCall (cFName f) (as ++ map cExpr es)
      in
      case (captures, ?captures) of
        (Capture,Capture) ->
          case vmfDef fun of
            VMDef d  ->  cJump (JumpPoint (vmfEntry d) es)
            VMExtern _ -> panic "Tail call" ["Capturing primitive?", showPP f]
        (Capture,NoCapture) -> panic "cBasicBlock" [ "Capture from no-capture" ]

        -- this is not a tail call anymore
        (NoCapture,Capture)
          | vmfPure fun ->
            [ cAssign (cRetVar retT) (doCall [])
            , cGoto ("*" <.> cCall "p.returnPure" [])
            ]

          | otherwise ->
            [ cIf (doCall [ "p", "&" <.> cRetVar retT, "&" <.> cRetInput ])
                  [cGoto ("*" <.> cCall "p.returnYes" [])]
                  [cGoto ("*" <.> cCall "p.returnNo" [])]
            ]

        (NoCapture,NoCapture) ->
            [ cStmt $ "return" <+> doCall args ]

          where
          args
            | vmfPure fun = []
            | otherwise   = [ "p", cRetVarFun, cRetInputFun ]


  where
  lkpFun f = case Map.lookup f ?allFuns of
               Just fun -> fun
               Nothing  -> panic "cTermStmt" [ "Unknown function", show (pp f) ]

  doPush l =
    let clo = cCall (cReturnClassName (map getType (jArgs l)))
                    ("&&" <.> cBlockLabel (jLabel l) : map cExpr (jArgs l))
    in cStmt (cCall "p.push" ["new" <+> clo])


cDoJump :: (Copies,CurBlock,CaptureFun) => Block -> [E] -> [CStmt]
cDoJump b es =
  zipWith assignP as es ++ [ cGoto (cBlockLabel l) ]
  where
  as           = drop (extraArgs (blockType b)) (blockArgs b)
  l            = blockName b
  assignP ba e = cAssign (cArgUse b ba) (cExpr e)


cJump :: (AllBlocks, CurBlock, Copies,CaptureFun) => JumpPoint -> [CStmt]
cJump (JumpPoint l es) =
  case Map.lookup l ?allBlocks of
    Just b  -> cDoJump b es
    Nothing -> panic "cJump" [ "Missing block: " ++ show (pp l) ]

cDoCase :: (AllFuns, AllBlocks, CurBlock, Copies, CaptureFun) =>
           E -> Map Pattern JumpWithFree -> [CStmt]
cDoCase e opts =
  case getType e of
    TSem Src.TBool ->
      check
      do ifTrue  <- lkpOrDflt (PBool True)
         ifFalse <- lkpOrDflt (PBool False)
         pure [ cIf (cCallMethod (cExpr e) "getValue" [])
                    (doChoice ifTrue) (doChoice ifFalse) ]

    TSem (Src.TMaybe _) ->
      check
      do ifNothing <- lkpOrDflt PNothing
         ifJust    <- lkpOrDflt PJust
         pure [ cIf (cCallMethod (cExpr e) "isJust" [])
                    (doChoice ifJust) (doChoice ifNothing) ]

    TSem (Src.TInteger) ->
      check
      do let pats = Map.delete PAny opts
         (PNum lower,_) <- Map.lookupMin pats
         (PNum upper,_) <- Map.lookupMax pats

         -- WARNING: assuming 64-bit arch.
         case () of
           _ | 0 <= lower && upper <= toInteger (maxBound :: Word64) ->
               pure (mkSwitch "asULong" numPat)

             | toInteger (minBound :: Int64) <= lower
             , upper <= toInteger (maxBound :: Int64) ->
               pure (mkSwitch "asSLong" numPat)

              -- Lenar ifs. We could probably do something smarted depending
              -- on the patterns but not sure that it is worted
             | otherwise -> mkBigInt

    TSem (Src.TUInt _)  -> mkSwitch "rep" numPat
    TSem (Src.TSInt _)  -> mkSwitch "rep" numPat
    TSem (Src.TUser {}) -> mkSwitch "getTag" conPat

    ty -> panic "JumpIf" [ "`case` on unexpected type", show (pp ty) ]


  where
  dflt        = Map.lookup PAny opts
  lkpOrDflt p = Map.lookup p opts <|> dflt
  doChoice ch = cFree (freeFirst ch) ++ cJump (jumpTarget ch)

  check = fromMaybe
            (panic "JumpIf" ["Invalid case", "Type: " ++ show (pp (getType e))])

  numPat p = case p of
               PNum n -> integer n
               _ -> panic "numPat" [ "Unexpected", show (pp p) ]

  conPat ~(PCon l) =
    case getType e of
      TSem (Src.TUser ut) -> cSumTagV (Src.utName ut) l
      _ -> panic "cDoCase" [ "conPat on non-user type" ]

  mkSwitch getNum pToCase =
    let addDflt cs = case dflt of
                       Nothing -> cs
                       Just x  -> cs ++ [cDefault $ vcat (doChoice x)]
    in [ cSwitch (cCallMethod (cExpr e) getNum []) $
           addDflt
            [ cCase (pToCase pat) (vcat (doChoice ch))
                            | (pat, ch) <- Map.toList opts, pat /= PAny ]
       ]

  mkBigInt =
    do d <- dflt
       let ce = cExpr e
           ifThis ~(PNum n,ch) el = 
              [ cIf (ce <+> "==" <+> integer n) (doChoice ch) el ]
       pure (foldr ifThis (doChoice d) (Map.toList (Map.delete PAny opts)))



