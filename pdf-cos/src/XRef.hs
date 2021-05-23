{-# Language TypeApplications, DataKinds #-}
{-# Language FlexibleContexts, ConstraintKinds #-}
{-# Language OverloadedStrings #-}
module XRef
  ( findStartXRef
  , parseXRefs1
  , parseXRefs2
  , printObjIndex
  , printIncUpdateReport
  )
  where

import Data.Char(isSpace,isNumber)
import Data.Foldable(foldlM)
import qualified Data.Map as Map
import qualified Data.ByteString.Char8 as BS
import Control.Monad(unless,forM,forM_,foldM)
import Control.Applicative((<|>))
import GHC.Records(HasField, getField)

import Text.PrettyPrint

import RTS.Vector(Vector,toList,VecElem)
import RTS.Numeric
import RTS.Input(advanceBy)

import PdfMonad
import PdfParser
import PdfPP

---- types -------------------------------------------------------------------

-- an incremental update (or the base DOM)
data IncUpdate = IU { iu_offset  :: Int  -- offset of this IU
                    , iu_type    :: XRefType
                    , iu_xrefs   :: [[XRefEntry]]
                    , iu_trailer :: TrailerDict
                    }

data XRefType = XRefTable  
              | XRefStream  -- newer alternative to XRef table
              deriving (Eq,Ord,Show)


---- utilities ---------------------------------------------------------------

runParserWithoutObjects :: DbgMode => Input -> Parser a -> IO (PdfResult a)
runParserWithoutObjects i p = 
  runParser (error "Unexpected ObjIndex reference") Nothing p i
    -- the parser should not be attempting to deref any objects!
  
---- xref table: parse and construct -----------------------------------------

-- | Construct the xref map (and etc), version 2
parseXRefs2 :: DbgMode => Input -> Int -> IO (PdfResult ([IncUpdate], ObjIndex, TrailerDict))
parseXRefs2 inp off0 =
  runParserWithoutObjects inp $
    do
    updates <- parseAllIncUpdates inp off0
    validateFirstUpdate (head updates)
    
    -- create object index (oi) map:
    oi <- foldlM
            (\oi iu-> do oi' <- convertSubSectionsToObjMap (iu_xrefs iu)
                         return (Map.union oi' oi)
                                -- NOTE: Map.union is left-biased.
            )
            Map.empty
            updates
    pure (updates, oi, iu_trailer(last updates))

    -- updates == [base,upd1,upd2,...]
    -- length(updates) >= 1
    -- FIXME[F2]: validate that trailers are consistent

  where
    
  convertSubSectionsToObjMap :: [[XRefEntry]] -> Parser ObjIndex
  convertSubSectionsToObjMap xrefss =
    do objMaps  <- mapM xrefEntriesToMap xrefss
       let objMap = Map.unions objMaps
       unless (Map.size objMap == sum (map Map.size objMaps))
           (pError FromUser "convertSubSectionsToObjMap"
                   "Duplicate entries in xref section")
       pure objMap

validateFirstUpdate :: IncUpdate -> Parser ()
validateFirstUpdate iu =
  do
  let xrefss = iu_xrefs iu
  unless (length xrefss == 1) $
    err "must have only one subsection"

    -- Section 7.5.4: For a PDF file that has never been incrementally
    -- updated, the cross-reference section shall contain only one subsection,
    -- whose object numbering begins at 0.

  let [xrefs] = xrefss
  case xrefs of
    []                     -> err "must not be empty"
    Free 0 (R _ 65535) : _ -> return ()
    _                      -> err "first object must be 0, free, generation 65535"

    -- The first entry in the table (object number 0) shall always be free and
    -- shall have a generation number of 65,535;

    -- [first entry] shall be the head of the linked list of free objects.
    -- The last free entry (the tail of the linked list) links back to object number 0.

  case [ g | InUse (R _ g) _ <- xrefs, g /= 0] of
    _:_ -> err "objects exist without generation number 0"
    []  -> return ()

    -- Except for object number 0, all objects in the cross-reference table
    -- shall initially have generation numbers of 0.
       
  where
  err s = pError FromUser "validateFirstUpdate" ("first xref table: " ++ s)

---- parsing IncUpdates ------------------------------------------------------

parseAllIncUpdates :: Input -> Int -> Parser [IncUpdate]
parseAllIncUpdates inp offset0 =
  do
  (x, next) <- parseOneIncUpdate inp offset0
  case next of
    Just offset -> (++[x]) <$> parseAllIncUpdates inp offset
    Nothing     -> return [x]
  

parseOneIncUpdate :: Input -> Int -> Parser (IncUpdate, Maybe Int)
parseOneIncUpdate inp offset = 
  case advanceBy (intToSize offset) inp of
    Just i ->
      do pSetInput i
         refSec <- pCrossRef  -- slight misnomer, this parses
                              --   - standard xref table OR xref streams
                              --   - the trailer too (in the former case)
         case refSec of
           CrossRef_oldXref x -> processTrailer XRefTable  x
           CrossRef_newXref x -> processTrailer XRefStream x
    Nothing -> pError FromUser "parseOneIncUpdate'"
                 ("Offset out of bounds: " ++ show offset)

  where
  
  processTrailer :: ( VecElem s
                    , HasField "trailer" x TrailerDict
                    , HasField "xref"    x (Vector s)
                    , XRefSection s e o
                    ) => XRefType -> x -> Parser (IncUpdate, Maybe Int)
  processTrailer xrefType x =
    do let t = getField @"trailer" x
       prev <- case getField @"prev" t of
                 Nothing -> pure Nothing
                 Just i ->
                    case toInt i of
                      Nothing  -> pError FromUser "parseTrailer"
                                                  "Prev offset too large."
                      Just offset' ->
                          if offset' < offset then
                            pure (Just offset')
                          else
                            -- this ensures no infinite loop:
                            pError FromUser "parseTrailer"
                              (unwords ["Prev offset", show offset'
                                       ,"does not precede offset", show offset
                                       ,"in file."
                                       ])
                           
       xrefss <- mapM convertToXRefEntries (toList (getField @"xref" x))
       return ( IU{ iu_offset = offset
                  , iu_type   = xrefType
                  , iu_xrefs  = xrefss
                  , iu_trailer= t
                  }
              , prev
              )


---- report ------------------------------------------------------------------

printIncUpdateReport :: [IncUpdate] -> IO ()
printIncUpdateReport updates =
  do
  let us = zip ("initial DOM" : map (\n->"incremental update " ++ show (n::Int)) [1..])
               updates 
  forM_ us $
    \(nm,iu)->
      do
      mapM_ putStrLn [ nm ++ ":"
                     , "  " ++ show (iu_type iu)
                     , "  starts at byte offset " ++ show (iu_offset iu)
                     , "  xref entries:"
                     ]
      printXRefs 4 (iu_xrefs iu)
      putStrLn "  trailer dictionary:"
      print (nest 4 $ pp (iu_trailer iu))


printXRefs :: Int -> [[XRefEntry]] -> IO ()
printXRefs indent ess =
  print
  $ nest indent
  $ ppBlock "[" "]"
     [ ppBlock "[" "]" (map ppXRefEntry es) | es <- ess]
  
-- | printObjIndex - NOTE prints the Map/Index abstraction (not the entries)
printObjIndex :: Int -> ObjIndex -> IO ()
printObjIndex indent oi = print
                          $ nest indent
                          $ ppBlock "[" "]" (map ppXRef (Map.toList oi))


---- xref table: parse and construct (old version) ---------------------------

-- | Construct the xref table, version 1

parseXRefs1 :: DbgMode => Input -> Int -> IO (PdfResult (ObjIndex, TrailerDict))
parseXRefs1 inp off0 = runParser Map.empty Nothing (go Nothing (Just off0)) inp
  where
  go :: Maybe TrailerDict -> Maybe Int -> Parser (ObjIndex, TrailerDict)
  go mbRoot Nothing =
    do oix <- getObjIndex
       case mbRoot of
         Just r -> return (oix, r)
         Nothing -> pError FromUser "parseXRefs.go" "Missing document root."

  go mbRoot (Just offset) =
    case advanceBy (intToSize offset) inp of
      Just i ->
        do pSetInput i
           refSec <- pCrossRef
           case refSec of
             CrossRef_oldXref x -> goWith mbRoot x
             CrossRef_newXref x -> goWith mbRoot x
      Nothing -> pError FromUser "parseXRefs.go"
                  ("Offset out of bounds: " ++ show offset)

  goWith :: ( VecElem s
            , HasField "trailer" x TrailerDict
            , HasField "xref"    x (Vector s)
            , XRefSection s e o
            ) => Maybe TrailerDict -> x -> Parser (ObjIndex, TrailerDict)
  goWith mbRoot x =
    do let t = getField @"trailer" x
       prev <- case getField @"prev" t of
                 Nothing -> pure Nothing
                 Just i ->
                    case toInt i of  -- XXX: remember previous offsets
                                     -- to ensure we are not stuck in a loop.
                      Nothing -> pError FromUser "parseXRefs.goWith(1)"
                                                 "Prev offset too large."
                      Just off -> pure (Just off)

       tabs <- mapM (\s->convertToXRefEntries s >>= xrefEntriesToMap)
                    (toList (getField @"xref" x))
       let entries = Map.unions tabs
       unless (Map.size entries == sum (map Map.size tabs))
         (pError FromUser "parseXRefs.goWith(2)" "Duplicate entries in xref section")

       let newRoot = mbRoot <|> Just t

       extendObjIndex entries (go newRoot prev)
         -- entries may be shadowing previous entries
         -- note that the 'entries' are being added, in order, from the top of the file
         -- and in the reverse order in which 'extensions' would be applied.

type XRefSection s e o =
  ( VecElem e
  , HasField "firstId" s Integer
  , HasField "entries" s (Vector e)
  , SubSectionEntry e
  )

class SubSectionEntry t where
  processEntry :: Int -> t -> Parser XRefEntry

data XRefEntry = InUse R ObjLoc
               | Free  Int R     -- object is next free object, generation
               | Null    

ppXRefEntry :: XRefEntry -> Doc
ppXRefEntry x =
  case x of
    InUse (R o g) loc -> "inuse" <+> ppHDict [ "obj:" <+> pp o
                                             , "gen:" <+> pp g
                                             , ppObjLoc loc
                                             ]
    Free obj (R n g)  -> "free " <+> ppHDict [ "obj:" <+> pp obj
                                             , "next:" <+> pp n
                                             , "gen:" <+> pp g
                                             ]
    Null              -> "null"
      
instance SubSectionEntry XRefObjEntry where
  processEntry o t =
    case t of
      XRefObjEntry_inUse u ->
        do off <- integerToInt (getField @"offset" u)
           g   <- integerToInt (getField @"gen" u)
           pure $ InUse R{ refObj = o, refGen = g} (InFileAt off)

      XRefObjEntry_compressed u ->
        do cnt <- integerToInt (getField @"container_obj" u)
           let ref x = R { refObj = x, refGen = 0 }
           i <- integerToInt (getField @"obj_index" u)
           pure $ InUse (ref o) (InObj (ref cnt) i)

      XRefObjEntry_free u ->
        do obj <- integerToInt (getField @"obj" u)
           g   <- integerToInt (getField @"gen" u)
           pure $ Free o R{ refObj = obj, refGen = g}
      XRefObjEntry_null {} -> pure Null

instance SubSectionEntry CrossRefEntry where
  processEntry o t =
    case t of
      CrossRefEntry_inUse u ->
        do g   <- integerToInt (getField @"gen" u)
           off <- integerToInt (getField @"offset" u)
           pure $ InUse (R { refObj = o, refGen = g }) (InFileAt off)

      CrossRefEntry_free u ->
        do g   <- integerToInt (getField @"gen" u)
           obj <- integerToInt (getField @"obj" u)
           pure $ Free o R{ refObj = obj, refGen = g }

  {- Note the file offset and generation will never really fail
     because in the format the offset is a 10 digit number, which
     always fits in a 64-bit Int.  We still need the check to get the types
     to work out, and this also makes the code more portable, in theory.
  -}

-- | Join together the entries into a single xref sub-section
--    - merging XRefObjEntry and CrossRefEntry into XRefEntry
convertToXRefEntries :: XRefSection s e o => s -> Parser [XRefEntry]
convertToXRefEntries xrs =
  forM (zip [ getField @"firstId" xrs .. ]
             (toList (getField @"entries" xrs))) $
       \(n,e)->     
          do o <- integerToInt n
             processEntry o e

-- | Create an Obj Index Map from the XRefEntry list
xrefEntriesToMap :: [XRefEntry] -> Parser ObjIndex
xrefEntriesToMap = foldM entry Map.empty
  where
  entry mp xref =
       case xref of
         Free{} -> pure mp   
         Null   -> pure mp   -- XXX: This skips compressed objects. ??
         InUse ref oi ->
           let (exists,newMap) = Map.insertLookupWithKey (\_ x _ -> x) ref oi mp
           in case exists of
                Nothing -> pure newMap
                Just _  ->
                  pError FromUser "xrefEntriesToMap.entry"
                                  ("Multiple entries for " ++ show ref)


integerToInt :: Integer -> Parser Int
integerToInt i =
  case toInt i of
    Nothing -> pError FromUser "integerToInt" "Integer constant too large."
    Just x  -> pure x


--------------------------------------------------------------------------------

-- Pretty gross
findStartXRef :: BS.ByteString -> Either String Int
findStartXRef bs
  | BS.null post   = Left "Couldn't find EOF"
  | not (BS.isPrefixOf (BS.reverse "startxref") (BS.dropWhile isSpace rest)) =
      Left "Couldn't find startxref"
  | otherwise      = Right $ read $ BS.unpack $ BS.reverse numBits
  where
  eof             = "%%EOF"
  (_pre, post)    = BS.breakSubstring (BS.reverse eof) (BS.reverse lastChunk)
  (numBits, rest) = BS.span isNumber
                  $ BS.dropWhile isSpace
                  $ BS.drop (BS.length eof) post

  len             = BS.length bs

  -- Leave 100 bytes for number and startxref (FIXME)
  lastChunk       = BS.drop (len - 1024 - BS.length eof - 100) bs



