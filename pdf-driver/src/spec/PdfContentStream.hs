{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# Language TypeOperators #-}
{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleInstances #-}
{-# Language StandaloneDeriving #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language OverloadedStrings #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
module PdfContentStream where
 
import qualified PdfMonad as D
import qualified PdfValue
import qualified Prelude as HS
import qualified GHC.TypeLits as HS
import qualified GHC.Records as HS
import qualified Control.Monad as HS
import qualified RTS as RTS
import qualified RTS.Input as RTS
import qualified RTS.Map as Map
import qualified RTS.Vector as Vector
 
 
data ColourOp_0
  = ColourOp_0 (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq ColourOp_0
 
deriving instance HS.Ord ColourOp_0
 
deriving instance HS.Show ColourOp_0
 
instance RTS.DDL ColourOp_0 where
 
instance HS.HasField "nm" ColourOp_0
           (Vector.Vector (RTS.UInt 8)) where
  getField (ColourOp_0 x) = x
 
data ColourOp_1
  = ColourOp_1 (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq ColourOp_1
 
deriving instance HS.Ord ColourOp_1
 
deriving instance HS.Show ColourOp_1
 
instance RTS.DDL ColourOp_1 where
 
instance HS.HasField "nm" ColourOp_1
           (Vector.Vector (RTS.UInt 8)) where
  getField (ColourOp_1 x) = x
 
data ColourOp_2
  = ColourOp_2 (Vector.Vector PdfValue.Number)
  
 
deriving instance HS.Eq ColourOp_2
 
deriving instance HS.Ord ColourOp_2
 
deriving instance HS.Show ColourOp_2
 
instance RTS.DDL ColourOp_2 where
 
instance HS.HasField "cs" ColourOp_2
           (Vector.Vector PdfValue.Number) where
  getField (ColourOp_2 x) = x
 
data ColourOp_3
  = ColourOp_3 (Vector.Vector PdfValue.Number)
  
 
deriving instance HS.Eq ColourOp_3
 
deriving instance HS.Ord ColourOp_3
 
deriving instance HS.Show ColourOp_3
 
instance RTS.DDL ColourOp_3 where
 
instance HS.HasField "cs" ColourOp_3
           (Vector.Vector PdfValue.Number) where
  getField (ColourOp_3 x) = x
 
data ColourOp_4
  = ColourOp_4 (Vector.Vector PdfValue.Number)
  
 
deriving instance HS.Eq ColourOp_4
 
deriving instance HS.Ord ColourOp_4
 
deriving instance HS.Show ColourOp_4
 
instance RTS.DDL ColourOp_4 where
 
instance HS.HasField "cs" ColourOp_4
           (Vector.Vector PdfValue.Number) where
  getField (ColourOp_4 x) = x
 
data ColourOp_5
  = ColourOp_5 (Vector.Vector PdfValue.Number)
  
 
deriving instance HS.Eq ColourOp_5
 
deriving instance HS.Ord ColourOp_5
 
deriving instance HS.Show ColourOp_5
 
instance RTS.DDL ColourOp_5 where
 
instance HS.HasField "cs" ColourOp_5
           (Vector.Vector PdfValue.Number) where
  getField (ColourOp_5 x) = x
 
data ColourOp_6
  = ColourOp_6 PdfValue.Number
  
 
deriving instance HS.Eq ColourOp_6
 
deriving instance HS.Ord ColourOp_6
 
deriving instance HS.Show ColourOp_6
 
instance RTS.DDL ColourOp_6 where
 
instance HS.HasField "gray" ColourOp_6 PdfValue.Number where
  getField (ColourOp_6 x) = x
 
data ColourOp_7
  = ColourOp_7 PdfValue.Number
  
 
deriving instance HS.Eq ColourOp_7
 
deriving instance HS.Ord ColourOp_7
 
deriving instance HS.Show ColourOp_7
 
instance RTS.DDL ColourOp_7 where
 
instance HS.HasField "gray" ColourOp_7 PdfValue.Number where
  getField (ColourOp_7 x) = x
 
data ColourOp_8
  = ColourOp_8 PdfValue.Number PdfValue.Number PdfValue.Number
  
 
deriving instance HS.Eq ColourOp_8
 
deriving instance HS.Ord ColourOp_8
 
deriving instance HS.Show ColourOp_8
 
instance RTS.DDL ColourOp_8 where
 
instance HS.HasField "r" ColourOp_8 PdfValue.Number where
  getField (ColourOp_8 x _ _) = x
 
instance HS.HasField "g" ColourOp_8 PdfValue.Number where
  getField (ColourOp_8 _ x _) = x
 
instance HS.HasField "b" ColourOp_8 PdfValue.Number where
  getField (ColourOp_8 _ _ x) = x
 
data ColourOp_9
  = ColourOp_9 PdfValue.Number PdfValue.Number PdfValue.Number
  
 
deriving instance HS.Eq ColourOp_9
 
deriving instance HS.Ord ColourOp_9
 
deriving instance HS.Show ColourOp_9
 
instance RTS.DDL ColourOp_9 where
 
instance HS.HasField "r" ColourOp_9 PdfValue.Number where
  getField (ColourOp_9 x _ _) = x
 
instance HS.HasField "g" ColourOp_9 PdfValue.Number where
  getField (ColourOp_9 _ x _) = x
 
instance HS.HasField "b" ColourOp_9 PdfValue.Number where
  getField (ColourOp_9 _ _ x) = x
 
data ColourOp_10
  = ColourOp_10 PdfValue.Number PdfValue.Number PdfValue.Number
      PdfValue.Number
  
 
deriving instance HS.Eq ColourOp_10
 
deriving instance HS.Ord ColourOp_10
 
deriving instance HS.Show ColourOp_10
 
instance RTS.DDL ColourOp_10 where
 
instance HS.HasField "c" ColourOp_10 PdfValue.Number where
  getField (ColourOp_10 x _ _ _) = x
 
instance HS.HasField "m" ColourOp_10 PdfValue.Number where
  getField (ColourOp_10 _ x _ _) = x
 
instance HS.HasField "y" ColourOp_10 PdfValue.Number where
  getField (ColourOp_10 _ _ x _) = x
 
instance HS.HasField "k" ColourOp_10 PdfValue.Number where
  getField (ColourOp_10 _ _ _ x) = x
 
data ColourOp_11
  = ColourOp_11 PdfValue.Number PdfValue.Number PdfValue.Number
      PdfValue.Number
  
 
deriving instance HS.Eq ColourOp_11
 
deriving instance HS.Ord ColourOp_11
 
deriving instance HS.Show ColourOp_11
 
instance RTS.DDL ColourOp_11 where
 
instance HS.HasField "c" ColourOp_11 PdfValue.Number where
  getField (ColourOp_11 x _ _ _) = x
 
instance HS.HasField "m" ColourOp_11 PdfValue.Number where
  getField (ColourOp_11 _ x _ _) = x
 
instance HS.HasField "y" ColourOp_11 PdfValue.Number where
  getField (ColourOp_11 _ _ x _) = x
 
instance HS.HasField "k" ColourOp_11 PdfValue.Number where
  getField (ColourOp_11 _ _ _ x) = x
 
data FontOp_0
  = FontOp_0 PdfValue.Number
  
 
deriving instance HS.Eq FontOp_0
 
deriving instance HS.Ord FontOp_0
 
deriving instance HS.Show FontOp_0
 
instance RTS.DDL FontOp_0 where
 
instance HS.HasField "wx" FontOp_0 PdfValue.Number where
  getField (FontOp_0 x) = x
 
data FontOp_1
  = FontOp_1 PdfValue.Number PdfValue.Number PdfValue.Number
      PdfValue.Number
      PdfValue.Number
  
 
deriving instance HS.Eq FontOp_1
 
deriving instance HS.Ord FontOp_1
 
deriving instance HS.Show FontOp_1
 
instance RTS.DDL FontOp_1 where
 
instance HS.HasField "wx" FontOp_1 PdfValue.Number where
  getField (FontOp_1 x _ _ _ _) = x
 
instance HS.HasField "llx" FontOp_1 PdfValue.Number where
  getField (FontOp_1 _ x _ _ _) = x
 
instance HS.HasField "lly" FontOp_1 PdfValue.Number where
  getField (FontOp_1 _ _ x _ _) = x
 
instance HS.HasField "urx" FontOp_1 PdfValue.Number where
  getField (FontOp_1 _ _ _ x _) = x
 
instance HS.HasField "ury" FontOp_1 PdfValue.Number where
  getField (FontOp_1 _ _ _ _ x) = x
 
data Fractional_0
  = Fractional_0 HS.Integer HS.Integer
  
 
deriving instance HS.Eq Fractional_0
 
deriving instance HS.Ord Fractional_0
 
deriving instance HS.Show Fractional_0
 
instance RTS.DDL Fractional_0 where
 
instance HS.HasField "num" Fractional_0 HS.Integer where
  getField (Fractional_0 x _) = x
 
instance HS.HasField "exp" Fractional_0 HS.Integer where
  getField (Fractional_0 _ x) = x
 
data Fractional_1
  = Fractional_1 HS.Integer HS.Integer
  
 
deriving instance HS.Eq Fractional_1
 
deriving instance HS.Ord Fractional_1
 
deriving instance HS.Show Fractional_1
 
instance RTS.DDL Fractional_1 where
 
instance HS.HasField "num" Fractional_1 HS.Integer where
  getField (Fractional_1 x _) = x
 
instance HS.HasField "exp" Fractional_1 HS.Integer where
  getField (Fractional_1 _ x) = x
 
data GenDict_0 j
  = GenDict_0 (Vector.Vector (RTS.UInt 8)) j
  
 
deriving instance HS.Eq j => HS.Eq (GenDict_0 j)
 
deriving instance HS.Ord j => HS.Ord (GenDict_0 j)
 
deriving instance HS.Show j => HS.Show (GenDict_0 j)
 
instance RTS.DDL j => RTS.DDL (GenDict_0 j) where
 
instance HS.HasField "key" (GenDict_0 j)
           (Vector.Vector (RTS.UInt 8)) where
  getField (GenDict_0 x _) = x
 
instance HS.HasField "obj" (GenDict_0 j) j where
  getField (GenDict_0 _ x) = x
 
data GenGraphicsStateOp_0
  = GenGraphicsStateOp_0 PdfValue.Number
  
 
deriving instance HS.Eq GenGraphicsStateOp_0
 
deriving instance HS.Ord GenGraphicsStateOp_0
 
deriving instance HS.Show GenGraphicsStateOp_0
 
instance RTS.DDL GenGraphicsStateOp_0 where
 
instance HS.HasField "lineWidth" GenGraphicsStateOp_0
           PdfValue.Number where
  getField (GenGraphicsStateOp_0 x) = x
 
data GenGraphicsStateOp_1
  = GenGraphicsStateOp_1 (RTS.UInt 8)
  
 
deriving instance HS.Eq GenGraphicsStateOp_1
 
deriving instance HS.Ord GenGraphicsStateOp_1
 
deriving instance HS.Show GenGraphicsStateOp_1
 
instance RTS.DDL GenGraphicsStateOp_1 where
 
instance HS.HasField "lineCap" GenGraphicsStateOp_1
           (RTS.UInt 8) where
  getField (GenGraphicsStateOp_1 x) = x
 
data GenGraphicsStateOp_2
  = GenGraphicsStateOp_2 (RTS.UInt 8)
  
 
deriving instance HS.Eq GenGraphicsStateOp_2
 
deriving instance HS.Ord GenGraphicsStateOp_2
 
deriving instance HS.Show GenGraphicsStateOp_2
 
instance RTS.DDL GenGraphicsStateOp_2 where
 
instance HS.HasField "lineJoin" GenGraphicsStateOp_2
           (RTS.UInt 8) where
  getField (GenGraphicsStateOp_2 x) = x
 
data GenGraphicsStateOp_3
  = GenGraphicsStateOp_3 PdfValue.Number
  
 
deriving instance HS.Eq GenGraphicsStateOp_3
 
deriving instance HS.Ord GenGraphicsStateOp_3
 
deriving instance HS.Show GenGraphicsStateOp_3
 
instance RTS.DDL GenGraphicsStateOp_3 where
 
instance HS.HasField "miterLimit" GenGraphicsStateOp_3
           PdfValue.Number where
  getField (GenGraphicsStateOp_3 x) = x
 
data GenGraphicsStateOp_4
  = GenGraphicsStateOp_4 (Vector.Vector HS.Integer) PdfValue.Number
  
 
deriving instance HS.Eq GenGraphicsStateOp_4
 
deriving instance HS.Ord GenGraphicsStateOp_4
 
deriving instance HS.Show GenGraphicsStateOp_4
 
instance RTS.DDL GenGraphicsStateOp_4 where
 
instance HS.HasField "dashArray" GenGraphicsStateOp_4
           (Vector.Vector HS.Integer) where
  getField (GenGraphicsStateOp_4 x _) = x
 
instance HS.HasField "dashPhase" GenGraphicsStateOp_4
           PdfValue.Number where
  getField (GenGraphicsStateOp_4 _ x) = x
 
data Intent
  = Intent_absoluteColorimetric (Vector.Vector (RTS.UInt 8))
  | Intent_perceptual (Vector.Vector (RTS.UInt 8))
  | Intent_relativeColorimetric (Vector.Vector (RTS.UInt 8))
  | Intent_saturation (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq Intent
 
deriving instance HS.Ord Intent
 
deriving instance HS.Show Intent
 
instance RTS.DDL Intent where
 
instance HS.HasField "absoluteColorimetric" Intent
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (Intent_absoluteColorimetric x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "perceptual" Intent
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (Intent_perceptual x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "relativeColorimetric" Intent
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (Intent_relativeColorimetric x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "saturation" Intent
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (Intent_saturation x) = HS.Just x
   
  getField _ = HS.Nothing
 
data GenGraphicsStateOp_5
  = GenGraphicsStateOp_5 Intent
  
 
deriving instance HS.Eq GenGraphicsStateOp_5
 
deriving instance HS.Ord GenGraphicsStateOp_5
 
deriving instance HS.Show GenGraphicsStateOp_5
 
instance RTS.DDL GenGraphicsStateOp_5 where
 
instance HS.HasField "intent" GenGraphicsStateOp_5 Intent where
  getField (GenGraphicsStateOp_5 x) = x
 
data GenGraphicsStateOp_6
  = GenGraphicsStateOp_6 HS.Integer HS.Integer
  
 
deriving instance HS.Eq GenGraphicsStateOp_6
 
deriving instance HS.Ord GenGraphicsStateOp_6
 
deriving instance HS.Show GenGraphicsStateOp_6
 
instance RTS.DDL GenGraphicsStateOp_6 where
 
instance HS.HasField "num" GenGraphicsStateOp_6 HS.Integer where
  getField (GenGraphicsStateOp_6 x _) = x
 
instance HS.HasField "exp" GenGraphicsStateOp_6 HS.Integer where
  getField (GenGraphicsStateOp_6 _ x) = x
 
data GenGraphicsStateOp_7
  = GenGraphicsStateOp_7 PdfValue.Number
  
 
deriving instance HS.Eq GenGraphicsStateOp_7
 
deriving instance HS.Ord GenGraphicsStateOp_7
 
deriving instance HS.Show GenGraphicsStateOp_7
 
instance RTS.DDL GenGraphicsStateOp_7 where
 
instance HS.HasField "flatness" GenGraphicsStateOp_7
           PdfValue.Number where
  getField (GenGraphicsStateOp_7 x) = x
 
data GenGraphicsStateOp_8
  = GenGraphicsStateOp_8 (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq GenGraphicsStateOp_8
 
deriving instance HS.Ord GenGraphicsStateOp_8
 
deriving instance HS.Show GenGraphicsStateOp_8
 
instance RTS.DDL GenGraphicsStateOp_8 where
 
instance HS.HasField "dictName" GenGraphicsStateOp_8
           (Vector.Vector (RTS.UInt 8)) where
  getField (GenGraphicsStateOp_8 x) = x
 
data GenDirectObj i
  = GenDirectObj_array (Vector.Vector i)
  | GenDirectObj_bool HS.Bool
  | GenDirectObj_dict (Map.Map (Vector.Vector (RTS.UInt 8)) i)
  | GenDirectObj_name (Vector.Vector (RTS.UInt 8))
  | GenDirectObj_null ()
  | GenDirectObj_number PdfValue.Number
  | GenDirectObj_string (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq i => HS.Eq (GenDirectObj i)
 
deriving instance HS.Ord i => HS.Ord (GenDirectObj i)
 
deriving instance HS.Show i => HS.Show (GenDirectObj i)
 
instance RTS.DDL i => RTS.DDL (GenDirectObj i) where
 
instance HS.HasField "array" (GenDirectObj i)
           (HS.Maybe (Vector.Vector i)) where
  getField (GenDirectObj_array x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "bool" (GenDirectObj i)
           (HS.Maybe HS.Bool) where
  getField (GenDirectObj_bool x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "dict" (GenDirectObj i)
           (HS.Maybe (Map.Map (Vector.Vector (RTS.UInt 8)) i)) where
  getField (GenDirectObj_dict x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "name" (GenDirectObj i)
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (GenDirectObj_name x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "null" (GenDirectObj i) (HS.Maybe ()) where
  getField (GenDirectObj_null x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "number" (GenDirectObj i)
           (HS.Maybe PdfValue.Number) where
  getField (GenDirectObj_number x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "string" (GenDirectObj i)
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (GenDirectObj_string x) = HS.Just x
   
  getField _ = HS.Nothing
 
data DirectObj
  = DirectObj (GenDirectObj DirectObj)
  
 
deriving instance HS.Eq DirectObj
 
deriving instance HS.Ord DirectObj
 
deriving instance HS.Show DirectObj
 
instance RTS.DDL DirectObj where
 
instance HS.HasField "box" DirectObj (GenDirectObj DirectObj) where
  getField (DirectObj x) = x
 
data InlineImageObj_0
  = InlineImageObj_0_arr (Vector.Vector DirectObj)
  | InlineImageObj_0_nm (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq InlineImageObj_0
 
deriving instance HS.Ord InlineImageObj_0
 
deriving instance HS.Show InlineImageObj_0
 
instance RTS.DDL InlineImageObj_0 where
 
instance HS.HasField "arr" InlineImageObj_0
           (HS.Maybe (Vector.Vector DirectObj)) where
  getField (InlineImageObj_0_arr x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "nm" InlineImageObj_0
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (InlineImageObj_0_nm x) = HS.Just x
   
  getField _ = HS.Nothing
 
data InlineImageObj_1
  = InlineImageObj_1_arr
      (Vector.Vector (Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj))
  | InlineImageObj_1_d
      (Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj)
  
 
deriving instance HS.Eq InlineImageObj_1
 
deriving instance HS.Ord InlineImageObj_1
 
deriving instance HS.Show InlineImageObj_1
 
instance RTS.DDL InlineImageObj_1 where
 
instance HS.HasField "arr" InlineImageObj_1
           (HS.Maybe
              (Vector.Vector
                 (Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj))) where
  getField (InlineImageObj_1_arr x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "d" InlineImageObj_1
           (HS.Maybe (Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj)) where
  getField (InlineImageObj_1_d x) = HS.Just x
   
  getField _ = HS.Nothing
 
data InlineImageObj_2
  = InlineImageObj_2_name (Vector.Vector (RTS.UInt 8))
  | InlineImageObj_2_names
      (Vector.Vector (Vector.Vector (RTS.UInt 8)))
  
 
deriving instance HS.Eq InlineImageObj_2
 
deriving instance HS.Ord InlineImageObj_2
 
deriving instance HS.Show InlineImageObj_2
 
instance RTS.DDL InlineImageObj_2 where
 
instance HS.HasField "name" InlineImageObj_2
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (InlineImageObj_2_name x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "names" InlineImageObj_2
           (HS.Maybe (Vector.Vector (Vector.Vector (RTS.UInt 8)))) where
  getField (InlineImageObj_2_names x) = HS.Just x
   
  getField _ = HS.Nothing
 
data InlineImageObj_3
  = InlineImageObj_3_absColorimetric (Vector.Vector (RTS.UInt 8))
  | InlineImageObj_3_perceptual (Vector.Vector (RTS.UInt 8))
  | InlineImageObj_3_relColorimetric (Vector.Vector (RTS.UInt 8))
  | InlineImageObj_3_sat (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq InlineImageObj_3
 
deriving instance HS.Ord InlineImageObj_3
 
deriving instance HS.Show InlineImageObj_3
 
instance RTS.DDL InlineImageObj_3 where
 
instance HS.HasField "absColorimetric" InlineImageObj_3
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (InlineImageObj_3_absColorimetric x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "perceptual" InlineImageObj_3
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (InlineImageObj_3_perceptual x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "relColorimetric" InlineImageObj_3
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (InlineImageObj_3_relColorimetric x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "sat" InlineImageObj_3
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (InlineImageObj_3_sat x) = HS.Just x
   
  getField _ = HS.Nothing
 
data InlineImageObj_4
  = InlineImageObj_4_bpc HS.Integer
  | InlineImageObj_4_colorSpace InlineImageObj_0
  | InlineImageObj_4_decode (Vector.Vector PdfValue.Number)
  | InlineImageObj_4_decodeParams InlineImageObj_1
  | InlineImageObj_4_filter InlineImageObj_2
  | InlineImageObj_4_height HS.Integer
  | InlineImageObj_4_imageMask HS.Bool
  | InlineImageObj_4_intent InlineImageObj_3
  
 
deriving instance HS.Eq InlineImageObj_4
 
deriving instance HS.Ord InlineImageObj_4
 
deriving instance HS.Show InlineImageObj_4
 
instance RTS.DDL InlineImageObj_4 where
 
instance HS.HasField "bpc" InlineImageObj_4
           (HS.Maybe HS.Integer) where
  getField (InlineImageObj_4_bpc x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "colorSpace" InlineImageObj_4
           (HS.Maybe InlineImageObj_0) where
  getField (InlineImageObj_4_colorSpace x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "decode" InlineImageObj_4
           (HS.Maybe (Vector.Vector PdfValue.Number)) where
  getField (InlineImageObj_4_decode x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "decodeParams" InlineImageObj_4
           (HS.Maybe InlineImageObj_1) where
  getField (InlineImageObj_4_decodeParams x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "filter" InlineImageObj_4
           (HS.Maybe InlineImageObj_2) where
  getField (InlineImageObj_4_filter x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "height" InlineImageObj_4
           (HS.Maybe HS.Integer) where
  getField (InlineImageObj_4_height x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "imageMask" InlineImageObj_4
           (HS.Maybe HS.Bool) where
  getField (InlineImageObj_4_imageMask x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "intent" InlineImageObj_4
           (HS.Maybe InlineImageObj_3) where
  getField (InlineImageObj_4_intent x) = HS.Just x
   
  getField _ = HS.Nothing
 
data InlineImageObj_5
  = InlineImageObj_5 (Vector.Vector (RTS.UInt 8)) DirectObj
  
 
deriving instance HS.Eq InlineImageObj_5
 
deriving instance HS.Ord InlineImageObj_5
 
deriving instance HS.Show InlineImageObj_5
 
instance RTS.DDL InlineImageObj_5 where
 
instance HS.HasField "key" InlineImageObj_5
           (Vector.Vector (RTS.UInt 8)) where
  getField (InlineImageObj_5 x _) = x
 
instance HS.HasField "value" InlineImageObj_5 DirectObj where
  getField (InlineImageObj_5 _ x) = x
 
data MarkedContentOp_0
  = MarkedContentOp_0 (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq MarkedContentOp_0
 
deriving instance HS.Ord MarkedContentOp_0
 
deriving instance HS.Show MarkedContentOp_0
 
instance RTS.DDL MarkedContentOp_0 where
 
instance HS.HasField "tag" MarkedContentOp_0
           (Vector.Vector (RTS.UInt 8)) where
  getField (MarkedContentOp_0 x) = x
 
data ContentProps
  = ContentProps_inline
      (Map.Map (Vector.Vector (RTS.UInt 8)) PdfValue.Value)
  | ContentProps_nm (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq ContentProps
 
deriving instance HS.Ord ContentProps
 
deriving instance HS.Show ContentProps
 
instance RTS.DDL ContentProps where
 
instance HS.HasField "inline" ContentProps
           (HS.Maybe
              (Map.Map (Vector.Vector (RTS.UInt 8)) PdfValue.Value)) where
  getField (ContentProps_inline x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "nm" ContentProps
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ContentProps_nm x) = HS.Just x
   
  getField _ = HS.Nothing
 
data MarkedContentOp_1
  = MarkedContentOp_1 (Vector.Vector (RTS.UInt 8)) ContentProps
  
 
deriving instance HS.Eq MarkedContentOp_1
 
deriving instance HS.Ord MarkedContentOp_1
 
deriving instance HS.Show MarkedContentOp_1
 
instance RTS.DDL MarkedContentOp_1 where
 
instance HS.HasField "tag" MarkedContentOp_1
           (Vector.Vector (RTS.UInt 8)) where
  getField (MarkedContentOp_1 x _) = x
 
instance HS.HasField "props" MarkedContentOp_1 ContentProps where
  getField (MarkedContentOp_1 _ x) = x
 
data MarkedContentSeq_0
  = MarkedContentSeq_0 (Vector.Vector (RTS.UInt 8)) ContentProps
  
 
deriving instance HS.Eq MarkedContentSeq_0
 
deriving instance HS.Ord MarkedContentSeq_0
 
deriving instance HS.Show MarkedContentSeq_0
 
instance RTS.DDL MarkedContentSeq_0 where
 
instance HS.HasField "tag" MarkedContentSeq_0
           (Vector.Vector (RTS.UInt 8)) where
  getField (MarkedContentSeq_0 x _) = x
 
instance HS.HasField "props" MarkedContentSeq_0 ContentProps where
  getField (MarkedContentSeq_0 _ x) = x
 
data MarkedContentSeq_1
  = MarkedContentSeq_1_beginMarkedContent ()
  | MarkedContentSeq_1_beginMarkedContentProp MarkedContentSeq_0
  
 
deriving instance HS.Eq MarkedContentSeq_1
 
deriving instance HS.Ord MarkedContentSeq_1
 
deriving instance HS.Show MarkedContentSeq_1
 
instance RTS.DDL MarkedContentSeq_1 where
 
instance HS.HasField "beginMarkedContent" MarkedContentSeq_1
           (HS.Maybe ()) where
  getField (MarkedContentSeq_1_beginMarkedContent x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "beginMarkedContentProp" MarkedContentSeq_1
           (HS.Maybe MarkedContentSeq_0) where
  getField (MarkedContentSeq_1_beginMarkedContentProp x) = HS.Just x
   
  getField _ = HS.Nothing
 
data ColourOp
  = ColourOp_setCMYKNonStroking ColourOp_11
  | ColourOp_setCMYKStroking ColourOp_10
  | ColourOp_setColorNonStroking ColourOp_4
  | ColourOp_setColorNonStrokingICC ColourOp_5
  | ColourOp_setColorSpaceNonStroking ColourOp_1
  | ColourOp_setColorSpaceStroking ColourOp_0
  | ColourOp_setColorStroking ColourOp_2
  | ColourOp_setColorStrokingICC ColourOp_3
  | ColourOp_setGrayNonStroking ColourOp_7
  | ColourOp_setGrayStroking ColourOp_6
  | ColourOp_setRGBNonStroking ColourOp_9
  | ColourOp_setRGBStroking ColourOp_8
  
 
deriving instance HS.Eq ColourOp
 
deriving instance HS.Ord ColourOp
 
deriving instance HS.Show ColourOp
 
instance RTS.DDL ColourOp where
 
instance HS.HasField "setCMYKNonStroking" ColourOp
           (HS.Maybe ColourOp_11) where
  getField (ColourOp_setCMYKNonStroking x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setCMYKStroking" ColourOp
           (HS.Maybe ColourOp_10) where
  getField (ColourOp_setCMYKStroking x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setColorNonStroking" ColourOp
           (HS.Maybe ColourOp_4) where
  getField (ColourOp_setColorNonStroking x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setColorNonStrokingICC" ColourOp
           (HS.Maybe ColourOp_5) where
  getField (ColourOp_setColorNonStrokingICC x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setColorSpaceNonStroking" ColourOp
           (HS.Maybe ColourOp_1) where
  getField (ColourOp_setColorSpaceNonStroking x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setColorSpaceStroking" ColourOp
           (HS.Maybe ColourOp_0) where
  getField (ColourOp_setColorSpaceStroking x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setColorStroking" ColourOp
           (HS.Maybe ColourOp_2) where
  getField (ColourOp_setColorStroking x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setColorStrokingICC" ColourOp
           (HS.Maybe ColourOp_3) where
  getField (ColourOp_setColorStrokingICC x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setGrayNonStroking" ColourOp
           (HS.Maybe ColourOp_7) where
  getField (ColourOp_setGrayNonStroking x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setGrayStroking" ColourOp
           (HS.Maybe ColourOp_6) where
  getField (ColourOp_setGrayStroking x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setRGBNonStroking" ColourOp
           (HS.Maybe ColourOp_9) where
  getField (ColourOp_setRGBNonStroking x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setRGBStroking" ColourOp
           (HS.Maybe ColourOp_8) where
  getField (ColourOp_setRGBStroking x) = HS.Just x
   
  getField _ = HS.Nothing
 
data PossibleOp
  = PossibleOp (Vector.Vector DirectObj) (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq PossibleOp
 
deriving instance HS.Ord PossibleOp
 
deriving instance HS.Show PossibleOp
 
instance RTS.DDL PossibleOp where
 
instance HS.HasField "operands" PossibleOp
           (Vector.Vector DirectObj) where
  getField (PossibleOp x _) = x
 
instance HS.HasField "op" PossibleOp
           (Vector.Vector (RTS.UInt 8)) where
  getField (PossibleOp _ x) = x
 
data GenGraphicsStateOp
  = GenGraphicsStateOp_setColorRenderingIntent GenGraphicsStateOp_5
  | GenGraphicsStateOp_setFlat GenGraphicsStateOp_7
  | GenGraphicsStateOp_setGraphicsStateParams GenGraphicsStateOp_8
  | GenGraphicsStateOp_setLineCapStyle GenGraphicsStateOp_1
  | GenGraphicsStateOp_setLineDash GenGraphicsStateOp_4
  | GenGraphicsStateOp_setLineJoinStyle GenGraphicsStateOp_2
  | GenGraphicsStateOp_setLineWidth GenGraphicsStateOp_0
  | GenGraphicsStateOp_setMiterLimit GenGraphicsStateOp_3
  
 
deriving instance HS.Eq GenGraphicsStateOp
 
deriving instance HS.Ord GenGraphicsStateOp
 
deriving instance HS.Show GenGraphicsStateOp
 
instance RTS.DDL GenGraphicsStateOp where
 
instance HS.HasField "setColorRenderingIntent" GenGraphicsStateOp
           (HS.Maybe GenGraphicsStateOp_5) where
  getField (GenGraphicsStateOp_setColorRenderingIntent x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setFlat" GenGraphicsStateOp
           (HS.Maybe GenGraphicsStateOp_7) where
  getField (GenGraphicsStateOp_setFlat x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setGraphicsStateParams" GenGraphicsStateOp
           (HS.Maybe GenGraphicsStateOp_8) where
  getField (GenGraphicsStateOp_setGraphicsStateParams x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setLineCapStyle" GenGraphicsStateOp
           (HS.Maybe GenGraphicsStateOp_1) where
  getField (GenGraphicsStateOp_setLineCapStyle x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setLineDash" GenGraphicsStateOp
           (HS.Maybe GenGraphicsStateOp_4) where
  getField (GenGraphicsStateOp_setLineDash x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setLineJoinStyle" GenGraphicsStateOp
           (HS.Maybe GenGraphicsStateOp_2) where
  getField (GenGraphicsStateOp_setLineJoinStyle x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setLineWidth" GenGraphicsStateOp
           (HS.Maybe GenGraphicsStateOp_0) where
  getField (GenGraphicsStateOp_setLineWidth x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setMiterLimit" GenGraphicsStateOp
           (HS.Maybe GenGraphicsStateOp_3) where
  getField (GenGraphicsStateOp_setMiterLimit x) = HS.Just x
   
  getField _ = HS.Nothing
 
data InlineImageObj
  = InlineImageObj (Vector.Vector InlineImageObj_5)
      (Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj)
      HS.Integer
      (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq InlineImageObj
 
deriving instance HS.Ord InlineImageObj
 
deriving instance HS.Show InlineImageObj
 
instance RTS.DDL InlineImageObj where
 
instance HS.HasField "hdrEnts" InlineImageObj
           (Vector.Vector InlineImageObj_5) where
  getField (InlineImageObj x _ _ _) = x
 
instance HS.HasField "hdr" InlineImageObj
           (Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj) where
  getField (InlineImageObj _ x _ _) = x
 
instance HS.HasField "len" InlineImageObj HS.Integer where
  getField (InlineImageObj _ _ x _) = x
 
instance HS.HasField "imageData" InlineImageObj
           (Vector.Vector (RTS.UInt 8)) where
  getField (InlineImageObj _ _ _ x) = x
 
data ClippingPathOp
  = ClippingPathOp_setClippingEvenOdd ()
  | ClippingPathOp_setClippingNzWinding ()
  
 
deriving instance HS.Eq ClippingPathOp
 
deriving instance HS.Ord ClippingPathOp
 
deriving instance HS.Show ClippingPathOp
 
instance RTS.DDL ClippingPathOp where
 
instance HS.HasField "setClippingEvenOdd" ClippingPathOp
           (HS.Maybe ()) where
  getField (ClippingPathOp_setClippingEvenOdd x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setClippingNzWinding" ClippingPathOp
           (HS.Maybe ()) where
  getField (ClippingPathOp_setClippingNzWinding x) = HS.Just x
   
  getField _ = HS.Nothing
 
data ContentPoint
  = ContentPoint PdfValue.Number PdfValue.Number
  
 
deriving instance HS.Eq ContentPoint
 
deriving instance HS.Ord ContentPoint
 
deriving instance HS.Show ContentPoint
 
instance RTS.DDL ContentPoint where
 
instance HS.HasField "x" ContentPoint PdfValue.Number where
  getField (ContentPoint x _) = x
 
instance HS.HasField "y" ContentPoint PdfValue.Number where
  getField (ContentPoint _ x) = x
 
data PathBeginOp_0
  = PathBeginOp_0 ContentPoint
  
 
deriving instance HS.Eq PathBeginOp_0
 
deriving instance HS.Ord PathBeginOp_0
 
deriving instance HS.Show PathBeginOp_0
 
instance RTS.DDL PathBeginOp_0 where
 
instance HS.HasField "pt" PathBeginOp_0 ContentPoint where
  getField (PathBeginOp_0 x) = x
 
data PathBeginOp_1
  = PathBeginOp_1 ContentPoint PdfValue.Number PdfValue.Number
  
 
deriving instance HS.Eq PathBeginOp_1
 
deriving instance HS.Ord PathBeginOp_1
 
deriving instance HS.Show PathBeginOp_1
 
instance RTS.DDL PathBeginOp_1 where
 
instance HS.HasField "pt" PathBeginOp_1 ContentPoint where
  getField (PathBeginOp_1 x _ _) = x
 
instance HS.HasField "width" PathBeginOp_1 PdfValue.Number where
  getField (PathBeginOp_1 _ x _) = x
 
instance HS.HasField "height" PathBeginOp_1 PdfValue.Number where
  getField (PathBeginOp_1 _ _ x) = x
 
data PathBeginOp
  = PathBeginOp_appendRect PathBeginOp_1
  | PathBeginOp_beginNewSuppath PathBeginOp_0
  
 
deriving instance HS.Eq PathBeginOp
 
deriving instance HS.Ord PathBeginOp
 
deriving instance HS.Show PathBeginOp
 
instance RTS.DDL PathBeginOp where
 
instance HS.HasField "appendRect" PathBeginOp
           (HS.Maybe PathBeginOp_1) where
  getField (PathBeginOp_appendRect x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "beginNewSuppath" PathBeginOp
           (HS.Maybe PathBeginOp_0) where
  getField (PathBeginOp_beginNewSuppath x) = HS.Just x
   
  getField _ = HS.Nothing
 
data PathConsOp_0
  = PathConsOp_0 ContentPoint
  
 
deriving instance HS.Eq PathConsOp_0
 
deriving instance HS.Ord PathConsOp_0
 
deriving instance HS.Show PathConsOp_0
 
instance RTS.DDL PathConsOp_0 where
 
instance HS.HasField "pt" PathConsOp_0 ContentPoint where
  getField (PathConsOp_0 x) = x
 
data PathConsOp_1
  = PathConsOp_1 ContentPoint ContentPoint ContentPoint
  
 
deriving instance HS.Eq PathConsOp_1
 
deriving instance HS.Ord PathConsOp_1
 
deriving instance HS.Show PathConsOp_1
 
instance RTS.DDL PathConsOp_1 where
 
instance HS.HasField "pt1" PathConsOp_1 ContentPoint where
  getField (PathConsOp_1 x _ _) = x
 
instance HS.HasField "pt2" PathConsOp_1 ContentPoint where
  getField (PathConsOp_1 _ x _) = x
 
instance HS.HasField "pt3" PathConsOp_1 ContentPoint where
  getField (PathConsOp_1 _ _ x) = x
 
data PathConsOp_2
  = PathConsOp_2 ContentPoint ContentPoint
  
 
deriving instance HS.Eq PathConsOp_2
 
deriving instance HS.Ord PathConsOp_2
 
deriving instance HS.Show PathConsOp_2
 
instance RTS.DDL PathConsOp_2 where
 
instance HS.HasField "pt2" PathConsOp_2 ContentPoint where
  getField (PathConsOp_2 x _) = x
 
instance HS.HasField "pt3" PathConsOp_2 ContentPoint where
  getField (PathConsOp_2 _ x) = x
 
data PathConsOp_3
  = PathConsOp_3 ContentPoint ContentPoint
  
 
deriving instance HS.Eq PathConsOp_3
 
deriving instance HS.Ord PathConsOp_3
 
deriving instance HS.Show PathConsOp_3
 
instance RTS.DDL PathConsOp_3 where
 
instance HS.HasField "pt1" PathConsOp_3 ContentPoint where
  getField (PathConsOp_3 x _) = x
 
instance HS.HasField "pt3" PathConsOp_3 ContentPoint where
  getField (PathConsOp_3 _ x) = x
 
data PathConsOp
  = PathConsOp_appendCurvedFinalPt PathConsOp_3
  | PathConsOp_appendCurvedInitPtRepl PathConsOp_2
  | PathConsOp_appendCurvedThreePoints PathConsOp_1
  | PathConsOp_appendLine PathConsOp_0
  | PathConsOp_beginSubpath PathBeginOp
  | PathConsOp_closeSubpath ()
  
 
deriving instance HS.Eq PathConsOp
 
deriving instance HS.Ord PathConsOp
 
deriving instance HS.Show PathConsOp
 
instance RTS.DDL PathConsOp where
 
instance HS.HasField "appendCurvedFinalPt" PathConsOp
           (HS.Maybe PathConsOp_3) where
  getField (PathConsOp_appendCurvedFinalPt x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "appendCurvedInitPtRepl" PathConsOp
           (HS.Maybe PathConsOp_2) where
  getField (PathConsOp_appendCurvedInitPtRepl x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "appendCurvedThreePoints" PathConsOp
           (HS.Maybe PathConsOp_1) where
  getField (PathConsOp_appendCurvedThreePoints x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "appendLine" PathConsOp
           (HS.Maybe PathConsOp_0) where
  getField (PathConsOp_appendLine x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "beginSubpath" PathConsOp
           (HS.Maybe PathBeginOp) where
  getField (PathConsOp_beginSubpath x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "closeSubpath" PathConsOp (HS.Maybe ()) where
  getField (PathConsOp_closeSubpath x) = HS.Just x
   
  getField _ = HS.Nothing
 
data PathPaintingOp
  = PathPaintingOp_closeFillStrokeEvenOdd ()
  | PathPaintingOp_closeFillStrokeNzWinding ()
  | PathPaintingOp_closeStrokePath ()
  | PathPaintingOp_endPath ()
  | PathPaintingOp_fillPathEvenOdd ()
  | PathPaintingOp_fillPathNzWinding ()
  | PathPaintingOp_fillPathNzWindingOld ()
  | PathPaintingOp_fillStroke ()
  | PathPaintingOp_fillStrokeEvenOdd ()
  | PathPaintingOp_stroke ()
  
 
deriving instance HS.Eq PathPaintingOp
 
deriving instance HS.Ord PathPaintingOp
 
deriving instance HS.Show PathPaintingOp
 
instance RTS.DDL PathPaintingOp where
 
instance HS.HasField "closeFillStrokeEvenOdd" PathPaintingOp
           (HS.Maybe ()) where
  getField (PathPaintingOp_closeFillStrokeEvenOdd x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "closeFillStrokeNzWinding" PathPaintingOp
           (HS.Maybe ()) where
  getField (PathPaintingOp_closeFillStrokeNzWinding x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "closeStrokePath" PathPaintingOp
           (HS.Maybe ()) where
  getField (PathPaintingOp_closeStrokePath x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "endPath" PathPaintingOp (HS.Maybe ()) where
  getField (PathPaintingOp_endPath x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "fillPathEvenOdd" PathPaintingOp
           (HS.Maybe ()) where
  getField (PathPaintingOp_fillPathEvenOdd x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "fillPathNzWinding" PathPaintingOp
           (HS.Maybe ()) where
  getField (PathPaintingOp_fillPathNzWinding x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "fillPathNzWindingOld" PathPaintingOp
           (HS.Maybe ()) where
  getField (PathPaintingOp_fillPathNzWindingOld x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "fillStroke" PathPaintingOp
           (HS.Maybe ()) where
  getField (PathPaintingOp_fillStroke x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "fillStrokeEvenOdd" PathPaintingOp
           (HS.Maybe ()) where
  getField (PathPaintingOp_fillStrokeEvenOdd x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "stroke" PathPaintingOp (HS.Maybe ()) where
  getField (PathPaintingOp_stroke x) = HS.Just x
   
  getField _ = HS.Nothing
 
data PathObj
  = PathObj PathBeginOp (Vector.Vector PathConsOp)
      (HS.Maybe ClippingPathOp)
      PathPaintingOp
  
 
deriving instance HS.Eq PathObj
 
deriving instance HS.Ord PathObj
 
deriving instance HS.Show PathObj
 
instance RTS.DDL PathObj where
 
instance HS.HasField "begin" PathObj PathBeginOp where
  getField (PathObj x _ _ _) = x
 
instance HS.HasField "pathOps" PathObj
           (Vector.Vector PathConsOp) where
  getField (PathObj _ x _ _) = x
 
instance HS.HasField "clippy" PathObj
           (HS.Maybe ClippingPathOp) where
  getField (PathObj _ _ x _) = x
 
instance HS.HasField "paint" PathObj PathPaintingOp where
  getField (PathObj _ _ _ x) = x
 
data ShadingObj
  = ShadingObj (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq ShadingObj
 
deriving instance HS.Ord ShadingObj
 
deriving instance HS.Show ShadingObj
 
instance RTS.DDL ShadingObj where
 
instance HS.HasField "name" ShadingObj
           (Vector.Vector (RTS.UInt 8)) where
  getField (ShadingObj x) = x
 
data SpecialGraphicsStateSeq_1
  = SpecialGraphicsStateSeq_1 PdfValue.Number PdfValue.Number
      PdfValue.Number
      PdfValue.Number
      PdfValue.Number
      PdfValue.Number
  
 
deriving instance HS.Eq SpecialGraphicsStateSeq_1
 
deriving instance HS.Ord SpecialGraphicsStateSeq_1
 
deriving instance HS.Show SpecialGraphicsStateSeq_1
 
instance RTS.DDL SpecialGraphicsStateSeq_1 where
 
instance HS.HasField "a" SpecialGraphicsStateSeq_1
           PdfValue.Number where
  getField (SpecialGraphicsStateSeq_1 x _ _ _ _ _) = x
 
instance HS.HasField "b" SpecialGraphicsStateSeq_1
           PdfValue.Number where
  getField (SpecialGraphicsStateSeq_1 _ x _ _ _ _) = x
 
instance HS.HasField "c" SpecialGraphicsStateSeq_1
           PdfValue.Number where
  getField (SpecialGraphicsStateSeq_1 _ _ x _ _ _) = x
 
instance HS.HasField "d" SpecialGraphicsStateSeq_1
           PdfValue.Number where
  getField (SpecialGraphicsStateSeq_1 _ _ _ x _ _) = x
 
instance HS.HasField "e" SpecialGraphicsStateSeq_1
           PdfValue.Number where
  getField (SpecialGraphicsStateSeq_1 _ _ _ _ x _) = x
 
instance HS.HasField "f" SpecialGraphicsStateSeq_1
           PdfValue.Number where
  getField (SpecialGraphicsStateSeq_1 _ _ _ _ _ x) = x
 
data TextPosOp_0
  = TextPosOp_0 PdfValue.Number PdfValue.Number
  
 
deriving instance HS.Eq TextPosOp_0
 
deriving instance HS.Ord TextPosOp_0
 
deriving instance HS.Show TextPosOp_0
 
instance RTS.DDL TextPosOp_0 where
 
instance HS.HasField "tx" TextPosOp_0 PdfValue.Number where
  getField (TextPosOp_0 x _) = x
 
instance HS.HasField "ty" TextPosOp_0 PdfValue.Number where
  getField (TextPosOp_0 _ x) = x
 
data TextPosOp_1
  = TextPosOp_1 PdfValue.Number PdfValue.Number
  
 
deriving instance HS.Eq TextPosOp_1
 
deriving instance HS.Ord TextPosOp_1
 
deriving instance HS.Show TextPosOp_1
 
instance RTS.DDL TextPosOp_1 where
 
instance HS.HasField "tx" TextPosOp_1 PdfValue.Number where
  getField (TextPosOp_1 x _) = x
 
instance HS.HasField "ty" TextPosOp_1 PdfValue.Number where
  getField (TextPosOp_1 _ x) = x
 
data TextPosOp_2
  = TextPosOp_2 PdfValue.Number PdfValue.Number PdfValue.Number
      PdfValue.Number
      PdfValue.Number
      PdfValue.Number
  
 
deriving instance HS.Eq TextPosOp_2
 
deriving instance HS.Ord TextPosOp_2
 
deriving instance HS.Show TextPosOp_2
 
instance RTS.DDL TextPosOp_2 where
 
instance HS.HasField "a" TextPosOp_2 PdfValue.Number where
  getField (TextPosOp_2 x _ _ _ _ _) = x
 
instance HS.HasField "b" TextPosOp_2 PdfValue.Number where
  getField (TextPosOp_2 _ x _ _ _ _) = x
 
instance HS.HasField "c" TextPosOp_2 PdfValue.Number where
  getField (TextPosOp_2 _ _ x _ _ _) = x
 
instance HS.HasField "d" TextPosOp_2 PdfValue.Number where
  getField (TextPosOp_2 _ _ _ x _ _) = x
 
instance HS.HasField "e" TextPosOp_2 PdfValue.Number where
  getField (TextPosOp_2 _ _ _ _ x _) = x
 
instance HS.HasField "f" TextPosOp_2 PdfValue.Number where
  getField (TextPosOp_2 _ _ _ _ _ x) = x
 
data TextPosOp
  = TextPosOp TextPosOp_0 TextPosOp_1 TextPosOp_2 ()
  
 
deriving instance HS.Eq TextPosOp
 
deriving instance HS.Ord TextPosOp
 
deriving instance HS.Show TextPosOp
 
instance RTS.DDL TextPosOp where
 
instance HS.HasField "moveTextPos" TextPosOp TextPosOp_0 where
  getField (TextPosOp x _ _ _) = x
 
instance HS.HasField "moveTextPosSetLeading" TextPosOp
           TextPosOp_1 where
  getField (TextPosOp _ x _ _) = x
 
instance HS.HasField "setTextMatrix" TextPosOp TextPosOp_2 where
  getField (TextPosOp _ _ x _) = x
 
instance HS.HasField "moveStartText" TextPosOp () where
  getField (TextPosOp _ _ _ x) = x
 
data TextShowOp_0
  = TextShowOp_0 (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq TextShowOp_0
 
deriving instance HS.Ord TextShowOp_0
 
deriving instance HS.Show TextShowOp_0
 
instance RTS.DDL TextShowOp_0 where
 
instance HS.HasField "str" TextShowOp_0
           (Vector.Vector (RTS.UInt 8)) where
  getField (TextShowOp_0 x) = x
 
data TextShowOp_1
  = TextShowOp_1 (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq TextShowOp_1
 
deriving instance HS.Ord TextShowOp_1
 
deriving instance HS.Show TextShowOp_1
 
instance RTS.DDL TextShowOp_1 where
 
instance HS.HasField "str" TextShowOp_1
           (Vector.Vector (RTS.UInt 8)) where
  getField (TextShowOp_1 x) = x
 
data TextShowOp_2
  = TextShowOp_2 PdfValue.Number PdfValue.Number
  
 
deriving instance HS.Eq TextShowOp_2
 
deriving instance HS.Ord TextShowOp_2
 
deriving instance HS.Show TextShowOp_2
 
instance RTS.DDL TextShowOp_2 where
 
instance HS.HasField "aw" TextShowOp_2 PdfValue.Number where
  getField (TextShowOp_2 x _) = x
 
instance HS.HasField "ac" TextShowOp_2 PdfValue.Number where
  getField (TextShowOp_2 _ x) = x
 
data ShowVal
  = ShowVal_num PdfValue.Number
  | ShowVal_str (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq ShowVal
 
deriving instance HS.Ord ShowVal
 
deriving instance HS.Show ShowVal
 
instance RTS.DDL ShowVal where
 
instance HS.HasField "num" ShowVal (HS.Maybe PdfValue.Number) where
  getField (ShowVal_num x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "str" ShowVal
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ShowVal_str x) = HS.Just x
   
  getField _ = HS.Nothing
 
data TextShowOp_3
  = TextShowOp_3 (Vector.Vector ShowVal)
  
 
deriving instance HS.Eq TextShowOp_3
 
deriving instance HS.Ord TextShowOp_3
 
deriving instance HS.Show TextShowOp_3
 
instance RTS.DDL TextShowOp_3 where
 
instance HS.HasField "arr" TextShowOp_3
           (Vector.Vector ShowVal) where
  getField (TextShowOp_3 x) = x
 
data TextShowOp
  = TextShowOp_moveShow TextShowOp_1
  | TextShowOp_setSpacing TextShowOp_2
  | TextShowOp_showText TextShowOp_0
  | TextShowOp_showTextIndGlyph TextShowOp_3
  
 
deriving instance HS.Eq TextShowOp
 
deriving instance HS.Ord TextShowOp
 
deriving instance HS.Show TextShowOp
 
instance RTS.DDL TextShowOp where
 
instance HS.HasField "moveShow" TextShowOp
           (HS.Maybe TextShowOp_1) where
  getField (TextShowOp_moveShow x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setSpacing" TextShowOp
           (HS.Maybe TextShowOp_2) where
  getField (TextShowOp_setSpacing x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "showText" TextShowOp
           (HS.Maybe TextShowOp_0) where
  getField (TextShowOp_showText x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "showTextIndGlyph" TextShowOp
           (HS.Maybe TextShowOp_3) where
  getField (TextShowOp_showTextIndGlyph x) = HS.Just x
   
  getField _ = HS.Nothing
 
data TextStateOp_0
  = TextStateOp_0 PdfValue.Number
  
 
deriving instance HS.Eq TextStateOp_0
 
deriving instance HS.Ord TextStateOp_0
 
deriving instance HS.Show TextStateOp_0
 
instance RTS.DDL TextStateOp_0 where
 
instance HS.HasField "charSpace" TextStateOp_0
           PdfValue.Number where
  getField (TextStateOp_0 x) = x
 
data TextStateOp_1
  = TextStateOp_1 PdfValue.Number
  
 
deriving instance HS.Eq TextStateOp_1
 
deriving instance HS.Ord TextStateOp_1
 
deriving instance HS.Show TextStateOp_1
 
instance RTS.DDL TextStateOp_1 where
 
instance HS.HasField "x" TextStateOp_1 PdfValue.Number where
  getField (TextStateOp_1 x) = x
 
data TextStateOp_2
  = TextStateOp_2 PdfValue.Number
  
 
deriving instance HS.Eq TextStateOp_2
 
deriving instance HS.Ord TextStateOp_2
 
deriving instance HS.Show TextStateOp_2
 
instance RTS.DDL TextStateOp_2 where
 
instance HS.HasField "scale" TextStateOp_2 PdfValue.Number where
  getField (TextStateOp_2 x) = x
 
data TextStateOp_3
  = TextStateOp_3 PdfValue.Number
  
 
deriving instance HS.Eq TextStateOp_3
 
deriving instance HS.Ord TextStateOp_3
 
deriving instance HS.Show TextStateOp_3
 
instance RTS.DDL TextStateOp_3 where
 
instance HS.HasField "leading" TextStateOp_3 PdfValue.Number where
  getField (TextStateOp_3 x) = x
 
data TextStateOp_4
  = TextStateOp_4 (Vector.Vector (RTS.UInt 8)) PdfValue.Number
  
 
deriving instance HS.Eq TextStateOp_4
 
deriving instance HS.Ord TextStateOp_4
 
deriving instance HS.Show TextStateOp_4
 
instance RTS.DDL TextStateOp_4 where
 
instance HS.HasField "font" TextStateOp_4
           (Vector.Vector (RTS.UInt 8)) where
  getField (TextStateOp_4 x _) = x
 
instance HS.HasField "size" TextStateOp_4 PdfValue.Number where
  getField (TextStateOp_4 _ x) = x
 
data TextStateOp_5
  = TextStateOp_5 HS.Integer
  
 
deriving instance HS.Eq TextStateOp_5
 
deriving instance HS.Ord TextStateOp_5
 
deriving instance HS.Show TextStateOp_5
 
instance RTS.DDL TextStateOp_5 where
 
instance HS.HasField "render" TextStateOp_5 HS.Integer where
  getField (TextStateOp_5 x) = x
 
data TextStateOp_6
  = TextStateOp_6 PdfValue.Number
  
 
deriving instance HS.Eq TextStateOp_6
 
deriving instance HS.Ord TextStateOp_6
 
deriving instance HS.Show TextStateOp_6
 
instance RTS.DDL TextStateOp_6 where
 
instance HS.HasField "rise" TextStateOp_6 PdfValue.Number where
  getField (TextStateOp_6 x) = x
 
data TextStateOp
  = TextStateOp_setCharSpacing TextStateOp_0
  | TextStateOp_setHorizontalTextScaling TextStateOp_2
  | TextStateOp_setTextFont TextStateOp_4
  | TextStateOp_setTextLeading TextStateOp_3
  | TextStateOp_setTextRendering TextStateOp_5
  | TextStateOp_setTextRise TextStateOp_6
  | TextStateOp_setWordSpacing TextStateOp_1
  
 
deriving instance HS.Eq TextStateOp
 
deriving instance HS.Ord TextStateOp
 
deriving instance HS.Show TextStateOp
 
instance RTS.DDL TextStateOp where
 
instance HS.HasField "setCharSpacing" TextStateOp
           (HS.Maybe TextStateOp_0) where
  getField (TextStateOp_setCharSpacing x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setHorizontalTextScaling" TextStateOp
           (HS.Maybe TextStateOp_2) where
  getField (TextStateOp_setHorizontalTextScaling x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setTextFont" TextStateOp
           (HS.Maybe TextStateOp_4) where
  getField (TextStateOp_setTextFont x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setTextLeading" TextStateOp
           (HS.Maybe TextStateOp_3) where
  getField (TextStateOp_setTextLeading x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setTextRendering" TextStateOp
           (HS.Maybe TextStateOp_5) where
  getField (TextStateOp_setTextRendering x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setTextRise" TextStateOp
           (HS.Maybe TextStateOp_6) where
  getField (TextStateOp_setTextRise x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setWordSpacing" TextStateOp
           (HS.Maybe TextStateOp_1) where
  getField (TextStateOp_setWordSpacing x) = HS.Just x
   
  getField _ = HS.Nothing
 
data XObj
  = XObj (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq XObj
 
deriving instance HS.Ord XObj
 
deriving instance HS.Show XObj
 
instance RTS.DDL XObj where
 
instance HS.HasField "name" XObj (Vector.Vector (RTS.UInt 8)) where
  getField (XObj x) = x
 
data PageDescription_0
  = PageDescription_0_colour ColourOp
  | PageDescription_0_compat CompatOps
  | PageDescription_0_genGraphics GenGraphicsStateOp
  | PageDescription_0_inlineObj InlineImageObj
  | PageDescription_0_markedContent MarkedContentSeq
  | PageDescription_0_pathObj PathObj
  | PageDescription_0_shadingObj ShadingObj
  | PageDescription_0_specialGraphics SpecialGraphicsStateSeq
  | PageDescription_0_textObj TextObj
  | PageDescription_0_textState TextStateOp
  | PageDescription_0_xObj XObj
  
 
deriving instance HS.Eq PageDescription_0
 
deriving instance HS.Ord PageDescription_0
 
deriving instance HS.Show PageDescription_0
 
instance RTS.DDL PageDescription_0 where
 
instance HS.HasField "colour" PageDescription_0
           (HS.Maybe ColourOp) where
  getField (PageDescription_0_colour x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "compat" PageDescription_0
           (HS.Maybe CompatOps) where
  getField (PageDescription_0_compat x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "genGraphics" PageDescription_0
           (HS.Maybe GenGraphicsStateOp) where
  getField (PageDescription_0_genGraphics x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "inlineObj" PageDescription_0
           (HS.Maybe InlineImageObj) where
  getField (PageDescription_0_inlineObj x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "markedContent" PageDescription_0
           (HS.Maybe MarkedContentSeq) where
  getField (PageDescription_0_markedContent x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "pathObj" PageDescription_0
           (HS.Maybe PathObj) where
  getField (PageDescription_0_pathObj x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "shadingObj" PageDescription_0
           (HS.Maybe ShadingObj) where
  getField (PageDescription_0_shadingObj x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "specialGraphics" PageDescription_0
           (HS.Maybe SpecialGraphicsStateSeq) where
  getField (PageDescription_0_specialGraphics x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "textObj" PageDescription_0
           (HS.Maybe TextObj) where
  getField (PageDescription_0_textObj x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "textState" PageDescription_0
           (HS.Maybe TextStateOp) where
  getField (PageDescription_0_textState x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "xObj" PageDescription_0 (HS.Maybe XObj) where
  getField (PageDescription_0_xObj x) = HS.Just x
   
  getField _ = HS.Nothing
 
data TextObj_0
  = TextObj_0_color ColourOp
  | TextObj_0_graphicsStateOp GenGraphicsStateOp
  | TextObj_0_marked MarkedContentSeq
  | TextObj_0_textPos TextPosOp
  | TextObj_0_textShow TextShowOp
  | TextObj_0_textState TextStateOp
  
 
deriving instance HS.Eq TextObj_0
 
deriving instance HS.Ord TextObj_0
 
deriving instance HS.Show TextObj_0
 
instance RTS.DDL TextObj_0 where
 
instance HS.HasField "color" TextObj_0 (HS.Maybe ColourOp) where
  getField (TextObj_0_color x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "graphicsStateOp" TextObj_0
           (HS.Maybe GenGraphicsStateOp) where
  getField (TextObj_0_graphicsStateOp x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "marked" TextObj_0
           (HS.Maybe MarkedContentSeq) where
  getField (TextObj_0_marked x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "textPos" TextObj_0 (HS.Maybe TextPosOp) where
  getField (TextObj_0_textPos x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "textShow" TextObj_0
           (HS.Maybe TextShowOp) where
  getField (TextObj_0_textShow x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "textState" TextObj_0
           (HS.Maybe TextStateOp) where
  getField (TextObj_0_textState x) = HS.Just x
   
  getField _ = HS.Nothing
 
data TextObj
  = TextObj (Vector.Vector TextObj_0)
  
 
deriving instance HS.Eq TextObj
 
deriving instance HS.Ord TextObj
 
deriving instance HS.Show TextObj
 
instance RTS.DDL TextObj where
 
instance HS.HasField "ops" TextObj (Vector.Vector TextObj_0) where
  getField (TextObj x) = x
 
data SpecialGraphicsStateSeq_0
  = SpecialGraphicsStateSeq_0 (Vector.Vector PageDescription_0)
  
 
deriving instance HS.Eq SpecialGraphicsStateSeq_0
 
deriving instance HS.Ord SpecialGraphicsStateSeq_0
 
deriving instance HS.Show SpecialGraphicsStateSeq_0
 
instance RTS.DDL SpecialGraphicsStateSeq_0 where
 
instance HS.HasField "page" SpecialGraphicsStateSeq_0
           (Vector.Vector PageDescription_0) where
  getField (SpecialGraphicsStateSeq_0 x) = x
 
data SpecialGraphicsStateSeq
  = SpecialGraphicsStateSeq_concatMatrix SpecialGraphicsStateSeq_1
  | SpecialGraphicsStateSeq_nesting SpecialGraphicsStateSeq_0
  
 
deriving instance HS.Eq SpecialGraphicsStateSeq
 
deriving instance HS.Ord SpecialGraphicsStateSeq
 
deriving instance HS.Show SpecialGraphicsStateSeq
 
instance RTS.DDL SpecialGraphicsStateSeq where
 
instance HS.HasField "concatMatrix" SpecialGraphicsStateSeq
           (HS.Maybe SpecialGraphicsStateSeq_1) where
  getField (SpecialGraphicsStateSeq_concatMatrix x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "nesting" SpecialGraphicsStateSeq
           (HS.Maybe SpecialGraphicsStateSeq_0) where
  getField (SpecialGraphicsStateSeq_nesting x) = HS.Just x
   
  getField _ = HS.Nothing
 
data MarkedContentSeq
  = MarkedContentSeq MarkedContentSeq_1
      (Vector.Vector PageDescription_0)
  
 
deriving instance HS.Eq MarkedContentSeq
 
deriving instance HS.Ord MarkedContentSeq
 
deriving instance HS.Show MarkedContentSeq
 
instance RTS.DDL MarkedContentSeq where
 
instance HS.HasField "beginMarked" MarkedContentSeq
           MarkedContentSeq_1 where
  getField (MarkedContentSeq x _) = x
 
instance HS.HasField "page" MarkedContentSeq
           (Vector.Vector PageDescription_0) where
  getField (MarkedContentSeq _ x) = x
 
data CompatOps
  = CompatOps_compatSection (Vector.Vector PageDescription_0)
  | CompatOps_futureOp PossibleOp
  
 
deriving instance HS.Eq CompatOps
 
deriving instance HS.Ord CompatOps
 
deriving instance HS.Show CompatOps
 
instance RTS.DDL CompatOps where
 
instance HS.HasField "compatSection" CompatOps
           (HS.Maybe (Vector.Vector PageDescription_0)) where
  getField (CompatOps_compatSection x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "futureOp" CompatOps
           (HS.Maybe PossibleOp) where
  getField (CompatOps_futureOp x) = HS.Just x
   
  getField _ = HS.Nothing
 
data ColorSpace
  = ColorSpace_calGray (Vector.Vector (RTS.UInt 8))
  | ColorSpace_calRGB (Vector.Vector (RTS.UInt 8))
  | ColorSpace_devN (Vector.Vector (RTS.UInt 8))
  | ColorSpace_deviceCMYK (Vector.Vector (RTS.UInt 8))
  | ColorSpace_deviceGray (Vector.Vector (RTS.UInt 8))
  | ColorSpace_deviceRGB (Vector.Vector (RTS.UInt 8))
  | ColorSpace_iccBased (Vector.Vector (RTS.UInt 8))
  | ColorSpace_indexed (Vector.Vector (RTS.UInt 8))
  | ColorSpace_lab (Vector.Vector (RTS.UInt 8))
  | ColorSpace_pattern (Vector.Vector (RTS.UInt 8))
  | ColorSpace_sep (Vector.Vector (RTS.UInt 8))
  
 
deriving instance HS.Eq ColorSpace
 
deriving instance HS.Ord ColorSpace
 
deriving instance HS.Show ColorSpace
 
instance RTS.DDL ColorSpace where
 
instance HS.HasField "calGray" ColorSpace
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ColorSpace_calGray x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "calRGB" ColorSpace
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ColorSpace_calRGB x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "devN" ColorSpace
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ColorSpace_devN x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "deviceCMYK" ColorSpace
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ColorSpace_deviceCMYK x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "deviceGray" ColorSpace
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ColorSpace_deviceGray x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "deviceRGB" ColorSpace
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ColorSpace_deviceRGB x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "iccBased" ColorSpace
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ColorSpace_iccBased x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "indexed" ColorSpace
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ColorSpace_indexed x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "lab" ColorSpace
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ColorSpace_lab x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "pattern" ColorSpace
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ColorSpace_pattern x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "sep" ColorSpace
           (HS.Maybe (Vector.Vector (RTS.UInt 8))) where
  getField (ColorSpace_sep x) = HS.Just x
   
  getField _ = HS.Nothing
 
data FontOp
  = FontOp_setGlpyhWidthBoundingBox FontOp_1
  | FontOp_setGlyphWidth FontOp_0
  
 
deriving instance HS.Eq FontOp
 
deriving instance HS.Ord FontOp
 
deriving instance HS.Show FontOp
 
instance RTS.DDL FontOp where
 
instance HS.HasField "setGlpyhWidthBoundingBox" FontOp
           (HS.Maybe FontOp_1) where
  getField (FontOp_setGlpyhWidthBoundingBox x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "setGlyphWidth" FontOp
           (HS.Maybe FontOp_0) where
  getField (FontOp_setGlyphWidth x) = HS.Just x
   
  getField _ = HS.Nothing
 
data MarkedContentOp
  = MarkedContentOp_defMarkedContentPoint MarkedContentOp_1
  | MarkedContentOp_defineMarkedContent MarkedContentOp_0
  
 
deriving instance HS.Eq MarkedContentOp
 
deriving instance HS.Ord MarkedContentOp
 
deriving instance HS.Show MarkedContentOp
 
instance RTS.DDL MarkedContentOp where
 
instance HS.HasField "defMarkedContentPoint" MarkedContentOp
           (HS.Maybe MarkedContentOp_1) where
  getField (MarkedContentOp_defMarkedContentPoint x) = HS.Just x
   
  getField _ = HS.Nothing
 
instance HS.HasField "defineMarkedContent" MarkedContentOp
           (HS.Maybe MarkedContentOp_0) where
  getField (MarkedContentOp_defineMarkedContent x) = HS.Just x
   
  getField _ = HS.Nothing
 
pBot :: forall b. RTS.DDL b => D.Parser b -> D.Parser b
 
pBot (pP :: D.Parser b) =
  do RTS.pEnter "PdfValue._Guard" (PdfValue._Guard HS.False)
     (__ :: b) <- pP
     HS.pure __
 
_Cmp ::
  forall a b d h.
    (RTS.DDL a, RTS.DDL b, RTS.DDL d, RTS.DDL h,
     RTS.HasStruct a "num" d, RTS.HasStruct b "num" d,
     RTS.HasStruct a "exp" h, RTS.HasStruct b "exp" h) =>
      a -> (b -> D.Parser ())
 
_Cmp (a :: a) (b :: b) =
  (RTS.|||)
    (RTS.pEnter "PdfValue._Guard"
       (PdfValue._Guard (HS.getField @"num" a HS.< HS.getField @"num" b)))
    (do RTS.pEnter "PdfValue._Guard"
          (PdfValue._Guard (HS.getField @"num" a HS.== HS.getField @"num" b))
        RTS.pEnter "PdfValue._Guard"
          (PdfValue._Guard
             (HS.getField @"exp" a HS.<= HS.getField @"exp" b)))
 
pBoundedNonNeg ::
  forall a.
    (RTS.DDL a, RTS.HasStruct a "num" HS.Integer,
     RTS.HasStruct a "exp" HS.Integer) =>
      a -> D.Parser PdfValue.Number
 
pBoundedNonNeg (ub :: a) =
  do (__ :: PdfValue.Number) <-
       RTS.pEnter "PdfValue.UnsignedNumber" PdfValue.pUnsignedNumber
     RTS.pEnter "PdfContentStream._Cmp"
       (_Cmp @PdfValue.Number @a @HS.Integer @HS.Integer __ ub)
     HS.pure __
 
pByte :: D.Parser (RTS.UInt 8)
 
pByte =
  RTS.uint8
    HS.<$> RTS.pMatch1 "6:12--6:19"
             (RTS.bcRange (RTS.lit 0 :: RTS.UInt 8) (RTS.lit 255 :: RTS.UInt 8))
 
pClippingPathOp :: D.Parser ClippingPathOp
 
pClippingPathOp =
  (RTS.<||)
    (RTS.pEnter "setClippingEvenOdd"
       (do (_0 :: ()) <-
             RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "W*"))
           HS.pure (ClippingPathOp_setClippingEvenOdd _0)))
    (RTS.pEnter "setClippingNzWinding"
       (do (_1 :: ()) <-
             RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "W"))
           HS.pure (ClippingPathOp_setClippingNzWinding _1)))
 
pCmp ::
  forall a b d h.
    (RTS.DDL a, RTS.DDL b, RTS.DDL d, RTS.DDL h,
     RTS.HasStruct a "num" d, RTS.HasStruct b "num" d,
     RTS.HasStruct a "exp" h, RTS.HasStruct b "exp" h) =>
      a -> (b -> D.Parser ())
 
pCmp (a :: a) (b :: b) =
  (RTS.|||)
    (RTS.pEnter "PdfValue.Guard"
       (PdfValue.pGuard (HS.getField @"num" a HS.< HS.getField @"num" b)))
    (do RTS.pEnter "PdfValue._Guard"
          (PdfValue._Guard (HS.getField @"num" a HS.== HS.getField @"num" b))
        (__ :: ()) <-
          RTS.pEnter "PdfValue.Guard"
            (PdfValue.pGuard (HS.getField @"exp" a HS.<= HS.getField @"exp" b))
        HS.pure __)
 
pColorSpace :: D.Parser ColorSpace
 
pColorSpace =
  (RTS.<||)
    (RTS.pEnter "calRGB"
       (do (_2 :: Vector.Vector (RTS.UInt 8)) <-
             HS.pure (Vector.vecFromRep "/CalRGB")
           HS.pure (ColorSpace_calRGB _2)))
    ((RTS.<||)
       (RTS.pEnter "calGray"
          (do (_3 :: Vector.Vector (RTS.UInt 8)) <-
                HS.pure (Vector.vecFromRep "CalGray")
              HS.pure (ColorSpace_calGray _3)))
       ((RTS.<||)
          (RTS.pEnter "lab"
             (do (_4 :: Vector.Vector (RTS.UInt 8)) <-
                   HS.pure (Vector.vecFromRep "/Lab")
                 HS.pure (ColorSpace_lab _4)))
          ((RTS.<||)
             (RTS.pEnter "iccBased"
                (do (_5 :: Vector.Vector (RTS.UInt 8)) <-
                      HS.pure (Vector.vecFromRep "/ICCBased")
                    HS.pure (ColorSpace_iccBased _5)))
             ((RTS.<||)
                (RTS.pEnter "deviceRGB"
                   (do (_6 :: Vector.Vector (RTS.UInt 8)) <-
                         HS.pure (Vector.vecFromRep "/DeviceRGB")
                       HS.pure (ColorSpace_deviceRGB _6)))
                ((RTS.<||)
                   (RTS.pEnter "deviceCMYK"
                      (do (_7 :: Vector.Vector (RTS.UInt 8)) <-
                            HS.pure (Vector.vecFromRep "/DeviceCMYK")
                          HS.pure (ColorSpace_deviceCMYK _7)))
                   ((RTS.<||)
                      (RTS.pEnter "deviceGray"
                         (do (_8 :: Vector.Vector (RTS.UInt 8)) <-
                               HS.pure (Vector.vecFromRep "/DeviceGray")
                             HS.pure (ColorSpace_deviceGray _8)))
                      ((RTS.<||)
                         (RTS.pEnter "sep"
                            (do (_9 :: Vector.Vector (RTS.UInt 8)) <-
                                  HS.pure (Vector.vecFromRep "/Separation")
                                HS.pure (ColorSpace_sep _9)))
                         ((RTS.<||)
                            (RTS.pEnter "devN"
                               (do (_10 :: Vector.Vector (RTS.UInt 8)) <-
                                     HS.pure (Vector.vecFromRep "/DeviceN")
                                   HS.pure (ColorSpace_devN _10)))
                            ((RTS.<||)
                               (RTS.pEnter "indexed"
                                  (do (_11 :: Vector.Vector (RTS.UInt 8)) <-
                                        HS.pure (Vector.vecFromRep "/Indexed")
                                      HS.pure (ColorSpace_indexed _11)))
                               (RTS.pEnter "pattern"
                                  (do (_12 :: Vector.Vector (RTS.UInt 8)) <-
                                        HS.pure (Vector.vecFromRep "/Pattern")
                                      HS.pure (ColorSpace_pattern _12))))))))))))
 
pFractional :: D.Parser PdfValue.Number
 
pFractional =
  do (__ :: PdfValue.Number) <-
       RTS.pEnter "PdfValue.Number" PdfValue.pNumber
     do (_13 :: Fractional_0) <-
          do (num :: HS.Integer) <- HS.pure (RTS.lit 0 :: HS.Integer)
             (exp :: HS.Integer) <- HS.pure (RTS.lit 0 :: HS.Integer)
             HS.pure (Fractional_0 num exp)
        RTS.pEnter "PdfContentStream._Cmp"
          (_Cmp @Fractional_0 @PdfValue.Number @HS.Integer @HS.Integer _13
             __)
     do (_14 :: Fractional_1) <-
          do (num :: HS.Integer) <- HS.pure (RTS.lit 1 :: HS.Integer)
             (exp :: HS.Integer) <- HS.pure (RTS.lit 0 :: HS.Integer)
             HS.pure (Fractional_1 num exp)
        RTS.pEnter "PdfContentStream._Cmp"
          (_Cmp @PdfValue.Number @Fractional_1 @HS.Integer @HS.Integer __
             _14)
     HS.pure __
 
pColourOp :: D.Parser ColourOp
 
pColourOp =
  (RTS.<||)
    (RTS.pEnter "setColorSpaceStroking"
       (do (_15 :: ColourOp_0) <-
             do (nm :: Vector.Vector (RTS.UInt 8)) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
                       (RTS.pEnter "PdfValue.Name" PdfValue.pName))
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "CS"))
                HS.pure (ColourOp_0 nm)
           HS.pure (ColourOp_setColorSpaceStroking _15)))
    ((RTS.<||)
       (RTS.pEnter "setColorSpaceNonStroking"
          (do (_16 :: ColourOp_1) <-
                do (nm :: Vector.Vector (RTS.UInt 8)) <-
                     RTS.pEnter "PdfValue.Token"
                       (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
                          (RTS.pEnter "PdfValue.Name" PdfValue.pName))
                   RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "cs"))
                   HS.pure (ColourOp_1 nm)
              HS.pure (ColourOp_setColorSpaceNonStroking _16)))
       ((RTS.<||)
          (RTS.pEnter "setColorStroking"
             (do (_17 :: ColourOp_2) <-
                   do (cs :: Vector.Vector PdfValue.Number) <-
                        RTS.pMany (RTS.<||)
                          (RTS.pEnter "PdfValue.Token"
                             (PdfValue.pToken @PdfValue.Number
                                (RTS.pEnter "PdfValue.Number" PdfValue.pNumber)))
                      RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "SC"))
                      HS.pure (ColourOp_2 cs)
                 HS.pure (ColourOp_setColorStroking _17)))
          ((RTS.<||)
             (RTS.pEnter "setColorStrokingICC"
                (do (_18 :: ColourOp_3) <-
                      do (cs :: Vector.Vector PdfValue.Number) <-
                           RTS.pMany (RTS.<||)
                             (RTS.pEnter "PdfValue.Token"
                                (PdfValue.pToken @PdfValue.Number
                                   (RTS.pEnter "PdfValue.Number" PdfValue.pNumber)))
                         RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "SCN"))
                         HS.pure (ColourOp_3 cs)
                    HS.pure (ColourOp_setColorStrokingICC _18)))
             ((RTS.<||)
                (RTS.pEnter "setColorNonStroking"
                   (do (_19 :: ColourOp_4) <-
                         do (cs :: Vector.Vector PdfValue.Number) <-
                              RTS.pMany (RTS.<||)
                                (RTS.pEnter "PdfValue.Token"
                                   (PdfValue.pToken @PdfValue.Number
                                      (RTS.pEnter "PdfValue.Number" PdfValue.pNumber)))
                            RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "sc"))
                            HS.pure (ColourOp_4 cs)
                       HS.pure (ColourOp_setColorNonStroking _19)))
                ((RTS.<||)
                   (RTS.pEnter "setColorNonStrokingICC"
                      (do (_20 :: ColourOp_5) <-
                            do (cs :: Vector.Vector PdfValue.Number) <-
                                 RTS.pMany (RTS.<||)
                                   (RTS.pEnter "PdfValue.Token"
                                      (PdfValue.pToken @PdfValue.Number
                                         (RTS.pEnter "PdfValue.Number" PdfValue.pNumber)))
                               RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "scn"))
                               HS.pure (ColourOp_5 cs)
                          HS.pure (ColourOp_setColorNonStrokingICC _20)))
                   ((RTS.<||)
                      (RTS.pEnter "setGrayStroking"
                         (do (_21 :: ColourOp_6) <-
                               do (gray :: PdfValue.Number) <-
                                    RTS.pEnter "PdfValue.Token"
                                      (PdfValue.pToken @PdfValue.Number
                                         (RTS.pEnter "PdfContentStream.Fractional" pFractional))
                                  RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "G"))
                                  HS.pure (ColourOp_6 gray)
                             HS.pure (ColourOp_setGrayStroking _21)))
                      ((RTS.<||)
                         (RTS.pEnter "setGrayNonStroking"
                            (do (_22 :: ColourOp_7) <-
                                  do (gray :: PdfValue.Number) <-
                                       RTS.pEnter "PdfValue.Token"
                                         (PdfValue.pToken @PdfValue.Number
                                            (RTS.pEnter "PdfContentStream.Fractional" pFractional))
                                     RTS.pEnter "PdfValue._KW"
                                       (PdfValue._KW (Vector.vecFromRep "g"))
                                     HS.pure (ColourOp_7 gray)
                                HS.pure (ColourOp_setGrayNonStroking _22)))
                         ((RTS.<||)
                            (RTS.pEnter "setRGBStroking"
                               (do (_23 :: ColourOp_8) <-
                                     do (r :: PdfValue.Number) <-
                                          RTS.pEnter "PdfValue.Token"
                                            (PdfValue.pToken @PdfValue.Number
                                               (RTS.pEnter "PdfContentStream.Fractional"
                                                  pFractional))
                                        (g :: PdfValue.Number) <-
                                          RTS.pEnter "PdfValue.Token"
                                            (PdfValue.pToken @PdfValue.Number
                                               (RTS.pEnter "PdfContentStream.Fractional"
                                                  pFractional))
                                        (b :: PdfValue.Number) <-
                                          RTS.pEnter "PdfValue.Token"
                                            (PdfValue.pToken @PdfValue.Number
                                               (RTS.pEnter "PdfContentStream.Fractional"
                                                  pFractional))
                                        RTS.pEnter "PdfValue._KW"
                                          (PdfValue._KW (Vector.vecFromRep "RG"))
                                        HS.pure (ColourOp_8 r g b)
                                   HS.pure (ColourOp_setRGBStroking _23)))
                            ((RTS.<||)
                               (RTS.pEnter "setRGBNonStroking"
                                  (do (_24 :: ColourOp_9) <-
                                        do (r :: PdfValue.Number) <-
                                             RTS.pEnter "PdfValue.Token"
                                               (PdfValue.pToken @PdfValue.Number
                                                  (RTS.pEnter "PdfContentStream.Fractional"
                                                     pFractional))
                                           (g :: PdfValue.Number) <-
                                             RTS.pEnter "PdfValue.Token"
                                               (PdfValue.pToken @PdfValue.Number
                                                  (RTS.pEnter "PdfContentStream.Fractional"
                                                     pFractional))
                                           (b :: PdfValue.Number) <-
                                             RTS.pEnter "PdfValue.Token"
                                               (PdfValue.pToken @PdfValue.Number
                                                  (RTS.pEnter "PdfContentStream.Fractional"
                                                     pFractional))
                                           RTS.pEnter "PdfValue._KW"
                                             (PdfValue._KW (Vector.vecFromRep "rg"))
                                           HS.pure (ColourOp_9 r g b)
                                      HS.pure (ColourOp_setRGBNonStroking _24)))
                               ((RTS.<||)
                                  (RTS.pEnter "setCMYKStroking"
                                     (do (_25 :: ColourOp_10) <-
                                           do (c :: PdfValue.Number) <-
                                                RTS.pEnter "PdfValue.Token"
                                                  (PdfValue.pToken @PdfValue.Number
                                                     (RTS.pEnter "PdfContentStream.Fractional"
                                                        pFractional))
                                              (m :: PdfValue.Number) <-
                                                RTS.pEnter "PdfValue.Token"
                                                  (PdfValue.pToken @PdfValue.Number
                                                     (RTS.pEnter "PdfContentStream.Fractional"
                                                        pFractional))
                                              (y :: PdfValue.Number) <-
                                                RTS.pEnter "PdfValue.Token"
                                                  (PdfValue.pToken @PdfValue.Number
                                                     (RTS.pEnter "PdfContentStream.Fractional"
                                                        pFractional))
                                              (k :: PdfValue.Number) <-
                                                RTS.pEnter "PdfValue.Token"
                                                  (PdfValue.pToken @PdfValue.Number
                                                     (RTS.pEnter "PdfContentStream.Fractional"
                                                        pFractional))
                                              RTS.pEnter "PdfValue._KW"
                                                (PdfValue._KW (Vector.vecFromRep "K"))
                                              HS.pure (ColourOp_10 c m y k)
                                         HS.pure (ColourOp_setCMYKStroking _25)))
                                  (RTS.pEnter "setCMYKNonStroking"
                                     (do (_26 :: ColourOp_11) <-
                                           do (c :: PdfValue.Number) <-
                                                RTS.pEnter "PdfValue.Token"
                                                  (PdfValue.pToken @PdfValue.Number
                                                     (RTS.pEnter "PdfContentStream.Fractional"
                                                        pFractional))
                                              (m :: PdfValue.Number) <-
                                                RTS.pEnter "PdfValue.Token"
                                                  (PdfValue.pToken @PdfValue.Number
                                                     (RTS.pEnter "PdfContentStream.Fractional"
                                                        pFractional))
                                              (y :: PdfValue.Number) <-
                                                RTS.pEnter "PdfValue.Token"
                                                  (PdfValue.pToken @PdfValue.Number
                                                     (RTS.pEnter "PdfContentStream.Fractional"
                                                        pFractional))
                                              (k :: PdfValue.Number) <-
                                                RTS.pEnter "PdfValue.Token"
                                                  (PdfValue.pToken @PdfValue.Number
                                                     (RTS.pEnter "PdfContentStream.Fractional"
                                                        pFractional))
                                              RTS.pEnter "PdfValue._KW"
                                                (PdfValue._KW (Vector.vecFromRep "K"))
                                              HS.pure (ColourOp_11 c m y k)
                                         HS.pure (ColourOp_setCMYKNonStroking _26)))))))))))))
 
pGenArray ::
  forall c. RTS.DDL c => D.Parser c -> D.Parser (Vector.Vector c)
 
pGenArray (pP :: D.Parser c) =
  RTS.pEnter "PdfValue.Between"
    (PdfValue.pBetween @(Vector.Vector c) (Vector.vecFromRep "[")
       (Vector.vecFromRep "]")
       (RTS.pMany (RTS.<||) pP))
 
pIntent :: D.Parser Intent
 
pIntent =
  (RTS.<||)
    (RTS.pEnter "absoluteColorimetric"
       (do (_27 :: Vector.Vector (RTS.UInt 8)) <-
             HS.pure (Vector.vecFromRep "/Absolutecolorimetric")
           HS.pure (Intent_absoluteColorimetric _27)))
    ((RTS.<||)
       (RTS.pEnter "relativeColorimetric"
          (do (_28 :: Vector.Vector (RTS.UInt 8)) <-
                HS.pure (Vector.vecFromRep "/RelativeColorimetric")
              HS.pure (Intent_relativeColorimetric _28)))
       ((RTS.<||)
          (RTS.pEnter "saturation"
             (do (_29 :: Vector.Vector (RTS.UInt 8)) <-
                   HS.pure (Vector.vecFromRep "/Saturation")
                 HS.pure (Intent_saturation _29)))
          (RTS.pEnter "perceptual"
             (do (_30 :: Vector.Vector (RTS.UInt 8)) <-
                   HS.pure (Vector.vecFromRep "/Perceptual")
                 HS.pure (Intent_perceptual _30)))))
 
pLineStyle :: D.Parser (RTS.UInt 8)
 
pLineStyle =
  RTS.uint8
    HS.<$> RTS.pMatch1 "81:17--81:34"
             (RTS.bcRange (RTS.uint8 48) (RTS.uint8 50))
 
pGenGraphicsStateOp :: D.Parser GenGraphicsStateOp
 
pGenGraphicsStateOp =
  (RTS.<||)
    (RTS.pEnter "setLineWidth"
       (do (_31 :: GenGraphicsStateOp_0) <-
             do (lineWidth :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "w"))
                HS.pure (GenGraphicsStateOp_0 lineWidth)
           HS.pure (GenGraphicsStateOp_setLineWidth _31)))
    ((RTS.<||)
       (RTS.pEnter "setLineCapStyle"
          (do (_32 :: GenGraphicsStateOp_1) <-
                do (lineCap :: RTS.UInt 8) <-
                     RTS.pEnter "PdfValue.Token"
                       (PdfValue.pToken @(RTS.UInt 8)
                          (RTS.pEnter "PdfContentStream.LineStyle" pLineStyle))
                   RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "J"))
                   HS.pure (GenGraphicsStateOp_1 lineCap)
              HS.pure (GenGraphicsStateOp_setLineCapStyle _32)))
       ((RTS.<||)
          (RTS.pEnter "setLineJoinStyle"
             (do (_33 :: GenGraphicsStateOp_2) <-
                   do (lineJoin :: RTS.UInt 8) <-
                        RTS.pEnter "PdfValue.Token"
                          (PdfValue.pToken @(RTS.UInt 8)
                             (RTS.pEnter "PdfContentStream.LineStyle" pLineStyle))
                      RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "j"))
                      HS.pure (GenGraphicsStateOp_2 lineJoin)
                 HS.pure (GenGraphicsStateOp_setLineJoinStyle _33)))
          ((RTS.<||)
             (RTS.pEnter "setMiterLimit"
                (do (_34 :: GenGraphicsStateOp_3) <-
                      do (miterLimit :: PdfValue.Number) <-
                           RTS.pEnter "PdfValue.Token"
                             (PdfValue.pToken @PdfValue.Number
                                (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                         RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "M"))
                         HS.pure (GenGraphicsStateOp_3 miterLimit)
                    HS.pure (GenGraphicsStateOp_setMiterLimit _34)))
             ((RTS.<||)
                (RTS.pEnter "setLineDash"
                   (do (_35 :: GenGraphicsStateOp_4) <-
                         do (dashArray :: Vector.Vector HS.Integer) <-
                              RTS.pEnter "PdfValue.Token"
                                (PdfValue.pToken @(Vector.Vector HS.Integer)
                                   (RTS.pEnter "PdfContentStream.GenArray"
                                      (pGenArray @HS.Integer
                                         (RTS.pEnter "PdfValue.Token"
                                            (PdfValue.pToken @HS.Integer
                                               (RTS.pEnter "PdfValue.Natural"
                                                  PdfValue.pNatural))))))
                            (dashPhase :: PdfValue.Number) <-
                              RTS.pEnter "PdfValue.Token"
                                (PdfValue.pToken @PdfValue.Number
                                   (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                            RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "d"))
                            HS.pure (GenGraphicsStateOp_4 dashArray dashPhase)
                       HS.pure (GenGraphicsStateOp_setLineDash _35)))
                ((RTS.<||)
                   (RTS.pEnter "setColorRenderingIntent"
                      (do (_36 :: GenGraphicsStateOp_5) <-
                            do (intent :: Intent) <-
                                 RTS.pEnter "PdfValue.Token"
                                   (PdfValue.pToken @Intent
                                      (RTS.pEnter "PdfContentStream.Intent" pIntent))
                               RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "ri"))
                               HS.pure (GenGraphicsStateOp_5 intent)
                          HS.pure (GenGraphicsStateOp_setColorRenderingIntent _36)))
                   ((RTS.<||)
                      (RTS.pEnter "setFlat"
                         (do (_38 :: GenGraphicsStateOp_7) <-
                               do (flatness :: PdfValue.Number) <-
                                    RTS.pEnter "PdfValue.Token"
                                      (PdfValue.pToken @PdfValue.Number
                                         (do (_37 :: GenGraphicsStateOp_6) <-
                                               do (num :: HS.Integer) <-
                                                    HS.pure (RTS.lit 100 :: HS.Integer)
                                                  (exp :: HS.Integer) <-
                                                    HS.pure (RTS.lit 0 :: HS.Integer)
                                                  HS.pure (GenGraphicsStateOp_6 num exp)
                                             RTS.pEnter "PdfContentStream.BoundedNonNeg"
                                               (pBoundedNonNeg @GenGraphicsStateOp_6 _37)))
                                  RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "i"))
                                  HS.pure (GenGraphicsStateOp_7 flatness)
                             HS.pure (GenGraphicsStateOp_setFlat _38)))
                      (RTS.pEnter "setGraphicsStateParams"
                         (do (_39 :: GenGraphicsStateOp_8) <-
                               do (dictName :: Vector.Vector (RTS.UInt 8)) <-
                                    RTS.pEnter "PdfValue.Token"
                                      (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
                                         (RTS.pEnter "PdfValue.Name" PdfValue.pName))
                                  RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "gs"))
                                  HS.pure (GenGraphicsStateOp_8 dictName)
                             HS.pure (GenGraphicsStateOp_setGraphicsStateParams _39)))))))))
 
pKeyObjsToMap ::
  forall a b c d e.
    (RTS.DDL a, RTS.DDL b, RTS.DDL c, RTS.DDL d, RTS.DDL e,
     RTS.IsLoop a, RTS.ColElType a d, RTS.ColElType a e,
     RTS.HasStruct e "key" b, RTS.HasStruct e "obj" c) =>
      a -> D.Parser (Map.Map b c)
 
pKeyObjsToMap (ents :: a) =
  RTS.loopFoldM
    (\(d :: Map.Map b c) (e :: e) ->
       RTS.pIsJust "17:31--17:50" "Key already present"
         (Map.insertMaybe (HS.getField @"key" e) (HS.getField @"obj" e) d))
    (Map.empty :: Map.Map b c)
    ents
 
pGenDict ::
  forall j.
    RTS.DDL j =>
      D.Parser j -> D.Parser (Map.Map (Vector.Vector (RTS.UInt 8)) j)
 
pGenDict (pObj :: D.Parser j) =
  do (ents :: Vector.Vector (GenDict_0 j)) <-
       RTS.pEnter "PdfValue.Between"
         (PdfValue.pBetween @(Vector.Vector (GenDict_0 j))
            (Vector.vecFromRep "<<")
            (Vector.vecFromRep ">>")
            (RTS.pMany (RTS.<||)
               (do (key :: Vector.Vector (RTS.UInt 8)) <-
                     RTS.pEnter "PdfValue.Name" PdfValue.pName
                   (obj :: j) <- pObj
                   HS.pure (GenDict_0 key obj))))
     (__ :: Map.Map (Vector.Vector (RTS.UInt 8)) j) <-
       RTS.pEnter "PdfContentStream.KeyObjsToMap"
         (pKeyObjsToMap @(Vector.Vector (GenDict_0 j))
            @(Vector.Vector (RTS.UInt 8))
            @j
            @HS.Integer
            @(GenDict_0 j)
            ents)
     HS.pure __
 
pGenDirectObj ::
  forall i. RTS.DDL i => D.Parser i -> D.Parser (GenDirectObj i)
 
pGenDirectObj (pObj :: D.Parser i) =
  (RTS.<||)
    (RTS.pEnter "null"
       (do (_40 :: ()) <- RTS.pEnter "PdfValue.Null" PdfValue.pNull
           HS.pure (GenDirectObj_null _40)))
    ((RTS.<||)
       (RTS.pEnter "bool"
          (do (_41 :: HS.Bool) <- RTS.pEnter "PdfValue.Bool" PdfValue.pBool
              HS.pure (GenDirectObj_bool _41)))
       ((RTS.<||)
          (RTS.pEnter "name"
             (do (_42 :: Vector.Vector (RTS.UInt 8)) <-
                   RTS.pEnter "PdfValue.Name" PdfValue.pName
                 HS.pure (GenDirectObj_name _42)))
          ((RTS.<||)
             (RTS.pEnter "string"
                (do (_43 :: Vector.Vector (RTS.UInt 8)) <-
                      RTS.pEnter "PdfValue.String" PdfValue.pString
                    HS.pure (GenDirectObj_string _43)))
             ((RTS.<||)
                (RTS.pEnter "string"
                   (do (_44 :: Vector.Vector (RTS.UInt 8)) <-
                         RTS.pEnter "PdfValue.HexString" PdfValue.pHexString
                       HS.pure (GenDirectObj_string _44)))
                ((RTS.<||)
                   (RTS.pEnter "number"
                      (do (_45 :: PdfValue.Number) <-
                            RTS.pEnter "PdfValue.Number" PdfValue.pNumber
                          HS.pure (GenDirectObj_number _45)))
                   ((RTS.<||)
                      (RTS.pEnter "array"
                         (do (_46 :: Vector.Vector i) <-
                               RTS.pEnter "PdfContentStream.GenArray" (pGenArray @i pObj)
                             HS.pure (GenDirectObj_array _46)))
                      (RTS.pEnter "dict"
                         (do (_47 :: Map.Map (Vector.Vector (RTS.UInt 8)) i) <-
                               RTS.pEnter "PdfContentStream.GenDict" (pGenDict @i pObj)
                             HS.pure (GenDirectObj_dict _47)))))))))
 
pDirectObj :: D.Parser DirectObj
 
pDirectObj =
  do (box :: GenDirectObj DirectObj) <-
       RTS.pEnter "PdfContentStream.GenDirectObj"
         (pGenDirectObj @DirectObj
            (RTS.pEnter "PdfContentStream.DirectObj" pDirectObj))
     HS.pure (DirectObj box)
 
pLastElt ::
  forall a c d.
    (RTS.DDL a, RTS.DDL c, RTS.DDL d, RTS.IsLoop a, RTS.ColElType a c,
     RTS.ColElType a d) =>
      a -> D.Parser (HS.Maybe d)
 
pLastElt (fs :: a) =
  RTS.loopFoldM
    (\(last :: HS.Maybe d) (f :: d) -> HS.pure (HS.Just f))
    (HS.Nothing :: HS.Maybe d)
    fs
 
pLookupDirectNat ::
  forall a.
    RTS.DDL a => a -> (Map.Map a DirectObj -> D.Parser HS.Integer)
 
pLookupDirectNat (k :: a) (m :: Map.Map a DirectObj) =
  do (vV :: DirectObj) <-
       RTS.pIsJust "457:11--457:20"
         ("Missing key: " HS.++ HS.show (k :: a))
         (Map.lookup k m)
     (v :: PdfValue.Number) <-
       RTS.pIsJust "458:11--458:26" "Expected `number`"
         (HS.getField @"number" (HS.getField @"box" vV))
     (__ :: HS.Integer) <-
       RTS.pEnter "PdfValue.NumberAsNat" (PdfValue.pNumberAsNat v)
     HS.pure __
 
_Default2 :: forall a. RTS.DDL a => D.Parser () -> D.Parser ()
 
_Default2 (_P :: D.Parser ()) = (RTS.<||) _P (HS.pure ())
 
_GenArray :: forall c. RTS.DDL c => D.Parser () -> D.Parser ()
 
_GenArray (_P :: D.Parser ()) =
  RTS.pEnter "PdfValue._Between"
    (PdfValue._Between @(Vector.Vector c) (Vector.vecFromRep "[")
       (Vector.vecFromRep "]")
       (RTS.pSkipMany (RTS.<||) _P))
 
_KeyObjsToMap ::
  forall a b c d e.
    (RTS.DDL a, RTS.DDL b, RTS.DDL c, RTS.DDL d, RTS.DDL e,
     RTS.IsLoop a, RTS.ColElType a d, RTS.ColElType a e,
     RTS.HasStruct e "key" b, RTS.HasStruct e "obj" c) =>
      a -> D.Parser (Map.Map b c)
 
_KeyObjsToMap (ents :: a) =
  RTS.loopFoldM
    (\(d :: Map.Map b c) (e :: e) ->
       RTS.pIsJust "17:31--17:50" "Key already present"
         (Map.insertMaybe (HS.getField @"key" e) (HS.getField @"obj" e) d))
    (Map.empty :: Map.Map b c)
    ents
 
_GenDict :: forall j. RTS.DDL j => D.Parser j -> D.Parser ()
 
_GenDict (pObj :: D.Parser j) =
  do (ents :: Vector.Vector (GenDict_0 j)) <-
       RTS.pEnter "PdfValue.Between"
         (PdfValue.pBetween @(Vector.Vector (GenDict_0 j))
            (Vector.vecFromRep "<<")
            (Vector.vecFromRep ">>")
            (RTS.pMany (RTS.<||)
               (do (key :: Vector.Vector (RTS.UInt 8)) <-
                     RTS.pEnter "PdfValue.Name" PdfValue.pName
                   (obj :: j) <- pObj
                   HS.pure (GenDict_0 key obj))))
     RTS.pEnter "PdfContentStream._KeyObjsToMap"
       (_KeyObjsToMap @(Vector.Vector (GenDict_0 j))
          @(Vector.Vector (RTS.UInt 8))
          @j
          @HS.Integer
          @(GenDict_0 j)
          ents)
 
_GenDirectObj ::
  forall i. RTS.DDL i => D.Parser i -> (D.Parser () -> D.Parser ())
 
_GenDirectObj (pObj :: D.Parser i) (_Obj :: D.Parser ()) =
  (RTS.<||)
    (RTS.pEnter "null" (RTS.pEnter "PdfValue._Null" PdfValue._Null))
    ((RTS.<||)
       (RTS.pEnter "bool" (RTS.pEnter "PdfValue._Bool" PdfValue._Bool))
       ((RTS.<||)
          (RTS.pEnter "name" (RTS.pEnter "PdfValue._Name" PdfValue._Name))
          ((RTS.<||)
             (RTS.pEnter "string"
                (RTS.pEnter "PdfValue._String" PdfValue._String))
             ((RTS.<||)
                (RTS.pEnter "string"
                   (RTS.pEnter "PdfValue._HexString" PdfValue._HexString))
                ((RTS.<||)
                   (RTS.pEnter "number"
                      (RTS.pEnter "PdfValue._Number" PdfValue._Number))
                   ((RTS.<||)
                      (RTS.pEnter "array"
                         (RTS.pEnter "PdfContentStream._GenArray" (_GenArray @i _Obj)))
                      (RTS.pEnter "dict"
                         (RTS.pEnter "PdfContentStream._GenDict" (_GenDict @i pObj)))))))))
 
_DirectObj :: D.Parser ()
 
_DirectObj =
  RTS.pEnter "PdfContentStream._GenDirectObj"
    (_GenDirectObj @DirectObj
       (RTS.pEnter "PdfContentStream.DirectObj" pDirectObj)
       (do HS.void (RTS.pEnter "PdfContentStream.DirectObj" pDirectObj)
           HS.pure ()))
 
_DirectArray :: D.Parser ()
 
_DirectArray =
  RTS.pEnter "PdfContentStream._GenArray"
    (_GenArray @DirectObj
       (RTS.pEnter "PdfContentStream._DirectObj" _DirectObj))
 
_DirectDict :: D.Parser ()
 
_DirectDict =
  RTS.pEnter "PdfContentStream._GenDict"
    (_GenDict @DirectObj
       (RTS.pEnter "PdfContentStream.DirectObj" pDirectObj))
 
pInlineImageObj :: D.Parser InlineImageObj
 
pInlineImageObj =
  do RTS.pEnter "PdfValue._KW"
       (PdfValue._KW (Vector.vecFromRep "BI"))
     (hdrEnts :: Vector.Vector InlineImageObj_5) <-
       RTS.pMany (RTS.<||)
         (do (key :: Vector.Vector (RTS.UInt 8)) <-
               RTS.pEnter "PdfValue.Token"
                 (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
                    (RTS.pEnter "PdfValue.Name" PdfValue.pName))
             (RTS.<||)
               (RTS.pEnter "bpc"
                  (do RTS.pEnter "PdfValue._Guard"
                        (PdfValue._Guard
                           ((key HS.== Vector.vecFromRep "BitsPerComponent")
                              HS.|| (key HS.== Vector.vecFromRep "BPC")))
                      RTS.pEnter "PdfValue._Natural" PdfValue._Natural))
               ((RTS.<||)
                  (RTS.pEnter "colorSpace"
                     (do RTS.pEnter "PdfValue._Guard"
                           (PdfValue._Guard
                              ((key HS.== Vector.vecFromRep "ColorSpace")
                                 HS.|| (key HS.== Vector.vecFromRep "CS")))
                         (RTS.<||)
                           (RTS.pEnter "nm" (RTS.pEnter "PdfValue._Name" PdfValue._Name))
                           (RTS.pEnter "arr"
                              (RTS.pEnter "PdfContentStream._DirectArray" _DirectArray))))
                  ((RTS.<||)
                     (RTS.pEnter "decode"
                        (do RTS.pEnter "PdfValue._Guard"
                              (PdfValue._Guard
                                 ((key HS.== Vector.vecFromRep "Decode")
                                    HS.|| (key HS.== Vector.vecFromRep "D")))
                            RTS.pEnter "PdfContentStream._GenArray"
                              (_GenArray @PdfValue.Number
                                 (RTS.pEnter "PdfValue._Number" PdfValue._Number))))
                     ((RTS.<||)
                        (RTS.pEnter "decodeParams"
                           (do RTS.pEnter "PdfValue._Guard"
                                 (PdfValue._Guard
                                    ((key HS.== Vector.vecFromRep "DecodeParms")
                                       HS.|| (key HS.== Vector.vecFromRep "DP")))
                               (RTS.<||)
                                 (RTS.pEnter "d"
                                    (RTS.pEnter "PdfContentStream._DirectDict" _DirectDict))
                                 (RTS.pEnter "arr"
                                    (RTS.pEnter "PdfContentStream._GenArray"
                                       (_GenArray @(Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj)
                                          (RTS.pEnter "PdfContentStream._DirectDict"
                                             _DirectDict))))))
                        ((RTS.<||)
                           (RTS.pEnter "filter"
                              (do RTS.pEnter "PdfValue._Guard"
                                    (PdfValue._Guard
                                       ((key HS.== Vector.vecFromRep "Filter")
                                          HS.|| (key HS.== Vector.vecFromRep "F")))
                                  (RTS.<||)
                                    (RTS.pEnter "name" (RTS.pEnter "PdfValue._Name" PdfValue._Name))
                                    (RTS.pEnter "names"
                                       (RTS.pEnter "PdfContentStream._GenArray"
                                          (_GenArray @(Vector.Vector (RTS.UInt 8))
                                             (RTS.pEnter "PdfValue._Name" PdfValue._Name))))))
                           ((RTS.<||)
                              (RTS.pEnter "height"
                                 (do RTS.pEnter "PdfValue._Guard"
                                       (PdfValue._Guard
                                          ((key HS.== Vector.vecFromRep "Height")
                                             HS.|| (key HS.== Vector.vecFromRep "H")))
                                     RTS.pEnter "PdfValue._Natural" PdfValue._Natural))
                              ((RTS.<||)
                                 (RTS.pEnter "imageMask"
                                    (do RTS.pEnter "PdfValue._Guard"
                                          (PdfValue._Guard
                                             ((key HS.== Vector.vecFromRep "ImageMask")
                                                HS.|| (key HS.== Vector.vecFromRep "IM")))
                                        RTS.pEnter "PdfValue._Bool" PdfValue._Bool))
                                 (RTS.pEnter "intent"
                                    (do RTS.pEnter "PdfValue._Guard"
                                          (PdfValue._Guard (key HS.== Vector.vecFromRep "Intent"))
                                        (RTS.<||) (RTS.pEnter "absColorimetric" (HS.pure ()))
                                          ((RTS.<||) (RTS.pEnter "relColorimetric" (HS.pure ()))
                                             ((RTS.<||) (RTS.pEnter "sat" (HS.pure ()))
                                                (RTS.pEnter "perceptual" (HS.pure ()))))))))))))
             (value :: DirectObj) <-
               RTS.pEnter "PdfValue.Token"
                 (PdfValue.pToken @DirectObj
                    (RTS.pEnter "PdfContentStream.DirectObj" pDirectObj))
             HS.pure (InlineImageObj_5 key value))
     (hdr :: Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj) <-
       RTS.loopFoldM
         (\(d :: Map.Map (Vector.Vector (RTS.UInt 8))
                   DirectObj) (e :: InlineImageObj_5) ->
            RTS.pIsJust "524:40--524:61" "Key already present"
              (Map.insertMaybe (HS.getField @"key" e) (HS.getField @"value" e)
                 d))
         (Map.empty :: Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj)
         hdrEnts
     (len :: HS.Integer) <-
       (RTS.|||)
         (RTS.pEnter "PdfContentStream.LookupDirectNat"
            (pLookupDirectNat @(Vector.Vector (RTS.UInt 8))
               (Vector.vecFromRep "Length")
               hdr))
         (RTS.pEnter "PdfContentStream.LookupDirectNat"
            (pLookupDirectNat @(Vector.Vector (RTS.UInt 8))
               (Vector.vecFromRep "L")
               hdr))
     RTS.pEnter "PdfValue._Guard"
       (PdfValue._Guard (len HS.<= (RTS.lit 4096 :: HS.Integer)))
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "ID"))
     HS.const ()
       HS.<$> RTS.pMatch1 "533:13--533:21" PdfValue.cs_simpleWS
     RTS.pEnter "PdfContentStream._Default2"
       (_Default2 @(Vector.Vector (RTS.UInt 8))
          (do (filtersObj :: DirectObj) <-
                (RTS.|||)
                  (RTS.pIsJust "535:20--535:38"
                     ("Missing key: "
                        HS.++ HS.show
                                (Vector.vecFromRep "Filter" :: Vector.Vector (RTS.UInt 8)))
                     (Map.lookup (Vector.vecFromRep "Filter") hdr))
                  (RTS.pIsJust "535:44--535:57"
                     ("Missing key: "
                        HS.++ HS.show
                                (Vector.vecFromRep "F" :: Vector.Vector (RTS.UInt 8)))
                     (Map.lookup (Vector.vecFromRep "F") hdr))
              (filters :: Vector.Vector DirectObj) <-
                RTS.pIsJust "536:16--536:38" "Expected `array`"
                  (HS.getField @"array" (HS.getField @"box" filtersObj))
              (filterNames :: Vector.Vector (Vector.Vector (RTS.UInt 8))) <-
                RTS.loopMapM
                  (\(fobj :: DirectObj) ->
                     do (__ :: Vector.Vector (RTS.UInt 8)) <-
                          RTS.pIsJust "539:7--539:22" "Expected `name`"
                            (HS.getField @"name" (HS.getField @"box" fobj))
                        HS.pure __)
                  filters
                  :: D.Parser (Vector.Vector (Vector.Vector (RTS.UInt 8)))
              (lastFilter :: HS.Maybe (Vector.Vector (RTS.UInt 8))) <-
                RTS.pEnter "PdfContentStream.LastElt"
                  (pLastElt @(Vector.Vector (Vector.Vector (RTS.UInt 8))) @HS.Integer
                     @(Vector.Vector (RTS.UInt 8))
                     filterNames)
              (lastF :: Vector.Vector (RTS.UInt 8)) <-
                RTS.pIsJust "542:14--542:31" "Expected `Just`" lastFilter
              RTS.pEnter "PdfValue._Guard"
                (PdfValue._Guard
                   ((lastF HS.== Vector.vecFromRep "ASCIIHexDecode")
                      HS.|| (lastF HS.== Vector.vecFromRep "ASCII85Decode")))
              RTS.pSkipMany (RTS.<||)
                (RTS.pEnter "PdfValue._AnyWS" PdfValue._AnyWS)))
     (imageData :: Vector.Vector (RTS.UInt 8)) <-
       Vector.replicateM len (RTS.pEnter "PdfContentStream.Byte" pByte)
     RTS.pSkipMany (RTS.<||)
       (RTS.pEnter "PdfValue._AnyWS" PdfValue._AnyWS)
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "EI"))
     HS.pure (InlineImageObj hdrEnts hdr len imageData)
 
pContentProps :: D.Parser ContentProps
 
pContentProps =
  (RTS.|||)
    (RTS.pEnter "inline"
       (do (_66 :: Map.Map (Vector.Vector (RTS.UInt 8)) PdfValue.Value) <-
             RTS.pEnter "PdfValue.Dict" PdfValue.pDict
           HS.pure (ContentProps_inline _66)))
    (RTS.pEnter "nm"
       (do (_67 :: Vector.Vector (RTS.UInt 8)) <-
             RTS.pEnter "PdfValue.Name" PdfValue.pName
           HS.pure (ContentProps_nm _67)))
 
pContentPoint :: D.Parser ContentPoint
 
pContentPoint =
  do (x :: PdfValue.Number) <-
       RTS.pEnter "PdfValue.Token"
         (PdfValue.pToken @PdfValue.Number
            (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
     (y :: PdfValue.Number) <-
       RTS.pEnter "PdfValue.Token"
         (PdfValue.pToken @PdfValue.Number
            (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
     HS.pure (ContentPoint x y)
 
pPathBeginOp :: D.Parser PathBeginOp
 
pPathBeginOp =
  (RTS.<||)
    (RTS.pEnter "beginNewSuppath"
       (do (_68 :: PathBeginOp_0) <-
             do (pt :: ContentPoint) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @ContentPoint
                       (RTS.pEnter "PdfContentStream.ContentPoint" pContentPoint))
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "m"))
                HS.pure (PathBeginOp_0 pt)
           HS.pure (PathBeginOp_beginNewSuppath _68)))
    (RTS.pEnter "appendRect"
       (do (_69 :: PathBeginOp_1) <-
             do (pt :: ContentPoint) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @ContentPoint
                       (RTS.pEnter "PdfContentStream.ContentPoint" pContentPoint))
                (width :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                (height :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "re"))
                HS.pure (PathBeginOp_1 pt width height)
           HS.pure (PathBeginOp_appendRect _69)))
 
pPathConsOp :: D.Parser PathConsOp
 
pPathConsOp =
  (RTS.<||)
    (RTS.pEnter "beginSubpath"
       (do (_70 :: PathBeginOp) <-
             RTS.pEnter "PdfContentStream.PathBeginOp" pPathBeginOp
           HS.pure (PathConsOp_beginSubpath _70)))
    ((RTS.<||)
       (RTS.pEnter "appendLine"
          (do (_71 :: PathConsOp_0) <-
                do (pt :: ContentPoint) <-
                     RTS.pEnter "PdfValue.Token"
                       (PdfValue.pToken @ContentPoint
                          (RTS.pEnter "PdfContentStream.ContentPoint" pContentPoint))
                   RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "l"))
                   HS.pure (PathConsOp_0 pt)
              HS.pure (PathConsOp_appendLine _71)))
       ((RTS.<||)
          (RTS.pEnter "appendCurvedThreePoints"
             (do (_72 :: PathConsOp_1) <-
                   do (pt1 :: ContentPoint) <-
                        RTS.pEnter "PdfValue.Token"
                          (PdfValue.pToken @ContentPoint
                             (RTS.pEnter "PdfContentStream.ContentPoint" pContentPoint))
                      (pt2 :: ContentPoint) <-
                        RTS.pEnter "PdfValue.Token"
                          (PdfValue.pToken @ContentPoint
                             (RTS.pEnter "PdfContentStream.ContentPoint" pContentPoint))
                      (pt3 :: ContentPoint) <-
                        RTS.pEnter "PdfValue.Token"
                          (PdfValue.pToken @ContentPoint
                             (RTS.pEnter "PdfContentStream.ContentPoint" pContentPoint))
                      RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "c"))
                      HS.pure (PathConsOp_1 pt1 pt2 pt3)
                 HS.pure (PathConsOp_appendCurvedThreePoints _72)))
          ((RTS.<||)
             (RTS.pEnter "appendCurvedInitPtRepl"
                (do (_73 :: PathConsOp_2) <-
                      do (pt2 :: ContentPoint) <-
                           RTS.pEnter "PdfValue.Token"
                             (PdfValue.pToken @ContentPoint
                                (RTS.pEnter "PdfContentStream.ContentPoint" pContentPoint))
                         (pt3 :: ContentPoint) <-
                           RTS.pEnter "PdfValue.Token"
                             (PdfValue.pToken @ContentPoint
                                (RTS.pEnter "PdfContentStream.ContentPoint" pContentPoint))
                         RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "v"))
                         HS.pure (PathConsOp_2 pt2 pt3)
                    HS.pure (PathConsOp_appendCurvedInitPtRepl _73)))
             ((RTS.<||)
                (RTS.pEnter "appendCurvedFinalPt"
                   (do (_74 :: PathConsOp_3) <-
                         do (pt1 :: ContentPoint) <-
                              RTS.pEnter "PdfValue.Token"
                                (PdfValue.pToken @ContentPoint
                                   (RTS.pEnter "PdfContentStream.ContentPoint" pContentPoint))
                            (pt3 :: ContentPoint) <-
                              RTS.pEnter "PdfValue.Token"
                                (PdfValue.pToken @ContentPoint
                                   (RTS.pEnter "PdfContentStream.ContentPoint" pContentPoint))
                            RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "y"))
                            HS.pure (PathConsOp_3 pt1 pt3)
                       HS.pure (PathConsOp_appendCurvedFinalPt _74)))
                (RTS.pEnter "closeSubpath"
                   (do (_75 :: ()) <-
                         RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "h"))
                       HS.pure (PathConsOp_closeSubpath _75)))))))
 
pPathPaintingOp :: D.Parser PathPaintingOp
 
pPathPaintingOp =
  (RTS.<||)
    (RTS.pEnter "stroke"
       (do (_76 :: ()) <-
             RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "S"))
           HS.pure (PathPaintingOp_stroke _76)))
    ((RTS.<||)
       (RTS.pEnter "closeStrokePath"
          (do (_77 :: ()) <-
                RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "s"))
              HS.pure (PathPaintingOp_closeStrokePath _77)))
       ((RTS.<||)
          (RTS.pEnter "fillPathNzWindingOld"
             (do (_78 :: ()) <-
                   RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "F"))
                 HS.pure (PathPaintingOp_fillPathNzWindingOld _78)))
          ((RTS.<||)
             (RTS.pEnter "fillPathEvenOdd"
                (do (_79 :: ()) <-
                      RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "f*"))
                    HS.pure (PathPaintingOp_fillPathEvenOdd _79)))
             ((RTS.<||)
                (RTS.pEnter "fillPathNzWinding"
                   (do (_80 :: ()) <-
                         RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "f"))
                       HS.pure (PathPaintingOp_fillPathNzWinding _80)))
                ((RTS.<||)
                   (RTS.pEnter "fillStrokeEvenOdd"
                      (do (_81 :: ()) <-
                            RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "B*"))
                          HS.pure (PathPaintingOp_fillStrokeEvenOdd _81)))
                   ((RTS.<||)
                      (RTS.pEnter "fillStroke"
                         (do (_82 :: ()) <-
                               RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "B"))
                             HS.pure (PathPaintingOp_fillStroke _82)))
                      ((RTS.<||)
                         (RTS.pEnter "closeFillStrokeEvenOdd"
                            (do (_83 :: ()) <-
                                  RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "b*"))
                                HS.pure (PathPaintingOp_closeFillStrokeEvenOdd _83)))
                         ((RTS.<||)
                            (RTS.pEnter "closeFillStrokeNzWinding"
                               (do (_84 :: ()) <-
                                     RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "b"))
                                   HS.pure (PathPaintingOp_closeFillStrokeNzWinding _84)))
                            (RTS.pEnter "endPath"
                               (do (_85 :: ()) <-
                                     RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "n"))
                                   HS.pure (PathPaintingOp_endPath _85)))))))))))
 
pPathObj :: D.Parser PathObj
 
pPathObj =
  do (begin :: PathBeginOp) <-
       RTS.pEnter "PdfContentStream.PathBeginOp" pPathBeginOp
     (pathOps :: Vector.Vector PathConsOp) <-
       RTS.pMany (RTS.<||)
         (RTS.pEnter "PdfContentStream.PathConsOp" pPathConsOp)
     (clippy :: HS.Maybe ClippingPathOp) <-
       RTS.pOptional (RTS.<||) HS.Just
         (RTS.pEnter "PdfContentStream.ClippingPathOp" pClippingPathOp)
     (paint :: PathPaintingOp) <-
       RTS.pEnter "PdfContentStream.PathPaintingOp" pPathPaintingOp
     HS.pure (PathObj begin pathOps clippy paint)
 
pShadingObj :: D.Parser ShadingObj
 
pShadingObj =
  do (name :: Vector.Vector (RTS.UInt 8)) <-
       RTS.pEnter "PdfValue.Token"
         (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
            (RTS.pEnter "PdfValue.Name" PdfValue.pName))
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "sh"))
     HS.pure (ShadingObj name)
 
pTextPosOp :: D.Parser TextPosOp
 
pTextPosOp =
  do (moveTextPos :: TextPosOp_0) <-
       do (tx :: PdfValue.Number) <-
            RTS.pEnter "PdfValue.Token"
              (PdfValue.pToken @PdfValue.Number
                 (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
          (ty :: PdfValue.Number) <-
            RTS.pEnter "PdfValue.Token"
              (PdfValue.pToken @PdfValue.Number
                 (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
          RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Td"))
          HS.pure (TextPosOp_0 tx ty)
     (moveTextPosSetLeading :: TextPosOp_1) <-
       do (tx :: PdfValue.Number) <-
            RTS.pEnter "PdfValue.Token"
              (PdfValue.pToken @PdfValue.Number
                 (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
          (ty :: PdfValue.Number) <-
            RTS.pEnter "PdfValue.Token"
              (PdfValue.pToken @PdfValue.Number
                 (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
          RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "TD"))
          HS.pure (TextPosOp_1 tx ty)
     (setTextMatrix :: TextPosOp_2) <-
       do (a :: PdfValue.Number) <-
            RTS.pEnter "PdfValue.Token"
              (PdfValue.pToken @PdfValue.Number
                 (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
          (b :: PdfValue.Number) <-
            RTS.pEnter "PdfValue.Token"
              (PdfValue.pToken @PdfValue.Number
                 (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
          (c :: PdfValue.Number) <-
            RTS.pEnter "PdfValue.Token"
              (PdfValue.pToken @PdfValue.Number
                 (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
          (d :: PdfValue.Number) <-
            RTS.pEnter "PdfValue.Token"
              (PdfValue.pToken @PdfValue.Number
                 (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
          (e :: PdfValue.Number) <-
            RTS.pEnter "PdfValue.Token"
              (PdfValue.pToken @PdfValue.Number
                 (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
          (f :: PdfValue.Number) <-
            RTS.pEnter "PdfValue.Token"
              (PdfValue.pToken @PdfValue.Number
                 (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
          RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tm"))
          HS.pure (TextPosOp_2 a b c d e f)
     (moveStartText :: ()) <-
       RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "T*"))
     HS.pure
       (TextPosOp moveTextPos moveTextPosSetLeading setTextMatrix
          moveStartText)
 
pShowVal :: D.Parser ShowVal
 
pShowVal =
  (RTS.<||)
    (RTS.pEnter "str"
       (do (_86 :: Vector.Vector (RTS.UInt 8)) <-
             RTS.pEnter "PdfValue.String" PdfValue.pString
           HS.pure (ShowVal_str _86)))
    (RTS.pEnter "num"
       (do (_87 :: PdfValue.Number) <-
             RTS.pEnter "PdfValue.Number" PdfValue.pNumber
           HS.pure (ShowVal_num _87)))
 
pTextShowOp :: D.Parser TextShowOp
 
pTextShowOp =
  (RTS.<||)
    (RTS.pEnter "showText"
       (do (_88 :: TextShowOp_0) <-
             do (str :: Vector.Vector (RTS.UInt 8)) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
                       (RTS.pEnter "PdfValue.String" PdfValue.pString))
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tj"))
                HS.pure (TextShowOp_0 str)
           HS.pure (TextShowOp_showText _88)))
    ((RTS.<||)
       (RTS.pEnter "moveShow"
          (do (_89 :: TextShowOp_1) <-
                do (str :: Vector.Vector (RTS.UInt 8)) <-
                     RTS.pEnter "PdfValue.Token"
                       (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
                          (RTS.pEnter "PdfValue.String" PdfValue.pString))
                   RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "'"))
                   HS.pure (TextShowOp_1 str)
              HS.pure (TextShowOp_moveShow _89)))
       ((RTS.<||)
          (RTS.pEnter "setSpacing"
             (do (_90 :: TextShowOp_2) <-
                   do (aw :: PdfValue.Number) <-
                        RTS.pEnter "PdfValue.Token"
                          (PdfValue.pToken @PdfValue.Number
                             (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                      (ac :: PdfValue.Number) <-
                        RTS.pEnter "PdfValue.Token"
                          (PdfValue.pToken @PdfValue.Number
                             (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                      RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "\""))
                      HS.pure (TextShowOp_2 aw ac)
                 HS.pure (TextShowOp_setSpacing _90)))
          (RTS.pEnter "showTextIndGlyph"
             (do (_91 :: TextShowOp_3) <-
                   do (arr :: Vector.Vector ShowVal) <-
                        RTS.pEnter "PdfValue.Token"
                          (PdfValue.pToken @(Vector.Vector ShowVal)
                             (RTS.pEnter "PdfContentStream.GenArray"
                                (pGenArray @ShowVal
                                   (RTS.pEnter "PdfValue.Token"
                                      (PdfValue.pToken @ShowVal
                                         (RTS.pEnter "PdfContentStream.ShowVal" pShowVal))))))
                      RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "TJ"))
                      HS.pure (TextShowOp_3 arr)
                 HS.pure (TextShowOp_showTextIndGlyph _91)))))
 
pTextStateOp :: D.Parser TextStateOp
 
pTextStateOp =
  (RTS.<||)
    (RTS.pEnter "setCharSpacing"
       (do (_92 :: TextStateOp_0) <-
             do (charSpace :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tc"))
                HS.pure (TextStateOp_0 charSpace)
           HS.pure (TextStateOp_setCharSpacing _92)))
    ((RTS.<||)
       (RTS.pEnter "setWordSpacing"
          (do (_93 :: TextStateOp_1) <-
                do (x :: PdfValue.Number) <-
                     RTS.pEnter "PdfValue.Token"
                       (PdfValue.pToken @PdfValue.Number
                          (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                   RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tw"))
                   HS.pure (TextStateOp_1 x)
              HS.pure (TextStateOp_setWordSpacing _93)))
       ((RTS.<||)
          (RTS.pEnter "setHorizontalTextScaling"
             (do (_94 :: TextStateOp_2) <-
                   do (scale :: PdfValue.Number) <-
                        RTS.pEnter "PdfValue.Token"
                          (PdfValue.pToken @PdfValue.Number
                             (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                      RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tz"))
                      HS.pure (TextStateOp_2 scale)
                 HS.pure (TextStateOp_setHorizontalTextScaling _94)))
          ((RTS.<||)
             (RTS.pEnter "setTextLeading"
                (do (_95 :: TextStateOp_3) <-
                      do (leading :: PdfValue.Number) <-
                           RTS.pEnter "PdfValue.Token"
                             (PdfValue.pToken @PdfValue.Number
                                (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                         RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "TL"))
                         HS.pure (TextStateOp_3 leading)
                    HS.pure (TextStateOp_setTextLeading _95)))
             ((RTS.<||)
                (RTS.pEnter "setTextFont"
                   (do (_96 :: TextStateOp_4) <-
                         do (font :: Vector.Vector (RTS.UInt 8)) <-
                              RTS.pEnter "PdfValue.Token"
                                (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
                                   (RTS.pEnter "PdfValue.Name" PdfValue.pName))
                            (size :: PdfValue.Number) <-
                              RTS.pEnter "PdfValue.Token"
                                (PdfValue.pToken @PdfValue.Number
                                   (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                            RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tf"))
                            HS.pure (TextStateOp_4 font size)
                       HS.pure (TextStateOp_setTextFont _96)))
                ((RTS.<||)
                   (RTS.pEnter "setTextRendering"
                      (do (_97 :: TextStateOp_5) <-
                            do (render :: HS.Integer) <-
                                 RTS.pEnter "PdfValue.Token"
                                   (PdfValue.pToken @HS.Integer
                                      (RTS.pEnter "PdfValue.Natural" PdfValue.pNatural))
                               RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tr"))
                               HS.pure (TextStateOp_5 render)
                          HS.pure (TextStateOp_setTextRendering _97)))
                   (RTS.pEnter "setTextRise"
                      (do (_98 :: TextStateOp_6) <-
                            do (rise :: PdfValue.Number) <-
                                 RTS.pEnter "PdfValue.Token"
                                   (PdfValue.pToken @PdfValue.Number
                                      (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                               RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Ts"))
                               HS.pure (TextStateOp_6 rise)
                          HS.pure (TextStateOp_setTextRise _98))))))))
 
pXObj :: D.Parser XObj
 
pXObj =
  do (name :: Vector.Vector (RTS.UInt 8)) <-
       RTS.pEnter "PdfValue.Token"
         (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
            (RTS.pEnter "PdfValue.Name" PdfValue.pName))
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Do"))
     HS.pure (XObj name)
 
pPossibleOp :: D.Parser PossibleOp
 
pPossibleOp =
  do (operands :: Vector.Vector DirectObj) <-
       RTS.pMany (RTS.<||)
         (RTS.pEnter "PdfValue.Token"
            (PdfValue.pToken @DirectObj
               (RTS.pEnter "PdfContentStream.DirectObj" pDirectObj)))
     (op :: Vector.Vector (RTS.UInt 8)) <-
       RTS.pEnter "PdfValue.Token"
         (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
            (RTS.pMany (RTS.<||)
               (RTS.pEnter "PdfValue.NameChar" PdfValue.pNameChar)))
     HS.pure (PossibleOp operands op)
 
pCompatOps :: D.Parser PossibleOp -> D.Parser CompatOps
 
pCompatOps (pFutureOp :: D.Parser PossibleOp) =
  (RTS.<||)
    (RTS.pEnter "compatSection"
       (do (_99 :: Vector.Vector PageDescription_0) <-
             do RTS.pEnter "PdfValue._KW"
                  (PdfValue._KW (Vector.vecFromRep "BX"))
                (__ :: Vector.Vector PageDescription_0) <-
                  RTS.pEnter "PdfContentStream.PageDescription"
                    (pPageDescription
                       (RTS.pEnter "PdfContentStream.PossibleOp" pPossibleOp))
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "EX"))
                HS.pure __
           HS.pure (CompatOps_compatSection _99)))
    (RTS.pEnter "futureOp"
       (do (_100 :: PossibleOp) <- pFutureOp
           HS.pure (CompatOps_futureOp _100)))
 
pTextObj :: D.Parser PossibleOp -> D.Parser TextObj
 
pTextObj (pFutureOp :: D.Parser PossibleOp) =
  do RTS.pEnter "PdfValue._KW"
       (PdfValue._KW (Vector.vecFromRep "BT"))
     (ops :: Vector.Vector TextObj_0) <-
       RTS.pMany (RTS.<||)
         ((RTS.<||)
            (RTS.pEnter "graphicsStateOp"
               (do (_101 :: GenGraphicsStateOp) <-
                     RTS.pEnter "PdfContentStream.GenGraphicsStateOp"
                       pGenGraphicsStateOp
                   HS.pure (TextObj_0_graphicsStateOp _101)))
            ((RTS.<||)
               (RTS.pEnter "color"
                  (do (_102 :: ColourOp) <-
                        RTS.pEnter "PdfContentStream.ColourOp" pColourOp
                      HS.pure (TextObj_0_color _102)))
               ((RTS.<||)
                  (RTS.pEnter "textState"
                     (do (_103 :: TextStateOp) <-
                           RTS.pEnter "PdfContentStream.TextStateOp" pTextStateOp
                         HS.pure (TextObj_0_textState _103)))
                  ((RTS.<||)
                     (RTS.pEnter "textPos"
                        (do (_104 :: TextPosOp) <-
                              RTS.pEnter "PdfContentStream.TextPosOp" pTextPosOp
                            HS.pure (TextObj_0_textPos _104)))
                     ((RTS.<||)
                        (RTS.pEnter "textShow"
                           (do (_105 :: TextShowOp) <-
                                 RTS.pEnter "PdfContentStream.TextShowOp" pTextShowOp
                               HS.pure (TextObj_0_textShow _105)))
                        (RTS.pEnter "marked"
                           (do (_106 :: MarkedContentSeq) <-
                                 RTS.pEnter "PdfContentStream.MarkedContentSeq"
                                   (pMarkedContentSeq pFutureOp)
                               HS.pure (TextObj_0_marked _106))))))))
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "ET"))
     HS.pure (TextObj ops)
 
pSpecialGraphicsStateSeq ::
      D.Parser PossibleOp -> D.Parser SpecialGraphicsStateSeq
 
pSpecialGraphicsStateSeq (pFutureOps :: D.Parser PossibleOp) =
  (RTS.<||)
    (RTS.pEnter "nesting"
       (do (_107 :: SpecialGraphicsStateSeq_0) <-
             do RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "q"))
                (page :: Vector.Vector PageDescription_0) <-
                  RTS.pEnter "PdfContentStream.PageDescription"
                    (pPageDescription pFutureOps)
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Q"))
                HS.pure (SpecialGraphicsStateSeq_0 page)
           HS.pure (SpecialGraphicsStateSeq_nesting _107)))
    (RTS.pEnter "concatMatrix"
       (do (_108 :: SpecialGraphicsStateSeq_1) <-
             do (a :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                (b :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                (c :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                (d :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                (e :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                (f :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "cm"))
                HS.pure (SpecialGraphicsStateSeq_1 a b c d e f)
           HS.pure (SpecialGraphicsStateSeq_concatMatrix _108)))
 
pMarkedContentSeq ::
      D.Parser PossibleOp -> D.Parser MarkedContentSeq
 
pMarkedContentSeq (pFutureOp :: D.Parser PossibleOp) =
  do (beginMarked :: MarkedContentSeq_1) <-
       (RTS.<||)
         (RTS.pEnter "beginMarkedContent"
            (do (_109 :: ()) <-
                  RTS.pEnter "PdfValue.KW" (PdfValue.pKW (Vector.vecFromRep "BMC"))
                HS.pure (MarkedContentSeq_1_beginMarkedContent _109)))
         (RTS.pEnter "beginMarkedContentProp"
            (do (_110 :: MarkedContentSeq_0) <-
                  do (tag :: Vector.Vector (RTS.UInt 8)) <-
                       RTS.pEnter "PdfValue.Token"
                         (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
                            (RTS.pEnter "PdfValue.Name" PdfValue.pName))
                     (props :: ContentProps) <-
                       RTS.pEnter "PdfValue.Token"
                         (PdfValue.pToken @ContentProps
                            (RTS.pEnter "PdfContentStream.ContentProps" pContentProps))
                     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "BDC"))
                     HS.pure (MarkedContentSeq_0 tag props)
                HS.pure (MarkedContentSeq_1_beginMarkedContentProp _110)))
     (page :: Vector.Vector PageDescription_0) <-
       RTS.pEnter "PdfContentStream.PageDescription"
         (pPageDescription pFutureOp)
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "EMC"))
     HS.pure (MarkedContentSeq beginMarked page)
 
pPageDescription ::
      D.Parser PossibleOp -> D.Parser (Vector.Vector PageDescription_0)
 
pPageDescription (pFutureOp :: D.Parser PossibleOp) =
  RTS.pMany (RTS.<||)
    ((RTS.<||)
       (RTS.pEnter "genGraphics"
          (do (_111 :: GenGraphicsStateOp) <-
                RTS.pEnter "PdfContentStream.GenGraphicsStateOp"
                  pGenGraphicsStateOp
              HS.pure (PageDescription_0_genGraphics _111)))
       ((RTS.<||)
          (RTS.pEnter "specialGraphics"
             (do (_112 :: SpecialGraphicsStateSeq) <-
                   RTS.pEnter "PdfContentStream.SpecialGraphicsStateSeq"
                     (pSpecialGraphicsStateSeq pFutureOp)
                 HS.pure (PageDescription_0_specialGraphics _112)))
          ((RTS.<||)
             (RTS.pEnter "colour"
                (do (_113 :: ColourOp) <-
                      RTS.pEnter "PdfContentStream.ColourOp" pColourOp
                    HS.pure (PageDescription_0_colour _113)))
             ((RTS.<||)
                (RTS.pEnter "textState"
                   (do (_114 :: TextStateOp) <-
                         RTS.pEnter "PdfContentStream.TextStateOp" pTextStateOp
                       HS.pure (PageDescription_0_textState _114)))
                ((RTS.<||)
                   (RTS.pEnter "markedContent"
                      (do (_115 :: MarkedContentSeq) <-
                            RTS.pEnter "PdfContentStream.MarkedContentSeq"
                              (pMarkedContentSeq pFutureOp)
                          HS.pure (PageDescription_0_markedContent _115)))
                   ((RTS.<||)
                      (RTS.pEnter "textObj"
                         (do (_116 :: TextObj) <-
                               RTS.pEnter "PdfContentStream.TextObj" (pTextObj pFutureOp)
                             HS.pure (PageDescription_0_textObj _116)))
                      ((RTS.<||)
                         (RTS.pEnter "shadingObj"
                            (do (_117 :: ShadingObj) <-
                                  RTS.pEnter "PdfContentStream.ShadingObj" pShadingObj
                                HS.pure (PageDescription_0_shadingObj _117)))
                         ((RTS.<||)
                            (RTS.pEnter "xObj"
                               (do (_118 :: XObj) <- RTS.pEnter "PdfContentStream.XObj" pXObj
                                   HS.pure (PageDescription_0_xObj _118)))
                            ((RTS.<||)
                               (RTS.pEnter "inlineObj"
                                  (do (_119 :: InlineImageObj) <-
                                        RTS.pEnter "PdfContentStream.InlineImageObj" pInlineImageObj
                                      HS.pure (PageDescription_0_inlineObj _119)))
                               ((RTS.<||)
                                  (RTS.pEnter "pathObj"
                                     (do (_120 :: PathObj) <-
                                           RTS.pEnter "PdfContentStream.PathObj" pPathObj
                                         HS.pure (PageDescription_0_pathObj _120)))
                                  (RTS.pEnter "compat"
                                     (do (_121 :: CompatOps) <-
                                           RTS.pEnter "PdfContentStream.CompatOps"
                                             (pCompatOps pFutureOp)
                                         HS.pure (PageDescription_0_compat _121)))))))))))))
 
pContentStream :: D.Parser (Vector.Vector PageDescription_0)
 
pContentStream =
  do RTS.pSkipMany (RTS.<||)
       (RTS.pEnter "PdfValue._AnyWS" PdfValue._AnyWS)
     (__ :: Vector.Vector PageDescription_0) <-
       RTS.pEnter "PdfContentStream.PageDescription"
         (pPageDescription
            (RTS.pEnter "PdfContentStream.Bot"
               (pBot @PossibleOp
                  (RTS.pEnter "PdfContentStream.PossibleOp" pPossibleOp))))
     HS.pure __
 
pDefault2 :: forall a. RTS.DDL a => a -> (D.Parser a -> D.Parser a)
 
pDefault2 (x :: a) (pP :: D.Parser a) = (RTS.<||) pP (HS.pure x)
 
pDirectArray :: D.Parser (Vector.Vector DirectObj)
 
pDirectArray =
  RTS.pEnter "PdfContentStream.GenArray"
    (pGenArray @DirectObj
       (RTS.pEnter "PdfContentStream.DirectObj" pDirectObj))
 
pDirectDict ::
      D.Parser (Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj)
 
pDirectDict =
  RTS.pEnter "PdfContentStream.GenDict"
    (pGenDict @DirectObj
       (RTS.pEnter "PdfContentStream.DirectObj" pDirectObj))
 
pFontOp :: D.Parser FontOp
 
pFontOp =
  (RTS.<||)
    (RTS.pEnter "setGlyphWidth"
       (do (_122 :: FontOp_0) <-
             do (wx :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                RTS.pEnter "PdfValue._Token"
                  (PdfValue._Token @(RTS.UInt 8)
                     (HS.const ()
                        HS.<$> RTS.pMatch1 "322:12--322:21" (RTS.bcSingle (RTS.uint8 48))))
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "d0"))
                HS.pure (FontOp_0 wx)
           HS.pure (FontOp_setGlyphWidth _122)))
    (RTS.pEnter "setGlpyhWidthBoundingBox"
       (do (_123 :: FontOp_1) <-
             do (wx :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                RTS.pEnter "PdfValue._Token"
                  (PdfValue._Token @(RTS.UInt 8)
                     (HS.const ()
                        HS.<$> RTS.pMatch1 "327:12--327:21" (RTS.bcSingle (RTS.uint8 48))))
                (llx :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                (lly :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                (urx :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                (ury :: PdfValue.Number) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @PdfValue.Number
                       (RTS.pEnter "PdfValue.Number" PdfValue.pNumber))
                RTS.pEnter "PdfValue._Token"
                  (PdfValue._Token @(RTS.UInt 8)
                     (HS.const ()
                        HS.<$> RTS.pMatch1 "332:12--332:21" (RTS.bcSingle (RTS.uint8 48))))
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "d1"))
                HS.pure (FontOp_1 wx llx lly urx ury)
           HS.pure (FontOp_setGlpyhWidthBoundingBox _123)))
 
pMarkedContentOp :: D.Parser MarkedContentOp
 
pMarkedContentOp =
  (RTS.<||)
    (RTS.pEnter "defineMarkedContent"
       (do (_124 :: MarkedContentOp_0) <-
             do (tag :: Vector.Vector (RTS.UInt 8)) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
                       (RTS.pEnter "PdfValue.Name" PdfValue.pName))
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "MP"))
                HS.pure (MarkedContentOp_0 tag)
           HS.pure (MarkedContentOp_defineMarkedContent _124)))
    (RTS.pEnter "defMarkedContentPoint"
       (do (_125 :: MarkedContentOp_1) <-
             do (tag :: Vector.Vector (RTS.UInt 8)) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
                       (RTS.pEnter "PdfValue.Name" PdfValue.pName))
                (props :: ContentProps) <-
                  RTS.pEnter "PdfValue.Token"
                    (PdfValue.pToken @ContentProps
                       (RTS.pEnter "PdfContentStream.ContentProps" pContentProps))
                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "DP"))
                HS.pure (MarkedContentOp_1 tag props)
           HS.pure (MarkedContentOp_defMarkedContentPoint _125)))
 
_Bot :: forall b. RTS.DDL b => D.Parser () -> D.Parser ()
 
_Bot (_P :: D.Parser ()) =
  do RTS.pEnter "PdfValue._Guard" (PdfValue._Guard HS.False)
     _P
 
_BoundedNonNeg ::
  forall a.
    (RTS.DDL a, RTS.HasStruct a "num" HS.Integer,
     RTS.HasStruct a "exp" HS.Integer) =>
      a -> D.Parser ()
 
_BoundedNonNeg (ub :: a) =
  do (__ :: PdfValue.Number) <-
       RTS.pEnter "PdfValue.UnsignedNumber" PdfValue.pUnsignedNumber
     RTS.pEnter "PdfContentStream._Cmp"
       (_Cmp @PdfValue.Number @a @HS.Integer @HS.Integer __ ub)
 
_Byte :: D.Parser ()
 
_Byte =
  HS.const ()
    HS.<$> RTS.pMatch1 "6:12--6:19"
             (RTS.bcRange (RTS.lit 0 :: RTS.UInt 8) (RTS.lit 255 :: RTS.UInt 8))
 
_ClippingPathOp :: D.Parser ()
 
_ClippingPathOp =
  (RTS.<||)
    (RTS.pEnter "setClippingEvenOdd"
       (RTS.pEnter "PdfValue._KW"
          (PdfValue._KW (Vector.vecFromRep "W*"))))
    (RTS.pEnter "setClippingNzWinding"
       (RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "W"))))
 
_ColorSpace :: D.Parser ()
 
_ColorSpace =
  (RTS.<||) (RTS.pEnter "calRGB" (HS.pure ()))
    ((RTS.<||) (RTS.pEnter "calGray" (HS.pure ()))
       ((RTS.<||) (RTS.pEnter "lab" (HS.pure ()))
          ((RTS.<||) (RTS.pEnter "iccBased" (HS.pure ()))
             ((RTS.<||) (RTS.pEnter "deviceRGB" (HS.pure ()))
                ((RTS.<||) (RTS.pEnter "deviceCMYK" (HS.pure ()))
                   ((RTS.<||) (RTS.pEnter "deviceGray" (HS.pure ()))
                      ((RTS.<||) (RTS.pEnter "sep" (HS.pure ()))
                         ((RTS.<||) (RTS.pEnter "devN" (HS.pure ()))
                            ((RTS.<||) (RTS.pEnter "indexed" (HS.pure ()))
                               (RTS.pEnter "pattern" (HS.pure ())))))))))))
 
_Fractional :: D.Parser ()
 
_Fractional =
  do (__ :: PdfValue.Number) <-
       RTS.pEnter "PdfValue.Number" PdfValue.pNumber
     do (_13 :: Fractional_0) <-
          do (num :: HS.Integer) <- HS.pure (RTS.lit 0 :: HS.Integer)
             (exp :: HS.Integer) <- HS.pure (RTS.lit 0 :: HS.Integer)
             HS.pure (Fractional_0 num exp)
        RTS.pEnter "PdfContentStream._Cmp"
          (_Cmp @Fractional_0 @PdfValue.Number @HS.Integer @HS.Integer _13
             __)
     (_14 :: Fractional_1) <-
       do (num :: HS.Integer) <- HS.pure (RTS.lit 1 :: HS.Integer)
          (exp :: HS.Integer) <- HS.pure (RTS.lit 0 :: HS.Integer)
          HS.pure (Fractional_1 num exp)
     RTS.pEnter "PdfContentStream._Cmp"
       (_Cmp @PdfValue.Number @Fractional_1 @HS.Integer @HS.Integer __
          _14)
 
_ColourOp :: D.Parser ()
 
_ColourOp =
  (RTS.<||)
    (RTS.pEnter "setColorSpaceStroking"
       (do RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @(Vector.Vector (RTS.UInt 8))
                (RTS.pEnter "PdfValue._Name" PdfValue._Name))
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "CS"))))
    ((RTS.<||)
       (RTS.pEnter "setColorSpaceNonStroking"
          (do RTS.pEnter "PdfValue._Token"
                (PdfValue._Token @(Vector.Vector (RTS.UInt 8))
                   (RTS.pEnter "PdfValue._Name" PdfValue._Name))
              RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "cs"))))
       ((RTS.<||)
          (RTS.pEnter "setColorStroking"
             (do RTS.pSkipMany (RTS.<||)
                   (RTS.pEnter "PdfValue._Token"
                      (PdfValue._Token @PdfValue.Number
                         (RTS.pEnter "PdfValue._Number" PdfValue._Number)))
                 RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "SC"))))
          ((RTS.<||)
             (RTS.pEnter "setColorStrokingICC"
                (do RTS.pSkipMany (RTS.<||)
                      (RTS.pEnter "PdfValue._Token"
                         (PdfValue._Token @PdfValue.Number
                            (RTS.pEnter "PdfValue._Number" PdfValue._Number)))
                    RTS.pEnter "PdfValue._KW"
                      (PdfValue._KW (Vector.vecFromRep "SCN"))))
             ((RTS.<||)
                (RTS.pEnter "setColorNonStroking"
                   (do RTS.pSkipMany (RTS.<||)
                         (RTS.pEnter "PdfValue._Token"
                            (PdfValue._Token @PdfValue.Number
                               (RTS.pEnter "PdfValue._Number" PdfValue._Number)))
                       RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "sc"))))
                ((RTS.<||)
                   (RTS.pEnter "setColorNonStrokingICC"
                      (do RTS.pSkipMany (RTS.<||)
                            (RTS.pEnter "PdfValue._Token"
                               (PdfValue._Token @PdfValue.Number
                                  (RTS.pEnter "PdfValue._Number" PdfValue._Number)))
                          RTS.pEnter "PdfValue._KW"
                            (PdfValue._KW (Vector.vecFromRep "scn"))))
                   ((RTS.<||)
                      (RTS.pEnter "setGrayStroking"
                         (do RTS.pEnter "PdfValue._Token"
                               (PdfValue._Token @PdfValue.Number
                                  (RTS.pEnter "PdfContentStream._Fractional" _Fractional))
                             RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "G"))))
                      ((RTS.<||)
                         (RTS.pEnter "setGrayNonStroking"
                            (do RTS.pEnter "PdfValue._Token"
                                  (PdfValue._Token @PdfValue.Number
                                     (RTS.pEnter "PdfContentStream._Fractional" _Fractional))
                                RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "g"))))
                         ((RTS.<||)
                            (RTS.pEnter "setRGBStroking"
                               (do RTS.pEnter "PdfValue._Token"
                                     (PdfValue._Token @PdfValue.Number
                                        (RTS.pEnter "PdfContentStream._Fractional" _Fractional))
                                   RTS.pEnter "PdfValue._Token"
                                     (PdfValue._Token @PdfValue.Number
                                        (RTS.pEnter "PdfContentStream._Fractional" _Fractional))
                                   RTS.pEnter "PdfValue._Token"
                                     (PdfValue._Token @PdfValue.Number
                                        (RTS.pEnter "PdfContentStream._Fractional" _Fractional))
                                   RTS.pEnter "PdfValue._KW"
                                     (PdfValue._KW (Vector.vecFromRep "RG"))))
                            ((RTS.<||)
                               (RTS.pEnter "setRGBNonStroking"
                                  (do RTS.pEnter "PdfValue._Token"
                                        (PdfValue._Token @PdfValue.Number
                                           (RTS.pEnter "PdfContentStream._Fractional" _Fractional))
                                      RTS.pEnter "PdfValue._Token"
                                        (PdfValue._Token @PdfValue.Number
                                           (RTS.pEnter "PdfContentStream._Fractional" _Fractional))
                                      RTS.pEnter "PdfValue._Token"
                                        (PdfValue._Token @PdfValue.Number
                                           (RTS.pEnter "PdfContentStream._Fractional" _Fractional))
                                      RTS.pEnter "PdfValue._KW"
                                        (PdfValue._KW (Vector.vecFromRep "rg"))))
                               ((RTS.<||)
                                  (RTS.pEnter "setCMYKStroking"
                                     (do RTS.pEnter "PdfValue._Token"
                                           (PdfValue._Token @PdfValue.Number
                                              (RTS.pEnter "PdfContentStream._Fractional"
                                                 _Fractional))
                                         RTS.pEnter "PdfValue._Token"
                                           (PdfValue._Token @PdfValue.Number
                                              (RTS.pEnter "PdfContentStream._Fractional"
                                                 _Fractional))
                                         RTS.pEnter "PdfValue._Token"
                                           (PdfValue._Token @PdfValue.Number
                                              (RTS.pEnter "PdfContentStream._Fractional"
                                                 _Fractional))
                                         RTS.pEnter "PdfValue._Token"
                                           (PdfValue._Token @PdfValue.Number
                                              (RTS.pEnter "PdfContentStream._Fractional"
                                                 _Fractional))
                                         RTS.pEnter "PdfValue._KW"
                                           (PdfValue._KW (Vector.vecFromRep "K"))))
                                  (RTS.pEnter "setCMYKNonStroking"
                                     (do RTS.pEnter "PdfValue._Token"
                                           (PdfValue._Token @PdfValue.Number
                                              (RTS.pEnter "PdfContentStream._Fractional"
                                                 _Fractional))
                                         RTS.pEnter "PdfValue._Token"
                                           (PdfValue._Token @PdfValue.Number
                                              (RTS.pEnter "PdfContentStream._Fractional"
                                                 _Fractional))
                                         RTS.pEnter "PdfValue._Token"
                                           (PdfValue._Token @PdfValue.Number
                                              (RTS.pEnter "PdfContentStream._Fractional"
                                                 _Fractional))
                                         RTS.pEnter "PdfValue._Token"
                                           (PdfValue._Token @PdfValue.Number
                                              (RTS.pEnter "PdfContentStream._Fractional"
                                                 _Fractional))
                                         RTS.pEnter "PdfValue._KW"
                                           (PdfValue._KW (Vector.vecFromRep "K"))))))))))))))
 
_CompatOps :: D.Parser () -> D.Parser ()
 
_CompatOps (_FutureOp :: D.Parser ()) =
  (RTS.<||)
    (RTS.pEnter "compatSection"
       (do RTS.pEnter "PdfValue._KW"
             (PdfValue._KW (Vector.vecFromRep "BX"))
           do HS.void
                (RTS.pEnter "PdfContentStream.PageDescription"
                   (pPageDescription
                      (RTS.pEnter "PdfContentStream.PossibleOp" pPossibleOp)))
              HS.pure ()
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "EX"))))
    (RTS.pEnter "futureOp" _FutureOp)
 
_ContentPoint :: D.Parser ()
 
_ContentPoint =
  do RTS.pEnter "PdfValue._Token"
       (PdfValue._Token @PdfValue.Number
          (RTS.pEnter "PdfValue._Number" PdfValue._Number))
     RTS.pEnter "PdfValue._Token"
       (PdfValue._Token @PdfValue.Number
          (RTS.pEnter "PdfValue._Number" PdfValue._Number))
 
_ContentProps :: D.Parser ()
 
_ContentProps =
  (RTS.|||)
    (RTS.pEnter "inline" (RTS.pEnter "PdfValue._Dict" PdfValue._Dict))
    (RTS.pEnter "nm" (RTS.pEnter "PdfValue._Name" PdfValue._Name))
 
_Intent :: D.Parser ()
 
_Intent =
  (RTS.<||) (RTS.pEnter "absoluteColorimetric" (HS.pure ()))
    ((RTS.<||) (RTS.pEnter "relativeColorimetric" (HS.pure ()))
       ((RTS.<||) (RTS.pEnter "saturation" (HS.pure ()))
          (RTS.pEnter "perceptual" (HS.pure ()))))
 
_LineStyle :: D.Parser ()
 
_LineStyle =
  HS.const ()
    HS.<$> RTS.pMatch1 "81:17--81:34"
             (RTS.bcRange (RTS.uint8 48) (RTS.uint8 50))
 
_GenGraphicsStateOp :: D.Parser ()
 
_GenGraphicsStateOp =
  (RTS.<||)
    (RTS.pEnter "setLineWidth"
       (do RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "w"))))
    ((RTS.<||)
       (RTS.pEnter "setLineCapStyle"
          (do RTS.pEnter "PdfValue._Token"
                (PdfValue._Token @(RTS.UInt 8)
                   (RTS.pEnter "PdfContentStream._LineStyle" _LineStyle))
              RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "J"))))
       ((RTS.<||)
          (RTS.pEnter "setLineJoinStyle"
             (do RTS.pEnter "PdfValue._Token"
                   (PdfValue._Token @(RTS.UInt 8)
                      (RTS.pEnter "PdfContentStream._LineStyle" _LineStyle))
                 RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "j"))))
          ((RTS.<||)
             (RTS.pEnter "setMiterLimit"
                (do RTS.pEnter "PdfValue._Token"
                      (PdfValue._Token @PdfValue.Number
                         (RTS.pEnter "PdfValue._Number" PdfValue._Number))
                    RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "M"))))
             ((RTS.<||)
                (RTS.pEnter "setLineDash"
                   (do RTS.pEnter "PdfValue._Token"
                         (PdfValue._Token @(Vector.Vector HS.Integer)
                            (RTS.pEnter "PdfContentStream._GenArray"
                               (_GenArray @HS.Integer
                                  (RTS.pEnter "PdfValue._Token"
                                     (PdfValue._Token @HS.Integer
                                        (RTS.pEnter "PdfValue._Natural" PdfValue._Natural))))))
                       RTS.pEnter "PdfValue._Token"
                         (PdfValue._Token @PdfValue.Number
                            (RTS.pEnter "PdfValue._Number" PdfValue._Number))
                       RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "d"))))
                ((RTS.<||)
                   (RTS.pEnter "setColorRenderingIntent"
                      (do RTS.pEnter "PdfValue._Token"
                            (PdfValue._Token @Intent
                               (RTS.pEnter "PdfContentStream._Intent" _Intent))
                          RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "ri"))))
                   ((RTS.<||)
                      (RTS.pEnter "setFlat"
                         (do RTS.pEnter "PdfValue._Token"
                               (PdfValue._Token @PdfValue.Number
                                  (do (_37 :: GenGraphicsStateOp_6) <-
                                        do (num :: HS.Integer) <-
                                             HS.pure (RTS.lit 100 :: HS.Integer)
                                           (exp :: HS.Integer) <- HS.pure (RTS.lit 0 :: HS.Integer)
                                           HS.pure (GenGraphicsStateOp_6 num exp)
                                      RTS.pEnter "PdfContentStream._BoundedNonNeg"
                                        (_BoundedNonNeg @GenGraphicsStateOp_6 _37)))
                             RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "i"))))
                      (RTS.pEnter "setGraphicsStateParams"
                         (do RTS.pEnter "PdfValue._Token"
                               (PdfValue._Token @(Vector.Vector (RTS.UInt 8))
                                  (RTS.pEnter "PdfValue._Name" PdfValue._Name))
                             RTS.pEnter "PdfValue._KW"
                               (PdfValue._KW (Vector.vecFromRep "gs"))))))))))
 
_InlineImageObj :: D.Parser ()
 
_InlineImageObj =
  do RTS.pEnter "PdfValue._KW"
       (PdfValue._KW (Vector.vecFromRep "BI"))
     (hdrEnts :: Vector.Vector InlineImageObj_5) <-
       RTS.pMany (RTS.<||)
         (do (key :: Vector.Vector (RTS.UInt 8)) <-
               RTS.pEnter "PdfValue.Token"
                 (PdfValue.pToken @(Vector.Vector (RTS.UInt 8))
                    (RTS.pEnter "PdfValue.Name" PdfValue.pName))
             (RTS.<||)
               (RTS.pEnter "bpc"
                  (do RTS.pEnter "PdfValue._Guard"
                        (PdfValue._Guard
                           ((key HS.== Vector.vecFromRep "BitsPerComponent")
                              HS.|| (key HS.== Vector.vecFromRep "BPC")))
                      RTS.pEnter "PdfValue._Natural" PdfValue._Natural))
               ((RTS.<||)
                  (RTS.pEnter "colorSpace"
                     (do RTS.pEnter "PdfValue._Guard"
                           (PdfValue._Guard
                              ((key HS.== Vector.vecFromRep "ColorSpace")
                                 HS.|| (key HS.== Vector.vecFromRep "CS")))
                         (RTS.<||)
                           (RTS.pEnter "nm" (RTS.pEnter "PdfValue._Name" PdfValue._Name))
                           (RTS.pEnter "arr"
                              (RTS.pEnter "PdfContentStream._DirectArray" _DirectArray))))
                  ((RTS.<||)
                     (RTS.pEnter "decode"
                        (do RTS.pEnter "PdfValue._Guard"
                              (PdfValue._Guard
                                 ((key HS.== Vector.vecFromRep "Decode")
                                    HS.|| (key HS.== Vector.vecFromRep "D")))
                            RTS.pEnter "PdfContentStream._GenArray"
                              (_GenArray @PdfValue.Number
                                 (RTS.pEnter "PdfValue._Number" PdfValue._Number))))
                     ((RTS.<||)
                        (RTS.pEnter "decodeParams"
                           (do RTS.pEnter "PdfValue._Guard"
                                 (PdfValue._Guard
                                    ((key HS.== Vector.vecFromRep "DecodeParms")
                                       HS.|| (key HS.== Vector.vecFromRep "DP")))
                               (RTS.<||)
                                 (RTS.pEnter "d"
                                    (RTS.pEnter "PdfContentStream._DirectDict" _DirectDict))
                                 (RTS.pEnter "arr"
                                    (RTS.pEnter "PdfContentStream._GenArray"
                                       (_GenArray @(Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj)
                                          (RTS.pEnter "PdfContentStream._DirectDict"
                                             _DirectDict))))))
                        ((RTS.<||)
                           (RTS.pEnter "filter"
                              (do RTS.pEnter "PdfValue._Guard"
                                    (PdfValue._Guard
                                       ((key HS.== Vector.vecFromRep "Filter")
                                          HS.|| (key HS.== Vector.vecFromRep "F")))
                                  (RTS.<||)
                                    (RTS.pEnter "name" (RTS.pEnter "PdfValue._Name" PdfValue._Name))
                                    (RTS.pEnter "names"
                                       (RTS.pEnter "PdfContentStream._GenArray"
                                          (_GenArray @(Vector.Vector (RTS.UInt 8))
                                             (RTS.pEnter "PdfValue._Name" PdfValue._Name))))))
                           ((RTS.<||)
                              (RTS.pEnter "height"
                                 (do RTS.pEnter "PdfValue._Guard"
                                       (PdfValue._Guard
                                          ((key HS.== Vector.vecFromRep "Height")
                                             HS.|| (key HS.== Vector.vecFromRep "H")))
                                     RTS.pEnter "PdfValue._Natural" PdfValue._Natural))
                              ((RTS.<||)
                                 (RTS.pEnter "imageMask"
                                    (do RTS.pEnter "PdfValue._Guard"
                                          (PdfValue._Guard
                                             ((key HS.== Vector.vecFromRep "ImageMask")
                                                HS.|| (key HS.== Vector.vecFromRep "IM")))
                                        RTS.pEnter "PdfValue._Bool" PdfValue._Bool))
                                 (RTS.pEnter "intent"
                                    (do RTS.pEnter "PdfValue._Guard"
                                          (PdfValue._Guard (key HS.== Vector.vecFromRep "Intent"))
                                        (RTS.<||) (RTS.pEnter "absColorimetric" (HS.pure ()))
                                          ((RTS.<||) (RTS.pEnter "relColorimetric" (HS.pure ()))
                                             ((RTS.<||) (RTS.pEnter "sat" (HS.pure ()))
                                                (RTS.pEnter "perceptual" (HS.pure ()))))))))))))
             (value :: DirectObj) <-
               RTS.pEnter "PdfValue.Token"
                 (PdfValue.pToken @DirectObj
                    (RTS.pEnter "PdfContentStream.DirectObj" pDirectObj))
             HS.pure (InlineImageObj_5 key value))
     (hdr :: Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj) <-
       RTS.loopFoldM
         (\(d :: Map.Map (Vector.Vector (RTS.UInt 8))
                   DirectObj) (e :: InlineImageObj_5) ->
            RTS.pIsJust "524:40--524:61" "Key already present"
              (Map.insertMaybe (HS.getField @"key" e) (HS.getField @"value" e)
                 d))
         (Map.empty :: Map.Map (Vector.Vector (RTS.UInt 8)) DirectObj)
         hdrEnts
     (len :: HS.Integer) <-
       (RTS.|||)
         (RTS.pEnter "PdfContentStream.LookupDirectNat"
            (pLookupDirectNat @(Vector.Vector (RTS.UInt 8))
               (Vector.vecFromRep "Length")
               hdr))
         (RTS.pEnter "PdfContentStream.LookupDirectNat"
            (pLookupDirectNat @(Vector.Vector (RTS.UInt 8))
               (Vector.vecFromRep "L")
               hdr))
     RTS.pEnter "PdfValue._Guard"
       (PdfValue._Guard (len HS.<= (RTS.lit 4096 :: HS.Integer)))
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "ID"))
     HS.const ()
       HS.<$> RTS.pMatch1 "533:13--533:21" PdfValue.cs_simpleWS
     RTS.pEnter "PdfContentStream._Default2"
       (_Default2 @(Vector.Vector (RTS.UInt 8))
          (do (filtersObj :: DirectObj) <-
                (RTS.|||)
                  (RTS.pIsJust "535:20--535:38"
                     ("Missing key: "
                        HS.++ HS.show
                                (Vector.vecFromRep "Filter" :: Vector.Vector (RTS.UInt 8)))
                     (Map.lookup (Vector.vecFromRep "Filter") hdr))
                  (RTS.pIsJust "535:44--535:57"
                     ("Missing key: "
                        HS.++ HS.show
                                (Vector.vecFromRep "F" :: Vector.Vector (RTS.UInt 8)))
                     (Map.lookup (Vector.vecFromRep "F") hdr))
              (filters :: Vector.Vector DirectObj) <-
                RTS.pIsJust "536:16--536:38" "Expected `array`"
                  (HS.getField @"array" (HS.getField @"box" filtersObj))
              (filterNames :: Vector.Vector (Vector.Vector (RTS.UInt 8))) <-
                RTS.loopMapM
                  (\(fobj :: DirectObj) ->
                     do (__ :: Vector.Vector (RTS.UInt 8)) <-
                          RTS.pIsJust "539:7--539:22" "Expected `name`"
                            (HS.getField @"name" (HS.getField @"box" fobj))
                        HS.pure __)
                  filters
                  :: D.Parser (Vector.Vector (Vector.Vector (RTS.UInt 8)))
              (lastFilter :: HS.Maybe (Vector.Vector (RTS.UInt 8))) <-
                RTS.pEnter "PdfContentStream.LastElt"
                  (pLastElt @(Vector.Vector (Vector.Vector (RTS.UInt 8))) @HS.Integer
                     @(Vector.Vector (RTS.UInt 8))
                     filterNames)
              (lastF :: Vector.Vector (RTS.UInt 8)) <-
                RTS.pIsJust "542:14--542:31" "Expected `Just`" lastFilter
              RTS.pEnter "PdfValue._Guard"
                (PdfValue._Guard
                   ((lastF HS.== Vector.vecFromRep "ASCIIHexDecode")
                      HS.|| (lastF HS.== Vector.vecFromRep "ASCII85Decode")))
              RTS.pSkipMany (RTS.<||)
                (RTS.pEnter "PdfValue._AnyWS" PdfValue._AnyWS)))
     RTS.pSkipExact len (RTS.pEnter "PdfContentStream._Byte" _Byte)
     RTS.pSkipMany (RTS.<||)
       (RTS.pEnter "PdfValue._AnyWS" PdfValue._AnyWS)
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "EI"))
 
_MarkedContentSeq :: D.Parser PossibleOp -> D.Parser ()
 
_MarkedContentSeq (pFutureOp :: D.Parser PossibleOp) =
  do (RTS.<||)
       (RTS.pEnter "beginMarkedContent"
          (RTS.pEnter "PdfValue._KW"
             (PdfValue._KW (Vector.vecFromRep "BMC"))))
       (RTS.pEnter "beginMarkedContentProp"
          (do RTS.pEnter "PdfValue._Token"
                (PdfValue._Token @(Vector.Vector (RTS.UInt 8))
                   (RTS.pEnter "PdfValue._Name" PdfValue._Name))
              RTS.pEnter "PdfValue._Token"
                (PdfValue._Token @ContentProps
                   (RTS.pEnter "PdfContentStream._ContentProps" _ContentProps))
              RTS.pEnter "PdfValue._KW"
                (PdfValue._KW (Vector.vecFromRep "BDC"))))
     do HS.void
          (RTS.pEnter "PdfContentStream.PageDescription"
             (pPageDescription pFutureOp))
        HS.pure ()
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "EMC"))
 
_PathBeginOp :: D.Parser ()
 
_PathBeginOp =
  (RTS.<||)
    (RTS.pEnter "beginNewSuppath"
       (do RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @ContentPoint
                (RTS.pEnter "PdfContentStream._ContentPoint" _ContentPoint))
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "m"))))
    (RTS.pEnter "appendRect"
       (do RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @ContentPoint
                (RTS.pEnter "PdfContentStream._ContentPoint" _ContentPoint))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "re"))))
 
_PathConsOp :: D.Parser ()
 
_PathConsOp =
  (RTS.<||)
    (RTS.pEnter "beginSubpath"
       (RTS.pEnter "PdfContentStream._PathBeginOp" _PathBeginOp))
    ((RTS.<||)
       (RTS.pEnter "appendLine"
          (do RTS.pEnter "PdfValue._Token"
                (PdfValue._Token @ContentPoint
                   (RTS.pEnter "PdfContentStream._ContentPoint" _ContentPoint))
              RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "l"))))
       ((RTS.<||)
          (RTS.pEnter "appendCurvedThreePoints"
             (do RTS.pEnter "PdfValue._Token"
                   (PdfValue._Token @ContentPoint
                      (RTS.pEnter "PdfContentStream._ContentPoint" _ContentPoint))
                 RTS.pEnter "PdfValue._Token"
                   (PdfValue._Token @ContentPoint
                      (RTS.pEnter "PdfContentStream._ContentPoint" _ContentPoint))
                 RTS.pEnter "PdfValue._Token"
                   (PdfValue._Token @ContentPoint
                      (RTS.pEnter "PdfContentStream._ContentPoint" _ContentPoint))
                 RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "c"))))
          ((RTS.<||)
             (RTS.pEnter "appendCurvedInitPtRepl"
                (do RTS.pEnter "PdfValue._Token"
                      (PdfValue._Token @ContentPoint
                         (RTS.pEnter "PdfContentStream._ContentPoint" _ContentPoint))
                    RTS.pEnter "PdfValue._Token"
                      (PdfValue._Token @ContentPoint
                         (RTS.pEnter "PdfContentStream._ContentPoint" _ContentPoint))
                    RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "v"))))
             ((RTS.<||)
                (RTS.pEnter "appendCurvedFinalPt"
                   (do RTS.pEnter "PdfValue._Token"
                         (PdfValue._Token @ContentPoint
                            (RTS.pEnter "PdfContentStream._ContentPoint" _ContentPoint))
                       RTS.pEnter "PdfValue._Token"
                         (PdfValue._Token @ContentPoint
                            (RTS.pEnter "PdfContentStream._ContentPoint" _ContentPoint))
                       RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "y"))))
                (RTS.pEnter "closeSubpath"
                   (RTS.pEnter "PdfValue._KW"
                      (PdfValue._KW (Vector.vecFromRep "h"))))))))
 
_PathPaintingOp :: D.Parser ()
 
_PathPaintingOp =
  (RTS.<||)
    (RTS.pEnter "stroke"
       (RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "S"))))
    ((RTS.<||)
       (RTS.pEnter "closeStrokePath"
          (RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "s"))))
       ((RTS.<||)
          (RTS.pEnter "fillPathNzWindingOld"
             (RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "F"))))
          ((RTS.<||)
             (RTS.pEnter "fillPathEvenOdd"
                (RTS.pEnter "PdfValue._KW"
                   (PdfValue._KW (Vector.vecFromRep "f*"))))
             ((RTS.<||)
                (RTS.pEnter "fillPathNzWinding"
                   (RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "f"))))
                ((RTS.<||)
                   (RTS.pEnter "fillStrokeEvenOdd"
                      (RTS.pEnter "PdfValue._KW"
                         (PdfValue._KW (Vector.vecFromRep "B*"))))
                   ((RTS.<||)
                      (RTS.pEnter "fillStroke"
                         (RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "B"))))
                      ((RTS.<||)
                         (RTS.pEnter "closeFillStrokeEvenOdd"
                            (RTS.pEnter "PdfValue._KW"
                               (PdfValue._KW (Vector.vecFromRep "b*"))))
                         ((RTS.<||)
                            (RTS.pEnter "closeFillStrokeNzWinding"
                               (RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "b"))))
                            (RTS.pEnter "endPath"
                               (RTS.pEnter "PdfValue._KW"
                                  (PdfValue._KW (Vector.vecFromRep "n"))))))))))))
 
_PathObj :: D.Parser ()
 
_PathObj =
  do RTS.pEnter "PdfContentStream._PathBeginOp" _PathBeginOp
     RTS.pSkipMany (RTS.<||)
       (RTS.pEnter "PdfContentStream._PathConsOp" _PathConsOp)
     (RTS.<||)
       (RTS.pEnter "PdfContentStream._ClippingPathOp" _ClippingPathOp)
       (HS.pure ())
     RTS.pEnter "PdfContentStream._PathPaintingOp" _PathPaintingOp
 
_ShadingObj :: D.Parser ()
 
_ShadingObj =
  do RTS.pEnter "PdfValue._Token"
       (PdfValue._Token @(Vector.Vector (RTS.UInt 8))
          (RTS.pEnter "PdfValue._Name" PdfValue._Name))
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "sh"))
 
_SpecialGraphicsStateSeq :: D.Parser PossibleOp -> D.Parser ()
 
_SpecialGraphicsStateSeq (pFutureOps :: D.Parser PossibleOp) =
  (RTS.<||)
    (RTS.pEnter "nesting"
       (do RTS.pEnter "PdfValue._KW"
             (PdfValue._KW (Vector.vecFromRep "q"))
           do HS.void
                (RTS.pEnter "PdfContentStream.PageDescription"
                   (pPageDescription pFutureOps))
              HS.pure ()
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Q"))))
    (RTS.pEnter "concatMatrix"
       (do RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "cm"))))
 
_TextPosOp :: D.Parser ()
 
_TextPosOp =
  do do RTS.pEnter "PdfValue._Token"
          (PdfValue._Token @PdfValue.Number
             (RTS.pEnter "PdfValue._Number" PdfValue._Number))
        RTS.pEnter "PdfValue._Token"
          (PdfValue._Token @PdfValue.Number
             (RTS.pEnter "PdfValue._Number" PdfValue._Number))
        RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Td"))
     do RTS.pEnter "PdfValue._Token"
          (PdfValue._Token @PdfValue.Number
             (RTS.pEnter "PdfValue._Number" PdfValue._Number))
        RTS.pEnter "PdfValue._Token"
          (PdfValue._Token @PdfValue.Number
             (RTS.pEnter "PdfValue._Number" PdfValue._Number))
        RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "TD"))
     do RTS.pEnter "PdfValue._Token"
          (PdfValue._Token @PdfValue.Number
             (RTS.pEnter "PdfValue._Number" PdfValue._Number))
        RTS.pEnter "PdfValue._Token"
          (PdfValue._Token @PdfValue.Number
             (RTS.pEnter "PdfValue._Number" PdfValue._Number))
        RTS.pEnter "PdfValue._Token"
          (PdfValue._Token @PdfValue.Number
             (RTS.pEnter "PdfValue._Number" PdfValue._Number))
        RTS.pEnter "PdfValue._Token"
          (PdfValue._Token @PdfValue.Number
             (RTS.pEnter "PdfValue._Number" PdfValue._Number))
        RTS.pEnter "PdfValue._Token"
          (PdfValue._Token @PdfValue.Number
             (RTS.pEnter "PdfValue._Number" PdfValue._Number))
        RTS.pEnter "PdfValue._Token"
          (PdfValue._Token @PdfValue.Number
             (RTS.pEnter "PdfValue._Number" PdfValue._Number))
        RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tm"))
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "T*"))
 
_ShowVal :: D.Parser ()
 
_ShowVal =
  (RTS.<||)
    (RTS.pEnter "str" (RTS.pEnter "PdfValue._String" PdfValue._String))
    (RTS.pEnter "num" (RTS.pEnter "PdfValue._Number" PdfValue._Number))
 
_TextShowOp :: D.Parser ()
 
_TextShowOp =
  (RTS.<||)
    (RTS.pEnter "showText"
       (do RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @(Vector.Vector (RTS.UInt 8))
                (RTS.pEnter "PdfValue._String" PdfValue._String))
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tj"))))
    ((RTS.<||)
       (RTS.pEnter "moveShow"
          (do RTS.pEnter "PdfValue._Token"
                (PdfValue._Token @(Vector.Vector (RTS.UInt 8))
                   (RTS.pEnter "PdfValue._String" PdfValue._String))
              RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "'"))))
       ((RTS.<||)
          (RTS.pEnter "setSpacing"
             (do RTS.pEnter "PdfValue._Token"
                   (PdfValue._Token @PdfValue.Number
                      (RTS.pEnter "PdfValue._Number" PdfValue._Number))
                 RTS.pEnter "PdfValue._Token"
                   (PdfValue._Token @PdfValue.Number
                      (RTS.pEnter "PdfValue._Number" PdfValue._Number))
                 RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "\""))))
          (RTS.pEnter "showTextIndGlyph"
             (do RTS.pEnter "PdfValue._Token"
                   (PdfValue._Token @(Vector.Vector ShowVal)
                      (RTS.pEnter "PdfContentStream._GenArray"
                         (_GenArray @ShowVal
                            (RTS.pEnter "PdfValue._Token"
                               (PdfValue._Token @ShowVal
                                  (RTS.pEnter "PdfContentStream._ShowVal" _ShowVal))))))
                 RTS.pEnter "PdfValue._KW"
                   (PdfValue._KW (Vector.vecFromRep "TJ"))))))
 
_TextStateOp :: D.Parser ()
 
_TextStateOp =
  (RTS.<||)
    (RTS.pEnter "setCharSpacing"
       (do RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tc"))))
    ((RTS.<||)
       (RTS.pEnter "setWordSpacing"
          (do RTS.pEnter "PdfValue._Token"
                (PdfValue._Token @PdfValue.Number
                   (RTS.pEnter "PdfValue._Number" PdfValue._Number))
              RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tw"))))
       ((RTS.<||)
          (RTS.pEnter "setHorizontalTextScaling"
             (do RTS.pEnter "PdfValue._Token"
                   (PdfValue._Token @PdfValue.Number
                      (RTS.pEnter "PdfValue._Number" PdfValue._Number))
                 RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tz"))))
          ((RTS.<||)
             (RTS.pEnter "setTextLeading"
                (do RTS.pEnter "PdfValue._Token"
                      (PdfValue._Token @PdfValue.Number
                         (RTS.pEnter "PdfValue._Number" PdfValue._Number))
                    RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "TL"))))
             ((RTS.<||)
                (RTS.pEnter "setTextFont"
                   (do RTS.pEnter "PdfValue._Token"
                         (PdfValue._Token @(Vector.Vector (RTS.UInt 8))
                            (RTS.pEnter "PdfValue._Name" PdfValue._Name))
                       RTS.pEnter "PdfValue._Token"
                         (PdfValue._Token @PdfValue.Number
                            (RTS.pEnter "PdfValue._Number" PdfValue._Number))
                       RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tf"))))
                ((RTS.<||)
                   (RTS.pEnter "setTextRendering"
                      (do RTS.pEnter "PdfValue._Token"
                            (PdfValue._Token @HS.Integer
                               (RTS.pEnter "PdfValue._Natural" PdfValue._Natural))
                          RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Tr"))))
                   (RTS.pEnter "setTextRise"
                      (do RTS.pEnter "PdfValue._Token"
                            (PdfValue._Token @PdfValue.Number
                               (RTS.pEnter "PdfValue._Number" PdfValue._Number))
                          RTS.pEnter "PdfValue._KW"
                            (PdfValue._KW (Vector.vecFromRep "Ts")))))))))
 
_TextObj :: D.Parser PossibleOp -> D.Parser ()
 
_TextObj (pFutureOp :: D.Parser PossibleOp) =
  do RTS.pEnter "PdfValue._KW"
       (PdfValue._KW (Vector.vecFromRep "BT"))
     RTS.pSkipMany (RTS.<||)
       ((RTS.<||)
          (RTS.pEnter "graphicsStateOp"
             (RTS.pEnter "PdfContentStream._GenGraphicsStateOp"
                _GenGraphicsStateOp))
          ((RTS.<||)
             (RTS.pEnter "color"
                (RTS.pEnter "PdfContentStream._ColourOp" _ColourOp))
             ((RTS.<||)
                (RTS.pEnter "textState"
                   (RTS.pEnter "PdfContentStream._TextStateOp" _TextStateOp))
                ((RTS.<||)
                   (RTS.pEnter "textPos"
                      (RTS.pEnter "PdfContentStream._TextPosOp" _TextPosOp))
                   ((RTS.<||)
                      (RTS.pEnter "textShow"
                         (RTS.pEnter "PdfContentStream._TextShowOp" _TextShowOp))
                      (RTS.pEnter "marked"
                         (do HS.void
                               (RTS.pEnter "PdfContentStream.MarkedContentSeq"
                                  (pMarkedContentSeq pFutureOp))
                             HS.pure ())))))))
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "ET"))
 
_XObj :: D.Parser ()
 
_XObj =
  do RTS.pEnter "PdfValue._Token"
       (PdfValue._Token @(Vector.Vector (RTS.UInt 8))
          (RTS.pEnter "PdfValue._Name" PdfValue._Name))
     RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "Do"))
 
_PageDescription ::
      D.Parser PossibleOp -> (D.Parser () -> D.Parser ())
 
_PageDescription (pFutureOp :: D.Parser PossibleOp)
  (_FutureOp :: D.Parser ()) =
  RTS.pSkipMany (RTS.<||)
    ((RTS.<||)
       (RTS.pEnter "genGraphics"
          (RTS.pEnter "PdfContentStream._GenGraphicsStateOp"
             _GenGraphicsStateOp))
       ((RTS.<||)
          (RTS.pEnter "specialGraphics"
             (RTS.pEnter "PdfContentStream._SpecialGraphicsStateSeq"
                (_SpecialGraphicsStateSeq pFutureOp)))
          ((RTS.<||)
             (RTS.pEnter "colour"
                (RTS.pEnter "PdfContentStream._ColourOp" _ColourOp))
             ((RTS.<||)
                (RTS.pEnter "textState"
                   (RTS.pEnter "PdfContentStream._TextStateOp" _TextStateOp))
                ((RTS.<||)
                   (RTS.pEnter "markedContent"
                      (RTS.pEnter "PdfContentStream._MarkedContentSeq"
                         (_MarkedContentSeq pFutureOp)))
                   ((RTS.<||)
                      (RTS.pEnter "textObj"
                         (RTS.pEnter "PdfContentStream._TextObj" (_TextObj pFutureOp)))
                      ((RTS.<||)
                         (RTS.pEnter "shadingObj"
                            (RTS.pEnter "PdfContentStream._ShadingObj" _ShadingObj))
                         ((RTS.<||)
                            (RTS.pEnter "xObj" (RTS.pEnter "PdfContentStream._XObj" _XObj))
                            ((RTS.<||)
                               (RTS.pEnter "inlineObj"
                                  (RTS.pEnter "PdfContentStream._InlineImageObj" _InlineImageObj))
                               ((RTS.<||)
                                  (RTS.pEnter "pathObj"
                                     (RTS.pEnter "PdfContentStream._PathObj" _PathObj))
                                  (RTS.pEnter "compat"
                                     (RTS.pEnter "PdfContentStream._CompatOps"
                                        (_CompatOps _FutureOp)))))))))))))
 
_PossibleOp :: D.Parser ()
 
_PossibleOp =
  do RTS.pSkipMany (RTS.<||)
       (RTS.pEnter "PdfValue._Token"
          (PdfValue._Token @DirectObj
             (RTS.pEnter "PdfContentStream._DirectObj" _DirectObj)))
     RTS.pEnter "PdfValue._Token"
       (PdfValue._Token @(Vector.Vector (RTS.UInt 8))
          (RTS.pSkipMany (RTS.<||)
             (RTS.pEnter "PdfValue._NameChar" PdfValue._NameChar)))
 
_ContentStream :: D.Parser ()
 
_ContentStream =
  do RTS.pSkipMany (RTS.<||)
       (RTS.pEnter "PdfValue._AnyWS" PdfValue._AnyWS)
     RTS.pEnter "PdfContentStream._PageDescription"
       (_PageDescription
          (RTS.pEnter "PdfContentStream.Bot"
             (pBot @PossibleOp
                (RTS.pEnter "PdfContentStream.PossibleOp" pPossibleOp)))
          (RTS.pEnter "PdfContentStream._Bot"
             (_Bot @PossibleOp
                (RTS.pEnter "PdfContentStream._PossibleOp" _PossibleOp))))
 
_FontOp :: D.Parser ()
 
_FontOp =
  (RTS.<||)
    (RTS.pEnter "setGlyphWidth"
       (do RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @(RTS.UInt 8)
                (HS.const ()
                   HS.<$> RTS.pMatch1 "322:12--322:21" (RTS.bcSingle (RTS.uint8 48))))
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "d0"))))
    (RTS.pEnter "setGlpyhWidthBoundingBox"
       (do RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @(RTS.UInt 8)
                (HS.const ()
                   HS.<$> RTS.pMatch1 "327:12--327:21" (RTS.bcSingle (RTS.uint8 48))))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @PdfValue.Number
                (RTS.pEnter "PdfValue._Number" PdfValue._Number))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @(RTS.UInt 8)
                (HS.const ()
                   HS.<$> RTS.pMatch1 "332:12--332:21" (RTS.bcSingle (RTS.uint8 48))))
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "d1"))))
 
_LastElt ::
  forall a c d.
    (RTS.DDL a, RTS.DDL c, RTS.DDL d, RTS.IsLoop a, RTS.ColElType a c,
     RTS.ColElType a d) =>
      a -> D.Parser ()
 
_LastElt (fs :: a) =
  RTS.loopFoldM (\(last :: ()) (f :: d) -> HS.pure ()) () fs
 
_LookupDirectNat ::
  forall a. RTS.DDL a => a -> (Map.Map a DirectObj -> D.Parser ())
 
_LookupDirectNat (k :: a) (m :: Map.Map a DirectObj) =
  do (vV :: DirectObj) <-
       RTS.pIsJust "457:11--457:20"
         ("Missing key: " HS.++ HS.show (k :: a))
         (Map.lookup k m)
     (v :: PdfValue.Number) <-
       RTS.pIsJust "458:11--458:26" "Expected `number`"
         (HS.getField @"number" (HS.getField @"box" vV))
     RTS.pEnter "PdfValue._NumberAsNat" (PdfValue._NumberAsNat v)
 
_MarkedContentOp :: D.Parser ()
 
_MarkedContentOp =
  (RTS.<||)
    (RTS.pEnter "defineMarkedContent"
       (do RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @(Vector.Vector (RTS.UInt 8))
                (RTS.pEnter "PdfValue._Name" PdfValue._Name))
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "MP"))))
    (RTS.pEnter "defMarkedContentPoint"
       (do RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @(Vector.Vector (RTS.UInt 8))
                (RTS.pEnter "PdfValue._Name" PdfValue._Name))
           RTS.pEnter "PdfValue._Token"
             (PdfValue._Token @ContentProps
                (RTS.pEnter "PdfContentStream._ContentProps" _ContentProps))
           RTS.pEnter "PdfValue._KW" (PdfValue._KW (Vector.vecFromRep "DP"))))