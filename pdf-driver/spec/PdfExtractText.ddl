import Stdlib
import PdfValue
import PdfDecl
import PdfXRef

import Unicode

import ContentStreamLight
-- TODO: gradually replace this with a more heavyweight parser/validator

-- entry point for text extraction
def ExtractRootUTF8Bytes r = {
  @utf8s = ExtractRootText r;
  ^(utf8Bytes utf8s)
}

def ExtractRootText r = Default [] {
  ExtractPageOrPagesText nothing r
}

def ExtractPageOrPagesText p c =
  (ExtractPageText p c) |
  (ExtractPagesText p c)

def ExtractPageText (p : maybe Ref) (r : Ref) =
{
    @v = ResolveValRef r;
    @dict = v is dict;
    CheckType "Page" dict;
    CheckParent p dict;
    ExtractContentsText dict
}

def ExtractPagesText (p : maybe Ref) (r : Ref) =
{
    @v = ResolveValRef r;
    @dict = v is dict;
    CheckType "Pages" dict;
    CheckParent p dict;
    -- Ignore count for now
    @kidsv = Lookup "Kids" dict;    -- XXX: can this be a ref?
    @kids  = kidsv is array;
    @pagesText = map (refv in kids) {
      @ref = refv is ref;
      ExtractPageOrPagesText (just r) ref
    };
    ^(concat pagesText)
}

def CheckParent (p : maybe Ref) (dict : [[uint 8] -> Value]) =
    { p is nothing;
      @v = Optional (LookupRef "Parent" dict);
      v is nothing;
    }
    <|
    { @pref = p is just;
      @dpref = LookupRef "Parent" dict;
      Guard (dpref == pref);
    }

-- Check that the (optional) contents point to a valid Content Stream
def ExtractContentsText d = Default [ ] {
  @s = Lookup "Contents" d ; -- try to find content stream
  @strm =
    { @arr = s is array;
      @strms = map (s in arr) {
        @strm = ResolveStream s;
        @strmBody = strm.body is ok;
        WithStream strmBody (Many UInt8)
      };
      ^ (arrayStream (concat strms))
    } <|
    { @strm = ResolveStream s ;
      strm.body is ok
    };
  WithStream strm (Only ContentStream) -- parse the content stream
}

--------------------------------------------------------------------------------
-- Catalogue objects

-- The JS stuff will be take care of by the global safety check as
-- Names->JavaScript maps to JavaScript actions.

def ExtractCatalogText r = {
  @catv = ResolveValRef r;
  @cat   = catv is dict;
  CheckType "Catalog" cat;
  @pages = LookupRef "Pages" cat;
  ExtractRootText pages;
}

--------------------------------------------------------------------------------
-- Checked

def CheckDecl expectId expectGen (decl : TopDecl) = {
  Guard (decl.id == expectId);
  Guard (decl.gen == expectGen);
  obj    = ^ decl.obj;
}

def TopDeclCheck expectId expectGen = {
  @decl = TopDecl;
  CheckDecl expectId expectGen decl;
}

def ResolveObjectStreamEntryCheck
      expectId expectGen (oid : Nat) (gen : Nat) (idx : Nat) = {
  @decl = ResolveObjectStreamEntry oid gen idx;
  CheckDecl expectId expectGen decl;
}
