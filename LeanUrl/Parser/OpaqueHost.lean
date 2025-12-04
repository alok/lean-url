import LeanUrl.Util
import LeanUrl.Percent.Basic
import LeanUrl.Parser.Util

namespace LeanUrl.Parser.OpaqueHost

open SyntaxViolation

def pctEncodeCk : List Char → Bool
  | [] => true
  | hd :: rest =>
    if hd == '\u0025'
    then
      match rest with
      | a :: b :: rest => a.isASCIIHexDigit && b.isASCIIHexDigit && pctEncodeCk rest
      | _ => false
    else
      pctEncodeCk rest

def parseAux : EStateM SyntaxViolationLog (Array Char) String := do
  let s ← get
  -- 1. Forbidden host code points cause failure
  if s.any (·.isForbiddenHostCodePoint)
  then
    throw (hostInvalidCodePoint, none, none)
  -- 2. Non-URL code points (except %) are a validation error but NOT a failure
  -- They will be percent-encoded below (WHATWG spec says this is just a warning)
  -- 3. Invalid percent-encoding (% not followed by two hex digits) is also just
  -- a validation error per WHATWG, the % gets percent-encoded as %25
  -- So we don't check pctEncodeCk anymore - invalid % will be encoded
  -- 4. Percent-encode the result using C0 control percent-encode set
  return LeanUrl.Percent.utf8PercentEncode s.toString LeanUrl.Percent.PercentEncodeSets.c0Controls

def parse (chars : Array Char) : Except SyntaxViolationLog String :=
  match parseAux.run chars with
  | .ok opaqueHost _ => .ok opaqueHost
  | .error e _ => .error e
