import LeanUrl.Util
import LeanUrl.Percent.Basic
import LeanUrl.Parser.Util

namespace LeanUrl.Parser.OpaqueHost

open SyntaxViolation

def parse (chars : Array Char) : Except SyntaxViolationLog String :=
  -- 1. Forbidden host code points cause failure
  if chars.any (fun c => c.isForbiddenHostCodePoint)
  then
    .error (hostInvalidCodePoint, none, none)
  else
    -- 2. Non-URL code points (except %) are a validation error but NOT a failure
    -- They will be percent-encoded below (WHATWG spec says this is just a warning)
    -- 3. Invalid percent-encoding (% not followed by two hex digits) is also just
    -- a validation error per WHATWG, the % gets percent-encoded as %25
    -- So we don't check pctEncodeCk anymore - invalid % will be encoded
    -- 4. Percent-encode the result using C0 control percent-encode set
    .ok (LeanUrl.Percent.utf8PercentEncode chars.toString LeanUrl.Percent.PercentEncodeSets.c0Controls)
