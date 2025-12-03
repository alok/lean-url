import LeanUrl.Util
import LeanUrl.Parser.Util
import LeanUrl.Idna
import Std.Data.HashSet

open Std (HashSet)
open LeanUrl.Idna

set_option linter.unusedVariables false

/-
IDNA/UTS46 Unicode Processing for WHATWG URL
See: https://url.spec.whatwg.org/#host-parsing
See: https://www.unicode.org/reports/tr46/
-/

/-
 4.2 ToASCII (UTS46)

The operation corresponding to ToASCII of [RFC3490] is defined by the following steps:

Input
    A prospective domain_name expressed as a sequence of Unicode code points
    Boolean flags: CheckHyphens, CheckBidi, CheckJoiners, UseSTD3ASCIIRules,
                   Transitional_Processing (deprecated), VerifyDnsLength, IgnoreInvalidPunycode

Processing
    1. Apply the Processing Steps in Section 4, using the input boolean flags.
    2. Break the result into labels at U+002E FULL STOP.
    3. Convert each label with non-ASCII characters into Punycode, prefix by "xn--".
    4. If VerifyDnsLength, check: domain 1-253 chars, each label 1-63 chars.
    5. If error, return failure. Otherwise join labels with '.' and return.
-/
def unicodeToAscii
  (domainName : String)
  (
    checkHyphens
    checkBidi
    checkJoiners
    useStd3ASCIIRules
    transitionalProcessing
    verifyDnsLength
    ignoreInvalidPunycode
    : Option Bool := none
  )
  : Except String String := do
  -- Use strict mode if CheckHyphens or UseSTD3ASCIIRules is set
  let beStrict := checkHyphens.getD false || useStd3ASCIIRules.getD false

  -- Process domain using our IDNA implementation
  let processed ← processDomain domainName beStrict

  -- Verify DNS length if requested
  if verifyDnsLength.getD false then
    -- Domain length check (1-253)
    if processed.isEmpty ∨ processed.length > 253 then
      throw "Domain length must be 1-253 characters"
    -- Label length check (1-63)
    for label in processed.splitOn "." do
      if label.length > 63 then
        throw "Label length must be 1-63 characters"

  return processed


/-
Let result be the result of running Unicode ToASCII with
domain_name set to domain,
CheckHyphens set to beStrict,
CheckBidi set to true,
CheckJoiners set to true,
UseSTD3ASCIIRules set to beStrict,
Transitional_Processing set to false,
VerifyDnsLength set to beStrict,
and IgnoreInvalidPunycode set to false.
-/
def domainToAscii (domainName : String) (beStrict : Bool) : Except SyntaxViolationLog String :=
  let result := unicodeToAscii
    domainName
    (checkHyphens := some beStrict)
    (checkBidi := some true)
    (checkJoiners := some true)
    (useStd3ASCIIRules := some beStrict)
    (transitionalProcessing := some false)
    (verifyDnsLength := some beStrict)
    (ignoreInvalidPunycode := some false)
  match result with
  | .error e => throw (SyntaxViolation.domainInvalidCodePoint, none, some sourceLoc!)
  | .ok a =>
    if a.any (fun c => c.forbiddenDomainCodePoint)
    then throw (SyntaxViolation.domainInvalidCodePoint, none, some s!"{sourceLoc!}")
    else .ok a


/-
4.3 ToUnicode (UTS46)

Converts ACE-encoded labels back to Unicode for display.
Unlike ToASCII, this always produces a result (may record errors but continues).
-/
def unicodeToUnicode
  (domainName : String)
  (
    checkHyphens
    checkBidi
    checkJoiners
    useStd3ASCIIRules
    transitionalProcessing
    ignoreInvalidPunycode
    : Option Bool := none
  ) : Except String String :=
  -- First apply mapping, then decode any ACE labels
  match LeanUrl.Idna.domainToUnicode (mapString domainName) with
  | some result => .ok result
  | none => .ok domainName  -- Fallback to original on decode failure


/-
Let result be the result of running Unicode ToUnicode with
domain_name set to domain,
CheckHyphens set to beStrict,
CheckBidi set to true,
CheckJoiners set to true,
UseSTD3ASCIIRules set to beStrict,
Transitional_Processing set to false,
and IgnoreInvalidPunycode set to false.
-/
def domainToUnicode (domainName : String) (beStrict : Bool) : Except String String :=
  unicodeToUnicode
    domainName
    (checkHyphens := some beStrict)
    (checkBidi := some true)
    (checkJoiners := some true)
    (useStd3ASCIIRules := some beStrict)
    (transitionalProcessing := some false)
    (ignoreInvalidPunycode := some false)
