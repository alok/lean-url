/-
# IDNA Processing for WHATWG URL
Implements the domain name processing required by WHATWG URL spec.

References:
- WHATWG URL: https://url.spec.whatwg.org/#host-parsing
- UTS46: https://www.unicode.org/reports/tr46/
- RFC 5891: https://datatracker.ietf.org/doc/html/rfc5891
-/
import LeanUrl.Punycode

namespace LeanUrl.Idna

/-- Characters that should be mapped to nothing (removed) in IDNA processing -/
def ignoredCodePoints : List UInt32 := [
  0x00AD,   -- SOFT HYPHEN
  0x034F,   -- COMBINING GRAPHEME JOINER
  0x180B,   -- MONGOLIAN FREE VARIATION SELECTOR ONE
  0x180C,   -- MONGOLIAN FREE VARIATION SELECTOR TWO
  0x180D,   -- MONGOLIAN FREE VARIATION SELECTOR THREE
  0x180F,   -- MONGOLIAN FREE VARIATION SELECTOR FOUR
  0x200B,   -- ZERO WIDTH SPACE
  0x200C,   -- ZERO WIDTH NON-JOINER
  0x200D,   -- ZERO WIDTH JOINER
  0x2060,   -- WORD JOINER
  0xFE00, 0xFE01, 0xFE02, 0xFE03, 0xFE04, 0xFE05, 0xFE06, 0xFE07,
  0xFE08, 0xFE09, 0xFE0A, 0xFE0B, 0xFE0C, 0xFE0D, 0xFE0E, 0xFE0F,  -- VARIATION SELECTORS
  0xFEFF    -- ZERO WIDTH NO-BREAK SPACE (BOM)
]

/-- Check if a character should be ignored (mapped to nothing) -/
def isIgnored (c : Char) : Bool :=
  ignoredCodePoints.contains c.val

/-- Map fullwidth ASCII (U+FF01-U+FF5E) to regular ASCII -/
def mapFullwidth (c : Char) : Char :=
  let n := c.val
  if 0xFF01 ≤ n ∧ n ≤ 0xFF5E then
    -- Fullwidth forms are offset by 0xFEE0 from ASCII
    Char.ofNat (n.toNat - 0xFEE0)
  else
    c

/-- Map fullwidth digits (U+FF10-U+FF19) and letters to ASCII -/
def mapFullwidthDigits (c : Char) : Char :=
  let n := c.val
  if 0xFF10 ≤ n ∧ n ≤ 0xFF19 then  -- Fullwidth 0-9
    Char.ofNat (n.toNat - 0xFEE0)
  else
    c

/-- Map ideographic full stop (U+3002) to ASCII period -/
def mapIdeographicStop (c : Char) : Char :=
  if c.val == 0x3002 then '.'
  else c

/-- U+3000 ideographic space maps to U+0020 space -/
def mapIdeographicSpace (c : Char) : Char :=
  if c.val == 0x3000 then ' '
  else c

/-- Map halfwidth Katakana to regular Katakana (simplified) -/
def mapHalfwidth (c : Char) : Char :=
  -- Halfwidth Katakana: U+FF65-U+FF9F
  -- This is a simplified version - full implementation would need the complete mapping table
  c

/-- Map mathematical alphanumeric symbols to ASCII -/
def mapMathAlpha (c : Char) : Char :=
  let n := c.val.toNat
  -- Mathematical Bold Capital (U+1D400-U+1D419 → A-Z)
  if 0x1D400 ≤ n ∧ n ≤ 0x1D419 then Char.ofNat (n - 0x1D400 + 'a'.toNat)
  -- Mathematical Bold Small (U+1D41A-U+1D433 → a-z)
  else if 0x1D41A ≤ n ∧ n ≤ 0x1D433 then Char.ofNat (n - 0x1D41A + 'a'.toNat)
  -- Mathematical Italic Capital (U+1D434-U+1D44D → A-Z)
  else if 0x1D434 ≤ n ∧ n ≤ 0x1D44D then Char.ofNat (n - 0x1D434 + 'a'.toNat)
  -- Mathematical Italic Small (U+1D44E-U+1D467 → a-z)
  else if 0x1D44E ≤ n ∧ n ≤ 0x1D467 then Char.ofNat (n - 0x1D44E + 'a'.toNat)
  -- Mathematical Bold Italic Capital (U+1D468-U+1D481 → A-Z)
  else if 0x1D468 ≤ n ∧ n ≤ 0x1D481 then Char.ofNat (n - 0x1D468 + 'a'.toNat)
  -- Mathematical Bold Italic Small (U+1D482-U+1D49B → a-z)
  else if 0x1D482 ≤ n ∧ n ≤ 0x1D49B then Char.ofNat (n - 0x1D482 + 'a'.toNat)
  -- Mathematical Script Capital (U+1D49C-U+1D4B5 → A-Z, with gaps)
  else if 0x1D49C ≤ n ∧ n ≤ 0x1D4B5 then Char.ofNat (n - 0x1D49C + 'a'.toNat)
  -- Mathematical Script Small (U+1D4B6-U+1D4CF → a-z, with gaps)
  else if 0x1D4B6 ≤ n ∧ n ≤ 0x1D4CF then Char.ofNat (n - 0x1D4B6 + 'a'.toNat)
  -- Add more ranges as needed...
  else c

/-- Simple case folding for ASCII -/
def caseFold (c : Char) : Char :=
  if 'A' ≤ c ∧ c ≤ 'Z' then
    Char.ofNat (c.toNat - 'A'.toNat + 'a'.toNat)
  else
    c

/-- Apply all IDNA character mappings -/
def mapChar (c : Char) : Option Char :=
  if isIgnored c then none
  else
    let c := mapFullwidth c
    let c := mapIdeographicStop c
    let c := mapIdeographicSpace c
    let c := mapMathAlpha c
    let c := caseFold c
    some c

/-- Apply IDNA mapping to a string, removing ignored chars and mapping others -/
def mapString (s : String) : String :=
  String.mk (s.toList.filterMap mapChar)

/-- Check if a character is a valid domain label character after IDNA processing -/
def isValidLabelChar (c : Char) : Bool :=
  -- ASCII letters, digits, hyphen
  ('a' ≤ c ∧ c ≤ 'z') ∨ ('0' ≤ c ∧ c ≤ '9') ∨ c == '-' ∨
  -- Non-ASCII characters (will be encoded with Punycode)
  c.val > 0x7F

/-- IDNA disallowed code points for domain names per UTS46/IDNA2008 -/
def isDisallowed (c : Char) : Bool :=
  let n := c.val
  -- Control characters
  n < 0x20 ∨
  -- DEL
  n == 0x7F ∨
  -- C1 control characters
  (0x80 ≤ n ∧ n ≤ 0x9F) ∨
  -- Some specific disallowed characters
  n == 0x0000 ∨
  -- Replacement character (indicates encoding error)
  n == 0xFFFD ∨
  -- Noncharacters U+FDD0-U+FDEF
  (0xFDD0 ≤ n ∧ n ≤ 0xFDEF) ∨
  -- Noncharacters ending in FFFE or FFFF
  (n % 0x10000 == 0xFFFE) ∨ (n % 0x10000 == 0xFFFF) ∨
  -- Private use areas
  (0xE000 ≤ n ∧ n ≤ 0xF8FF) ∨
  (0xF0000 ≤ n ∧ n ≤ 0xFFFFD) ∨
  (0x100000 ≤ n ∧ n ≤ 0x10FFFD) ∨
  -- Surrogates
  (0xD800 ≤ n ∧ n ≤ 0xDFFF) ∨
  -- CJK Compatibility - Enclosed CJK Letters and Months (contains circled characters)
  (0x3200 ≤ n ∧ n ≤ 0x32FF) ∨
  -- CJK Compatibility - CJK Compatibility (contains squared characters)
  (0x3300 ≤ n ∧ n ≤ 0x33FF) ∨
  -- CJK Compatibility Ideographs
  (0xF900 ≤ n ∧ n ≤ 0xFAFF) ∨
  -- CJK Compatibility Forms
  (0xFE30 ≤ n ∧ n ≤ 0xFE4F) ∨
  -- Halfwidth and Fullwidth Forms (except those we map)
  (0xFFA0 ≤ n ∧ n ≤ 0xFFEF) ∨
  -- Tags
  (0xE0000 ≤ n ∧ n ≤ 0xE007F) ∨
  -- Variation Selectors Supplement
  (0xE0100 ≤ n ∧ n ≤ 0xE01EF)

/-- Split domain into labels by dots (handles ideographic dot) -/
def splitLabels (domain : String) : Array String :=
  let mapped := mapString domain
  -- Split on dots (already mapped ideographic stop to ASCII dot)
  mapped.splitOn "." |>.toArray

/-- Check if a label is a valid Punycode label (starts with xn--) -/
def isAceLabel (label : String) : Bool :=
  label.toLower.startsWith "xn--"

/-- Validate decoded Unicode label content -/
def validateLabelContent (label : String) : Except String Unit := do
  for c in label.toList do
    if isDisallowed c then
      throw s!"Disallowed character U+{Nat.toDigits 16 c.val.toNat |>.asString}"
  -- Check for space (disallowed in domain labels)
  if label.any (· == ' ') then
    throw "Space character in domain label"
  return ()

/-- Validate and process a single label -/
def processLabel (label : String) (beStrict : Bool) : Except String String := do
  if label.isEmpty then
    return ""

  -- Apply mapping
  let mapped := mapString label

  -- If this is an ACE label, validate by roundtrip
  if isAceLabel mapped then
    -- Decode the punycode
    let decoded ← match Punycode.fromAce mapped.toLower with
      | some d => pure d
      | none => throw "Invalid Punycode in ACE label"
    -- Validate the decoded content
    validateLabelContent decoded
    -- Re-encode and verify it matches (case-insensitive)
    let reencoded ← match Punycode.toAce decoded with
      | some e => pure e
      | none => throw "Failed to re-encode ACE label"
    if reencoded.toLower != mapped.toLower then
      throw "ACE label roundtrip mismatch"
    return reencoded.toLower

  -- Check for disallowed characters
  validateLabelContent mapped

  -- If all ASCII, validate label syntax
  if mapped.all (fun c => c.val < 128) then
    -- Check hyphen restrictions in strict mode
    if beStrict then
      if mapped.startsWith "-" ∨ mapped.endsWith "-" then
        throw "Label starts or ends with hyphen"
      if mapped.length >= 4 ∧ mapped.get? ⟨2⟩ == some '-' ∧ mapped.get? ⟨3⟩ == some '-' then
        throw "Label has hyphens in positions 3 and 4"
    return mapped.toLower
  else
    -- Contains non-ASCII: encode to Punycode
    match Punycode.toAce mapped with
    | some ace => return ace.toLower
    | none => throw "Failed to encode label to Punycode"

/-- Process a domain name according to IDNA/UTS46 -/
def processDomain (domain : String) (beStrict : Bool) : Except String String := do
  -- Handle empty domain
  if domain.isEmpty then
    return ""

  let labels := splitLabels domain
  let mut result := #[]

  for label in labels do
    let processed ← processLabel label beStrict
    result := result.push processed

  -- Join with dots
  return ".".intercalate result.toList

/-- Decode an ACE label to Unicode -/
def decodeLabel (label : String) : Option String :=
  if isAceLabel label then
    Punycode.fromAce label.toLower
  else
    some label

/-- Convert domain from ACE to Unicode (for display) -/
def domainToUnicode (domain : String) : Option String := do
  let labels := domain.splitOn "."
  let mut result := #[]
  for label in labels do
    let decoded ← decodeLabel label
    result := result.push decoded
  return ".".intercalate result.toList

end LeanUrl.Idna
