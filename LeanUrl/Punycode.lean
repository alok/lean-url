/-
# Punycode: A Bootstring encoding of Unicode for IDNA
RFC 3492: https://datatracker.ietf.org/doc/html/rfc3492

Punycode uses Bootstring, a general algorithm for representing Unicode
strings in ASCII. The parameters are tuned for Unicode domain names.
-/

namespace LeanUrl.Punycode

/-- Insert element at position i, shifting subsequent elements right -/
def arrayInsertAt {α : Type} (arr : Array α) (i : Nat) (x : α) : Array α :=
  let left := arr.toList.take i
  let right := arr.toList.drop i
  (left ++ [x] ++ right).toArray

/-- Punycode parameters from RFC 3492 section 5 -/
def base      : Nat := 36
def tmin      : Nat := 1
def tmax      : Nat := 26
def skew      : Nat := 38
def damp      : Nat := 700
def initialBias : Nat := 72
def initialN  : UInt32 := 128
def delimiter : Char := '-'

/-- Convert a digit value to a Punycode character (a-z for 0-25, 0-9 for 26-35) -/
def digitToChar (d : Nat) : Char :=
  if d < 26 then Char.ofNat (d + 'a'.toNat)
  else Char.ofNat (d - 26 + '0'.toNat)

/-- Convert a Punycode character to a digit value -/
def charToDigit (c : Char) : Option Nat :=
  let n := c.toNat
  if 'a'.toNat ≤ n ∧ n ≤ 'z'.toNat then some (n - 'a'.toNat)
  else if 'A'.toNat ≤ n ∧ n ≤ 'Z'.toNat then some (n - 'A'.toNat)
  else if '0'.toNat ≤ n ∧ n ≤ '9'.toNat then some (n - '0'.toNat + 26)
  else none

/-- Bias adaptation function from RFC 3492 section 6.1 -/
def adapt (delta : Nat) (numPoints : Nat) (firstTime : Bool) : Nat := Id.run do
  let mut delta := if firstTime then delta / damp else delta / 2
  delta := delta + delta / numPoints
  let mut k : Nat := 0
  while delta > ((base - tmin) * tmax) / 2 do
    delta := delta / (base - tmin)
    k := k + base
  return k + (base - tmin + 1) * delta / (delta + skew)

/-- Compute threshold for a given k and bias -/
def threshold (k : Nat) (bias : Nat) : Nat :=
  if k <= bias + tmin then tmin
  else if k >= bias + tmax then tmax
  else k - bias

/-- Encode a Unicode string to Punycode.
Returns `none` if the input contains invalid characters. -/
def encode (input : String) : Option String := Id.run do
  let codePoints := input.toList.map (·.toNat)

  -- Basic code points are ASCII letters, digits, and hyphen
  let basicCodePoints := codePoints.filter (· < 128)
  let basicStr := String.mk (basicCodePoints.map Char.ofNat)

  let nonBasicCodePoints := codePoints.filter (· >= 128)
  if nonBasicCodePoints.isEmpty then
    return some basicStr

  -- Sort and deduplicate non-basic code points for iteration
  let sortedNonBasic := (nonBasicCodePoints.toArray.qsort (· < ·)).toList.eraseDups

  let mut output := basicStr
  let h := basicCodePoints.length

  if h > 0 then
    output := output.push delimiter

  let mut n := initialN.toNat
  let mut delta : Nat := 0
  let mut bias := initialBias
  let mut handledCodePoints := h

  for m in sortedNonBasic do
    if m < n then continue  -- Skip already processed

    -- Increase delta for all code points below m
    delta := delta + (m - n) * (handledCodePoints + 1)
    n := m

    for cp in codePoints do
      if cp < n then
        delta := delta + 1
      else if cp == n then
        -- Encode delta in variable-length integer
        let mut q := delta
        let mut k := base
        while true do
          let t := threshold k bias
          if q < t then
            output := output.push (digitToChar q)
            break
          let digit := t + ((q - t) % (base - t))
          output := output.push (digitToChar digit)
          q := (q - t) / (base - t)
          k := k + base
        handledCodePoints := handledCodePoints + 1
        bias := adapt delta handledCodePoints (handledCodePoints == h + 1)
        delta := 0

    delta := delta + 1
    n := n + 1

  return some output

/-- Decode a Punycode string to Unicode.
Returns `none` if the input is malformed. -/
def decode (input : String) : Option String := Id.run do
  let chars := input.toList

  -- Find the last delimiter
  let lastDelimPos := chars.reverse.findIdx? (· == delimiter)

  let (basicPart, extendedPart) := match lastDelimPos with
    | none => ([], chars)
    | some rpos =>
      let pos := chars.length - 1 - rpos
      (chars.take pos, chars.drop (pos + 1))

  -- Start with basic code points
  let mut output := basicPart.toArray

  let mut n : Nat := initialN.toNat
  let mut i : Nat := 0
  let mut bias := initialBias

  let mut extChars := extendedPart

  while !extChars.isEmpty do
    let oldi := i
    let mut w : Nat := 1
    let mut k := base

    -- Decode one delta value
    let mut broke := false
    while !extChars.isEmpty do
      let c := extChars.head!
      extChars := extChars.tail!

      let some digit := charToDigit c | return none

      i := i + digit * w
      let t := threshold k bias

      if digit < t then
        broke := true
        break

      w := w * (base - t)
      k := k + base

    if !broke && !extChars.isEmpty then
      return none

    bias := adapt (i - oldi) (output.size + 1) (oldi == 0)
    n := n + i / (output.size + 1)
    i := i % (output.size + 1)

    -- Insert the decoded code point
    output := arrayInsertAt output i (Char.ofNat n)
    i := i + 1

  return some (String.mk output.toList)

/-- Encode a domain label to ACE form if it contains non-ASCII characters.
Prepends "xn--" prefix to Punycode-encoded labels. -/
def toAce (label : String) : Option String :=
  if label.all (fun c => c.toNat < 128) then
    some label
  else
    match encode label with
    | some encoded => some s!"xn--{encoded}"
    | none => none

/-- Decode an ACE label (with "xn--" prefix) to Unicode.
Returns the original label if it doesn't have the ACE prefix. -/
def fromAce (label : String) : Option String :=
  if label.startsWith "xn--" then
    decode (label.drop 4)
  else
    some label

end LeanUrl.Punycode
