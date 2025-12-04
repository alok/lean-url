import LeanUrl.Util
import LeanUrl.Parser.Util
import LeanUrl.Parser.Ipv4
import LeanUrl.Parser.Ipv6
import LeanUrl.Parser.OpaqueHost
import LeanUrl.Parser.Unicode
import LeanUrl.Percent.Basic
import LeanUrl.Url.Basic

namespace LeanUrl.Parser.Host

structure State where
  isOpaque : Bool
  pointer : Nat
  input : Array Char
deriving Inhabited

open SyntaxViolation

def curr? : EStateM SyntaxViolationLog State (Option Char) := fun s =>
  .ok s.input[s.pointer]? s

def peek1? : EStateM SyntaxViolationLog State (Option Char) := fun s =>
  .ok s.input[s.pointer+1]? s

def hasNext : EStateM SyntaxViolationLog State Bool := do
  return (← peek1?).isSome

def remainingToString : EStateM SyntaxViolationLog State String := fun s =>
  .ok (s.input[s.pointer:] : Subarray Char).toString s

/-- Check if a string ends in a number (for IPv4 detection) -/
def stringEndsInNumber (s : String) : Bool :=
  let parts := strictSplit s.toList.toArray '\u002E'
  let parts := if parts.back? == some "" ∧ parts.size > 1 then parts.pop else parts
  match parts.back? with
  | none => false
  | some last =>
    if last != "" && last.all (fun c => c.isDigit) then true
    else (Ipv4Number.parse last.toArray).isOk

def endsInNumber : EStateM SyntaxViolationLog State Bool := do
  return stringEndsInNumber (← get).input.toString

def parseAux : EStateM SyntaxViolationLog State Host := do
  /- 1. -/
  if let some '\u005B' := (← curr?)
  then
    /- 1.1 -/
    if !((← get).input.back? == some ']') then throw (ipv6Unclosed, none, none)
    let extracted : Array Char :=
      let s := (← get).input
      let s := (s.drop 1)
      s.pop
    /- 1.2 -/
    match Ipv6.parse extracted with
    | .error e => throw e
    | .ok a => return (Host.ipAddr (Std.Net.IPAddr.v6 ⟨a⟩))
  /- 2. -/
  if (← get).isOpaque
  then
    let opaqueHost := OpaqueHost.parse (← get).input
    match opaqueHost with
    | .error e => throw e
    | .ok a =>
      -- Empty opaque hosts are valid per WHATWG spec
      if he: a.isEmpty
      then return Host.empty
      else if h: a.all Char.isAscii
      then return (Host.opq ⟨a, by simp [he], h⟩)
      else throw (invalidUrlUnit, none, none)
  /- 3. -/
  if (← curr?).isNone then throw (hostEarlyEOF, some (Int.ofNat (← get).pointer), none)
  /- 4. -/
  let percentDecoded := Percent.percentDecodeStr (← remainingToString)
  -- Use strict UTF-8 decoding - invalid sequences should fail
  let domain : String ← match Percent.utf8DecodeWithoutBOMOrFail? percentDecoded with
    | some s => pure s
    | none => throw (invalidUrlUnit, none, some "Invalid UTF-8 in host")
  /- 5., 6. -/
  let asciiDomain ← domainToAscii domain false
  /- 7. Check ends in number using the processed domain, not original input -/
  if !asciiDomain.isEmpty && stringEndsInNumber asciiDomain
  then
    match Ipv4.parse asciiDomain with
    | .error e => throw e
    | .ok a => return Host.ipAddr <| Std.Net.IPAddr.v4 a
  else
    if h: !asciiDomain.isEmpty
    then return (Host.domain ⟨asciiDomain, h⟩)
    else throw (invalidUrlUnit, none, none)

def parseWwg (chars : Array Char) (isOpaque : Bool) : Except SyntaxViolationLog Host :=
  match parseAux.run { input := chars, pointer := 0, isOpaque } with
  | .ok a _ => .ok a
  | .error e _ => .error e
