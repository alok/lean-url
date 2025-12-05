/-
Safe Option extraction patterns for verified .get! elimination.

These helpers allow extracting values from Options with compile-time
verification that the extraction is safe.
-/
import LeanUrl.Parser.Basic

namespace LeanUrl.Parser.Safe

/-! ## Core safe extraction patterns -/

/-- Extract character when predicate check passes.
    The proof `h` ensures `c?` is `some`. -/
def Option.getWhenPred {α : Type} (o : Option α) (f : α → Bool)
    (h : (o.map f).getD false = true) : α :=
  match ho : o with
  | some a => a
  | none => absurd h (by simp)

/-- Extract value when `isSome` is true -/
def Option.getWhenIsSome {α : Type} (o : Option α) (h : o.isSome = true) : α :=
  match ho : o with
  | some a => a
  | none => absurd h (by simp)

/-- Extract value when `!= none` check passes -/
def Option.getWhenNotNone {α : Type} [DecidableEq α] (o : Option α)
    (h : (o != none) = true) : α :=
  match ho : o with
  | some a => a
  | none => absurd h (by simp)

/-- Extract value when equality check passes -/
def Option.getWhenEq {α : Type} [DecidableEq α] (o : Option α) (a : α)
    (h : (o == some a) = true) : α :=
  match ho : o with
  | some x => x
  | none => absurd h (by simp)

/-- Extract character when OR'd condition passes -/
def Option.getWhenPredOrEq (o : Option Char) (f : Char → Bool) (a : Char)
    (h : ((o.map f).getD false || (o == some a)) = true) : Char :=
  match ho : o with
  | some c => c
  | none => absurd h (by simp)

/-! ## Monadic safe extraction -/

/-- Safe curr? with extraction when predicate passes -/
def currWhenPred (f : Char → Bool) : ParserM (Option Char) := do
  let c? ← curr?
  if h : (c?.map f).getD false then
    return some (Option.getWhenPred c? f h)
  else
    return none

/-- Safe curr? that returns the character directly when available -/
def currSome : ParserM (Option Char) := curr?

/-! ## Pattern: Replace `.get!` after predicate check

Instead of:
```
let c? ← curr?
if (c?.map f).getD false then
  ... c?.get! ...
```

Use:
```
let c? ← curr?
match c? with
| some c => if f c then ... c ... else ...
| none => ...
```

Or with our helper:
```
if let some c := ← currWhenPred f then
  ... c ...
```
-/

/-! ## Verified transformations -/

/-- Proof that getWhenPred gives same result as get! when safe -/
theorem getWhenPred_eq_get! {α : Type} [Inhabited α] (o : Option α) (f : α → Bool)
    (h : (o.map f).getD false = true) :
    Option.getWhenPred o f h = o.get! := by
  cases o with
  | none => simp at h
  | some a => rfl

/-- Proof that getWhenIsSome gives same result as get! -/
theorem getWhenIsSome_eq_get! {α : Type} [Inhabited α] (o : Option α)
    (h : o.isSome = true) :
    Option.getWhenIsSome o h = o.get! := by
  cases o with
  | none => simp at h
  | some a => rfl

end LeanUrl.Parser.Safe
