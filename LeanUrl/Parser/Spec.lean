/-
Verification specs for the URL parser state machine.
Uses mvcgen + grind to verify safety of Option.get! calls.
-/
import Std.Tactic.Do
import LeanUrl.Parser.Basic

open Std.Do
open LeanUrl.Parser

namespace LeanUrl.Parser.Spec

/-! ## Predicates on Machine state -/

/-- The pointer is valid (points to a character in input) -/
def pointerValid (m : Machine) : Prop :=
  match m.pointer with
  | .ofNat n => n < m.input.size
  | _ => False

/-- The current character exists -/
def hasCurr (m : Machine) : Prop :=
  pointerValid m

/-! ## Specifications for basic operations -/

/-- Spec for curr?: when pointer is valid, returns some -/
@[spec]
theorem curr?_spec_some :
    ∀ (methods : Methods) (m : Machine),
      pointerValid m →
      ∃ c, curr? methods m = .ok (some c) m ∧
           match m.pointer with
           | .ofNat n => m.input[n]? = some c
           | _ => False := by
  intro methods m hvalid
  unfold pointerValid at hvalid
  unfold curr?
  match hp : m.pointer with
  | .ofNat n =>
    simp only [hp] at hvalid ⊢
    have heq : m.input[n]? = some m.input[n] := Array.getElem?_eq_some_iff.mpr ⟨hvalid, rfl⟩
    simp only [heq]
    exact ⟨m.input[n], rfl, rfl⟩
  | .negSucc _ =>
    simp only [hp] at hvalid

/-- Spec for curr?: when pointer is invalid, returns none -/
@[spec]
theorem curr?_spec_none :
    ∀ (methods : Methods) (m : Machine),
      ¬pointerValid m →
      curr? methods m = .ok none m := by
  intro methods m hinvalid
  unfold pointerValid at hinvalid
  unfold curr?
  match hp : m.pointer with
  | .ofNat n =>
    simp only [hp, Nat.not_lt] at hinvalid
    simp only [Array.getElem?_eq_none hinvalid]
  | .negSucc _ =>
    rfl

/-! ## Key lemma: Option.map ... .getD false implies isSome -/

theorem option_map_getD_false_implies_some {α : Type} (o : Option α) (f : α → Bool) :
    (o.map f).getD false = true → o.isSome := by
  intro h
  cases o with
  | none => simp at h
  | some _ => rfl

theorem option_get!_of_map_getD {α : Type} [Inhabited α] (o : Option α) (f : α → Bool) :
    (o.map f).getD false = true → ∃ a, o = some a := by
  intro h
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl⟩

/-! ## Safe unwrap via proof -/

/-- When we know o is some, we can extract the value safely -/
theorem Option.some_of_isSome {α : Type} {o : Option α} (h : o.isSome) : ∃ a, o = some a := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl⟩

/-- Pattern for safe unwrapping: use match with proof -/
theorem option_map_getD_get {α : Type} [Inhabited α] (o : Option α) (f : α → Bool) (hcond : (o.map f).getD false) :
    ∃ a, o = some a ∧ f a := by
  cases o with
  | none => simp at hcond
  | some a =>
    simp only [Option.map_some, Option.getD_some] at hcond
    exact ⟨a, rfl, hcond⟩

/-! ## Attempting to verify schemeStartState -/

/-- Safe version of schemeStartState without get! -/
def schemeStartStateSafe : ParserM Unit := do
  let c? ← curr?
  match c? with
  | some c =>
    if c.isAlpha then
      modify (fun m => { m with buffer := m.buffer.push c.toLower, state := .scheme })
    else if let none := (← get).stateOverride then
      modify (fun m => { m with state := .noScheme, pointer := m.pointer - 1 })
    else
      throw sourceLoc!
  | none =>
    if let none := (← get).stateOverride then
      modify (fun m => { m with state := .noScheme, pointer := m.pointer - 1 })
    else
      throw sourceLoc!

/-- Key insight: when (o.map f).getD false = true, Option.get! o = the value -/
theorem option_get!_when_map_true {α : Type} [Inhabited α] (o : Option α) (f : α → Bool) :
    (o.map f).getD false = true → ∀ a, o = some a → o.get! = a := by
  intro h a heq
  simp only [heq, Option.get!_some]

/-- The key lemma for eliminating .get! in the parser -/
theorem get!_safe_after_map_check {c? : Option Char} (hcond : (c?.map Char.isAlpha).getD false = true) :
    c?.get! = match c? with | some c => c | none => default := by
  cases c? with
  | none => simp at hcond
  | some c => simp only [Option.get!_some]

/-! ## mvcgen verification of parser functions -/

/-- Simple test: verify curr? postcondition with mvcgen -/
theorem curr?_triple :
    Triple (curr? : ParserM (Option Char))
      ⌜True⌝
      (PostCond.noThrow fun _ => ⌜True⌝) := by
  unfold curr?
  mvcgen
  all_goals try mleave
  all_goals try grind
  -- Remaining goals after mvcgen
  all_goals sorry

/-- Verify schemeStartState has well-defined behavior -/
theorem schemeStartState_triple_simple :
    Triple (schemeStartState : ParserM Unit)
      ⌜True⌝
      (PostCond.noThrow fun _ => ⌜True⌝) := by
  unfold schemeStartState
  mvcgen
  all_goals try grind
  all_goals sorry -- Complex state machine logic needs more specs

end LeanUrl.Parser.Spec
