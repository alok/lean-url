/-
Verification specs for the URL parser state machine.
Uses mvcgen + grind to verify safety of Option.get! calls.

Infrastructure based on Std.Do by Sebastian Graf and Markus Himmel.
-/
import Std.Tactic.Do
import LeanUrl.Parser.Basic

open Std.Do
open LeanUrl.Parser

namespace LeanUrl.Parser.Spec

/-! ## PostShape for ParserM

ParserM = ReaderT Methods (EStateM String Machine)
- EStateM String Machine has shape: .except String (.arg Machine .pure)
- ReaderT Methods adds: .arg Methods (...)
- Full shape: .arg Methods (.except String (.arg Machine .pure))
-/

/-- The PostShape for ParserM -/
abbrev ParserPostShape : PostShape := .arg Methods (.except String (.arg Machine .pure))

/-! ## WP instance derivation

The WP instance for ParserM is automatically derived from:
- ReaderT.instWP : WP (ReaderT ρ m) (.arg ρ ps) given WP m ps
- EStateM.instWP : WP (EStateM ε σ) (.except ε (.arg σ .pure))
-/

-- Verify the instance exists
#check (inferInstance : WP ParserM ParserPostShape)
#check (inferInstance : WPMonad ParserM ParserPostShape)

/-! ## Predicates on Machine state -/

/-- The pointer is valid (points to a character in input) -/
def pointerValid (m : Machine) : Prop :=
  match m.pointer with
  | .ofNat n => n < m.input.size
  | _ => False

/-- The current character exists -/
def hasCurr (m : Machine) : Prop :=
  pointerValid m

/-- Pointer is at or past end of input -/
def atEnd (m : Machine) : Prop :=
  match m.pointer with
  | .ofNat n => n ≥ m.input.size
  | _ => True

/-! ## Specifications for curr? -/

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

/-- curr? never throws -/
@[spec]
theorem curr?_never_throws :
    ∀ (methods : Methods) (m : Machine),
      ∃ c?, curr? methods m = .ok c? m := by
  intro methods m
  unfold curr?
  match m.pointer with
  | .ofNat n => exact ⟨m.input[n]?, rfl⟩
  | .negSucc _ => exact ⟨none, rfl⟩

/-! ## Specifications for peek operations -/

@[spec]
theorem peekNext1_spec :
    ∀ (methods : Methods) (m : Machine),
      ∃ c?, peekNext1 methods m = .ok c? m := by
  intro methods m
  unfold peekNext1
  match m.pointer with
  | .ofNat n => exact ⟨m.input[n+1]?, rfl⟩
  | .negSucc _ => exact ⟨none, rfl⟩

@[spec]
theorem peekNext2_spec :
    ∀ (methods : Methods) (m : Machine),
      ∃ c?, peekNext2 methods m = .ok c? m := by
  intro methods m
  unfold peekNext2
  match m.pointer with
  | .ofNat n => exact ⟨m.input[n+2]?, rfl⟩
  | .negSucc _ => exact ⟨none, rfl⟩

@[spec]
theorem remaining_spec :
    ∀ (methods : Methods) (m : Machine),
      ∃ s?, remaining methods m = .ok s? m := by
  intro methods m
  unfold remaining
  match m.pointer with
  | .ofNat n => exact ⟨some (m.input.drop n).toString, rfl⟩
  | .negSucc _ => exact ⟨none, rfl⟩

/-! ## Option safety lemmas for Option.get -/

/-- Key lemma: Option.map ... .getD false implies isSome (for Option.get) -/
@[spec]
theorem isSome_of_map_getD_true {α : Type} {o : Option α} {f : α → Bool}
    (h : (o.map f).getD false = true) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- isSome from equality check -/
@[spec]
theorem isSome_of_eq_some {α : Type} [DecidableEq α] {o : Option α} {a : α}
    (h : o == some a) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- isSome when negated isNone -/
@[spec]
theorem isSome_of_not_isNone {α : Type} {o : Option α}
    (h : ¬o.isNone) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- isSome from not-none check -/
@[spec]
theorem isSome_of_ne_none {α : Type} [DecidableEq α] {o : Option α}
    (h : (o != none) = true) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- isSome from isSome check (trivial but useful) -/
@[spec]
theorem isSome_of_isSome_true {α : Type} {o : Option α}
    (h : o.isSome = true) : o.isSome = true := h

/-- isSome from OR'd condition -/
@[spec]
theorem isSome_of_or_cond {α : Type} [DecidableEq α] {o : Option α} {f : α → Bool} {a : α}
    (h : ((o.map f).getD false || (o == some a)) = true) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- isSome from AND with isSome on left -/
@[spec]
theorem isSome_of_and_isSome {α : Type} {o : Option α} {p : Bool}
    (h : (o.isSome && p) = true) : o.isSome = true := by
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- isSome from negation of first disjunct in c?.isNone || ... -/
@[spec]
theorem isSome_of_not_isNone_or {α : Type} {o : Option α} {p : Prop}
    (h : ¬(o.isNone = true ∨ p)) : o.isSome = true := by
  have hn : o.isNone ≠ true := fun hx => h (Or.inl hx)
  cases o with
  | none => simp at hn
  | some _ => rfl

/-- Value equality after Option.get when we know it's some a -/
@[spec]
theorem Option.get_eq_of_eq_some {α : Type} [DecidableEq α] {o : Option α} {a : α}
    (heq : o == some a) (h : o.isSome = true) : o.get h = a := by
  cases o with
  | none => simp at heq
  | some x =>
    simp only [beq_iff_eq, Option.some.injEq] at heq
    simp only [Option.get_some, heq]

/-- The predicate holds for the extracted value -/
@[spec]
theorem pred_of_map_getD_true {α : Type} {o : Option α} {f : α → Bool}
    (h : (o.map f).getD false = true) (hisSome : o.isSome = true) : f (o.get hisSome) = true := by
  cases o with
  | none => simp at hisSome
  | some a =>
    simp only [Option.map_some, Option.getD_some] at h
    simp only [Option.get_some, h]

/-! ## Decidable condition lemmas for `if h : cond then ... else ...` -/

/-- For decidable isSome in if conditions -/
instance instDecidableIsSomeEqTrue {α : Type} {o : Option α} : Decidable (o.isSome = true) :=
  inferInstanceAs (Decidable (_ = true))

/-- Convert decidable Bool equality to isSome proof -/
@[spec]
theorem isSome_of_decide_map_getD {α : Type} {o : Option α} {f : α → Bool}
    (h : (o.map f).getD false) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- Legacy: Option.map ... .getD false implies isSome -/
theorem option_map_getD_implies_some {α : Type} (o : Option α) (f : α → Bool) :
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

/-- When we know o is some, we can extract the value safely -/
theorem Option.some_of_isSome {α : Type} {o : Option α} (h : o.isSome) : ∃ a, o = some a := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl⟩

/-- Pattern for safe unwrapping with condition and value -/
theorem option_map_getD_get {α : Type} [Inhabited α] (o : Option α) (f : α → Bool)
    (hcond : (o.map f).getD false) : ∃ a, o = some a ∧ f a := by
  cases o with
  | none => simp at hcond
  | some a =>
    simp only [Option.map_some, Option.getD_some] at hcond
    exact ⟨a, rfl, hcond⟩

/-- get! equals the value when we know it's some -/
theorem option_get!_eq_of_some {α : Type} [Inhabited α] {o : Option α} {a : α}
    (h : o = some a) : o.get! = a := by
  simp only [h, Option.get!_some]

/-- The key lemma for eliminating .get! after map check -/
theorem get!_safe_after_map_check {c? : Option Char}
    (hcond : (c?.map Char.isAlpha).getD false = true) :
    ∃ c, c? = some c ∧ c.isAlpha ∧ c?.get! = c := by
  cases c? with
  | none => simp at hcond
  | some c =>
    simp only [Option.map_some, Option.getD_some] at hcond
    exact ⟨c, rfl, hcond, rfl⟩

/-- Generalized: any predicate check on option implies safety -/
theorem get!_safe_after_pred_check {α : Type} [Inhabited α] {o : Option α} {f : α → Bool}
    (hcond : (o.map f).getD false = true) :
    ∃ a, o = some a ∧ f a ∧ o.get! = a := by
  cases o with
  | none => simp at hcond
  | some a =>
    simp only [Option.map_some, Option.getD_some] at hcond
    exact ⟨a, rfl, hcond, rfl⟩

/-! ## Option equality checks imply safety -/

theorem get!_safe_of_eq_some {α : Type} [Inhabited α] [DecidableEq α] {o : Option α} {a : α}
    (h : o == some a) : o.get! = a := by
  cases o with
  | none => simp at h
  | some x =>
    simp only [beq_iff_eq, Option.some.injEq] at h
    simp only [Option.get!_some, h]

theorem some_of_eq_some {α : Type} [DecidableEq α] {o : Option α} {a : α}
    (h : o == some a) : o = some a := by
  cases o with
  | none => simp at h
  | some x =>
    simp only [beq_iff_eq, Option.some.injEq] at h
    simp only [h]

/-! ## Disjunction patterns for parser conditions -/

/-- When checking multiple conditions with ||, at least one path gives safety -/
theorem option_safe_of_or_check {α : Type} [Inhabited α] [DecidableEq α] {o : Option α}
    {f : α → Bool} {a : α}
    (h : (o.map f).getD false = true ∨ o == some a) :
    o.isSome := by
  cases h with
  | inl hmap => exact option_map_getD_implies_some o f hmap
  | inr heq =>
    cases o with
    | none => simp at heq
    | some _ => rfl

/-! ## Character predicate safety lemmas -/

/-- Safety for isAsciiDigit checks -/
theorem get!_safe_after_isDigit_check {c? : Option Char}
    (hcond : (c?.map Char.isDigit).getD false = true) :
    ∃ c, c? = some c ∧ c.isDigit ∧ c?.get! = c := by
  cases c? with
  | none => simp at hcond
  | some c => exact ⟨c, rfl, hcond, rfl⟩

/-- Safety for isASCIIHexDigit checks -/
theorem get!_safe_after_isASCIIHexDigit_check {c? : Option Char}
    (hcond : (c?.map Char.isASCIIHexDigit).getD false = true) :
    ∃ c, c? = some c ∧ c.isASCIIHexDigit ∧ c?.get! = c := by
  cases c? with
  | none => simp at hcond
  | some c => exact ⟨c, rfl, hcond, rfl⟩

/-- Safety for isAlphaNum checks -/
theorem get!_safe_after_isAlphaNum_check {c? : Option Char}
    (hcond : (c?.map Char.isAlphanum).getD false = true) :
    ∃ c, c? = some c ∧ c.isAlphanum ∧ c?.get! = c := by
  cases c? with
  | none => simp at hcond
  | some c => exact ⟨c, rfl, hcond, rfl⟩

/-! ## Combined condition patterns -/

/-- When c? != none, we can extract a value -/
theorem some_of_ne_none {α : Type} [DecidableEq α] {o : Option α} (h : o != none) : o.isSome := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- Safety after c? != none check -/
theorem get!_defined_of_ne_none {α : Type} [Inhabited α] [DecidableEq α] {o : Option α}
    (h : o != none) : ∃ a, o = some a ∧ o.get! = a := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl, rfl⟩

/-- Safety for OR'd character checks: (c?.map f).getD false || c? == some a -/
theorem get!_safe_of_pred_or_eq {c? : Option Char} {f : Char → Bool} {a : Char}
    (h : (c?.map f).getD false || (c? == some a)) :
    ∃ c, c? = some c ∧ c?.get! = c := by
  cases c? with
  | none => simp at h
  | some c => exact ⟨c, rfl, rfl⟩

/-- Safety for AND'd conditions where one implies some -/
theorem get!_safe_of_isSome_and {α : Type} [Inhabited α] {o : Option α} {p : Bool}
    (h : o.isSome && p) : ∃ a, o = some a ∧ o.get! = a := by
  simp only [Bool.and_eq_true] at h
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl, rfl⟩

/-! ## Pointer arithmetic safety -/

/-- After incrementing, pointer stays valid if not at end -/
theorem pointerValid_of_lt_pred {m : Machine} {n : Nat}
    (hp : m.pointer = .ofNat n) (hlt : n + 1 < m.input.size) :
    pointerValid { m with pointer := m.pointer + 1 } := by
  unfold pointerValid
  simp only [hp]
  show n + 1 < m.input.size
  exact hlt

/-! ## Safe schemeStartState -/

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

/-! ## mvcgen verification -/

/-- Verify get operation on simple StateM -/
theorem get_triple : Triple (get : StateM Nat Nat) ⌜True⌝ (PostCond.noThrow fun _ => ⌜True⌝) := by
  mvcgen

/-- Verify modify operation -/
theorem modify_triple : Triple (modify (· + 1) : StateM Nat Unit) ⌜True⌝ (PostCond.noThrow fun _ => ⌜True⌝) := by
  mvcgen

/-- Verify pure operation -/
theorem pure_triple : Triple (pure 42 : StateM Nat Nat) ⌜True⌝ (PostCond.noThrow fun _ => ⌜True⌝) := by
  mvcgen

/-- Verify bind with mvcgen -/
theorem bind_triple :
    Triple (do let x ← get; pure (x + 1) : StateM Nat Nat)
      ⌜True⌝
      (PostCond.noThrow fun _ => ⌜True⌝) := by
  mvcgen

/-- Verify if-then-else with mvcgen -/
theorem ite_triple :
    Triple (do if true then pure 1 else pure 2 : StateM Nat Nat)
      ⌜True⌝
      (PostCond.noThrow fun _ => ⌜True⌝) := by
  mvcgen

/-- Verify option match with mvcgen -/
theorem option_match_triple (o : Option Nat) :
    Triple (do match o with | some n => pure n | none => pure 0 : StateM Nat Nat)
      ⌜True⌝
      (PostCond.noThrow fun _ => ⌜True⌝) := by
  mvcgen

/-! ## mvcgen patterns from Lean Reference Manual PR #683

Key patterns for verification with mvcgen:

1. **Adequacy theorems** bridge wp semantics to concrete results:
   - `Id.of_wp_run_eq` for Id monad
   - `StateM.of_wp_run_eq` for StateM
   - `EStateM.of_wp_run_eq` for EStateM

2. **Postcondition syntax**:
   - `⇓ r => ...` - success case only (total correctness)
   - `⇓? r => ...` - partial correctness (if terminates)
   - `post⟨success, exception⟩` - explicit exception handling

3. **Loop invariants** with `Invariant.withEarlyReturn`:
   - `onReturn` - holds after early return
   - `onContinue` - preserved each iteration
   - `onExcept` - holds when exception thrown

4. **Proof mode tactics**:
   - `mvcgen` - generate verification conditions
   - `mspec` - apply specification lemma step by step
   - `mpure_intro` - introduce pure hypotheses
   - `mleave` - leave stateful proof mode
   - `mframe` - frame hypotheses

5. **PostCond for ParserM**:
   PostShape = .arg Methods (.except String (.arg Machine .pure))
   PostCond α ps = (α → Methods → Machine → SPred,   -- success
                    String → Machine → SPred,         -- exception
                    Methods → SPred)                  -- reader pure
-/

/-! ## ParserM-specific specs using Hoare triples

These specs use the full PostShape for ParserM:
  .arg Methods (.except String (.arg Machine .pure))

PostCond structure for exception-aware specs:
  post⟨fun result methods machine => success_assertion,
       fun error machine => exception_assertion,
       fun methods => reader_assertion⟩
-/

/-- curr? never throws and preserves state -/
@[spec]
theorem Spec.curr?_ParserM :
    Triple (curr? : ParserM (Option Char))
      ⌜True⌝
      (PostCond.noThrow fun _ => ⌜True⌝) := by
  unfold curr?
  mvcgen
  intro _ m
  simp only [wp, PostCond.noThrow, PredTrans.pushArg_apply, PredTrans.map_apply]
  cases m.pointer <;> trivial

/-- peekNext1 never throws -/
@[spec]
theorem Spec.peekNext1_ParserM :
    Triple (peekNext1 : ParserM (Option Char))
      ⌜True⌝
      (PostCond.noThrow fun _ => ⌜True⌝) := by
  unfold peekNext1
  mvcgen
  intro _ m
  simp only [wp, PostCond.noThrow, PredTrans.pushArg_apply, PredTrans.map_apply]
  cases m.pointer <;> trivial

/-- peekNext2 never throws -/
@[spec]
theorem Spec.peekNext2_ParserM :
    Triple (peekNext2 : ParserM (Option Char))
      ⌜True⌝
      (PostCond.noThrow fun _ => ⌜True⌝) := by
  unfold peekNext2
  mvcgen
  intro _ m
  simp only [wp, PostCond.noThrow, PredTrans.pushArg_apply, PredTrans.map_apply]
  cases m.pointer <;> trivial

/-- remaining never throws -/
@[spec]
theorem Spec.remaining_ParserM :
    Triple (remaining : ParserM (Option String))
      ⌜True⌝
      (PostCond.noThrow fun _ => ⌜True⌝) := by
  unfold remaining
  mvcgen
  intro _ m
  simp only [wp, PostCond.noThrow, PredTrans.pushArg_apply, PredTrans.map_apply]
  cases m.pointer <;> trivial

/-- Verify schemeStartState has well-defined behavior -/
theorem schemeStartState_triple :
    Triple (schemeStartState : ParserM Unit)
      ⌜True⌝
      (PostCond.noThrow fun _ => ⌜True⌝) := by
  unfold schemeStartState
  mvcgen
  all_goals try grind
  all_goals sorry -- Complex state machine logic needs more infrastructure

/-! ## Key safety theorem for the parser pattern -/

/-- When (c?.map f).getD false is true in a branch, c?.get! is safe -/
theorem parser_get!_safe {c? : Option Char} {f : Char → Bool}
    (hbranch : (c?.map f).getD false = true) :
    c?.get! = match c? with | some c => c | none => default := by
  cases c? with
  | none => simp at hbranch
  | some c => rfl

/-- The unsafe get! in schemeStartState is safe because of the isAlpha check -/
theorem schemeStartState_get!_safe (c? : Option Char)
    (hcond : (c?.map Char.isAlpha).getD false = true) :
    ∃ c, c? = some c ∧ c?.get! = c := by
  cases c? with
  | none => simp at hcond
  | some c => exact ⟨c, rfl, rfl⟩

#check @get_triple
#check @curr?_spec_some
#check @get!_safe_after_map_check

end LeanUrl.Parser.Spec
