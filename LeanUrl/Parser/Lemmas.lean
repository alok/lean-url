import LeanUrl.Parser.Basic
import Canonical

/-!
# Ultra-Granular ParserM Lemmas

This file breaks down every monadic operation into its smallest provable pieces.
The goal is to make each lemma trivial enough that standard tactics can handle it.

## Strategy: "Ridiculous level of modularization"

Each monadic operation is decomposed into:
1. Result type lemma (what constructor does it return?)
2. Value lemma (what's the returned value?)
3. State lemma (what's the output state?)
4. Composition lemmas (how do they combine via bind?)
-/

namespace LeanUrl.Parser

open EStateM

/-! ## Level 1: ParserM Basic Operations -/

section ParserMBasics

/-- get in ParserM returns current machine -/
@[simp] theorem get_ParserM (methods : Methods) (m : Machine) :
    (get : ParserM Machine) methods m = .ok m m := rfl

/-- pure in ParserM returns value with unchanged state -/
@[simp] theorem pure_ParserM {α : Type} (a : α) (methods : Methods) (m : Machine) :
    (pure a : ParserM α) methods m = .ok a m := rfl

/-- modify in ParserM applies function to state -/
@[simp] theorem modify_ParserM (f : Machine → Machine) (methods : Methods) (m : Machine) :
    (modify f : ParserM Unit) methods m = .ok () (f m) := rfl

/-- throw in ParserM returns error -/
@[simp] theorem throw_ParserM {α : Type} (e : String) (methods : Methods) (m : Machine) :
    (throw e : ParserM α) methods m = .error e m := rfl

end ParserMBasics

/-! ## Level 2: curr? Decomposition -/

section Curr

/-- curr? with ofNat pointer: value is input[n]? -/
@[simp] theorem curr?_value_ofNat (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n) :
    curr? methods m = .ok (m.input[n]?) m := by
  unfold curr?
  simp only [hp]

/-- curr? with ofNat pointer: state is unchanged -/
theorem curr?_state_ofNat (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (v : Option Char) (m' : Machine) (h : curr? methods m = .ok v m') :
    m' = m := by
  rw [curr?_value_ofNat methods m n hp] at h
  injection h with _ hm
  exact hm.symm

/-- curr? with negative pointer: returns none -/
@[simp] theorem curr?_neg_pointer (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .negSucc n) :
    curr? methods m = .ok none m := by
  unfold curr?
  simp only [hp]

/-- curr? returning specific none -/
theorem curr?_returns_none (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n) (hc : m.input[n]? = none) :
    curr? methods m = .ok none m := by
  simp only [curr?_value_ofNat methods m n hp, hc]

/-- curr? returning some char -/
theorem curr?_returns_some (methods : Methods) (m : Machine) (n : Nat) (c : Char)
    (hp : m.pointer = .ofNat n) (hc : m.input[n]? = some c) :
    curr? methods m = .ok (some c) m := by
  simp only [curr?_value_ofNat methods m n hp, hc]

end Curr

/-! ## Level 3: Bind Composition -/

section BindComposition

variable {α β : Type}

/-- Full bind composition: ok >>= ok → ok -/
theorem bind_ok_ok (x : ParserM α) (f : α → ParserM β) (methods : Methods) (m m' m'' : Machine)
    (a : α) (b : β)
    (hx : x methods m = .ok a m')
    (hf : f a methods m' = .ok b m'') :
    (x >>= f) methods m = .ok b m'' := by
  simp only [bind, ReaderT.bind, EStateM.bind, hx, hf]

/-- Full bind composition: ok >>= error → error -/
theorem bind_ok_error (x : ParserM α) (f : α → ParserM β) (methods : Methods) (m m' m'' : Machine)
    (a : α) (e : String)
    (hx : x methods m = .ok a m')
    (hf : f a methods m' = .error e m'') :
    (x >>= f) methods m = .error e m'' := by
  simp only [bind, ReaderT.bind, EStateM.bind, hx, hf]

/-- Full bind composition: error >>= _ → error -/
theorem bind_error_any (x : ParserM α) (f : α → ParserM β) (methods : Methods) (m : Machine)
    (e : String) (m' : Machine)
    (hx : x methods m = .error e m') :
    (x >>= f) methods m = .error e m' := by
  simp only [bind, ReaderT.bind, EStateM.bind, hx]

end BindComposition

/-! ## Level 4: Hypothesis Conversion -/

section HypothesisConversion

/-- Convert pointer hypothesis for array indexing -/
theorem pointer_toNat_eq (m : Machine) (n : Nat) (hp : m.pointer = .ofNat n) :
    m.pointer.toNat = n := by
  simp only [hp, Int.toNat.eq_1]

/-- Convert input hypothesis through pointer -/
theorem input_at_pointer_eq (m : Machine) (n : Nat) (hp : m.pointer = .ofNat n) :
    m.input[m.pointer.toNat]? = m.input[n]? := by
  simp only [pointer_toNat_eq m n hp]

/-- Option.isSome true implies value exists -/
theorem isSome_implies_exists {α : Type} (o : Option α) (h : o.isSome = true) :
    ∃ a, o = some a := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl⟩

/-- Option.isNone true implies value is none -/
theorem isNone_implies_eq_none {α : Type} (o : Option α) (h : o.isNone = true) :
    o = none := by
  cases o with
  | none => rfl
  | some a => simp at h

end HypothesisConversion

/-! ## Level 5: Control Flow -/

section ControlFlow

/-- Pure if-then-else with true condition -/
theorem ite_apply_true {α : Type} {P : Prop} [Decidable P] (hP : P)
    (t e : ParserM α) (methods : Methods) (m : Machine) :
    (if P then t else e) methods m = t methods m := by simp [hP]

/-- Pure if-then-else with false condition -/
theorem ite_apply_false {α : Type} {P : Prop} [Decidable P] (hP : ¬P)
    (t e : ParserM α) (methods : Methods) (m : Machine) :
    (if P then t else e) methods m = e methods m := by simp [hP]

/-- Dependent if-then-else with true condition -/
theorem dite_apply_true {α : Type} {P : Prop} [Decidable P] (hP : P)
    (t : P → ParserM α) (e : ¬P → ParserM α) (methods : Methods) (m : Machine) :
    (if h : P then t h else e h) methods m = t hP methods m := by simp [hP]

/-- Dependent if-then-else with false condition -/
theorem dite_apply_false {α : Type} {P : Prop} [Decidable P] (hP : ¬P)
    (t : P → ParserM α) (e : ¬P → ParserM α) (methods : Methods) (m : Machine) :
    (if h : P then t h else e h) methods m = e hP methods m := by simp [hP]

end ControlFlow

/-! ## Level 6: Multi-Step Composition -/

section MultiStepComposition

variable {α β γ : Type}

/-- Two-step composition -/
theorem two_step_ok (x : ParserM α) (y : ParserM β)
    (methods : Methods) (m m₁ m₂ : Machine) (a : α) (b : β)
    (hx : x methods m = .ok a m₁)
    (hy : y methods m₁ = .ok b m₂) :
    (x >>= fun _ => y) methods m = .ok b m₂ := by
  simp only [bind, ReaderT.bind, EStateM.bind, hx, hy]

/-- Three-step composition -/
theorem three_step_ok (x : ParserM α) (y : ParserM β) (z : ParserM γ)
    (methods : Methods) (m m₁ m₂ m₃ : Machine) (a : α) (b : β) (c : γ)
    (hx : x methods m = .ok a m₁)
    (hy : y methods m₁ = .ok b m₂)
    (hz : z methods m₂ = .ok c m₃) :
    (x >>= fun _ => y >>= fun _ => z) methods m = .ok c m₃ := by
  simp only [bind, ReaderT.bind, EStateM.bind, hx, hy, hz]

/-- get-then-conditional pattern (true) -/
theorem get_then_cond_true {α : Type} (P : Machine → Prop) [DecidablePred P]
    (t e : ParserM α) (methods : Methods) (m : Machine)
    (hP : P m) :
    (do let m' ← get; if P m' then t else e) methods m = t methods m := by
  simp only [bind, ReaderT.bind, EStateM.bind, get_ParserM, hP, ↓reduceIte]

/-- get-then-conditional pattern (false) -/
theorem get_then_cond_false {α : Type} (P : Machine → Prop) [DecidablePred P]
    (t e : ParserM α) (methods : Methods) (m : Machine)
    (hP : ¬P m) :
    (do let m' ← get; if P m' then t else e) methods m = e methods m := by
  simp only [bind, ReaderT.bind, EStateM.bind, get_ParserM, hP, ↓reduceIte]

end MultiStepComposition

/-! ## Level 7: State Field Extraction -/

section StateFields

/-- After modify, extract state field -/
theorem modify_state_eq (methods : Methods) (m : Machine)
    (f : Machine → Machine) :
    match (modify f : ParserM Unit) methods m with
    | .ok () m' => m'.state = (f m).state
    | .error _ _ => True := by
  simp only [modify_ParserM]

/-- After modify, extract buffer field -/
theorem modify_buffer_eq (methods : Methods) (m : Machine)
    (f : Machine → Machine) :
    match (modify f : ParserM Unit) methods m with
    | .ok () m' => m'.buffer = (f m).buffer
    | .error _ _ => True := by
  simp only [modify_ParserM]

/-- After modify, extract pointer field -/
theorem modify_pointer_eq (methods : Methods) (m : Machine)
    (f : Machine → Machine) :
    match (modify f : ParserM Unit) methods m with
    | .ok () m' => m'.pointer = (f m).pointer
    | .error _ _ => True := by
  simp only [modify_ParserM]

end StateFields

/-! ## Level 8: Port State Specific -/

section PortStateSpecific

/-- The port terminator condition -/
def isPortTermCond (c? : Option Char) (isSpecial : Bool) (hasOverride : Bool) : Bool :=
  c?.isNone || c? == some '/' || c? == some '?' || c? == some '#'
    || (isSpecial && c? == some '\\')
    || hasOverride

/-- Port terminator condition: none is terminator -/
@[simp] theorem isPortTermCond_none (isSpecial hasOverride : Bool) :
    isPortTermCond none isSpecial hasOverride = true := by
  unfold isPortTermCond
  simp

/-- Port terminator condition: slash is terminator -/
@[simp] theorem isPortTermCond_slash (isSpecial hasOverride : Bool) :
    isPortTermCond (some '/') isSpecial hasOverride = true := by
  unfold isPortTermCond
  simp

/-- Port terminator condition: question is terminator -/
@[simp] theorem isPortTermCond_question (isSpecial hasOverride : Bool) :
    isPortTermCond (some '?') isSpecial hasOverride = true := by
  unfold isPortTermCond
  simp

/-- Port terminator condition: hash is terminator -/
@[simp] theorem isPortTermCond_hash (isSpecial hasOverride : Bool) :
    isPortTermCond (some '#') isSpecial hasOverride = true := by
  unfold isPortTermCond
  simp

/-- Port terminator condition: backslash is terminator when special -/
@[simp] theorem isPortTermCond_backslash_special (hasOverride : Bool) :
    isPortTermCond (some '\\') true hasOverride = true := by
  unfold isPortTermCond
  simp

/-- Port terminator condition: hasOverride makes it terminator -/
@[simp] theorem isPortTermCond_override (c? : Option Char) (isSpecial : Bool) :
    isPortTermCond c? isSpecial true = true := by
  unfold isPortTermCond
  simp

/-- Port parsing helper -/
def parsePortHelper (buf : String) : Option UInt16 :=
  buf.toNat?.bind fun x => if x < UInt16.size then some (UInt16.ofNat x) else none

/-- Port parsing: valid port -/
theorem parsePortHelper_valid (buf : String) (n : Nat) (hn : n < UInt16.size)
    (hbuf : buf.toNat? = some n) :
    parsePortHelper buf = some (UInt16.ofNat n) := by
  unfold parsePortHelper
  simp [hbuf, hn]

/-- Port parsing: too large -/
theorem parsePortHelper_toolarge (buf : String) (n : Nat) (hn : ¬(n < UInt16.size))
    (hbuf : buf.toNat? = some n) :
    parsePortHelper buf = none := by
  unfold parsePortHelper
  simp [hbuf, hn]

/-- Port parsing: not a number -/
theorem parsePortHelper_notNumber (buf : String) (hbuf : buf.toNat? = none) :
    parsePortHelper buf = none := by
  unfold parsePortHelper
  simp [hbuf]

end PortStateSpecific

/-! ## Level 9: Result Matching -/

section ResultMatching

/-- Match on ok result extracts value -/
theorem match_ok_extract {α β : Type} (a : α) (s : Machine)
    (f : α → Machine → β) (g : String → Machine → β) :
    (match EStateM.Result.ok a s with
     | .ok a' s' => f a' s'
     | .error e s' => g e s') = f a s := rfl

/-- Match on error result extracts error -/
theorem match_error_extract {α β : Type} (e : String) (s : Machine)
    (f : α → Machine → β) (g : String → Machine → β) :
    (match EStateM.Result.error e s with
     | .ok a' s' => f a' s'
     | .error e' s' => g e' s') = g e s := rfl

/-- Result ok injection -/
theorem ok_injective {α : Type} (a a' : α) (s s' : Machine)
    (h : (EStateM.Result.ok a s : Result String Machine α) = EStateM.Result.ok a' s') :
    a = a' ∧ s = s' := by
  injection h with ha hs
  exact ⟨ha, hs⟩

/-- Result error injection -/
theorem error_injective {α : Type} (e e' : String) (s s' : Machine)
    (h : (EStateM.Result.error e s : Result String Machine α) = EStateM.Result.error e' s') :
    e = e' ∧ s = s' := by
  injection h with he hs
  exact ⟨he, hs⟩

end ResultMatching

/-! ## Level 10: Character Predicates -/

section CharPredicates

/-- Slash is not a digit -/
theorem slash_not_digit : '/'.isDigit = false := by native_decide

/-- Question is not a digit -/
theorem question_not_digit : '?'.isDigit = false := by native_decide

/-- Hash is not a digit -/
theorem hash_not_digit : '#'.isDigit = false := by native_decide

/-- Backslash is not a digit -/
theorem backslash_not_digit : '\\'.isDigit = false := by native_decide

/-- Zero is a digit -/
theorem zero_is_digit : '0'.isDigit = true := by native_decide

/-- Nine is a digit -/
theorem nine_is_digit : '9'.isDigit = true := by native_decide

end CharPredicates

/-! ## Level 11: portState Path Lemmas -/

section PortStatePaths

/-- portState with digit: returns early after pushing to buffer -/
theorem portState_digit_path (methods : Methods) (m : Machine) (n : Nat) (c : Char)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some c)
    (hDigit : c.isDigit = true) :
    portState methods m = .ok () { m with buffer := m.buffer.push c } := by
  unfold portState
  simp only [bind, ReaderT.bind, EStateM.bind]
  have hcurr : curr? methods m = .ok (some c) m := curr?_returns_some methods m n c hp hc
  rw [hcurr]
  simp only [Option.isSome_some, dite_true, Option.get_some, hDigit, ↓reduceIte]
  -- After the digit branch with return, we have:
  -- modify (push c) >>= fun _ => pure ()
  simp only [bind, ReaderT.bind, EStateM.bind, modify_ParserM, pure, ReaderT.pure, EStateM.pure]

/-- portState with none and empty buffer and no override: transitions to pathStart -/
theorem portState_none_emptyBuf_path (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = none)
    (hbuf : m.buffer = "")
    (hso : m.stateOverride = none) :
    portState methods m = .ok () { m with state := .pathStart, pointer := m.pointer - 1 } := by
  unfold portState
  simp only [bind, ReaderT.bind, EStateM.bind]
  have hcurr : curr? methods m = .ok none m := curr?_returns_none methods m n hp hc
  rw [hcurr]
  simp only [Option.isSome_none, dif_neg (Bool.false_ne_true)]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  rw [hget]; simp only []
  rw [hget]; simp only []
  simp only [Option.isNone_none, Bool.true_or, if_true]
  simp only [bind, ReaderT.bind, EStateM.bind]
  rw [hget]; simp only []
  simp only [hbuf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  rw [hget]; simp only []
  simp only [hso, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  simp only [modify_ParserM]
  simp only [hbuf, hso]

/-- portState with slash and empty buffer and no override: transitions to pathStart -/
theorem portState_slash_emptyBuf_path (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '/')
    (hbuf : m.buffer = "")
    (hso : m.stateOverride = none) :
    portState methods m = .ok () { m with state := .pathStart, pointer := m.pointer - 1 } := by
  unfold portState
  simp only [bind, ReaderT.bind, EStateM.bind]
  have hcurr : curr? methods m = .ok (some '/') m := curr?_returns_some methods m n '/' hp hc
  rw [hcurr]
  simp only [Option.isSome_some, dite_true, Option.get_some]
  simp only [slash_not_digit, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  rw [hget]; simp only []
  rw [hget]; simp only []
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, Bool.true_or, if_true]
  simp only [bind, ReaderT.bind, EStateM.bind]
  rw [hget]; simp only []
  simp only [hbuf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  rw [hget]; simp only []
  simp only [hso, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  simp only [modify_ParserM]
  simp only [hbuf, hso]

/-- portState with question and empty buffer and no override: transitions to pathStart -/
theorem portState_question_emptyBuf_path (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '?')
    (hbuf : m.buffer = "")
    (hso : m.stateOverride = none) :
    portState methods m = .ok () { m with state := .pathStart, pointer := m.pointer - 1 } := by
  unfold portState
  simp only [bind, ReaderT.bind, EStateM.bind]
  have hcurr : curr? methods m = .ok (some '?') m := curr?_returns_some methods m n '?' hp hc
  rw [hcurr]
  simp only [Option.isSome_some, dite_true, Option.get_some]
  simp only [question_not_digit, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  rw [hget]; simp only []
  rw [hget]; simp only []
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, Bool.or_true, Bool.true_or, if_true]
  simp only [bind, ReaderT.bind, EStateM.bind]
  rw [hget]; simp only []
  simp only [hbuf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  rw [hget]; simp only []
  simp only [hso, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  simp only [modify_ParserM]
  simp only [hbuf, hso]

/-- portState with hash and empty buffer and no override: transitions to pathStart -/
theorem portState_hash_emptyBuf_path (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '#')
    (hbuf : m.buffer = "")
    (hso : m.stateOverride = none) :
    portState methods m = .ok () { m with state := .pathStart, pointer := m.pointer - 1 } := by
  unfold portState
  simp only [bind, ReaderT.bind, EStateM.bind]
  have hcurr : curr? methods m = .ok (some '#') m := curr?_returns_some methods m n '#' hp hc
  rw [hcurr]
  simp only [Option.isSome_some, dite_true, Option.get_some]
  simp only [hash_not_digit, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  rw [hget]; simp only []
  rw [hget]; simp only []
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, Bool.or_true, Bool.true_or, if_true]
  simp only [bind, ReaderT.bind, EStateM.bind]
  rw [hget]; simp only []
  simp only [hbuf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  rw [hget]; simp only []
  simp only [hso, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  simp only [modify_ParserM]
  simp only [hbuf, hso]

/-- portState with backslash, special URL, empty buffer and no override: transitions to pathStart -/
theorem portState_backslash_special_emptyBuf_path (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '\\')
    (hSpecial : m.url.isSpecial = true)
    (hbuf : m.buffer = "")
    (hso : m.stateOverride = none) :
    portState methods m = .ok () { m with state := .pathStart, pointer := m.pointer - 1 } := by
  unfold portState
  simp only [bind, ReaderT.bind, EStateM.bind]
  have hcurr : curr? methods m = .ok (some '\\') m := curr?_returns_some methods m n '\\' hp hc
  rw [hcurr]
  simp only [Option.isSome_some, dite_true, Option.get_some]
  simp only [backslash_not_digit, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  rw [hget]; simp only []
  rw [hget]; simp only []
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, hSpecial, Bool.true_and,
             Bool.or_true, Bool.true_or, if_true]
  simp only [bind, ReaderT.bind, EStateM.bind]
  rw [hget]; simp only []
  simp only [hbuf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  rw [hget]; simp only []
  simp only [hso, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  simp only [modify_ParserM]
  simp only [hbuf, hso]

/-- portState with terminator, empty buffer, and stateOverride throws -/
theorem portState_term_emptyBuf_override_throws (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = none)
    (hbuf : m.buffer = "")
    (hso : ∃ so, m.stateOverride = some so) :
    ∃ e m', portState methods m = .error e m' := by
  obtain ⟨so, hso⟩ := hso
  unfold portState
  simp only [bind, ReaderT.bind, EStateM.bind]
  have hcurr : curr? methods m = .ok none m := curr?_returns_none methods m n hp hc
  rw [hcurr]
  simp only [Option.isSome_none, dif_neg (Bool.false_ne_true)]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  rw [hget]; simp only []
  rw [hget]; simp only []
  simp only [Option.isNone_none, Bool.true_or, if_true]
  simp only [bind, ReaderT.bind, EStateM.bind]
  rw [hget]; simp only []
  simp only [hbuf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  rw [hget]; simp only []
  simp only [hso, Option.isSome_some, ↓reduceIte]
  exact ⟨_, _, rfl⟩

end PortStatePaths

/-! ## Level 12: portState Non-Empty Buffer Lemmas -/

section PortStateNonEmptyBuffer

/-- Helper: parse port from buffer -/
def portParsing (buf : String) : Option UInt16 :=
  buf.toNat?.bind fun x => if x < UInt16.size then some (UInt16.ofNat x) else none

/-- Port parsing returns some when buffer is valid port -/
theorem portParsing_some (buf : String) (n : Nat) (hn : n < UInt16.size)
    (hbuf : buf.toNat? = some n) :
    portParsing buf = some (UInt16.ofNat n) := by
  unfold portParsing
  simp [hbuf, hn]

/-- Port parsing returns none when buffer is not a number -/
theorem portParsing_none_notNumber (buf : String) (hbuf : buf.toNat? = none) :
    portParsing buf = none := by
  unfold portParsing
  simp [hbuf]

/-- Port parsing returns none when number is too large -/
theorem portParsing_none_toolarge (buf : String) (n : Nat) (hn : ¬n < UInt16.size)
    (hbuf : buf.toNat? = some n) :
    portParsing buf = none := by
  unfold portParsing
  simp [hbuf, hn]

/-- When portState succeeds via EOF terminator path with nonempty buffer and no override,
    the output state is pathStart.

    Key insight: With hbuf (buffer ≠ "") and hso (stateOverride = none) and hc (EOF),
    the only success path is:
    1. Enter terminator branch (EOF makes c?.isNone true)
    2. Enter buffer ≠ "" branch (hbuf)
    3. Port parsing succeeds (REQUIRED for .ok - if parsing fails, we get .error not .ok)
    4. Execute two modifies (set port, clear buffer)
    5. Skip early return (stateOverride.isNone)
    6. Skip throw (stateOverride.isNone)
    7. Execute final modify setting state := pathStart

    Note: hValid is required because the port parsing MUST succeed for hr to be .ok.
    If the buffer doesn't parse to a valid port, portState would return .error.
-/
theorem portState_eof_nonEmptyBuf_noOverride_success_pathStart
    (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = none)  -- EOF terminator case
    (hbuf : m.buffer ≠ "")
    (hso : m.stateOverride = none)
    (hValid : ∃ portVal : Nat, m.buffer.toNat? = some portVal ∧ portVal < UInt16.size)
    (m' : Machine) (hr : portState methods m = .ok () m') :
    m'.state = .pathStart := by
  obtain ⟨portVal, hport, hsize⟩ := hValid
  unfold portState at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  have hcurr : curr? methods m = .ok none m := by
    unfold curr?
    simp only [hp, hc]
  rw [hcurr] at hr
  simp only [Option.isSome_none, dif_neg (Bool.false_ne_true)] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  simp only [hget] at hr
  simp only [Option.isNone_none, Bool.true_or, if_true] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [hget] at hr
  -- Buffer check: buffer ≠ ""
  -- Need to show that m.buffer != "" evaluates to true
  have hbuf' : (m.buffer != "") = true := by
    simp only [bne_iff_ne, ne_eq, hbuf, not_false_eq_true]
  simp only [hbuf', ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [hget] at hr
  -- Port parsing: we know it succeeds from hValid
  simp only [hport, Option.bind_some, hsize, ↓reduceIte] at hr
  -- Now we have match some port_ with | some port_ => ... | none => ...
  -- Continue with the some branch
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  -- First modify: set url.port
  simp only [modify_ParserM] at hr
  -- There's NO second modify here yet - the buffer clear comes AFTER the modify for port
  -- The structure is: modify url.port >>= modify buffer := "" >>= get >>= if stateOverride.isSome then return else ...

  -- The state we're in after first modify preserves stateOverride from m
  -- So when we do the get and check stateOverride, it's still none

  -- Clear bind structure and reduce the get in the match
  simp only [get_ParserM] at hr
  -- The stateOverride in the modified state is still m.stateOverride which is none
  simp only [hso, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  -- Now we're in the else branch
  simp only [get_ParserM] at hr
  -- Again check stateOverride (for the throw check)
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  -- Final modify: set state := pathStart
  simp only [modify_ParserM] at hr
  -- Extract the result
  cases hr
  rfl

/-- If portState succeeds with non-empty buffer and terminator input,
    then the buffer must have parsed to a valid port.

    This is the "inversion" lemma: success of portState implies port parsing succeeded.
-/
theorem portState_success_implies_valid_port
    (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = none)  -- EOF terminator
    (hbuf : m.buffer ≠ "")
    (m' : Machine) (hr : portState methods m = .ok () m') :
    ∃ portVal : Nat, m.buffer.toNat? = some portVal ∧ portVal < UInt16.size := by
  -- By contrapositive: if port parsing fails, portState returns .error
  -- Since hr says it returned .ok, port parsing must have succeeded
  unfold portState at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  have hcurr : curr? methods m = .ok none m := by
    unfold curr?
    simp only [hp, hc]
  rw [hcurr] at hr
  simp only [Option.isSome_none, dif_neg (Bool.false_ne_true)] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  simp only [hget] at hr
  simp only [Option.isNone_none, Bool.true_or, if_true] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [hget] at hr
  -- Buffer check
  have hbuf' : (m.buffer != "") = true := by simp only [bne_iff_ne, ne_eq, hbuf, not_false_eq_true]
  simp only [hbuf', ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [hget] at hr
  -- Now we're at the port parsing step
  -- If m.buffer.toNat? = none, we get match none with | none => throw ..., which is .error
  -- So for hr to be .ok, we need m.buffer.toNat? = some portVal
  cases hparse : m.buffer.toNat? with
  | none =>
    -- Contradiction: this would lead to .error, not .ok
    simp only [hparse, Option.bind_none] at hr
    cases hr  -- hr : .error = .ok → contradiction
  | some portVal =>
    -- Now check if portVal < UInt16.size
    by_cases hsize : portVal < UInt16.size
    · exact ⟨portVal, rfl, hsize⟩
    · -- portVal >= UInt16.size → parsing returns none → match none → throw → .error
      simp only [hparse, Option.bind_some, hsize, ↓reduceIte] at hr
      cases hr  -- hr : .error = .ok → contradiction

end PortStateNonEmptyBuffer

/-! ## Level 13: Inverse Derivation Lemmas -/

section InverseLemmas

/-- When portState succeeds via EOF terminator with nonempty buffer and no override,
    state becomes pathStart.

    This version doesn't require hValid - it derives validity from hr using inversion.
-/
theorem portState_eof_nonEmptyBuf_noOverride_pathStart_noValid
    (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = none)  -- EOF terminator
    (hbuf : m.buffer ≠ "")
    (hso : m.stateOverride = none)
    (m' : Machine) (hr : portState methods m = .ok () m') :
    m'.state = .pathStart := by
  -- First derive that port parsing succeeded
  have hValid := portState_success_implies_valid_port methods m n hp hc hbuf m' hr
  -- Now use the explicit lemma
  exact portState_eof_nonEmptyBuf_noOverride_success_pathStart methods m n hp hc hbuf hso hValid m' hr

/-- Derive port validity from success with slash terminator and nonempty buffer. -/
theorem portState_slash_success_implies_valid_port
    (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '/')
    (hbuf : m.buffer ≠ "")
    (m' : Machine) (hr : portState methods m = .ok () m') :
    ∃ portVal : Nat, m.buffer.toNat? = some portVal ∧ portVal < UInt16.size := by
  -- Similar derivation as EOF case - the port parsing must succeed for hr to be .ok
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  -- Trace through portState execution to the port parsing step
  unfold portState at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  have h_curr : curr? methods m = .ok (some '/') m := by
    unfold curr?
    simp only [hp, hc]
  simp only [h_curr] at hr
  simp only [Option.isSome_some, dite_true, Option.get_some] at hr
  have hNotDigit : '/'.isDigit = false := by native_decide
  simp only [hNotDigit, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [hget, get_ParserM] at hr
  -- Check terminator condition for /
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, Bool.true_or] at hr
  simp only [if_true] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [hget] at hr
  -- Now at buffer check
  have hbuf' : (m.buffer != "") = true := by simp only [bne_iff_ne, ne_eq, hbuf, not_false_eq_true]
  simp only [hbuf', ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [hget] at hr
  -- Port parsing step
  cases hparse : m.buffer.toNat? with
  | none =>
    simp only [hparse, Option.bind_none] at hr
    cases hr
  | some portVal =>
    by_cases hsize : portVal < UInt16.size
    · exact ⟨portVal, rfl, hsize⟩
    · simp only [hparse, Option.bind_some, hsize, ↓reduceIte] at hr
      cases hr

/-- When portState succeeds via slash terminator with nonempty buffer and no override,
    state becomes pathStart. -/
theorem portState_slash_nonEmptyBuf_noOverride_pathStart
    (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '/')
    (hbuf : m.buffer ≠ "")
    (hso : m.stateOverride = none)
    (m' : Machine) (hr : portState methods m = .ok () m') :
    m'.state = .pathStart := by
  have hValid := portState_slash_success_implies_valid_port methods m n hp hc hbuf m' hr
  obtain ⟨portVal, hport, hsize⟩ := hValid
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  unfold portState at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  have h_curr : curr? methods m = .ok (some '/') m := by
    unfold curr?
    simp only [hp, hc]
  simp only [h_curr] at hr
  simp only [Option.isSome_some, dite_true, Option.get_some] at hr
  have hNotDigit : '/'.isDigit = false := by native_decide
  simp only [hNotDigit, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [hget, get_ParserM] at hr
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, Bool.true_or] at hr
  simp only [if_true] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  have hbuf' : (m.buffer != "") = true := by simp only [bne_iff_ne, ne_eq, hbuf, not_false_eq_true]
  simp only [hbuf', ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  simp only [hport, Option.bind_some, hsize, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [modify_ParserM] at hr
  simp only [get_ParserM] at hr
  simp only [hso, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [get_ParserM] at hr
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [modify_ParserM] at hr
  cases hr
  rfl

/-- When portState succeeds via ? terminator with nonempty buffer and no override,
    state becomes pathStart. -/
theorem portState_question_nonEmptyBuf_noOverride_pathStart
    (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '?')
    (hbuf : m.buffer ≠ "")
    (hso : m.stateOverride = none)
    (m' : Machine) (hr : portState methods m = .ok () m') :
    m'.state = .pathStart := by
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  unfold portState at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  have h_curr : curr? methods m = .ok (some '?') m := by
    unfold curr?
    simp only [hp, hc]
  simp only [h_curr] at hr
  simp only [Option.isSome_some, dite_true, Option.get_some] at hr
  have hNotDigit : '?'.isDigit = false := by native_decide
  simp only [hNotDigit, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [hget, get_ParserM] at hr
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, Bool.true_or, Bool.or_true] at hr
  simp only [if_true] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  have hbuf' : (m.buffer != "") = true := by simp only [bne_iff_ne, ne_eq, hbuf, not_false_eq_true]
  simp only [hbuf', ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  -- Derive port validity from success
  have hValid : ∃ portVal, m.buffer.toNat? = some portVal ∧ portVal < UInt16.size := by
    cases hparse : m.buffer.toNat? with
    | none =>
      simp only [hparse, Option.bind_none] at hr
      cases hr
    | some portVal =>
      by_cases hsize : portVal < UInt16.size
      · exact ⟨portVal, rfl, hsize⟩
      · simp only [hparse, Option.bind_some, hsize, ↓reduceIte] at hr
        cases hr
  obtain ⟨portVal, hport, hsize⟩ := hValid
  simp only [hport, Option.bind_some, hsize, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [modify_ParserM] at hr
  simp only [get_ParserM] at hr
  simp only [hso, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [get_ParserM] at hr
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [modify_ParserM] at hr
  cases hr
  rfl

/-- When portState succeeds via # terminator with nonempty buffer and no override,
    state becomes pathStart. -/
theorem portState_hash_nonEmptyBuf_noOverride_pathStart
    (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '#')
    (hbuf : m.buffer ≠ "")
    (hso : m.stateOverride = none)
    (m' : Machine) (hr : portState methods m = .ok () m') :
    m'.state = .pathStart := by
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  unfold portState at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  have h_curr : curr? methods m = .ok (some '#') m := by
    unfold curr?
    simp only [hp, hc]
  simp only [h_curr] at hr
  simp only [Option.isSome_some, dite_true, Option.get_some] at hr
  have hNotDigit : '#'.isDigit = false := by native_decide
  simp only [hNotDigit, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [hget, get_ParserM] at hr
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, Bool.true_or, Bool.or_true] at hr
  simp only [if_true] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  have hbuf' : (m.buffer != "") = true := by simp only [bne_iff_ne, ne_eq, hbuf, not_false_eq_true]
  simp only [hbuf', ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  -- Derive port validity from success
  have hValid : ∃ portVal, m.buffer.toNat? = some portVal ∧ portVal < UInt16.size := by
    cases hparse : m.buffer.toNat? with
    | none =>
      simp only [hparse, Option.bind_none] at hr
      cases hr
    | some portVal =>
      by_cases hsize : portVal < UInt16.size
      · exact ⟨portVal, rfl, hsize⟩
      · simp only [hparse, Option.bind_some, hsize, ↓reduceIte] at hr
        cases hr
  obtain ⟨portVal, hport, hsize⟩ := hValid
  simp only [hport, Option.bind_some, hsize, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [modify_ParserM] at hr
  simp only [get_ParserM] at hr
  simp only [hso, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [get_ParserM] at hr
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [modify_ParserM] at hr
  cases hr
  rfl

/-- When portState succeeds via \\ terminator (special URLs) with nonempty buffer and no override,
    state becomes pathStart. -/
theorem portState_backslash_nonEmptyBuf_noOverride_pathStart
    (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '\\')
    (hSpecial : m.url.isSpecial = true)
    (hbuf : m.buffer ≠ "")
    (hso : m.stateOverride = none)
    (m' : Machine) (hr : portState methods m = .ok () m') :
    m'.state = .pathStart := by
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  unfold portState at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  have h_curr : curr? methods m = .ok (some '\\') m := by
    unfold curr?
    simp only [hp, hc]
  simp only [h_curr] at hr
  simp only [Option.isSome_some, dite_true, Option.get_some] at hr
  have hNotDigit : '\\'.isDigit = false := by native_decide
  simp only [hNotDigit, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [hget, get_ParserM] at hr
  -- For \\, need isSpecial to trigger terminator
  -- The condition has m.url.isSpecial && some '\\' == some '\\' which with hSpecial becomes true
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, hSpecial, Bool.and_true, Bool.true_or,
    Bool.or_true, beq_iff_eq, Char.reduceEq, hso, Option.isSome_none, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, get_ParserM] at hr
  have hbuf' : (m.buffer != "") = true := by simp only [bne_iff_ne, ne_eq, hbuf, not_false_eq_true]
  simp only [hbuf', ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  -- Derive port validity from success
  have hValid : ∃ portVal, m.buffer.toNat? = some portVal ∧ portVal < UInt16.size := by
    cases hparse : m.buffer.toNat? with
    | none =>
      simp only [hparse, Option.bind_none] at hr
      cases hr
    | some portVal =>
      by_cases hsize : portVal < UInt16.size
      · exact ⟨portVal, rfl, hsize⟩
      · simp only [hparse, Option.bind_some, hsize, ↓reduceIte] at hr
        cases hr
  obtain ⟨portVal, hport, hsize⟩ := hValid
  simp only [hport, Option.bind_some, hsize, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [modify_ParserM] at hr
  simp only [get_ParserM] at hr
  simp only [hso, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [get_ParserM] at hr
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [modify_ParserM] at hr
  cases hr
  rfl

end InverseLemmas

/-! ## Level 14: State Override Lemmas (early return paths) -/

section StateOverrideLemmas

/-- When portState succeeds with nonempty buffer and stateOverride.isSome (EOF),
    state is unchanged due to early return after port parsing. -/
theorem portState_eof_nonEmptyBuf_withOverride_state_unchanged
    (methods : Methods) (m : Machine) (n : Nat) (so : State)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = none)
    (hbuf : m.buffer ≠ "")
    (hso : m.stateOverride = some so)
    (m' : Machine) (hr : portState methods m = .ok () m') :
    m'.state = m.state := by
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  unfold portState at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  have h_curr : curr? methods m = .ok none m := by
    unfold curr?
    simp only [hp, hc]
  simp only [h_curr] at hr
  simp only [Option.isSome_none, dif_neg (Bool.false_ne_true)] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure, get_ParserM] at hr
  simp only [Option.isNone_none, Bool.true_or, hso, Option.isSome_some, if_true] at hr
  have hbuf' : (m.buffer != "") = true := by simp only [bne_iff_ne, ne_eq, hbuf, not_false_eq_true]
  simp only [bind, ReaderT.bind, EStateM.bind, get_ParserM, hbuf', ↓reduceIte] at hr
  -- Derive port validity from success
  have hValid : ∃ portVal, m.buffer.toNat? = some portVal ∧ portVal < UInt16.size := by
    cases hparse : m.buffer.toNat? with
    | none =>
      simp only [hparse, Option.bind_none] at hr
      cases hr
    | some portVal =>
      by_cases hsize : portVal < UInt16.size
      · exact ⟨portVal, rfl, hsize⟩
      · simp only [hparse, Option.bind_some, hsize, ↓reduceIte] at hr
        cases hr
  obtain ⟨portVal, hport, hsize⟩ := hValid
  simp only [hport, Option.bind_some, hsize, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [modify_ParserM] at hr
  simp only [get_ParserM] at hr
  -- This is where stateOverride.isSome triggers early return
  simp only [hso, Option.isSome_some, ↓reduceIte] at hr
  -- Early return: just pure ()
  simp only [pure, ReaderT.pure, EStateM.pure] at hr
  cases hr
  rfl

/-- When portState succeeds with nonempty buffer and stateOverride.isSome (slash),
    state is unchanged. -/
theorem portState_slash_nonEmptyBuf_withOverride_state_unchanged
    (methods : Methods) (m : Machine) (n : Nat) (so : State)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '/')
    (hbuf : m.buffer ≠ "")
    (hso : m.stateOverride = some so)
    (m' : Machine) (hr : portState methods m = .ok () m') :
    m'.state = m.state := by
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  unfold portState at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  have h_curr : curr? methods m = .ok (some '/') m := by
    unfold curr?
    simp only [hp, hc]
  simp only [h_curr] at hr
  simp only [Option.isSome_some, dite_true, Option.get_some] at hr
  have hNotDigit : '/'.isDigit = false := by native_decide
  simp only [hNotDigit, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [hget, get_ParserM] at hr
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, Bool.true_or] at hr
  simp only [if_true] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  have hbuf' : (m.buffer != "") = true := by simp only [bne_iff_ne, ne_eq, hbuf, not_false_eq_true]
  simp only [hbuf', ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  have hValid : ∃ portVal, m.buffer.toNat? = some portVal ∧ portVal < UInt16.size := by
    cases hparse : m.buffer.toNat? with
    | none =>
      simp only [hparse, Option.bind_none] at hr
      cases hr
    | some portVal =>
      by_cases hsize : portVal < UInt16.size
      · exact ⟨portVal, rfl, hsize⟩
      · simp only [hparse, Option.bind_some, hsize, ↓reduceIte] at hr
        cases hr
  obtain ⟨portVal, hport, hsize⟩ := hValid
  simp only [hport, Option.bind_some, hsize, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [modify_ParserM] at hr
  simp only [get_ParserM] at hr
  simp only [hso, Option.isSome_some, ↓reduceIte] at hr
  simp only [pure, ReaderT.pure, EStateM.pure] at hr
  cases hr
  rfl

/-- When portState succeeds with nonempty buffer and stateOverride.isSome (?),
    state is unchanged. -/
theorem portState_question_nonEmptyBuf_withOverride_state_unchanged
    (methods : Methods) (m : Machine) (n : Nat) (so : State)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '?')
    (hbuf : m.buffer ≠ "")
    (hso : m.stateOverride = some so)
    (m' : Machine) (hr : portState methods m = .ok () m') :
    m'.state = m.state := by
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  unfold portState at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  have h_curr : curr? methods m = .ok (some '?') m := by
    unfold curr?
    simp only [hp, hc]
  simp only [h_curr] at hr
  simp only [Option.isSome_some, dite_true, Option.get_some] at hr
  have hNotDigit : '?'.isDigit = false := by native_decide
  simp only [hNotDigit, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [hget, get_ParserM] at hr
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, Bool.true_or, Bool.or_true] at hr
  simp only [if_true] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  have hbuf' : (m.buffer != "") = true := by simp only [bne_iff_ne, ne_eq, hbuf, not_false_eq_true]
  simp only [hbuf', ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  have hValid : ∃ portVal, m.buffer.toNat? = some portVal ∧ portVal < UInt16.size := by
    cases hparse : m.buffer.toNat? with
    | none =>
      simp only [hparse, Option.bind_none] at hr
      cases hr
    | some portVal =>
      by_cases hsize : portVal < UInt16.size
      · exact ⟨portVal, rfl, hsize⟩
      · simp only [hparse, Option.bind_some, hsize, ↓reduceIte] at hr
        cases hr
  obtain ⟨portVal, hport, hsize⟩ := hValid
  simp only [hport, Option.bind_some, hsize, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [modify_ParserM] at hr
  simp only [get_ParserM] at hr
  simp only [hso, Option.isSome_some, ↓reduceIte] at hr
  simp only [pure, ReaderT.pure, EStateM.pure] at hr
  cases hr
  rfl

/-- When portState succeeds with nonempty buffer and stateOverride.isSome (#),
    state is unchanged. -/
theorem portState_hash_nonEmptyBuf_withOverride_state_unchanged
    (methods : Methods) (m : Machine) (n : Nat) (so : State)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '#')
    (hbuf : m.buffer ≠ "")
    (hso : m.stateOverride = some so)
    (m' : Machine) (hr : portState methods m = .ok () m') :
    m'.state = m.state := by
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  unfold portState at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  have h_curr : curr? methods m = .ok (some '#') m := by
    unfold curr?
    simp only [hp, hc]
  simp only [h_curr] at hr
  simp only [Option.isSome_some, dite_true, Option.get_some] at hr
  have hNotDigit : '#'.isDigit = false := by native_decide
  simp only [hNotDigit, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [hget, get_ParserM] at hr
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, Bool.true_or, Bool.or_true] at hr
  simp only [if_true] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  have hbuf' : (m.buffer != "") = true := by simp only [bne_iff_ne, ne_eq, hbuf, not_false_eq_true]
  simp only [hbuf', ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  have hValid : ∃ portVal, m.buffer.toNat? = some portVal ∧ portVal < UInt16.size := by
    cases hparse : m.buffer.toNat? with
    | none =>
      simp only [hparse, Option.bind_none] at hr
      cases hr
    | some portVal =>
      by_cases hsize : portVal < UInt16.size
      · exact ⟨portVal, rfl, hsize⟩
      · simp only [hparse, Option.bind_some, hsize, ↓reduceIte] at hr
        cases hr
  obtain ⟨portVal, hport, hsize⟩ := hValid
  simp only [hport, Option.bind_some, hsize, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [modify_ParserM] at hr
  simp only [get_ParserM] at hr
  simp only [hso, Option.isSome_some, ↓reduceIte] at hr
  simp only [pure, ReaderT.pure, EStateM.pure] at hr
  cases hr
  rfl

/-- When portState succeeds with nonempty buffer and stateOverride.isSome (\\),
    state is unchanged. -/
theorem portState_backslash_nonEmptyBuf_withOverride_state_unchanged
    (methods : Methods) (m : Machine) (n : Nat) (so : State)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = some '\\')
    (hSpecial : m.url.isSpecial = true)
    (hbuf : m.buffer ≠ "")
    (hso : m.stateOverride = some so)
    (m' : Machine) (hr : portState methods m = .ok () m') :
    m'.state = m.state := by
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  unfold portState at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  have h_curr : curr? methods m = .ok (some '\\') m := by
    unfold curr?
    simp only [hp, hc]
  simp only [h_curr] at hr
  simp only [Option.isSome_some, dite_true, Option.get_some] at hr
  have hNotDigit : '\\'.isDigit = false := by native_decide
  simp only [hNotDigit, Bool.false_eq_true, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure] at hr
  simp only [hget, get_ParserM] at hr
  simp only [Option.isNone_some, Bool.false_or, beq_self_eq_true, hSpecial, Bool.and_true, Bool.true_or,
    Bool.or_true, beq_iff_eq, Char.reduceEq, hso, Option.isSome_some, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, get_ParserM] at hr
  have hbuf' : (m.buffer != "") = true := by simp only [bne_iff_ne, ne_eq, hbuf, not_false_eq_true]
  simp only [hbuf', ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind, hget, get_ParserM] at hr
  have hValid : ∃ portVal, m.buffer.toNat? = some portVal ∧ portVal < UInt16.size := by
    cases hparse : m.buffer.toNat? with
    | none =>
      simp only [hparse, Option.bind_none] at hr
      cases hr
    | some portVal =>
      by_cases hsize : portVal < UInt16.size
      · exact ⟨portVal, rfl, hsize⟩
      · simp only [hparse, Option.bind_some, hsize, ↓reduceIte] at hr
        cases hr
  obtain ⟨portVal, hport, hsize⟩ := hValid
  simp only [hport, Option.bind_some, hsize, ↓reduceIte] at hr
  simp only [bind, ReaderT.bind, EStateM.bind] at hr
  simp only [modify_ParserM] at hr
  simp only [get_ParserM] at hr
  simp only [hso, Option.isSome_some, ↓reduceIte] at hr
  simp only [pure, ReaderT.pure, EStateM.pure] at hr
  cases hr
  rfl

end StateOverrideLemmas

end LeanUrl.Parser
