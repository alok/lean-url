/-
Option.get compatibility lemmas for verified Option extraction.

These lemmas provide compile-time proof that an Option is Some,
allowing use of Option.get instead of Option.get!

Import this module to use `Option.get` with evidence from guards.
-/

namespace LeanUrl.Parser.OptionProofs

/-! ## Core isSome lemmas for Option.get -/

/-- Key lemma: Option.map ... .getD false implies isSome (for Option.get) -/
theorem isSome_of_map_getD_true {α : Type} {o : Option α} {f : α → Bool}
    (h : (o.map f).getD false = true) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- isSome from equality check -/
theorem isSome_of_eq_some {α : Type} [DecidableEq α] {o : Option α} {a : α}
    (h : o == some a) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- isSome when negated isNone -/
theorem isSome_of_not_isNone {α : Type} {o : Option α}
    (h : ¬o.isNone) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- isSome from Bool negation of isNone -/
theorem isSome_of_isNone_false {α : Type} {o : Option α}
    (h : o.isNone = false) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- isSome from not-none check -/
theorem isSome_of_ne_none {α : Type} [DecidableEq α] {o : Option α}
    (h : (o != none) = true) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- isSome from isSome check (trivial but useful) -/
theorem isSome_of_isSome_true {α : Type} {o : Option α}
    (h : o.isSome = true) : o.isSome = true := h

/-- isSome from OR'd condition -/
theorem isSome_of_or_cond {α : Type} [DecidableEq α] {o : Option α} {f : α → Bool} {a : α}
    (h : ((o.map f).getD false || (o == some a)) = true) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- isSome from AND with isSome on left -/
theorem isSome_of_and_isSome {α : Type} {o : Option α} {p : Bool}
    (h : (o.isSome && p) = true) : o.isSome = true := by
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- isSome from negation of isNone in OR -/
theorem isSome_of_not_isNone_or {α : Type} {o : Option α} {p : Prop}
    (h : ¬(o.isNone = true ∨ p)) : o.isSome = true := by
  have hn : o.isNone ≠ true := fun hx => h (Or.inl hx)
  cases o with
  | none => simp at hn
  | some _ => rfl

/-- isSome when we're in the else branch of `if c?.isNone || ...` -/
theorem isSome_of_not_isNone_or_bool {α : Type} {o : Option α} {p : Bool}
    (h : ¬(o.isNone || p)) : o.isSome = true := by
  simp only [Bool.or_eq_true, not_or] at h
  cases o with
  | none => simp at h
  | some _ => rfl

/-! ## Value extraction lemmas -/

/-- Value equality after Option.get when we know it's some a -/
theorem Option.get_eq_of_eq_some {α : Type} [DecidableEq α] {o : Option α} {a : α}
    (heq : o == some a) (h : o.isSome = true) : o.get h = a := by
  cases o with
  | none => simp at heq
  | some x =>
    simp only [beq_iff_eq, Option.some.injEq] at heq
    simp only [Option.get_some, heq]

/-- The predicate holds for the extracted value -/
theorem pred_of_map_getD_true {α : Type} {o : Option α} {f : α → Bool}
    (h : (o.map f).getD false = true) (hisSome : o.isSome = true) : f (o.get hisSome) = true := by
  cases o with
  | none => simp at hisSome
  | some a =>
    simp only [Option.map_some, Option.getD_some] at h
    simp only [Option.get_some, h]

/-- Convert decidable Bool to isSome proof -/
theorem isSome_of_decide_map_getD {α : Type} {o : Option α} {f : α → Bool}
    (h : (o.map f).getD false) : o.isSome = true := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-! ## Char-specific lemmas -/

/-- isSome when isAlpha check passes -/
theorem isSome_of_isAlpha {c? : Option Char}
    (h : (c?.map Char.isAlpha).getD false = true) : c?.isSome = true :=
  isSome_of_map_getD_true h

/-- isSome when isDigit check passes -/
theorem isSome_of_isDigit {c? : Option Char}
    (h : (c?.map Char.isDigit).getD false = true) : c?.isSome = true :=
  isSome_of_map_getD_true h

/-- isSome when isAlphanum check passes -/
theorem isSome_of_isAlphanum {c? : Option Char}
    (h : (c?.map Char.isAlphanum).getD false = true) : c?.isSome = true :=
  isSome_of_map_getD_true h

/-- isAlpha holds for extracted char -/
theorem isAlpha_of_map_getD {c? : Option Char}
    (h : (c?.map Char.isAlpha).getD false = true) (hisSome : c?.isSome = true) :
    (c?.get hisSome).isAlpha = true :=
  pred_of_map_getD_true h hisSome

/-- isDigit holds for extracted char -/
theorem isDigit_of_map_getD {c? : Option Char}
    (h : (c?.map Char.isDigit).getD false = true) (hisSome : c?.isSome = true) :
    (c?.get hisSome).isDigit = true :=
  pred_of_map_getD_true h hisSome

end LeanUrl.Parser.OptionProofs
