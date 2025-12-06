import LeanUrl.Parser.Basic

/-!
# Monadic Binding Reduction Exploration

This file explores why simp/grind don't reduce ParserM bindings
and develops strategies to make them work.

## Test Cases:
1. curr? standalone (simplest)
2. get/modify in ParserM context (intermediate)
3. portState full (complex)
-/

open LeanUrl.Parser

/-! ## Understanding the Types -/

#check @curr?
-- curr? : ParserM (Option Char)
-- ParserM = ReaderT Methods (EStateM String Machine)

#check @ReaderT.bind
#check @EStateM.bind
#check @EStateM.Result

/-! ## Test 1: curr? standalone -/

-- Goal: Show curr? methods m = .ok (m.input[n]?) m when m.pointer = .ofNat n
-- RESULT: This WORKS! simp only [hp] proves it!
theorem curr?_ofNat (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n) :
    curr? methods m = .ok (m.input[n]?) m := by
  unfold curr?
  simp only [hp]
  -- PROVED!

-- Variant: when we know the result is none
-- RESULT: Also works with one more rewrite!
theorem curr?_none (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n) (hc : m.input[n]? = none) :
    curr? methods m = .ok none m := by
  rw [curr?_ofNat methods m n hp, hc]

/-! ## Test 2: get in ParserM context -/

-- get : ParserM Machine = ReaderT Methods (EStateM String Machine) Machine
-- For ReaderT over EStateM, get lifts EStateM.get
-- Let's find the right unfold path

#check (get : ParserM Machine)
#check @MonadStateOf.get

-- Try different unfold approaches
theorem get_ParserM (methods : Methods) (m : Machine) :
    (get : ParserM Machine) methods m = .ok m m := by
  -- get in ReaderT context is: fun r => EStateM.get
  -- native_decide fails with free variables, try rfl:
  rfl

/-! ## Test 3: modify in ParserM context -/

#check @modify
#check @MonadStateOf.modifyGet

theorem modify_ParserM (methods : Methods) (m : Machine) (f : Machine → Machine) :
    (modify f : ParserM Unit) methods m = .ok () (f m) := by
  -- Try rfl first
  rfl

/-! ## Test 4: bind composition -/

-- If we know x methods m = .ok a m'
-- And we know f a methods m' = .ok b m''
-- Then (x >>= f) methods m = .ok b m''

-- RESULT: This works with simp + rewrite!
theorem bind_ok_ok {α β : Type} (x : ParserM α) (f : α → ParserM β)
    (methods : Methods) (m m' m'' : Machine) (a : α) (b : β)
    (hx : x methods m = .ok a m')
    (hf : f a methods m' = .ok b m'') :
    (x >>= f) methods m = .ok b m'' := by
  -- Unfold bind for ReaderT, then EStateM
  simp only [bind, ReaderT.bind, EStateM.bind]
  -- Goal: match x methods m with | .ok a s => f a methods s | ...
  -- Rewrite with hx to reduce the match
  rw [hx]
  -- Goal: f a methods m' = .ok b m''
  exact hf

/-! ## Test 5: Try grind interactive -/

example (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n) :
    curr? methods m = .ok (m.input[n]?) m := by
  unfold curr?
  simp only [hp]
  -- Proved!

/-! ## Test 6: The actual portState lemma -/

-- Now that we have the building blocks, let's try the actual proof
-- portState is: curr? >>= fun c? => (if c?.isSome then ... else ...) >>= ...
-- With our hypotheses, c? = none, so we take the else branch

-- First, let's prove some helper facts about conditions
theorem portState_none_emptyBuf_noOverride' (methods : Methods) (m : Machine) (n : Nat)
    (hp : m.pointer = .ofNat n)
    (hc : m.input[n]? = none)
    (hbuf : m.buffer = "")
    (hso : m.stateOverride = none) :
    portState methods m = .ok () { m with state := .pathStart, pointer := m.pointer - 1, buffer := m.buffer, stateOverride := m.stateOverride } := by
  -- Step 1: Unfold portState and look at the structure
  unfold portState

  -- The do-block structure is:
  -- do let c? ← curr?
  --    if hc : c?.isSome then ... else ... (takes else since c? = none)
  -- The else branch eventually does: modify fun m => { m with state := pathStart, ... }

  -- Step 2: Use simp to unfold bind and apply curr? result
  simp only [bind, ReaderT.bind, EStateM.bind]

  -- Step 3: We need to show that curr? methods m = .ok none m
  -- and trace through the conditionals

  -- curr? unfolds and uses hp
  have h_curr : curr? methods m = .ok none m := by
    rw [curr?_ofNat methods m n hp]
    simp only [hc]

  -- Now rw with h_curr to reduce the first match
  rw [h_curr]

  -- Reduce the match on .ok none m - should give us the ok branch
  simp only []

  -- Now we're in the continuation with a = none, s = m
  -- The condition is: if h : (Option.isSome none = true) then ... else ...
  -- none.isSome = false, so reduce it
  simp only [Option.isSome_none, Option.isNone_none]

  -- Now we have: if h : false = true then ... else ...
  -- This dite should reduce to the else branch
  simp only [dif_neg (Bool.false_ne_true)]

  -- Reduce pure >>= f to f
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]

  -- Now we have match get methods m with ... - get returns .ok m m
  -- Use have statements to reduce each get
  have hget : (get : ParserM Machine) methods m = .ok m m := rfl
  rw [hget]
  -- Now the first match should reduce - state is still m
  simp only []
  -- Second get - note: state s is now m (from first get)
  -- Same state, same result
  rw [hget]
  simp only []

  -- Now simplify: (true || ...) = true => take then branch
  simp only [Bool.true_or, decide_eq_true_eq]
  -- Reduce if True then A else B => A
  simp only [if_true]

  -- Unfold ReaderT.bind and apply hget again
  simp only [bind, ReaderT.bind, EStateM.bind]
  rw [hget]
  simp only []

  -- Now we have: if (m.buffer != "") = true then ... else ...
  -- Since hbuf : m.buffer = "", this is: if ("" != "") = true then ... else ...
  -- = if false = true then ... else ...
  simp only [hbuf, bne_self_eq_false]
  -- The condition false = true is decidable as False, use decide
  simp only [Bool.false_eq_true, ↓reduceIte]

  -- Now we're in the else branch with another pure >>= pattern
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  rw [hget]
  simp only []

  -- Now: if m.stateOverride.isSome = true then ... else ...
  -- Since hso : m.stateOverride = none, this is false
  simp only [hso, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

  -- Pure >>= pattern should reduce
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, EStateM.bind, EStateM.pure]
  -- No more get in the goal after the last reduction

  -- Now we should have modify
  -- Use ext to decompose the equality
  -- First, prove modify f methods m = .ok () (f m) directly
  have hmod : ∀ (f : Machine → Machine), (modify f : ParserM Unit) methods m = .ok () (f m) := by
    intro f
    rfl

  -- Apply hmod
  rw [hmod]

  -- Now need to show: f m = { m with ... }
  -- where f = fun m => { m with state := .pathStart, pointer := m.pointer - 1 }
  -- This should be rfl, but we need to match the structure fields
  -- Since hbuf : m.buffer = "" and hso : m.stateOverride = none
  -- And RHS uses defaults, we need to rewrite
  simp only [hbuf, hso]

/-! ## Debugging: See what unfold produces -/

-- Use #check and #reduce to understand the terms
#check (portState : ParserM Unit)

-- See the definition after elaboration
set_option pp.all false in
#print portState

/-! ## Notes on stuck points -/

/-
After experimenting, document:
1. What goal shape appears after each unfold?
2. Where exactly does simp get stuck?
3. What lemma would be needed to continue?

Example stuck signature format:
```
STUCK at: [line number / after which tactic]
Goal: [the goal]
Missing: [what lemma/fact would help]
```
-/
