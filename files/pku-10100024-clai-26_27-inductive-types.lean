/-! # Numbers, induction, and inductive types — the Lean on the slides

Self-contained: needs only Lean 4 (v4.34.0-rc1 or later), no library.

How to run
* Install Lean via elan: https://lean-lang.org/install
* Open this file in VS Code with the "Lean 4" extension.  Results of
  `#eval`/`#check`/`#print`/`#reduce` appear in the Infoview; errors are
  underlined, and the ones marked `#guard_msgs(drop error)` are expected.
* Or, in a terminal: `lean inductive-types.lean`

`-- Slide N` names the page of the deck the code appears on.  Blocks marked
"support" are definitions from the course library that the slides use but
do not show.  Section and figure numbers are Nederpelt & Geuvers, *Type
Theory and Formal Proof*, §14.1, §8.2, §16.2.  Each slide sits in its own
`section`, so a name one slide introduces does not leak into the next.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- support: L1's Term and its size, as in Clai.Lambda
namespace Clai.Lambda
inductive Term where
  | var : String → Term
  | app : Term → Term → Term
  | lam : String → Term → Term
namespace Term
def size : Term → Nat
  | var _ => 1
  | app M N => M.size + N.size + 1
  | lam _ M => M.size + 1
end Term
end Clai.Lambda

/-! ## Slide 13 — What `inductive` generates -/

section
inductive N where
  | zero : N
  | succ : N → N

#check @N.rec
-- @N.rec : {motive : N → Sort u_1} →
--   motive N.zero →
--   ((a : N) → motive a → motive a.succ) →
--   (t : N) → motive t

#print axioms N.rec   -- 'N.rec' does not depend on any axioms
end

/-! ## Slide 14 — The recursor computes -/

section
def fac' : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun n r => (n + 1) * r)

#reduce fac' 3                  -- 6
example : fac' 3 = 6 := rfl     -- (conv), no proof steps
#eval fac' 5                    -- 120
end

/-! ## Slide 15 — Pattern matching is the recursor -/

section
def fac : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * fac n

example : fac 3 = 6 := rfl
#eval fac 20                    -- 2432902008176640000

#print fac
-- def fac : Nat → Nat :=
-- fun x => Nat.brecOn x fac._f
end

/-! ## Slide 18 — `induction`, and the term it built -/

section
theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero      => rfl                    -- ⊢ 0 + 0 = 0
  | succ n ih => rw [Nat.add_succ, ih]  -- ⊢ 0 + (n + 1) = n + 1

#print zero_add'
-- theorem zero_add' : ∀ (n : Nat), 0 + n = n :=
-- fun n => Nat.recAux (Eq.refl (0 + 0)) (fun n ih => ⋯) n
end

/-! ## Slide 19 — `cases`: elimination without the hypothesis -/

section
theorem zero_or_succ (n : Nat) : n = 0 ∨ ∃ m, n = m + 1 := by
  cases n with
  | zero   => exact Or.inl rfl
  | succ m => exact Or.inr ⟨m, rfl⟩
end

/-! ## Slide 20 — Every inductive type has induction -/

section
theorem length_append' (xs ys : List Nat) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil          => simp
  | cons x xs ih => simp [ih, Nat.add_right_comm]

open Clai.Lambda in
theorem size_pos (M : Term) : 0 < M.size := by
  induction M with
  | var _       => simp [Term.size]
  | app _ _ _ _ => simp [Term.size]
  | lam _ _ _   => simp [Term.size]
end

/-! ## Slide 22 — Rule induction, and inversion, in Lean -/

section
inductive Even : Nat → Prop where
  | zero : Even 0
  | add2 {n} : Even n → Even (n + 2)

theorem even_double (n : Nat) : Even (2 * n) := by
  induction n with
  | zero      => exact Even.zero
  | succ n ih => rw [Nat.mul_succ]; exact Even.add2 ih

theorem even_inv (n : Nat) (h : Even (n + 2)) : Even n := by
  cases h with
  | add2 h' => exact h'            -- `zero` cannot end in n + 2
end

/-! ## Slide 24 — The connectives and =, in Lean -/

section
#print And
-- structure And (a b : Prop) : Prop
-- constructor:
--   And.intro {a b : Prop} (left : a) (right : b) : a ∧ b

#check @Or.rec
-- ∀ {a b : Prop} {motive : a ∨ b → Prop},
--   (∀ (h : a), motive ⋯) → (∀ (h : b), motive ⋯) →
--   ∀ (t : a ∨ b), motive t

#print False   -- inductive False : Prop,  constructors: (none)

#print Eq
-- inductive Eq : {α : Sort u_1} → α → α → Prop
-- constructors: Eq.refl : ∀ {α : Sort u_1} (a : α), a = a
end

/-! ## Slide 26 — Termination is an obligation -/

section
def gcd' : Nat → Nat → Nat
  | 0,     y => y
  | x + 1, y => gcd' (y % (x + 1)) (x + 1)
termination_by x _ => x
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos x)

#eval gcd' 12 18                              -- 6
#guard_msgs(drop error) in
example : gcd' 12 18 = 6 := rfl               -- error: not by (conv)
example : gcd' 12 18 = 6 := by simp [gcd']    -- by its equations
end

/-! ## Slide 28 — `decide` and `omega` -/

section
example : 7 % 3 = 1 := by decide
example : ∀ n < 5, n * n < 20 := by decide
#guard_msgs(drop error) in
example : ∀ n < 100000, n + 0 = n := by decide  -- too big

example (a b : Nat) (h : a + 2 * b < 10) (k : 4 < b) : False := by
  omega
example (n : Nat) : n ≤ 2 * n := by omega
#guard_msgs(drop error) in
example (a b : Nat) : 0 ≤ a * b := by omega       -- a * b: not linear
end

/-! ## Slide 29 — `grind` -/

section
example (f : Nat → Nat) (a b c : Nat) (h₁ : a = b) (h₂ : b = c) :
    f (f a) = f (f c) := by grind
example (xs ys : List Nat) :
    (xs ++ ys).length = xs.length + ys.length := by grind
theorem g (p q : Prop) (a b : Nat) (h : p ∨ q)
    (hp : p → a < b) (hq : q → a < b) : a ≤ b := by grind

#print axioms g
-- 'g' depends on axioms: [propext, Classical.choice, Quot.sound]
end
