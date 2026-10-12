/-! # Definitions and environments — the Lean on the slides

Self-contained: needs only Lean 4 (v4.34.0-rc1 or later), no library.

How to run
* Install Lean via elan: https://lean-lang.org/install
* Open this file in VS Code with the "Lean 4" extension.  Results of
  `#eval`/`#check`/`#print` appear in the Infoview; errors are underlined.
* Or, in a terminal: `lean definitions.lean`

`-- Slide N` names the page of the deck the code appears on.  Each slide
sits in its own namespace, so a name defined on one slide (`d`, `Reflexive`)
can be defined afresh on another.
-/

set_option linter.unusedVariables false

/-! ## Slide 06 — The series, in Lean -/

namespace Slide06

-- The two flags are the two binders; the type follows `:`, the definiens `:=`.
def Reflexive  (S : Type) (R : S → S → Prop) : Prop := ∀ x, R x x
def Antisymm   (S : Type) (R : S → S → Prop) : Prop :=
  ∀ x y, R x y → R y x → x = y
def Transitive (S : Type) (R : S → S → Prop) : Prop :=
  ∀ x y z, R x y → R y z → R x z
def PartialOrder (S : Type) (R : S → S → Prop) : Prop :=
  Reflexive S R ∧ Antisymm S R ∧ Transitive S R     -- (4) after (1)–(3)

#check @Reflexive        -- @Reflexive : (S : Type) → (S → S → Prop) → Prop

end Slide06

/-! ## Slide 08 — Instantiation is application -/

namespace Slide08

-- (declared on an earlier slide)
def Reflexive  (S : Type) (R : S → S → Prop) : Prop := ∀ x, R x x

-- Two instantiations; the type of R is computed from the choice of S.
#check Reflexive Nat (· ≤ ·)          -- Reflexive Nat (fun x y => x ≤ y) : Prop
#check Reflexive String (· ≠ ·)       -- Reflexive String (fun x y => x ≠ y) : Prop

-- Under S := Nat, a relation on strings is refused:
#guard_msgs(drop error) in
#check Reflexive Nat (fun (s t : String) => s = t)
-- Application type mismatch: the argument has type String → String → Prop
-- but is expected to have type Nat → Nat → Prop

-- A correct instantiation, a false proposition, and so refutable:
example : Reflexive Nat (· < ·) → False := fun h => Nat.lt_irrefl 0 (h 0)

end Slide08

/-! ## Slide 09 — Flags in Lean: `variable` and `section` -/

namespace Slide09

-- `variable` raises the flag; `section … end` is its pole.
section
variable (S : Type) (R : S → S → Prop)

def Refl  : Prop := ∀ x, R x x                -- parameters unwritten
def Trans : Prop := ∀ x y z, R x y → R y z → R x z
def Preord : Prop := Refl S R ∧ Trans S R      -- and written when used
end                                            -- the flag is hauled down

#check @Preord     -- Preord : (S : Type) → (S → S → Prop) → Prop

end Slide09

/-! ## Slide 11 — A theorem is a definition -/

namespace Slide11

-- `theorem` for proofs, `def` for the other three kinds.
def      Nat2   : Type := Nat                    -- sets
def      two    : Nat  := 2                      -- objects
def      Even   (n : Nat) : Prop := ∃ k, n = 2*k -- propositions
theorem  even4  : Even 4 := ⟨2, rfl⟩             -- proofs

#print two        -- def …two : Nat :=
                  -- 2
#print even4      -- theorem …even4 : Even 4 :=
                  -- Exists.intro 2 rfl

end Slide11

/-! ## Slide 13 — A theorem applied by instantiation, in Lean -/

namespace Slide13

-- 1. A theorem with three data parameters and one proof parameter, u.
theorem le_add_right_of_le (a b k : Nat) (u : a ≤ b) : a + k ≤ b + k :=
  Nat.add_le_add_right u k

-- 2. Instantiate the data: the type of u becomes 3 ≤ 5.
#check le_add_right_of_le 3 5 10      -- 3 ≤ 5 → 3 + 10 ≤ 5 + 10

-- 3. Supply U : 3 ≤ 5 as the last argument: the specialised theorem.
example : 3 + 10 ≤ 5 + 10 := le_add_right_of_le 3 5 10 (by decide)

end Slide13

/-! ## Slide 16 — A file is an environment -/

namespace Slide16

-- A file is Δ; `variable` and a declaration's binders are Γ.
variable (S : Type)
def Reflexive (R : S → S → Prop) : Prop := ∀ x, R x x
def PartialOrder (R : S → S → Prop) : Prop := Reflexive S R

#print PartialOrder
-- def …PartialOrder : (S : Type) → (S → S → Prop) → Prop :=
-- fun S R => Reflexive S R
-- Γ has become λ.

end Slide16

/-! ## Slide 18 — `rw` takes one δ-step -/

namespace Slide18

def d (n : Nat) : Nat := n + n       -- n:ℕ ▷ d(n) := n + n : ℕ, now in Δ

-- `rw [d]` unfolds one occurrence of d: the first it finds, here d a.
example (a b : Nat) : d a + d b = (a + a) + (b + b) := by
  rw [d]      -- ⊢ a + a + d b = a + a + (b + b)       d b is still folded
  rw [d]      -- ⊢ a + a + (b + b) = a + a + (b + b)   both sides agree: closed

end Slide18

/-! ## Slide 20 — `unfold` takes every δ-step for one constant -/

namespace Slide20

-- (declared on an earlier slide)
def d (n : Nat) : Nat := n + n

-- `unfold d` unfolds every occurrence of d: the δ-normal form with respect to d.
example (a b : Nat) : d a + d b = (a + a) + (b + b) := by
  unfold d    -- ⊢ a + a + (b + b) = a + a + (b + b)
  rfl

-- With respect to d only: a constant defined through d stays folded.
def e (n : Nat) : Nat := d n + 1
example (a : Nat) : e a = (a + a) + 1 := by
  unfold e    -- ⊢ d a + 1 = a + a + 1                  d is still folded
  unfold d    -- ⊢ a + a + 1 = a + a + 1
  rfl

end Slide20

/-! ## Slide 22 — `rfl` does β and δ -/

namespace Slide22

-- `rfl` decides βδ-convertibility: it normalises both sides and compares.
def d (n : Nat) : Nat := n + n

example : d 3 = 6 := rfl        -- one δ-step, then arithmetic
example : d = fun n => n + n := rfl

-- Three definitions, the third using the other two; unfolding all of them:
def a (x y : Int) : Int := x*x + y*y
def b (x y : Int) : Int := 2 * (x * y)
def c (x y : Int) : Int := a x y + b x y
def lemma' (x y : Int) : Prop := c x y = (x + y) * (x + y)

example (u v : Int) : lemma' u v = (u*u + v*v + 2*(u*v) = (u+v)*(u+v)) := rfl
-- Three δ-steps, in whichever order: the normal form is unique.

end Slide22

/-! ## Slide 23 — Unfolding is a policy -/

namespace Slide23

-- Which constants the checker unfolds on its own is set per definition.
abbrev  Fast : Type := Nat        -- @[reducible]: always unfolded
def     Norm : Type := Nat        -- default: unfolded when needed
@[irreducible] def Slow : Type := Nat   -- never unfolded automatically

example : Fast = Nat := rfl
example : Norm = Nat := rfl
#guard_msgs(drop error) in
example : Slow = Nat := rfl       -- Type mismatch: rfl has type ?m = ?m
                                  -- but is expected to have type Slow = Nat
unseal Slow in                    -- the policy, lifted for one declaration
example : Slow = Nat := rfl       -- accepted: δ is available again

end Slide23

/-! ## Slide 25 — `axiom` is a definition with no body -/

namespace Slide25

-- A primitive definition has no body: `axiom`, and no `:=`.
axiom choiceLike (α : Type) : Nonempty α → α

#print choiceLike
-- axiom choiceLike : (α : Type) → Nonempty α → α
-- no `:=`: nothing to unfold

-- Lean's own three primitives are of exactly this kind:
#check @propext
#check @Classical.choice
#check @Quot.sound

end Slide25

/-! ## Slide 27 — The audit -/

namespace Slide27

-- `#print axioms`: the primitive constants left after δ-normalisation.
theorem plain : 2 + 2 = 4 := rfl
theorem classy (p : Prop) : p ∨ ¬p := Classical.em p

#print axioms plain      -- 'plain' does not depend on any axioms
#print axioms classy
-- 'classy' depends on axioms: [propext, Classical.choice, Quot.sound]

-- One caveat.  A recursor has no body either, yet:
#print axioms Nat.rec    -- 'Nat.rec' does not depend on any axioms
-- The audit lists the constants declared as axioms; the ones every
-- `inductive` adds, its recursor, it trusts silently.

end Slide27

/-! ## Slide 28 — Why three names, and not one -/

namespace Slide28

-- On paper classical logic adds one primitive; the audit reported three.
#print axioms Classical.choice   -- depends on axioms: [Classical.choice]
#print axioms propext            -- depends on axioms: [propext]
#print axioms Quot.sound         -- depends on axioms: [Quot.sound]

-- These two are not: both are theorems, and the audit says what they cost.
#print axioms funext             -- depends on axioms: [Quot.sound]
#print axioms Classical.em
-- 'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound]

-- `funext` is proved from quotients; `Classical.em` from choice, propext
-- and funext, Diaconescu's theorem.  The excluded third is derived.

end Slide28

/-! ## Slide 29 — `sorry` compiles -/

namespace Slide29

-- `sorry` is a primitive constant that inhabits any type: an environment
-- containing it proves everything.
theorem shaky : 2 + 2 = 5 := by sorry

#print axioms shaky      -- 'shaky' depends on axioms: [sorryAx]
#check @sorryAx          -- sorryAx : (α : Sort u_1) → Bool → α

-- It compiles, with a warning.  Only the audit reveals it.

end Slide29

/-! ## Slide 30 — An axiom is a promise -/

namespace Slide30

-- A primitive definition passes every check whether or not it makes sense.
-- k(A,B) := ⊥⊥ : (A ⇒ B) ⇒ A looks like Peirce's law, and derives False:
axiom bad (A B : Prop) : (A → B) → A

theorem everything : False := bad False False (fun h => h)

#print axioms everything    -- 'everything' depends on axioms: [bad]

-- The kernel is not fooled: it reports the culprit by name.  An axiom is
-- a promise, and `#print axioms` is where the promises are collected.

end Slide30

/-! ## Slide 34 — The rules, by their library names -/

namespace Slide34

-- The library holds the named rules; the parameters that only repeat
-- the context, A B C, are suppressed by `{}`.
#check @And.intro    -- @And.intro : ∀ {a b : Prop}, a → b → a ∧ b
#check @Or.elim      -- @Or.elim : ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
#check @absurd       -- @absurd : {a : Prop} → {b : Sort u_1} → a → ¬a → b

variable (A B C : Prop)
example (u : A) (v : B) : A ∧ B := And.intro u v      -- ∧-in(A,B,u,v)
example (u : A ∧ B) : A := u.left                     -- ∧-el₁(A,B,u)
example (u : A) : A ∨ B := Or.inl u                   -- ∨-in₁(A,B,u)
example (u : A ∨ B) (v : A → C) (w : B → C) : C :=
  Or.elim u v w                                       -- ∨-el(A,B,C,u,v,w)

end Slide34

/-! ## Slide 36 — `have` is a flag line -/

namespace Slide36

-- `have` is a flag line: the statement is checked, recorded under a
-- name, and usable below.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  have h1 : p := hp          -- checked, recorded, usable below
  have h2 : q := hq
  exact And.intro h1 h2

end Slide36

/-! ## Slide 37 — `show`, `suffices`, `refine` -/

namespace Slide37

-- Three more ways to write a flag line.
-- `show` restates the goal at a βδ-convertible type: (conv), as a tactic.
example (p : Prop) (hp : p) : ¬¬p := by
  show ¬p → False
  intro hnp; exact hnp hp

-- `suffices` is `have` read backwards: name what would be enough, use it
-- at once, and prove it afterwards.
example (p q : Prop) (hp : p) (h : p → q) : q ∧ p := by
  suffices hq : q from ⟨hq, hp⟩
  exact h hp

-- `refine` is `exact` with holes: each `?_` becomes a goal, a flag still
-- to be hauled down.
example (p q : Prop) (hp : p) (hq : q) : (p ∧ q) ∧ p := by
  refine ⟨⟨?_, hq⟩, ?_⟩
  · exact hp
  · exact hp

end Slide37

/-! ## Slide 41 — The case split, and what the audit says of it -/

namespace Slide41

-- On paper exc-thrd(A) := ⊥⊥ : A ∨ ¬A is primitive; in Lean it is a
-- theorem, and a script that uses it is classical:
theorem doubNeg (A : Prop) (u : ¬¬A) : A := by
  by_cases h : A               -- exc-thrd(A), as a case split
  · exact h
  · exact (u h).elim           -- ¬¬A and ¬A give ⊥, and ⊥-el

theorem doubNeg' (A : Prop) (u : ¬¬A) : A :=
  Classical.byContradiction u  -- assume ¬A, derive ⊥

theorem constructive (A : Prop) : A → ¬¬A := fun a f => f a

#print axioms doubNeg        -- depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms constructive   -- 'constructive' does not depend on any axioms

end Slide41

/-! ## Slide 43 — `obtain` is ∃-elimination -/

namespace Slide43

-- To use ∃x:S. P x while proving A, raise two flags, x : S and u : P x,
-- prove A under them, and ∃-el discharges both.  That is `obtain`.
example (S : Type) (P : S → Prop) (Q : Prop)
    (h : ∃ x, P x) (k : ∀ x, P x → Q) : Q := by
  obtain ⟨x, hx⟩ := h        -- raises the flags x : S and hx : P x
  exact k x hx               -- prove Q under them

-- ∃x.Px ⇒ ∀y.(Py ⇒ Qy) ⇒ ∃z.Qz, a six-line derivation in two:
example (S : Type) (P Q : S → Prop) (u : ∃ x, P x) (v : ∀ y, P y → Q y) :
    ∃ z, Q z := by
  obtain ⟨x, w⟩ := u         -- the flags x : S, w : P x
  exact ⟨x, v x w⟩           -- (1) v x, (2) a₁ w, (3) ∃-in, (5) ∃-el
-- The side condition: x must not occur free in the goal.  Lean enforces
-- it: the goal may not mention `x`.

end Slide43

/-! ## Slide 45 — The script is not the term -/

namespace Slide45

-- A derivation is checked from top to bottom, but devised the other way:
-- from the goal, with the failed attempts left unrecorded.
theorem demorgan (A B : Prop) (h : ¬A ∨ ¬B) : ¬(A ∧ B) := by
  intro hab                   -- backwards: from the goal
  cases h with
  | inl ha => exact ha hab.left
  | inr hb => exact hb hab.right

#print demorgan               -- forwards: only the result survives
-- fun A B h hab =>
--   Or.casesOn (motive := fun t => h = t → False) h
--     (fun ha h => ha hab.left) (fun hb h => hb hab.right) (Eq.refl h)
-- The `cases` became a recursor application.  The script is not the term.

end Slide45

/-! ## Slide 46 — Search in the environment: `exact?` -/

namespace Slide46

example (a b : Nat) : a + b = b + a := by exact?     -- Try this: exact Nat.add_comm a b
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by exact?   -- Try this: exact ⟨hp, hq⟩

end Slide46
