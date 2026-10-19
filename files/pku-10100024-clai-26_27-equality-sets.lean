/-! # Equality, and sets as predicates — the Lean on the slides

Self-contained: needs only Lean 4 (v4.34.0-rc1 or later), no library.

How to run
* Install Lean via elan: https://lean-lang.org/install
* Open this file in VS Code with the "Lean 4" extension.  Results of
  `#eval`/`#check`/`#print` appear in the Infoview; errors are underlined.
* Or, in a terminal: `lean equality-sets.lean`

`-- Slide N` names the page of the deck the code appears on.  Each slide
sits in its own namespace, so a name defined on one slide (`d`, `LEq`,
`iota`) can be defined afresh on another; the subset definitions of
slide 32 stay at top level, since later slides use them.  The block marked
"support" holds definitions the slides use but do not show.  Expected errors are
wrapped in `#guard_msgs(drop error) in`, as on the slides.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Slide 07 — Leibniz equality, written out -/

namespace Slide07

-- eq(S,x,y) := ΠP : S → ∗ₚ. (P x ⇔ P y)
-- "x and y are equal iff they are INDISCERNIBLE by any predicate."
def LEq {S : Type} (x y : S) : Prop := ∀ P : S → Prop, P x ↔ P y

-- reflexivity: for every P, ⇔-refl, which Lean calls Iff.rfl
theorem leq_refl {S : Type} (x : S) : LEq x x := fun _ => Iff.rfl

-- ⇒ instead of ⇔ would already do: P x ⇒ P y for all P gives the converse.
def LEq' {S : Type} (x y : S) : Prop := ∀ P : S → Prop, P x → P y

-- The Π ranges over PREDICATES, P : S → ∗ₚ, and S → ∗ₚ : □.  So this is
-- a SECOND-ORDER definition, not a first-order ∀ over elements.
#check @LEq     -- @LEq : {S : Type} → S → S → Prop

end Slide07

/-! ## Slide 09 — What Lean uses instead -/

namespace Slide09

-- Lean does not use Leibniz's definition.  `Eq` is an inductive with ONE
-- constructor, and its recursor is what substitutivity becomes.
#print Eq
-- inductive Eq.{u_1} : {α : Sort u_1} → α → α → Prop
-- number of parameters: 2
-- constructors: Eq.refl : ∀ {α : Sort u_1} (a : α), a = a

#check @Eq.subst
-- ∀ {α : Sort u_1} {motive : α → Prop} {a b : α}, a = b → motive a → motive b
-- Compare eq-subs(S,P,x,y,u,v) : P y.  Same shape; the predicate P is
-- what Lean calls the `motive`.

end Slide09

/-! ## Slide 10 — The two agree -/

namespace Slide10

-- (declared on an earlier slide)
def LEq {S : Type} (x y : S) : Prop := ∀ P : S → Prop, P x ↔ P y

-- The two notions coincide.  One direction substitutes along h,
-- starting from reflexivity ...
theorem eq_to_leq {S : Type} {x y : S} (h : x = y) : LEq x y :=
  fun P => h ▸ Iff.rfl

-- ... the other instantiates the quantifier at the predicate (x = ·):
-- once more, the proof is the choice of predicate.
theorem leq_to_eq {S : Type} {x y : S} (h : LEq x y) : x = y :=
  (h (fun z => x = z)).mp rfl

end Slide10

/-! ## Slide 13 — "motive is not type correct" -/

namespace Slide13

-- `rw` builds the MOTIVE Q by abstracting `n` out of the goal, then checks
-- it.  Here the goal mentions `v : Fin (n+1)` (a natural below n+1, bundled
-- with that proof), whose TYPE mentions n — so the abstraction is ill-typed:
#guard_msgs(drop error) in
example (n m : Nat) (v : Fin (n + 1)) (h : n = m) : v.val < n + 1 := by
  rw [h]
-- Tactic `rewrite` failed: motive is not type correct:
--   fun _a => ↑v < _a + 1
-- Error: Application type mismatch: The argument  v  has type
--   Fin (n + 1)  but is expected to have type  Fin (_a + 1) ...

-- Two cures: `subst` replaces n EVERYWHERE, v's type included; `▸` takes
-- the motive from the proof term's type instead of from the goal.
example (n m : Nat) (v : Fin (n + 1)) (h : n = m) : v.val < n + 1 := by
  subst h; exact v.isLt
example (n m : Nat) (v : Fin (n + 1)) (h : n = m) : v.val < n + 1 :=
  h ▸ v.isLt

end Slide13

/-! ## Slide 15 — Motives in Lean -/

namespace Slide15

-- Congruence: the motive inferred from the goal, or given.
theorem cong' {S T : Type} (f : S → T) {x y : S} (h : x = y) : f x = f y :=
  h ▸ rfl                                       -- motive inferred
theorem cong'' {S T : Type} (f : S → T) {x y : S} (h : x = y) : f x = f y :=
  @Eq.subst S (fun z => f x = f z) x y h rfl    -- motive Q₁

-- Symmetry and transitivity, with Q₂ and Q₃ given.
theorem sym' {S : Type} {x y : S} (h : x = y) : y = x :=
  @Eq.subst S (fun z => z = x) x y h rfl        -- Q₂ x is x = x
theorem trans' {S : Type} {x y z : S} (h : x = y) (k : y = z) : x = z :=
  @Eq.subst S (fun w => x = w) y z k h          -- Q₃ y is x = y

-- In the library: `congrArg`, `Eq.symm`, `Eq.trans`.

end Slide15

/-! ## Slide 16 — `rw` chooses the motive for you -/

namespace Slide16

-- `rw [h]` is eq-subs with the predicate chosen FOR you: it abstracts every
-- occurrence of h's left side out of the goal, and that abstraction is Q.
theorem rw1 (a b : Nat) (h : a = b) (f : Nat → Nat) : f a + a = f b + b := by
  rw [h]           -- Q := fun z => f z + z = f b + b; the rest is Eq.refl

example (a b : Nat) (h : a = b) (k : b = 0) : a = 0 := by
  rw [h, k]        -- one equation after another, each left to right
example (a b : Nat) (h : b = a) : a = b := by
  rw [← h]         -- right to left
example (a b : Nat) (h : a = b) (k : a + 1 = 5) : b + 1 = 5 := by
  rw [h] at k; exact k                 -- in a hypothesis

#print rw1
-- fun a b h f => Eq.mpr (id (congrArg (fun _a => f _a + _a = f b + b) h))
--                       (Eq.refl (f b + b))

end Slide16

/-! ## Slide 17 — Chains of steps: `calc` -/

namespace Slide17

-- `calc` chains equalities step by step.  Each step names its
-- justification; transitivity is applied for you.
def d (n : Nat) : Nat := n + n

example (a b : Nat) (h : a = b) (k : b = 5) : d a = 10 :=
  calc d a = d b := by rw [h]      -- congruence
    _      = d 5 := by rw [k]
    _      = 10  := rfl              -- definitional: δ, then arithmetic

-- Mixed relations chain too; the result is the strongest one used.
example (a b c e : Nat) (h₁ : a ≤ b) (h₂ : b < c) (h₃ : c ≤ e) : a < e :=
  calc a ≤ b := h₁
    _ < c := h₂
    _ ≤ e := h₃

end Slide17

/-! ## Slide 21 — The same proof, as named lines -/

namespace Slide21

-- (declared on an earlier slide)
def Refl {S : Type} (le : S → S → Prop) : Prop := ∀ x, le x x
def Trans' {S : Type} (le : S → S → Prop) : Prop :=
  ∀ x y z, le x y → le y z → le x z
def Antisymm {S : Type} (le : S → S → Prop) : Prop :=
  ∀ x y, le x y → le y x → x = y
def PreOrd {S : Type} (le : S → S → Prop) : Prop := Refl le ∧ Trans' le
def PartOrd {S : Type} (le : S → S → Prop) : Prop := PreOrd le ∧ Antisymm le

-- The flag derivation, line for line.  A `have` is a named line; `exact`
-- is the last.
theorem least_unique {S : Type} (le : S → S → Prop) (r : PartOrd le)
    (m₁ m₂ : S) (u : ∀ n, le m₁ n) (v : ∀ n, le m₂ n) : m₁ = m₂ := by
  have a₁ : le m₁ m₂ := u m₂                  -- (1)  ∀-el on u
  have a₂ : le m₂ m₁ := v m₁                  -- (2)  ∀-el on v
  have a₄ : Antisymm le := r.2                -- (3)–(4)  ∧-el₂ on r
  have a₆ : le m₁ m₂ → le m₂ m₁ → m₁ = m₂ := a₄ m₁ m₂   -- (5)–(6)
  exact a₆ a₁ a₂                              -- (7)–(8)

#print least_unique
-- fun {S} le r m₁ m₂ u v => have a₁ := u m₂; have a₂ := v m₁;
--   have a₄ := r.right; have a₆ := a₄ m₁ m₂; a₆ a₁ a₂

end Slide21

/-! ## Slide 24 — Where `rfl` stops, and what takes over -/

namespace Slide24

-- `Nat.add` recurses on its SECOND argument, so one of these computes and
-- the other is stuck on the variable n:
example (n : Nat) : n + 0 = n := rfl
#guard_msgs(drop error) in
example (n : Nat) : 0 + n = n := rfl
-- The type of `Eq.refl ?a` ... is not definitionally equal to `0 + n = n`

-- What closes it is a theorem from Δ — proved by induction, next lecture:
example (n : Nat) : 0 + n = n := Nat.zero_add n

-- With n closed, computation is back, and `decide` runs it in the kernel:
example : 0 + 5 = 5 := by decide

end Slide24

/-! ## Slide 28 — `Classical.choose` is ι -/

namespace Slide28

-- ∃¹ is "at least one" and "at most one".  Core Lean has no ∃¹, so the
-- definition is written out.
def ExUnique {S : Type} (P : S → Prop) : Prop :=
  (∃ x, P x) ∧ ∀ y z, P y → P z → y = z

-- ι(S,P,u) := ⊥⊥ : S  and  ι-prop(S,P,u) := ⊥⊥ : P (ι ...).
-- Lean's are `Classical.choose` and `choose_spec`, built on an axiom:
noncomputable def iota {S : Type} (P : S → Prop) (u : ExUnique P) : S :=
  Classical.choose u.1
theorem iota_prop {S : Type} (P : S → Prop) (u : ExUnique P) : P (iota P u) :=
  Classical.choose_spec u.1
#print axioms iota_prop     -- 'iota_prop' depends on axioms: [Classical.choice]

-- Whatever satisfies P is the ι.
theorem eq_iota {S : Type} (P : S → Prop) (u : ExUnique P) (z : S) (v : P z) :
    z = iota P u := u.2 z _ v (iota_prop P u)

end Slide28

/-! ## Slide 29 — Irrelevance of proof -/

namespace Slide29

-- (declared on an earlier slide)
def ExUnique {S : Type} (P : S → Prop) : Prop :=
  (∃ x, P x) ∧ ∀ y z, P y → P z → y = z
noncomputable def iota {S : Type} (P : S → Prop) (u : ExUnique P) : S :=
  Classical.choose u.1

-- λD does not make proof irrelevance a principle.  Lean's kernel has it
-- for Prop, definitionally: two proofs of one proposition are rfl-equal.
example (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := rfl

-- So the worry that ι(S,P,u₁) and ι(S,P,u₂) might differ
-- cannot even be stated as a difference:
example {S : Type} (P : S → Prop) (u₁ u₂ : ExUnique P) :
    iota P u₁ = iota P u₂ := rfl

-- What keeps it consistent: a proof may not be turned into DATA.  A Prop's
-- recursor eliminates only into Prop, so no function can tell two
-- proofs apart:
#guard_msgs(drop error) in
def theWitness (h : ∃ n : Nat, 3 < n) : Nat := match h with | ⟨n, _⟩ => n
-- error: recursor `Exists.casesOn` can only eliminate into `Prop`

end Slide29

/-! ## Slide 32 — ps(S) in Lean (top level: later slides use it) -/

-- Lean core has no `Set`; these lines are all of it.
abbrev PS (S : Type) : Type := S → Prop                   -- (1) ps(S)
def Mem {S : Type} (V : PS S) (x : S) : Prop := V x       -- (2) x ε V
instance {S : Type} : Membership S (PS S) := ⟨Mem⟩        -- write x ∈ V
def Subs {S : Type} (V W : PS S) : Prop :=                -- (3) V ⊆ W
  ∀ x : S, x ∈ V → x ∈ W
infix:50 " ⊑ " => Subs
def IS {S : Type} (V W : PS S) : Prop := V ⊑ W ∧ W ⊑ V    -- same elements
def diff {S : Type} (V W : PS S) : PS S := fun x => x ∈ V ∧ ¬ x ∈ W  -- V \ W
def compl {S : Type} (V : PS S) : PS S := fun x => ¬ x ∈ V           -- V^c

example (S : Type) (V W : PS S) :
    (V ⊑ W) = ∀ x : S, x ∈ V → x ∈ W := rfl     -- the guarded ∀, verbatim

-- support: set-builder notation, which the slides mention but do not show.
def sep {S : Type} (P : S → Prop) : PS S := P
notation "{" x " | " p "}" => sep (fun x => p)

/-! ## Slide 33 — Membership needs a proof -/

namespace Slide33

-- x ∈ V is not a typing x : V but a PROPOSITION.  To establish it we
-- have to give a PROOF.
def Evens : PS Nat := fun n => n % 2 = 0

-- `4 ∈ Evens` unfolds to `4 % 2 = 0`, so a computation proves it.
example : 4 ∈ Evens := show 4 % 2 = 0 by decide
#guard_msgs(drop error) in
example : 5 ∈ Evens := show 5 % 2 = 0 by decide   -- fails: 5 % 2 = 1

-- `n ∈ Evens` IS `n % 2 = 0`, up to unfolding: a proof of one is a
-- proof of the other, with nothing to convert.
example (n : Nat) (h : n % 2 = 0) : n ∈ Evens := h

end Slide33

/-! ## Slide 35 — Guarded quantifiers -/

namespace Slide35

-- (declared on an earlier slide)
def Evens : PS Nat := fun n => n % 2 = 0

-- ∀x ∈ Evens. x·x is even:  quantify over Nat, guard with ⇒.
example : ∀ x : Nat, x ∈ Evens → (x * x) % 2 = 0 := by
  intro x (hx : x % 2 = 0)                 -- any x, assuming the guard
  simp [Nat.mul_mod, hx]

-- ∃x ∈ Evens. x > 3:  guard with ∧; the witness 4 meets both halves.
example : ∃ x : Nat, x ∈ Evens ∧ x > 3 :=
  ⟨4, show 4 % 2 = 0 by decide, by decide⟩

-- With ⇒ instead, x = 1 would do: 1 ∉ Evens makes the ⇒ vacuous.
example : ∃ x : Nat, x ∈ Evens → x > 1000 :=
  ⟨1, fun h => absurd (show 1 % 2 = 0 from h) (by decide)⟩

end Slide35

/-! ## Slide 37 — The same proof, as a script -/

namespace Slide37

-- The flag derivation, as a script.  `intro x v` raises the flags x : S
-- and v; the hints "use ∧-el₁", "use ∧-in", "use ⇒-in and ∀-in" become
-- `.1`, `⟨_, _⟩` and `intro`.
theorem diff_eq {S : Type} (V W : PS S) (u : V ⊑ compl W) :
    IS (diff V W) V := by
  constructor
  · intro x v                          -- lines (1)–(4): no use of u
    exact v.1                          -- (2) ∧-el₁ on v : x ε V ∧ ¬(x ε W)
  · intro x v                          -- lines (5)–(10)
    have a₅ : x ∈ compl W := u x v     -- (5) u x v : x ε W^c
    exact ⟨v, a₅⟩                      -- (7)–(8) ∧-in: x ε V\W

-- The second half needs u and the first does not, and the parameter
-- lists show it (a₄(S,V,W) against a₁₀(S,V,W,u)).

end Slide37

/-! ## Slide 40 — Subtypes in Lean -/

namespace Slide40

-- Bundle the element WITH its proof:
-- the proof is carried, not searched for.
def NonNeg := {n : Int // 0 ≤ n}

def three : NonNeg := ⟨3, by decide⟩
#eval three.val        -- 3
#check three.property
-- three.property : 0 ≤ three.val

-- The cost: `3 : Int` and `three : NonNeg`
-- are different terms of different types;
-- a coercion moves between them.
-- `Fin n` is `{i : Nat // i < n}`.

end Slide40

/-! ## Slide 41 — Extensionality is an axiom -/

namespace Slide41

-- Same elements, different terms: 0 + n does not compute to n.
def A : PS Nat := fun n => 0 + n = 5
def B : PS Nat := fun n => n = 5
theorem same_elements : ∀ x, x ∈ A ↔ x ∈ B := by
  intro x; show 0 + x = 5 ↔ x = 5; rw [Nat.zero_add]

#guard_msgs(drop error) in
example : A = B := rfl          -- fails: equality compares the terms

-- The axioms: functions equal pointwise, propositions equal if ↔.
theorem setext {α : Type} {V W : PS α} (h : ∀ x, x ∈ V ↔ x ∈ W) : V = W :=
  funext (fun x => propext (h x))
example : A = B := setext same_elements

#print axioms setext  -- [propext, Quot.sound]: funext comes from quotients

end Slide41
