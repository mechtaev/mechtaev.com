/-! # Propositional and predicate logic in λC — the Lean on the slides

Self-contained: needs only Lean 4 (v4.34.0-rc1 or later), no library.

How to run
* Install Lean via elan: https://lean-lang.org/install
* Open this file in VS Code with the "Lean 4" extension.  Results of
  `#eval`/`#check`/`#print` appear in the Infoview; errors are underlined.
* Or, in a terminal: `lean connectives.lean`

`-- Slide N` names the page of the deck the code appears on.  Section and
figure numbers are Nederpelt & Geuvers, *Type Theory and Formal Proof*,
ch. 7.  Each slide sits in its own `section`; the book's codings `And₂`,
`Or₂`, `Ex₂` are defined once, on the slide that introduces them, and
reused after.
-/

set_option linter.unusedVariables false

/-! ## Slide 08 — `False` and `Not`, in Lean (§7.1, Rem. 7.1.1–7.1.2) -/

section
-- §7.1: ⊥ := Πα:∗. α, and ⊥-elim is one (appl)
def Bot : Prop := ∀ α : Prop, α
theorem bot_elim (f : Bot) (A : Prop) : A := f A

-- Lean: False has no constructor; Not is the same abbreviation
#print False           -- inductive False : Prop   (no constructors)
#print Not             -- def Not : Prop → Prop := fun a => a → False
#check @False.elim     -- {C : Sort u_1} → False → C
#check @absurd         -- {a : Prop} → {b : Sort u_1} → a → ¬a → b

-- the two readings of "empty" agree, in both directions
example : False → Bot := fun h _ => h.elim
example : Bot → False := fun f => f False
end

/-! ## Slide 09 — A set is not a statement (§7.1, Rem. 7.1.2) -/

section
#check (2 = 3) → False     -- 2 = 3 → False : Prop         ¬(2 = 3)
#check Nat → False         -- ∀ (a : Nat), False : Prop    "Nat is empty": a proposition too
example : (Nat → False) → False := fun h => h 0            -- and 0 refutes it
#check_failure ¬ Nat       -- Nat has type Type but is expected to have type Prop
end

/-! ## Slide 12 — `And`, in Lean (§7.2 I) -/

section
-- §7.2 I: A ∧ B := ΠC:∗. (A → B → C) → C, typed in Prop (impredicative)
def And₂ (A B : Prop) : Prop := ∀ C : Prop, (A → B → C) → C

-- the three rules, derived from the coding
theorem And₂.intro {A B : Prop} (x : A) (y : B) : And₂ A B := fun _ z => z x y
theorem And₂.left  {A B : Prop} (u : And₂ A B) : A := u A (fun x _ => x)
theorem And₂.right {A B : Prop} (u : And₂ A B) : B := u B (fun _ y => y)

-- Lean's And: an inductive type with the same three rules
#print And             -- structure And (a b : Prop) : Prop
                       --   fields: And.left : a   And.right : b
#check @And.intro      -- ∀ {a b : Prop}, a → b → a ∧ b
example (A B : Prop) (h : A ∧ B) : B ∧ A := ⟨h.right, h.left⟩
end

/-! ## Slide 16 — `Or`, in Lean (§7.2 II) -/

section
-- A ∨ B := ΠC:∗. (A → C) → (B → C) → C
def Or₂ (A B : Prop) : Prop := ∀ C : Prop, (A → C) → (B → C) → C
theorem Or₂.inl  {A B : Prop} (x : A) : Or₂ A B := fun _ f _ => f x
theorem Or₂.elim {A B C : Prop} (x : Or₂ A B) (y : A → C) (z : B → C) : C :=
  x C y z

#print Or              -- inductive Or : Prop → Prop → Prop
                       --   Or.inl : a → a ∨ b     Or.inr : b → a ∨ b
#check @Or.elim        -- ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c

-- ∨-elim, then ∨-intro-right and ∨-intro-left
example (A B : Prop) (h : A ∨ B) : B ∨ A :=
  h.elim (fun a => Or.inr a) (fun b => Or.inl b)
example (A B : Prop) (h : A ∨ B) : B ∨ A :=    -- the same, by pattern
  match h with
  | .inl a => .inr a
  | .inr b => .inl b
end

/-! ## Slide 17 — Biimplication (Rem. 7.3.1) -/

section
-- Rem. 7.3.1: A ⇔ B := (A ⇒ B) ∧ (B ⇒ A).  Lean: a structure with two fields.
#print Iff             -- structure Iff (a b : Prop) : Prop
                       --   fields: Iff.mp : a → b   Iff.mpr : b → a
#check @Iff.intro      -- ∀ {a b : Prop}, (a → b) → (b → a) → (a ↔ b)

example (A B : Prop) (h : A ↔ B) (a : A) : B := h.mp a
example (A B : Prop) : (A ∧ B) ↔ (B ∧ A) :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
end

/-! ## Slide 19 — The same proof, as one term (Fig. 7.1) -/

section
-- the proof object of (A ∨ B) ⇒ (¬A ⇒ B), line (10) of the derivation
theorem or_neg (A B : Prop) : A ∨ B → ¬A → B :=
  fun x y => x.elim (fun u => (y u).elim) (fun v => v)

#print or_neg
-- theorem or_neg : ∀ (A B : Prop), A ∨ B → ¬A → B :=
-- fun A B x y => Or.elim x (fun u => False.elim (y u)) fun v => v
end

/-! ## Slide 22 — The excluded third, in Lean -/

section
-- the excluded third as a flag in front of the context: a parameter em
theorem dn (q : Prop) (em : ∀ p : Prop, p ∨ ¬p) (h : ¬¬q) : q :=
  (em q).elim (fun y => y) (fun z => (h z).elim)
#print axioms dn        -- 'dn' does not depend on any axioms

-- as a library constant: Classical.em discharges the flag
#check Classical.em                 -- Classical.em (p : Prop) : p ∨ ¬p
#check @Classical.byContradiction   -- ∀ {p : Prop}, (¬p → False) → p
theorem dn' (q : Prop) (h : ¬¬q) : q := dn q Classical.em h
#print axioms dn'
-- 'dn'' depends on axioms: [propext, Classical.choice, Quot.sound]
end

/-! ## Slide 25 — `Exists`, in Lean (§7.5) -/

section
-- ∃x:S. P x := Πα:∗. ((Πx:S. P x → α) → α)
def Ex₂ (S : Type) (P : S → Prop) : Prop :=
  ∀ α : Prop, (∀ x : S, P x → α) → α
theorem Ex₂.intro {S : Type} {P : S → Prop} (a : S) (u : P a) : Ex₂ S P :=
  fun _ v => v a u
theorem Ex₂.elim {S : Type} {P : S → Prop} {A : Prop}
    (y : Ex₂ S P) (z : ∀ x, P x → A) : A := y A z

#print Exists          -- inductive Exists : (α → Prop) → Prop
                       --   Exists.intro (w : α) : p w → Exists p
example : ∃ n : Nat, n + n = 6 := ⟨3, rfl⟩        -- the witness, then the proof
example (S : Type) (P : S → Prop) (h : ∃ x, P x) (k : ∀ x, P x → False) :
    False :=
  match h with                                     -- ∃-el: open the flag
  | ⟨w, hw⟩ => k w hw
end

/-! ## Slide 26 — The witness stays inside the flag (§7.5) -/

section
-- the conclusion A may not mention the witness x.
-- Lean's version of the side condition is a sort: an Exists in Prop may
-- only be eliminated into a Prop, so no function can return the witness.
#guard_msgs(drop error) in
def witness (h : ∃ n : Nat, n + n = 6) : Nat :=
  match h with
  | ⟨w, _⟩ => w
-- error: recursor 'Exists.casesOn' can only eliminate into Prop

theorem witness' (h : ∃ n : Nat, n + n = 6) : ∃ m : Nat, m + m + 2 = 8 :=
  match h with                                     -- into Prop: accepted
  | ⟨w, hw⟩ => ⟨w, by omega⟩
end

/-! ## Slide 28 — The same proof, as one term (§7.6) -/

section
-- the proof object of ¬∃x:S. P x ⇒ ∀y:S. ¬P y, line (5) of the derivation
theorem not_ex (S : Type) (P : S → Prop) : ¬(∃ x, P x) → ∀ y, ¬P y :=
  fun u y v => u ⟨y, v⟩

#print not_ex
-- theorem not_ex : ∀ (S : Type) (P : S → Prop), (¬∃ x, P x) → ∀ (y : S), ¬P y :=
-- fun S P u y v => u (Exists.intro y v)

-- with the coding instead of Lean's Exists, line (1) reappears:
theorem not_ex' (S : Type) (P : S → Prop) : ¬(Ex₂ S P) → ∀ y, ¬P y :=
  fun u y v => u (fun _ w => w y v)
end

/-! ## Slide 32 — `intro` raises a flag, `exact` fills the hole -/

section
theorem diag' (S : Type) (Q : S → S → Prop) :
    (∀ x y : S, Q x y) → ∀ u : S, Q u u := by
  intro z        -- z : ∀ x y, Q x y          ⊢ ∀ u, Q u u
  intro u        -- z : ∀ x y, Q x y,  u : S  ⊢ Q u u
  exact z u u    -- no goals

#print diag'
-- theorem diag' : ∀ (S : Type) (Q : S → S → Prop),
--     (∀ (x y : S), Q x y) → ∀ (u : S), Q u u :=
--   fun S Q z u => z u u
end

/-! ## Slide 33 — `apply` leaves a hole -/

section
theorem chain (p q r : Prop) (hpq : p → q) (hqr : q → r) :
    p → r := by
  intro hp      -- ⊢ r     term so far:  fun hp => ?m
  apply hqr     -- ⊢ q                   fun hp => hqr ?m
  apply hpq     -- ⊢ p                   fun hp => hqr (hpq ?m)
  exact hp      -- no goals              fun hp => hqr (hpq hp)

#print chain
-- theorem chain : ∀ (p q r : Prop), (p → q) → (q → r) → p → r :=
--   fun p q r hpq hqr hp => hqr (hpq hp)
end

/-! ## Slide 36 — ∧, ∨, ∃: the rules as tactics -/

section
example (A B : Prop) (h : A ∧ B) : B ∧ A := by
  obtain ⟨a, b⟩ := h        -- ∧-el: two flags  a : A,  b : B
  constructor               -- ∧-in: two goals, B and A
  · exact b
  · exact a

example (A B : Prop) (h : A ∨ B) : B ∨ A := by
  rcases h with a | b       -- ∨-el: one goal per case
  · right; exact a          -- ∨-in₂
  · left;  exact b          -- ∨-in₁

example (S : Type) (P Q : S → Prop) (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  obtain ⟨w, _, hq⟩ := h    -- ∃-el then ∧-el: flags  w : S,  hq : Q w
  exact ⟨w, hq⟩             -- ∃-in
end

/-! ## Slide 37 — ¬, ⊥, ∀, ⇔: the rules as tactics -/

section
example (A : Prop) (h : ¬A) (a : A) : False := by exact h a      -- ¬-el
example (A : Prop) (a : A) : ¬¬A := by                           -- ¬-in
  intro h; exact h a
example (A : Prop) (h : False) : A := by exact h.elim            -- ⊥-el
example (A : Prop) (h : False) : A := by contradiction           -- the same

example (S : Type) (P : S → Prop) (h : ∀ x, P x) (a : S) : P a := by
  apply h                                                        -- ∀-el
example (S : Type) (P : S → Prop) (h : ∀ x, P x ∧ P x) : ∀ y, P y := by
  intro y; exact (h y).1                                         -- ∀-in

example (A B : Prop) (f : A → B) (g : B → A) : A ↔ B := by
  constructor                                                    -- ⇔-in
  · exact f
  · exact g
end

/-! ## Slide 38 — The propositional proof, as a script (Fig. 7.1) -/

section
theorem or_neg' (A B : Prop) :
    A ∨ B → ¬A → B := by
  intro x y          -- flags (c), (d)
  apply x.elim       -- ∨-el, backwards
  · intro u          -- flag (e)
    exact absurd u y -- (2), (3)
  · intro v          -- flag (f)
    exact v          -- (6)

#print or_neg'
-- theorem or_neg' : ∀ (A B : Prop),
--     A ∨ B → ¬A → B :=
-- fun A B x y =>
--   Or.elim x (fun u => absurd u y)
--     fun v => v
end
