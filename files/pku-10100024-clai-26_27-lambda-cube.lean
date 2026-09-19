/-! # The λ-cube and propositions-as-types — the Lean on the slides

Self-contained: needs only Lean 4 (v4.34.0-rc1 or later), no library.

How to run
* Install Lean via elan: https://lean-lang.org/install
* Open this file in VS Code with the "Lean 4" extension.  Results of
  `#eval`/`#check`/`#print` appear in the Infoview; errors are underlined.
* Or, in a terminal: `lean lambda-cube.lean`

`-- Slide N` names the page of the deck the code appears on.  Section and
definition numbers are Nederpelt & Geuvers, *Type Theory and Formal Proof*,
ch. 3–6.  Each slide sits in its own `section`, so a name a slide
introduces with `variable` or `universe` does not leak into the next.
-/

set_option linter.unusedVariables false

/-! ## Slide 15 — Type abstraction, in Lean (λ2: Ex. 3.1.1, Def. 3.3.1, 3.3.2) -/

section
-- λα:∗. λx:α. x  :  Πα:∗. α → α
def idPoly : (α : Type) → α → α :=
  fun α x => x

#check idPoly Nat               -- idPoly Nat : Nat → Nat
#eval  idPoly Nat 3             -- 3
#eval  idPoly String "three"    -- "three"

-- braces: the type argument is still there, but Lean finds it
def idImp {α : Type} (x : α) : α := x

-- `@` switches the braces off, so that the whole type is shown
#check @idImp                   -- @idImp : {α : Type} → α → α
#eval  idImp 3                  -- 3            α := Nat
end

/-! ## Slide 26 — Constructors and kinds, in Lean (§4.1, Def. 4.1.4, 4.1.6) -/

section
def SelfMap : Type → Type := fun α => α → α     -- λα:∗. α → α

-- level 1, a term
#check (fun n => n + 1 : SelfMap Nat)   -- fun n => n + 1 : Nat → Nat
-- level 2, a type, and a proper constructor
#check SelfMap Nat              -- SelfMap Nat : Type
#check (SelfMap)                -- SelfMap : Type → Type
-- level 3, a kind
#check Type → Type              -- Type → Type : Type 1

-- Lean's library is full of proper constructors
#check (List : Type → Type)
#check (Prod : Type → Type → Type)
end

/-! ## Slide 27 — (conv) in Lean: definitional equality (Def. 4.7.1) -/

section
-- `SelfMap` is the constructor of slide 26.
#reduce (types := true) SelfMap Nat     -- Nat → Nat

-- declared at one spelling of the type, used at the other
def succ' : SelfMap Nat := fun n => n + 1
#check (succ' : Nat → Nat)              -- accepted
#eval  succ' 3                          -- 4

-- the side condition of (conv), stated and proved
example : SelfMap Nat = (Nat → Nat) := rfl
end

/-! ## Slide 36 — Types depending on terms, in Lean (§5.1, §5.2) -/

section
def Vec (α : Type) : Nat → Type          -- a family: λn:nat. Vₙ
  | 0     => Unit
  | n + 1 => α × Vec α n
#check Vec Nat                  -- Vec Nat : Nat → Type
#check ((3, 4, ()) : Vec Nat 2)

def zeros : (n : Nat) → Vec Nat n        -- a term of a Π-type
  | 0     => ()
  | n + 1 => (0, zeros n)
#check zeros 2                  -- zeros 2 : Vec Nat 2
#eval  zeros 2                  -- (0, 0, ())

def IsPrime (n : Nat) : Prop :=          -- a predicate: λn:nat. Pₙ
  2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n
#check (IsPrime)                -- IsPrime : Nat → Prop
end

/-! ## Slide 44 — `theorem` is `def` (§5.4) -/

section
def     idData (A : Type) : A → A := fun a => a
theorem idProp (A : Prop) : A → A := fun a => a

#print idData
-- def idData : (A : Type) → A → A := fun A a => a
#print idProp
-- theorem idProp : ∀ (A : Prop), A → A := fun A a => a

#print False
-- inductive False : Prop
-- number of parameters: 0
-- constructors:
end

/-! ## Slide 45 — Π-types, in Lean (§3.2, Notation 5.2.1, Fig. 5.2) -/

section
-- typed as (x : A) → B
#check (α : Type) → α → α         -- (α : Type) → α → α : Type 1
#check (n : Nat) → Nat            -- Nat → Nat : Type
#check (n : Nat) → n = n          -- ∀ (n : Nat), n = n : Prop

-- typed as ∀ x : A, B
#check ∀ α : Type, α → α          -- (α : Type) → α → α : Type 1
#check ∀ n : Nat, n = n           -- ∀ (n : Nat), n = n : Prop
end

/-! ## Slide 46 — Using and proving ∀ and ⇒, in Lean (§5.4) -/

section
variable (S : Type) (P : S → Prop)

-- (∀-elim) is (appl): apply the proof to the element
example (h : ∀ x : S, P x) (a : S) : P a := h a

-- (∀-intro) is (abst): abstract over an arbitrary element
example (h : ∀ x : S, P x) : ∀ y : S, P y := fun y => h y

-- (⇒-elim) and (⇒-intro) are the same two rules
example (A B : Prop) (f : A → B) (a : A) : B := f a
example (A : Prop) : A → A := fun a => a
end

/-! ## Slide 49 — The proof object, in Lean (§5.5) -/

section
theorem diag (S : Type) (Q : S → S → Prop) :
    (∀ x y : S, Q x y) → ∀ u : S, Q u u :=
  fun z u => z u u

#check diag
-- diag (S : Type) (Q : S → S → Prop) :
--   (∀ (x y : S), Q x y) → ∀ (u : S), Q u u
end

/-! ## Slide 54 — Which corner is Lean? (§6.1, Fig. 6.2) -/

section
#check Nat → Nat                  -- : Type           (∗,∗)
#check ∀ p : Prop, p → p          -- : Prop           (□,∗)
#check fun (α : Type) => α → α    -- : Type → Type    (□,□)
#check fun (n : Nat) => n = n     -- : Nat → Prop     (∗,□)

-- (□,∗) over Prop stays in Prop; over Type it climbs one step
#check ∀ α : Type, α → α          -- : Type 1
end

/-! ## Slide 57 — The three problems, in Lean (§2.6, Thm. 6.3.15) -/

section
variable (S : Type) (Q : S → S → Prop)

-- 1. Well-typedness: from the term alone, Lean computes a type
#check fun (z : ∀ x y, Q x y) (u : S) => z u u
-- fun z u => z u u : (∀ (x y : S), Q x y) → ∀ (u : S), Q u u

-- 2. Type Checking: from the term and the type, Lean answers yes or no
example : (∀ x y, Q x y) → ∀ u, Q u u := fun z u => z u u    -- yes
#guard_msgs (drop error) in
example : (∀ x y, Q x y) → ∀ u, Q u u := fun z u => z u      -- no
-- error: z u has type ∀ (y : S), Q u y, but Q u u is expected

-- 3. Term Finding: from the type alone, Lean does not search
#guard_msgs (drop error) in
example : (∀ x y, Q x y) → ∀ u, Q u u := _
-- error: don't know how to synthesize placeholder
end
