/-! # Simply typed λ-calculus — the Lean on the slides

Self-contained: needs only Lean 4 (v4.34.0-rc1 or later), no library.

How to run
* Install Lean via elan: https://lean-lang.org/install
* Open this file in VS Code with the "Lean 4" extension.  Results of
  `#eval`/`#check` appear in the Infoview; errors are underlined.
* Or, in a terminal: `lean simply-typed-lambda-calculus.lean`

`-- Slide N` names the page of the deck the code appears on.  Blocks marked
"support" are definitions the slides use but do not show.  Definition
numbers are Nederpelt & Geuvers, *Type Theory and Formal Proof*, ch. 2.
-/

set_option linter.unusedVariables false

/-! ## Slide 6 — 𝕋, as an `inductive` (Def. 2.2.1) -/

inductive Ty where
  | base  : String → Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq

infixr:25 " ⇒ " => Ty.arrow          -- infixr: right-associative

#check (Ty.base "α" ⇒ Ty.base "β" ⇒ Ty.base "α")
-- α ⇒ (β ⇒ α)

/-! ### Support: print a type as the book writes it, and two type variables -/

protected def Ty.repr : Ty → Nat → Std.Format
  | .base a,    _ => a
  | .arrow a b, p =>
      let f := f!"{a.repr 26} ⇒ {b.repr 25}"
      if p > 25 then Std.Format.paren f else f
instance : Repr Ty := ⟨Ty.repr⟩

def α : Ty := .base "α"
def β : Ty := .base "β"

/-! ## Slide 10 — The size argument, as a tactic proof (Ex. 2.2.6(3)) -/

def size : Ty → Nat
  | .base _    => 1
  | .arrow a b => size a + size b + 1

theorem arrow_ne (σ τ : Ty) : (σ ⇒ τ) ≠ σ := by
  intro h
  have := congrArg size h
  simp [size] at this
  omega

/-! ## Slide 11 — Ill-typed programs are rejected -/

def double (n : Nat) : Nat := 2 * n

/-- error: Application type mismatch: The argument
  "one"
has type
  String
but is expected to have type
  Nat
in the application
  double "one" -/
#guard_msgs in                    -- records the error Lean reports
def bad : Nat := double "one"

/-! ## Slide 13 — Lean is Church-typed underneath (§2.3) -/

set_option pp.funBinderTypes true

-- 1. Annotated binder: reaches the checker as written.
#check fun (x : Nat) => x         -- fun (x : Nat) => x : Nat → Nat
-- 2. Bare binder, expected type Nat → Nat: Nat is written on it.
#check (fun x => x : Nat → Nat)   -- fun (x : Nat) => x : Nat → Nat
-- 3. Bare binder, no expected type: the placeholder ?m.1 stays,
--    and a definition may not contain one.
#check fun x => x                 -- fun (x : ?m.1) => x : ?m.1 → ?m.1
-- rejected: "Failed to infer type of binder `x`"
#guard_msgs (drop error) in
def idc := fun x => x

/-! ## Slide 14 — Pre-typed terms Λ_T (Def. 2.4.1) -/

inductive TTerm where
  | var : String → TTerm
  | app : TTerm → TTerm → TTerm
  | lam : String → Ty → TTerm → TTerm
  deriving Repr, DecidableEq

-- Example 2.4.6's term, λy:α⇒β. λz:α. y z, as a value:
def ex246 : TTerm :=
  .lam "y" (α ⇒ β) (.lam "z" α (.app (.var "y") (.var "z")))

/-! ## Slide 16 — A context is a list (Def. 2.4.2) -/

abbrev Ctx := List (String × Ty)

#check ([("x", α), ("y", α ⇒ β)] : Ctx)

/-! ## Slide 21 — The three rules, as an `inductive` (Def. 2.4.5) -/

inductive Derives : Ctx → TTerm → Ty → Prop where
  | var {Γ x σ} :
      Γ.lookup x = some σ →                       -- (var)
      Derives Γ (.var x) σ
  | app {Γ M N σ τ} :
      Derives Γ M (σ ⇒ τ) → Derives Γ N σ →       -- (appl)
      Derives Γ (.app M N) τ
  | abs {Γ x M σ τ} :
      Derives ((x, σ) :: Γ) M τ →                 -- (abst)
      Derives Γ (.lam x σ M) (σ ⇒ τ)

notation:40 Γ " ⊢ " M " : " σ => Derives Γ M σ

/-! ## Slide 25 — That derivation, as a term (Example 2.4.6) -/

-- line (5), then (4), (3), (1) and (2) of the flag derivation
example : [] ⊢ ex246 : ((α ⇒ β) ⇒ α ⇒ β) :=
  .abs (.abs (.app (.var rfl) (.var rfl)))

/-! ## Slide 29 — The rules, read backwards, are an algorithm (Rem. 2.4.7) -/

def infer (Γ : Ctx) : TTerm → Option Ty
  | .var x     => Γ.lookup x
  | .app M N   =>
      match infer Γ M, infer Γ N with
      | some (σ ⇒ τ), some σ' => if σ = σ' then some τ else none
      | _,            _       => none
  | .lam x σ M => (infer ((x, σ) :: Γ) M).map (σ ⇒ ·)

#eval infer [] ex246                -- some ((α ⇒ β) ⇒ α ⇒ β)
#eval infer [] (.app ex246 ex246)   -- none

/-! ## Slide 32 — Soundness, in Lean -/

theorem infer_sound : ∀ {Γ M σ}, infer Γ M = some σ → Γ ⊢ M : σ
  | Γ, .var x,     σ, h => .var h          -- h is the side condition
  | Γ, .lam x ρ P, σ, h => by              -- σ is (ρ ⇒ τ), from some τ
      obtain ⟨τ, hP, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .abs (infer_sound hP)
  | Γ, .app P Q,   σ, h => by
      unfold infer at h
      split at h <;> try (cases h)         -- only the first arm answers
      rename_i ρ τ _ hP hQ
      split at h <;> cases h               -- and only if the test passed
      subst_vars
      exact .app (infer_sound hP) (infer_sound hQ)

/-! ## Slide 34 — Completeness, in Lean -/

theorem infer_complete {Γ M σ} (d : Γ ⊢ M : σ) :
    infer Γ M = some σ := by
  induction d with
  | var h           => simpa [infer] using h   -- the side condition
  | app _ _ ihM ihN => simp [infer, ihM, ihN]  -- the input types agree
  | abs _ ih        => simp [infer, ih]        -- prefix ρ ⇒

/-! ## Slide 35 — Decidability, as a tactic (Thm. 2.10.10(2)) -/

-- run `infer`; the two lemmas turn its answer into a verdict
instance (Γ : Ctx) (M : TTerm) (σ : Ty) : Decidable (Γ ⊢ M : σ) :=
  if h : infer Γ M = some σ then .isTrue (infer_sound h)
  else .isFalse fun d => h (infer_complete d)

example : [] ⊢ ex246 : ((α ⇒ β) ⇒ α ⇒ β) := by decide
example : ¬ ([] ⊢ .app ex246 ex246 : α)   := by decide

/-! ## Slide 38 — λ→ is too weak: three things Lean says that λ→ cannot -/

def id' {α : Type} (x : α) : α := x    -- one identity, for every type
#check (List : Type → Type)             -- a type built from a type
#check (Fin 3 : Type)                   -- a type mentioning a term
