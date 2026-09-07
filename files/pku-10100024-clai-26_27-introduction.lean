import Std.Internal.Do
/-! # Introduction — the Lean on the slides

Self-contained: needs only Lean 4 (v4.34.0-rc1 or later).

How to run
* Install Lean via elan: https://lean-lang.org/install
* Open this file in VS Code with the "Lean 4" extension.  Results of
  `#eval`/`#check` appear in the Infoview; errors are underlined.
* Or, in a terminal: `lean introduction.lean`

`-- Slide N` names the page of the deck the code appears on.
-/
set_option mvcgen.warning false

/-! ## Slide 5 — Lean's foundation: the Curry–Howard correspondence

A proposition is a type and a proof is a term, so checking the proof is
type checking. -/

theorem S (p q r : Prop) :
  (p → q → r) → (p → q) → (p → r) :=
  fun f g a => f a (g a)

#check S      -- S (p q r : Prop) : (p → q → r) → (p → q) → p → r

/-! ## Slide 10 — Why the course covers all of this

Where the course ends: a program that ships with a machine-checked proof.
A scoring rule, a lemma about it proved by induction, then a stateful loop
carrying a contract (`requires`/`ensures`) and a loop `invariant`; the
verification conditions are discharged in `where finally`.  Every piece is
explained in a later lecture. -/

def bonus (x : Nat) : Nat :=
  if x % 2 == 0 then 2 * x else x

def score : List Nat → Nat
  | []      => 0
  | x :: xs => bonus x + score xs

theorem score_append (l : List Nat) (x : Nat) :
    score (l ++ [x]) = score l + bonus x := by
  induction l with
  | nil => simp [score]
  | cons y ys ih => simp [score, ih]; omega

def scoreInto (xs : List Nat) : StateM Nat Unit
    requires s => s = 0
    ensures _ s => s = score xs
  := do
    for x in xs invariant pref _ s => s = score pref do
      modify (· + bonus x)
  where finally
    | spec =>
      case vc1 => simp_all [score]
      case vc3 => simp_all [score_append]

#eval (scoreInto [1, 2, 3]).run 0    -- ((), 8): 1 + 2·2 + 3
