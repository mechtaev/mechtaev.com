/-! # Untyped λ-calculus — the Lean on the slides

Self-contained: needs only Lean 4 (v4.34.0-rc1 or later), no library.

How to run
* Install Lean via elan: https://lean-lang.org/install
* Open this file in VS Code with the "Lean 4" extension.  Results of
  `#eval`/`#check` appear in the Infoview; errors are underlined.
* Or, in a terminal: `lean untyped-lambda-calculus.lean`

`-- Slide N` names the page of the deck the code appears on.  Blocks marked
"support" are definitions the slides use but do not show.  Definition
numbers are Nederpelt & Geuvers, *Type Theory and Formal Proof*, ch. 1.
-/

/-! ## Slide 7 — Lean's `def`, `#eval`, `#check` -/

def double (n : Nat) : Nat := 2 * n
#eval double 21        -- 42
#check (double)        -- double : Nat → Nat
#check double 21       -- double 21 : Nat

-- Two arguments are two arrows: a function returning a function.
def tag (k : Nat) (s : String) : String :=
  s ++ toString k
#check (tag)           -- tag : Nat → String → String
#eval tag 3 "v"        -- "v3"

/-! ## Slide 8 — `Nat` is an inductive type -/

#print Nat
-- inductive Nat : Type
-- constructors:
--   Nat.zero : Nat
--   Nat.succ : Nat → Nat

/-! ## Slide 9 — Pattern matching, and what Lean demands

Every `def` must cover every case and must terminate.  The two guarded
definitions below are rejected; `#guard_msgs` records the expected error. -/

def fact : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * fact n
#eval fact 5           -- 120

/-- error: Missing cases:
(Nat.succ Nat.zero) -/
#guard_msgs in
def half : Nat → Nat
  | 0     => 0
  | n + 2 => half n + 1

#guard_msgs (drop error) in
def loop (n : Nat) : Nat := loop (n + 1)

/-! ## Slide 10 — Λ is an inductive type (Def. 1.3.2) -/

inductive Term where
  | var : String → Term
  | app : Term → Term → Term
  | lam : String → Term → Term

/-! ### Support: equality, printing, size -/

deriving instance DecidableEq for Term

namespace Term

-- Print a term as it is written: `lam "x" (var "x")`.
protected def repr : Term → Nat → Std.Format
  | var x,   p => Repr.addAppParen f!"var {repr x}" p
  | app P Q, p => Repr.addAppParen f!"app {P.repr max_prec} {Q.repr max_prec}" p
  | lam x P, p => Repr.addAppParen f!"lam {repr x} {P.repr max_prec}" p
instance : Repr Term := ⟨Term.repr⟩

-- Number of nodes; the termination measure for `subst`.
def size : Term → Nat
  | var _   => 1
  | app P Q => size P + size Q + 1
  | lam _ P => size P + 1

/-! ## Slide 11 — Examples of λ-terms (Def. 1.3.4) -/

def examples : List Term :=
  [ var "x",
    app (var "x") (var "y"),
    lam "x" (app (var "x") (var "y")),
    app (lam "x" (var "x")) (lam "x" (var "x")) ]

/-! ### Support: the standard combinators (§1.10, §1.12) -/

def I : Term := lam "x" (var "x")
def K : Term := lam "x" (lam "y" (var "x"))
def S : Term := lam "x" (lam "y" (lam "z"
                  (app (app (var "x") (var "z")) (app (var "y") (var "z")))))
def ω : Term := lam "x" (app (var "x") (var "x"))
def Ω : Term := app ω ω                    -- no normal form (Ex. 1.9.3)

/-! ## Slide 13 — Syntactic identity is decidable (Notation 1.3.4) -/

#eval I == I                                   -- true
#eval lam "x" (var "x") == lam "z" (var "z")   -- false: the names differ

example : lam "x" (var "x") ≠ lam "z" (var "z") := by decide

/-! ### Support: duplicate-free union of name lists -/

def nameUnion (a b : List String) : List String :=
  a ++ b.filter (fun x => !a.contains x)

/-! ## Slide 18 — FV, by recursion over the rules (Def. 1.4.1) -/

def FV : Term → List String
  | var x   => [x]                        -- a variable is free in itself
  | app P Q => nameUnion (FV P) (FV Q)    -- free on either side
  | lam x P => (FV P).erase x             -- x is bound here

#eval Term.FV (lam "x" (app (var "x") (var "y")))   -- ["y"]

def isClosed (M : Term) : Bool := M.FV.isEmpty      -- Def. 1.4.3

/-! ### Support: renaming, and a fresh name -/

-- Rename every free `x` to `y`.  Structural and size-preserving.
def rename (x y : String) : Term → Term
  | var z   => if z = x then var y else var z
  | app P Q => app (rename x y P) (rename x y Q)
  | lam z P => if z = x then lam z P else lam z (rename x y P)

theorem size_rename (x y : String) (M : Term) :
    (rename x y M).size = M.size := by
  induction M with
  | var z => by_cases h : z = x <;> simp [rename, size, h]
  | app P Q ihP ihQ => simp [rename, size, ihP, ihQ]
  | lam z P ih => by_cases h : z = x <;> simp [rename, size, h, ih]

-- A name not in `avoid`, obtained by priming.
def freshAux (avoid : List String) (base : String) : Nat → String
  | 0     => base
  | n + 1 => if avoid.contains base then freshAux avoid (base ++ "'") n else base
def fresh (avoid : List String) (base : String) : String :=
  freshAux avoid base (avoid.length + 1)

/-! ## Slide 23 — Substitution, and the clause that avoids capture (Def. 1.6.1) -/

def subst (x : String) (N : Term) : Term → Term
  | var y   => if y = x then N else var y
  | app P Q => app (subst x N P) (subst x N Q)
  | lam y P =>
      if y = x then lam y P                -- x is bound here: stop
      else if (FV N).contains y then
        let z := fresh (nameUnion (FV N) (FV P)) y
        lam z (subst x N (rename y z P))   -- rename y apart, descend
      else lam y (subst x N P)
termination_by M => M.size
decreasing_by
  all_goals simp_wf <;> simp [size, size_rename] <;> omega

/-! ## Slide 24 — Capture, prevented

`(λy. y x)[x := x y]`: clause 3 renames the binder first. -/

#eval subst "x" (app (var "x") (var "y"))
                (lam "y" (app (var "y") (var "x")))
-- lam "y'" (app (var "y'") (app (var "x") (var "y")))

/-! ### Support: nameless terms (§1.12)

A bound variable becomes the number of binders between it and its `λ`;
a free one keeps its name. -/

inductive DB where
  | idx  : Nat → DB
  | free : String → DB
  | app  : DB → DB → DB
  | lam  : DB → DB
  deriving DecidableEq

protected def DB.repr : DB → Nat → Std.Format
  | .idx k,   p => Repr.addAppParen f!"idx {k}" p
  | .free x,  p => Repr.addAppParen f!"free {repr x}" p
  | .app P Q, p => Repr.addAppParen f!"app {P.repr max_prec} {Q.repr max_prec}" p
  | .lam P,   p => Repr.addAppParen f!"lam {P.repr max_prec}" p
instance : Repr DB := ⟨DB.repr⟩

-- `ctx` lists the binders in scope, innermost first.
def toDB (ctx : List String) : Term → DB
  | var x   => match ctx.idxOf? x with
               | some i => .idx i
               | none   => .free x
  | app P Q => .app (toDB ctx P) (toDB ctx Q)
  | lam x P => .lam (toDB (x :: ctx) P)

-- α-equivalence (Def. 1.5.2), decided by erasure.
def alphaEq (M N : Term) : Bool := toDB [] M == toDB [] N

/-! ## Slide 27 — Erasing names decides =α -/

#eval toDB [] (lam "x" (var "x"))          -- lam (idx 0)
#eval toDB [] (lam "z" (var "z"))          -- lam (idx 0)   -- same
#eval toDB ["w"] (lam "x" (app (var "w") (var "x")))
-- lam (app (idx 1) (idx 0))     -- w: read off the context
#eval toDB []    (lam "x" (app (var "w") (var "x")))
-- lam (app (free "w") (idx 0))  -- w: keeps its name

#eval alphaEq (lam "x" (var "x")) (lam "z" (var "z"))  -- true
#eval alphaEq (var "a") (var "b")                      -- false

/-! ## Slide 31 — One step, made deterministic (Def. 1.8.1)

`→β` is a relation; to run it, choose a redex.  This is leftmost-outermost. -/

def step : Term → Option Term
  | app (lam x P) Q => some (subst x Q P)    -- the basis: contract
  | app P Q         => match step P with       -- else look left,
      | some P' => some (app P' Q)
      | none    => (step Q).map (app P)        -- then right,
  | lam x P         => (step P).map (lam x)    -- then under the λ.
  | var _           => none                  -- a variable is normal

/-! ### Support: reduce with a step budget -/

def nf : Nat → Term → Term
  | 0,     M => M
  | n + 1, M => match step M with
                | some M' => nf n M'
                | none    => M

/-! ## Slide 36 — Why the budget is not an artefact (§1.9)

Some terms have no normal form, so no total function can return one. -/

#eval nf 20 (app I (var "q"))                   -- var "q"
#eval nf 20 (app (app K (var "a")) (var "b"))   -- var "a"

-- Ω reduces to itself forever: after any number of steps we are where we began.
#eval nf 20 Ω == Ω                         -- true
#eval nf 1000 Ω == Ω                       -- true

/-! ### Support: Curry's fixed-point combinator (Thm. 1.10.1) -/

def Y : Term :=
  lam "f" (app (lam "x" (app (var "f") (app (var "x") (var "x"))))
               (lam "x" (app (var "f") (app (var "x") (var "x")))))

/-! ## Slide 39 — Fixed points, computed

`Y f ↠β f (Y f)`: each step peels off one more `f`, and the term never
settles.  `Y` is closed, and cannot be typed: Turing-completeness has a price. -/

#eval nf 3 (app Y (var "f"))
-- app (var "f") (app (var "f") (app (lam "x" ..) (lam "x" ..)))
#eval Term.isClosed Y                      -- true

/-! ### Support: Church numerals, `⌜n⌝ = λf.λx. fⁿ x` -/

def church (n : Nat) : Term :=
  lam "f" (lam "x" (go n))
where
  go : Nat → Term
    | 0     => var "x"
    | k + 1 => app (var "f") (go k)

#eval church 2   -- lam "f" (lam "x" (app (var "f") (app (var "f") (var "x"))))

/-! ## Slide 41 — Addition composes iterators

`add ≡ λm.λn.λf.λx. m f (n f x)`: n's passes through f, then m's. -/

def add : Term :=
  lam "m" (lam "n" (lam "f" (lam "x"
    (app (app (var "m") (var "f"))
         (app (app (var "n") (var "f")) (var "x"))))))

#eval alphaEq (nf 100 (app (app add (church 2)) (church 3)))
              (church 5)                       -- true

end Term
