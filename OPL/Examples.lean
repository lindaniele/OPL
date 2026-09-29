/-
  OPL/Examples.lean

  sanity checks forthe defs: the arithmetic expressions of Examples 1-3 of the
  paper.
  these arehere for one reason only: to notice *right away* when a def is wrong,
  instead of a hundred lines o proofs late. in particular `figI21_run` replays
  the computation of Fig. I.2.1 step by step, stack column included — if the
  semantics of `Step` were wrong it woudn't typecheck.
-/
import OPL.Automaton

namespace OPL
namespace Examples

open Relation

/-- the alphabet ofExample 1. `lpar`/`rpar` are the paer's `L`/`M` (it uses those
so as not to overload the parens) -/
inductive Sym where
  | n | plus | times | lpar | rpar
  deriving DecidableEq, Repr

open Sym

/-- the OPM of Fig. I.1.3.
so that `#[x]#` is a
chain; no move of the utomaton ever looks at it (push reads a real char, shift and
pop hae a symbol on top of the stack). set to `≐` here ,,my choice, not the
paper's -/
def exprM : Option Sym → Option Sym → Option Prec
  | none, none => some .eq
  | none, some _ => some .lt
  | some _, none => some .gt
  | some a, some b =>
    match a, b with
    | plus, plus => some .gt
    | plus, times => some .lt
    | plus, lpar => some .lt
    | plus, rpar => some .gt
    | plus, n => some .lt
    | times, plus => some .gt
    | times, times => some .gt
    | times, lpar => some .lt
    | times, rpar => some .gt
    | times, n => some .lt
    | lpar, plus => some .lt
    | lpar, times => some .lt
    | lpar, lpar => some .lt
    | lpar, rpar => some .eq
    | lpar, n => some .lt
    | rpar, plus => some .gt
    | rpar, times => some .gt
    | rpar, rpar => some .gt
    | rpar, _ => none
    | n, plus => some .gt
    | n, times => some .gt
    | n, rpar => some .gt
    | n, _ => none

def exprAlph : OPAlphabet Sym where
  M := exprM
  sharp_left _ := rfl
  sharp_right _ := rfl

/-- matrix is not total: `n n` and `M L` are empty ells, and that's eactly what
maks `n + n × Ln + nM Ln + nM` not cmpatible (the example right after
Def. I.1.6) -/
example : ¬ exprAlph.Total := by
  intro h
  have := h (some n) (some n)
  simp [OPAlphabet.Total, exprAlph, exprM] at this

/-! ## universal automaton

one stat, all transitions: accepts exactly th words compatible with the matrix.
here to test `Step` on its own -/

def univAutomaton : OPA Sym Unit where
  G := exprAlph
  I := Set.univ
  F := Set.univ
  push _ _ _ := True
  shift _ _ _ := True
  pop _ _ _ := True

example : Accepts univAutomaton [n, plus, n] := by
  refine ⟨(), (), Set.mem_univ _, Set.mem_univ _, ?_⟩
  refine ReflTransGen.head (Step.push (q := ()) rfl trivial) ?_   -- ⊥ ⋖ n
  refine ReflTransGen.head (Step.pop (r := ()) rfl trivial) ?_    -- n ⋗ +
  refine ReflTransGen.head (Step.push (q := ()) rfl trivial) ?_   -- ⊥ ⋖ +
  refine ReflTransGen.head (Step.push (q := ()) rfl trivial) ?_   -- + ⋖ n
  refine ReflTransGen.head (Step.pop (r := ()) rfl trivial) ?_    -- n ⋗ #
  refine ReflTransGen.head (Step.pop (r := ()) rfl trivial) ?_    -- + ⋗ #
  exact ReflTransGen.refl

/-! ## the automaton of Fig. I.2.1

CAREFUL: rebuilt from the computationtrace printed in Fig. I2.1 (stack / state /
remaining input column), not read off the picture of the graph. it has exactly the
transitions that computation exercises andnothing else. final states are `q1` and
`q3`: `q3` is where the rn of the figure ends, `q1` is there o accept a single
`n`. to be checked aainst the original figure before using it for anything more
thn a test. -/

inductive St where
  | q0 | q1 | q2 | q3
  deriving DecidableEq, Repr

open St

def pushT : List (St × Sym × St) :=
  [(q0, n, q1), (q1, plus, q0), (q1, times, q0),
   (q0, lpar, q2), (q2, n, q3), (q3, plus, q2)]

def shiftT : List (St × Sym × St) :=
  [(q3, rpar, q3)]

def popT : List (St × St × St) :=
  [(q1, q0, q1), (q3, q2, q3), (q3, q3, q3), (q3, q0, q3), (q3, q1, q3)]

def figI21 : OPA Sym St where
  G := exprAlph
  I := {q | q = q0}
  F := {q | q = q1 ∨ q = q3}
  push p a q := (p, a, q) ∈ pushT
  shift p a q := (p, a, q) ∈ shiftT
  pop p r q := (p, r, q) ∈ popT

-- decidabiity instances: witout thm `decide` doesn't get through the `OPA.push`
-- projection applied to a sructure literal
instance(p : St) (a : Sym) (q : St) : Decidable (figI21.push p a q) :=
  inferInstanceAs (Decidable ((p, a, q) ∈ pushT))

instance (p : St) (a : Sym) (q : St) : Decidable (figI21.shift p a q) :=
  inferInstanceAs (Decidable ((p, a, q) ∈ shiftT))

instance (p r q : St) : Decidable (figI21.pop p r q) :=
  inferInstanceAs (Decidable ((p, r, q) ∈ popT))

/-- the expresion `n + n × Ln + nM` of Fig. I.2.1 is accepted. the 17 steps are
exactly the rows of the table in thefigure -/
theorem figI21_run :
    Accepts figI21 [n, plus, n, times, lpar, n, plus, n, rpar] := by
  refine ⟨q0, q3, rfl, Or.inr rfl, ?_⟩
  -- ⊥ ⋖ n, push: stack [n,q0]
  refine ReflTransGen.head (Step.push (q := q1) rfl (by decide)) ?_
  -- n ⋗ +, pop: stack ⊥
  refine ReflTransGen.head (Step.pop (r := q1) rfl (by decide)) ?_
  -- ⊥ ⋖ +, push: stack [+,q1]
  refine ReflTransGen.head (Step.push (q := q0) rfl (by decide)) ?_
  -- + ⋖ n, push: stack [+,q1][n,q0]
  refine ReflTransGen.head (Step.push (q := q1) rfl (by decide)) ?_
  -- n ⋗ ×, pop: stack [+,q1]
  refine ReflTransGen.head (Step.pop (r := q1) rfl (by decide)) ?_
  -- + ⋖ ×, push: stack [+,q1][×,q1]
  refine ReflTransGen.head (Step.push (q := q0) rfl (by decide)) ?_
  -- × ⋖ L, push: stack [+,q1][×,q1][L,q0]
  refine ReflTransGen.head (Step.push (q := q2) rfl (by decide)) ?_
  -- L ⋖ n, push: stack …[L,q0][n,q2]
  refine ReflTransGen.head (Step.push (q := q3) rfl (by decide)) ?_
  -- n ⋗ +, pop: stack …[L,q0]
  refine ReflTransGen.head (Step.pop (r := q3) rfl (by decide)) ?_
  -- L ⋖ +, push: stack …[L,q0][+,q3]
  refine ReflTransGen.head (Step.push (q := q2) rfl (by decide)) ?_
  -- + ⋖ n, push: stack …[+,q3][n,q2]
  refine ReflTransGen.head (Step.push (q := q3) rfl (by decide)) ?_
  -- n ⋗ M, pop: stack …[L,q0][+,q3]
  refine ReflTransGen.head (Step.pop (r := q3) rfl (by decide)) ?_
  -- + ⋗ M, pop: stack [+,q1][×,q1][L,q0]
  refine ReflTransGen.head (Step.pop (r := q3) rfl (by decide)) ?_
  -- L ≐ M, shift: stack [+,q1][×,q1][M,q0]
  refine ReflTransGen.head (Step.shift (r := q3) rfl (by decide)) ?_
  -- M ⋗ #, pop: stack [+,q1][×,q1]
  refine ReflTransGen.head (Step.pop (r := q3) rfl (by decide)) ?_
  -- × ⋗ #, pop: stack [+,q1]
  refine ReflTransGen.head (Step.pop (r := q3) rfl (by decide)) ?_
  -- + ⋗ #, pop: stack ⊥
  refine ReflTransGen.head (Step.pop (r := q3) rfl (by decide)) ?_
  exact ReflTransGen.refl

/-- a single `n` is accepted too -/
theorem figI21_single : Accepts figI21 [n] := by
  refine ⟨q0, q1, rfl, Or.inl rfl, ?_⟩
  refine ReflTransGen.head (Step.push (q := q1) rfl (by decide)) ?_
  refine ReflTransGen.head (Step.pop (r := q1) rfl (by decide)) ?_
  exact ReflTransGen.refl

/-! ## chains

`#[n]₊` is a smple chain: `# ⋖ n ⋗ +`. -/

example : SimpleChain exprAlph none [n] (some plus) :=
  ⟨n, n, EqRun.single n, rfl, rfl, rfl⟩

example : IsChain exprAlph none [n] (some plus) :=
  ⟨1, ChainD.simple ⟨n, n, EqRun.single n, rfl, rfl, rfl⟩⟩
/-- `L[n]M` is a smple chain with `L ≐ M`: body is `n`, delimites are `L` and
`M` -/
example : SimpleChain exprAlph (some lpar) [n] (some rpar) :=
  ⟨n, n, EqRun.single n, rfl, rfl, rfl⟩

end Examples
end OPL
