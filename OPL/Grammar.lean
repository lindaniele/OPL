/-
  OPL/Grammar.lea
  sec I.1, grammar side: context-free and operato grammars, left/right
  terminal sets, the OPM(G) mrix, OP grammars, Fischer normal form.
  sec I.1, Def. I.1.1, Def. I.1.2.
-/
import Mathlib.Logic.Relation
import OPL.Alphabet

namespace OPL

variable {α N : Type}

/-- grammar symbol: nonterminal or terminal -/
abbrev GSym (N α : Type) := N ⊕ α

/-- context-free grammar `G = (N, Σ, P, S)`.

decision10, axios as a set. the paper takes `S ⊆ N` instead of the usual single
axiom, "to simplify some notations and constructions" (footnote 4), so here
`S : N → Prop`. that's also eactly why `CFG` was *nt* replaced by Mathlib's
`ContextFreeGrammar` when migrating: that one has a single axiom, and switching to
it would mean rewritin the paper's constuctions. -/
structure CFG (α N : Type) where
  P : N → List (GSym N α) → Prop
  S : N → Prop

/-- one-step dervation `⇒` -/
inductive DerivStep (G : CFG α N) : List (GSym N α) → List (GSym N α) → Prop
  | intro {pre A rhs post} :
      G.P A rhs → DerivStep G (pre ++ Sum.inl A :: post) (pre ++ rhs ++ post)

/-- derivaion `⇒*`, refl-trans closure ìjust Mathlib's `ReflTransGen` -/
abbrev Derives (G : CFG α N) : List (GSym N α) → List (GSym N α) → Prop :=
  Relation.ReflTransGen (DerivStep G)

theorem Derives.trans {G : CFG α N} {x y z : List (GSym N α)} :
    Derives G x y → Derives G y z → Derives G x z :=
  Relation.ReflTransGen.trans

/-- languagegenerateìd by `G` -/
def langG (G : CFG α N) : Language α :=
  {w | ∃ A, G.S A ∧ Derives G [Sum.inl A] (w.map Sum.inr)}

/-! ## operator form -/

/-- no twoadjacent nonterìminals -/
def NoAdjacentNT : List (GSym N α) → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => ¬ (x.isLeft ∧ y.isLeft) ∧ NoAdjacentNT (y :: rest)

/-- operatorgrammar (OG): every rule is in operator form -/
def IsOG (G : CFG α N) : Prop :=
  ∀ A rhs, G.P A rhs → NoAdjacentNT rhs

/-- `[B]` if `B` is there, `[]` otherwise. makes the paper's "`B ∈ N ∪ {ε}`"
literal-/
def optNT (B : Option N) : List (GSym N α) :=
  match B with
  | none => []
  | some B => [Sum.inl B]

/-- leftterminal set `L_G(A) = {a | A ⇒* B a α}` -/
def leftTerm (G : CFG α N) (A : N) (a : α) : Prop :=
  ∃ (B : Option N) (rest : List (GSym N α)),
    Derives G [Sum.inl A] (optNT B ++ Sum.inr a :: rest)

/-- righttrminal set `R_G(A) = {a | A ⇒* α a B}` -/
def rightTerm (G : CFG α N) (A : N) (a : α) : Prop :=
  ∃ (B : Option N) (pre : List (GSym N α)),
    Derives G [Sum.inl A] (pre ++ Sum.inr a :: optNT B)

/-! ## the OPM(G) matrix (sec. I.1)

decision11, two represetations of the matrix. `OPAlphabet` (decision 2) is
`Option Prec`-valued hence conflct-free by construction, which is fie for the
automata, where the matrix is given up front. but `OPM(G)` is *derived* from the
productions and in general it dos have conflicts — that's precisely what Def.
I.1.1 rules out. so ere the matrix is `α → α → Prec → Prop` and conflic-freeness
is a separate redicate. `Agrees` is the bridge between the two. -/

/-- the `≐` relation: `a ≐ b ⟺ ∃ A → α a B b β`, with `B ∈ N ∪ {ε}` -/
def eqPrecG (G : CFG α N) (a b : α) : Prop :=
  ∃ (A : N) (pre : List (GSym N α)) (B : Option N) (post : List (GSym N α)),
    G.P A (pre ++ Sum.inr a :: (optNT B ++ Sum.inr b :: post))

/-- the `⋖` relation: `a ⋖ b ⟺ ∃ A → α a D β`, `D ∈ N`, `b ∈ L_G(D)` -/
def yieldsG (G : CFG α N) (a b : α) : Prop :=
  ∃ (A : N) (pre : List (GSym N α)) (D : N) (post : List (GSym N α)),
    G.P A (pre ++ Sum.inr a :: Sum.inl D :: post) ∧ leftTerm G D b

/-- the `⋗` relation: `a ⋗ b ⟺ ∃ A → α D b β`, `D ∈ N`, `a ∈ R_G(D)` -/
def takesG (G : CFG α N) (a b : α) : Prop :=
  ∃ (A : N) (pre : List (GSym N α)) (D : N) (post : List (GSym N α)),
    G.P A (pre ++ Sum.inl D :: Sum.inr b :: post) ∧ rightTerm G D a

/-- `OPM(G)`, conflicts and all -/
def OPM (G : CFG α N) (a b : α) : Prec → Prop
  | .lt => yieldsG G a b
  | .eq => eqPrecG G a b
  | .gt => takesG G a b

/-- conflict-free matrix: `|M_ab| ≤ 1` (Def. I.1.1) -/
def ConflictFree (G : CFG α N) : Prop :=
  ∀ a b r₁ r₂, OPM G a b r₁ → OPM G a b r₂ → r₁ = r₂

/-- operator precedence grammar (Def. I.1.1) -/
structure IsOPG (G : CFG α N) : Prop where
  og : IsOG G
  conflictFree : ConflictFree G

/-- the OP alphabet `(Σ, M)` gives back exactly `OPM(G)`. this is the "`A` has the
same precedence mtrix `M` as `G`" condition of Th I.3.1. on terminal the two
matrices agree, the `#` cells are pinne by the `sharp_left` / `sharp_right` fields
of `OPAlphabet` -/
def Agrees (Γ : OPAlphabet α) (G : CFG α N) : Prop :=
  ∀ a b r, OPM G a b r ↔ Γ.M (some a) (some b) = some r

/-! ## Fischer normal form (Def. I.1.2) -/

/-- invertible gramma: no to rules share a r.h.s. -/
def Invertible (G : CFG α N) : Prop :=
  ∀ A B rhs, G.P A rhs → G.P B rhs → A = B
/-- renaming rule:a single nonterminal on the right -/
def IsRenaming (rhs : List (GSym N α)) : Prop :=
  ∃ B, rhs = [Sum.inl B]
/-- `A` shows up in no r.h.s. a all -/
def UnusedElsewhere (G : CFG α N) (A : N) : Prop :=
  ∀ B rhs, G.P B rhs → Sum.inl A ∉ rhs

/-- Fischer normal form (Def. I.1.2): invertible, no empty rules except possibly
`A → ε` with `A` an axiom not used elsewhere, no renaming rules -/
structure FNF (G : CFG α N) : Prop where
  invertible : Invertible G
  no_renaming : ∀ A rhs, G.P A rhs → ¬ IsRenaming rhs
  empty_rule : ∀ A, G.P A [] → G.S A ∧ UnusedElsewhere G A

/-- reduced grammarery nonterminal is reachable from an axiom and produces at
least one terminal word
decision 12, "redced" done on nonterminals,not on rules. the paper says "every
rule can be used to generatesom string in Σ*"; here it's the usual conjunction of
reachability + productvity f nonterminals, which is the standard and handier
form. if some proof ends up needing the literal per-rule version, this def has to
be strengthened. -/
structure Reduced (G : CFG α N) : Prop where
  productive : ∀ A, ∃ w : List α, Derives G [Sum.inl A] (w.map Sum.inr)
  reachable : ∀ A, ∃ S₀ pre post, G.S S₀ ∧
    Derives G [Sum.inl S₀] (pre ++ Sum.inl A :: post)

/-- OPL "alla Floyd"

generated by an OPG whose matrix is the one of `Γ`. compare
with `IsOPL` (via automata) the two agree, that's   I.3  -/
def IsOPLg (Γ : OPAlphabet α) (L : Language α) : Prop :=
  ∃ (N : Type) (G : CFG α N), IsOPG G ∧ Agrees Γ G ∧ ∀ w, w ∈ L ↔ w ∈ langG G

end OPL
