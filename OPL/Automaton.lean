/-
  OPL/Automton.lean
  sec I.2: operator precedence automata, operational semantics, accepted
  language, suports, determinism. Def. I.2.1, I.2.2, I.2.3.
-/
import Mathlib.Logic.Relation
import OPL.Alphabet

namespace OPL

variable {α : Type}

/-! ## OP automata (Def. I.2.1)

decision 4, δ kept reltional. the paper uses `δ : Q × (Σ ∪ Q) → ℘(Q)`. here the
three tranition functions stay relations `… → Prop`: statements stay
propositional and te deterministic version is just uniqueness (`∃!`), which is
literally Def. I.2.3. the *sets* of staes (`I`, `F`) are `Set Q` instead, direct
rendering of `℘(Q)`. `Fintype` only shows up wher states actually get counted
(Thm I.2.4). -/

/-- nondeterministic operator precedence automaton -/
structure OPA (α : Type) (Q : Type) where
  G : OPAlphabet α
  I : Set Q
  F : Set Q
  push : Q → α → Q → Prop
  shift : Q → α → Q → Prop
  pop : Q → Q → Q → Prop

variable {Q : Type}

/-! ## configurations and semantics

decision 5, stack rientation. the paper wites the stack with the top on the
*right* (`Π[a,p]`), here the top is the *head* of the list. only notational
divergence from the text,keep it in ind when porting proofs.

decision 6, the final `#` is not in the input. a configuration in the paper has
third component in `Σ*#`; here the intpu is a `List α` and the final `#` is just
the end ìof the list, `nextSymbol [] = none`. so malformed cofigurations (no `#`,
or a `#` in the middle) aren't even representable. -/

/-- stack: `Γ* = (Σ × Q)*`, top at the head. empty stack = `⊥` -/
abbrev Stack (α Q : Type) := List (α × Q)

/-- `symbol(Π)`: gives `#` (ie `none`) when the stack is just `⊥` -/
def topSymbol : Stack α Q → Option α
  | [] => none
  | (a, _) :: _ => some a

/-- next input char, `none` is the final `#` -/
def nextSymbol : List α → Option α
  | [] => none
  | a :: _ => some a

/-- configuration `⟨Π, q, w⟩` -/
structure Config (α Q : Type) where
  stack : Stack α Q
  state : Q
  input : List α

/-- the three moves (Def. I.2.1) -/
inductive Step (A : OPA α Q) : Config α Q → Config α Q → Prop
  | push {S p q a x} :
      A.G.M (topSymbol S) (some a) = some .lt →
      A.push p a q →
      Step A ⟨S, p, a :: x⟩ ⟨(a, p) :: S, q, x⟩
  | shift {S p q r a b x} :
      A.G.M (some a) (some b) = some .eq →
      A.shift q b r →
      Step A ⟨(a, p) :: S, q, b :: x⟩ ⟨(b, p) :: S, r, x⟩
  | pop {S p q r a w} :
      A.G.M (some a) (nextSymbol w) = some .gt →
      A.pop q p r →
      Step A ⟨(a, p) :: S, q, w⟩ ⟨S, r, w⟩

/-- refl-trans ìclosure of `Step`, Mathlib's `ReflTransGen`. constructors are
`Relation.ReflTransGen.refl` and `.tail` (which *appends* a step); to *prepend* one,
like the example runs do, use `Relation.ReflTransGen.head` -/
abbrev Steps (A : OPA α Q) : Config α Q → Config α Q → Prop :=
  Relation.ReflTransGen (Step A)

theorem Steps.trans {A : OPA α Q} {c₁ c₂ c₃ : Config α Q} :
    Steps A c₁ c₂ → Steps A c₂ c₃ → Steps A c₁ c₃ :=
  Relation.ReflTransGen.trans

/-- `w ∈ L(A)` (Def. I.2.1) -/
def Accepts (A : OPA α Q) (w : List α) : Prop :=
  ∃ qi qf, qi ∈ A.I ∧ qf ∈ A.F ∧ Steps A ⟨[], qi, w⟩ ⟨[], qf, []⟩

/-- language recognized by `A` -/
def lang (A : OPA α Q) : Language α := {w | Accepts A w}

/-- `L` is an OPL over `(Σ, M)` when some OPA on that alphabet recognizes it. the
state type is existentially quantified, see decision 7 -/
def IsOPL (G : OPAlphabet α) (L : Language α) : Prop :=
  ∃ (Q : Type) (A : OPA α Q), A.G = G ∧ ∀ w, w ∈ L ↔ Accepts A w

/-! decision 7, finitenìess of the state set. `IsOPL` quantifies over `Q : Type`
without asking it to e finite. for all the purely language-theoretic results of
Part I (closures, equivalence with grammars, MSO characterization) finiteness is
not needed, nd asking for i would mean dragging `Fintype` istances verywhere.
where cardinality does matter  the `2^O(s²)` bound of Thm I.2.4 — the `Fintype`
instance is aked for right there. to revisit if some proof turns out to use
finiteness in an essential way: then this is the first def to change. -/

/-! ## supports (Def. I.2.2)

a support is the run that reduces the body of a chain. indexed by depth like
`ChainD`, sam reason (decision 3).

one constructor is enough: the support of a *simple* chain (I.2.1) is the case
where all sub-boies are empty. -/

mutual

/-- `Support A d q x q'`: support of depth ≤ `d` for a chain with body `x`, from `q`
to `q'` (Def. I.2.2, eq. I.2.1 and I.2.2).
shape: process `x₀`, *push* `a₁`, process the `xᵢ` alternating with *shifts* of
`a₂ … aₙ`, then one *pop* whose label is exactly the state reache after `x₀` -/
inductive Support (A : OPA α Q) : Nat → Q → List α → Q → Prop
  | intro {d q₀ x₀ q₀' a q₁ xs as qn q'} :
      SubRun A d q₀ x₀ q₀' →
      A.push q₀' a q₁ →
      Inner A d q₁ xs as qn →
      A.pop qn q₀' q' →
      Support A (d + 1) q₀ (x₀ ++ a :: weave xs as) q'

/-- a sub-bodyeither empty (state doesn't move), or a chain itself with its own
support -/
inductive SubRun (A : OPA α Q) : Nat → Q → List α → Q → Prop
  | empty {d q} : SubRun A d q [] q
  | chain {d q x q'} : Support A d q x q' → SubRun A d q x q'

/-- the `x₁ a₂ x₂ … aₙ xₙ` part of a support: sub-bodies alternating with shifts -/
inductive Inner (A : OPA α Q) : Nat → Q → List (List α) → List α → Q → Prop
  | last {d q x q'} : SubRun A d q x q' → Inner A d q [x] [] q'
  | cons {d q x q' a q'' xs as r} :
      SubRun A d q x q' →
      A.shift q' a q'' →
      Inner A d q'' xs as r →
      Inner A d q (x :: xs) (a :: as) r

end

/-- the paper's `q ↝ q'` fo body `x`, depth forgotten -/
def HasSupport (A : OPA α Q) (q : Q) (x : List α) (q' : Q) : Prop :=
  ∃ d, Support A d q x q'

/-! ## deterministic automata (Def. I.2.3) -/

/-- an OPA is deterministic hwen `I` is a singleton and the three transitions are
total functions (paper: "the ranges of δpush, δshift and δpop are `Q` rather than
`℘(Q)`") -/
structure Deterministic (A : OPA α Q) : Prop where
  init : ∃! q, q ∈ A.I
  det_push : ∀ p a, ∃! q, A.push p a q
  det_shift : ∀ p a, ∃! q, A.shift p a q
  det_pop : ∀ p r, ∃! q, A.pop p r q

end OPL
