/-
  OPL/Alphabet.lean

  Section I.1 of the paper: operator precedence alphabets, chains,
  depth, and compatible words.

  References: Def. I.1.3, I.1.4, I.1.5, I.1.6.
-/
import Mathlib.Computability.Language

namespace OPL

/-! ## Precedence relations -/

/-- The three precedence relations between terminals:
`lt` = ⋖ (yields precedence), `eq` = ≐ (equal in precedence),
`gt` = ⋗ (takes precedence).
they are like parentheses: `lt` opens a chain, `eq` continues it, and `gt` closes it.

for example, in the arithmetic alphabet `{n, +, ×}` we have `+ ⋖ ×` and `× ⋗ +`,
Prendi n + n × n con la matrice di Fig. I.1.3. Le relazioni tra terminali adiacenti sono:

# ⋖ n ⋗ + ⋖ n ⋗ × ⋖ n ⋗ #
-/
inductive Prec where
  | lt -- pushes
  | eq --equal
  | gt --pops
  deriving DecidableEq, Repr


/-! ## Alfabeto OP (Def. I.1.3)

DECISION 1  the delimiter `#`.
`#` is represented by `none : Option α`, so `Σ ∪ {#}` is `Option α`,
without needing a dedicated sum type. The concrete gain appears in the
automaton semantics: the pop move compares the top of the stack with the
*next symbol in the input*, which at the end of a word is exactly `#`;
with this encoding we have `nextSymbol [] = none`, and there is no need
to treat the terminal case separately.

DECISION 2 conflict-freeness .
The paper defines `M` as a matrix of *sets* of relations and then imposes
`|M_ab| ≤ 1`. well, it means that each pair of terminals
gets at most one of the three relations.
Here `M` returns `Option Prec` and `none` is the empty cell,
`some r` is the unique relation. Conflict-freeness is therefore true by
construction and does not need to be carried as an assumption in every
statement. The price: the matrix *with* conflicts (used only to define
OPM(G) for an arbitrary grammar, see `Grammar.lean`) must be represented
separately as `α → α → Prec → Prop`. -/

/-- Operator-precedence alphabet `(Σ, M)`.
Σ is the set of terminals. and M is the precedence matrix conflict-free-/
structure OPAlphabet (α : Type) where
  M : Option α → Option α → Option Prec
  /-- The initial `#` can only yield precedence. -/
  sharp_left : ∀ a : α, M none (some a) = some .lt
  /-- Every symbol can only take precedence over the final `#`. -/
  sharp_right : ∀ a : α, M (some a) none = some .gt

variable {α : Type}

/- abbreviations are used to make the statements more readable

some is one of the two constructors of Lean's Option type, which represents
"a value that might be missing".
So a value of type Option α is either:
none: nothing there, or
some x: there is a value, and it is x.
-/

/-- `a ⋖ b`. -/
abbrev OPAlphabet.yields (G : OPAlphabet α) (a b : Option α) : Prop :=
  G.M a b = some .lt --G.M a b is the matrix cell for the pair (a, b)
  -- and it is equal to some .lt if a yields precedence to b

/-- `a ≐ b`. -/
abbrev OPAlphabet.equalPrec (G : OPAlphabet α) (a b : Option α) : Prop :=
  G.M a b = some .eq

/-- `a ⋗ b`. -/
abbrev OPAlphabet.takes (G : OPAlphabet α) (a b : Option α) : Prop :=
  G.M a b = some .gt

/-- Total matrix (Sec. I.1): no empty cell. -/
def OPAlphabet.Total (G : OPAlphabet α) : Prop :=
  ∀ a b, (G.M a b).isSome

/-- Inclusion between matrices, `M₁ ⊆ M₂` (Sec. I.1). -/
def OPAlphabet.Sub (G₁ G₂ : OPAlphabet α) : Prop :=
  ∀ a b r, G₁.M a b = some r → G₂.M a b = some r

/-- Two matrices are compatible if their union is conflict-free;
with DECISION 2 this is expressed as: wherever they are both
defined, they coincide (Sec. I.1). -/
def OPAlphabet.Compatible (G₁ G₂ : OPAlphabet α) : Prop :=
  ∀ a b r₁ r₂, G₁.M a b = some r₁ → G₂.M a b = some r₂ → r₁ = r₂

/-- Matrice partizionata (Fig. I.1.5): caratterizza la sottofamiglia
dei linguaggi visibly pushdown. `c` = call, `r` = return, `i` =
internal.
The idea is that you split the alphabet into three classes, and the calss alone determines
the relation:
call	open parenthesis	(, procedure call
ret	close parenthesis	), return
internal	neutral symbol	x, an assignment
-/
structure Partitioned (G : OPAlphabet α) (call ret internal : α → Prop) : Prop where
  covers : ∀ a, call a ∨ ret a ∨ internal a
  call_call : ∀ a b, call a → call b → G.M (some a) (some b) = some .lt
  call_ret : ∀ a b, call a → ret b → G.M (some a) (some b) = some .eq
  call_int : ∀ a b, call a → internal b → G.M (some a) (some b) = some .lt
  ret_any : ∀ a b, ret a → G.M (some a) (some b) = some .gt
  int_any : ∀ a b, internal a → G.M (some a) (some b) = some .gt
  /-
  call_call	call ⋖ call	Open a new nested frame: push.
  call_ret	call ≐ ret	The return matches the call: shift.
  call_int	call ⋖ internal	An internal symbol inside a call is pushed.
  ret_any	ret ⋗ anything	After a return, always reduce.
  int_any	internal ⋗ anything	An internal symbol is a leaf, so reduce right away.
  covers		Every terminal belongs to at least one class.
  -/

/-! ## Catene (Def. I.1.4)

DECISIONE 3 — catene indicizzate dalla profondità.
La definizione del paper è una ricorsione annidata: una catena composta
contiene una *lista* di sotto-catene. Scritta come inductive annidato
dentro `List` produce un ricorsore inutilizzabile; scritta con `∨` che
contiene l'occorrenza ricorsiva viene proprio rifiutata dal kernel
("invalid nested inductive datatype 'Or'").

Qui la catena è indicizzata da un `Nat` che maggiora la profondità
(Def. I.1.5): `ChainD G d a₀ x b` significa "catena di profondità ≤ d".
Due vantaggi:
* i sotto-corpi si quantificano per indice (`∀ i, i < xs.length → …`),
  che è strettamente positivo e lascia il ricorsore automatico;
* il principio di induzione usato ovunque nel paper ("we reason by
  induction on the depth h of the chain": Lemmi I.3.2, I.3.3, I.2.5,
  I.2.6) diventa *induzione su `Nat`*, cioè gratis.

`IsChain` è poi `∃ d, ChainD d`. -/

/-- `EqRun G f x l`: `x = f … l` con `≐` fra caratteri consecutivi.
Evita di dover parlare di `List.getLast` con la sua ipotesi `≠ []`.
it says that x runs from f to l with ≐ between consecutive elements.
It is used instead of getLast to avoid the non-emptiness proof

so: a simple chain has a1 = ... = an and to state the chain conditions
you need to takl about a1 and an
if you represent the chain as Lst α lean needs to check non-empty
instead: you represent as this runs from a1 to an -/
inductive EqRun (G : OPAlphabet α) : α → List α → α → Prop
  | single (a : α) : EqRun G a [a] a
  | cons {a b : α} {l : List α} {z : α} :
      G.M (some a) (some b) = some .eq →
      EqRun G b (b :: l) z →
      EqRun G a (a :: b :: l) z

/-- Catena semplice `a₀[a₁ a₂ … aₙ]ₐ₍ₙ₊₁₎` (Def. I.1.4, primo punto):
`a₀ ⋖ a₁ ≐ a₂ … ≐ aₙ ⋗ aₙ₊₁` e `M a₀ aₙ₊₁ ≠ ∅`. -/
def SimpleChain (G : OPAlphabet α) (a₀ : Option α) (x : List α) (b : Option α) : Prop :=
  ∃ f l, EqRun G f x l ∧          -- a1 ≐ … ≐ an
      G.M a₀ (some f) = some .lt ∧   -- a0 ⋖ a1
      G.M (some l) b = some .gt ∧    -- an ⋗ a(n+1)
      (G.M a₀ b).isSome              -- M(a0, a(n+1)) ≠ ∅


/- weave and borders are two helpers for composed chains:
weave xs as builds x0 a1 x1 … an xn from the gaps and the skeleton.
For example weave [[n],[n]] [+] = [n, +, n].
borders a₀ as b builds the list of contexts a0, a1, …, an, a(n+1).
Gap xi has context borders[i] on the left and borders[i+1] on the right.
For a₀ = none, as = [+], b = none you get [none, some +, none],
so x0 sits between # and +, and x1 between + and #.-/

/-- `weave [x₀, …, xₙ] [a₁, …, aₙ] = x₀ a₁ x₁ a₂ … aₙ xₙ`. -/
def weave : List (List α) → List α → List α
  | [], _ => []
  | x :: _, [] => x
  | x :: xs, a :: as => x ++ a :: weave xs as

/-- I contesti `a₀, a₁, …, aₙ, aₙ₊₁` che delimitano i sotto-corpi
`x₀, …, xₙ` di una catena composta. -/
def borders (a₀ : Option α) (as : List α) (b : Option α) : List (Option α) :=
  a₀ :: (as.map some ++ [b])

/-- Catena di profondità al più `d` (Def. I.1.4 + I.1.5).
Il costruttore `composed` copre anche il caso semplice, prendendo tutti
i sotto-corpi vuoti. -/
inductive ChainD (G : OPAlphabet α) : Nat → Option α → List α → Option α → Prop
  | simple {d a₀ x b} :
      SimpleChain G a₀ x b → ChainD G (d + 1) a₀ x b
  | composed {d a₀ as b} {xs : List (List α)} :
      SimpleChain G a₀ as b →
      xs.length = as.length + 1 →
      (∀ i, (h : i < xs.length) → xs[i] ≠ [] →
        ChainD G d ((borders a₀ as b).getD i none) xs[i]
                   ((borders a₀ as b).getD (i + 1) none)) →
      ChainD G (d + 1) a₀ (weave xs as) b

/-- Catena (Def. I.1.4), senza vincolo di profondità. -/
def IsChain (G : OPAlphabet α) (a₀ : Option α) (x : List α) (b : Option α) : Prop :=
  ∃ d, ChainD G d a₀ x b

/-- `x` ha profondità `d` (Def. I.1.5): è una catena di profondità `≤ d`
ma non `≤ d - 1`. recovers the exact depth-/
def HasDepth (G : OPAlphabet α) (a₀ : Option α) (x : List α) (b : Option α) (d : Nat) : Prop :=
  ChainD G d a₀ x b ∧ ∀ e, e < d → ¬ ChainD G e a₀ x b

/-! ## Parole compatibili (Def. I.1.6) -/

/-- Fattore (sottostringa) di una lista.
x is a contiguous substring of w.
IsFactor [c, d] w means c and d sit next to each other somewhere in w.-/
def IsFactor (x w : List α) : Prop :=
  ∃ pre post, w = pre ++ x ++ post

/-- Scheletro di catena semplice `a₀ ⋖ a₁ ≐ … ≐ aₙ ⋗ aₙ₊₁`, cioè la
catena semplice senza la richiesta `M a₀ aₙ₊₁ ≠ ∅`: è la premessa
della seconda condizione di Def. I.1.6. -/
def SimpleSkeleton (G : OPAlphabet α) (a₀ : Option α) (x : List α) (b : Option α) : Prop :=
  ∃ f l, EqRun G f x l ∧
         G.M a₀ (some f) = some .lt ∧
         G.M (some l) b = some .gt

/-- Parola compatibile con `M` (Def. I.1.6). -/
def Compatible (G : OPAlphabet α) (w : List α) : Prop :=
  -- (i) ogni coppia di caratteri consecutivi è in relazione
  -- Every two consecutive letters c d in w must have a non-empty cell M(c,d)
  --This rules out … M L … in the arithmetic example,
  --since (M, L) is empty.
  --The pairs involving # are guaranteed by sharp_left and sharp_right,
  --so they aren't checked here.
  (∀ c d, IsFactor [c, d] w → (G.M (some c) (some d)).isSome) ∧
  -- (ii) ogni fattore di #w# che ha la forma a₀ x₀ a₁ … aₙ xₙ aₙ₊₁ con
  -- scheletro semplice e sotto-corpi che sono catene, ha M a₀ aₙ₊₁ ≠ ∅
  (∀ (a₀ b : Option α) (as : List α) (xs : List (List α)),
      IsFactor (weave xs as) w →
      xs.length = as.length + 1 →
      SimpleSkeleton G a₀ as b →
      (∀ i, (h : i < xs.length) → xs[i] ≠ [] →
        IsChain G ((borders a₀ as b).getD i none) xs[i]
                  ((borders a₀ as b).getD (i + 1) none)) →
      (G.M a₀ b).isSome)

/-- Il linguaggio massimo su `(Σ, M)`: tutte e sole le parole
compatibili (usato in Statement I.1.1 per il complemento). -/
def maxLang (G : OPAlphabet α) : Language α := {w | Compatible G w}

end OPL
