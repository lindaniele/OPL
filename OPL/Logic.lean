/-
 MONADIC S O
-/
import OPL.Alphabet

namespace OPL

variable {α : Type}

/-! ## positions

a formula is read on `#w#`, so positions run from `0` to `|w| + 1`, with `0` and
`|w| + 1` taken by `#`. -/

/-- symbol at position `i` of `#w#`, `none` = `#`.
out of range it gives `none` too, so it always has to come with the constraint
`i ≤ w.length + 1` (see `Sat`) -/
def symbolAt (w : List α) : Nat → Option α
  | 0 => none
  | i + 1 => w[i]?

/-- the chars strictly between positions `i` and `j` -/
def between (w : List α) (i j : Nat) : List α :=
  (w.drop i).take (j - 1 - i)

/-! ## syntax (Def. I.4.1)

decision 13, variables are just naturals. `V₁` and `V₂` are both `Nat` and
assignments are `Nat → Nat` and `Nat → Nat → Prop`. lightestoption: no de Bruijn
indices, no typed contexts. price: *sentence* (formula with no free variables) is
not syntùactic any more it has to be said semantically (see `IsSentence`). if the
proofìs of sec. I.4 end up needing to andle free variableslikely in the MSO to
automata trnslation, which rewrites the formula killing predicates an first order
variables — then better to switcòh o de Bruijn. -/

/-- MSO formulas over `(Σ, M)` (Def. I.4.1) -/
inductive MSO (α : Type) where
  /-- `c(x)`: position `x` carries the char `c` (`none` = `#`) -/
  | lett (c : Option α) (x : Nat)
  /-- `x ∈ X` -/
  | mem (x X : Nat)
  /-- `x ≤ y` -/
  | le (x y : Nat)
  /-- `x ↷ y`: there is a chain between `x` and `y` -/
  | nest (x y : Nat)
  | neg (φ : MSO α)
  | or (φ ψ : MSO α)
  | ex1 (x : Nat) (φ : MSO α)
  | ex2 (X : Nat) (φ : MSO α)

/-- update a first order assignment-/
def upd1 (ν : Nat → Nat) (x n : Nat) : Nat → Nat :=
  fun y => if y = x then n else ν y

/-- update a second order assignmen-/
def upd2 (ν : Nat → Nat → Prop) (X : Nat) (S : Nat → Prop) : Nat → Nat → Prop :=
  fun Y => if Y = X then S else ν Y

/-- satisfaction `#w#, M, ν₁, ν₂ ⊧ φ` (Def. I.4.1) -/
def Sat (Γ : OPAlphabet α) (w : List α) : MSO α → (Nat → Nat) → (Nat → Nat → Prop) → Prop
  | .lett c x, ν₁, _ => ν₁ x ≤ w.length + 1 ∧ symbolAt w (ν₁ x) = c
  | .mem x X, ν₁, ν₂ => ν₂ X (ν₁ x)
  | .le x y, ν₁, _ => ν₁ x ≤ ν₁ y
  | .nest x y, ν₁, _ =>
      ν₁ y ≤ w.length + 1 ∧ ν₁ x < ν₁ y ∧
      IsChain Γ (symbolAt w (ν₁ x)) (between w (ν₁ x) (ν₁ y)) (symbolAt w (ν₁ y))
  | .neg φ, ν₁, ν₂ => ¬ Sat Γ w φ ν₁ ν₂
  | .or φ ψ, ν₁, ν₂ => Sat Γ w φ ν₁ ν₂ ∨ Sat Γ w ψ ν₁ ν₂
  | .ex1 x φ, ν₁, ν₂ => ∃ n, n ≤ w.length + 1 ∧ Sat Γ w φ (upd1 ν₁ x n) ν₂
  | .ex2 X φ, ν₁, ν₂ => ∃ S, Sat Γ w φ ν₁ (upd2 ν₂ X S)

/-- closed formula, semantically: truth value doesn't depend on the assignments
(see decision 13) -/
def IsSentence (Γ : OPAlphabet α) (φ : MSO α) : Prop :=
  ∀ w ν₁ ν₁' ν₂ ν₂', Sat Γ w φ ν₁ ν₂ ↔ Sat Γ w φ ν₁' ν₂'

/-- `L(φ)`, the language defined by a sentence -/
def MSOlang (Γ : OPAlphabet α) (φ : MSO α) : Language α :=
  {w | Sat Γ w φ (fun _ => 0) (fun _ _ => False)}

/-! ## shorthands the paper uses -/

/-- `φ ∧ ψ` -/
def MSO.and (φ ψ : MSO α) : MSO α := .neg (.or (.neg φ) (.neg ψ))

/-- `∀x. φ` -/
def MSO.all1 (x : Nat) (φ : MSO α) : MSO α := .neg (.ex1 x (.neg φ))

/-- `∀X. φ` -/
def MSO.all2 (X : Nat) (φ : MSO α) : MSO α := .neg (.ex2 X (.neg φ))

/-- `φ → ψ` -/
def MSO.imp (φ ψ : MSO α) : MSO α := .or (.neg φ) ψ

end OPL
