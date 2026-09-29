/-
  OPL/Statements.lean

  every statement of Part I, formalized and not proved yet. each `sorry` in here
  is a work item-/
import OPL.Automaton
import OPL.Determinization
import OPL.Grammar
import OPL.Logic

namespace OPL

open scoped Computability

variable {α β : Type}

/-! ## operations on languages

these are Mathlib's on `Language α`, not redefined here: `L₁ + L₂` union,
`L₁ ⊓ L₂` intersection, `L₁ * L₂` concatenation, `L∗` Kleene star, `Lᶜ` absolute
complement, `L₁ - L₂` difference, `Language.map f L` homomorphic image. the win
isn't in the defs — those were five lines — but in the lemmas about `++`,
`flatten` and `List.map` that come with them. -/

/-- complement *relative* to the universe of compatible words. that's the form the
paper states closure in (`L₁max \ L₁`) -/
def Lcompl (Γ : OPAlphabet α) (L : Language α) : Language α :=
  maxLang Γ - L

/-- union of two matrices (sec. I.1).

decision 14,the union is *defined* by taking `Γ₁` where it's defined. with
decisioì2 a matrix can't have conflicts, so the paper' set-theoretic union isn't
represeìtable as is. `unionM` gives the right matrix exactly when `Γ₁` and `Γ₂` are
compatible — which is what the paper assumeìanywhee i uses the union. outside
that case `unionM` is not he union, so the statements always use it under
`Γ₁.Compatible Γ₂`. -/
def unionM (Γ₁ Γ₂ : OPAlphabet α) : OPAlphabet α where
  M a b := match Γ₁.M a b with
    | some r => some r
    | none => Γ₂.M a b
  sharp_left a := by simp only [Γ₁.sharp_left a]
  sharp_right a := by simp only [Γ₁.sharp_right a]

/-! ## sec. I.2 — bridge between operational semantics and supports

not a numbered lemma of the paper, but implicit all over sec. I.2 and needed by
every proof that goes from runs to supports ,,,,,,,,
t piece of infrastructure to build, it pays off everywhere. -/

/-- a run that starts and ends with empty stack eating the whole input is exactly a
support for the chain `#[w]#` -/
theorem accepts_iff_support {Q : Type} (A : OPA α Q) (w : List α) (hw : w ≠ []) :
    (∃ qi qf, qi ∈ A.I ∧ qf ∈ A.F ∧ Steps A ⟨[], qi, w⟩ ⟨[], qf, []⟩) ↔
    (∃ qi qf, qi ∈ A.I ∧ qf ∈ A.F ∧ HasSupport A qi w qf) := by
  sorry

/-- an OPA "selects a subset of the universe of the strings compatible with `M`"
(sec. I.2). good first target: only uses the defs, and validates them -/
theorem accepts_compatible {Q : Type} (A : OPA α Q) {w : List α} :
    Accepts A w → Compatible A.G w := by
  sorry

/-! ## Statement I.1.1 — boolean algebra -/

/-- closure under intersection (product construction) -/
theorem opl_inter {Γ₁ Γ₂ : OPAlphabet α} (hc : Γ₁.Compatible Γ₂)
    {L₁ L₂ : Language α} (h₁ : IsOPL Γ₁ L₁) (h₂ : IsOPL Γ₂ L₂) :
    IsOPL (unionM Γ₁ Γ₂) (L₁ ⊓ L₂) := by
  sorry

/-- closure under union -/
theorem opl_union {Γ₁ Γ₂ : OPAlphabet α} (hc : Γ₁.Compatible Γ₂)
    {L₁ L₂ : Language α} (h₁ : IsOPL Γ₁ L₁) (h₂ : IsOPL Γ₂ L₂) :
    IsOPL (unionM Γ₁ Γ₂) (L₁ + L₂) := by
  sorry

/-- closure under complement wrt the universe of compatible words. in the paper it
follows from determinization (Thm I.2.4) -/
theorem opl_compl {Γ : OPAlphabet α} {L : Language α} (h : IsOPL Γ L) :
    IsOPL Γ (Lcompl Γ L) := by
  sorry

/-- if the matrix is total, the absolute complement is an OPL too -/
theorem opl_compl_total {Γ : OPAlphabet α} (ht : Γ.Total)
    {L : Language α} (h : IsOPL Γ L) :
    IsOPL Γ Lᶜ := by
  sorry

/-! ## Statement I.1.2 — concatenation, star, homomorphisms -/

theorem opl_concat {Γ₁ Γ₂ : OPAlphabet α} (hc : Γ₁.Compatible Γ₂)
    {L₁ L₂ : Language α} (h₁ : IsOPL Γ₁ L₁) (h₂ : IsOPL Γ₂ L₂) :
    ∃ Γ, (unionM Γ₁ Γ₂).Compatible Γ ∧ IsOPL Γ (L₁ * L₂) := by
  sorry

theorem opl_star {Γ : OPAlphabet α} {L : Language α} (h : IsOPL Γ L) :
    ∃ Γ', Γ.Compatible Γ' ∧ IsOPL Γ' L∗ := by
  sorry

/-- closure under alphabetic homomorphisms that keep conflict-freeness: `hpres` is
how I spell out "preserve conflict-freedom" -/
theorem opl_hom {Γ : OPAlphabet α} {Γ' : OPAlphabet β} (f : α → β)
    (hpres : ∀ a b r, Γ.M (some a) (some b) = some r →
      Γ'.M (some (f a)) (some (f b)) = some r)
    {L : Language α} (h : IsOPL Γ L) :
    IsOPL Γ' (Language.map f L) := by
  sorry

/-! ## sec. I.3 — automata vs grammars -/

/-- Thm I.3.1. from an OPG build an equivalent OPA with the same matrix -/
theorem opa_of_opg {N : Type} (G : CFG α N) (hG : IsOPG G)
    (Γ : OPAlphabet α) (hΓ : Agrees Γ G) :
    ∃ (Q : Type) (A : OPA α Q), A.G = Γ ∧ ∀ w, Accepts A w ↔ w ∈ langG G := by
  sorry

/-! Thm I.3.1, quantitative part: if `m` is the sum of the lengths of the r.h.s.
of `G`, the automaton has `O(m²)` states.

decision 15, th bound needs grammas with enumerated rules. `CFG` has `P`
relational (decision 10) so there is no "sum of the lengths of the r.h.s." to talk
about. statingù the bound needs ì finite pesentaion,ie a list of rules. will add
it when actually attacking this part; for now the bound is not stated. -/


/-- Corollary I.3.4. if the grammar is in Fischer normal form, the automaton built
in Thm I.3.1 is already deterministic -/
theorem opa_of_fnf_deterministic {N : Type} (G : CFG α N) (hG : IsOPG G)
    (hf : FNF G) (Γ : OPAlphabet α) (hΓ : Agrees Γ G) :
    ∃ (Q : Type) (A : OPA α Q), A.G = Γ ∧ Deterministic A ∧
      ∀ w, Accepts A w ↔ w ∈ langG G := by
  sorry

/-- Thm I.3.5. from an OPA build an equivalent OPG -/
theorem opg_of_opa {Q : Type} (A : OPA α Q) :
    ∃ (N : Type) (G : CFG α N), IsOPG G ∧ Agrees A.G G ∧
      ∀ w, w ∈ langG G ↔ Accepts A w := by
  sorry

/-- sec. I.3, punchline: the two definitions of OPL are the same -/
theorem isOPL_iff_isOPLg (Γ : OPAlphabet α) (L : Language α) :
    IsOPL Γ L ↔ IsOPLg Γ L := by
  sorry

/-! ## sec. I.4 — logical characterization -/

/-- Statement I.4.1. from an MSO sentence to an OPA -/
theorem opa_of_mso (Γ : OPAlphabet α) (φ : MSO α) (hφ : IsSentence Γ φ) :
    IsOPL Γ (MSOlang Γ φ) := by
  sorry

/-- Statement I.4.2. from an OPA to an MSO sentence -/
theorem mso_of_opa {Q : Type} (A : OPA α Q) :
    ∃ φ : MSO α, IsSentence A.G φ ∧ ∀ w, w ∈ MSOlang A.G φ ↔ Accepts A w := by
  sorry

/-- Thm I.4.2. `L` is an OPL over `(Σ, M)` iff it's defined by an MSO sentence over
`(Σ, M)` -/
theorem opl_iff_mso (Γ : OPAlphabet α) (L : Language α) :
    IsOPL Γ L ↔ ∃ φ : MSO α, IsSentence Γ φ ∧ ∀ w, w ∈ L ↔ w ∈ MSOlang Γ φ := by
  sorry

/-! ## Part I statements NOT formalized

* **Statement I.1.3**

* **sec. I.2.3**

* **Lemmas I.3.2 and I.3.3**. t

* **Lemmas I.4.3 and I.4.4**.
-/

end OPL
