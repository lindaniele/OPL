/-
  OPL/Deterinization.lean

  sec I.2.2: the eqivalent determinstic automaton and the two lemmas the
  equivalence proof rests on. Thm I.2.4, Lemmas I.2.5 and I.2.6.
-/
import Mathlib.Data.Fintype.Card
import OPL.Automaton

namespace OPL

variable {α : Type} {Q : Type}

/-! ## the Ã construction (Thm I.2.4)

sates of `Ã` are *sets f pairs* of state of`A`: firstcomponetsimulates `A`,
secnd one remembers the state that fired he current push and gets carried along by
the shfts. the paper's `⊺` (baselineof the computation) is `none : Option Q`.

decisio 8, the construction is deined, not just postulated. Thm I.2.4 could have
been stte as "there is an equivalent deterministic OPA". spelling out `detOPA`
costs a few lins more and makes Lemmas .2.5 and I.2.6 *statable at all*, since
they talk about `Ã` and not about some automaton. plus determinism of `detOPA` comes
out immedately (below) — first `sorry` closed in the project. -/

/-- state of `Ã`: a set of pairs `(state, origin)`, `none` for the paper's `⊺` -/
abbrev DetState (Q : Type) : Type := Set (Q × Option Q)

/-- the deterministic automaton `Ã` buil from `A` (Thm I.2.4) -/
def detOPA (A : OPA α Q) : OPA α (DetState Q) where
  G := A.G
  I := {K | K = {x | x.1 ∈ A.I ∧ x.2 = none}}
  F := {K | ∃ q, (q, none) ∈ K ∧ q ∈ A.F}
  push := fun K a K' =>
    K' = {x | ∃ q p, x.2 = some q ∧ (q, p) ∈ K ∧ A.push q a x.1}
  shift := fun K a K' =>
    K' = {x | ∃ q, (q, x.2) ∈ K ∧ A.shift q a x.1}
  pop := fun K₁ K₂ K' =>
    K' = {x | ∃ r q, (r, some q) ∈ K₁ ∧ (q, x.2) ∈ K₂ ∧ A.pop r q x.1}

/-- `Ã` is deterministic -/
theorem detOPA_deterministic (A : OPA α Q) : Deterministic (detOPA A) where
  init := ⟨_, rfl, fun _ h => h⟩
  det_push := fun _ _ => ⟨_, rfl, fun _ h => h⟩
  det_shift := fun _ _ => ⟨_, rfl, fun _ h => h⟩
  det_pop := fun _ _ => ⟨_, rfl, fun _ h => h⟩

/-- `Ã` has the same OP alphabet as `A` -/
theorem detOPA_alphabet (A : OPA α Q) : (detOPA A).G = A.G := rfl

/-! ## the two support-transport lemmas -/

/-- Lemma I.2.5. if `y` is the bdy of a chain with support `q ↝ q'` in `A`, then
for every `p` and every `K` with `(q, p) ∈ K` there'sa support `K ↝ K'` in `Ã`
with `(q', p) ∈ K'` -/
theorem support_det_of_support (A : OPA α Q) {q q' : Q} {y : List α}
    (hy : HasSupport A q y q') (p : Option Q) (K : DetState Q) (hK : (q, p) ∈ K) :
    ∃ K', HasSupport (detOPA A) K y K' ∧ (q', p) ∈ K' := by
  sorry

/-- Lemma I.2.6. other way round: if `y` is the body of a chain with support
`K ↝ K'` in `Ã`, then for every `(q', p) ∈ K'` there's  `q` with `(q, p) ∈ K` and a
support `q ↝ q'` in `A` -/
theorem support_of_support_det (A : OPA α Q) {K K' : DetState Q} {y : List α}
    (hy : HasSupport (detOPA A) K y K') (q' : Q) (p : Option Q) (hK' : (q', p) ∈ K') :
    ∃ q, (q, p) ∈ K ∧ HasSupport A q y q' := by
  sorry

/-! ## Thm I.2.4 -/

/-- Thm I.2.4, language part: `Ã` recognizes the same language as `A` -/
theorem detOPA_equiv (A : OPA α Q) (w : List α) :
    Accepts (detOPA A) w ↔ Accepts A w := by
  sorry

/-- Thm I.2.4, quantitative part: from `s` state you get an equivalent
deterministic automaton with `2^(s·(s+1))` states, ie `2^O(s²)`.

decision 9, finiteness only showsup here. the rest of the library never asks `Q`
to be finite (decision 7). here I need to count: `Q` carries a `Fintype` instance
and the cardinality is `Fintype.card`, instead of being baked into the state type
like in the pre-Mathlib version (`OPA α (Fin (2 ^ (n * (n + 1)))`).
the count is exact, not an upper bound: states of `Ã` are
`DetState Q = Set (Q × Option Q)`, which has exactly `2 ^ (card Q * (card Q + 1))`
elements. -/
theorem detOPA_card {Q : Type} [Fintype Q] (A : OPA α Q) :
    ∃ (Q' : Type) (_inst : Fintype Q') (A' : OPA α Q'),
      Fintype.card Q' = 2 ^ (Fintype.card Q * (Fintype.card Q + 1)) ∧
      A'.G = A.G ∧ Deterministic A' ∧ ∀ w, Accepts A' w ↔ Accepts A w := by
  sorry

/-- corollary of Thm I.2.4: every OPL is recognized by a deterministic OPA -/
theorem opl_deterministic (G : OPAlphabet α) (L : Language α) (h : IsOPL G L) :
    ∃ (Q' : Type) (A : OPA α Q'), A.G = G ∧ Deterministic A ∧ ∀ w, w ∈ L ↔ Accepts A w := by
  sorry

end OPL
