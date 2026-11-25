import Conjectures.QuasisymmetricBruhat.Coef
import Mathlib.Logic.Relation

/-!
# The quasisymmetric Bruhat order (Definition 2.7) and zigzag forests (Definition 6.8)

`MonkCover F G`: for some `i ≥ 1` the product `(x₁ + ⋯ + xᵢ) P_F` is the sum of the forest
polynomials of a finite set of forests containing `G`.  By uniqueness of forest expansions
(`ecoeff`), the set is the support of the expansion, so `MonkCover F G` forces the coefficient
`coefL G i F` to be `1`; conversely a decidable check of all candidate coefficients
(`monkCover_of_check`) certifies a cover.
-/

namespace QuasisymmetricBruhat

open MvPolynomial Finset Forest

/-- Definition 2.7: `F ⋖ G` iff `P_G` appears in `(x₁ + ⋯ + xᵢ) P_F` for some `i ≥ 1`. -/
def MonkCover (F G : Forest) : Prop :=
  ∃ i, 1 ≤ i ∧ ∃ S : Finset Forest, G ∈ S ∧ L i * forestPoly F = ∑ H ∈ S, forestPoly H

/-- The quasisymmetric Bruhat order: the reflexive-transitive closure of Monk covers. -/
def QBruhatLE : Forest → Forest → Prop := Relation.ReflTransGen MonkCover

/-- Definition 6.8: all code entries before the last nonzero one are positive. -/
def IsZigzag (F : Forest) : Prop := ∀ a ∈ F.code, 0 < a

/-- Principal lower interval `[∅, F]`. -/
def lowerInterval (F : Forest) : Set Forest := {E | QBruhatLE E F}

lemma sum_mem_supported (S : Finset Forest) :
    (∑ H ∈ S, forestPoly H) ∈ supported ℤ posVars :=
  Subalgebra.sum_mem _ fun H _ => forestPoly_mem_supported H

lemma cover_coefL {F G : Forest} (h : MonkCover F G) : ∃ i, 1 ≤ i ∧ coefL G i F = 1 := by
  classical
  obtain ⟨i, hi, S, hG, hS⟩ := h
  refine ⟨i, hi, ?_⟩
  rw [← coefL_eq hi, hS]
  have := ecoeff_finset_sum S (fun _ => 1) G
  simp only [one_smul] at this
  rw [this, if_pos hG]

lemma cover_size {F G : Forest} (h : MonkCover F G) : G.size = F.size + 1 := by
  obtain ⟨i, hi, hc⟩ := cover_coefL h
  exact coefLAux_size _ G rfl i F (by unfold coefL at hc; rw [hc]; decide)

/-- Lower covers are found among the candidates `lowL G i` with `i ≤ |code G| + |G|`. -/
lemma cover_lowL {F G : Forest} (h : MonkCover F G) :
    ∃ i, 1 ≤ i ∧ i ≤ G.len + G.size ∧ F ∈ lowL G i ∧ coefL G i F = 1 := by
  obtain ⟨i, hi, hc⟩ := cover_coefL h
  have hne : coefLAux G.size G i F ≠ 0 := by unfold coefL at hc; rw [hc]; decide
  exact ⟨i, hi, coefLAux_bound _ G rfl i F hne, lowLAux_sound _ G i F hne, hc⟩

/-- A decidable certificate for a Monk cover. -/
theorem monkCover_of_check {F G₀ : Forest} {k : ℕ} (hk : 1 ≤ k)
    (hcheck : ∀ G ∈ upL k F, coefL G k F = 0 ∨ coefL G k F = 1) (hG₀ : coefL G₀ k F = 1) :
    MonkCover F G₀ := by
  classical
  have hsound : ∀ G, coefL G k F ≠ 0 → G ∈ upL k F := fun G hG =>
    upLAux_sound _ G rfl k F hk hG
  set S := ((upL k F).filter (fun G => coefL G k F = 1)).toFinset
  have hmemS : ∀ G, G ∈ S ↔ coefL G k F = 1 := by
    intro G
    simp only [S, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨hsound G (by rw [h]; decide), h⟩
  refine ⟨k, hk, S, (hmemS G₀).2 hG₀, ?_⟩
  have heq : ecoeff (L k * forestPoly F) = ecoeff (∑ H ∈ S, forestPoly H) := by
    ext G
    have h1 := ecoeff_finset_sum S (fun _ => 1) G
    simp only [one_smul] at h1
    rw [h1, coefL_eq hk]
    by_cases hc : coefL G k F = 0
    · rw [hc, if_neg (by rw [hmemS, hc]; decide)]
    · rcases hcheck G (hsound G hc) with h | h
      · exact absurd h hc
      · rw [h, if_pos ((hmemS G).2 h)]
  rw [ecoeff_spec (LP_mem k F), ecoeff_spec (sum_mem_supported S), heq]

/-! ### Grading -/

lemma le_size {F G : Forest} (h : QBruhatLE F G) : F.size ≤ G.size := by
  induction h with
  | refl => exact le_rfl
  | tail _ hc ih => have := cover_size hc; omega

lemma size_lt_of_le_ne {F G : Forest} (h : QBruhatLE F G) (hne : F ≠ G) : F.size < G.size := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨M, hM, hc⟩
  · exact absurd rfl hne
  · have := le_size hM; have := cover_size hc; omega

lemma eq_of_le_of_size {F G : Forest} (h : QBruhatLE F G) (hs : G.size ≤ F.size) : F = G := by
  by_contra hne; have := size_lt_of_le_ne h hne; omega

lemma QBruhatLE.antisymm {F G : Forest} (h1 : QBruhatLE F G) (h2 : QBruhatLE G F) : F = G :=
  eq_of_le_of_size h1 (le_size h2)

lemma QBruhatLE.trans {F G H : Forest} (h1 : QBruhatLE F G) (h2 : QBruhatLE G H) :
    QBruhatLE F H := Relation.ReflTransGen.trans h1 h2

lemma QBruhatLE.refl (F : Forest) : QBruhatLE F F := Relation.ReflTransGen.refl

lemma QBruhatLE.of_cover {F G : Forest} (h : MonkCover F G) : QBruhatLE F G :=
  Relation.ReflTransGen.single h

/-- A relation `F ≤ G` with `|G| = |F| + 1` is a cover. -/
lemma cover_of_le {F G : Forest} (h : QBruhatLE F G) (hs : G.size = F.size + 1) :
    MonkCover F G := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨M, hM, hc⟩
  · omega
  · have := cover_size hc
    rw [eq_of_le_of_size hM (by omega)]; exact hc

/-- Peel the last cover off a strict relation. -/
lemma exists_cover_of_le {F G : Forest} (h : QBruhatLE F G) (hne : F ≠ G) :
    ∃ M, QBruhatLE F M ∧ MonkCover M G := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨M, hM, hc⟩
  · exact absurd rfl hne
  · exact ⟨M, hM, hc⟩

lemma size_empty : empty.size = 0 := rfl

end QuasisymmetricBruhat
