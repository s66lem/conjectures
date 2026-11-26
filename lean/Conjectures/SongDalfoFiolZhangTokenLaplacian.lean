import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# Resolution of the Song–Dalfó–Fiol–Zhang Conjecture on the Laplacian Spectral
# Radius of Token Graphs (`arXiv:2610.00500v1`)

In *The Algebraic Connectivity and Laplacian Spectral Radius of Token Graphs*
(`arXiv:2610.00500v1`, September 2026), X. Song, C. Dalfó, M. À. Fiol, and
S. Zhang conjectured that for a graph `G` of order `n ≥ 4`, the equality
`ρ(F_k(G)) = ρ(G)` holds for all `2 ≤ k ≤ ⌊n / 2⌋` if and only if `G ≅ S_n`.

We prove:
1. `connected_nonstar_rho_F2_gt`: For every connected non-star graph `G` of
   order `n ≥ 4`, `ρ(F_2(G)) > ρ(G)` (establishing the connected conjecture
   in `connected_conjecture_iff`).
2. `all_graphs_equality_iff`: For an arbitrary graph `G` of order `n ≥ 4`,
   `ρ(F_k(G)) = ρ(G)` for all `2 ≤ k ≤ ⌊n / 2⌋` if and only if `G` is edgeless,
   a star plus isolated vertices `S_m ∪ (n - m)K_1` (`m ≥ 2`), or a triangle
   plus isolated vertices `K_3 ∪ (n - 3)K_1`.
-/

namespace SongDalfoFiolZhangTokenLaplacian

open Matrix SimpleGraph Finset

/-! ### 1. Token Graphs and Laplacian Spectral Radius -/

/-- Vertices of the `k`-token graph `F_k(G)`: `k`-element subsets of `V`. -/
abbrev TokenVertex (V : Type*) [DecidableEq V] (k : ℕ) :=
  {S : Finset V // S.card = k}

/-- The `k`-token graph `F_k(G)`: two `k`-subsets `S, T` are adjacent iff
`T` is obtained from `S` by moving a single token along an edge of `G`. -/
def tokenGraph {V : Type*} [DecidableEq V] (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph (TokenVertex V k) where
  Adj S T := ∃ u v : V, u ∈ S.1 ∧ u ∉ T.1 ∧ v ∈ T.1 ∧ v ∉ S.1 ∧
    G.Adj u v ∧ S.1.erase u = T.1.erase v
  symm := ⟨fun _ _ ⟨u, v, huS, huT, hvT, hvS, huv, heq⟩ =>
    ⟨v, u, hvT, hvS, huS, huT, huv.symm, heq.symm⟩⟩
  loopless := ⟨fun _ ⟨_, _, huS, huT, _⟩ => huT huS⟩

/-- Decidability of adjacency in the `k`-token graph on a finite vertex type. -/
instance instDecidableRelTokenGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    DecidableRel (tokenGraph G k).Adj := fun S T => by
  unfold tokenGraph
  dsimp only
  infer_instance

/-- Equivalent symmetric-difference characterization of adjacency in `F_k(G)`. -/
theorem tokenGraph_adj_iff_symmDiff {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (S T : TokenVertex V k) :
    (tokenGraph G k).Adj S T ↔ ∃ u v : V, G.Adj u v ∧ symmDiff S.1 T.1 = {u, v} := by
  constructor
  · rintro ⟨u, v, huS, huT, hvT, hvS, huv, heq⟩
    refine ⟨u, v, huv, ?_⟩
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    by_cases hxu : x = u
    · subst hxu; simp [huS, huT]
    · by_cases hxv : x = v
      · subst hxv; simp [hvT, hvS]
      · have hx1 : x ∈ S.1 ↔ x ∈ S.1.erase u := (Finset.mem_erase.trans (and_iff_right hxu)).symm
        have hx2 : x ∈ T.1 ↔ x ∈ T.1.erase v := (Finset.mem_erase.trans (and_iff_right hxv)).symm
        rw [hx1, hx2, heq]
        tauto
  · rintro ⟨u, v, huv, hsd⟩
    have hne : u ≠ v := G.ne_of_adj huv
    have hu_sd : u ∈ symmDiff S.1 T.1 := by rw [hsd]; simp
    have hv_sd : v ∈ symmDiff S.1 T.1 := by rw [hsd]; simp
    rw [Finset.mem_symmDiff] at hu_sd hv_sd
    -- Cannot have both `u, v ∈ S \ T` or both `u, v ∈ T \ S` because `S.card = T.card`.
    have hcard_eq : (S.1 \ T.1).card = (T.1 \ S.1).card := by
      have h1 := Finset.card_sdiff_add_card_inter S.1 T.1
      have h2 := Finset.card_sdiff_add_card_inter T.1 S.1
      rw [Finset.inter_comm] at h2
      have hST : S.1.card = T.1.card := S.2.trans T.2.symm
      omega
    have hsd_union : (S.1 \ T.1) ∪ (T.1 \ S.1) = {u, v} := hsd
    have hdisj : Disjoint (S.1 \ T.1) (T.1 \ S.1) :=
      Finset.disjoint_left.mpr fun x h1 h2 => (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
    have hsum2 : (S.1 \ T.1).card + (T.1 \ S.1).card = 2 := by
      rw [← Finset.card_union_of_disjoint hdisj, hsd_union, Finset.card_pair hne]
    have hcard1 : (S.1 \ T.1).card = 1 := by omega
    rcases hu_sd with ⟨huS, huT⟩ | ⟨huT, huS⟩
    · have hvTS : v ∈ T.1 ∧ v ∉ S.1 := by
        rcases hv_sd with ⟨hvS, hvT⟩ | hv
        · have hsub : ({u, v} : Finset V) ⊆ S.1 \ T.1 := by
            intro x hx; simp at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_sdiff.mpr ⟨huS, huT⟩
            · exact Finset.mem_sdiff.mpr ⟨hvS, hvT⟩
          have := Finset.card_le_card hsub
          rw [Finset.card_pair hne] at this; omega
        · exact hv
      refine ⟨u, v, huS, huT, hvTS.1, hvTS.2, huv, ?_⟩
      ext x
      simp only [Finset.mem_erase]
      by_cases hxu : x = u
      · subst hxu; simp [huT]
      · by_cases hxv : x = v
        · subst hxv; simp [hvTS.2]
        · have hnot : x ∉ symmDiff S.1 T.1 := by rw [hsd]; simp [hxu, hxv]
          rw [Finset.mem_symmDiff] at hnot
          tauto
    · have hvST : v ∈ S.1 ∧ v ∉ T.1 := by
        rcases hv_sd with hv | ⟨hvT, hvS⟩
        · exact hv
        · have hsub : ({u, v} : Finset V) ⊆ T.1 \ S.1 := by
            intro x hx; simp at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_sdiff.mpr ⟨huT, huS⟩
            · exact Finset.mem_sdiff.mpr ⟨hvT, hvS⟩
          have := Finset.card_le_card hsub
          rw [Finset.card_pair hne] at this; omega
      refine ⟨v, u, hvST.1, hvST.2, huT, huS, huv.symm, ?_⟩
      ext x
      simp only [Finset.mem_erase]
      by_cases hxv : x = v
      · subst hxv; simp [hvST.2]
      · by_cases hxu : x = u
        · subst hxu; simp [huS]
        · have hnot : x ∉ symmDiff S.1 T.1 := by rw [hsd]; simp [hxu, hxv]
          rw [Finset.mem_symmDiff] at hnot
          tauto

/-- Laplacian quadratic form `fᵀ L(G) f`. -/
noncomputable def lapQuad {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) : ℝ :=
  f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)

/-- Laplacian spectral radius `ρ(G)`: largest eigenvalue of `G.lapMatrix ℝ`
(and `0` on the empty graph). -/
noncomputable def lapSpectralRadius {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  open Classical in
  if _ : Nonempty V then
    (Finset.univ.image (G.isHermitian_lapMatrix ℝ).eigenvalues).max'
      (Finset.Nonempty.image Finset.univ_nonempty _)
  else 0

/-- `G` is a star graph `S_n` (`n ≥ 1`): some vertex `c` is adjacent to all other
vertices, and no other edges exist. -/
def IsStar {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ c : V, ∀ u v : V, G.Adj u v ↔ (u = c ∧ v ≠ c) ∨ (v = c ∧ u ≠ c)

private lemma lapQuad_eq_sum_sq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) :
    lapQuad G f = (∑ u : V, ∑ v : V, if G.Adj u v then (f u - f v) ^ 2 else 0) / 2 := by
  have h := G.lapMatrix_toLinearMap₂' ℝ f
  rw [Matrix.toLinearMap₂'_apply'] at h
  exact h

private lemma lapQuad_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) :
    0 ≤ lapQuad G f := by
  rw [lapQuad_eq_sum_sq]
  positivity

private lemma dotProduct_self_nonneg {V : Type*} [Fintype V] (f : V → ℝ) :
    0 ≤ f ⬝ᵥ f := by
  unfold dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (f i)

private lemma dotProduct_self_pos {V : Type*} [Fintype V] {f : V → ℝ} (hf : f ≠ 0) :
    0 < f ⬝ᵥ f := by
  have hex : ∃ i, f i ≠ 0 := by
    by_contra hall; push Not at hall; exact hf (funext hall)
  rcases hex with ⟨i, hi⟩
  have h1 : 0 < f i * f i := mul_self_pos.mpr hi
  have h2 : f i * f i ≤ ∑ j : V, f j * f j :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (f j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le h1 h2

private lemma lapSpectralRadius_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ lapSpectralRadius G := by
  unfold lapSpectralRadius
  split_ifs with h
  · obtain ⟨v0⟩ := h
    have hle := Finset.le_max'
      (Finset.univ.image (G.isHermitian_lapMatrix ℝ).eigenvalues)
      ((G.isHermitian_lapMatrix ℝ).eigenvalues v0)
      (Finset.mem_image_of_mem _ (Finset.mem_univ v0))
    have h0 : 0 ≤ (G.isHermitian_lapMatrix ℝ).eigenvalues v0 := by
      have heq := (G.isHermitian_lapMatrix ℝ).eigenvalues_eq v0
      simp only [RCLike.re_to_real, star_trivial] at heq
      rw [heq]
      exact lapQuad_nonneg G _
    exact le_trans h0 hle
  · exact le_rfl

/-- Spectral upper bound (Rayleigh quotient): `fᵀ L(G) f ≤ ρ(G) (fᵀ f)` for every `f`. -/
theorem rayleigh_le_rho {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) :
    lapQuad G f ≤ lapSpectralRadius G * (f ⬝ᵥ f) := by
  by_cases hV : Nonempty V
  · set hL := G.isHermitian_lapMatrix ℝ
    set U : Matrix V V ℝ := (hL.eigenvectorUnitary : Matrix V V ℝ)
    have hUtU : Uᵀ * U = 1 := by
      have h := Unitary.coe_star_mul_self hL.eigenvectorUnitary
      simpa [U, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h
    have hUUt : U * Uᵀ = 1 := by
      have h := Unitary.coe_mul_star_self hL.eigenvectorUnitary
      simpa [U, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h
    have hspec : G.lapMatrix ℝ = U * Matrix.diagonal hL.eigenvalues * Uᵀ := by
      have h := hL.spectral_theorem
      simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        conjTranspose_eq_transpose_of_trivial, Function.comp_def, RCLike.ofReal_real_eq_id] using h
    set c : V → ℝ := Uᵀ *ᵥ f
    have hnorm : f ⬝ᵥ f = c ⬝ᵥ c := by
      calc f ⬝ᵥ f = f ⬝ᵥ ((U * Uᵀ) *ᵥ f) := by rw [hUUt, one_mulVec]
        _ = f ⬝ᵥ (U *ᵥ c) := by rw [mulVec_mulVec]
        _ = (Uᵀ *ᵥ f) ⬝ᵥ c := by rw [dotProduct_mulVec, ← mulVec_transpose]
        _ = c ⬝ᵥ c := rfl
    have hquad : lapQuad G f = ∑ i : V, hL.eigenvalues i * (c i * c i) := by
      unfold lapQuad
      calc f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)
          = f ⬝ᵥ ((U * Matrix.diagonal hL.eigenvalues * Uᵀ) *ᵥ f) := by conv_lhs => rw [hspec]
        _ = f ⬝ᵥ (U *ᵥ (Matrix.diagonal hL.eigenvalues *ᵥ c)) := by
            rw [mulVec_mulVec, mulVec_mulVec]
        _ = c ⬝ᵥ (Matrix.diagonal hL.eigenvalues *ᵥ c) := by
            rw [dotProduct_mulVec, ← mulVec_transpose]
        _ = ∑ i : V, hL.eigenvalues i * (c i * c i) := by
            simp only [dotProduct, mulVec_diagonal]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [hquad, hnorm]
    have hrho_ge : ∀ i : V, hL.eigenvalues i ≤ lapSpectralRadius G := by
      intro i
      unfold lapSpectralRadius
      rw [dif_pos hV]
      exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    calc ∑ i : V, hL.eigenvalues i * (c i * c i)
        ≤ ∑ i : V, lapSpectralRadius G * (c i * c i) := by
          refine Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hrho_ge i) (mul_self_nonneg (c i))
      _ = lapSpectralRadius G * (c ⬝ᵥ c) := by
          rw [← Finset.mul_sum]; rfl
  · have hsub : IsEmpty V := not_nonempty_iff.mp hV
    unfold lapQuad
    simp [dotProduct]

private lemma lt_rho_of_rayleigh {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ} {f : V → ℝ}
    (h : c * (f ⬝ᵥ f) < lapQuad G f) :
    c < lapSpectralRadius G := by
  have hle := rayleigh_le_rho G f
  have hpos : 0 < f ⬝ᵥ f := by
    by_cases hf : f = 0
    · subst hf; unfold lapQuad at h; simp [dotProduct] at h
    · exact dotProduct_self_pos hf
  nlinarith

private lemma le_rho_of_rayleigh {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ} {f : V → ℝ}
    (hf : f ≠ 0) (h : c * (f ⬝ᵥ f) ≤ lapQuad G f) :
    c ≤ lapSpectralRadius G := by
  have hle := rayleigh_le_rho G f
  have hpos : 0 < f ⬝ᵥ f := dotProduct_self_pos hf
  nlinarith

/-- Existence of a nonzero top eigenvector for `G.lapMatrix ℝ`. -/
theorem exists_top_eigenvector {V : Type*} [Fintype V] [DecidableEq V] [hV : Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ x : V → ℝ, x ≠ 0 ∧ G.lapMatrix ℝ *ᵥ x = lapSpectralRadius G • x := by
  set hL := G.isHermitian_lapMatrix ℝ
  have hmem : lapSpectralRadius G ∈ Finset.univ.image hL.eigenvalues := by
    unfold lapSpectralRadius
    rw [dif_pos hV]
    exact Finset.max'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
  refine ⟨⇑(hL.eigenvectorBasis i), ?_, ?_⟩
  · intro h0
    have hn : ‖hL.eigenvectorBasis i‖ = 1 := hL.eigenvectorBasis.orthonormal.1 i
    have hzero : hL.eigenvectorBasis i = 0 := by
      ext v; exact congr_fun h0 v
    rw [hzero, norm_zero] at hn
    norm_num at hn
  · rw [← hi]
    exact hL.mulVec_eigenvectorBasis i

/-- **Lemma 0 (Subgraph Monotonicity):** If `φ : V₁ → V₂` is an injective graph
homomorphism from `H` into `G`, then `ρ(H) ≤ ρ(G)`. -/
theorem rho_le_of_embedding {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂]
    {H : SimpleGraph V₁} {G : SimpleGraph V₂}
    [DecidableRel H.Adj] [DecidableRel G.Adj]
    (φ : V₁ → V₂) (hinj : Function.Injective φ)
    (hadj : ∀ u v : V₁, H.Adj u v → G.Adj (φ u) (φ v)) :
    lapSpectralRadius H ≤ lapSpectralRadius G := by
  by_cases hV₁ : Nonempty V₁
  · let : Nonempty V₁ := hV₁
    obtain ⟨x, hx0, hxeig⟩ := exists_top_eigenvector H
    let f : V₂ → ℝ := fun w => if h : ∃ u : V₁, φ u = w then x h.choose else 0
    have hf_phi : ∀ u : V₁, f (φ u) = x u := by
      intro u
      have hex : ∃ u' : V₁, φ u' = φ u := ⟨u, rfl⟩
      dsimp only [f]
      rw [dif_pos hex]
      exact congr_arg x (hinj hex.choose_spec)
    have hf_ne : f ≠ 0 := by
      intro h0
      apply hx0; ext u
      rw [← hf_phi u, h0]; rfl
    have hnorm : f ⬝ᵥ f = x ⬝ᵥ x := by
      unfold dotProduct
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image φ))]
      · rw [Finset.sum_image (fun a _ b _ h => hinj h)]
        refine Finset.sum_congr rfl fun u _ => by rw [hf_phi]
      · intro w _ hw
        dsimp only [f]
        have hnot : ¬ ∃ u : V₁, φ u = w := by
          rintro ⟨u, rfl⟩; exact hw (Finset.mem_image_of_mem _ (Finset.mem_univ u))
        rw [dif_neg hnot, mul_zero]
    have hquad_le : lapQuad H x ≤ lapQuad G f := by
      rw [lapQuad_eq_sum_sq, lapQuad_eq_sum_sq]
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      calc ∑ u : V₁, ∑ v : V₁, (if H.Adj u v then (x u - x v) ^ 2 else 0)
          ≤ ∑ u : V₁, ∑ v : V₁, (if G.Adj (φ u) (φ v) then (f (φ u) - f (φ v)) ^ 2 else 0) := by
            refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
            rw [hf_phi u, hf_phi v]
            split_ifs with h1 h2
            · exact le_rfl
            · exact absurd (hadj u v h1) h2
            · positivity
            · exact le_rfl
        _ = ∑ a ∈ Finset.univ.image φ, ∑ b ∈ Finset.univ.image φ,
              (if G.Adj a b then (f a - f b) ^ 2 else 0) := by
            rw [Finset.sum_image (fun a _ b _ h => hinj h)]
            refine Finset.sum_congr rfl fun u _ => by
              rw [Finset.sum_image (fun a _ b _ h => hinj h)]
        _ ≤ ∑ a : V₂, ∑ b : V₂, (if G.Adj a b then (f a - f b) ^ 2 else 0) := by
            refine Finset.sum_le_univ_sum_of_nonneg (fun a => Finset.sum_nonneg fun b _ => by positivity) |>
              le_trans (Finset.sum_le_sum fun a _ => Finset.sum_le_univ_sum_of_nonneg fun b => by positivity)
    have hx_quad : lapQuad H x = lapSpectralRadius H * (x ⬝ᵥ x) := by
      unfold lapQuad
      rw [hxeig, dotProduct_smul, smul_eq_mul]
    refine le_rho_of_rayleigh G hf_ne ?_
    rw [hnorm, ← hx_quad]
    exact hquad_le
  · unfold lapSpectralRadius
    rw [dif_neg hV₁]
    exact lapSpectralRadius_nonneg G

private lemma rho_eq_of_iso {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂]
    {H : SimpleGraph V₁} {G : SimpleGraph V₂}
    [DecidableRel H.Adj] [DecidableRel G.Adj]
    (e : H ≃g G) :
    lapSpectralRadius H = lapSpectralRadius G :=
  le_antisymm
    (rho_le_of_embedding e e.injective (fun _ _ h => e.map_rel_iff.mpr h))
    (rho_le_of_embedding e.symm e.symm.injective (fun _ _ h => e.symm.map_rel_iff.mpr h))

private lemma rho_pos_of_edge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    0 < lapSpectralRadius G := by
  let f : V → ℝ := Pi.single u 1
  have hquad : 0 < lapQuad G f := by
    rw [lapQuad_eq_sum_sq]
    have hne : u ≠ v := G.ne_of_adj huv
    have hterm : (0 : ℝ) < if G.Adj u v then (f u - f v) ^ 2 else 0 := by
      rw [if_pos huv]
      simp [f, Pi.single_eq_same, Pi.single_eq_of_ne hne.symm]
    have hsum1 : (if G.Adj u v then (f u - f v) ^ 2 else 0) ≤
        ∑ w : V, (if G.Adj u w then (f u - f w) ^ 2 else 0) :=
      Finset.single_le_sum (f := fun w => if G.Adj u w then (f u - f w) ^ 2 else 0)
        (fun w _ => by positivity) (Finset.mem_univ v)
    have hsum2 : (∑ w : V, (if G.Adj u w then (f u - f w) ^ 2 else 0)) ≤
        ∑ a : V, ∑ b : V, (if G.Adj a b then (f a - f b) ^ 2 else 0) :=
      Finset.single_le_sum (f := fun a => ∑ b : V, if G.Adj a b then (f a - f b) ^ 2 else 0)
        (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ u)
    linarith
  exact lt_rho_of_rayleigh G (by simpa using hquad)

/-! ### 2. Core Lemmas (Grone–Merris, Edge-Difference Bound, Perturbed Star Product) -/

/-- **Lemma 1 (Grone–Merris Star Test Vector):**
For any vertex `S` with `D = G.degree S ≥ 1`, `ρ(G) ≥ D + 1`, with strict inequality
if some neighbor `T` of `S` is adjacent to a vertex `U ∉ {S} ∪ N(S)`. -/
theorem grone_merris_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : V) (hD : 1 ≤ G.degree S) :
    (G.degree S : ℝ) + 1 ≤ lapSpectralRadius G := by
  let D : ℝ := G.degree S
  let f : V → ℝ := fun w => if w = S then D else if G.Adj S w then -1 else 0
  have hf_ne : f ≠ 0 := by
    intro h0
    have hS := congr_fun h0 S
    simp only [f, ↓reduceIte, Pi.zero_apply] at hS
    have : (1 : ℝ) ≤ D := by dsimp only [D]; exact_mod_cast hD
    linarith
  have hnorm : f ⬝ᵥ f = D * (D + 1) := by
    unfold dotProduct
    have hsplit : ∑ w : V, f w * f w =
        f S * f S + ∑ w ∈ G.neighborFinset S, f w * f w := by
      have hsub : insert S (G.neighborFinset S) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_insert (G.notMem_neighborFinset_self S)]
      · intro w _ hw
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hw
        simp [f, hw.1, hw.2]
    rw [hsplit]
    have hS : f S = D := by simp [f]
    have hN : ∀ w ∈ G.neighborFinset S, f w = -1 := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      simp [f, (G.ne_of_adj hw).symm, hw]
    rw [hS, Finset.sum_congr rfl (fun w hw => by rw [hN w hw])]
    simp only [mul_neg, neg_neg, mul_one, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul]
    ring
  have hquad : D * (D + 1) ^ 2 ≤ lapQuad G f := by
    rw [lapQuad_eq_sum_sq]
    have hS_row : ∑ w : V, (if G.Adj S w then (f S - f w) ^ 2 else 0) = D * (D + 1) ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_univ (G.neighborFinset S))]
      · have hterm : ∀ w ∈ G.neighborFinset S,
            (if G.Adj S w then (f S - f w) ^ 2 else 0) = (D + 1) ^ 2 := by
          intro w hw; rw [SimpleGraph.mem_neighborFinset] at hw
          simp [f, hw, (G.ne_of_adj hw).symm]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
          nsmul_eq_mul]
      · intro w _ hw; rw [SimpleGraph.mem_neighborFinset] at hw; simp [hw]
    have hN_rows : ∑ w ∈ G.neighborFinset S, ∑ u : V, (if G.Adj w u then (f w - f u) ^ 2 else 0) ≥
        D * (D + 1) ^ 2 := by
      calc ∑ w ∈ G.neighborFinset S, ∑ u : V, (if G.Adj w u then (f w - f u) ^ 2 else 0)
          ≥ ∑ w ∈ G.neighborFinset S, (if G.Adj w S then (f w - f S) ^ 2 else 0) :=
            Finset.sum_le_sum fun w _ =>
              Finset.single_le_sum (f := fun u => if G.Adj w u then (f w - f u) ^ 2 else 0)
                (fun u _ => by positivity) (Finset.mem_univ S)
        _ = D * (D + 1) ^ 2 := by
            have hterm : ∀ w ∈ G.neighborFinset S,
                (if G.Adj w S then (f w - f S) ^ 2 else 0) = (D + 1) ^ 2 := by
              intro w hw; rw [SimpleGraph.mem_neighborFinset] at hw
              simp [f, hw, hw.symm, (G.ne_of_adj hw).symm]; ring
            rw [Finset.sum_congr rfl hterm, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
              nsmul_eq_mul]
    have htot : (∑ w : V, (if G.Adj S w then (f S - f w) ^ 2 else 0)) +
        ∑ w ∈ G.neighborFinset S, ∑ u : V, (if G.Adj w u then (f w - f u) ^ 2 else 0) ≤
        ∑ a : V, ∑ b : V, (if G.Adj a b then (f a - f b) ^ 2 else 0) := by
      have hsub : insert S (G.neighborFinset S) ⊆ Finset.univ := Finset.subset_univ _
      have hins : (∑ w : V, (if G.Adj S w then (f S - f w) ^ 2 else 0)) +
          ∑ w ∈ G.neighborFinset S, ∑ u : V, (if G.Adj w u then (f w - f u) ^ 2 else 0) =
          ∑ a ∈ insert S (G.neighborFinset S), ∑ b : V, (if G.Adj a b then (f a - f b) ^ 2 else 0) :=
        (Finset.sum_insert (f := fun a => ∑ b : V, if G.Adj a b then (f a - f b) ^ 2 else 0)
          (G.notMem_neighborFinset_self S)).symm
      rw [hins]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun a _ _ =>
        Finset.sum_nonneg fun b _ => by positivity
    linarith
  refine le_rho_of_rayleigh G hf_ne ?_
  have heq : ((G.degree S : ℝ) + 1) * (f ⬝ᵥ f) = D * (D + 1) ^ 2 := by
    rw [hnorm]; dsimp only [D]; ring
  linarith

theorem grone_merris_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T U : V) (_hD : 1 ≤ G.degree S)
    (hST : G.Adj S T) (hTU : G.Adj T U) (hUS : U ≠ S) (hnotSU : ¬ G.Adj S U) :
    (G.degree S : ℝ) + 1 < lapSpectralRadius G := by
  let D : ℝ := G.degree S
  let f : V → ℝ := fun w => if w = S then D else if G.Adj S w then -1 else 0
  have hnorm : f ⬝ᵥ f = D * (D + 1) := by
    unfold dotProduct
    have hsplit : ∑ w : V, f w * f w =
        f S * f S + ∑ w ∈ G.neighborFinset S, f w * f w := by
      have hsub : insert S (G.neighborFinset S) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_insert (G.notMem_neighborFinset_self S)]
      · intro w _ hw
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hw
        simp [f, hw.1, hw.2]
    rw [hsplit]
    have hS : f S = D := by simp [f]
    have hN : ∀ w ∈ G.neighborFinset S, f w = -1 := by
      intro w hw; rw [SimpleGraph.mem_neighborFinset] at hw
      simp [f, (G.ne_of_adj hw).symm, hw]
    rw [hS, Finset.sum_congr rfl (fun w hw => by rw [hN w hw])]
    simp only [mul_neg, neg_neg, mul_one, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul]
    ring
  have hquad : D * (D + 1) ^ 2 < lapQuad G f := by
    rw [lapQuad_eq_sum_sq]
    have hS_row : ∑ w : V, (if G.Adj S w then (f S - f w) ^ 2 else 0) = D * (D + 1) ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_univ (G.neighborFinset S))]
      · have hterm : ∀ w ∈ G.neighborFinset S,
            (if G.Adj S w then (f S - f w) ^ 2 else 0) = (D + 1) ^ 2 := by
          intro w hw; rw [SimpleGraph.mem_neighborFinset] at hw
          simp [f, hw, (G.ne_of_adj hw).symm]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
          nsmul_eq_mul]
      · intro w _ hw; rw [SimpleGraph.mem_neighborFinset] at hw; simp [hw]
    have hT_extra : (if G.Adj T S then (f T - f S) ^ 2 else 0) + 1 ≤
        ∑ u : V, (if G.Adj T u then (f T - f u) ^ 2 else 0) := by
      have hsub : ({S, U} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by positivity : ∀ u ∈ Finset.univ, u ∉ ({S, U} : Finset V) → 0 ≤ if G.Adj T u then (f T - f u) ^ 2 else 0)
      rw [Finset.sum_pair hUS.symm] at hle
      have hTU_val : (if G.Adj T U then (f T - f U) ^ 2 else 0) = 1 := by
        simp [f, hST, (G.ne_of_adj hST).symm, hTU, hUS, hnotSU]
      linarith
    have hN_rows : D * (D + 1) ^ 2 + 1 ≤
        ∑ w ∈ G.neighborFinset S, ∑ u : V, (if G.Adj w u then (f w - f u) ^ 2 else 0) := by
      have hTmem : T ∈ G.neighborFinset S := (G.mem_neighborFinset S T).mpr hST
      have hsum_ge : ∑ w ∈ G.neighborFinset S,
          ((if G.Adj w S then (f w - f S) ^ 2 else 0) + if w = T then 1 else 0) ≤
          ∑ w ∈ G.neighborFinset S, ∑ u : V, (if G.Adj w u then (f w - f u) ^ 2 else 0) := by
        refine Finset.sum_le_sum fun w _ => ?_
        by_cases hwT : w = T
        · subst hwT; simpa using hT_extra
        · simp only [hwT, ↓reduceIte, add_zero]
          exact Finset.single_le_sum (f := fun u => if G.Adj w u then (f w - f u) ^ 2 else 0)
            (fun u _ => by positivity) (Finset.mem_univ S)
      rw [Finset.sum_add_distrib] at hsum_ge
      have h1 : ∑ w ∈ G.neighborFinset S, (if G.Adj w S then (f w - f S) ^ 2 else 0) =
          D * (D + 1) ^ 2 := by
        have hterm : ∀ w ∈ G.neighborFinset S,
            (if G.Adj w S then (f w - f S) ^ 2 else 0) = (D + 1) ^ 2 := by
          intro w hw; rw [SimpleGraph.mem_neighborFinset] at hw
          simp [f, hw, hw.symm, (G.ne_of_adj hw).symm]; ring
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
          nsmul_eq_mul]
      have h2 : ∑ w ∈ G.neighborFinset S, (if w = T then (1 : ℝ) else 0) = 1 := by
        rw [Finset.sum_ite_eq' (G.neighborFinset S) T (fun _ => (1 : ℝ)), if_pos hTmem]
      linarith
    have htot : (∑ w : V, (if G.Adj S w then (f S - f w) ^ 2 else 0)) +
        ∑ w ∈ G.neighborFinset S, ∑ u : V, (if G.Adj w u then (f w - f u) ^ 2 else 0) ≤
        ∑ a : V, ∑ b : V, (if G.Adj a b then (f a - f b) ^ 2 else 0) := by
      have hsub : insert S (G.neighborFinset S) ⊆ Finset.univ := Finset.subset_univ _
      have hins : (∑ w : V, (if G.Adj S w then (f S - f w) ^ 2 else 0)) +
          ∑ w ∈ G.neighborFinset S, ∑ u : V, (if G.Adj w u then (f w - f u) ^ 2 else 0) =
          ∑ a ∈ insert S (G.neighborFinset S), ∑ b : V, (if G.Adj a b then (f a - f b) ^ 2 else 0) :=
        (Finset.sum_insert (f := fun a => ∑ b : V, if G.Adj a b then (f a - f b) ^ 2 else 0)
          (G.notMem_neighborFinset_self S)).symm
      rw [hins]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun a _ _ =>
        Finset.sum_nonneg fun b _ => by positivity
    linarith
  refine lt_rho_of_rayleigh G (f := f) ?_
  have heq : ((G.degree S : ℝ) + 1) * (f ⬝ᵥ f) = D * (D + 1) ^ 2 := by
    rw [hnorm]; dsimp only [D]; ring
  linarith

/-- **Lemma 2 (Edge-Difference Upper Bound):**
For any connected graph `G` with at least one edge, there exists an edge `u ~ v`
such that `ρ(G) ≤ |N(u) ∪ N(v)|`. -/
theorem edge_diff_upper_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hedge : ∃ a b : V, G.Adj a b) :
    ∃ u v : V, G.Adj u v ∧
      lapSpectralRadius G ≤ ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) := by
  let : Nonempty V := hconn.nonempty
  obtain ⟨x, hx0, hxeig⟩ := exists_top_eigenvector G
  let E : Finset (V × V) := Finset.univ.filter (fun p => G.Adj p.1 p.2)
  have hE_ne : E.Nonempty := by
    rcases hedge with ⟨a, b, hab⟩
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩
  obtain ⟨⟨u, v⟩, huvE, hmax⟩ := Finset.exists_max_image E (fun p => x p.1 - x p.2) hE_ne
  have huv : G.Adj u v := (Finset.mem_filter.mp huvE).2
  set M : ℝ := x u - x v
  have hM_ge : ∀ a b : V, G.Adj a b → x a - x b ≤ M := fun a b hab =>
    hmax (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
  have hM_pos : 0 < M := by
    have hM_nn : 0 ≤ M := by
      have h1 := hM_ge v u huv.symm
      linarith
    by_contra hle
    have hM0 : M = 0 := le_antisymm (not_lt.mp hle) hM_nn
    have hconst : ∀ a b : V, G.Adj a b → x a = x b := by
      intro a b hab
      have h1 := hM_ge a b hab
      have h2 := hM_ge b a hab.symm
      linarith
    have hLx0 : G.lapMatrix ℝ *ᵥ x = 0 :=
      G.lapMatrix_mulVec_eq_zero_iff_forall_adj.mpr hconst
    rw [hLx0] at hxeig
    have hrho_pos : 0 < lapSpectralRadius G := by
      rcases hedge with ⟨a, b, hab⟩
      exact rho_pos_of_edge G hab
    have : x = 0 := (smul_eq_zero.mp hxeig.symm).resolve_left hrho_pos.ne'
    exact hx0 this
  have hrow_u : lapSpectralRadius G * x u = ∑ w ∈ G.neighborFinset u, (x u - x w) := by
    have h1 := congr_fun hxeig u
    simp only [Pi.smul_apply, smul_eq_mul, SimpleGraph.lapMatrix_mulVec_apply] at h1
    rw [← h1, Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul]
  have hrow_v : lapSpectralRadius G * x v = ∑ w ∈ G.neighborFinset v, (x v - x w) := by
    have h1 := congr_fun hxeig v
    simp only [Pi.smul_apply, smul_eq_mul, SimpleGraph.lapMatrix_mulVec_apply] at h1
    rw [← h1, Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul]
  have hdiff : lapSpectralRadius G * M =
      (∑ w ∈ G.neighborFinset u, (x u - x w)) + ∑ w ∈ G.neighborFinset v, (x w - x v) := by
    have hneg : ∑ w ∈ G.neighborFinset v, (x w - x v) = - ∑ w ∈ G.neighborFinset v, (x v - x w) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w _ => by ring
    dsimp only [M]
    linarith
  -- Split `N(u)` and `N(v)` into `N(u) \ N(v)`, `N(u) ∩ N(v)`, and `N(v) \ N(u)`!
  set Nu := G.neighborFinset u
  set Nv := G.neighborFinset v
  have hsplit_u : ∑ w ∈ Nu, (x u - x w) =
      (∑ w ∈ Nu \ Nv, (x u - x w)) + ∑ w ∈ Nu ∩ Nv, (x u - x w) := by
    have hd : Disjoint (Nu \ Nv) (Nu ∩ Nv) :=
      Finset.disjoint_left.mpr fun w h1 h2 => (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2
    rw [← Finset.sum_union hd, Finset.sdiff_union_inter]
  have hsplit_v : ∑ w ∈ Nv, (x w - x v) =
      (∑ w ∈ Nv \ Nu, (x w - x v)) + ∑ w ∈ Nu ∩ Nv, (x w - x v) := by
    rw [Finset.inter_comm Nu Nv]
    have hd : Disjoint (Nv \ Nu) (Nv ∩ Nu) :=
      Finset.disjoint_left.mpr fun w h1 h2 => (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2
    rw [← Finset.sum_union hd, Finset.sdiff_union_inter]
  have hcommon : (∑ w ∈ Nu ∩ Nv, (x u - x w)) + ∑ w ∈ Nu ∩ Nv, (x w - x v) =
      ((Nu ∩ Nv).card : ℝ) * M := by
    have hterm : ∀ w ∈ Nu ∩ Nv, (x u - x w) + (x w - x v) = M := fun _ _ => by dsimp only [M]; ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hpriv_u : ∑ w ∈ Nu \ Nv, (x u - x w) ≤ ((Nu \ Nv).card : ℝ) * M := by
    calc ∑ w ∈ Nu \ Nv, (x u - x w)
        ≤ ∑ _w ∈ Nu \ Nv, M := Finset.sum_le_sum fun w hw =>
          hM_ge u w ((G.mem_neighborFinset u w).mp (Finset.mem_sdiff.mp hw).1)
      _ = ((Nu \ Nv).card : ℝ) * M := by simp [nsmul_eq_mul]
  have hpriv_v : ∑ w ∈ Nv \ Nu, (x w - x v) ≤ ((Nv \ Nu).card : ℝ) * M := by
    calc ∑ w ∈ Nv \ Nu, (x w - x v)
        ≤ ∑ _w ∈ Nv \ Nu, M := Finset.sum_le_sum fun w hw =>
          hM_ge w v ((G.mem_neighborFinset v w).mp (Finset.mem_sdiff.mp hw).1).symm
      _ = ((Nv \ Nu).card : ℝ) * M := by simp [nsmul_eq_mul]
  have hcard_union : ((Nu \ Nv).card : ℝ) + ((Nv \ Nu).card : ℝ) + ((Nu ∩ Nv).card : ℝ) =
      ((Nu ∪ Nv).card : ℝ) := by
    have h1 : (Nu \ Nv).card + (Nu ∩ Nv).card = Nu.card := Finset.card_sdiff_add_card_inter Nu Nv
    have h2 : (Nv \ Nu).card + (Nu ∩ Nv).card = Nv.card := by
      rw [Finset.inter_comm Nu Nv]; exact Finset.card_sdiff_add_card_inter Nv Nu
    have h3 : (Nu ∪ Nv).card + (Nu ∩ Nv).card = Nu.card + Nv.card := Finset.card_union_add_card_inter Nu Nv
    have hnat : (Nu \ Nv).card + (Nv \ Nu).card + (Nu ∩ Nv).card = (Nu ∪ Nv).card := by omega
    exact_mod_cast hnat
  have hbound : lapSpectralRadius G * M ≤ ((Nu ∪ Nv).card : ℝ) * M := by
    nlinarith
  refine ⟨u, v, huv, ?_⟩
  nlinarith

/-- Helper: constructing a 2-token vertex `{a, b}` for `a ≠ b`. -/
private def mkTok2 {V : Type*} [DecidableEq V] (a b : V) (h : a ≠ b) : TokenVertex V 2 :=
  ⟨{a, b}, Finset.card_pair h⟩

private lemma mkTok2_adj_left {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a a' b : V} (hab : a ≠ b) (ha'b : a' ≠ b) (haa' : G.Adj a a') :
    (tokenGraph G 2).Adj (mkTok2 a b hab) (mkTok2 a' b ha'b) := by
  have hne : a ≠ a' := G.ne_of_adj haa'
  refine ⟨a, a', by simp [mkTok2], by simp [mkTok2, hne, hab], by simp [mkTok2],
    by simp [mkTok2, hne.symm, ha'b], haa', ?_⟩
  ext x; simp only [mkTok2, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, rfl | rfl⟩
    · exact absurd rfl h1
    · exact ⟨ha'b.symm, Or.inr rfl⟩
  · rintro ⟨h1, rfl | rfl⟩
    · exact absurd rfl h1
    · exact ⟨hab.symm, Or.inr rfl⟩

private lemma mkTok2_adj_right {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b b' : V} (hab : a ≠ b) (hab' : a ≠ b') (hbb' : G.Adj b b') :
    (tokenGraph G 2).Adj (mkTok2 a b hab) (mkTok2 a b' hab') := by
  have hne : b ≠ b' := G.ne_of_adj hbb'
  refine ⟨b, b', by simp [mkTok2], by simp [mkTok2, hab.symm, hne], by simp [mkTok2],
    by simp [mkTok2, hab'.symm, hne.symm], hbb', ?_⟩
  ext x; simp only [mkTok2, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, rfl | rfl⟩
    · exact ⟨hab', Or.inl rfl⟩
    · exact absurd rfl h1
  · rintro ⟨h1, rfl | rfl⟩
    · exact ⟨hab, Or.inl rfl⟩
    · exact absurd rfl h1

/-- **Lemmas 3–5 (Perturbed Star-Product Embedding):**
Given an edge `u ~ v` such that both `A₀ = N(u) \ N[v]` and `B₀ = N(v) \ N[u]` are
nonempty, `ρ(F₂(G)) > |N(u) ∪ N(v)|`. -/
theorem prod_star_perturbation_gt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v)
    (hA0 : (G.neighborFinset u \ insert v (G.neighborFinset v)).Nonempty)
    (hB0 : (G.neighborFinset v \ insert u (G.neighborFinset u)).Nonempty) :
    ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) <
      lapSpectralRadius (tokenGraph G 2) := by
  classical
  set X : Finset V := (G.neighborFinset u).erase v
  set A0 : Finset V := G.neighborFinset u \ insert v (G.neighborFinset v)
  set Y : Finset V := G.neighborFinset v \ insert u (G.neighborFinset u)
  set Uset : Finset V := insert u X
  set Vset : Finset V := insert v Y
  have huv_ne : u ≠ v := G.ne_of_adj huv
  have hu_notX : u ∉ X := by
    simp [X, G.notMem_neighborFinset_self u]
  have hv_notY : v ∉ Y := by
    simp [Y, G.notMem_neighborFinset_self v]
  have hdisj : Disjoint Uset Vset := by
    rw [Finset.disjoint_left]
    intro w hwU hwV
    simp only [Uset, Vset, Finset.mem_insert, X, Y, Finset.mem_erase, Finset.mem_sdiff,
      SimpleGraph.mem_neighborFinset, not_or] at hwU hwV
    rcases hwU with rfl | ⟨hwv, hwu⟩
    · rcases hwV with rfl | ⟨_, hnotu, _⟩
      · exact huv_ne rfl
      · exact hnotu rfl
    · rcases hwV with rfl | ⟨_, _, hnotNu⟩
      · exact hwv rfl
      · exact hnotNu hwu
  have hdisj_ne : ∀ s ∈ Uset, ∀ t ∈ Vset, s ≠ t := fun s hs t ht hst =>
    Finset.disjoint_left.mp hdisj hs (hst ▸ ht)
  set a : ℝ := (X.card : ℝ)
  set b : ℝ := (Y.card : ℝ)
  have hA0_sub_X : A0 ⊆ X := by
    intro x hx
    simp only [A0, X, Finset.mem_sdiff, Finset.mem_insert, SimpleGraph.mem_neighborFinset,
      Finset.mem_erase, not_or] at hx ⊢
    exact ⟨hx.2.1, hx.1⟩
  have ha_pos : 1 ≤ X.card := Finset.one_le_card.mpr (hA0.mono hA0_sub_X)
  have hb_pos : 1 ≤ Y.card := Finset.one_le_card.mpr hB0
  have hrho0_nat : (G.neighborFinset u ∪ G.neighborFinset v).card = X.card + Y.card + 2 := by
    have hunion : G.neighborFinset u ∪ G.neighborFinset v =
        insert u (insert v (X ∪ Y)) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, X, Y, Finset.mem_erase, Finset.mem_sdiff,
        SimpleGraph.mem_neighborFinset, not_or]
      constructor
      · rintro (huw | hvw)
        · by_cases hwv : w = v
          · exact Or.inr (Or.inl hwv)
          · exact Or.inr (Or.inr (Or.inl ⟨hwv, huw⟩))
        · by_cases hwu : w = u
          · exact Or.inl hwu
          · by_cases huw : G.Adj u w
            · have hwv : w ≠ v := (G.ne_of_adj hvw).symm
              exact Or.inr (Or.inr (Or.inl ⟨hwv, huw⟩))
            · exact Or.inr (Or.inr (Or.inr ⟨hvw, hwu, huw⟩))
      · rintro (rfl | rfl | ⟨_, huw⟩ | ⟨hvw, _⟩)
        · exact Or.inr huv.symm
        · exact Or.inl huv
        · exact Or.inl huw
        · exact Or.inr hvw
    have hXY_disj : Disjoint X Y := by
      rw [Finset.disjoint_left]; intro w hwX hwY
      exact Finset.disjoint_left.mp hdisj (Finset.mem_insert_of_mem hwX) (Finset.mem_insert_of_mem hwY)
    have hv_notXY : v ∉ X ∪ Y := by
      simp only [Finset.mem_union, X, Y, Finset.mem_erase, Finset.mem_sdiff, not_or]
      exact ⟨fun h => h.1 rfl, fun h => G.loopless.irrefl v ((G.mem_neighborFinset v v).mp h.1)⟩
    have hu_notvXY : u ∉ insert v (X ∪ Y) := by
      simp only [Finset.mem_insert, Finset.mem_union, X, Y, Finset.mem_erase, Finset.mem_sdiff,
        not_or]
      exact ⟨huv_ne, fun h => G.loopless.irrefl u ((G.mem_neighborFinset u u).mp h.2),
        fun h => h.2.1 trivial⟩
    rw [hunion, Finset.card_insert_of_notMem hu_notvXY, Finset.card_insert_of_notMem hv_notXY,
      Finset.card_union_of_disjoint hXY_disj]
  set ρ₀ : ℝ := a + b + 2
  have hrho0_eq : ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) = ρ₀ := by
    rw [hrho0_nat]; push_cast; dsimp [ρ₀, a, b]
  rw [hrho0_eq]
  -- Define `P` on `Uset`, `Q` on `Vset`, and transported vector `y` on `TokenVertex V 2`.
  let P : V → ℝ := fun s => if s = u then a else -1
  let Q : V → ℝ := fun t => if t = v then b else -1
  let phi : (s : V) → (t : V) → s ∈ Uset → t ∈ Vset → TokenVertex V 2 :=
    fun s t hs ht => mkTok2 s t (hdisj_ne s hs t ht)
  -- `phi` is injective on `Uset ×ˢ Vset`:
  have hphi_inj : ∀ s₁ t₁ (hs₁ : s₁ ∈ Uset) (ht₁ : t₁ ∈ Vset)
      s₂ t₂ (hs₂ : s₂ ∈ Uset) (ht₂ : t₂ ∈ Vset),
      phi s₁ t₁ hs₁ ht₁ = phi s₂ t₂ hs₂ ht₂ → s₁ = s₂ ∧ t₁ = t₂ := by
    intro s₁ t₁ hs₁ ht₁ s₂ t₂ hs₂ ht₂ h
    have hset : ({s₁, t₁} : Finset V) = {s₂, t₂} := congr_arg Subtype.val h
    have hs1_mem : s₁ ∈ ({s₂, t₂} : Finset V) := hset ▸ Finset.mem_insert_self s₁ {t₁}
    have ht1_mem : t₁ ∈ ({s₂, t₂} : Finset V) := hset ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self t₁)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs1_mem ht1_mem
    rcases hs1_mem with h1 | h1
    · rcases ht1_mem with h2 | h2
      · exact absurd (h1.trans h2.symm) (hdisj_ne s₁ hs₁ t₁ ht₁)
      · exact ⟨h1, h2⟩
    · exact absurd h1 (hdisj_ne s₁ hs₁ t₂ ht₂)
  let y : TokenVertex V 2 → ℝ := fun T =>
    ∑ s ∈ Uset, ∑ t ∈ Vset, if T.1 = {s, t} then P s * Q t else 0
  have hy_phi : ∀ s (hs : s ∈ Uset) t (ht : t ∈ Vset),
      y (phi s t hs ht) = P s * Q t := by
    intro s hs t ht
    dsimp only [y, phi, mkTok2]
    rw [Finset.sum_eq_single s]
    · rw [Finset.sum_eq_single t]
      · simp
      · intro t' ht' hne
        rw [if_neg]
        intro hset
        have heq := hphi_inj s t hs ht s t' hs ht' (Subtype.ext hset)
        exact hne heq.2.symm
      · intro hnot; exact absurd ht hnot
    · intro s' hs' hne
      refine Finset.sum_eq_zero fun t' ht' => ?_
      rw [if_neg]
      intro hset
      have heq := hphi_inj s t hs ht s' t' hs' ht' (Subtype.ext hset)
      exact hne heq.1.symm
    · intro hnot; exact absurd hs hnot
  have hy_out : ∀ T : TokenVertex V 2,
      (∀ s ∈ Uset, ∀ t ∈ Vset, T.1 ≠ {s, t}) → y T = 0 := by
    intro T hnot
    dsimp only [y]
    exact Finset.sum_eq_zero fun s hs => Finset.sum_eq_zero fun t ht => if_neg (hnot s hs t ht)
  -- Norm of `y`: `y ⬝ᵥ y = (a(a+1)) * (b(b+1))`
  let W : Finset (TokenVertex V 2) :=
    (Uset ×ˢ Vset).attach.image (fun p =>
      phi p.1.1 p.1.2 (Finset.mem_product.mp p.2).1 (Finset.mem_product.mp p.2).2)
  have hW_mem : ∀ T : TokenVertex V 2, T ∈ W ↔ ∃ s ∈ Uset, ∃ t ∈ Vset, T.1 = {s, t} := by
    intro T
    simp only [W, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_product]
    constructor
    · rintro ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩; exact ⟨s, hs, t, ht, rfl⟩
    · rintro ⟨s, hs, t, ht, hT⟩; exact ⟨(s, t), ⟨hs, ht⟩, Subtype.ext hT.symm⟩
  have hnorm_y : y ⬝ᵥ y = (a * (a + 1)) * (b * (b + 1)) := by
    unfold dotProduct
    rw [← Finset.sum_subset (Finset.subset_univ W)]
    · have hinjW : Function.Injective (fun p : {q // q ∈ Uset ×ˢ Vset} =>
          phi p.1.1 p.1.2 (Finset.mem_product.mp p.2).1 (Finset.mem_product.mp p.2).2) := by
        intro p₁ p₂ h
        have heq := hphi_inj p₁.1.1 p₁.1.2 (Finset.mem_product.mp p₁.2).1 (Finset.mem_product.mp p₁.2).2
          p₂.1.1 p₂.1.2 (Finset.mem_product.mp p₂.2).1 (Finset.mem_product.mp p₂.2).2 h
        exact Subtype.ext (Prod.ext heq.1 heq.2)
      dsimp only [W]
      rw [Finset.sum_image (fun p₁ _ p₂ _ h => hinjW h)]
      have h1 : ∑ p ∈ (Uset ×ˢ Vset).attach,
          y (phi p.1.1 p.1.2 (Finset.mem_product.mp p.2).1 (Finset.mem_product.mp p.2).2) *
          y (phi p.1.1 p.1.2 (Finset.mem_product.mp p.2).1 (Finset.mem_product.mp p.2).2) =
          ∑ p ∈ Uset ×ˢ Vset, (P p.1 * Q p.2) * (P p.1 * Q p.2) := by
        rw [← Finset.sum_attach (Uset ×ˢ Vset) (fun p => (P p.1 * Q p.2) * (P p.1 * Q p.2))]
        refine Finset.sum_congr rfl fun p _ => by
          rw [hy_phi p.1.1 (Finset.mem_product.mp p.2).1 p.1.2 (Finset.mem_product.mp p.2).2]
      rw [h1, Finset.sum_product]
      have hP2 : ∑ s ∈ Uset, P s * P s = a * (a + 1) := by
        rw [Finset.sum_insert hu_notX]
        have hX : ∑ s ∈ X, P s * P s = a := by
          have hterm : ∀ s ∈ X, P s * P s = 1 := fun s hs => by
            have hne : s ≠ u := fun h => hu_notX (h ▸ hs)
            simp [P, hne]
          rw [Finset.sum_congr rfl hterm]; simp [a]
        rw [hX]; simp [P]; ring
      have hQ2 : ∑ t ∈ Vset, Q t * Q t = b * (b + 1) := by
        rw [Finset.sum_insert hv_notY]
        have hY : ∑ t ∈ Y, Q t * Q t = b := by
          have hterm : ∀ t ∈ Y, Q t * Q t = 1 := fun t ht => by
            have hne : t ≠ v := fun h => hv_notY (h ▸ ht)
            simp [Q, hne]
          rw [Finset.sum_congr rfl hterm]; simp [b]
        rw [hY]; simp [Q]; ring
      calc ∑ s ∈ Uset, ∑ t ∈ Vset, (P s * Q t) * (P s * Q t)
          = ∑ s ∈ Uset, (P s * P s) * ∑ t ∈ Vset, (Q t * Q t) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => by ring
        _ = (∑ s ∈ Uset, P s * P s) * (∑ t ∈ Vset, Q t * Q t) := by rw [← Finset.sum_mul]
        _ = (a * (a + 1)) * (b * (b + 1)) := by rw [hP2, hQ2]
    · intro T _ hTW
      rw [hW_mem] at hTW; push Not at hTW
      rw [hy_out T hTW, mul_zero]
  -- Lower bound on quadratic form `lapQuad (tokenGraph G 2) y ≥ ρ₀ * (y ⬝ᵥ y)`
  -- by summing only over the disjoint horizontal and vertical star-product edges inside `F₂(G)`!
  have hquad_y : ρ₀ * (y ⬝ᵥ y) ≤ lapQuad (tokenGraph G 2) y := by
    rw [lapQuad_eq_sum_sq, hnorm_y]
    -- Directed pairs `(T₁, T₂)` from star-product edges are pairwise distinct across 4 families:
    -- F1: `(φ(u, t), φ(x, t))` (`x ∈ X, t ∈ Vset`), F2: `(φ(x, t), φ(u, t))`,
    -- F3: `(φ(s, v), φ(s, y))` (`s ∈ Uset, y ∈ Y`), F4: `(φ(s, y), φ(s, v))`.
    let F1 : Finset (TokenVertex V 2 × TokenVertex V 2) :=
      (X ×ˢ Vset).attach.image fun p =>
        (phi u p.1.2 (Finset.mem_insert_self u X) (Finset.mem_product.mp p.2).2,
         phi p.1.1 p.1.2 (Finset.mem_insert_of_mem (Finset.mem_product.mp p.2).1) (Finset.mem_product.mp p.2).2)
    let F2 : Finset (TokenVertex V 2 × TokenVertex V 2) :=
      (X ×ˢ Vset).attach.image fun p =>
        (phi p.1.1 p.1.2 (Finset.mem_insert_of_mem (Finset.mem_product.mp p.2).1) (Finset.mem_product.mp p.2).2,
         phi u p.1.2 (Finset.mem_insert_self u X) (Finset.mem_product.mp p.2).2)
    let F3 : Finset (TokenVertex V 2 × TokenVertex V 2) :=
      (Uset ×ˢ Y).attach.image fun p =>
        (phi p.1.1 v (Finset.mem_product.mp p.2).1 (Finset.mem_insert_self v Y),
         phi p.1.1 p.1.2 (Finset.mem_product.mp p.2).1 (Finset.mem_insert_of_mem (Finset.mem_product.mp p.2).2))
    let F4 : Finset (TokenVertex V 2 × TokenVertex V 2) :=
      (Uset ×ˢ Y).attach.image fun p =>
        (phi p.1.1 p.1.2 (Finset.mem_product.mp p.2).1 (Finset.mem_insert_of_mem (Finset.mem_product.mp p.2).2),
         phi p.1.1 v (Finset.mem_product.mp p.2).1 (Finset.mem_insert_self v Y))
    let term : TokenVertex V 2 × TokenVertex V 2 → ℝ := fun p =>
      if (tokenGraph G 2).Adj p.1 p.2 then (y p.1 - y p.2) ^ 2 else 0
    have hsum_F1 : ∑ p ∈ F1, term p = a * (a + 1) ^ 2 * (b * (b + 1)) := by
      have hinj : Function.Injective (fun p : {q // q ∈ X ×ˢ Vset} =>
          (phi u p.1.2 (Finset.mem_insert_self u X) (Finset.mem_product.mp p.2).2,
           phi p.1.1 p.1.2 (Finset.mem_insert_of_mem (Finset.mem_product.mp p.2).1) (Finset.mem_product.mp p.2).2)) := by
        intro p₁ p₂ h
        have h2 := hphi_inj p₁.1.1 p₁.1.2
          (Finset.mem_insert_of_mem (Finset.mem_product.mp p₁.2).1) (Finset.mem_product.mp p₁.2).2
          p₂.1.1 p₂.1.2
          (Finset.mem_insert_of_mem (Finset.mem_product.mp p₂.2).1) (Finset.mem_product.mp p₂.2).2
          (congr_arg Prod.snd h)
        exact Subtype.ext (Prod.ext h2.1 h2.2)
      dsimp only [F1]
      rw [Finset.sum_image (fun p₁ _ p₂ _ h => hinj h)]
      have heval : ∀ p ∈ (X ×ˢ Vset).attach,
          term (phi u p.1.2 (Finset.mem_insert_self u X) (Finset.mem_product.mp p.2).2,
                phi p.1.1 p.1.2 (Finset.mem_insert_of_mem (Finset.mem_product.mp p.2).1) (Finset.mem_product.mp p.2).2) =
          (a + 1) ^ 2 * (Q p.1.2 * Q p.1.2) := by
        intro p _
        have hxX : p.1.1 ∈ X := (Finset.mem_product.mp p.2).1
        have htV : p.1.2 ∈ Vset := (Finset.mem_product.mp p.2).2
        have hux : G.Adj u p.1.1 := (G.mem_neighborFinset u p.1.1).mp (Finset.mem_erase.mp hxX).2
        have hadj : (tokenGraph G 2).Adj (phi u p.1.2 (Finset.mem_insert_self u X) htV)
            (phi p.1.1 p.1.2 (Finset.mem_insert_of_mem hxX) htV) :=
          mkTok2_adj_left _ _ hux
        dsimp only [term]
        rw [if_pos hadj,
          hy_phi u (Finset.mem_insert_self u X) p.1.2 htV,
          hy_phi p.1.1 (Finset.mem_insert_of_mem hxX) p.1.2 htV]
        have hne : p.1.1 ≠ u := fun h => hu_notX (h ▸ hxX)
        simp only [P, ↓reduceIte, hne]; ring
      rw [Finset.sum_congr rfl heval, Finset.sum_attach (X ×ˢ Vset) (fun p => (a + 1) ^ 2 * (Q p.2 * Q p.2)),
        Finset.sum_product]
      have hQ2 : ∑ t ∈ Vset, Q t * Q t = b * (b + 1) := by
        rw [Finset.sum_insert hv_notY]
        have hY : ∑ t ∈ Y, Q t * Q t = b := by
          have hterm : ∀ t ∈ Y, Q t * Q t = 1 := fun t ht => by
            have htv : t ≠ v := fun h => hv_notY (h ▸ ht)
            simp [Q, htv]
          rw [Finset.sum_congr rfl hterm]; simp [b]
        rw [hY]; simp [Q]; ring
      simp_rw [← Finset.mul_sum, hQ2, Finset.sum_const, nsmul_eq_mul]
      dsimp only [a]; ring
    have hsum_F2 : ∑ p ∈ F2, term p = a * (a + 1) ^ 2 * (b * (b + 1)) := by
      have hswap : F2 = F1.image Prod.swap := by
        ext ⟨A, B⟩; simp only [F1, F2, Finset.mem_image, Finset.mem_attach, true_and]
        constructor
        · rintro ⟨p, h⟩; exact ⟨_, ⟨p, rfl⟩, by simpa [Prod.swap] using h⟩
        · rintro ⟨_, ⟨p, rfl⟩, h⟩; exact ⟨p, by simpa [Prod.swap] using h⟩
      rw [hswap, Finset.sum_image (fun p₁ _ p₂ _ h => Prod.swap_injective h)]
      rw [← hsum_F1]
      refine Finset.sum_congr rfl fun p _ => ?_
      dsimp only [term, Prod.swap]
      exact if_congr (SimpleGraph.adj_comm _ p.2 p.1) (by ring) rfl
    have hsum_F3 : ∑ p ∈ F3, term p = b * (b + 1) ^ 2 * (a * (a + 1)) := by
      have hinj : Function.Injective (fun p : {q // q ∈ Uset ×ˢ Y} =>
          (phi p.1.1 v (Finset.mem_product.mp p.2).1 (Finset.mem_insert_self v Y),
           phi p.1.1 p.1.2 (Finset.mem_product.mp p.2).1 (Finset.mem_insert_of_mem (Finset.mem_product.mp p.2).2))) := by
        intro p₁ p₂ h
        have h2 := hphi_inj p₁.1.1 p₁.1.2
          (Finset.mem_product.mp p₁.2).1 (Finset.mem_insert_of_mem (Finset.mem_product.mp p₁.2).2)
          p₂.1.1 p₂.1.2
          (Finset.mem_product.mp p₂.2).1 (Finset.mem_insert_of_mem (Finset.mem_product.mp p₂.2).2)
          (congr_arg Prod.snd h)
        exact Subtype.ext (Prod.ext h2.1 h2.2)
      dsimp only [F3]
      rw [Finset.sum_image (fun p₁ _ p₂ _ h => hinj h)]
      have heval : ∀ p ∈ (Uset ×ˢ Y).attach,
          term (phi p.1.1 v (Finset.mem_product.mp p.2).1 (Finset.mem_insert_self v Y),
                phi p.1.1 p.1.2 (Finset.mem_product.mp p.2).1 (Finset.mem_insert_of_mem (Finset.mem_product.mp p.2).2)) =
          (b + 1) ^ 2 * (P p.1.1 * P p.1.1) := by
        intro p _
        have hsU : p.1.1 ∈ Uset := (Finset.mem_product.mp p.2).1
        have hyY : p.1.2 ∈ Y := (Finset.mem_product.mp p.2).2
        have hvy : G.Adj v p.1.2 := (G.mem_neighborFinset v p.1.2).mp (Finset.mem_sdiff.mp hyY).1
        have hadj : (tokenGraph G 2).Adj (phi p.1.1 v hsU (Finset.mem_insert_self v Y))
            (phi p.1.1 p.1.2 hsU (Finset.mem_insert_of_mem hyY)) :=
          mkTok2_adj_right _ _ hvy
        dsimp only [term]
        rw [if_pos hadj,
          hy_phi p.1.1 hsU v (Finset.mem_insert_self v Y),
          hy_phi p.1.1 hsU p.1.2 (Finset.mem_insert_of_mem hyY)]
        have hne : p.1.2 ≠ v := fun h => hv_notY (h ▸ hyY)
        simp only [Q, ↓reduceIte, hne]; ring
      rw [Finset.sum_congr rfl heval, Finset.sum_attach (Uset ×ˢ Y) (fun p => (b + 1) ^ 2 * (P p.1 * P p.1)),
        Finset.sum_product]
      have hP2 : ∑ s ∈ Uset, P s * P s = a * (a + 1) := by
        rw [Finset.sum_insert hu_notX]
        have hX : ∑ s ∈ X, P s * P s = a := by
          have hterm : ∀ s ∈ X, P s * P s = 1 := fun s hs => by
            have hsu : s ≠ u := fun h => hu_notX (h ▸ hs)
            simp [P, hsu]
          rw [Finset.sum_congr rfl hterm]; simp [a]
        rw [hX]; simp [P]; ring
      simp_rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      rw [hP2]
      dsimp only [b]; ring
    have hsum_F4 : ∑ p ∈ F4, term p = b * (b + 1) ^ 2 * (a * (a + 1)) := by
      have hswap : F4 = F3.image Prod.swap := by
        ext ⟨A, B⟩; simp only [F3, F4, Finset.mem_image, Finset.mem_attach, true_and]
        constructor
        · rintro ⟨p, h⟩; exact ⟨_, ⟨p, rfl⟩, by simpa [Prod.swap] using h⟩
        · rintro ⟨_, ⟨p, rfl⟩, h⟩; exact ⟨p, by simpa [Prod.swap] using h⟩
      rw [hswap, Finset.sum_image (fun p₁ _ p₂ _ h => Prod.swap_injective h)]
      rw [← hsum_F3]
      refine Finset.sum_congr rfl fun p _ => ?_
      dsimp only [term, Prod.swap]
      exact if_congr (SimpleGraph.adj_comm _ p.2 p.1) (by ring) rfl
    -- Pairwise disjointness of `F1, F2, F3, F4`:
    have hd12 : Disjoint F1 F2 := by
      rw [Finset.disjoint_left]; intro q h1 h2
      simp only [F1, F2, Finset.mem_image, Finset.mem_attach, true_and] at h1 h2
      rcases h1 with ⟨p₁, rfl⟩; rcases h2 with ⟨p₂, h2⟩
      have heq := hphi_inj p₂.1.1 p₂.1.2
        (Finset.mem_insert_of_mem (Finset.mem_product.mp p₂.2).1) (Finset.mem_product.mp p₂.2).2
        u p₁.1.2 (Finset.mem_insert_self u X) (Finset.mem_product.mp p₁.2).2
        (congr_arg Prod.fst h2)
      exact hu_notX (heq.1 ▸ (Finset.mem_product.mp p₂.2).1)
    have hd34 : Disjoint F3 F4 := by
      rw [Finset.disjoint_left]; intro q h3 h4
      simp only [F3, F4, Finset.mem_image, Finset.mem_attach, true_and] at h3 h4
      rcases h3 with ⟨p₁, rfl⟩; rcases h4 with ⟨p₂, h4⟩
      have heq := hphi_inj p₂.1.1 p₂.1.2
        (Finset.mem_product.mp p₂.2).1 (Finset.mem_insert_of_mem (Finset.mem_product.mp p₂.2).2)
        p₁.1.1 v (Finset.mem_product.mp p₁.2).1 (Finset.mem_insert_self v Y)
        (congr_arg Prod.fst h4)
      exact hv_notY (heq.2 ▸ (Finset.mem_product.mp p₂.2).2)
    have hd12_34 : Disjoint (F1 ∪ F2) (F3 ∪ F4) := by
      rw [Finset.disjoint_left]; intro q h12 h34
      simp only [Finset.mem_union, F1, F2, F3, F4, Finset.mem_image, Finset.mem_attach, true_and] at h12 h34
      -- In `F1 ∪ F2`, first components differ (one is `u`, one is in `X`) while second components are equal;
      -- in `F3 ∪ F4`, first components are equal while second components differ!
      rcases h12 with ⟨p₁, rfl⟩ | ⟨p₁, rfl⟩ <;> rcases h34 with ⟨p₂, h⟩ | ⟨p₂, h⟩
      · have hA := hphi_inj p₂.1.1 v (Finset.mem_product.mp p₂.2).1 (Finset.mem_insert_self v Y)
          u p₁.1.2 (Finset.mem_insert_self u X) (Finset.mem_product.mp p₁.2).2 (congr_arg Prod.fst h)
        have hB := hphi_inj p₂.1.1 p₂.1.2 (Finset.mem_product.mp p₂.2).1 (Finset.mem_insert_of_mem (Finset.mem_product.mp p₂.2).2)
          p₁.1.1 p₁.1.2 (Finset.mem_insert_of_mem (Finset.mem_product.mp p₁.2).1) (Finset.mem_product.mp p₁.2).2 (congr_arg Prod.snd h)
        exact hu_notX ((hB.1.symm.trans hA.1) ▸ (Finset.mem_product.mp p₁.2).1)
      · have hA := hphi_inj p₂.1.1 p₂.1.2 (Finset.mem_product.mp p₂.2).1 (Finset.mem_insert_of_mem (Finset.mem_product.mp p₂.2).2)
          u p₁.1.2 (Finset.mem_insert_self u X) (Finset.mem_product.mp p₁.2).2 (congr_arg Prod.fst h)
        have hB := hphi_inj p₂.1.1 v (Finset.mem_product.mp p₂.2).1 (Finset.mem_insert_self v Y)
          p₁.1.1 p₁.1.2 (Finset.mem_insert_of_mem (Finset.mem_product.mp p₁.2).1) (Finset.mem_product.mp p₁.2).2 (congr_arg Prod.snd h)
        exact hu_notX ((hB.1.symm.trans hA.1) ▸ (Finset.mem_product.mp p₁.2).1)
      · have hA := hphi_inj p₂.1.1 v (Finset.mem_product.mp p₂.2).1 (Finset.mem_insert_self v Y)
          p₁.1.1 p₁.1.2 (Finset.mem_insert_of_mem (Finset.mem_product.mp p₁.2).1) (Finset.mem_product.mp p₁.2).2 (congr_arg Prod.fst h)
        have hB := hphi_inj p₂.1.1 p₂.1.2 (Finset.mem_product.mp p₂.2).1 (Finset.mem_insert_of_mem (Finset.mem_product.mp p₂.2).2)
          u p₁.1.2 (Finset.mem_insert_self u X) (Finset.mem_product.mp p₁.2).2 (congr_arg Prod.snd h)
        exact hu_notX ((hA.1.symm.trans hB.1) ▸ (Finset.mem_product.mp p₁.2).1)
      · have hA := hphi_inj p₂.1.1 p₂.1.2 (Finset.mem_product.mp p₂.2).1 (Finset.mem_insert_of_mem (Finset.mem_product.mp p₂.2).2)
          p₁.1.1 p₁.1.2 (Finset.mem_insert_of_mem (Finset.mem_product.mp p₁.2).1) (Finset.mem_product.mp p₁.2).2 (congr_arg Prod.fst h)
        have hB := hphi_inj p₂.1.1 v (Finset.mem_product.mp p₂.2).1 (Finset.mem_insert_self v Y)
          u p₁.1.2 (Finset.mem_insert_self u X) (Finset.mem_product.mp p₁.2).2 (congr_arg Prod.snd h)
        exact hu_notX ((hA.1.symm.trans hB.1) ▸ (Finset.mem_product.mp p₁.2).1)
    have hsum_tot : ∑ p ∈ (F1 ∪ F2) ∪ (F3 ∪ F4), term p ≤
        ∑ A : TokenVertex V 2, ∑ B : TokenVertex V 2, term (A, B) := by
      have hprod : ∑ A : TokenVertex V 2, ∑ B : TokenVertex V 2, term (A, B) =
          ∑ p ∈ (Finset.univ : Finset (TokenVertex V 2 × TokenVertex V 2)), term p := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
      rw [hprod]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => by
        dsimp only [term]; positivity
    rw [Finset.sum_union hd12_34, Finset.sum_union hd12, Finset.sum_union hd34,
      hsum_F1, hsum_F2, hsum_F3, hsum_F4] at hsum_tot
    have halg : ρ₀ * (a * (a + 1) * (b * (b + 1))) =
        (a * (a + 1) ^ 2 * (b * (b + 1)) + a * (a + 1) ^ 2 * (b * (b + 1)) +
        (b * (b + 1) ^ 2 * (a * (a + 1)) + b * (b + 1) ^ 2 * (a * (a + 1)))) / 2 := by
      dsimp only [ρ₀]; ring
    linarith
  -- Strict perturbation at `S = {u, x₀}` with `x₀ ∈ A₀`:
  rcases hA0 with ⟨x₀, hx₀A0⟩
  have hx₀X : x₀ ∈ X := hA0_sub_X hx₀A0
  have hux₀ : G.Adj u x₀ := (G.mem_neighborFinset u x₀).mp (Finset.mem_erase.mp hx₀X).2
  have hux₀_ne : u ≠ x₀ := G.ne_of_adj hux₀
  have hx₀_notv : x₀ ≠ v := (Finset.mem_erase.mp hx₀X).1
  have hx₀_notNv : ¬ G.Adj v x₀ := by
    intro h
    have hmem := (Finset.mem_sdiff.mp hx₀A0).2
    exact hmem (Finset.mem_insert_of_mem ((G.mem_neighborFinset v x₀).mpr h))
  let S : TokenVertex V 2 := mkTok2 u x₀ hux₀_ne
  have hS_notW : S ∉ W := by
    rw [hW_mem]; rintro ⟨s, hs, t, ht, hST⟩
    have ht_mem : t ∈ ({u, x₀} : Finset V) := by
      have : t ∈ S.1 := by rw [hST]; simp
      exact this
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht_mem
    rcases ht_mem with htu | htx
    · exact hdisj_ne u (Finset.mem_insert_self u X) t ht htu.symm
    · exact hdisj_ne x₀ (Finset.mem_insert_of_mem hx₀X) t ht htx.symm
  have hyS : y S = 0 := by
    rw [hW_mem] at hS_notW; push Not at hS_notW
    exact hy_out S hS_notW
  -- Every neighbor `T` of `S` in `F₂(G)` satisfies `y T ≤ 0`, and `T₀ = {x₀, v}` has `y T₀ = -b < 0`!
  have hy_nb_nonpos : ∀ T : TokenVertex V 2, (tokenGraph G 2).Adj S T → y T ≤ 0 := by
    intro T hST
    by_cases hTW : T ∈ W
    · rw [hW_mem] at hTW
      rcases hTW with ⟨s, hs, t, ht, hTeq⟩
      have hT_eq : T = phi s t hs ht := Subtype.ext hTeq
      rw [hT_eq, hy_phi s hs t ht]
      -- Since `S = {u, x₀}` is adjacent to `{s, t}` with `s ∈ Uset` and `t ∈ Vset`:
      -- `S` and `T` share exactly one element, which MUST be `s` (since `t ∈ Vset` is disjoint from `Uset`).
      -- Thus either `s = x₀` (so `P s = -1`, and moving `u` to `t` forces `t = v`, `Q t = b`, `P s * Q t = -b ≤ 0`)
      -- or `s = u` (so `P s = a`, and moving `x₀` to `t` forces `t ≠ v` since `x₀ ≁ v`, so `Q t = -1`, `P s * Q t = -a ≤ 0`)!
      rcases hST with ⟨w₁, w₂, hw1S, hw1T, hw2T, hw2S, hw12, herase⟩
      have ht_notS : t ∉ S.1 := by
        intro htS; simp only [S, mkTok2, Finset.mem_insert, Finset.mem_singleton] at htS
        rcases htS with htu | htx
        · exact hdisj_ne u (Finset.mem_insert_self u X) t ht htu.symm
        · exact hdisj_ne x₀ (Finset.mem_insert_of_mem hx₀X) t ht htx.symm
      have hs_in_S : s ∈ S.1 := by
        have hw2_eq_t : w₂ = t := by
          have : w₂ ∈ ({s, t} : Finset V) := hTeq ▸ hw2T
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with hws | hwt
          · have : t ∈ T.1.erase w₂ := by
              rw [hTeq, hws]; exact Finset.mem_erase.mpr ⟨(hdisj_ne s hs t ht).symm, by simp⟩
            rw [← herase] at this
            exact absurd (Finset.mem_erase.mp this).2 ht_notS
          · exact hwt
        have hs_er : s ∈ T.1.erase w₂ := by
          rw [hTeq, hw2_eq_t]
          exact Finset.mem_erase.mpr ⟨hdisj_ne s hs t ht, by simp⟩
        rw [← herase] at hs_er
        exact (Finset.mem_erase.mp hs_er).2
      have ht_eq_w2 : t = w₂ := by
        have : w₂ ∈ ({s, t} : Finset V) := hTeq ▸ hw2T
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with hws | hwt
        · exact absurd (hws ▸ hs_in_S) hw2S
        · exact hwt.symm
      simp only [S, mkTok2, Finset.mem_insert, Finset.mem_singleton] at hs_in_S hw1S
      rcases hs_in_S with hsu | hsx
      · -- `s = u`: then `w₁ = x₀` (since `u = s ∈ T` while `w₁ ∉ T`), so `x₀ ~ t`, hence `t ≠ v`!
        have hw1_eq : w₁ = x₀ := by
          rcases hw1S with hw1u | hw1x
          · exact absurd (by rw [hTeq, hw1u, hsu]; simp) hw1T
          · exact hw1x
        have htv : t ≠ v := by
          intro htv; subst htv; rw [hw1_eq, ← ht_eq_w2] at hw12
          exact hx₀_notNv hw12.symm
        rw [hsu]
        simp only [P, Q, ↓reduceIte, htv]
        have : (1 : ℝ) ≤ a := by dsimp only [a]; exact_mod_cast ha_pos
        nlinarith
      · -- `s = x₀`: then `w₁ = u`, so `u ~ t`, hence `t = v` (since `Y ∩ N(u) = ∅`)!
        have hw1_eq : w₁ = u := by
          rcases hw1S with hw1u | hw1x
          · exact hw1u
          · exact absurd (by rw [hTeq, hw1x, hsx]; simp) hw1T
        have htv : t = v := by
          rw [hw1_eq, ← ht_eq_w2] at hw12
          simp only [Vset, Finset.mem_insert, Y, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at ht
          rcases ht with rfl | ⟨_, hnot⟩
          · rfl
          · exact absurd (Or.inr hw12) hnot
        have hx₀u : x₀ ≠ u := hux₀_ne.symm
        rw [hsx]
        simp only [P, Q, hx₀u, htv, ↓reduceIte]
        have : (1 : ℝ) ≤ b := by dsimp only [b]; exact_mod_cast hb_pos
        nlinarith
    · rw [hW_mem] at hTW; push Not at hTW
      rw [hy_out T hTW]
  let T₀ : TokenVertex V 2 := phi x₀ v (Finset.mem_insert_of_mem hx₀X) (Finset.mem_insert_self v Y)
  have hST₀ : (tokenGraph G 2).Adj S T₀ := by
    have h1 : (tokenGraph G 2).Adj (mkTok2 u x₀ hux₀_ne) (mkTok2 v x₀ hx₀_notv.symm) :=
      mkTok2_adj_left hux₀_ne hx₀_notv.symm huv
    have heq : mkTok2 v x₀ hx₀_notv.symm = T₀ := by
      ext z; simp [mkTok2, T₀, phi, or_comm]
    rwa [heq] at h1
  have hyT₀ : y T₀ = -b := by
    dsimp only [T₀]
    rw [hy_phi x₀ (Finset.mem_insert_of_mem hx₀X) v (Finset.mem_insert_self v Y)]
    simp [P, Q, hux₀_ne.symm]
  set g : ℝ := ((tokenGraph G 2).lapMatrix ℝ *ᵥ y) S
  have hg_pos : 0 < g := by
    dsimp only [g]
    rw [SimpleGraph.lapMatrix_mulVec_apply, hyS, mul_zero, zero_sub]
    have hsum_le : ∑ T ∈ (tokenGraph G 2).neighborFinset S, y T ≤ y T₀ := by
      have hmem : T₀ ∈ (tokenGraph G 2).neighborFinset S :=
        ((tokenGraph G 2).mem_neighborFinset S T₀).mpr hST₀
      have h1 := Finset.add_sum_erase ((tokenGraph G 2).neighborFinset S) y hmem
      have hrest : ∑ T ∈ ((tokenGraph G 2).neighborFinset S).erase T₀, y T ≤ 0 :=
        Finset.sum_nonpos fun T hT =>
          hy_nb_nonpos T (((tokenGraph G 2).mem_neighborFinset S T).mp (Finset.mem_erase.mp hT).2)
      linarith
    have hb1 : (1 : ℝ) ≤ b := by dsimp only [b]; exact_mod_cast hb_pos
    linarith
  -- Perturb `z = y + ε e_S` with `ε = g / (|deg(S) - ρ₀| + 1) > 0`:
  set dS : ℝ := ((tokenGraph G 2).degree S : ℝ)
  set ε : ℝ := g / (|dS - ρ₀| + 1)
  have hε_pos : 0 < ε := div_pos hg_pos (by positivity)
  let eS : TokenVertex V 2 → ℝ := Pi.single S 1
  let z : TokenVertex V 2 → ℝ := fun T => y T + ε * eS T
  have heS_dot_y : eS ⬝ᵥ y = 0 := by
    simp [eS, dotProduct, Pi.single_apply, hyS]
  have heS_dot_eS : eS ⬝ᵥ eS = 1 := by
    simp [eS, dotProduct, Pi.single_apply]
  have hz_norm : z ⬝ᵥ z = y ⬝ᵥ y + ε ^ 2 := by
    have h1 : z ⬝ᵥ z = y ⬝ᵥ y + 2 * ε * (eS ⬝ᵥ y) + ε ^ 2 * (eS ⬝ᵥ eS) := by
      unfold dotProduct
      simp only [z]
      calc ∑ T, (y T + ε * eS T) * (y T + ε * eS T)
          = ∑ T, (y T * y T + 2 * ε * (eS T * y T) + ε ^ 2 * (eS T * eS T)) :=
            Finset.sum_congr rfl fun T _ => by ring
        _ = (∑ T, y T * y T) + 2 * ε * (∑ T, eS T * y T) + ε ^ 2 * (∑ T, eS T * eS T) := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h1, heS_dot_y, heS_dot_eS]; ring
  have heS_L_y : eS ⬝ᵥ ((tokenGraph G 2).lapMatrix ℝ *ᵥ y) = g := by
    simp [eS, dotProduct, Pi.single_apply, g]
  have hy_L_eS : y ⬝ᵥ ((tokenGraph G 2).lapMatrix ℝ *ᵥ eS) = g := by
    have hsym : ((tokenGraph G 2).lapMatrix ℝ)ᵀ = (tokenGraph G 2).lapMatrix ℝ :=
      (tokenGraph G 2).isSymm_lapMatrix ℝ
    calc y ⬝ᵥ ((tokenGraph G 2).lapMatrix ℝ *ᵥ eS)
        = (eS ⬝ᵥ (((tokenGraph G 2).lapMatrix ℝ)ᵀ *ᵥ y)) := by
          rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]
      _ = g := by rw [hsym, heS_L_y]
  have heS_L_eS : eS ⬝ᵥ ((tokenGraph G 2).lapMatrix ℝ *ᵥ eS) = dS := by
    simp only [eS, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, SimpleGraph.lapMatrix_mulVec_apply, dS]
    rw [if_neg ((tokenGraph G 2).notMem_neighborFinset_self S)]; ring
  have hz_quad : lapQuad (tokenGraph G 2) z =
      lapQuad (tokenGraph G 2) y + 2 * ε * g + ε ^ 2 * dS := by
    have hz_eq : z = y + ε • eS := by ext T; simp [z]
    unfold lapQuad
    rw [hz_eq, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add,
      smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      heS_L_y, hy_L_eS, heS_L_eS]
    ring
  have hstrict : ρ₀ * (z ⬝ᵥ z) < lapQuad (tokenGraph G 2) z := by
    rw [hz_norm, hz_quad]
    have hquad_eps : 0 < 2 * ε * g + ε ^ 2 * (dS - ρ₀) := by
      have hden_pos : 0 < |dS - ρ₀| + 1 := by positivity
      have hle_abs : -(dS - ρ₀) ≤ |dS - ρ₀| := neg_le_abs (dS - ρ₀)
      have hmul : ε * (|dS - ρ₀| + 1) = g := div_mul_cancel₀ g hden_pos.ne'
      have h1 : ε * (-(dS - ρ₀)) ≤ ε * |dS - ρ₀| := mul_le_mul_of_nonneg_left hle_abs hε_pos.le
      nlinarith
    linarith
  exact lt_rho_of_rayleigh (tokenGraph G 2) hstrict

/-! ### 3. Theorem 1: Proof of the Connected Conjecture -/

/-- **Theorem 1 (Connected Non-Star Strict Inequality):**
For every connected non-star graph `G` of order `n ≥ 4`, `ρ(F₂(G)) > ρ(G)`. -/
theorem connected_nonstar_rho_F2_gt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 4 ≤ Fintype.card V) (hconn : G.Connected) (hnotstar : ¬ IsStar G) :
    lapSpectralRadius G < lapSpectralRadius (tokenGraph G 2) := by
  classical
  have hedge : ∃ a b : V, G.Adj a b := by
    obtain ⟨a⟩ := hconn.nonempty
    have hne : ∃ b : V, b ≠ a := by
      by_contra hall; push Not at hall
      have : Fintype.card V ≤ 1 := by
        calc Fintype.card V = (Finset.univ : Finset V).card := rfl
          _ ≤ ({a} : Finset V).card := Finset.card_le_card (fun x _ => by simp [hall x])
          _ = 1 := Finset.card_singleton a
      omega
    rcases hne with ⟨b, hba⟩
    rcases hconn a b with ⟨w⟩
    cases w with
    | nil => exact absurd rfl hba
    | @cons _ w1 _ hadj _ => exact ⟨a, w1, hadj⟩
  by_cases hdom : ∃ c : V, G.degree c = Fintype.card V - 1
  · -- Case 1: `G` has a dominating vertex `c` (degree `n - 1`).
    rcases hdom with ⟨c, hcdeg⟩
    have hc_adj : ∀ w : V, w ≠ c → G.Adj c w := by
      intro w hwc
      have hsub : G.neighborFinset c ⊆ Finset.univ.erase c := by
        intro x hx; exact Finset.mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset c x).mp hx)).symm, Finset.mem_univ x⟩
      have heq : G.neighborFinset c = Finset.univ.erase c := by
        refine Finset.eq_of_subset_of_card_le hsub ?_
        rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, SimpleGraph.card_neighborFinset_eq_degree, hcdeg]
      have hw : w ∈ G.neighborFinset c := heq ▸ Finset.mem_erase.mpr ⟨hwc, Finset.mem_univ w⟩
      exact (G.mem_neighborFinset c w).mp hw
    -- Since `G` is not a star centred at `c`, there is an edge `p ~ q` avoiding `c`.
    have hpq : ∃ p q : V, p ≠ c ∧ q ≠ c ∧ G.Adj p q := by
      by_contra hall; push Not at hall
      apply hnotstar
      refine ⟨c, fun u v => ⟨fun huv => ?_, ?_⟩⟩
      · by_cases huc : u = c
        · exact Or.inl ⟨huc, huc ▸ (G.ne_of_adj huv).symm⟩
        · by_cases hvc : v = c
          · exact Or.inr ⟨hvc, hvc ▸ G.ne_of_adj huv⟩
          · exact absurd huv (hall u v huc hvc)
      · rintro (⟨rfl, hv⟩ | ⟨rfl, hu⟩)
        · exact hc_adj v hv
        · exact (hc_adj u hu).symm
    rcases hpq with ⟨p, q, hpc, hqc, hpq_adj⟩
    have hpq_ne : p ≠ q := G.ne_of_adj hpq_adj
    -- Define spanning subgraph `H = S_n + pq ⊆ G`.
    let H : SimpleGraph V := {
      Adj := fun x y => (x = c ∧ y ≠ c) ∨ (y = c ∧ x ≠ c) ∨ (x = p ∧ y = q) ∨ (x = q ∧ y = p)
      symm := ⟨fun x y h => by rcases h with h | h | h | h <;> tauto⟩
      loopless := ⟨fun x h => by rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto⟩
    }
    have hHG : ∀ x y : V, H.Adj x y → G.Adj x y := by
      intro x y h
      rcases h with ⟨rfl, hy⟩ | ⟨rfl, hx⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hc_adj y hy
      · exact (hc_adj x hx).symm
      · exact hpq_adj
      · exact hpq_adj.symm
    have hF2_mono : lapSpectralRadius (tokenGraph H 2) ≤ lapSpectralRadius (tokenGraph G 2) :=
      rho_le_of_embedding id Function.injective_id fun A B ⟨u', v', h1, h2, h3, h4, huv', h5⟩ =>
        ⟨u', v', h1, h2, h3, h4, hHG u' v' huv', h5⟩
    -- In `F₂(H)`, `S = {c, p}` has degree `n - 1`; pick `ℓ ∉ {c, p, q}` (since `n ≥ 4`).
    have hℓ : ∃ ℓ : V, ℓ ≠ c ∧ ℓ ≠ p ∧ ℓ ≠ q := by
      have hcard3 : ({c, p, q} : Finset V).card ≤ 3 := by
        calc ({c, p, q} : Finset V).card ≤ ({p, q} : Finset V).card + 1 := Finset.card_insert_le _ _
          _ ≤ ({q} : Finset V).card + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
          _ = 3 := by simp
      have hlt : ({c, p, q} : Finset V).card < (Finset.univ : Finset V).card := by
        rw [Finset.card_univ]; omega
      obtain ⟨ℓ, _, hℓnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hℓnot
      exact ⟨ℓ, hℓnot.1, hℓnot.2.1, hℓnot.2.2⟩
    rcases hℓ with ⟨ℓ, hℓc, hℓp, hℓq⟩
    let S : TokenVertex V 2 := mkTok2 c p hpc.symm
    let T : TokenVertex V 2 := mkTok2 ℓ p hℓp
    let U : TokenVertex V 2 := mkTok2 ℓ c hℓc
    have hST : (tokenGraph H 2).Adj S T :=
      mkTok2_adj_left hpc.symm hℓp (Or.inl ⟨rfl, hℓc⟩)
    have hTU : (tokenGraph H 2).Adj T U :=
      mkTok2_adj_right hℓp hℓc (Or.inr (Or.inl ⟨rfl, hpc⟩))
    have hUS : U ≠ S := by
      intro h
      have hset : ({ℓ, c} : Finset V) = {c, p} := congr_arg Subtype.val h
      have : ℓ ∈ ({c, p} : Finset V) := hset ▸ Finset.mem_insert_self ℓ {c}
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl <;> contradiction
    have hnotSU : ¬ (tokenGraph H 2).Adj S U := by
      rintro ⟨u', v', hu'S, hu'U, hv'U, hv'S, huv', _⟩
      simp only [S, U, mkTok2, Finset.mem_insert, Finset.mem_singleton, not_or] at hu'S hu'U hv'U hv'S
      have hu'_eq : u' = p := by rcases hu'S with rfl | rfl; exact absurd rfl hu'U.2; rfl
      have hv'_eq : v' = ℓ := by rcases hv'U with rfl | rfl; rfl; exact absurd rfl hv'S.1
      rw [hu'_eq, hv'_eq] at huv'
      rcases huv' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
      · exact hpc h1
      · exact hℓc h1
      · exact hℓq h2
      · exact hpq_ne h1
    have hdegS : (tokenGraph H 2).degree S = Fintype.card V - 1 := by
      -- Neighbors of `{c, p}` in `F₂(H)` are `{w, p}` for `w ∉ {c, p}` (`n - 2`) plus `{c, q}` (`1`).
      let f : V → TokenVertex V 2 := fun w =>
        if hwc : w = c then mkTok2 c q hqc.symm
        else if hwp : w = p then mkTok2 c q hqc.symm
        else mkTok2 w p hwp
      have himg : (Finset.univ.erase p).image f = (tokenGraph H 2).neighborFinset S := by
        ext W
        simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
          SimpleGraph.mem_neighborFinset]
        constructor
        · rintro ⟨w, hwp, rfl⟩
          dsimp only [f]
          by_cases hwc : w = c
          · rw [dif_pos hwc]
            exact mkTok2_adj_right hpc.symm hqc.symm (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
          · rw [dif_neg hwc, dif_neg hwp]
            exact mkTok2_adj_left hpc.symm hwp (Or.inl ⟨rfl, hwc⟩)
        · rintro ⟨u', v', hu'S, hu'W, hv'W, hv'S, huv', herase⟩
          simp only [S, mkTok2, Finset.mem_insert, Finset.mem_singleton, not_or] at hu'S hv'S
          have hWeq : W.1 = insert v' (S.1.erase u') := by
            rw [herase, Finset.insert_erase hv'W]
          rcases hu'S with rfl | rfl
          · refine ⟨v', hv'S.2, Subtype.ext ?_⟩
            dsimp only [f]; rw [dif_neg hv'S.1, dif_neg hv'S.2]
            rw [hWeq]; ext x; simp [S, mkTok2, hpc.symm]
          · have hv'_eq : v' = q := by
              rcases huv' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, rfl⟩ | ⟨h1, _⟩
              · exact absurd h1 hpc
              · exact absurd h1 hv'S.1
              · rfl
              · exact absurd h1 hpq_ne
            refine ⟨c, hpc.symm, Subtype.ext ?_⟩
            dsimp only [f]; rw [dif_pos rfl]
            rw [hWeq, hv'_eq]; ext x
            simp only [S, mkTok2, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
            constructor
            · rintro (rfl | rfl)
              · exact Or.inr ⟨hpc.symm, Or.inl rfl⟩
              · exact Or.inl rfl
            · rintro (rfl | ⟨h1, rfl | rfl⟩)
              · exact Or.inr rfl
              · exact Or.inl rfl
              · exact absurd rfl h1
      have hfinj : Set.InjOn f (Finset.univ.erase p : Set V) := by
        intro w₁ hw₁ w₂ hw₂ hfeq
        simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true] at hw₁ hw₂
        dsimp only [f] at hfeq
        by_cases h1c : w₁ = c <;> by_cases h2c : w₂ = c
        · exact h1c.trans h2c.symm
        · rw [dif_pos h1c, dif_neg h2c, dif_neg hw₂] at hfeq
          have hset : ({c, q} : Finset V) = {w₂, p} := congr_arg Subtype.val hfeq
          have : p ∈ ({c, q} : Finset V) := hset ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self p)
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h | h <;> contradiction
        · rw [dif_neg h1c, dif_neg hw₁, dif_pos h2c] at hfeq
          have hset : ({w₁, p} : Finset V) = {c, q} := congr_arg Subtype.val hfeq
          have : p ∈ ({c, q} : Finset V) := hset ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self p)
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h | h <;> contradiction
        · rw [dif_neg h1c, dif_neg hw₁, dif_neg h2c, dif_neg hw₂] at hfeq
          have hset : ({w₁, p} : Finset V) = {w₂, p} := congr_arg Subtype.val hfeq
          have : w₁ ∈ ({w₂, p} : Finset V) := hset ▸ Finset.mem_insert_self w₁ {p}
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | h
          · rfl
          · exact absurd h hw₁
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← himg, Finset.card_image_of_injOn hfinj,
        Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]
    have hgt_H : (Fintype.card V : ℝ) < lapSpectralRadius (tokenGraph H 2) := by
      have hgm := grone_merris_lt (tokenGraph H 2) S T U (by omega) hST hTU hUS hnotSU
      rw [hdegS] at hgm
      have hcast : ((Fintype.card V - 1 : ℕ) : ℝ) + 1 = (Fintype.card V : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card V), Nat.cast_one]; ring
      linarith
    obtain ⟨u, v, _, hrho_le⟩ := edge_diff_upper_bound G hconn hedge
    have hcard_le : ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast Finset.card_le_univ _
    linarith
  · -- Case 2: No vertex has degree `n - 1`.
    push Not at hdom
    obtain ⟨u, v, huv, hrho_le⟩ := edge_diff_upper_bound G hconn hedge
    set A0 : Finset V := G.neighborFinset u \ insert v (G.neighborFinset v)
    set B0 : Finset V := G.neighborFinset v \ insert u (G.neighborFinset u)
    by_cases hA0 : A0.Nonempty
    · by_cases hB0 : B0.Nonempty
      · -- Both `A₀, B₀` nonempty: Lemma 5 gives `ρ(F₂(G)) > |N(u) ∪ N(v)| ≥ ρ(G)`.
        exact lt_of_le_of_lt hrho_le (prod_star_perturbation_gt G huv hA0 hB0)
      · -- `B₀ = ∅`: `N(v) ⊆ N[u]`, so `|N(u) ∪ N(v)| = d_u + 1`. Pick `z ∉ N[u]`!
        rw [Finset.not_nonempty_iff_eq_empty] at hB0
        have hunion_eq : G.neighborFinset u ∪ G.neighborFinset v = insert u (G.neighborFinset u) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
          constructor
          · rintro (huw | hvw)
            · exact Or.inr huw
            · by_contra hnot
              have : w ∈ B0 := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset v w).mpr hvw, by
                simpa [Finset.mem_insert, SimpleGraph.mem_neighborFinset] using hnot⟩
              rw [hB0] at this; exact Finset.notMem_empty w this
          · rintro (rfl | huw)
            · exact Or.inr huv.symm
            · exact Or.inl huw
        have hcard_u : (G.neighborFinset u ∪ G.neighborFinset v).card = G.degree u + 1 := by
          rw [hunion_eq, Finset.card_insert_of_notMem (G.notMem_neighborFinset_self u),
            SimpleGraph.card_neighborFinset_eq_degree]
        have hdeg_lt : G.degree u < Fintype.card V - 1 := by
          have hle : G.degree u ≤ Fintype.card V - 1 := by
            have := Finset.card_le_card (show G.neighborFinset u ⊆ Finset.univ.erase u from fun x hx =>
              Finset.mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset u x).mp hx)).symm, Finset.mem_univ x⟩)
            rw [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_erase_of_mem (Finset.mem_univ u),
              Finset.card_univ] at this
            exact this
          exact lt_of_le_of_ne hle (hdom u)
        have hlt_card : (insert u (G.neighborFinset u)).card < (Finset.univ : Finset V).card := by
          rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self u),
            SimpleGraph.card_neighborFinset_eq_degree, Finset.card_univ]; omega
        obtain ⟨z, _, hznot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_card
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hznot
        have hdz : 1 ≤ G.degree z := by
          rcases hconn z u with ⟨w⟩
          cases w with
          | nil => exact absurd rfl hznot.1
          | @cons _ w1 _ hadj _ =>
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            exact Finset.one_le_card.mpr ⟨w1, (G.mem_neighborFinset z w1).mpr hadj⟩
        have huz : u ≠ z := Ne.symm hznot.1
        let S : TokenVertex V 2 := mkTok2 u z huz
        have hdegS : G.degree u + G.degree z ≤ (tokenGraph G 2).degree S := by
          let fL : V → TokenVertex V 2 := fun w => if h : w = z then S else mkTok2 w z h
          let fR : V → TokenVertex V 2 := fun w => if h : w = u then S else mkTok2 u w (Ne.symm h)
          let NL : Finset (TokenVertex V 2) := (G.neighborFinset u).image fL
          let NR : Finset (TokenVertex V 2) := (G.neighborFinset z).image fR
          have hNL_sub : NL ⊆ (tokenGraph G 2).neighborFinset S := by
            intro T hT; rcases Finset.mem_image.mp hT with ⟨w, hw, rfl⟩
            rw [SimpleGraph.mem_neighborFinset] at hw ⊢
            have hwz : w ≠ z := fun h => hznot.2 (h ▸ hw)
            dsimp only [fL]; rw [dif_neg hwz]
            exact mkTok2_adj_left huz hwz hw
          have hNR_sub : NR ⊆ (tokenGraph G 2).neighborFinset S := by
            intro T hT; rcases Finset.mem_image.mp hT with ⟨w, hw, rfl⟩
            rw [SimpleGraph.mem_neighborFinset] at hw ⊢
            have hwu : w ≠ u := fun h => hznot.2 (h ▸ hw.symm)
            dsimp only [fR]; rw [dif_neg hwu]
            exact mkTok2_adj_right huz hwu.symm hw
          have hdisjLR : Disjoint NL NR := by
            rw [Finset.disjoint_left]; intro T h1 h2
            rcases Finset.mem_image.mp h1 with ⟨w₁, hw₁, rfl⟩
            rcases Finset.mem_image.mp h2 with ⟨w₂, hw₂, heq⟩
            rw [SimpleGraph.mem_neighborFinset] at hw₁ hw₂
            have h1z : w₁ ≠ z := fun h => hznot.2 (h ▸ hw₁)
            have h2u : w₂ ≠ u := fun h => hznot.2 (h ▸ hw₂.symm)
            dsimp only [fL, fR] at heq; rw [dif_neg h1z, dif_neg h2u] at heq
            have hset : ({u, w₂} : Finset V) = {w₁, z} := congr_arg Subtype.val heq
            have hu_mem : u ∈ ({w₁, z} : Finset V) := hset ▸ Finset.mem_insert_self u {w₂}
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu_mem
            rcases hu_mem with h | h
            · exact (G.ne_of_adj hw₁) h
            · exact huz h
          have hNL_card : NL.card = G.degree u := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            refine Finset.card_image_of_injOn fun w₁ hw₁ w₂ hw₂ heq => ?_
            rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
            have h1z : w₁ ≠ z := fun h => hznot.2 (h ▸ hw₁)
            have h2z : w₂ ≠ z := fun h => hznot.2 (h ▸ hw₂)
            dsimp only [fL] at heq; rw [dif_neg h1z, dif_neg h2z] at heq
            have hset : ({w₁, z} : Finset V) = {w₂, z} := congr_arg Subtype.val heq
            have : w₁ ∈ ({w₂, z} : Finset V) := hset ▸ Finset.mem_insert_self w₁ {z}
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | h
            · rfl
            · exact absurd h h1z
          have hNR_card : NR.card = G.degree z := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            refine Finset.card_image_of_injOn fun w₁ hw₁ w₂ hw₂ heq => ?_
            rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
            have h1u : w₁ ≠ u := fun h => hznot.2 (h ▸ hw₁.symm)
            have h2u : w₂ ≠ u := fun h => hznot.2 (h ▸ hw₂.symm)
            dsimp only [fR] at heq; rw [dif_neg h1u, dif_neg h2u] at heq
            have hset : ({u, w₁} : Finset V) = {u, w₂} := congr_arg Subtype.val heq
            have : w₁ ∈ ({u, w₂} : Finset V) := hset ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self w₁)
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h | rfl
            · exact absurd h h1u
            · rfl
          have hsub : NL ∪ NR ⊆ (tokenGraph G 2).neighborFinset S := Finset.union_subset hNL_sub hNR_sub
          have hc := Finset.card_le_card hsub
          rw [Finset.card_union_of_disjoint hdisjLR, hNL_card, hNR_card, SimpleGraph.card_neighborFinset_eq_degree] at hc
          exact hc
        have hgm := grone_merris_le (tokenGraph G 2) S (by omega)
        rw [hcard_u] at hrho_le
        have h1 : (G.degree u : ℝ) + 1 + 1 ≤ ((tokenGraph G 2).degree S : ℝ) + 1 := by
          have : G.degree u + 1 ≤ (tokenGraph G 2).degree S := by omega
          have hcast : ((G.degree u + 1 : ℕ) : ℝ) ≤ ((tokenGraph G 2).degree S : ℝ) := by exact_mod_cast this
          push_cast at hcast; linarith
        push_cast at hrho_le
        linarith
    · -- `A₀ = ∅`: symmetric to `B₀ = ∅`, with `u` and `v` swapped!
      rw [Finset.not_nonempty_iff_eq_empty] at hA0
      have hunion_eq : G.neighborFinset u ∪ G.neighborFinset v = insert v (G.neighborFinset v) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        constructor
        · rintro (huw | hvw)
          · by_contra hnot
            have : w ∈ A0 := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset u w).mpr huw, by
              simpa [Finset.mem_insert, SimpleGraph.mem_neighborFinset] using hnot⟩
            rw [hA0] at this; exact Finset.notMem_empty w this
          · exact Or.inr hvw
        · rintro (rfl | hvw)
          · exact Or.inl huv
          · exact Or.inr hvw
      have hcard_v : (G.neighborFinset u ∪ G.neighborFinset v).card = G.degree v + 1 := by
        rw [hunion_eq, Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
          SimpleGraph.card_neighborFinset_eq_degree]
      have hdeg_lt : G.degree v < Fintype.card V - 1 := by
        have hle : G.degree v ≤ Fintype.card V - 1 := by
          have := Finset.card_le_card (show G.neighborFinset v ⊆ Finset.univ.erase v from fun x hx =>
            Finset.mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset v x).mp hx)).symm, Finset.mem_univ x⟩)
          rw [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_erase_of_mem (Finset.mem_univ v),
            Finset.card_univ] at this
          exact this
        exact lt_of_le_of_ne hle (hdom v)
      have hlt_card : (insert v (G.neighborFinset v)).card < (Finset.univ : Finset V).card := by
        rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
          SimpleGraph.card_neighborFinset_eq_degree, Finset.card_univ]; omega
      obtain ⟨z, _, hznot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_card
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hznot
      have hdz : 1 ≤ G.degree z := by
        rcases hconn z v with ⟨w⟩
        cases w with
        | nil => exact absurd rfl hznot.1
        | @cons _ w1 _ hadj _ =>
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          exact Finset.one_le_card.mpr ⟨w1, (G.mem_neighborFinset z w1).mpr hadj⟩
      have hvz : v ≠ z := Ne.symm hznot.1
      let S : TokenVertex V 2 := mkTok2 v z hvz
      have hdegS : G.degree v + G.degree z ≤ (tokenGraph G 2).degree S := by
        let fL : V → TokenVertex V 2 := fun w => if h : w = z then S else mkTok2 w z h
        let fR : V → TokenVertex V 2 := fun w => if h : w = v then S else mkTok2 v w (Ne.symm h)
        let NL : Finset (TokenVertex V 2) := (G.neighborFinset v).image fL
        let NR : Finset (TokenVertex V 2) := (G.neighborFinset z).image fR
        have hNL_sub : NL ⊆ (tokenGraph G 2).neighborFinset S := by
          intro T hT; rcases Finset.mem_image.mp hT with ⟨w, hw, rfl⟩
          rw [SimpleGraph.mem_neighborFinset] at hw ⊢
          have hwz : w ≠ z := fun h => hznot.2 (h ▸ hw)
          dsimp only [fL]; rw [dif_neg hwz]
          exact mkTok2_adj_left hvz hwz hw
        have hNR_sub : NR ⊆ (tokenGraph G 2).neighborFinset S := by
          intro T hT; rcases Finset.mem_image.mp hT with ⟨w, hw, rfl⟩
          rw [SimpleGraph.mem_neighborFinset] at hw ⊢
          have hwv : w ≠ v := fun h => hznot.2 (h ▸ hw.symm)
          dsimp only [fR]; rw [dif_neg hwv]
          exact mkTok2_adj_right hvz hwv.symm hw
        have hdisjLR : Disjoint NL NR := by
          rw [Finset.disjoint_left]; intro T h1 h2
          rcases Finset.mem_image.mp h1 with ⟨w₁, hw₁, rfl⟩
          rcases Finset.mem_image.mp h2 with ⟨w₂, hw₂, heq⟩
          rw [SimpleGraph.mem_neighborFinset] at hw₁ hw₂
          have h1z : w₁ ≠ z := fun h => hznot.2 (h ▸ hw₁)
          have h2v : w₂ ≠ v := fun h => hznot.2 (h ▸ hw₂.symm)
          dsimp only [fL, fR] at heq; rw [dif_neg h1z, dif_neg h2v] at heq
          have hset : ({v, w₂} : Finset V) = {w₁, z} := congr_arg Subtype.val heq
          have hv_mem : v ∈ ({w₁, z} : Finset V) := hset ▸ Finset.mem_insert_self v {w₂}
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv_mem
          rcases hv_mem with h | h
          · exact (G.ne_of_adj hw₁) h
          · exact hvz h
        have hNL_card : NL.card = G.degree v := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          refine Finset.card_image_of_injOn fun w₁ hw₁ w₂ hw₂ heq => ?_
          rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
          have h1z : w₁ ≠ z := fun h => hznot.2 (h ▸ hw₁)
          have h2z : w₂ ≠ z := fun h => hznot.2 (h ▸ hw₂)
          dsimp only [fL] at heq; rw [dif_neg h1z, dif_neg h2z] at heq
          have hset : ({w₁, z} : Finset V) = {w₂, z} := congr_arg Subtype.val heq
          have : w₁ ∈ ({w₂, z} : Finset V) := hset ▸ Finset.mem_insert_self w₁ {z}
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | h
          · rfl
          · exact absurd h h1z
        have hNR_card : NR.card = G.degree z := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          refine Finset.card_image_of_injOn fun w₁ hw₁ w₂ hw₂ heq => ?_
          rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
          have h1v : w₁ ≠ v := fun h => hznot.2 (h ▸ hw₁.symm)
          have h2v : w₂ ≠ v := fun h => hznot.2 (h ▸ hw₂.symm)
          dsimp only [fR] at heq; rw [dif_neg h1v, dif_neg h2v] at heq
          have hset : ({v, w₁} : Finset V) = {v, w₂} := congr_arg Subtype.val heq
          have : w₁ ∈ ({v, w₂} : Finset V) := hset ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self w₁)
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h | rfl
          · exact absurd h h1v
          · rfl
        have hsub : NL ∪ NR ⊆ (tokenGraph G 2).neighborFinset S := Finset.union_subset hNL_sub hNR_sub
        have hc := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisjLR, hNL_card, hNR_card, SimpleGraph.card_neighborFinset_eq_degree] at hc
        exact hc
      have hgm := grone_merris_le (tokenGraph G 2) S (by omega)
      rw [hcard_v] at hrho_le
      have h1 : (G.degree v : ℝ) + 1 + 1 ≤ ((tokenGraph G 2).degree S : ℝ) + 1 := by
        have : G.degree v + 1 ≤ (tokenGraph G 2).degree S := by omega
        have hcast : ((G.degree v + 1 : ℕ) : ℝ) ≤ ((tokenGraph G 2).degree S : ℝ) := by exact_mod_cast this
        push_cast at hcast; linarith
      push_cast at hrho_le
      linarith

/-! ### 4. Lemma 6 (Stars and Triangles) and Theorem 2 (All Graphs Characterization) -/

/-- **Lemma 6a:** For any star `S_m` (`m ≥ 2`) and `1 ≤ j ≤ m - 1`,
`ρ(F_j(S_m)) = m` (and `ρ(S_m) = m`). -/
theorem rho_star {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hstar : IsStar G) (hm : 2 ≤ Fintype.card V) :
    lapSpectralRadius G = (Fintype.card V : ℝ) := by
  classical
  rcases hstar with ⟨c, hc⟩
  have hconn : G.Connected := by
    have hreach : ∀ v : V, G.Reachable c v := fun v => by
      by_cases hvc : v = c
      · rw [hvc]
      · exact ((hc c v).mpr (Or.inl ⟨rfl, hvc⟩)).reachable
    let : Nonempty V := ⟨c⟩
    exact ⟨fun u v => (hreach u).symm.trans (hreach v)⟩
  have hdegc : G.degree c = Fintype.card V - 1 := by
    have hnb : G.neighborFinset c = Finset.univ.erase c := by
      ext v; simp [SimpleGraph.mem_neighborFinset, hc]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hnb, Finset.card_erase_of_mem (Finset.mem_univ c),
      Finset.card_univ]
  have hge : (Fintype.card V : ℝ) ≤ lapSpectralRadius G := by
    have hgm := grone_merris_le G c (by omega)
    rw [hdegc] at hgm
    have hcast : ((Fintype.card V - 1 : ℕ) : ℝ) + 1 = (Fintype.card V : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card V), Nat.cast_one]; ring
    linarith
  have hedge : ∃ a b : V, G.Adj a b := by
    have hlt : ({c} : Finset V).card < (Finset.univ : Finset V).card := by simp; omega
    obtain ⟨v, _, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨c, v, (hc c v).mpr (Or.inl ⟨rfl, by simpa using hv⟩)⟩
  obtain ⟨u, v, _, hle⟩ := edge_diff_upper_bound G hconn hedge
  have hcard : ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Finset.card_le_univ _
  exact le_antisymm (le_trans hle hcard) hge

theorem rho_tokenGraph_star {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hstar : IsStar G) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j < Fintype.card V) :
    lapSpectralRadius (tokenGraph G j) = (Fintype.card V : ℝ) := by
  classical
  rcases hstar with ⟨c, hc⟩
  set m := Fintype.card V
  -- Bipartition: `c ∈ S` (degree `m - j`) vs `c ∉ S` (degree `j`).
  have hdeg_in : ∀ S : TokenVertex V j, c ∈ S.1 → (tokenGraph G j).degree S = m - j := by
    intro S hcS
    let f : V → TokenVertex V j := fun w =>
      if hw : w ∈ S.1 then S else ⟨insert w (S.1.erase c), by
        rw [Finset.card_insert_of_notMem (fun h => hw (Finset.mem_erase.mp h).2),
          Finset.card_erase_of_mem hcS, S.2]; omega⟩
    have himg : (Finset.univ \ S.1).image f = (tokenGraph G j).neighborFinset S := by
      ext T
      simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨w, hw, rfl⟩
        dsimp only [f]; rw [dif_neg hw]
        have hwc : w ≠ c := fun h => hw (h ▸ hcS)
        refine ⟨c, w, hcS, ?_, by simp, hw, (hc c w).mpr (Or.inl ⟨rfl, hwc⟩), ?_⟩
        · simp [hwc.symm]
        · ext x; simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨hxc, hxS⟩; exact ⟨fun h => hw (h ▸ hxS), Or.inr ⟨hxc, hxS⟩⟩
          · rintro ⟨hxw, rfl | ⟨hxc, hxS⟩⟩
            · exact absurd rfl hxw
            · exact ⟨hxc, hxS⟩
      · rintro ⟨u', v', hu'S, hu'T, hv'T, hv'S, huv', herase⟩
        have hu'c : u' = c := by
          rcases (hc u' v').mp huv' with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · rfl
          · exact absurd hcS hv'S
        subst hu'c
        refine ⟨v', hv'S, Subtype.ext ?_⟩
        dsimp only [f]; rw [dif_neg hv'S]; dsimp only
        rw [herase, Finset.insert_erase hv'T]
    have hfinj : Set.InjOn f ((Finset.univ \ S.1 : Finset V) : Set V) := by
      intro w₁ hw₁ w₂ hw₂ heq
      simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and] at hw₁ hw₂
      dsimp only [f] at heq; rw [dif_neg hw₁, dif_neg hw₂] at heq
      have hset : insert w₁ (S.1.erase c) = insert w₂ (S.1.erase c) := congr_arg Subtype.val heq
      have : w₁ ∈ insert w₂ (S.1.erase c) := hset ▸ Finset.mem_insert_self w₁ _
      simp only [Finset.mem_insert, Finset.mem_erase] at this
      rcases this with rfl | ⟨_, hS⟩
      · rfl
      · exact absurd hS hw₁
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← himg, Finset.card_image_of_injOn hfinj,
      Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, S.2]
  have hdeg_out : ∀ S : TokenVertex V j, c ∉ S.1 → (tokenGraph G j).degree S = j := by
    intro S hcS
    let f : V → TokenVertex V j := fun w =>
      if hw : w ∈ S.1 then ⟨insert c (S.1.erase w), by
        rw [Finset.card_insert_of_notMem (fun h => hcS (Finset.mem_erase.mp h).2),
          Finset.card_erase_of_mem hw, S.2]; omega⟩
      else S
    have himg : S.1.image f = (tokenGraph G j).neighborFinset S := by
      ext T
      simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨w, hw, rfl⟩
        dsimp only [f]; rw [dif_pos hw]
        have hwc : w ≠ c := fun h => hcS (h ▸ hw)
        refine ⟨w, c, hw, ?_, by simp, hcS, (hc w c).mpr (Or.inr ⟨rfl, hwc⟩), ?_⟩
        · simp [hwc]
        · ext x; simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨hxw, hxS⟩; exact ⟨fun h => hcS (h ▸ hxS), Or.inr ⟨hxw, hxS⟩⟩
          · rintro ⟨hxc, rfl | ⟨hxw, hxS⟩⟩
            · exact absurd rfl hxc
            · exact ⟨hxw, hxS⟩
      · rintro ⟨u', v', hu'S, hu'T, hv'T, hv'S, huv', herase⟩
        have hv'c : v' = c := by
          rcases (hc u' v').mp huv' with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact absurd hu'S hcS
          · rfl
        subst hv'c
        refine ⟨u', hu'S, Subtype.ext ?_⟩
        dsimp only [f]; rw [dif_pos hu'S]; dsimp only
        rw [herase, Finset.insert_erase hv'T]
    have hfinj : Set.InjOn f (S.1 : Set V) := by
      intro w₁ hw₁ w₂ hw₂ heq
      rw [Finset.mem_coe] at hw₁ hw₂
      dsimp only [f] at heq; rw [dif_pos hw₁, dif_pos hw₂] at heq
      have hset : insert c (S.1.erase w₁) = insert c (S.1.erase w₂) := congr_arg Subtype.val heq
      by_contra hne
      have : w₁ ∈ insert c (S.1.erase w₂) := Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hw₁⟩)
      rw [← hset] at this
      simp only [Finset.mem_insert, Finset.mem_erase] at this
      rcases this with rfl | ⟨h, _⟩
      · exact hcS hw₁
      · exact h rfl
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← himg, Finset.card_image_of_injOn hfinj, S.2]
  have hbip : ∀ S T : TokenVertex V j, (tokenGraph G j).Adj S T → (c ∈ S.1 ↔ c ∉ T.1) := by
    intro S T ⟨u', v', hu'S, hu'T, hv'T, hv'S, huv', _⟩
    rcases (hc u' v').mp huv' with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · simp [hu'S, hu'T]
    · simp [hv'T, hv'S]
  -- Existence of a vertex `S0` with `c ∈ S0`:
  have hS0 : ∃ S0 : TokenVertex V j, c ∈ S0.1 := by
    have hcard_er : (Finset.univ.erase c : Finset V).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ]
    obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq (s := Finset.univ.erase c) (n := j - 1) (by omega)
    have hcA : c ∉ A := fun h => (Finset.mem_erase.mp (hAsub h)).1 rfl
    exact ⟨⟨insert c A, by rw [Finset.card_insert_of_notMem hcA, hAcard]; omega⟩, Finset.mem_insert_self c A⟩
  rcases hS0 with ⟨S0, hS0c⟩
  let : Nonempty (TokenVertex V j) := ⟨S0⟩
  -- Upper bound `ρ(F_j(S_m)) ≤ m`: for any `f`, apply `(a - b)^2 ≤ (a^2/s + b^2/t) * (s + t)`
  -- or directly bound `fᵀ L f ≤ m * (fᵀ f)` via `(f S - f T)^2 ≤ (m/s) f S ^ 2 + (m/t) f T ^ 2`!
  -- Wait: for `s = m - j > 0` and `t = j > 0`, `s + t = m` and
  -- `(s * x - (-t) * y)` -> `(x - y)^2 ≤ (m / s) * x^2 + (m / t) * y^2` because
  -- `(m/s) x^2 + (m/t) y^2 - (x - y)^2 = (t/s) x^2 + 2xy + (s/t) y^2 = (√(t/s) x + √(s/t) y)^2 ≥ 0`!
  -- Multiply by `s * t > 0`: `s * t * (x - y)^2 ≤ t * m * x^2 + s * m * y^2` — PURE `nlinarith`!!
  have hle : lapSpectralRadius (tokenGraph G j) ≤ (m : ℝ) := by
    obtain ⟨x, hx0, hxeig⟩ := exists_top_eigenvector (tokenGraph G j)
    have hquad_eq : lapQuad (tokenGraph G j) x = lapSpectralRadius (tokenGraph G j) * (x ⬝ᵥ x) := by
      unfold lapQuad; rw [hxeig, dotProduct_smul, smul_eq_mul]
    set s : ℝ := ((m - j : ℕ) : ℝ)
    set t : ℝ := (j : ℝ)
    have hs_pos : 0 < s := by dsimp [s]; exact_mod_cast (by omega : 0 < m - j)
    have ht_pos : 0 < t := by dsimp [t]; exact_mod_cast (by omega : 0 < j)
    have hst_sum : s + t = (m : ℝ) := by
      dsimp [s, t]; rw [Nat.cast_sub (by omega : j ≤ m)]; ring
    have hbound : lapQuad (tokenGraph G j) x ≤ (m : ℝ) * (x ⬝ᵥ x) := by
      rw [lapQuad_eq_sum_sq]
      have hterm : ∀ S T : TokenVertex V j,
          (if (tokenGraph G j).Adj S T then (x S - x T) ^ 2 else 0) ≤
          if (tokenGraph G j).Adj S T then
            (if c ∈ S.1 then (m : ℝ) / s * x S ^ 2 + (m : ℝ) / t * x T ^ 2
             else (m : ℝ) / t * x S ^ 2 + (m : ℝ) / s * x T ^ 2)
          else 0 := by
        intro S T
        split_ifs with hadj hcS
        · have hkey : 0 ≤ (t * x S + s * x T) ^ 2 := sq_nonneg _
          have : (x S - x T) ^ 2 * (s * t) ≤ ((m : ℝ) * t * x S ^ 2 + (m : ℝ) * s * x T ^ 2) := by
            rw [← hst_sum]; nlinarith
          have hdiv := div_le_div_of_nonneg_right this (mul_pos hs_pos ht_pos).le
          calc (x S - x T) ^ 2 = (x S - x T) ^ 2 * (s * t) / (s * t) := by
                rw [mul_div_cancel_right₀ _ (mul_pos hs_pos ht_pos).ne']
            _ ≤ ((m : ℝ) * t * x S ^ 2 + (m : ℝ) * s * x T ^ 2) / (s * t) := hdiv
            _ = (m : ℝ) / s * x S ^ 2 + (m : ℝ) / t * x T ^ 2 := by
                field_simp [hs_pos.ne', ht_pos.ne']
        · have hkey : 0 ≤ (s * x S + t * x T) ^ 2 := sq_nonneg _
          have : (x S - x T) ^ 2 * (s * t) ≤ ((m : ℝ) * s * x S ^ 2 + (m : ℝ) * t * x T ^ 2) := by
            rw [← hst_sum]; nlinarith
          have hdiv := div_le_div_of_nonneg_right this (mul_pos hs_pos ht_pos).le
          calc (x S - x T) ^ 2 = (x S - x T) ^ 2 * (s * t) / (s * t) := by
                rw [mul_div_cancel_right₀ _ (mul_pos hs_pos ht_pos).ne']
            _ ≤ ((m : ℝ) * s * x S ^ 2 + (m : ℝ) * t * x T ^ 2) / (s * t) := hdiv
            _ = (m : ℝ) / t * x S ^ 2 + (m : ℝ) / s * x T ^ 2 := by
                field_simp [hs_pos.ne', ht_pos.ne']
        · exact le_rfl
      have hsum_le : (∑ S : TokenVertex V j, ∑ T : TokenVertex V j,
          if (tokenGraph G j).Adj S T then (x S - x T) ^ 2 else 0) ≤
          ∑ S : TokenVertex V j, ∑ T : TokenVertex V j,
          if (tokenGraph G j).Adj S T then
            (if c ∈ S.1 then (m : ℝ) / s * x S ^ 2 + (m : ℝ) / t * x T ^ 2
             else (m : ℝ) / t * x S ^ 2 + (m : ℝ) / s * x T ^ 2)
          else 0 :=
        Finset.sum_le_sum fun S _ => Finset.sum_le_sum fun T _ => hterm S T
      -- Evaluate RHS by symmetry `(S, T) ↔ (T, S)`!
      have hrhs : (∑ S : TokenVertex V j, ∑ T : TokenVertex V j,
          if (tokenGraph G j).Adj S T then
            (if c ∈ S.1 then (m : ℝ) / s * x S ^ 2 + (m : ℝ) / t * x T ^ 2
             else (m : ℝ) / t * x S ^ 2 + (m : ℝ) / s * x T ^ 2)
          else 0) = 2 * ((m : ℝ) * (x ⬝ᵥ x)) := by
        have hsplit : ∀ S : TokenVertex V j,
            (∑ T : TokenVertex V j,
              if (tokenGraph G j).Adj S T then
                (if c ∈ S.1 then (m : ℝ) / s * x S ^ 2 + (m : ℝ) / t * x T ^ 2
                 else (m : ℝ) / t * x S ^ 2 + (m : ℝ) / s * x T ^ 2)
              else 0) =
            (∑ T : TokenVertex V j,
              if (tokenGraph G j).Adj S T then
                (if c ∈ S.1 then (m : ℝ) / s * x S ^ 2 else (m : ℝ) / t * x S ^ 2)
              else 0) +
            (∑ T : TokenVertex V j,
              if (tokenGraph G j).Adj S T then
                (if c ∈ T.1 then (m : ℝ) / s * x T ^ 2 else (m : ℝ) / t * x T ^ 2)
              else 0) := by
          intro S; rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun T _ => ?_
          by_cases hadj : (tokenGraph G j).Adj S T
          · rw [if_pos hadj, if_pos hadj, if_pos hadj]
            have hb := hbip S T hadj
            by_cases hcS : c ∈ S.1
            · have hcT : c ∉ T.1 := hb.mp hcS
              simp [hcS, hcT]
            · have hcT : c ∈ T.1 := by_contra fun h => hcS (hb.mpr h)
              simp [hcS, hcT]
          · simp [hadj]
        simp_rw [hsplit, Finset.sum_add_distrib]
        have hpart1 : (∑ S : TokenVertex V j, ∑ T : TokenVertex V j,
            if (tokenGraph G j).Adj S T then
              (if c ∈ S.1 then (m : ℝ) / s * x S ^ 2 else (m : ℝ) / t * x S ^ 2)
            else 0) = (m : ℝ) * (x ⬝ᵥ x) := by
          have hrow : ∀ S : TokenVertex V j,
              (∑ T : TokenVertex V j,
                if (tokenGraph G j).Adj S T then
                  (if c ∈ S.1 then (m : ℝ) / s * x S ^ 2 else (m : ℝ) / t * x S ^ 2)
                else 0) = (m : ℝ) * (x S * x S) := by
            intro S
            rw [← Finset.sum_subset (Finset.subset_univ ((tokenGraph G j).neighborFinset S))]
            · have hcongr : ∑ T ∈ (tokenGraph G j).neighborFinset S,
                  (if (tokenGraph G j).Adj S T then
                    (if c ∈ S.1 then (m : ℝ) / s * x S ^ 2 else (m : ℝ) / t * x S ^ 2)
                   else 0) =
                  ((tokenGraph G j).degree S : ℝ) *
                    (if c ∈ S.1 then (m : ℝ) / s * x S ^ 2 else (m : ℝ) / t * x S ^ 2) := by
                rw [← SimpleGraph.card_neighborFinset_eq_degree, ← nsmul_eq_mul, ← Finset.sum_const]
                refine Finset.sum_congr rfl fun T hT => ?_
                rw [if_pos (((tokenGraph G j).mem_neighborFinset S T).mp hT)]
              rw [hcongr]
              by_cases hcS : c ∈ S.1
              · rw [if_pos hcS, hdeg_in S hcS]; change s * ((m : ℝ) / s * x S ^ 2) = _; field_simp [hs_pos.ne']
              · rw [if_neg hcS, hdeg_out S hcS]; change t * ((m : ℝ) / t * x S ^ 2) = _; field_simp [ht_pos.ne']
            · intro T _ hT; rw [SimpleGraph.mem_neighborFinset] at hT; rw [if_neg hT]
          simp_rw [hrow, ← Finset.mul_sum]; rfl
        have hpart2 : (∑ S : TokenVertex V j, ∑ T : TokenVertex V j,
            if (tokenGraph G j).Adj S T then
              (if c ∈ T.1 then (m : ℝ) / s * x T ^ 2 else (m : ℝ) / t * x T ^ 2)
            else 0) = (m : ℝ) * (x ⬝ᵥ x) := by
          rw [Finset.sum_comm]
          convert hpart1 using 2 with T
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [if_congr (SimpleGraph.adj_comm _ S T) rfl rfl]
        linarith
      linarith
    have hpos : 0 < x ⬝ᵥ x := dotProduct_self_pos hx0
    nlinarith
  -- Lower bound `ρ(F_j(S_m)) ≥ m` via explicit eigenvector `f S = if c ∈ S then s else -t`:
  have hge : (m : ℝ) ≤ lapSpectralRadius (tokenGraph G j) := by
    set s : ℝ := ((m - j : ℕ) : ℝ)
    set t : ℝ := (j : ℝ)
    have hs_pos : 0 < s := by dsimp [s]; exact_mod_cast (by omega : 0 < m - j)
    have hst_sum : s + t = (m : ℝ) := by
      dsimp [s, t]; rw [Nat.cast_sub (by omega : j ≤ m)]; ring
    let f : TokenVertex V j → ℝ := fun S => if c ∈ S.1 then s else -t
    have hf_ne : f ≠ 0 := by
      intro h0
      have := congr_fun h0 S0
      simp only [f, hS0c, ↓reduceIte, Pi.zero_apply] at this
      linarith
    have heig : (tokenGraph G j).lapMatrix ℝ *ᵥ f = (m : ℝ) • f := by
      ext S
      simp only [SimpleGraph.lapMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hcS : c ∈ S.1
      · have hnb : ∀ T ∈ (tokenGraph G j).neighborFinset S, f T = -t := by
          intro T hT
          have hcT : c ∉ T.1 := (hbip S T (((tokenGraph G j).mem_neighborFinset S T).mp hT)).mp hcS
          simp [f, hcT]
        rw [Finset.sum_congr rfl hnb, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
          hdeg_in S hcS, nsmul_eq_mul]
        simp only [f, hcS, ↓reduceIte]
        change s * s - s * -t = (m : ℝ) * s
        rw [← hst_sum]; ring
      · have hnb : ∀ T ∈ (tokenGraph G j).neighborFinset S, f T = s := by
          intro T hT
          have hcT : c ∈ T.1 := by_contra fun h => hcS ((hbip S T (((tokenGraph G j).mem_neighborFinset S T).mp hT)).mpr h)
          simp [f, hcT]
        rw [Finset.sum_congr rfl hnb, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
          hdeg_out S hcS, nsmul_eq_mul]
        simp only [f, hcS, ↓reduceIte]
        change t * -t - t * s = (m : ℝ) * -t
        rw [← hst_sum]; ring
    refine le_rho_of_rayleigh (tokenGraph G j) hf_ne ?_
    unfold lapQuad; rw [heig, dotProduct_smul, smul_eq_mul]
  exact le_antisymm hle hge

/-- **Theorem 1 Corollary (Connected Conjecture of Song–Dalfó–Fiol–Zhang):**
For every connected graph `G` of order `n ≥ 4`,
`(∀ k, 2 ≤ k → k ≤ n / 2 → ρ(F_k(G)) = ρ(G)) ↔ IsStar G`. -/
theorem connected_conjecture_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 4 ≤ Fintype.card V) (hconn : G.Connected) :
    (∀ k : ℕ, 2 ≤ k → k ≤ Fintype.card V / 2 →
      lapSpectralRadius (tokenGraph G k) = lapSpectralRadius G) ↔ IsStar G := by
  constructor
  · intro hall
    by_contra hnot
    have hlt := connected_nonstar_rho_F2_gt G hn hconn hnot
    have heq := hall 2 le_rfl (by omega)
    linarith
  · intro hstar k hk2 hkn
    rw [rho_tokenGraph_star G hstar k (by omega) (by omega), rho_star G hstar (by omega)]

/-! ### 5. Theorem 2: Complete Equality Characterization for All Graphs (`n ≥ 4`) -/

/-- Exact equality family in Theorem 2: edgeless, star plus isolated vertices (`m ≥ 2`),
or triangle `K_3` plus isolated vertices. -/
def IsEqualityGraph {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  (∀ u v : V, ¬ G.Adj u v) ∨
  (∃ H : Finset V, 2 ≤ H.card ∧ (∀ u v : V, G.Adj u v → u ∈ H ∧ v ∈ H) ∧
    IsStar (G.induce (H : Set V))) ∨
  (∃ H : Finset V, H.card = 3 ∧ (∀ u v : V, G.Adj u v → u ∈ H ∧ v ∈ H) ∧
    ∀ u v : V, u ∈ H → v ∈ H → u ≠ v → G.Adj u v)

private lemma rho_edgeless {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : ∀ u v : V, ¬ G.Adj u v) :
    lapSpectralRadius G = 0 := by
  refine le_antisymm ?_ (lapSpectralRadius_nonneg G)
  by_cases hV : Nonempty V
  · let : Nonempty V := hV
    obtain ⟨x, hx0, hxeig⟩ := exists_top_eigenvector G
    have hLx0 : G.lapMatrix ℝ *ᵥ x = 0 :=
      G.lapMatrix_mulVec_eq_zero_iff_forall_adj.mpr fun i j hij => absurd hij (h i j)
    rw [hLx0] at hxeig
    have := (smul_eq_zero.mp hxeig.symm).resolve_right hx0
    linarith
  · unfold lapSpectralRadius; rw [dif_neg hV]

private lemma rho_of_active_subset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : Finset V)
    (hact : ∀ u v : V, G.Adj u v → u ∈ H ∧ v ∈ H) :
    lapSpectralRadius G = lapSpectralRadius (G.induce (H : Set V)) := by
  classical
  refine le_antisymm ?_ (rho_le_of_embedding Subtype.val Subtype.val_injective (fun _ _ h => h))
  by_cases hV : Nonempty V
  · let : Nonempty V := hV
    obtain ⟨x, hx0, hxeig⟩ := exists_top_eigenvector G
    by_cases hzero : lapSpectralRadius G = 0
    · rw [hzero]; exact lapSpectralRadius_nonneg _
    · have hpos : 0 < lapSpectralRadius G :=
        lt_of_le_of_ne (lapSpectralRadius_nonneg G) (Ne.symm hzero)
      -- Every vertex outside `H` is isolated, so `x w = 0` for `w ∉ H`!
      have hx_out : ∀ w : V, w ∉ H → x w = 0 := by
        intro w hw
        have h1 := congr_fun hxeig w
        simp only [Pi.smul_apply, smul_eq_mul, SimpleGraph.lapMatrix_mulVec_apply] at h1
        have hnb0 : G.neighborFinset w = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro u hu; exact hw (hact w u ((G.mem_neighborFinset w u).mp hu)).1
        rw [← SimpleGraph.card_neighborFinset_eq_degree, hnb0] at h1
        simp only [Finset.card_empty, Nat.cast_zero, zero_mul, Finset.sum_empty, sub_self] at h1
        exact (mul_eq_zero.mp h1.symm).resolve_left hpos.ne'
      let xH : ↥(H : Set V) → ℝ := fun u => x u.1
      have hxH_ne : xH ≠ 0 := by
        intro h0; apply hx0; ext w
        by_cases hw : w ∈ H
        · exact congr_fun h0 ⟨w, hw⟩
        · exact hx_out w hw
      have hnorm : xH ⬝ᵥ xH = x ⬝ᵥ x := by
        unfold dotProduct
        have h1 : ∑ u : ↥(H : Set V), xH u * xH u = ∑ w ∈ H, x w * x w :=
          Finset.sum_coe_sort H (fun w => x w * x w)
        rw [h1, Finset.sum_subset (Finset.subset_univ H)]
        intro w _ hw; rw [hx_out w hw, mul_zero]
      have hquad : lapQuad (G.induce (H : Set V)) xH = lapQuad G x := by
        rw [lapQuad_eq_sum_sq, lapQuad_eq_sum_sq]
        congr 1
        have h1 : (∑ a : ↥(H : Set V), ∑ b : ↥(H : Set V),
            if (G.induce (H : Set V)).Adj a b then (xH a - xH b) ^ 2 else 0) =
            ∑ a ∈ H, ∑ b ∈ H, if G.Adj a b then (x a - x b) ^ 2 else 0 := by
          simp only [SimpleGraph.induce_adj, xH]
          calc (∑ a : ↥(H : Set V), ∑ b : ↥(H : Set V),
                if G.Adj a.1 b.1 then (x a.1 - x b.1) ^ 2 else 0)
              = ∑ a ∈ H, ∑ b : ↥(H : Set V), if G.Adj a b.1 then (x a - x b.1) ^ 2 else 0 :=
                Finset.sum_coe_sort H (fun a => ∑ b : ↥(H : Set V), if G.Adj a b.1 then (x a - x b.1) ^ 2 else 0)
            _ = ∑ a ∈ H, ∑ b ∈ H, if G.Adj a b then (x a - x b) ^ 2 else 0 :=
                Finset.sum_congr rfl fun a _ =>
                  Finset.sum_coe_sort H (fun b => if G.Adj a b then (x a - x b) ^ 2 else 0)
        rw [h1]
        rw [Finset.sum_subset (Finset.subset_univ H)]
        · refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_subset (Finset.subset_univ H)]
          intro b _ hb
          exact if_neg fun hadj => hb (hact a b hadj).2
        · intro a _ ha
          exact Finset.sum_eq_zero fun b _ => if_neg fun hadj => ha (hact a b hadj).1
      have hx_quad : lapQuad G x = lapSpectralRadius G * (x ⬝ᵥ x) := by
        unfold lapQuad; rw [hxeig, dotProduct_smul, smul_eq_mul]
      refine le_rho_of_rayleigh (G.induce (H : Set V)) hxH_ne ?_
      rw [hnorm, hquad, hx_quad]
  · unfold lapSpectralRadius; rw [dif_neg hV]; exact lapSpectralRadius_nonneg _

private lemma rho_K3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h3 : Fintype.card V = 3)
    (htop : ∀ u v : V, u ≠ v → G.Adj u v) :
    lapSpectralRadius G = 3 := by
  classical
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v0⟩ := hV
  have hdeg : ∀ v : V, G.degree v = 2 := by
    intro v
    have hnb : G.neighborFinset v = Finset.univ.erase v := by
      ext u; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h => (G.ne_of_adj h).symm, fun h => htop v u h.symm⟩
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hnb, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, h3]
  have hge : (3 : ℝ) ≤ lapSpectralRadius G := by
    have hgm := grone_merris_le G v0 (by rw [hdeg]; omega)
    rw [hdeg] at hgm; norm_num at hgm; exact hgm
  have hconn : G.Connected := by
    let : Nonempty V := ⟨v0⟩
    refine ⟨fun u v => ?_⟩
    by_cases h : u = v
    · subst h; exact SimpleGraph.Reachable.refl u
    · exact (htop u v h).reachable
  have hedge : ∃ a b : V, G.Adj a b := by
    have hlt : ({v0} : Finset V).card < (Finset.univ : Finset V).card := by simp [h3]
    obtain ⟨v1, _, hv1⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨v0, v1, htop v0 v1 (by simpa [eq_comm] using hv1)⟩
  obtain ⟨u, v, _, hle⟩ := edge_diff_upper_bound G hconn hedge
  have hcard : ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) ≤ 3 := by
    have : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ 3 := by
      calc (G.neighborFinset u ∪ G.neighborFinset v).card ≤ (Finset.univ : Finset V).card := Finset.card_le_univ _
        _ = 3 := h3
    exact_mod_cast this
  exact le_antisymm (le_trans hle hcard) hge

private lemma rho_tokenGraph_K3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h3 : Fintype.card V = 3)
    (htop : ∀ u v : V, u ≠ v → G.Adj u v) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 2) :
    lapSpectralRadius (tokenGraph G j) = 3 := by
  classical
  have hcard_tok : Fintype.card (TokenVertex V j) = 3 := by
    have h1 : Fintype.card (TokenVertex V j) = ((Finset.univ : Finset V).powersetCard j).card := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr
        { toFun := fun S => ⟨S.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.2⟩⟩
          invFun := fun S => ⟨S.1, (Finset.mem_powersetCard.mp S.2).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h1, Finset.card_powersetCard, Finset.card_univ, h3]
    interval_cases j <;> decide
  refine rho_K3 (tokenGraph G j) hcard_tok ?_
  intro S T hne
  have hcard_inter : (S.1 \ T.1).card = 1 ∧ (T.1 \ S.1).card = 1 := by
    have h1 := Finset.card_sdiff_add_card_inter S.1 T.1
    have h2 := Finset.card_sdiff_add_card_inter T.1 S.1
    rw [Finset.inter_comm] at h2
    have hunion : (S.1 ∪ T.1).card ≤ 3 := by
      calc (S.1 ∪ T.1).card ≤ (Finset.univ : Finset V).card := Finset.card_le_univ _
        _ = 3 := h3
    have h3' := Finset.card_union_add_card_inter S.1 T.1
    have hpos : 1 ≤ (S.1 \ T.1).card := by
      by_contra h0
      have he : S.1 \ T.1 = ∅ := Finset.card_eq_zero.mp (by omega)
      have hsub : S.1 ⊆ T.1 := Finset.sdiff_eq_empty_iff_subset.mp he
      have heq : S.1 = T.1 := Finset.eq_of_subset_of_card_le hsub (by rw [S.2, T.2])
      exact hne (Subtype.ext heq)
    have hS := S.2; have hT := T.2
    omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard_inter.1
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard_inter.2
  have huST : u ∈ S.1 ∧ u ∉ T.1 := Finset.mem_sdiff.mp (hu ▸ Finset.mem_singleton_self u)
  have hvTS : v ∈ T.1 ∧ v ∉ S.1 := Finset.mem_sdiff.mp (hv ▸ Finset.mem_singleton_self v)
  have huv_ne : u ≠ v := fun h => hvTS.2 (h ▸ huST.1)
  refine ⟨u, v, huST.1, huST.2, hvTS.1, hvTS.2, htop u v huv_ne, ?_⟩
  ext x
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hxu, hxS⟩
    have hxT : x ∈ T.1 := by
      by_contra hnot
      have : x ∈ S.1 \ T.1 := Finset.mem_sdiff.mpr ⟨hxS, hnot⟩
      rw [hu, Finset.mem_singleton] at this; exact hxu this
    exact ⟨fun h => hvTS.2 (h ▸ hxS), hxT⟩
  · rintro ⟨hxv, hxT⟩
    have hxS : x ∈ S.1 := by
      by_contra hnot
      have : x ∈ T.1 \ S.1 := Finset.mem_sdiff.mpr ⟨hxT, hnot⟩
      rw [hv, Finset.mem_singleton] at this; exact hxv this
    exact ⟨fun h => huST.2 (h ▸ hxT), hxS⟩

/-- Decomposition of `F_k(G)` when all edges of `G` lie inside a subset `H`:
every edge of `F_k(G)` preserves `S \ H` (the tokens sitting on isolated vertices outside `H`).
Hence `ρ(F_k(G)) = max_{j feasible} ρ(F_j(G[H]))`. -/
private lemma rho_tokenGraph_active_subset_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : Finset V)
    (hact : ∀ u v : V, G.Adj u v → u ∈ H ∧ v ∈ H)
    (k : ℕ) (B : ℝ) (hB0 : 0 ≤ B)
    (hbound : ∀ j : ℕ, 1 ≤ j → j < H.card → lapSpectralRadius (tokenGraph (G.induce (H : Set V)) j) ≤ B) :
    lapSpectralRadius (tokenGraph G k) ≤ B := by
  classical
  by_cases hNon : Nonempty (TokenVertex V k)
  · let : Nonempty (TokenVertex V k) := hNon
    obtain ⟨x, hx0, hxeig⟩ := exists_top_eigenvector (tokenGraph G k)
    have hquad_eq : lapQuad (tokenGraph G k) x = lapSpectralRadius (tokenGraph G k) * (x ⬝ᵥ x) := by
      unfold lapQuad; rw [hxeig, dotProduct_smul, smul_eq_mul]
    -- Partition `TokenVertex V k` by `R = S \ H` (fixed by all edges of `F_k(G)`!).
    have hpres : ∀ S T : TokenVertex V k, (tokenGraph G k).Adj S T → S.1 \ H = T.1 \ H := by
      intro S T ⟨u, v, _, _, _, _, huv, herase⟩
      have huH := (hact u v huv).1
      have hvH := (hact u v huv).2
      ext w
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨hwS, hwH⟩
        have hwu : w ≠ u := fun h => hwH (h ▸ huH)
        have : w ∈ T.1.erase v := herase ▸ Finset.mem_erase.mpr ⟨hwu, hwS⟩
        exact ⟨(Finset.mem_erase.mp this).2, hwH⟩
      · rintro ⟨hwT, hwH⟩
        have hwv : w ≠ v := fun h => hwH (h ▸ hvH)
        have : w ∈ S.1.erase u := herase.symm ▸ Finset.mem_erase.mpr ⟨hwv, hwT⟩
        exact ⟨(Finset.mem_erase.mp this).2, hwH⟩
    -- On each fiber `F_R = {S | S \ H = R}` (with `j = k - R.card`), the quadratic form is
    -- bounded by `B * ∑_{S ∈ F_R} x S ^ 2`!
    let fiber : Finset V → Finset (TokenVertex V k) :=
      fun R => Finset.univ.filter (fun S => S.1 \ H = R)
    have hfiber_bound : ∀ R : Finset V,
        (∑ S ∈ fiber R, ∑ T ∈ fiber R, if (tokenGraph G k).Adj S T then (x S - x T) ^ 2 else 0) / 2 ≤
        B * ∑ S ∈ fiber R, x S * x S := by
      intro R
      by_cases hne : (fiber R).Nonempty
      · obtain ⟨S₀, hS₀⟩ := hne
        have hR_sub : R ⊆ Finset.univ \ H := by
          intro w hw
          have hS₀R : S₀.1 \ H = R := (Finset.mem_filter.mp hS₀).2
          rw [← hS₀R, Finset.mem_sdiff] at hw
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw.2⟩
        have hR_disj : Disjoint R H := by
          rw [Finset.disjoint_left]; intro w hwR hwH
          exact (Finset.mem_sdiff.mp (hR_sub hwR)).2 hwH
        set j : ℕ := k - R.card
        have hR_le : R.card ≤ k := by
          have hS₀R : S₀.1 \ H = R := (Finset.mem_filter.mp hS₀).2
          calc R.card = (S₀.1 \ H).card := by rw [hS₀R]
            _ ≤ S₀.1.card := Finset.card_le_card Finset.sdiff_subset
            _ = k := S₀.2
        by_cases hj0 : j = 0 ∨ H.card ≤ j
        · -- Every edge inside `fiber R` is impossible (either `j = 0` or `j = |H|`, so `S ∩ H` is fixed)!
          have hno_edge : ∀ S ∈ fiber R, ∀ T ∈ fiber R, ¬ (tokenGraph G k).Adj S T := by
            intro S hS T hT ⟨u, v, huS, huT, hvT, hvS, huv, _⟩
            have huH := (hact u v huv).1
            have hvH := (hact u v huv).2
            have hSR : S.1 \ H = R := (Finset.mem_filter.mp hS).2
            have hcard_inter : (S.1 ∩ H).card = j := by
              have h1 := Finset.card_sdiff_add_card_inter S.1 H
              rw [hSR, S.2] at h1; omega
            rcases hj0 with hj0 | hjH
            · have : (S.1 ∩ H).card = 0 := by omega
              rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at this
              exact this u (Finset.mem_inter.mpr ⟨huS, huH⟩)
            · have heq : S.1 ∩ H = H := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
              have : v ∈ S.1 ∩ H := by rw [heq]; exact hvH
              exact hvS (Finset.mem_inter.mp this).1
          have h0 : (∑ S ∈ fiber R, ∑ T ∈ fiber R,
              if (tokenGraph G k).Adj S T then (x S - x T) ^ 2 else 0) = 0 :=
            Finset.sum_eq_zero fun S hS => Finset.sum_eq_zero fun T hT => if_neg (hno_edge S hS T hT)
          rw [h0, zero_div]
          exact mul_nonneg hB0 (Finset.sum_nonneg fun S _ => mul_self_nonneg (x S))
        · push Not at hj0
          -- Map `TokenVertex ↥(H : Set V) j` bijectively onto `fiber R` by `A ↦ A.map Subtype.val ∪ R`.
          let emb : TokenVertex ↥(H : Set V) j → TokenVertex V k := fun A =>
            ⟨A.1.map ⟨Subtype.val, Subtype.val_injective⟩ ∪ R, by
              have hd : Disjoint (A.1.map ⟨Subtype.val, Subtype.val_injective⟩) R := by
                rw [Finset.disjoint_left]; intro w hwA hwR
                rcases Finset.mem_map.mp hwA with ⟨a, _, rfl⟩
                exact Finset.disjoint_left.mp hR_disj hwR a.2
              rw [Finset.card_union_of_disjoint hd, Finset.card_map, A.2]; omega⟩
          have hemb_inj : Function.Injective emb := by
            intro A₁ A₂ heq
            have hset := congr_arg Subtype.val heq
            ext a
            have haR : a.1 ∉ R := fun h => Finset.disjoint_left.mp hR_disj h a.2
            have := Finset.ext_iff.mp hset a.1
            simpa [emb, haR] using this
          have hemb_img : Finset.univ.image emb = fiber R := by
            ext S
            simp only [Finset.mem_image, Finset.mem_univ, true_and, fiber, Finset.mem_filter]
            constructor
            · rintro ⟨A, rfl⟩
              ext w; simp only [emb, Finset.mem_sdiff, Finset.mem_union, Finset.mem_map,
                Function.Embedding.coeFn_mk, Subtype.exists]
              constructor
              · rintro ⟨⟨a, haH, _, rfl⟩ | hwR, hwH⟩
                · exact absurd haH hwH
                · exact hwR
              · intro hwR
                exact ⟨Or.inr hwR, fun hwH => Finset.disjoint_left.mp hR_disj hwR hwH⟩
            · intro hSR
              let Aset : Finset ↥(H : Set V) := (S.1 ∩ H).attach.image fun w =>
                ⟨w.1, (Finset.mem_inter.mp w.2).2⟩
              have hAcard : Aset.card = j := by
                have hinj : Function.Injective (fun w : {v // v ∈ S.1 ∩ H} =>
                    (⟨w.1, (Finset.mem_inter.mp w.2).2⟩ : ↥(H : Set V))) :=
                  fun _ _ h => Subtype.ext (congr_arg (Subtype.val : ↥(H : Set V) → V) h)
                dsimp only [Aset]
                rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
                have h1 := Finset.card_sdiff_add_card_inter S.1 H
                rw [hSR, S.2] at h1; omega
              refine ⟨⟨Aset, hAcard⟩, Subtype.ext ?_⟩
              ext w
              simp only [emb, Aset, Finset.mem_union, Finset.mem_map, Finset.mem_image,
                Finset.mem_attach, true_and, Subtype.exists, Function.Embedding.coeFn_mk]
              constructor
              · rintro (⟨a, _, ⟨y, hy, hyEq⟩, rfl⟩ | hwR)
                · have hya : y = a := congr_arg (Subtype.val : ↥(H : Set V) → V) hyEq
                  subst hya; exact (Finset.mem_inter.mp hy).1
                · rw [← hSR, Finset.mem_sdiff] at hwR; exact hwR.1
              · intro hwS
                by_cases hwH : w ∈ H
                · left; exact ⟨w, hwH, ⟨w, Finset.mem_inter.mpr ⟨hwS, hwH⟩, rfl⟩, rfl⟩
                · right; rw [← hSR]; exact Finset.mem_sdiff.mpr ⟨hwS, hwH⟩
          have hemb_adj : ∀ A₁ A₂ : TokenVertex ↥(H : Set V) j,
              (tokenGraph G k).Adj (emb A₁) (emb A₂) →
              (tokenGraph (G.induce (H : Set V)) j).Adj A₁ A₂ := by
            intro A₁ A₂ ⟨u, v, hu1, hu2, hv2, hv1, huv, herase⟩
            have huH := (hact u v huv).1
            have hvH := (hact u v huv).2
            have huR : u ∉ R := fun h => Finset.disjoint_left.mp hR_disj h huH
            have hvR : v ∉ R := fun h => Finset.disjoint_left.mp hR_disj h hvH
            have huA1 : (⟨u, huH⟩ : ↥(H : Set V)) ∈ A₁.1 := by
              rcases Finset.mem_union.mp hu1 with hmap | hR
              · rcases Finset.mem_map.mp hmap with ⟨a, ha, rfl⟩; exact ha
              · exact absurd hR huR
            have huA2 : (⟨u, huH⟩ : ↥(H : Set V)) ∉ A₂.1 := fun h =>
              hu2 (Finset.mem_union_left R (Finset.mem_map.mpr ⟨⟨u, huH⟩, h, rfl⟩))
            have hvA2 : (⟨v, hvH⟩ : ↥(H : Set V)) ∈ A₂.1 := by
              rcases Finset.mem_union.mp hv2 with hmap | hR
              · rcases Finset.mem_map.mp hmap with ⟨a, ha, rfl⟩; exact ha
              · exact absurd hR hvR
            have hvA1 : (⟨v, hvH⟩ : ↥(H : Set V)) ∉ A₁.1 := fun h =>
              hv1 (Finset.mem_union_left R (Finset.mem_map.mpr ⟨⟨v, hvH⟩, h, rfl⟩))
            refine ⟨⟨u, huH⟩, ⟨v, hvH⟩, huA1, huA2, hvA2, hvA1, huv, ?_⟩
            ext a
            have haR : a.1 ∉ R := fun h => Finset.disjoint_left.mp hR_disj h a.2
            have h1 := Finset.ext_iff.mp herase a.1
            simpa [emb, haR, Subtype.ext_iff] using h1
          let yA : TokenVertex ↥(H : Set V) j → ℝ := fun A => x (emb A)
          have hray := rayleigh_le_rho (tokenGraph (G.induce (H : Set V)) j) yA
          have hrho_leB : lapSpectralRadius (tokenGraph (G.induce (H : Set V)) j) ≤ B :=
            hbound j (by omega) hj0.2
          have hnorm_eq : yA ⬝ᵥ yA = ∑ S ∈ fiber R, x S * x S := by
            rw [← hemb_img, Finset.sum_image (fun a _ b _ h => hemb_inj h)]; rfl
          have hquad_le : (∑ S ∈ fiber R, ∑ T ∈ fiber R,
              if (tokenGraph G k).Adj S T then (x S - x T) ^ 2 else 0) / 2 ≤
              lapQuad (tokenGraph (G.induce (H : Set V)) j) yA := by
            rw [lapQuad_eq_sum_sq, ← hemb_img, Finset.sum_image (fun a _ b _ h => hemb_inj h)]
            refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun A₁ _ => ?_) (by norm_num)
            rw [Finset.sum_image (fun a _ b _ h => hemb_inj h)]
            refine Finset.sum_le_sum fun A₂ _ => ?_
            split_ifs with h1 h2
            · exact le_rfl
            · exact absurd (hemb_adj A₁ A₂ h1) h2
            · positivity
            · exact le_rfl
          have hnn : 0 ≤ yA ⬝ᵥ yA := dotProduct_self_nonneg yA
          calc (∑ S ∈ fiber R, ∑ T ∈ fiber R,
                if (tokenGraph G k).Adj S T then (x S - x T) ^ 2 else 0) / 2
              ≤ lapQuad (tokenGraph (G.induce (H : Set V)) j) yA := hquad_le
            _ ≤ lapSpectralRadius (tokenGraph (G.induce (H : Set V)) j) * (yA ⬝ᵥ yA) := hray
            _ ≤ B * (yA ⬝ᵥ yA) := mul_le_mul_of_nonneg_right hrho_leB hnn
            _ = B * ∑ S ∈ fiber R, x S * x S := by rw [hnorm_eq]
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
    -- Sum `hfiber_bound` over all `R : Finset V`:
    have htot : lapQuad (tokenGraph G k) x ≤ B * (x ⬝ᵥ x) := by
      rw [lapQuad_eq_sum_sq]
      have hpart_norm : x ⬝ᵥ x = ∑ R : Finset V, ∑ S ∈ fiber R, x S * x S := by
        unfold dotProduct
        rw [Finset.sum_fiberwise_of_maps_to (g := fun S : TokenVertex V k => S.1 \ H)
          (fun _ _ => Finset.mem_univ _)]
      have hpart_quad : (∑ S : TokenVertex V k, ∑ T : TokenVertex V k,
            if (tokenGraph G k).Adj S T then (x S - x T) ^ 2 else 0) =
          ∑ R : Finset V, ∑ S ∈ fiber R, ∑ T ∈ fiber R,
            if (tokenGraph G k).Adj S T then (x S - x T) ^ 2 else 0 := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun S : TokenVertex V k => S.1 \ H)
          (fun _ _ => Finset.mem_univ _)]
        refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun S hS => ?_
        rw [← Finset.sum_subset (Finset.subset_univ (fiber R))]
        intro T _ hT
        refine if_neg fun hadj => hT ?_
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ T, (hpres S T hadj).symm.trans (Finset.mem_filter.mp hS).2⟩
      rw [hpart_quad, hpart_norm, Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_le_sum fun R _ => hfiber_bound R
    have hpos : 0 < x ⬝ᵥ x := dotProduct_self_pos hx0
    nlinarith
  · unfold lapSpectralRadius; rw [dif_neg hNon]; exact hB0

private lemma rho_tokenGraph_active_subset_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : Finset V) (k j : ℕ)
    (hjk : j ≤ k) (hkj : k - j ≤ (Finset.univ \ H).card) :
    lapSpectralRadius (tokenGraph (G.induce (H : Set V)) j) ≤
      lapSpectralRadius (tokenGraph G k) := by
  classical
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hkj
  have hR_disj : Disjoint R H := by
    rw [Finset.disjoint_left]; intro w hwR hwH
    exact (Finset.mem_sdiff.mp (hRsub hwR)).2 hwH
  let emb : TokenVertex ↥(H : Set V) j → TokenVertex V k := fun A =>
    ⟨A.1.map ⟨Subtype.val, Subtype.val_injective⟩ ∪ R, by
      have hd : Disjoint (A.1.map ⟨Subtype.val, Subtype.val_injective⟩) R := by
        rw [Finset.disjoint_left]; intro w hwA hwR
        rcases Finset.mem_map.mp hwA with ⟨a, _, rfl⟩
        exact Finset.disjoint_left.mp hR_disj hwR a.2
      rw [Finset.card_union_of_disjoint hd, Finset.card_map, A.2, hRcard]; omega⟩
  refine rho_le_of_embedding emb ?_ ?_
  · intro A₁ A₂ heq
    have hset := congr_arg Subtype.val heq
    ext a
    have haR : a.1 ∉ R := fun h => Finset.disjoint_left.mp hR_disj h a.2
    have := Finset.ext_iff.mp hset a.1
    simpa [emb, haR] using this
  · intro A₁ A₂ ⟨u, v, hu1, hu2, hv2, hv1, huv, herase⟩
    have huR : u.1 ∉ R := fun h => Finset.disjoint_left.mp hR_disj h u.2
    have hvR : v.1 ∉ R := fun h => Finset.disjoint_left.mp hR_disj h v.2
    refine ⟨u.1, v.1, by simp [emb, hu1], by simp [emb, hu2, huR],
      by simp [emb, hv2], by simp [emb, hv1, hvR], huv, ?_⟩
    ext w
    simp only [emb, Finset.mem_erase, Finset.mem_union, Finset.mem_map,
      Function.Embedding.coeFn_mk, Subtype.exists]
    by_cases hwR : w ∈ R
    · have hwu : w ≠ u.1 := fun h => huR (h ▸ hwR)
      have hwv : w ≠ v.1 := fun h => hvR (h ▸ hwR)
      simp [hwR, hwu, hwv]
    · by_cases hwH : w ∈ H
      · have h1 := Finset.ext_iff.mp herase ⟨w, hwH⟩
        simpa [hwR, hwH, Subtype.ext_iff] using h1
      · simp [hwR, hwH]

/-- Two nontrivial components force `ρ(F₂(G)) > ρ(G)` via Cartesian product embedding
`G₁ □ G₂ ↪ F₂(G)`. -/
private lemma two_nontrivial_components_rho_F2_gt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H₁ H₂ : Finset V) (hdisj : Disjoint H₁ H₂)
    (_hclosed : ∀ u v : V, G.Adj u v → (u ∈ H₁ ↔ v ∈ H₁))
    (h1_rho : lapSpectralRadius (G.induce (H₁ : Set V)) = lapSpectralRadius G)
    (h2_edge : ∃ a b : V, a ∈ H₂ ∧ b ∈ H₂ ∧ G.Adj a b) :
    lapSpectralRadius G < lapSpectralRadius (tokenGraph G 2) := by
  classical
  let : Nonempty ↥(H₁ : Set V) := by
    by_contra h
    have h0 : lapSpectralRadius (G.induce (H₁ : Set V)) = 0 := by
      unfold lapSpectralRadius; rw [dif_neg h]
    rcases h2_edge with ⟨a, b, _, _, hab⟩
    have hpos := rho_pos_of_edge G hab
    linarith
  let : Nonempty ↥(H₂ : Set V) := by
    rcases h2_edge with ⟨a, _, ha, _, _⟩; exact ⟨⟨a, ha⟩⟩
  obtain ⟨x₁, hx1_ne, hx1_eig⟩ := exists_top_eigenvector (G.induce (H₁ : Set V))
  obtain ⟨x₂, hx2_ne, hx2_eig⟩ := exists_top_eigenvector (G.induce (H₂ : Set V))
  have hrho2_pos : 0 < lapSpectralRadius (G.induce (H₂ : Set V)) := by
    rcases h2_edge with ⟨a, b, ha, hb, hab⟩
    exact rho_pos_of_edge (G.induce (H₂ : Set V)) (u := ⟨a, ha⟩) (v := ⟨b, hb⟩) hab
  -- Embed `H₁ × H₂` into `TokenVertex V 2` via `(a, b) ↦ {a.1, b.1}` and take tensor product `x₁ ⊗ x₂`!
  have hne_pair : ∀ (a : ↥(H₁ : Set V)) (b : ↥(H₂ : Set V)), a.1 ≠ b.1 :=
    fun a b h => Finset.disjoint_left.mp hdisj a.2 (h ▸ b.2)
  let phi : ↥(H₁ : Set V) × ↥(H₂ : Set V) → TokenVertex V 2 :=
    fun p => mkTok2 p.1.1 p.2.1 (hne_pair p.1 p.2)
  have hphi_inj : Function.Injective phi := by
    intro p₁ p₂ h
    have hset : ({p₁.1.1, p₁.2.1} : Finset V) = {p₂.1.1, p₂.2.1} := congr_arg Subtype.val h
    have h1 : p₁.1.1 ∈ ({p₂.1.1, p₂.2.1} : Finset V) := hset ▸ Finset.mem_insert_self _ _
    have h2 : p₁.2.1 ∈ ({p₂.1.1, p₂.2.1} : Finset V) := hset ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h11 | h12
    · rcases h2 with h21 | h22
      · exact absurd (h11.trans h21.symm) (hne_pair p₁.1 p₁.2)
      · exact Prod.ext (Subtype.ext h11) (Subtype.ext h22)
    · exact absurd h12 (hne_pair p₁.1 p₂.2)
  let f : TokenVertex V 2 → ℝ := fun T =>
    if h : ∃ p : ↥(H₁ : Set V) × ↥(H₂ : Set V), phi p = T then x₁ h.choose.1 * x₂ h.choose.2 else 0
  have hf_phi : ∀ a b, f (phi (a, b)) = x₁ a * x₂ b := by
    intro a b
    have hex : ∃ p, phi p = phi (a, b) := ⟨(a, b), rfl⟩
    dsimp only [f]; rw [dif_pos hex]
    have heq := hphi_inj hex.choose_spec
    rw [heq]
  have hf_norm : f ⬝ᵥ f = (x₁ ⬝ᵥ x₁) * (x₂ ⬝ᵥ x₂) := by
    unfold dotProduct
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image phi))]
    · rw [Finset.sum_image (fun a _ b _ h => hphi_inj h), ← Finset.univ_product_univ, Finset.sum_product]
      calc ∑ a : ↥(H₁ : Set V), ∑ b : ↥(H₂ : Set V), f (phi (a, b)) * f (phi (a, b))
          = ∑ a : ↥(H₁ : Set V), (x₁ a * x₁ a) * ∑ b : ↥(H₂ : Set V), (x₂ b * x₂ b) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by rw [hf_phi]; ring
        _ = (∑ a : ↥(H₁ : Set V), x₁ a * x₁ a) * (∑ b : ↥(H₂ : Set V), x₂ b * x₂ b) := by
            rw [← Finset.sum_mul]
    · intro T _ hT
      dsimp only [f]
      have hnot : ¬ ∃ p, phi p = T := by
        rintro ⟨p, rfl⟩; exact hT (Finset.mem_image_of_mem _ (Finset.mem_univ p))
      rw [dif_neg hnot, mul_zero]
  -- Disjoint horizontal and vertical edge sums inside `F₂(G)` give
  -- `lapQuad (F₂(G)) f ≥ (ρ(H₁) + ρ(H₂)) * (x₁ ⬝ᵥ x₁) * (x₂ ⬝ᵥ x₂)`!
  let E1 : Finset (TokenVertex V 2 × TokenVertex V 2) :=
    ((Finset.univ.filter fun p : ↥(H₁ : Set V) × ↥(H₁ : Set V) => G.Adj p.1.1 p.2.1) ×ˢ
      (Finset.univ : Finset ↥(H₂ : Set V))).image fun q => (phi (q.1.1, q.2), phi (q.1.2, q.2))
  let E2 : Finset (TokenVertex V 2 × TokenVertex V 2) :=
    ((Finset.univ : Finset ↥(H₁ : Set V)) ×ˢ
      (Finset.univ.filter fun p : ↥(H₂ : Set V) × ↥(H₂ : Set V) => G.Adj p.1.1 p.2.1)).image fun q =>
        (phi (q.1, q.2.1), phi (q.1, q.2.2))
  have hE12_disj : Disjoint E1 E2 := by
    rw [Finset.disjoint_left]; intro q h1 h2
    rcases Finset.mem_image.mp h1 with ⟨⟨⟨a₁, a₂⟩, b⟩, hmem1, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨⟨a, ⟨b₁, b₂⟩⟩, hmem2, heq⟩
    have hA := hphi_inj (congr_arg Prod.fst heq)
    have hB := hphi_inj (congr_arg Prod.snd heq)
    have ha_eq : a₁ = a₂ := (congr_arg Prod.fst hA).symm.trans (congr_arg Prod.fst hB)
    have hadj : G.Adj a₁.1 a₂.1 := (Finset.mem_filter.mp (Finset.mem_product.mp hmem1).1).2
    exact G.loopless.irrefl a₁.1 (ha_eq ▸ hadj)
  let term : TokenVertex V 2 × TokenVertex V 2 → ℝ := fun q =>
    if (tokenGraph G 2).Adj q.1 q.2 then (f q.1 - f q.2) ^ 2 else 0
  have hsum_E1 : ∑ q ∈ E1, term q = 2 * lapQuad (G.induce (H₁ : Set V)) x₁ * (x₂ ⬝ᵥ x₂) := by
    have hinj1 : Function.Injective (fun q : (↥(H₁ : Set V) × ↥(H₁ : Set V)) × ↥(H₂ : Set V) =>
        (phi (q.1.1, q.2), phi (q.1.2, q.2))) := by
      intro q₁ q₂ h
      have hA := Prod.mk.inj (hphi_inj (congr_arg Prod.fst h))
      have hB := Prod.mk.inj (hphi_inj (congr_arg Prod.snd h))
      exact Prod.ext (Prod.ext hA.1 hB.1) hA.2
    dsimp only [E1]
    rw [Finset.sum_image (fun a _ b _ h => hinj1 h), Finset.sum_product]
    have hstep : ∀ p ∈ Finset.univ.filter (fun p : ↥(H₁ : Set V) × ↥(H₁ : Set V) => G.Adj p.1.1 p.2.1),
        (∑ b : ↥(H₂ : Set V), term (phi (p.1, b), phi (p.2, b))) =
        (x₁ p.1 - x₁ p.2) ^ 2 * (x₂ ⬝ᵥ x₂) := by
      intro p hp
      have hadj : G.Adj p.1.1 p.2.1 := (Finset.mem_filter.mp hp).2
      have hcongr : ∀ b ∈ (Finset.univ : Finset ↥(H₂ : Set V)),
          term (phi (p.1, b), phi (p.2, b)) = (x₁ p.1 - x₁ p.2) ^ 2 * (x₂ b * x₂ b) := by
        intro b _
        dsimp only [term]
        rw [if_pos (mkTok2_adj_left (hne_pair p.1 b) (hne_pair p.2 b) hadj), hf_phi, hf_phi]; ring
      rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum]; rfl
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, Finset.sum_filter,
      ← Finset.univ_product_univ, Finset.sum_product]
    have hq1 := lapQuad_eq_sum_sq (G.induce (H₁ : Set V)) x₁
    simp only [SimpleGraph.induce_adj] at hq1
    have : (∑ a : ↥(H₁ : Set V), ∑ b : ↥(H₁ : Set V), if G.Adj a.1 b.1 then (x₁ a - x₁ b) ^ 2 else 0) =
        2 * lapQuad (G.induce (H₁ : Set V)) x₁ := by
      linarith
    rw [this]
  have hsum_E2 : ∑ q ∈ E2, term q = 2 * (x₁ ⬝ᵥ x₁) * lapQuad (G.induce (H₂ : Set V)) x₂ := by
    have hinj2 : Function.Injective (fun q : ↥(H₁ : Set V) × (↥(H₂ : Set V) × ↥(H₂ : Set V)) =>
        (phi (q.1, q.2.1), phi (q.1, q.2.2))) := by
      intro q₁ q₂ h
      have hA := Prod.mk.inj (hphi_inj (congr_arg Prod.fst h))
      have hB := Prod.mk.inj (hphi_inj (congr_arg Prod.snd h))
      exact Prod.ext hA.1 (Prod.ext hA.2 hB.2)
    dsimp only [E2]
    rw [Finset.sum_image (fun a _ b _ h => hinj2 h), Finset.sum_product]
    have hstep : ∀ a ∈ (Finset.univ : Finset ↥(H₁ : Set V)),
        (∑ p ∈ Finset.univ.filter (fun p : ↥(H₂ : Set V) × ↥(H₂ : Set V) => G.Adj p.1.1 p.2.1),
          term (phi (a, p.1), phi (a, p.2))) =
        (x₁ a * x₁ a) * (2 * lapQuad (G.induce (H₂ : Set V)) x₂) := by
      intro a _
      have hcongr : ∀ p ∈ Finset.univ.filter (fun p : ↥(H₂ : Set V) × ↥(H₂ : Set V) => G.Adj p.1.1 p.2.1),
          term (phi (a, p.1), phi (a, p.2)) = (x₁ a * x₁ a) * (x₂ p.1 - x₂ p.2) ^ 2 := by
        intro p hp
        have hadj : G.Adj p.1.1 p.2.1 := (Finset.mem_filter.mp hp).2
        dsimp only [term]
        rw [if_pos (mkTok2_adj_right (hne_pair a p.1) (hne_pair a p.2) hadj), hf_phi, hf_phi]; ring
      rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum, Finset.sum_filter,
        ← Finset.univ_product_univ, Finset.sum_product]
      have hq2 := lapQuad_eq_sum_sq (G.induce (H₂ : Set V)) x₂
      simp only [SimpleGraph.induce_adj] at hq2
      congr 1; linarith
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]; unfold dotProduct; ring
  have hsum_tot : ∑ q ∈ E1 ∪ E2, term q ≤
      ∑ A : TokenVertex V 2, ∑ B : TokenVertex V 2, term (A, B) := by
    rw [show (∑ A : TokenVertex V 2, ∑ B : TokenVertex V 2, term (A, B)) =
      ∑ q ∈ (Finset.univ : Finset (TokenVertex V 2 × TokenVertex V 2)), term q by
        rw [← Finset.univ_product_univ, Finset.sum_product]]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun q _ _ => by
      dsimp only [term]; positivity
  rw [Finset.sum_union hE12_disj, hsum_E1, hsum_E2] at hsum_tot
  have hq1_eq : lapQuad (G.induce (H₁ : Set V)) x₁ = lapSpectralRadius G * (x₁ ⬝ᵥ x₁) := by
    unfold lapQuad; rw [hx1_eig, h1_rho, dotProduct_smul, smul_eq_mul]
  have hq2_eq : lapQuad (G.induce (H₂ : Set V)) x₂ =
      lapSpectralRadius (G.induce (H₂ : Set V)) * (x₂ ⬝ᵥ x₂) := by
    unfold lapQuad; rw [hx2_eig, dotProduct_smul, smul_eq_mul]
  have hpos1 : 0 < x₁ ⬝ᵥ x₁ := dotProduct_self_pos hx1_ne
  have hpos2 : 0 < x₂ ⬝ᵥ x₂ := dotProduct_self_pos hx2_ne
  refine lt_rho_of_rayleigh (tokenGraph G 2) (f := f) ?_
  rw [lapQuad_eq_sum_sq, hf_norm]
  rw [hq1_eq, hq2_eq] at hsum_tot
  have hstrict : lapSpectralRadius G * ((x₁ ⬝ᵥ x₁) * (x₂ ⬝ᵥ x₂)) <
      (lapSpectralRadius G + lapSpectralRadius (G.induce (H₂ : Set V))) *
        ((x₁ ⬝ᵥ x₁) * (x₂ ⬝ᵥ x₂)) := by
    nlinarith [mul_pos hpos1 hpos2]
  linarith

private lemma card_coe_set {V : Type*} [DecidableEq V] (H : Finset V) :
    Fintype.card ↥(H : Set V) = H.card := by
  simp

/-- **Theorem 2 (Complete Equality Characterization for All Graphs of Order `n ≥ 4`):**
For any graph `G` on `n ≥ 4` vertices, `ρ(F_k(G)) = ρ(G)` for all `2 ≤ k ≤ ⌊n / 2⌋`
if and only if `G` is edgeless, `S_m ∪ (n - m)K_1` (`m ≥ 2`), or `K_3 ∪ (n - 3)K_1`. -/
theorem all_graphs_equality_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 4 ≤ Fintype.card V) :
    (∀ k : ℕ, 2 ≤ k → k ≤ Fintype.card V / 2 →
      lapSpectralRadius (tokenGraph G k) = lapSpectralRadius G) ↔ IsEqualityGraph G := by
  classical
  constructor
  · intro hall
    have heq2 : lapSpectralRadius (tokenGraph G 2) = lapSpectralRadius G :=
      hall 2 le_rfl (by omega)
    by_cases hedge : ∃ a b : V, G.Adj a b
    · -- Look at the set of non-isolated vertices `Act = {v | ∃ w, G.Adj v w}` and pick a
      -- connected component `H₁` maximizing `ρ(G[H])`!
      -- Wait: every component `C` has `H_C = Finset.univ.filter (fun v => G.Reachable c v)`.
      -- Check if all edges lie in a SINGLE connected component `H`:
      rcases hedge with ⟨a₀, b₀, ha₀b₀⟩
      -- Pick a vertex `u₀` whose component `C₀` has maximal `ρ` among all components!
      let comp : V → Finset V := fun u => Finset.univ.filter (fun v => G.Reachable u v)
      have hcomp_closed : ∀ u x y : V, G.Adj x y → (x ∈ comp u ↔ y ∈ comp u) := by
        intro u x y hxy
        simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.trans hxy.reachable, fun h => h.trans hxy.symm.reachable⟩
      have hcomp_disj : ∀ u v : V, v ∉ comp u → Disjoint (comp u) (comp v) := by
        intro u v hv
        rw [Finset.disjoint_left]; intro w hwu hwv
        simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and] at hwu hwv hv
        exact hv (hwu.trans hwv.symm)
      have hcomp_conn : ∀ u : V, (G.induce (comp u : Set V)).Connected := by
        intro u
        have hu_mem : u ∈ comp u := Finset.mem_filter.mpr ⟨Finset.mem_univ u, SimpleGraph.Reachable.refl u⟩
        have hreach : ∀ v : ↥(comp u : Set V), (G.induce (comp u : Set V)).Reachable ⟨u, hu_mem⟩ v := by
          rintro ⟨v, hv⟩
          have huv : G.Reachable u v := (Finset.mem_filter.mp hv).2
          rcases huv with ⟨w⟩
          have lift : ∀ {x y : V} (hx : x ∈ comp u) (walk : G.Walk x y),
              (G.induce (comp u : Set V)).Reachable ⟨x, hx⟩
                ⟨y, by
                  have h1 : G.Reachable u x := (Finset.mem_filter.mp hx).2
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, h1.trans walk.reachable⟩⟩ := by
            intro x y hx walk
            induction walk with
            | nil => exact SimpleGraph.Reachable.refl _
            | @cons x₁ x₂ x₃ hadj w' ih =>
              have hx₂ : x₂ ∈ comp u := (hcomp_closed u x₁ x₂ hadj).mp hx
              have hstep : (G.induce (comp u : Set V)).Adj ⟨x₁, hx⟩ ⟨x₂, hx₂⟩ := hadj
              exact hstep.reachable.trans (ih hx₂)
          exact lift hu_mem w
        let : Nonempty ↥(comp u : Set V) := ⟨⟨u, hu_mem⟩⟩
        exact ⟨fun x y => (hreach x).symm.trans (hreach y)⟩
      -- Pick a component `H = comp u*` achieving `lapSpectralRadius (G.induce H) = lapSpectralRadius G`!
      have htop_comp : ∃ u₀ : V, lapSpectralRadius (G.induce (comp u₀ : Set V)) = lapSpectralRadius G := by
        let : Nonempty V := ⟨a₀⟩
        obtain ⟨x, hx0, hxeig⟩ := exists_top_eigenvector G
        have hex_u : ∃ u₀ : V, x u₀ ≠ 0 := by
          by_contra h; push Not at h; exact hx0 (funext h)
        rcases hex_u with ⟨u₀, hu₀⟩
        refine ⟨u₀, le_antisymm
          (rho_le_of_embedding Subtype.val Subtype.val_injective (fun _ _ h => h)) ?_⟩
        -- Restriction of eigenvector `x` to `comp u₀` is an eigenvector of `G.induce (comp u₀)` with eigenvalue `ρ(G)`!
        let xC : ↥(comp u₀ : Set V) → ℝ := fun w => x w.1
        have hxC_ne : xC ≠ 0 := by
          intro h0
          have hu₀_mem : u₀ ∈ comp u₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩
          exact hu₀ (congr_fun h0 ⟨u₀, hu₀_mem⟩)
        have hxC_eig : (G.induce (comp u₀ : Set V)).lapMatrix ℝ *ᵥ xC = lapSpectralRadius G • xC := by
          ext ⟨w, hw⟩
          have h1 := congr_fun hxeig w
          simp only [Pi.smul_apply, smul_eq_mul, SimpleGraph.lapMatrix_mulVec_apply] at h1 ⊢
          have hnb_eq : ((G.induce (comp u₀ : Set V)).neighborFinset ⟨w, hw⟩).map
              ⟨Subtype.val, Subtype.val_injective⟩ = G.neighborFinset w := by
            ext z
            simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Function.Embedding.coeFn_mk,
              Subtype.exists]
            constructor
            · rintro ⟨y, _, hyw, rfl⟩; exact hyw
            · intro hwz; exact ⟨z, (hcomp_closed u₀ w z hwz).mp hw, hwz, rfl⟩
          have hdeg_eq : (G.induce (comp u₀ : Set V)).degree ⟨w, hw⟩ = G.degree w := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
              ← hnb_eq, Finset.card_map]
          have hsum_eq : ∑ z ∈ (G.induce (comp u₀ : Set V)).neighborFinset ⟨w, hw⟩, xC z =
              ∑ z ∈ G.neighborFinset w, x z := by
            rw [← hnb_eq, Finset.sum_map]; rfl
          rw [hdeg_eq, hsum_eq]
          exact h1
        refine le_rho_of_rayleigh (G.induce (comp u₀ : Set V)) hxC_ne ?_
        unfold lapQuad; rw [hxC_eig, dotProduct_smul, smul_eq_mul]
      rcases htop_comp with ⟨u₀, hu₀_rho⟩
      set H : Finset V := comp u₀
      -- Every edge of `G` MUST lie in `H`; otherwise there is a second nontrivial component!
      have hall_in_H : ∀ x y : V, G.Adj x y → x ∈ H ∧ y ∈ H := by
        intro x y hxy
        by_contra hnot
        have hx_notH : x ∉ H := by
          intro hxH; exact hnot ⟨hxH, (hcomp_closed u₀ x y hxy).mp hxH⟩
        have hlt := two_nontrivial_components_rho_F2_gt G H (comp x)
          (hcomp_disj u₀ x hx_notH) (hcomp_closed u₀) hu₀_rho
          ⟨x, y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.reachable⟩, hxy⟩
        linarith
      have hH_ge2 : 2 ≤ H.card := by
        have h1 := hall_in_H a₀ b₀ ha₀b₀
        have hsub : ({a₀, b₀} : Finset V) ⊆ H := by
          intro w hw; simp at hw; rcases hw with rfl | rfl <;> [exact h1.1; exact h1.2]
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair (G.ne_of_adj ha₀b₀)] at this
      have hH_conn : (G.induce (H : Set V)).Connected := hcomp_conn u₀
      by_cases hH4 : 4 ≤ H.card
      · -- `|H| ≥ 4`: `G[H]` MUST be a star, else `ρ(F₂(G)) ≥ ρ(F₂(G[H])) > ρ(G[H]) = ρ(G)`!
        have hstarH : IsStar (G.induce (H : Set V)) := by
          by_contra hnotstar
          have hcardH : 4 ≤ Fintype.card ↥(H : Set V) := by rw [card_coe_set]; exact hH4
          have hlt := connected_nonstar_rho_F2_gt (G.induce (H : Set V)) hcardH hH_conn hnotstar
          have hge := rho_tokenGraph_active_subset_ge G H 2 2 le_rfl (by omega)
          linarith
        exact Or.inr (Or.inl ⟨H, hH_ge2, hall_in_H, hstarH⟩)
      · -- `|H| = 2` or `|H| = 3`: connected graph on 2 vertices is `S_2`, on 3 vertices is `S_3` or `K_3`!
        have hH23 : H.card = 2 ∨ H.card = 3 := by omega
        rcases hH23 with hH2 | hH3
        · -- `|H| = 2` and connected ⇒ `S_2`!
          obtain ⟨a, b, hab, hHab⟩ := Finset.card_eq_two.mp hH2
          have hadj_ab : G.Adj a b := by
            have h1 := hall_in_H a₀ b₀ ha₀b₀
            rw [hHab] at h1
            simp only [Finset.mem_insert, Finset.mem_singleton] at h1
            rcases h1 with ⟨rfl | rfl, rfl | rfl⟩
            · exact absurd rfl (G.ne_of_adj ha₀b₀)
            · exact ha₀b₀
            · exact ha₀b₀.symm
            · exact absurd rfl (G.ne_of_adj ha₀b₀)
          have hall_ab : ∀ x y : V, G.Adj x y → x ∈ ({a, b} : Finset V) ∧ y ∈ ({a, b} : Finset V) := by
            intro x y hxy; rw [← hHab]; exact hall_in_H x y hxy
          refine Or.inr (Or.inl ⟨{a, b}, by rw [Finset.card_pair hab], hall_ab, ?_⟩)
          refine ⟨⟨a, by simp⟩, fun u v => ?_⟩
          have hu := u.2; have hv := v.2
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
          constructor
          · intro huv
            rcases hu with hua | hub <;> rcases hv with hva | hvb
            · exact absurd (hua.trans hva.symm) (G.ne_of_adj huv)
            · exact Or.inl ⟨Subtype.ext hua, fun h => hab (hvb.symm.trans (congr_arg Subtype.val h)).symm⟩
            · exact Or.inr ⟨Subtype.ext hva, fun h => hab (hub.symm.trans (congr_arg Subtype.val h)).symm⟩
            · exact absurd (hub.trans hvb.symm) (G.ne_of_adj huv)
          · rintro (⟨hu1, hv1⟩ | ⟨hv1, hu1⟩)
            · have hua : u.1 = a := congr_arg Subtype.val hu1
              have hvb : v.1 = b := by
                rcases hv with hva | hvb
                · exact absurd (Subtype.ext hva) hv1
                · exact hvb
              show G.Adj u.1 v.1; rw [hua, hvb]; exact hadj_ab
            · have hva : v.1 = a := congr_arg Subtype.val hv1
              have hub : u.1 = b := by
                rcases hu with hua | hub
                · exact absurd (Subtype.ext hua) hu1
                · exact hub
              show G.Adj u.1 v.1; rw [hub, hva]; exact hadj_ab.symm
        · -- `|H| = 3` and connected: either complete (`K_3`) or has a missing edge (hence a star `S_3`)!
          by_cases hcomp3 : ∀ u v : V, u ∈ H → v ∈ H → u ≠ v → G.Adj u v
          · exact Or.inr (Or.inr ⟨H, hH3, hall_in_H, hcomp3⟩)
          · push Not at hcomp3
            rcases hcomp3 with ⟨p, q, hpH, hqH, hpq_ne, hnotpq⟩
            -- Pick the 3rd vertex `c ∈ H \ {p, q}`; since `G[H]` is connected, `c` must be adjacent to both `p` and `q`!
            have hcard_er : (H.erase p |>.erase q).card = 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hpq_ne.symm, hqH⟩),
                Finset.card_erase_of_mem hpH, hH3]
            obtain ⟨c, hc_eq⟩ := Finset.card_eq_one.mp hcard_er
            have hc_mem : c ∈ (H.erase p).erase q := hc_eq ▸ Finset.mem_singleton_self c
            have hcq : c ≠ q := (Finset.mem_erase.mp hc_mem).1
            have hcp : c ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hc_mem).2).1
            have hcH : c ∈ H := (Finset.mem_erase.mp (Finset.mem_erase.mp hc_mem).2).2
            have hH_eq : H = {c, p, q} := by
              ext w
              simp only [Finset.mem_insert, Finset.mem_singleton]
              constructor
              · intro hwH
                by_cases hwp : w = p
                · exact Or.inr (Or.inl hwp)
                · by_cases hwq : w = q
                  · exact Or.inr (Or.inr hwq)
                  · left
                    have : w ∈ (H.erase p).erase q := Finset.mem_erase.mpr ⟨hwq, Finset.mem_erase.mpr ⟨hwp, hwH⟩⟩
                    rw [hc_eq, Finset.mem_singleton] at this; exact this
              · rintro (rfl | rfl | rfl) <;> assumption
            have hcp_adj : G.Adj c p := by
              rcases hH_conn ⟨p, hpH⟩ ⟨q, hqH⟩ with ⟨w⟩
              cases w with
              | nil => exact absurd rfl hpq_ne
              | @cons _ w1 _ hadj _ =>
                have hadj' : G.Adj p w1.1 := hadj
                have hw1 : w1.1 ∈ ({c, p, q} : Finset V) := by rw [← hH_eq]; exact w1.2
                simp only [Finset.mem_insert, Finset.mem_singleton] at hw1
                rcases hw1 with h1 | h1 | h1
                · exact (h1 ▸ hadj').symm
                · exact absurd h1.symm (G.ne_of_adj hadj')
                · exact absurd (h1 ▸ hadj') hnotpq
            have hcq_adj : G.Adj c q := by
              rcases hH_conn ⟨q, hqH⟩ ⟨p, hpH⟩ with ⟨w⟩
              cases w with
              | nil => exact absurd rfl hpq_ne.symm
              | @cons _ w1 _ hadj _ =>
                have hadj' : G.Adj q w1.1 := hadj
                have hw1 : w1.1 ∈ ({c, p, q} : Finset V) := by rw [← hH_eq]; exact w1.2
                simp only [Finset.mem_insert, Finset.mem_singleton] at hw1
                rcases hw1 with h1 | h1 | h1
                · exact (h1 ▸ hadj').symm
                · exact absurd (h1 ▸ hadj').symm hnotpq
                · exact absurd h1.symm (G.ne_of_adj hadj')
            refine Or.inr (Or.inl ⟨H, by omega, hall_in_H, ⟨⟨c, hcH⟩, fun u v => ?_⟩⟩)
            have hu : u.1 ∈ ({c, p, q} : Finset V) := hH_eq ▸ u.2
            have hv : v.1 ∈ ({c, p, q} : Finset V) := hH_eq ▸ v.2
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
            constructor
            · intro huv
              rcases hu with h1 | h1 | h1 <;> rcases hv with h2 | h2 | h2
              · exact absurd (h1.trans h2.symm) (G.ne_of_adj huv)
              · exact Or.inl ⟨Subtype.ext h1, fun h => hcp (h2.symm.trans (congr_arg Subtype.val h)).symm⟩
              · exact Or.inl ⟨Subtype.ext h1, fun h => hcq (h2.symm.trans (congr_arg Subtype.val h)).symm⟩
              · exact Or.inr ⟨Subtype.ext h2, fun h => hcp (h1.symm.trans (congr_arg Subtype.val h)).symm⟩
              · exact absurd (h1.trans h2.symm) (G.ne_of_adj huv)
              · exact absurd (show G.Adj p q by rw [← h1, ← h2]; exact huv) hnotpq
              · exact Or.inr ⟨Subtype.ext h2, fun h => hcq (h1.symm.trans (congr_arg Subtype.val h)).symm⟩
              · exact absurd (show G.Adj p q by rw [← h2, ← h1]; exact huv.symm) hnotpq
              · exact absurd (h1.trans h2.symm) (G.ne_of_adj huv)
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · have hu1 : u.1 = c := congr_arg Subtype.val h1
                rcases hv with hv1 | hv1 | hv1
                · exact absurd (Subtype.ext hv1) h2
                · show G.Adj u.1 v.1; rw [hu1, hv1]; exact hcp_adj
                · show G.Adj u.1 v.1; rw [hu1, hv1]; exact hcq_adj
              · have hv1 : v.1 = c := congr_arg Subtype.val h1
                rcases hu with hu1 | hu1 | hu1
                · exact absurd (Subtype.ext hu1) h2
                · show G.Adj u.1 v.1; rw [hu1, hv1]; exact hcp_adj.symm
                · show G.Adj u.1 v.1; rw [hu1, hv1]; exact hcq_adj.symm
    · -- No edges: edgeless graph!
      push Not at hedge
      exact Or.inl hedge
  · -- Converse: every graph in `IsEqualityGraph G` satisfies `ρ(F_k(G)) = ρ(G)` for all `2 ≤ k ≤ ⌊n / 2⌋`.
    rintro (hno | ⟨H, hH2, hact, hstarH⟩ | ⟨H, hH3, hact, hcomp3⟩) k hk2 hkn
    · -- Edgeless:
      rw [rho_edgeless G hno]
      refine rho_edgeless (tokenGraph G k) ?_
      rintro S T ⟨u, v, _, _, _, _, huv, _⟩
      exact hno u v huv
    · -- `S_m ∪ (n - m)K_1` (`m = H.card ≥ 2`):
      have hrhoG : lapSpectralRadius G = (H.card : ℝ) := by
        rw [rho_of_active_subset G H hact, rho_star (G.induce (H : Set V)) hstarH (by rw [card_coe_set]; exact hH2),
          card_coe_set]
      rw [hrhoG]
      have hle : lapSpectralRadius (tokenGraph G k) ≤ (H.card : ℝ) := by
        refine rho_tokenGraph_active_subset_le G H hact k (H.card : ℝ) (by positivity) fun j hj1 hjH => ?_
        rw [rho_tokenGraph_star (G.induce (H : Set V)) hstarH j hj1 (by rw [card_coe_set]; exact hjH),
          card_coe_set]
      have hge : (H.card : ℝ) ≤ lapSpectralRadius (tokenGraph G k) := by
        -- Pick `j = min k (H.card - 1)`: then `1 ≤ j ≤ k`, `j < H.card`, and `k - j ≤ n - H.card`!
        set j := min k (H.card - 1)
        have hcomp_card : (Finset.univ \ H).card = Fintype.card V - H.card := by
          rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
        have hkj : k - j ≤ (Finset.univ \ H).card := by
          rw [hcomp_card]
          have hHle : H.card ≤ Fintype.card V := by
            rw [← Finset.card_univ]; exact Finset.card_le_univ H
          omega
        have hsub := rho_tokenGraph_active_subset_ge G H k j (min_le_left _ _) hkj
        rw [rho_tokenGraph_star (G.induce (H : Set V)) hstarH j (by omega)
          (by rw [card_coe_set]; omega), card_coe_set] at hsub
        exact hsub
      exact le_antisymm hle hge
    · -- `K_3 ∪ (n - 3)K_1`:
      have htop : ∀ u v : ↥(H : Set V), u ≠ v → (G.induce (H : Set V)).Adj u v :=
        fun u v hne => hcomp3 u.1 v.1 u.2 v.2 (fun h => hne (Subtype.ext h))
      have hrhoG : lapSpectralRadius G = 3 := by
        rw [rho_of_active_subset G H hact,
          rho_K3 (G.induce (H : Set V)) (by rw [card_coe_set]; exact hH3) htop]
      rw [hrhoG]
      have hle : lapSpectralRadius (tokenGraph G k) ≤ 3 := by
        refine rho_tokenGraph_active_subset_le G H hact k 3 (by norm_num) fun j hj1 hjH => ?_
        rw [rho_tokenGraph_K3 (G.induce (H : Set V)) (by rw [card_coe_set]; exact hH3) htop j hj1 (by omega)]
      have hge : (3 : ℝ) ≤ lapSpectralRadius (tokenGraph G k) := by
        -- Pick `j = 2`: `2 ≤ k` and `k - 2 ≤ n - 3` (since `k ≤ n / 2` and `n ≥ 4`)!
        have hcomp_card : (Finset.univ \ H).card = Fintype.card V - 3 := by
          rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hH3]
        have hsub := rho_tokenGraph_active_subset_ge G H k 2 hk2 (by rw [hcomp_card]; omega)
        rw [rho_tokenGraph_K3 (G.induce (H : Set V)) (by rw [card_coe_set]; exact hH3) htop 2 (by omega) le_rfl] at hsub
        exact hsub
      exact le_antisymm hle hge

end SongDalfoFiolZhangTokenLaplacian
