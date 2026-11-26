import Mathlib

/-!
# Proof That the Path Uniquely Maximizes the Tree Hitting-Time Index

This module proves the conjecture of Palacios, Tamura, Wiberg, and Petojević
(*The hitting time index: bounds, a sharp threshold, the proof of a conjecture and
the disproof of another conjecture*, arXiv:2611.34295v1, §3, p. 10) that among all
finite trees `T` on `n ≥ 1` vertices, the path `P_n` uniquely maximizes the
hitting-time index `HT(T) = ∑_{x < y} max(H(x, y), H(y, x))`.

## Main Theorems

* `hitTime_satisfies_first_step` and `first_step_unique`: on any finite tree `T` of
  order `n ≥ 2`, `hitTime T x y = (n - 1) * T.dist x y + D(y) - D(x)` is the unique
  solution of the simple-random-walk first-step Markov system.
* `graft_htIndex_strict_lt`: under a valid pendant-path grafting move (`r ≥ a ≥ b ≥ 1`),
  the grafted tree has one fewer leaf and strictly larger hitting-time index.
* `palacios_tree_hitting_time_le`: for every finite tree `T` on a nonempty vertex set `V`,
  `htIndex T ≤ htIndex (pathGraph (Fintype.card V))`.
* `palacios_tree_hitting_time_eq_iff`: equality holds if and only if
  `Nonempty (T ≃g pathGraph (Fintype.card V))`.
-/

namespace PalaciosHittingTimeTrees

open SimpleGraph Finset

section Definitions

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Transmission `D(x) = ∑ z, dist(x, z)` of vertex `x` in `G`. -/
noncomputable def transmission (G : SimpleGraph V) (x : V) : ℕ :=
  ∑ z : V, G.dist x z

/-- Closed-form expected hitting time `H(x, y) = (n - 1) d(x, y) + D(y) - D(x)` on a tree. -/
noncomputable def hitTime (G : SimpleGraph V) (x y : V) : ℤ :=
  ((Fintype.card V : ℤ) - 1) * (G.dist x y : ℤ) +
    (transmission G y : ℤ) - (transmission G x : ℤ)

/-- Twice the hitting-time index: sum over all ordered pairs `(x, y)` of
`(n - 1) * dist(x, y) + |D(y) - D(x)|`. -/
noncomputable def twoHT (G : SimpleGraph V) : ℕ :=
  ∑ x : V, ∑ y : V,
    ((Fintype.card V - 1) * G.dist x y +
      Int.natAbs ((transmission G y : ℤ) - (transmission G x : ℤ)))

/-- Hitting-time index `HT(G) = ∑_{{x, y}} max(H(x, y), H(y, x))` on trees. -/
noncomputable def htIndex (G : SimpleGraph V) : ℕ :=
  twoHT G / 2

/-- Number of leaves (degree-1 vertices) in `G`. -/
noncomputable def leafCount (G : SimpleGraph V) : ℕ :=
  by classical exact (Finset.univ.filter (fun u : V => G.degree u = 1)).card

/-- The path graph `P_n` on `Fin n`. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun i h => by omega⟩

instance pathGraph_decidableRel (n : ℕ) : DecidableRel (pathGraph n).Adj :=
  fun i j => inferInstanceAs (Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val))

omit [DecidableEq V] in
lemma hitTime_max_eq (G : SimpleGraph V) (x y : V) :
    max (hitTime G x y) (hitTime G y x) =
      ((Fintype.card V : ℤ) - 1) * (G.dist x y : ℤ) +
        |(transmission G y : ℤ) - (transmission G x : ℤ)| := by
  unfold hitTime
  rw [SimpleGraph.dist_comm (u := y) (v := x)]
  have h : max ((transmission G y : ℤ) - (transmission G x : ℤ))
      ((transmission G x : ℤ) - (transmission G y : ℤ)) =
      |(transmission G y : ℤ) - (transmission G x : ℤ)| := by
    rw [abs_eq_max_neg, neg_sub]
  omega

omit [DecidableEq V] in
lemma even_twoHT (G : SimpleGraph V) : Even (twoHT G) := by
  classical
  let e := Fintype.equivFin V
  let f : Fin (Fintype.card V) → Fin (Fintype.card V) → ℕ := fun i j =>
    (Fintype.card V - 1) * G.dist (e.symm i) (e.symm j) +
      Int.natAbs ((transmission G (e.symm j) : ℤ) - (transmission G (e.symm i) : ℤ))
  have hsymm : ∀ i j, f j i = f i j := by
    intro i j
    dsimp [f]
    rw [SimpleGraph.dist_comm, ← Int.natAbs_neg, neg_sub]
  have hdiag : ∀ i, f i i = 0 := by
    intro i
    simp [f]
  have heq : twoHT G = ∑ i : Fin (Fintype.card V), ∑ j : Fin (Fintype.card V), f i j := by
    unfold twoHT
    rw [← e.symm.sum_comp]
    congr 1; ext i
    exact (e.symm.sum_comp _).symm
  rw [heq]
  let S := ∑ i : Fin (Fintype.card V), ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j
  refine ⟨S, ?_⟩
  have hsplit : ∀ i : Fin (Fintype.card V),
      ∑ j : Fin (Fintype.card V), f i j =
        (∑ j ∈ Finset.univ.filter (fun j => i < j), f i j) +
        (∑ j ∈ Finset.univ.filter (fun j => j < i), f i j) := by
    intro i
    have hpart : (Finset.univ : Finset (Fin (Fintype.card V))) =
        insert i (Finset.univ.filter (fun j => i < j) ∪
          Finset.univ.filter (fun j => j < i)) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
        true_and, true_iff]
      exact lt_trichotomy j i |>.elim (fun h => Or.inr (Or.inr h))
        (fun h => h.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
    have hni : i ∉ Finset.univ.filter (fun j => i < j) ∪
        Finset.univ.filter (fun j => j < i) := by
      simp
    have hdisj : Disjoint (Finset.univ.filter (fun j => i < j))
        (Finset.univ.filter (fun j => j < i)) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
      exact lt_asymm hj1 hj2
    conv_lhs => rw [hpart]
    rw [Finset.sum_insert hni, Finset.sum_union hdisj, hdiag, zero_add]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hswap : (∑ i : Fin (Fintype.card V), ∑ j ∈ Finset.univ.filter (fun j => j < i), f i j) = S := by
    dsimp [S]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j
    split_ifs with h
    · exact hsymm i j
    · rfl
  rw [hswap]

omit [DecidableEq V] in
lemma two_mul_htIndex (G : SimpleGraph V) : 2 * htIndex G = twoHT G := by
  obtain ⟨k, hk⟩ := even_twoHT G
  unfold htIndex
  omega

omit [DecidableEq V] in
lemma htIndex_le_iff {G H : SimpleGraph V} :
    htIndex G ≤ htIndex H ↔ twoHT G ≤ twoHT H := by
  have hG := two_mul_htIndex G
  have hH := two_mul_htIndex H
  omega

omit [DecidableEq V] in
lemma htIndex_lt_iff {G H : SimpleGraph V} :
    htIndex G < htIndex H ↔ twoHT G < twoHT H := by
  have hG := two_mul_htIndex G
  have hH := two_mul_htIndex H
  omega

lemma dist_iso {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (x y : V) :
    H.dist (e x) (e y) = G.dist x y := by
  by_cases hreach : G.Reachable x y
  · have hreachH : H.Reachable (e x) (e y) := by
      obtain ⟨p⟩ := hreach
      exact ⟨p.map e.toHom⟩
    apply le_antisymm
    · obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
      calc H.dist (e x) (e y) ≤ (p.map e.toHom).length := H.dist_le _
        _ = p.length := Walk.length_map _ _
        _ = G.dist x y := hp
    · obtain ⟨q, hq⟩ := hreachH.exists_walk_length_eq_dist
      let hq' := (q.map e.symm.toHom).copy (e.symm_apply_apply x) (e.symm_apply_apply y)
      calc G.dist x y ≤ hq'.length := G.dist_le _
        _ = q.length := by rw [Walk.length_copy, Walk.length_map]
        _ = H.dist (e x) (e y) := hq
  · have hnotH : ¬ H.Reachable (e x) (e y) := by
      rintro ⟨q⟩
      exact hreach ⟨(q.map e.symm.toHom).copy (e.symm_apply_apply x) (e.symm_apply_apply y)⟩
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hnotH,
      SimpleGraph.dist_eq_zero_of_not_reachable hreach]

lemma transmission_iso {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (x : V) :
    transmission H (e x) = transmission G x := by
  unfold transmission
  rw [← e.toEquiv.sum_comp]
  congr 1; ext z
  exact dist_iso e x z

lemma twoHT_iso {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    twoHT G = twoHT H := by
  unfold twoHT
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e.toEquiv
  rw [hcard, ← e.toEquiv.sum_comp]
  congr 1; ext x
  rw [← e.toEquiv.sum_comp]
  congr 1; ext y
  change (Fintype.card W - 1) * G.dist x y +
      Int.natAbs ((transmission G y : ℤ) - (transmission G x : ℤ)) =
    (Fintype.card W - 1) * H.dist (e x) (e y) +
      Int.natAbs ((transmission H (e y) : ℤ) - (transmission H (e x) : ℤ))
  rw [dist_iso e x y, transmission_iso e x, transmission_iso e y]

lemma htIndex_iso {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    htIndex G = htIndex H := by
  unfold htIndex
  rw [twoHT_iso e]

end Definitions

section FirstStepMarkov

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Before G z x w` means `w` is adjacent to `x` and strictly closer to `z`. -/
private def Before (G : SimpleGraph V) (z x w : V) : Prop :=
  G.Adj x w ∧ G.dist w z + 1 = G.dist x z

omit [Fintype V] [DecidableEq V] in
private lemma before_exists {G : SimpleGraph V} (hT : G.IsTree) {z x : V} (hne : x ≠ z) :
    ∃ w, Before G z x w := by
  obtain ⟨q, hq⟩ := hT.connected.exists_walk_length_eq_dist x z
  cases q with
  | nil => exact (hne rfl).elim
  | @cons _ w _ e q =>
    refine ⟨w, e, ?_⟩
    have h₁ := G.dist_le q
    have h₂ := e.diff_dist_adj (u := z)
    simp only [SimpleGraph.dist_comm (u := z)] at h₂
    simp only [Walk.length_cons] at hq
    omega

omit [Fintype V] [DecidableEq V] in
private lemma before_unique {G : SimpleGraph V} (hT : G.IsTree) {z x w₁ w₂ : V}
    (h₁ : Before G z x w₁) (h₂ : Before G z x w₂) : w₁ = w₂ := by
  obtain ⟨a, ha⟩ := hT.connected.exists_walk_length_eq_dist w₁ z
  obtain ⟨b, hb⟩ := hT.connected.exists_walk_length_eq_dist w₂ z
  have h := (hT.existsUnique_path x z).unique
    ((a.cons h₁.1).isPath_of_length_eq_dist (by simpa [ha] using h₁.2))
    ((b.cons h₂.1).isPath_of_length_eq_dist (by simpa [hb] using h₂.2))
  simpa using congrArg Walk.snd h

omit [Fintype V] [DecidableEq V] in
private lemma before_or {G : SimpleGraph V} (hT : G.IsTree) (z : V) {x y : V} (he : G.Adj x y) :
    Before G z x y ∨ Before G z y x := by
  have h := hT.dist_eq_dist_add_one_of_adj z he
  simp only [SimpleGraph.dist_comm (u := z)] at h
  exact h.imp (fun h => ⟨he, h.symm⟩) (fun h => ⟨he.symm, h.symm⟩)

omit [Fintype V] [DecidableEq V] in
private lemma dist_eq_length_of_isPath {G : SimpleGraph V} (hT : G.IsTree) {x y : V}
    {p : G.Walk x y} (hp : p.IsPath) : G.dist x y = p.length := by
  obtain ⟨q, hq⟩ := hT.connected.exists_walk_length_eq_dist x y
  have hqp : q.IsPath := q.isPath_of_length_eq_dist hq
  have heq : p = q := (hT.existsUnique_path x y).unique hp hqp
  rw [heq, hq]

/-- Lemma 2.1: For any `x ≠ z` in a finite tree, summing `dist(w, z) - dist(x, z)` over
`w ∈ N(x)` yields `deg(x) - 2`. -/
theorem sum_dist_neighbors {G : SimpleGraph V} [DecidableRel G.Adj]
    (hT : G.IsTree) {x z : V} (hxz : x ≠ z) :
    ∑ w ∈ G.neighborFinset x, ((G.dist w z : ℤ) - (G.dist x z : ℤ)) =
      (G.degree x : ℤ) - 2 := by
  obtain ⟨w₀, hw₀⟩ := before_exists hT hxz
  have hw₀_mem : w₀ ∈ G.neighborFinset x := (mem_neighborFinset G x w₀).mpr hw₀.1
  have hother : ∀ w ∈ (G.neighborFinset x).erase w₀,
      ((G.dist w z : ℤ) - (G.dist x z : ℤ)) = 1 := by
    intro w hw
    have hne : w ≠ w₀ := (Finset.mem_erase.mp hw).1
    have hadj : G.Adj x w := (mem_neighborFinset G x w).mp (Finset.mem_erase.mp hw).2
    rcases before_or hT z hadj with h1 | h2
    · exact (hne (before_unique hT h1 hw₀)).elim
    · have := h2.2
      omega
  rw [← Finset.add_sum_erase _ _ hw₀_mem, Finset.sum_congr rfl hother, Finset.sum_const,
    Finset.card_erase_of_mem hw₀_mem, G.card_neighborFinset_eq_degree]
  have hdeg1 : 1 ≤ G.degree x := by
    rw [← G.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨w₀, hw₀_mem⟩
  have h0 : ((G.dist w₀ z : ℤ) - (G.dist x z : ℤ)) = -1 := by
    have := hw₀.2; omega
  simp only [nsmul_eq_mul, mul_one]
  omega

omit [Fintype V] [DecidableEq V] in
private lemma dist_eq_one_of_adj {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    G.dist u v = 1 := by
  have hle : G.dist u v ≤ 1 := G.dist_le (Walk.cons h Walk.nil)
  have hne : G.dist u v ≠ 0 := by
    intro h0
    rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h0 with rfl | hnr
    · exact G.loopless.irrefl u h
    · exact hnr ⟨Walk.cons h Walk.nil⟩
  omega

omit [Fintype V] [DecidableEq V] in
/-- Helper for path concatenation when two paths intersect only at their shared endpoint. -/
private lemma isPath_append_of_disjoint {G : SimpleGraph V} {x y z : V}
    {p : G.Walk x y} {q : G.Walk y z} (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ u, u ∈ p.support → u ∈ q.support → u = y) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro u hu1 v hv2 heq
  subst heq
  have hu2 : u ∈ q.support := List.mem_of_mem_tail hv2
  have huy : u = y := hinter u hu1 hu2
  subst huy
  have hnd := hq.support_nodup
  cases hsup : q.support with
  | nil => exact (Walk.support_ne_nil q hsup).elim
  | cons a l =>
    have ha : a = u := by
      have := Walk.head_support q
      simp only [hsup, List.head_cons] at this
      exact this
    rw [hsup, ha] at hnd hv2
    exact (List.nodup_cons.mp hnd).1 hv2

/-- Sum of transmission differences across neighbors of `x` in any finite tree. -/
theorem sum_transmission_neighbors {G : SimpleGraph V} [DecidableRel G.Adj]
    (hT : G.IsTree) (x : V) :
    ∑ w ∈ G.neighborFinset x, ((transmission G w : ℤ) - (transmission G x : ℤ)) =
      (Fintype.card V : ℤ) * (G.degree x : ℤ) - 2 * ((Fintype.card V : ℤ) - 1) := by
  have hrew : ∀ w ∈ G.neighborFinset x,
      ((transmission G w : ℤ) - (transmission G x : ℤ)) =
        ∑ z : V, ((G.dist w z : ℤ) - (G.dist x z : ℤ)) := by
    intro w _
    unfold transmission
    push_cast
    rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl hrew, Finset.sum_comm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  have hx : ∑ w ∈ G.neighborFinset x, ((G.dist w x : ℤ) - (G.dist x x : ℤ)) =
      (G.degree x : ℤ) := by
    have h1 : ∀ w ∈ G.neighborFinset x, ((G.dist w x : ℤ) - (G.dist x x : ℤ)) = 1 := by
      intro w hw
      have hadj : G.Adj w x := ((mem_neighborFinset G x w).mp hw).symm
      have hd : G.dist w x = 1 := dist_eq_one_of_adj hadj
      simp [hd]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, G.card_neighborFinset_eq_degree]
    simp
  have hrest : ∑ z ∈ Finset.univ.erase x,
      ∑ w ∈ G.neighborFinset x, ((G.dist w z : ℤ) - (G.dist x z : ℤ)) =
      ((Fintype.card V - 1 : ℕ) : ℤ) * ((G.degree x : ℤ) - 2) := by
    have hcongr : ∀ z ∈ Finset.univ.erase x,
        ∑ w ∈ G.neighborFinset x, ((G.dist w z : ℤ) - (G.dist x z : ℤ)) =
          (G.degree x : ℤ) - 2 := by
      intro z hz
      exact sum_dist_neighbors hT (Ne.symm (Finset.mem_erase.mp hz).1)
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ]
    simp
  rw [hx, hrest]
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  have hsub : ((Fintype.card V - 1 : ℕ) : ℤ) = (Fintype.card V : ℤ) - 1 := by omega
  rw [hsub]
  ring

/-- Lemma 2.2 (Existence): On any finite tree `G`, `hitTime G · y` solves the exact
simple-random-walk first-step Markov system. -/
theorem hitTime_satisfies_first_step {G : SimpleGraph V} [DecidableRel G.Adj]
    (hT : G.IsTree) (y : V) :
    hitTime G y y = 0 ∧
      ∀ x ≠ y, (G.degree x : ℤ) * hitTime G x y =
        (G.degree x : ℤ) + ∑ w ∈ G.neighborFinset x, hitTime G w y := by
  refine ⟨by simp [hitTime], fun x hxy => ?_⟩
  have hdiff : ∑ w ∈ G.neighborFinset x, (hitTime G w y - hitTime G x y) = -(G.degree x : ℤ) := by
    have hterm : ∀ w ∈ G.neighborFinset x,
        hitTime G w y - hitTime G x y =
          ((Fintype.card V : ℤ) - 1) * ((G.dist w y : ℤ) - (G.dist x y : ℤ)) -
            ((transmission G w : ℤ) - (transmission G x : ℤ)) := by
      intro w _; unfold hitTime; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_dist_neighbors hT hxy, sum_transmission_neighbors hT x]
    ring
  rw [Finset.sum_sub_distrib, Finset.sum_const, G.card_neighborFinset_eq_degree] at hdiff
  simp only [nsmul_eq_mul] at hdiff
  linarith

/-- Helper maximum principle on a finite connected graph: a function harmonic away from `y`
with `f y = 0` satisfies `f ≤ 0`. -/
private lemma harmonic_le_zero {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : G.Connected) (y : V) (f : V → ℚ) (hy : f y = 0)
    (hharm : ∀ x ≠ y, (G.degree x : ℚ) * f x = ∑ w ∈ G.neighborFinset x, f w) :
    ∀ x, f x ≤ 0 := by
  have : Nonempty V := ⟨y⟩
  obtain ⟨x₀, _, hx₀⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  set M := f x₀
  have hleM : ∀ u : V, f u ≤ M := fun u => hx₀ u (Finset.mem_univ u)
  have hprop : ∀ {u v : V}, f u = M → u ≠ y → G.Adj u v → f v = M := by
    intro u v hu huy hadj
    have hsum : ∑ w ∈ G.neighborFinset u, (M - f w) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, G.card_neighborFinset_eq_degree,
        nsmul_eq_mul, ← hu, hharm u huy, sub_self]
    have hnn : ∀ w ∈ G.neighborFinset u, 0 ≤ M - f w := fun w _ => sub_nonneg.mpr (hleM w)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum v
      ((mem_neighborFinset G u v).mpr hadj)
    linarith
  have hwalk : ∀ {u z : V} (p : G.Walk u z), z = y → f u = M → f z = M := by
    intro u z p
    induction p with
    | nil => intro _ ha; exact ha
    | @cons a b c hadj rest ih =>
      intro hcy ha
      subst hcy
      by_cases hay : a = c
      · subst hay; exact ha
      · exact ih rfl (hprop ha hay hadj)
  obtain ⟨p⟩ := hC x₀ y
  have hM0 : M = 0 := by rw [← hy, hwalk p rfl rfl]
  intro x
  rw [← hM0]
  exact hleM x

/-- Lemma 2.2 (Uniqueness): On any finite connected graph `G`, the first-step hitting-time
system has a unique rational solution. -/
theorem first_step_unique {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : G.Connected) (y : V) (h₁ h₂ : V → ℚ)
    (hy₁ : h₁ y = 0) (hy₂ : h₂ y = 0)
    (heq₁ : ∀ x ≠ y, (G.degree x : ℚ) * h₁ x = (G.degree x : ℚ) + ∑ w ∈ G.neighborFinset x, h₁ w)
    (heq₂ : ∀ x ≠ y, (G.degree x : ℚ) * h₂ x = (G.degree x : ℚ) + ∑ w ∈ G.neighborFinset x, h₂ w) :
    h₁ = h₂ := by
  have hle : ∀ x, h₁ x - h₂ x ≤ 0 := harmonic_le_zero hC y (fun x => h₁ x - h₂ x)
    (by simp [hy₁, hy₂]) (fun x hx => by
      rw [Finset.sum_sub_distrib, mul_sub, heq₁ x hx, heq₂ x hx]; ring)
  have hge : ∀ x, h₂ x - h₁ x ≤ 0 := harmonic_le_zero hC y (fun x => h₂ x - h₁ x)
    (by simp [hy₁, hy₂]) (fun x hx => by
      rw [Finset.sum_sub_distrib, mul_sub, heq₂ x hx, heq₁ x hx]; ring)
  ext x
  linarith [hle x, hge x]

end FirstStepMarkov

section AlgebraicGraftBounds

/-! ### Elementary summation identities and strictness polynomials for the grafting move -/

private lemma sum_Icc_linear (b : ℕ) :
    2 * ∑ j ∈ Finset.Icc 1 b, (j : ℤ) = (b : ℤ) * ((b : ℤ) + 1) := by
  induction b with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), mul_add, ih]
    push_cast; ring

private lemma sum_Icc_sq (b : ℕ) :
    6 * ∑ j ∈ Finset.Icc 1 b, (j : ℤ) ^ 2 =
      (b : ℤ) * ((b : ℤ) + 1) * (2 * (b : ℤ) + 1) := by
  induction b with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), mul_add, ih]
    push_cast; ring

private lemma sum_pairs_diff (b : ℕ) :
    6 * ∑ j ∈ Finset.Icc 1 b, ∑ k ∈ Finset.Icc (j + 1) b, ((k : ℤ) - (j : ℤ)) =
      (b : ℤ) * ((b : ℤ) ^ 2 - 1) := by
  induction b with
  | zero => simp
  | succ n ih =>
    have hsplit : ∑ j ∈ Finset.Icc 1 (n + 1), ∑ k ∈ Finset.Icc (j + 1) (n + 1),
        ((k : ℤ) - (j : ℤ)) =
        (∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc (j + 1) n, ((k : ℤ) - (j : ℤ))) +
        ∑ j ∈ Finset.Icc 1 n, ((n + 1 : ℤ) - (j : ℤ)) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hempty : Finset.Icc (n + 1 + 1) (n + 1) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty, add_zero, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      rw [Finset.sum_Icc_succ_top (by omega : j + 1 ≤ n + 1)]
      push_cast; rfl
    rw [hsplit, mul_add, ih]
    have hlin := sum_Icc_linear n
    have htail : 2 * ∑ j ∈ Finset.Icc 1 n, ((n + 1 : ℤ) - (j : ℤ)) =
        (n : ℤ) * ((n : ℤ) + 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
      have hcard : n + 1 - 1 = n := by omega
      rw [hcard]
      simp only [nsmul_eq_mul]
      linarith
    push_cast
    linarith

private lemma sum_lt_coeff_s (b : ℕ) :
    6 * ∑ j ∈ Finset.Icc 1 b, ∑ i ∈ Finset.Icc 1 (j - 1),
        ((b : ℤ) + 2 * (i : ℤ) - 2 * (j : ℤ)) =
      (b : ℤ) * ((b : ℤ) - 1) * ((b : ℤ) - 2) := by
  have h1 : ∀ j ∈ Finset.Icc 1 b,
      2 * ∑ i ∈ Finset.Icc 1 (j - 1), ((b : ℤ) + 2 * (i : ℤ) - 2 * (j : ℤ)) =
        ((j : ℤ) - 1) * (2 * (b : ℤ) - 2 * (j : ℤ)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hlin := sum_Icc_linear (j - 1)
    have hsub : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
    rw [hsub] at hlin
    have hconst : ∑ _i ∈ Finset.Icc 1 (j - 1), ((b : ℤ) - 2 * (j : ℤ)) =
        ((j : ℤ) - 1) * ((b : ℤ) - 2 * (j : ℤ)) := by
      rw [Finset.sum_const, Nat.card_Icc]
      have hc : j - 1 + 1 - 1 = j - 1 := by omega
      rw [hc, nsmul_eq_mul, hsub]
    have hrew : ∑ i ∈ Finset.Icc 1 (j - 1), ((b : ℤ) + 2 * (i : ℤ) - 2 * (j : ℤ)) =
        (∑ _i ∈ Finset.Icc 1 (j - 1), ((b : ℤ) - 2 * (j : ℤ))) +
          2 * ∑ i ∈ Finset.Icc 1 (j - 1), (i : ℤ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hrew, hconst]
    linarith
  have hsum : 6 * ∑ j ∈ Finset.Icc 1 b, ∑ i ∈ Finset.Icc 1 (j - 1),
      ((b : ℤ) + 2 * (i : ℤ) - 2 * (j : ℤ)) =
      3 * ∑ j ∈ Finset.Icc 1 b, (((j : ℤ) - 1) * (2 * (b : ℤ) - 2 * (j : ℤ))) := by
    rw [show (6 : ℤ) = 3 * 2 by norm_num, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact h1 j hj
  rw [hsum]
  have hlin := sum_Icc_linear b
  have hsq := sum_Icc_sq b
  have hexp : ∑ j ∈ Finset.Icc 1 b, (((j : ℤ) - 1) * (2 * (b : ℤ) - 2 * (j : ℤ))) =
      (-2) * (∑ j ∈ Finset.Icc 1 b, (j : ℤ) ^ 2) +
      (2 * (b : ℤ) + 2) * (∑ j ∈ Finset.Icc 1 b, (j : ℤ)) +
      (∑ _j ∈ Finset.Icc 1 b, (-2 * (b : ℤ))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hexp, Finset.sum_const, Nat.card_Icc]
  have hc : b + 1 - 1 = b := by omega
  rw [hc, nsmul_eq_mul]
  calc 3 * ((-2) * (∑ j ∈ Finset.Icc 1 b, (j : ℤ) ^ 2) +
          (2 * (b : ℤ) + 2) * (∑ j ∈ Finset.Icc 1 b, (j : ℤ)) + (b : ℤ) * (-2 * (b : ℤ)))
      = -(6 * ∑ j ∈ Finset.Icc 1 b, (j : ℤ) ^ 2) +
        3 * ((b : ℤ) + 1) * (2 * ∑ j ∈ Finset.Icc 1 b, (j : ℤ)) - 6 * (b : ℤ) ^ 2 := by ring
    _ = -((b : ℤ) * ((b : ℤ) + 1) * (2 * (b : ℤ) + 1)) +
        3 * ((b : ℤ) + 1) * ((b : ℤ) * ((b : ℤ) + 1)) - 6 * (b : ℤ) ^ 2 := by rw [hsq, hlin]
    _ = (b : ℤ) * ((b : ℤ) - 1) * ((b : ℤ) - 2) := by ring

private lemma sum_lt_const (b : ℕ) :
    3 * ∑ j ∈ Finset.Icc 1 b, ∑ i ∈ Finset.Icc 1 (j - 1),
        (2 * (i : ℤ) * ((i : ℤ) + (b : ℤ)) - 2 * (j : ℤ) ^ 2) =
      -(b : ℤ) * ((b : ℤ) ^ 2 - 1) := by
  induction b with
  | zero => simp
  | succ n ih =>
    have hsplit : ∑ j ∈ Finset.Icc 1 (n + 1), ∑ i ∈ Finset.Icc 1 (j - 1),
        (2 * (i : ℤ) * ((i : ℤ) + ((n + 1 : ℕ) : ℤ)) - 2 * (j : ℤ) ^ 2) =
        (∑ j ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc 1 (j - 1),
          (2 * (i : ℤ) * ((i : ℤ) + (n : ℤ)) - 2 * (j : ℤ) ^ 2)) +
        (∑ j ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc 1 (j - 1), (2 * (i : ℤ))) +
        ∑ i ∈ Finset.Icc 1 n, (2 * (i : ℤ) * ((i : ℤ) + ((n + 1 : ℕ) : ℤ)) - 2 * ((n + 1 : ℕ) : ℤ) ^ 2) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hsub : n + 1 - 1 = n := by omega
      rw [hsub]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      push_cast; ring
    rw [hsplit, mul_add, mul_add, ih]
    have hmid : 3 * ∑ j ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc 1 (j - 1), (2 * (i : ℤ)) =
        (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) + 1) := by
      have hinner : ∀ j ∈ Finset.Icc 1 n,
          ∑ i ∈ Finset.Icc 1 (j - 1), (2 * (i : ℤ)) = (j : ℤ) ^ 2 - (j : ℤ) := by
        intro j hj
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have hlin := sum_Icc_linear (j - 1)
        have hsub : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
        rw [hsub] at hlin
        rw [← Finset.mul_sum]
        linarith
      rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib]
      have hlin := sum_Icc_linear n
      have hsq := sum_Icc_sq n
      linarith
    have htail : 3 * ∑ i ∈ Finset.Icc 1 n,
        (2 * (i : ℤ) * ((i : ℤ) + ((n + 1 : ℕ) : ℤ)) - 2 * ((n + 1 : ℕ) : ℤ) ^ 2) =
        -(n : ℤ) ^ 3 - 3 * (n : ℤ) ^ 2 - 2 * (n : ℤ) := by
      have hexp : ∑ i ∈ Finset.Icc 1 n,
          (2 * (i : ℤ) * ((i : ℤ) + ((n + 1 : ℕ) : ℤ)) - 2 * ((n + 1 : ℕ) : ℤ) ^ 2) =
          2 * (∑ i ∈ Finset.Icc 1 n, (i : ℤ) ^ 2) +
          (2 * ((n + 1 : ℕ) : ℤ)) * (∑ i ∈ Finset.Icc 1 n, (i : ℤ)) +
          ∑ _i ∈ Finset.Icc 1 n, (-2 * ((n + 1 : ℕ) : ℤ) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hexp, Finset.sum_const, Nat.card_Icc]
      have hc : n + 1 - 1 = n := by omega
      rw [hc, nsmul_eq_mul]
      have hlin := sum_Icc_linear n
      have hsq := sum_Icc_sq n
      push_cast
      calc 3 * (2 * (∑ i ∈ Finset.Icc 1 n, (i : ℤ) ^ 2) +
              2 * ((n : ℤ) + 1) * (∑ i ∈ Finset.Icc 1 n, (i : ℤ)) +
              (n : ℤ) * (-2 * ((n : ℤ) + 1) ^ 2))
          = (6 * ∑ i ∈ Finset.Icc 1 n, (i : ℤ) ^ 2) +
            3 * ((n : ℤ) + 1) * (2 * ∑ i ∈ Finset.Icc 1 n, (i : ℤ)) -
            6 * (n : ℤ) * ((n : ℤ) + 1) ^ 2 := by ring
        _ = (n : ℤ) * ((n : ℤ) + 1) * (2 * (n : ℤ) + 1) +
            3 * ((n : ℤ) + 1) * ((n : ℤ) * ((n : ℤ) + 1)) -
            6 * (n : ℤ) * ((n : ℤ) + 1) ^ 2 := by rw [hsq, hlin]
        _ = -(n : ℤ) ^ 3 - 3 * (n : ℤ) ^ 2 - 2 * (n : ℤ) := by ring
    rw [hmid, htail]
    push_cast
    ring

/-- The closed-form polynomial bound for Case 2 (`a ≥ 2, 1 ≤ b ≤ a ≤ r`) is strictly positive. -/
private lemma graft_poly_pos {a b r : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) (hba : b ≤ a) (hra : a ≤ r) :
    0 < (12 * (a : ℤ) * (b : ℤ) * ((a : ℤ) - 1) +
          (b : ℤ) * ((b : ℤ) - 1) * ((b : ℤ) - 2)) * ((r : ℤ) - (a : ℤ)) +
        2 * (b : ℤ) * (6 * ((a : ℤ) - (b : ℤ)) ^ 3 +
          (15 * (b : ℤ) - 6) * ((a : ℤ) - (b : ℤ)) ^ 2 +
          2 * ((b : ℤ) - 1) * (7 * (b : ℤ) + 1) * ((a : ℤ) - (b : ℤ)) +
          (5 * (b : ℤ) ^ 3 - 7 * (b : ℤ) ^ 2 - 2 * (b : ℤ) + 1)) := by
  set d : ℤ := (a : ℤ) - (b : ℤ)
  set s : ℤ := (r : ℤ) - (a : ℤ)
  have hd : 0 ≤ d := by omega
  have hs : 0 ≤ s := by omega
  have haZ : (2 : ℤ) ≤ (a : ℤ) := by omega
  have hbZ : (1 : ℤ) ≤ (b : ℤ) := by omega
  have hcoeff : 0 ≤ 12 * (a : ℤ) * (b : ℤ) * ((a : ℤ) - 1) +
      (b : ℤ) * ((b : ℤ) - 1) * ((b : ℤ) - 2) := by
    have h1 : 0 ≤ 12 * (a : ℤ) * (b : ℤ) * ((a : ℤ) - 1) := by
      have : 0 ≤ (a : ℤ) - 1 := by omega
      positivity
    by_cases hb1 : b = 1
    · subst hb1; simp only [Nat.cast_one, sub_self, mul_zero, zero_mul, add_zero]; exact h1
    · have hb2 : (2 : ℤ) ≤ (b : ℤ) := by omega
      have h2 : 0 ≤ (b : ℤ) * ((b : ℤ) - 1) * ((b : ℤ) - 2) := by
        have : 0 ≤ (b : ℤ) - 1 := by omega
        have : 0 ≤ (b : ℤ) - 2 := by omega
        positivity
      linarith
  have hterm1 : 0 ≤ (12 * (a : ℤ) * (b : ℤ) * ((a : ℤ) - 1) +
      (b : ℤ) * ((b : ℤ) - 1) * ((b : ℤ) - 2)) * s := mul_nonneg hcoeff hs
  have hterm2 : 0 < 6 * d ^ 3 + (15 * (b : ℤ) - 6) * d ^ 2 +
      2 * ((b : ℤ) - 1) * (7 * (b : ℤ) + 1) * d +
      (5 * (b : ℤ) ^ 3 - 7 * (b : ℤ) ^ 2 - 2 * (b : ℤ) + 1) := by
    by_cases hb1 : b = 1
    · subst hb1
      have hd1 : 1 ≤ d := by omega
      have h3 : 1 ≤ d ^ 3 := by nlinarith [sq_nonneg d]
      have h2 : 1 ≤ d ^ 2 := by nlinarith
      simp only [Nat.cast_one]
      nlinarith
    · have hb2 : 2 ≤ (b : ℤ) := by omega
      have hcube : 5 * (b : ℤ) ^ 3 - 7 * (b : ℤ) ^ 2 - 2 * (b : ℤ) + 1 =
          ((b : ℤ) - 2) * (5 * (b : ℤ) ^ 2 + 3 * (b : ℤ) + 4) + 9 := by ring
      have hpos1 : 0 ≤ 6 * d ^ 3 := by positivity
      have hpos2 : 0 ≤ (15 * (b : ℤ) - 6) * d ^ 2 := by
        have : 0 ≤ 15 * (b : ℤ) - 6 := by omega
        positivity
      have hpos3 : 0 ≤ 2 * ((b : ℤ) - 1) * (7 * (b : ℤ) + 1) * d := by
        have : 0 ≤ (b : ℤ) - 1 := by omega
        positivity
      have hpos4 : 9 ≤ 5 * (b : ℤ) ^ 3 - 7 * (b : ℤ) ^ 2 - 2 * (b : ℤ) + 1 := by
        rw [hcube]
        have : 0 ≤ ((b : ℤ) - 2) * (5 * (b : ℤ) ^ 2 + 3 * (b : ℤ) + 4) := by
          have : 0 ≤ (b : ℤ) - 2 := by omega
          positivity
        linarith
      linarith
  nlinarith

end AlgebraicGraftBounds

section GraftMove

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A pendant-path grafting configuration in a finite tree `T`: two disjoint pendant paths
`armA` (length `a`) and `armB` (length `b`) attached at `v`, with `1 ≤ b ≤ a ≤ r` where
`r + 1 = |V \ (armA ∪ armB)|`. -/
structure GraftConfig (T : SimpleGraph V) where
  v : V
  a : ℕ
  b : ℕ
  ha : 1 ≤ a
  hb : 1 ≤ b
  hba : b ≤ a
  armA : Fin a ↪ V
  armB : Fin b ↪ V
  hdisjAB : Disjoint (Finset.univ.image armA) (Finset.univ.image armB)
  hvA : v ∉ Finset.univ.image armA
  hvB : v ∉ Finset.univ.image armB
  hC_card : a + 1 ≤ (Finset.univ \ (Finset.univ.image armA ∪ Finset.univ.image armB)).card
  hadjA : ∀ (i : Fin a) (u : V), T.Adj (armA i) u ↔
    (i.val = 0 ∧ u = v) ∨
    (∃ h : 0 < i.val, u = armA ⟨i.val - 1, by omega⟩) ∨
    (∃ h : i.val + 1 < a, u = armA ⟨i.val + 1, h⟩)
  hadjB : ∀ (j : Fin b) (u : V), T.Adj (armB j) u ↔
    (j.val = 0 ∧ u = v) ∨
    (∃ h : 0 < j.val, u = armB ⟨j.val - 1, by omega⟩) ∨
    (∃ h : j.val + 1 < b, u = armB ⟨j.val + 1, h⟩)

namespace GraftConfig

variable {T : SimpleGraph V} (cfg : GraftConfig T)

/-- Vertex set of arm `A`. -/
def setA : Finset V := Finset.univ.image cfg.armA

/-- Vertex set of arm `B`. -/
def setB : Finset V := Finset.univ.image cfg.armB

/-- Core vertex set `C = V \ (A ∪ B)` (contains `v`). -/
def setC : Finset V := Finset.univ \ (cfg.setA ∪ cfg.setB)

/-- Core size parameter `r = |C| - 1 ≥ a`. -/
def r : ℕ := cfg.setC.card - 1

lemma card_setA : cfg.setA.card = cfg.a := by
  simp [setA, Finset.card_image_of_injective _ cfg.armA.injective]

lemma card_setB : cfg.setB.card = cfg.b := by
  simp [setB, Finset.card_image_of_injective _ cfg.armB.injective]

lemma mem_setC_v : cfg.v ∈ cfg.setC := by
  simp [setC, setA, setB, cfg.hvA, cfg.hvB]

lemma card_setC_eq : cfg.setC.card = cfg.r + 1 := by
  have h : 1 ≤ cfg.setC.card := Finset.card_pos.mpr ⟨cfg.v, cfg.mem_setC_v⟩
  dsimp [r]; omega

lemma a_le_r : cfg.a ≤ cfg.r := by
  have := cfg.hC_card
  dsimp [r, setC, setA, setB] at *; omega

lemma card_V_eq : Fintype.card V = cfg.a + cfg.b + cfg.r + 1 := by
  have h1 : (cfg.setA ∪ cfg.setB).card + cfg.setC.card = Fintype.card V := by
    rw [setC, Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ]
    have hle : (cfg.setA ∪ cfg.setB).card ≤ Fintype.card V := Finset.card_le_univ _
    omega
  have hdisj : Disjoint cfg.setA cfg.setB := cfg.hdisjAB
  rw [Finset.card_union_of_disjoint hdisj, cfg.card_setA, cfg.card_setB,
    cfg.card_setC_eq] at h1
  omega

lemma armA_ne_armB (i : Fin cfg.a) (j : Fin cfg.b) : cfg.armA i ≠ cfg.armB j := by
  intro h
  have h1 : cfg.armA i ∈ cfg.setA := Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have h2 : cfg.armA i ∈ cfg.setB := h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)
  exact Finset.disjoint_left.mp cfg.hdisjAB h1 h2

lemma armA_ne_v (i : Fin cfg.a) : cfg.armA i ≠ cfg.v := by
  intro h
  exact cfg.hvA (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i))

lemma armB_ne_v (j : Fin cfg.b) : cfg.armB j ≠ cfg.v := by
  intro h
  exact cfg.hvB (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j))

lemma not_adj_armA_setC (i : Fin cfg.a) {z : V} (hz : z ∈ cfg.setC) (hzi : z ≠ cfg.v) :
    ¬ T.Adj (cfg.armA i) z := by
  rw [cfg.hadjA]
  rintro (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩)
  · exact hzi rfl
  · simp [setC, setA] at hz
  · simp [setC, setA] at hz

lemma not_adj_armB_setC (j : Fin cfg.b) {z : V} (hz : z ∈ cfg.setC) (hzv : z ≠ cfg.v) :
    ¬ T.Adj (cfg.armB j) z := by
  rw [cfg.hadjB]
  rintro (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩)
  · exact hzv rfl
  · simp [setC, setB] at hz
  · simp [setC, setB] at hz

lemma not_adj_armA_armB (i : Fin cfg.a) (j : Fin cfg.b) : ¬ T.Adj (cfg.armA i) (cfg.armB j) := by
  rw [cfg.hadjA]
  rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩)
  · exact cfg.armB_ne_v j h
  · exact cfg.armA_ne_armB _ j h.symm
  · exact cfg.armA_ne_armB _ j h.symm

/-- First vertex of arm `A`. -/
def a0 : V := cfg.armA ⟨0, cfg.ha⟩

/-- Tip vertex of arm `B`. -/
def bTip : V := cfg.armB ⟨cfg.b - 1, by have := cfg.hb; omega⟩

/-- The grafted graph `T'` obtained by replacing edge `v - a0` with `bTip - a0`. -/
def graftGraph : SimpleGraph V where
  Adj x y :=
    (T.Adj x y ∧ s(x, y) ≠ s(cfg.v, cfg.a0)) ∨ s(x, y) = s(cfg.bTip, cfg.a0)
  symm := ⟨fun x y h => by
    rcases h with ⟨h1, h2⟩ | h3
    · left; exact ⟨h1.symm, by rwa [Sym2.eq_swap]⟩
    · right; rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨h1, _⟩ | h3
    · exact T.loopless.irrefl x h1
    · rcases Sym2.eq_iff.mp h3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact cfg.armA_ne_armB ⟨0, cfg.ha⟩ ⟨cfg.b - 1, by have := cfg.hb; omega⟩ (h2.symm.trans h1)
      · exact cfg.armA_ne_armB ⟨0, cfg.ha⟩ ⟨cfg.b - 1, by have := cfg.hb; omega⟩ (h1.symm.trans h2)⟩

lemma adj_v_a0 : T.Adj cfg.v cfg.a0 := by
  exact ((cfg.hadjA ⟨0, cfg.ha⟩ cfg.v).mpr (Or.inl ⟨rfl, rfl⟩)).symm

lemma not_adj_bTip_a0 : ¬ T.Adj cfg.bTip cfg.a0 :=
  fun h => cfg.not_adj_armA_armB ⟨0, cfg.ha⟩ ⟨cfg.b - 1, by have := cfg.hb; omega⟩ h.symm

private lemma graftGraph_adj (x y : V) :
    cfg.graftGraph.Adj x y ↔
      (T.Adj x y ∧ s(x, y) ≠ s(cfg.v, cfg.a0)) ∨ s(x, y) = s(cfg.bTip, cfg.a0) := Iff.rfl

lemma graft_adj_C_iff {x y : V} (hx : x ∈ cfg.setC) (hy : y ∈ cfg.setC) :
    cfg.graftGraph.Adj x y ↔ T.Adj x y := by
  have hxa : x ≠ cfg.a0 := by
    intro h; subst h; simp [setC, setA, a0] at hx
  have hya : y ≠ cfg.a0 := by
    intro h; subst h; simp [setC, setA, a0] at hy
  rw [cfg.graftGraph_adj]
  simp only [ne_eq, Sym2.eq_iff, hxa, hya, and_false, false_and, or_self, not_false_eq_true,
    and_true, or_false]

/-- Path inside `armA` from `armA i` to `armA k` (valid in both `T` and `T'`). -/
private def walkArmA_aux (G : SimpleGraph V)
    (hstep : ∀ (t : ℕ) (ht : t + 1 < cfg.a), G.Adj (cfg.armA ⟨t, by omega⟩) (cfg.armA ⟨t + 1, ht⟩)) :
    ∀ (d : ℕ) (i : ℕ) (hi : i + d < cfg.a),
      G.Walk (cfg.armA ⟨i, by omega⟩) (cfg.armA ⟨i + d, hi⟩)
  | 0, _, _ => Walk.nil
  | d + 1, i, hi =>
    Walk.cons (hstep i (by omega))
      (Walk.copy (walkArmA_aux G hstep d (i + 1) (by omega)) rfl (by congr 1; apply Fin.ext; dsimp; omega))

private lemma walkArmA_aux_length (G : SimpleGraph V) (hstep) (d i : ℕ) (hi : i + d < cfg.a) :
    (cfg.walkArmA_aux G hstep d i hi).length = d := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih => simp [walkArmA_aux, ih]

private lemma walkArmA_aux_support (G : SimpleGraph V) (hstep) (d i : ℕ) (hi : i + d < cfg.a) :
    ∀ u ∈ (cfg.walkArmA_aux G hstep d i hi).support,
      ∃ t : Fin cfg.a, u = cfg.armA t ∧ i ≤ t.val ∧ t.val ≤ i + d := by
  induction d generalizing i with
  | zero =>
    intro u hu
    simp only [walkArmA_aux, Walk.support_nil, List.mem_singleton] at hu
    exact ⟨⟨i, hi⟩, hu, le_rfl, by dsimp; omega⟩
  | succ d ih =>
    intro u hu
    simp only [walkArmA_aux, Walk.support_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨⟨i, by omega⟩, rfl, le_rfl, by dsimp; omega⟩
    · rw [Walk.support_copy] at hu
      obtain ⟨t, rfl, h1, h2⟩ := ih (i + 1) (by omega) u hu
      exact ⟨t, rfl, by omega, by omega⟩

private lemma walkArmA_aux_isPath (G : SimpleGraph V) (hstep) (d i : ℕ) (hi : i + d < cfg.a) :
    (cfg.walkArmA_aux G hstep d i hi).IsPath := by
  induction d generalizing i with
  | zero => simp [walkArmA_aux]
  | succ d ih =>
    rw [walkArmA_aux, Walk.cons_isPath_iff]
    refine ⟨?_, ?_⟩
    · exact (Walk.isPath_copy _ rfl _).mpr (ih (i + 1) (by omega))
    · intro hmem
      rw [Walk.support_copy] at hmem
      obtain ⟨t, ht, h1, _⟩ := cfg.walkArmA_aux_support G hstep d (i + 1) (by omega) _ hmem
      have heq := congrArg Fin.val (cfg.armA.injective ht)
      dsimp at heq
      omega

/-- Path inside `armB` from `armB j` to `armB k` (valid in both `T` and `T'`). -/
private def walkArmB_aux (G : SimpleGraph V)
    (hstep : ∀ (t : ℕ) (ht : t + 1 < cfg.b), G.Adj (cfg.armB ⟨t, by omega⟩) (cfg.armB ⟨t + 1, ht⟩)) :
    ∀ (d : ℕ) (j : ℕ) (hj : j + d < cfg.b),
      G.Walk (cfg.armB ⟨j, by omega⟩) (cfg.armB ⟨j + d, hj⟩)
  | 0, _, _ => Walk.nil
  | d + 1, j, hj =>
    Walk.cons (hstep j (by omega))
      (Walk.copy (walkArmB_aux G hstep d (j + 1) (by omega)) rfl (by congr 1; apply Fin.ext; dsimp; omega))

private lemma walkArmB_aux_length (G : SimpleGraph V) (hstep) (d j : ℕ) (hj : j + d < cfg.b) :
    (cfg.walkArmB_aux G hstep d j hj).length = d := by
  induction d generalizing j with
  | zero => rfl
  | succ d ih => simp [walkArmB_aux, ih]

private lemma walkArmB_aux_support (G : SimpleGraph V) (hstep) (d j : ℕ) (hj : j + d < cfg.b) :
    ∀ u ∈ (cfg.walkArmB_aux G hstep d j hj).support,
      ∃ t : Fin cfg.b, u = cfg.armB t ∧ j ≤ t.val ∧ t.val ≤ j + d := by
  induction d generalizing j with
  | zero =>
    intro u hu
    simp only [walkArmB_aux, Walk.support_nil, List.mem_singleton] at hu
    exact ⟨⟨j, hj⟩, hu, le_rfl, by dsimp; omega⟩
  | succ d ih =>
    intro u hu
    simp only [walkArmB_aux, Walk.support_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨⟨j, by omega⟩, rfl, le_rfl, by dsimp; omega⟩
    · rw [Walk.support_copy] at hu
      obtain ⟨t, rfl, h1, h2⟩ := ih (j + 1) (by omega) u hu
      exact ⟨t, rfl, by omega, by omega⟩

private lemma walkArmB_aux_isPath (G : SimpleGraph V) (hstep) (d j : ℕ) (hj : j + d < cfg.b) :
    (cfg.walkArmB_aux G hstep d j hj).IsPath := by
  induction d generalizing j with
  | zero => simp [walkArmB_aux]
  | succ d ih =>
    rw [walkArmB_aux, Walk.cons_isPath_iff]
    refine ⟨?_, ?_⟩
    · exact (Walk.isPath_copy _ rfl _).mpr (ih (j + 1) (by omega))
    · intro hmem
      rw [Walk.support_copy] at hmem
      obtain ⟨t, ht, h1, _⟩ := cfg.walkArmB_aux_support G hstep d (j + 1) (by omega) _ hmem
      have heq := congrArg Fin.val (cfg.armB.injective ht)
      dsimp at heq
      omega

private lemma hstepA_T : ∀ (t : ℕ) (ht : t + 1 < cfg.a),
    T.Adj (cfg.armA ⟨t, by omega⟩) (cfg.armA ⟨t + 1, ht⟩) :=
  fun t ht => (cfg.hadjA ⟨t, by omega⟩ _).mpr (Or.inr (Or.inr ⟨ht, rfl⟩))

private lemma hstepB_T : ∀ (t : ℕ) (ht : t + 1 < cfg.b),
    T.Adj (cfg.armB ⟨t, by omega⟩) (cfg.armB ⟨t + 1, ht⟩) :=
  fun t ht => (cfg.hadjB ⟨t, by omega⟩ _).mpr (Or.inr (Or.inr ⟨ht, rfl⟩))

private lemma hstepA_T' : ∀ (t : ℕ) (ht : t + 1 < cfg.a),
    cfg.graftGraph.Adj (cfg.armA ⟨t, by omega⟩) (cfg.armA ⟨t + 1, ht⟩) := by
  intro t ht
  left
  refine ⟨cfg.hstepA_T t ht, ?_⟩
  simp only [ne_eq, Sym2.eq_iff, not_or]
  exact ⟨fun h => cfg.armA_ne_v _ h.1, fun h => cfg.armA_ne_v _ h.2⟩

private lemma hstepB_T' : ∀ (t : ℕ) (ht : t + 1 < cfg.b),
    cfg.graftGraph.Adj (cfg.armB ⟨t, by omega⟩) (cfg.armB ⟨t + 1, ht⟩) := by
  intro t ht
  left
  refine ⟨cfg.hstepB_T t ht, ?_⟩
  simp only [ne_eq, Sym2.eq_iff, not_or]
  exact ⟨fun h => cfg.armB_ne_v _ h.1, fun h => cfg.armB_ne_v _ h.2⟩

private lemma adj_v_b0_T : T.Adj cfg.v (cfg.armB ⟨0, cfg.hb⟩) :=
  ((cfg.hadjB ⟨0, cfg.hb⟩ cfg.v).mpr (Or.inl ⟨rfl, rfl⟩)).symm

private lemma adj_v_b0_T' : cfg.graftGraph.Adj cfg.v (cfg.armB ⟨0, cfg.hb⟩) := by
  left
  refine ⟨cfg.adj_v_b0_T, ?_⟩
  simp only [ne_eq, Sym2.eq_iff, not_or]
  exact ⟨fun h => cfg.armA_ne_armB ⟨0, cfg.ha⟩ ⟨0, cfg.hb⟩ h.2.symm,
    fun h => cfg.armB_ne_v _ h.2⟩

private lemma adj_bTip_a0_T' : cfg.graftGraph.Adj cfg.bTip cfg.a0 :=
  Or.inr rfl

/-- Any simple path in `T` between two vertices in `C` stays entirely inside `C`. -/
private lemma path_C_stays_in_C {z₁ z₂ : V} (hz₁ : z₁ ∈ cfg.setC) (hz₂ : z₂ ∈ cfg.setC)
    {p : T.Walk z₁ z₂} (hp : p.IsPath) : ∀ u ∈ p.support, u ∈ cfg.setC := by
  -- A path entering A (or B) must enter at armA 0 (or armB 0) from v and exit back through v,
  -- repeating v, contradicting IsPath.
  intro u hu
  by_contra hnotC
  have hor : u ∈ cfg.setA ∨ u ∈ cfg.setB := by
    simp only [setC, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_not] at hnotC
    exact hnotC
  -- Split `p` at `u` into `p₁ : z₁ → u` and `p₂ : u → z₂`
  let p₁ := p.takeUntil u hu
  let p₂ := p.dropUntil u hu
  have hp_eq : p₁.append p₂ = p := Walk.take_spec p hu
  have hv_in : ∀ (S : Finset V) (hS : ∀ x ∈ S, ∀ y, T.Adj x y → y ∈ S ∨ y = cfg.v)
      {a b : V} (ha : a ∈ S) (hb : b ∉ S) (q : T.Walk a b),
      cfg.v ∈ q.support := by
    intro S hS a b ha hb q
    induction q with
    | nil => exact (hb ha).elim
    | @cons x y _ hadj rest ih =>
      rcases hS x ha y hadj with hyS | rfl
      · exact List.mem_cons_of_mem _ (ih hyS hb)
      · exact List.mem_cons_of_mem _ (Walk.start_mem_support rest)
  have hS_A : ∀ x ∈ cfg.setA, ∀ y, T.Adj x y → y ∈ cfg.setA ∨ y = cfg.v := by
    intro x hx y hxy
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    rcases (cfg.hadjA i y).mp hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hS_B : ∀ x ∈ cfg.setB, ∀ y, T.Adj x y → y ∈ cfg.setB ∨ y = cfg.v := by
    intro x hx y hxy
    rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
    rcases (cfg.hadjB j y).mp hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hv1 : cfg.v ∈ p₁.support := by
    have hv1' : cfg.v ∈ p₁.reverse.support := by
      rcases hor with huA | huB
      · exact hv_in cfg.setA hS_A huA (by simp [setC] at hz₁; exact hz₁.1) p₁.reverse
      · exact hv_in cfg.setB hS_B huB (by simp [setC] at hz₁; exact hz₁.2) p₁.reverse
    simpa [Walk.support_reverse] using hv1'
  have hv2 : cfg.v ∈ p₂.support := by
    rcases hor with huA | huB
    · exact hv_in cfg.setA hS_A huA (by simp [setC] at hz₂; exact hz₂.1) p₂
    · exact hv_in cfg.setB hS_B huB (by simp [setC] at hz₂; exact hz₂.2) p₂
  have hne_vu : cfg.v ≠ u := by
    intro h; subst h; exact hnotC cfg.mem_setC_v
  have hv2_tail : cfg.v ∈ p₂.support.tail := by
    cases hsup : p₂.support with
    | nil => exact (Walk.support_ne_nil p₂ hsup).elim
    | cons a l =>
      have ha : a = u := by
        have := Walk.head_support p₂
        simp only [hsup, List.head_cons] at this
        exact this
      rw [hsup] at hv2
      rcases List.mem_cons.mp hv2 with rfl | hv2'
      · exact (hne_vu ha).elim
      · exact hv2'
  have hnd : p.support.Nodup := hp.support_nodup
  rw [← hp_eq, Walk.support_append] at hnd
  exact (List.nodup_append.mp hnd).2.2 cfg.v hv1 cfg.v hv2_tail rfl

/-- Lift any `T`-walk whose support lies inside `C` to a `T'`-walk with the same support. -/
private def liftWalkC : ∀ {x y : V} (p : T.Walk x y),
    (∀ u ∈ p.support, u ∈ cfg.setC) → cfg.graftGraph.Walk x y
  | _, _, Walk.nil, _ => Walk.nil
  | _, _, Walk.cons hadj rest, hC =>
    Walk.cons ((cfg.graft_adj_C_iff
        (hC _ (List.mem_cons_self ..))
        (hC _ (List.mem_cons_of_mem _ (Walk.start_mem_support rest)))).mpr hadj)
      (liftWalkC rest (fun u hu => hC u (List.mem_cons_of_mem _ hu)))

private lemma liftWalkC_support {x y : V} (p : T.Walk x y)
    (hC : ∀ u ∈ p.support, u ∈ cfg.setC) :
    (cfg.liftWalkC p hC).support = p.support := by
  induction p with
  | nil => rfl
  | cons _ rest ih =>
    simp only [liftWalkC, Walk.support_cons, ih]

private lemma liftWalkC_length {x y : V} (p : T.Walk x y)
    (hC : ∀ u ∈ p.support, u ∈ cfg.setC) :
    (cfg.liftWalkC p hC).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ rest ih =>
    simp only [liftWalkC, Walk.length_cons, ih]

private lemma liftWalkC_isPath {x y : V} {p : T.Walk x y}
    (hp : p.IsPath) (hC : ∀ u ∈ p.support, u ∈ cfg.setC) :
    (cfg.liftWalkC p hC).IsPath := by
  rw [Walk.isPath_def, cfg.liftWalkC_support p hC]
  exact hp.support_nodup

/-- The grafted graph `T'` is a tree. -/
theorem graft_isTree (hT : T.IsTree) : cfg.graftGraph.IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · -- Connected: every vertex is reachable from `v`
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨cfg.v, fun u => ?_⟩
    by_cases huC : u ∈ cfg.setC
    · obtain ⟨p, hp, _⟩ := hT.existsUnique_path cfg.v u
      exact ⟨cfg.liftWalkC p (cfg.path_C_stays_in_C cfg.mem_setC_v huC hp)⟩
    · have hor : u ∈ cfg.setA ∨ u ∈ cfg.setB := by
        simp only [setC, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_not] at huC
        exact huC
      rcases hor with huA | huB
      · rcases Finset.mem_image.mp huA with ⟨i, _, rfl⟩
        have hb0_to_tip : cfg.graftGraph.Walk (cfg.armB ⟨0, cfg.hb⟩) cfg.bTip :=
          Walk.copy (cfg.walkArmB_aux cfg.graftGraph cfg.hstepB_T' (cfg.b - 1) 0 (by have := cfg.hb; omega))
            (by congr 1) (by congr 1; apply Fin.ext; dsimp [bTip]; have := cfg.hb; omega)
        have ha0_to_i : cfg.graftGraph.Walk cfg.a0 (cfg.armA i) :=
          Walk.copy (cfg.walkArmA_aux cfg.graftGraph cfg.hstepA_T' i.val 0 (by omega))
            (by congr 1) (by congr 1; apply Fin.ext; simp)
        exact ⟨((hb0_to_tip.cons cfg.adj_v_b0_T').append (ha0_to_i.cons cfg.adj_bTip_a0_T'))⟩
      · rcases Finset.mem_image.mp huB with ⟨j, _, rfl⟩
        have hb0_to_j : cfg.graftGraph.Walk (cfg.armB ⟨0, cfg.hb⟩) (cfg.armB j) :=
          Walk.copy (cfg.walkArmB_aux cfg.graftGraph cfg.hstepB_T' j.val 0 (by omega))
            (by congr 1) (by congr 1; apply Fin.ext; simp)
        exact ⟨hb0_to_j.cons cfg.adj_v_b0_T'⟩
  · -- Same number of edges as `T`, hence `card V - 1`
    have he_eq : cfg.graftGraph.edgeFinset =
        insert s(cfg.bTip, cfg.a0) (T.edgeFinset.erase s(cfg.v, cfg.a0)) := by
      ext e
      induction e using Sym2.ind with
      | h x y =>
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_insert,
          Finset.mem_erase, graftGraph_adj]
        tauto
    have hmem_old : s(cfg.v, cfg.a0) ∈ T.edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr cfg.adj_v_a0
    have hnot_new : s(cfg.bTip, cfg.a0) ∉ T.edgeFinset.erase s(cfg.v, cfg.a0) := by
      intro h
      exact cfg.not_adj_bTip_a0 (SimpleGraph.mem_edgeFinset.mp (Finset.mem_erase.mp h).2)
    have hcard_edges : cfg.graftGraph.edgeFinset.card = T.edgeFinset.card := by
      rw [he_eq, Finset.card_insert_of_notMem hnot_new, Finset.card_erase_of_mem hmem_old]
      have hpos : 1 ≤ T.edgeFinset.card := Finset.card_pos.mpr ⟨_, hmem_old⟩
      omega
    have hTcard := (SimpleGraph.isTree_iff_connected_and_card.mp hT).2
    have h1 : Nat.card cfg.graftGraph.edgeSet = cfg.graftGraph.edgeFinset.card := by
      rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    have h2 : Nat.card T.edgeSet = T.edgeFinset.card := by
      rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    rw [h1, hcard_edges, ← h2]
    exact hTcard

/-- Exact degree comparison between `T'` and `T`, yielding `leafCount T' + 1 = leafCount T`. -/
theorem graft_leafCount (hT : T.IsTree) :
    leafCount cfg.graftGraph + 1 = leafCount T := by
  classical
  have hdeg_v : cfg.graftGraph.degree cfg.v + 1 = T.degree cfg.v := by
    have hnf : cfg.graftGraph.neighborFinset cfg.v =
        (T.neighborFinset cfg.v).erase cfg.a0 := by
      ext u
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_erase, SimpleGraph.mem_neighborFinset,
        cfg.graftGraph_adj]
      simp only [ne_eq, Sym2.eq_iff]
      constructor
      · rintro (⟨hadj, hne⟩ | hnew)
        · refine ⟨fun h => hne (Or.inl ⟨trivial, h⟩), hadj⟩
        · rcases hnew with ⟨hv, _⟩ | ⟨hv, _⟩
          · exact (cfg.armB_ne_v _ hv.symm).elim
          · exact (cfg.armA_ne_v _ hv.symm).elim
      · rintro ⟨hne, hadj⟩
        left
        refine ⟨hadj, ?_⟩
        rintro (⟨_, h⟩ | ⟨hv, _⟩)
        · exact hne h
        · exact cfg.armA_ne_v _ hv.symm
    have hmem : cfg.a0 ∈ T.neighborFinset cfg.v :=
      (SimpleGraph.mem_neighborFinset T _ _).mpr cfg.adj_v_a0
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
      hnf, Finset.card_erase_of_mem hmem]
    have hpos : 1 ≤ (T.neighborFinset cfg.v).card := Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  have hdeg_v_ge3 : 3 ≤ T.degree cfg.v := by
    -- `v` has neighbor `a0`, neighbor `armB 0`, and at least one neighbor in `C` since `|C| ≥ 2`
    have hC_ge2 : 2 ≤ cfg.setC.card := by
      have := cfg.card_setC_eq; have := cfg.a_le_r; have := cfg.ha; omega
    obtain ⟨z, hzC, hzv⟩ := Finset.exists_mem_ne (by omega : 1 < cfg.setC.card) cfg.v
    -- Take the first step of the unique path from `v` to `z`
    obtain ⟨p, hp, _⟩ := hT.existsUnique_path cfg.v z
    cases p with
    | nil => exact (hzv rfl).elim
    | @cons _ w _ hvw rest =>
      have hwC : w ∈ cfg.setC :=
        cfg.path_C_stays_in_C cfg.mem_setC_v hzC hp w (List.mem_cons_of_mem _ (Walk.start_mem_support rest))
      have hsub : ({cfg.a0, cfg.armB ⟨0, cfg.hb⟩, w} : Finset V) ⊆ T.neighborFinset cfg.v := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rw [SimpleGraph.mem_neighborFinset]
        rcases hu with rfl | rfl | rfl
        · exact cfg.adj_v_a0
        · exact cfg.adj_v_b0_T
        · exact hvw
      have hne1 : cfg.a0 ≠ cfg.armB ⟨0, cfg.hb⟩ := cfg.armA_ne_armB _ _
      have hne2 : cfg.a0 ≠ w := fun h => by subst h; simp [setC, setA, a0] at hwC
      have hne3 : cfg.armB ⟨0, cfg.hb⟩ ≠ w := fun h => by subst h; simp [setC, setB] at hwC
      have h3 : ({cfg.a0, cfg.armB ⟨0, cfg.hb⟩, w} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]),
          Finset.card_insert_of_notMem (by simp [hne3]), Finset.card_singleton]
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact h3 ▸ Finset.card_le_card hsub
  have hdeg_bTip_T : T.degree cfg.bTip = 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    by_cases hb1 : cfg.b = 1
    · have hnf : T.neighborFinset cfg.bTip = {cfg.v} := by
        ext u
        rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton, bTip, cfg.hadjB]
        constructor
        · rintro (⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩)
          · rfl
          · omega
          · omega
        · rintro rfl; left; exact ⟨by omega, rfl⟩
      rw [hnf, Finset.card_singleton]
    · have hb_ge2 : 2 ≤ cfg.b := by have := cfg.hb; omega
      have hnf : T.neighborFinset cfg.bTip = {cfg.armB ⟨cfg.b - 2, by omega⟩} := by
        ext u
        rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton, bTip, cfg.hadjB]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, rfl⟩ | ⟨h, _⟩)
          · dsimp only at h; omega
          · exact congrArg cfg.armB (Fin.ext (by dsimp only; omega))
          · dsimp only at h; omega
        · rintro rfl
          right; left; exact ⟨by dsimp only; omega, congrArg cfg.armB (Fin.ext (by dsimp only; omega))⟩
      rw [hnf, Finset.card_singleton]
  have hdeg_bTip_T' : cfg.graftGraph.degree cfg.bTip = 2 := by
    have hnf : cfg.graftGraph.neighborFinset cfg.bTip =
        insert cfg.a0 (T.neighborFinset cfg.bTip) := by
      ext u
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_insert, SimpleGraph.mem_neighborFinset,
        cfg.graftGraph_adj]
      simp only [ne_eq, Sym2.eq_iff]
      constructor
      · rintro (⟨hadj, _⟩ | (⟨_, h⟩ | ⟨h, _⟩))
        · exact Or.inr hadj
        · exact Or.inl h
        · exact (cfg.armA_ne_armB _ _ h.symm).elim
      · rintro (rfl | hadj)
        · exact Or.inr (Or.inl ⟨trivial, rfl⟩)
        · left
          refine ⟨hadj, ?_⟩
          rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact cfg.armB_ne_v _ h
          · exact cfg.armA_ne_armB _ _ h.symm
    have hnot : cfg.a0 ∉ T.neighborFinset cfg.bTip := by
      rw [SimpleGraph.mem_neighborFinset]
      exact cfg.not_adj_bTip_a0
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hnf, Finset.card_insert_of_notMem hnot,
      SimpleGraph.card_neighborFinset_eq_degree, hdeg_bTip_T]
  have hdeg_a0 : cfg.graftGraph.degree cfg.a0 = T.degree cfg.a0 := by
    have hnf : cfg.graftGraph.neighborFinset cfg.a0 =
        insert cfg.bTip ((T.neighborFinset cfg.a0).erase cfg.v) := by
      ext u
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_erase,
        SimpleGraph.mem_neighborFinset, cfg.graftGraph_adj]
      simp only [ne_eq, Sym2.eq_iff]
      constructor
      · rintro (⟨hadj, hne⟩ | (⟨h, _⟩ | ⟨_, h⟩))
        · right; exact ⟨fun hv => hne (Or.inr ⟨trivial, hv⟩), hadj⟩
        · exact (cfg.armA_ne_armB _ _ h).elim
        · exact Or.inl h
      · rintro (rfl | ⟨hne, hadj⟩)
        · exact Or.inr (Or.inr ⟨trivial, rfl⟩)
        · left
          refine ⟨hadj, ?_⟩
          rintro (⟨h, _⟩ | ⟨_, h⟩)
          · exact cfg.armA_ne_v _ h
          · exact hne h
    have hv_mem : cfg.v ∈ T.neighborFinset cfg.a0 :=
      (SimpleGraph.mem_neighborFinset T _ _).mpr cfg.adj_v_a0.symm
    have hb_not : cfg.bTip ∉ (T.neighborFinset cfg.a0).erase cfg.v := by
      intro h
      exact cfg.not_adj_bTip_a0 ((SimpleGraph.mem_neighborFinset T _ _).mp (Finset.mem_erase.mp h).2).symm
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
      hnf, Finset.card_insert_of_notMem hb_not, Finset.card_erase_of_mem hv_mem]
    have hpos : 1 ≤ (T.neighborFinset cfg.a0).card := Finset.card_pos.mpr ⟨_, hv_mem⟩
    omega
  have hdeg_other : ∀ u, u ≠ cfg.v → u ≠ cfg.bTip → u ≠ cfg.a0 →
      cfg.graftGraph.degree u = T.degree u := by
    intro u huv hub hua
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext w
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset, cfg.graftGraph_adj]
    simp only [ne_eq, Sym2.eq_iff]
    constructor
    · rintro (⟨h, _⟩ | (⟨h1, _⟩ | ⟨h1, _⟩))
      · exact h
      · exact (hub h1).elim
      · exact (hua h1).elim
    · intro h
      left
      refine ⟨h, ?_⟩
      rintro (⟨h1, _⟩ | ⟨h1, _⟩)
      · exact huv h1
      · exact hua h1
  -- Compare leaf sets: `leaves(T') = leaves(T).erase bTip`
  have hleaves : Finset.univ.filter (fun u : V => cfg.graftGraph.degree u = 1) =
      (Finset.univ.filter (fun u : V => T.degree u = 1)).erase cfg.bTip := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases huv : u = cfg.v
    · subst huv; omega
    · by_cases hub : u = cfg.bTip
      · subst hub; simp [hdeg_bTip_T']
      · by_cases hua : u = cfg.a0
        · subst hua; simp [hdeg_a0, hub]
        · simp [hdeg_other u huv hub hua, hub]
  have hb_leaf : cfg.bTip ∈ Finset.univ.filter (fun u : V => T.degree u = 1) := by
    simp [hdeg_bTip_T]
  unfold leafCount
  rw [hleaves, Finset.card_erase_of_mem hb_leaf]
  have hpos : 1 ≤ (Finset.univ.filter (fun u : V => T.degree u = 1)).card :=
    Finset.card_pos.mpr ⟨_, hb_leaf⟩
  omega

/-! ### Exact distance identities in `T` and `T'` -/

lemma dist_A_A_T (hT : T.IsTree) (i k : Fin cfg.a) :
    T.dist (cfg.armA i) (cfg.armA k) = Int.natAbs ((i.val : ℤ) - (k.val : ℤ)) := by
  by_cases hik : i.val ≤ k.val
  · let p : T.Walk (cfg.armA i) (cfg.armA k) :=
      Walk.copy (cfg.walkArmA_aux T cfg.hstepA_T (k.val - i.val) i.val (by omega))
        (by congr 1) (by congr 1; apply Fin.ext; dsimp; omega)
    have hp : p.IsPath := (Walk.isPath_copy _ _ _).mpr (cfg.walkArmA_aux_isPath T cfg.hstepA_T _ _ _)
    rw [dist_eq_length_of_isPath hT hp, Walk.length_copy, cfg.walkArmA_aux_length]
    omega
  · rw [SimpleGraph.dist_comm]
    let p : T.Walk (cfg.armA k) (cfg.armA i) :=
      Walk.copy (cfg.walkArmA_aux T cfg.hstepA_T (i.val - k.val) k.val (by omega))
        (by congr 1) (by congr 1; apply Fin.ext; dsimp; omega)
    have hp : p.IsPath := (Walk.isPath_copy _ _ _).mpr (cfg.walkArmA_aux_isPath T cfg.hstepA_T _ _ _)
    rw [dist_eq_length_of_isPath hT hp, Walk.length_copy, cfg.walkArmA_aux_length]
    omega

lemma dist_A_A_T' (hT : T.IsTree) (i k : Fin cfg.a) :
    cfg.graftGraph.dist (cfg.armA i) (cfg.armA k) = Int.natAbs ((i.val : ℤ) - (k.val : ℤ)) := by
  have hT' := cfg.graft_isTree hT
  by_cases hik : i.val ≤ k.val
  · let p : cfg.graftGraph.Walk (cfg.armA i) (cfg.armA k) :=
      Walk.copy (cfg.walkArmA_aux cfg.graftGraph cfg.hstepA_T' (k.val - i.val) i.val (by omega))
        (by congr 1) (by congr 1; apply Fin.ext; dsimp; omega)
    have hp : p.IsPath := (Walk.isPath_copy _ _ _).mpr
      (cfg.walkArmA_aux_isPath cfg.graftGraph cfg.hstepA_T' _ _ _)
    rw [dist_eq_length_of_isPath hT' hp, Walk.length_copy, cfg.walkArmA_aux_length]
    omega
  · rw [SimpleGraph.dist_comm]
    let p : cfg.graftGraph.Walk (cfg.armA k) (cfg.armA i) :=
      Walk.copy (cfg.walkArmA_aux cfg.graftGraph cfg.hstepA_T' (i.val - k.val) k.val (by omega))
        (by congr 1) (by congr 1; apply Fin.ext; dsimp; omega)
    have hp : p.IsPath := (Walk.isPath_copy _ _ _).mpr
      (cfg.walkArmA_aux_isPath cfg.graftGraph cfg.hstepA_T' _ _ _)
    rw [dist_eq_length_of_isPath hT' hp, Walk.length_copy, cfg.walkArmA_aux_length]
    omega

lemma dist_B_B_T (hT : T.IsTree) (j k : Fin cfg.b) :
    T.dist (cfg.armB j) (cfg.armB k) = Int.natAbs ((j.val : ℤ) - (k.val : ℤ)) := by
  by_cases hjk : j.val ≤ k.val
  · let p : T.Walk (cfg.armB j) (cfg.armB k) :=
      Walk.copy (cfg.walkArmB_aux T cfg.hstepB_T (k.val - j.val) j.val (by omega))
        (by congr 1) (by congr 1; apply Fin.ext; dsimp; omega)
    have hp : p.IsPath := (Walk.isPath_copy _ _ _).mpr (cfg.walkArmB_aux_isPath T cfg.hstepB_T _ _ _)
    rw [dist_eq_length_of_isPath hT hp, Walk.length_copy, cfg.walkArmB_aux_length]
    omega
  · rw [SimpleGraph.dist_comm]
    let p : T.Walk (cfg.armB k) (cfg.armB j) :=
      Walk.copy (cfg.walkArmB_aux T cfg.hstepB_T (j.val - k.val) k.val (by omega))
        (by congr 1) (by congr 1; apply Fin.ext; dsimp; omega)
    have hp : p.IsPath := (Walk.isPath_copy _ _ _).mpr (cfg.walkArmB_aux_isPath T cfg.hstepB_T _ _ _)
    rw [dist_eq_length_of_isPath hT hp, Walk.length_copy, cfg.walkArmB_aux_length]
    omega

lemma dist_B_B_T' (hT : T.IsTree) (j k : Fin cfg.b) :
    cfg.graftGraph.dist (cfg.armB j) (cfg.armB k) = Int.natAbs ((j.val : ℤ) - (k.val : ℤ)) := by
  have hT' := cfg.graft_isTree hT
  by_cases hjk : j.val ≤ k.val
  · let p : cfg.graftGraph.Walk (cfg.armB j) (cfg.armB k) :=
      Walk.copy (cfg.walkArmB_aux cfg.graftGraph cfg.hstepB_T' (k.val - j.val) j.val (by omega))
        (by congr 1) (by congr 1; apply Fin.ext; dsimp; omega)
    have hp : p.IsPath := (Walk.isPath_copy _ _ _).mpr
      (cfg.walkArmB_aux_isPath cfg.graftGraph cfg.hstepB_T' _ _ _)
    rw [dist_eq_length_of_isPath hT' hp, Walk.length_copy, cfg.walkArmB_aux_length]
    omega
  · rw [SimpleGraph.dist_comm]
    let p : cfg.graftGraph.Walk (cfg.armB k) (cfg.armB j) :=
      Walk.copy (cfg.walkArmB_aux cfg.graftGraph cfg.hstepB_T' (j.val - k.val) k.val (by omega))
        (by congr 1) (by congr 1; apply Fin.ext; dsimp; omega)
    have hp : p.IsPath := (Walk.isPath_copy _ _ _).mpr
      (cfg.walkArmB_aux_isPath cfg.graftGraph cfg.hstepB_T' _ _ _)
    rw [dist_eq_length_of_isPath hT' hp, Walk.length_copy, cfg.walkArmB_aux_length]
    omega

lemma dist_C_C_T' (hT : T.IsTree) {z₁ z₂ : V} (hz₁ : z₁ ∈ cfg.setC) (hz₂ : z₂ ∈ cfg.setC) :
    cfg.graftGraph.dist z₁ z₂ = T.dist z₁ z₂ := by
  obtain ⟨p, hp, _⟩ := hT.existsUnique_path z₁ z₂
  have hC := cfg.path_C_stays_in_C hz₁ hz₂ hp
  rw [dist_eq_length_of_isPath (cfg.graft_isTree hT) (cfg.liftWalkC_isPath hp hC),
    cfg.liftWalkC_length p hC, dist_eq_length_of_isPath hT hp]

lemma dist_B_C_T (hT : T.IsTree) (j : Fin cfg.b) {z : V} (hz : z ∈ cfg.setC) :
    T.dist (cfg.armB j) z = (j.val + 1) + T.dist cfg.v z := by
  obtain ⟨q, hq, _⟩ := hT.existsUnique_path cfg.v z
  have hqC := cfg.path_C_stays_in_C cfg.mem_setC_v hz hq
  let p0 : T.Walk (cfg.armB ⟨0, cfg.hb⟩) (cfg.armB j) :=
    Walk.copy (cfg.walkArmB_aux T cfg.hstepB_T j.val 0 (by omega))
      (by congr 1) (by congr 1; apply Fin.ext; simp)
  have hp0 : p0.IsPath := (Walk.isPath_copy _ _ _).mpr (cfg.walkArmB_aux_isPath T cfg.hstepB_T _ _ _)
  let p1 : T.Walk cfg.v (cfg.armB j) := p0.cons cfg.adj_v_b0_T
  have hp1 : p1.IsPath := by
    rw [Walk.cons_isPath_iff]
    refine ⟨hp0, fun hmem => ?_⟩
    rw [Walk.support_copy] at hmem
    obtain ⟨t, ht, _, _⟩ := cfg.walkArmB_aux_support T cfg.hstepB_T j.val 0 (by omega) _ hmem
    exact cfg.armB_ne_v t ht.symm
  have hcomb : (p1.reverse.append q).IsPath := by
    apply isPath_append_of_disjoint hp1.reverse hq
    intro u hu1 hu2
    rw [Walk.support_reverse, List.mem_reverse] at hu1
    simp only [p1, Walk.support_cons, List.mem_cons] at hu1
    rcases hu1 with rfl | hu1'
    · rfl
    · rw [Walk.support_copy] at hu1'
      obtain ⟨t, rfl, _, _⟩ := cfg.walkArmB_aux_support T cfg.hstepB_T j.val 0 (by omega) _ hu1'
      have := hqC _ hu2
      simp [setC, setB] at this
  rw [dist_eq_length_of_isPath hT hcomb, Walk.length_append, Walk.length_reverse,
    Walk.length_cons, Walk.length_copy, cfg.walkArmB_aux_length, dist_eq_length_of_isPath hT hq]

lemma dist_B_C_T' (hT : T.IsTree) (j : Fin cfg.b) {z : V} (hz : z ∈ cfg.setC) :
    cfg.graftGraph.dist (cfg.armB j) z = (j.val + 1) + T.dist cfg.v z := by
  obtain ⟨q, hq, _⟩ := hT.existsUnique_path cfg.v z
  have hqC := cfg.path_C_stays_in_C cfg.mem_setC_v hz hq
  let q' := cfg.liftWalkC q hqC
  let p0 : cfg.graftGraph.Walk (cfg.armB ⟨0, cfg.hb⟩) (cfg.armB j) :=
    Walk.copy (cfg.walkArmB_aux cfg.graftGraph cfg.hstepB_T' j.val 0 (by omega))
      (by congr 1) (by congr 1; apply Fin.ext; simp)
  have hp0 : p0.IsPath := (Walk.isPath_copy _ _ _).mpr
    (cfg.walkArmB_aux_isPath cfg.graftGraph cfg.hstepB_T' _ _ _)
  let p1 : cfg.graftGraph.Walk cfg.v (cfg.armB j) := p0.cons cfg.adj_v_b0_T'
  have hp1 : p1.IsPath := by
    rw [Walk.cons_isPath_iff]
    refine ⟨hp0, fun hmem => ?_⟩
    rw [Walk.support_copy] at hmem
    obtain ⟨t, ht, _, _⟩ := cfg.walkArmB_aux_support cfg.graftGraph cfg.hstepB_T' j.val 0 (by omega) _ hmem
    exact cfg.armB_ne_v t ht.symm
  have hcomb : (p1.reverse.append q').IsPath := by
    apply isPath_append_of_disjoint hp1.reverse (cfg.liftWalkC_isPath hq hqC)
    intro u hu1 hu2
    rw [Walk.support_reverse, List.mem_reverse] at hu1
    simp only [p1, Walk.support_cons, List.mem_cons] at hu1
    rcases hu1 with rfl | hu1'
    · rfl
    · rw [Walk.support_copy] at hu1'
      obtain ⟨t, rfl, _, _⟩ := cfg.walkArmB_aux_support cfg.graftGraph cfg.hstepB_T' j.val 0 (by omega) _ hu1'
      rw [cfg.liftWalkC_support] at hu2
      have := hqC _ hu2
      simp [setC, setB] at this
  rw [dist_eq_length_of_isPath (cfg.graft_isTree hT) hcomb, Walk.length_append, Walk.length_reverse,
    Walk.length_cons, Walk.length_copy, cfg.walkArmB_aux_length, cfg.liftWalkC_length,
    dist_eq_length_of_isPath hT hq]

private lemma adj_v_armA0 : T.Adj cfg.v (cfg.armA ⟨0, cfg.ha⟩) := cfg.adj_v_a0

private lemma adj_armA0_bTip_T' : cfg.graftGraph.Adj (cfg.armA ⟨0, cfg.ha⟩) cfg.bTip :=
  cfg.adj_bTip_a0_T'.symm

lemma dist_A_C_T (hT : T.IsTree) (i : Fin cfg.a) {z : V} (hz : z ∈ cfg.setC) :
    T.dist (cfg.armA i) z = (i.val + 1) + T.dist cfg.v z := by
  obtain ⟨q, hq, _⟩ := hT.existsUnique_path cfg.v z
  have hqC := cfg.path_C_stays_in_C cfg.mem_setC_v hz hq
  let p0 : T.Walk (cfg.armA ⟨0, cfg.ha⟩) (cfg.armA i) :=
    Walk.copy (cfg.walkArmA_aux T cfg.hstepA_T i.val 0 (by omega))
      (by congr 1) (by congr 1; apply Fin.ext; simp)
  have hp0 : p0.IsPath := (Walk.isPath_copy _ _ _).mpr (cfg.walkArmA_aux_isPath T cfg.hstepA_T _ _ _)
  let p1 : T.Walk cfg.v (cfg.armA i) := Walk.cons cfg.adj_v_armA0 p0
  have hp1 : p1.IsPath := by
    dsimp only [p1]
    rw [Walk.cons_isPath_iff]
    refine ⟨hp0, fun hmem => ?_⟩
    dsimp only [p0] at hmem
    rw [Walk.support_copy] at hmem
    obtain ⟨t, ht, _, _⟩ := cfg.walkArmA_aux_support T cfg.hstepA_T i.val 0 (by omega) _ hmem
    exact cfg.armA_ne_v t ht.symm
  have hcomb : (p1.reverse.append q).IsPath := by
    apply isPath_append_of_disjoint hp1.reverse hq
    intro u hu1 hu2
    rw [Walk.support_reverse, List.mem_reverse] at hu1
    dsimp only [p1] at hu1
    rw [Walk.support_cons, List.mem_cons] at hu1
    rcases hu1 with rfl | hu1'
    · rfl
    · dsimp only [p0] at hu1'
      rw [Walk.support_copy] at hu1'
      obtain ⟨t, rfl, _, _⟩ := cfg.walkArmA_aux_support T cfg.hstepA_T i.val 0 (by omega) _ hu1'
      have := hqC _ hu2
      simp [setC, setA] at this
  rw [dist_eq_length_of_isPath hT hcomb, Walk.length_append, Walk.length_reverse]
  dsimp only [p1]
  rw [Walk.length_cons]
  dsimp only [p0]
  rw [Walk.length_copy, cfg.walkArmA_aux_length, dist_eq_length_of_isPath hT hq]

lemma dist_A_B_T (hT : T.IsTree) (i : Fin cfg.a) (j : Fin cfg.b) :
    T.dist (cfg.armA i) (cfg.armB j) = (i.val + 1) + (j.val + 1) := by
  let pA0 : T.Walk (cfg.armA ⟨0, cfg.ha⟩) (cfg.armA i) :=
    Walk.copy (cfg.walkArmA_aux T cfg.hstepA_T i.val 0 (by omega))
      (by congr 1) (by congr 1; apply Fin.ext; simp)
  have hpA0 : pA0.IsPath := (Walk.isPath_copy _ _ _).mpr (cfg.walkArmA_aux_isPath T cfg.hstepA_T _ _ _)
  let pA : T.Walk cfg.v (cfg.armA i) := Walk.cons cfg.adj_v_armA0 pA0
  have hpA : pA.IsPath := by
    dsimp only [pA]
    rw [Walk.cons_isPath_iff]
    refine ⟨hpA0, fun hmem => ?_⟩
    dsimp only [pA0] at hmem
    rw [Walk.support_copy] at hmem
    obtain ⟨t, ht, _, _⟩ := cfg.walkArmA_aux_support T cfg.hstepA_T i.val 0 (by omega) _ hmem
    exact cfg.armA_ne_v t ht.symm
  let pB0 : T.Walk (cfg.armB ⟨0, cfg.hb⟩) (cfg.armB j) :=
    Walk.copy (cfg.walkArmB_aux T cfg.hstepB_T j.val 0 (by omega))
      (by congr 1) (by congr 1; apply Fin.ext; simp)
  have hpB0 : pB0.IsPath := (Walk.isPath_copy _ _ _).mpr (cfg.walkArmB_aux_isPath T cfg.hstepB_T _ _ _)
  let pB : T.Walk cfg.v (cfg.armB j) := Walk.cons cfg.adj_v_b0_T pB0
  have hpB : pB.IsPath := by
    dsimp only [pB]
    rw [Walk.cons_isPath_iff]
    refine ⟨hpB0, fun hmem => ?_⟩
    dsimp only [pB0] at hmem
    rw [Walk.support_copy] at hmem
    obtain ⟨t, ht, _, _⟩ := cfg.walkArmB_aux_support T cfg.hstepB_T j.val 0 (by omega) _ hmem
    exact cfg.armB_ne_v t ht.symm
  have hcomb : (pA.reverse.append pB).IsPath := by
    apply isPath_append_of_disjoint hpA.reverse hpB
    intro u hu1 hu2
    rw [Walk.support_reverse, List.mem_reverse] at hu1
    dsimp only [pA] at hu1
    dsimp only [pB] at hu2
    rw [Walk.support_cons, List.mem_cons] at hu1 hu2
    rcases hu1 with rfl | hu1'
    · rfl
    · rcases hu2 with rfl | hu2'
      · rfl
      · dsimp only [pA0, pB0] at hu1' hu2'
        rw [Walk.support_copy] at hu1' hu2'
        obtain ⟨t1, rfl, _, _⟩ := cfg.walkArmA_aux_support T cfg.hstepA_T i.val 0 (by omega) _ hu1'
        obtain ⟨t2, ht2, _, _⟩ := cfg.walkArmB_aux_support T cfg.hstepB_T j.val 0 (by omega) _ hu2'
        exact (cfg.armA_ne_armB t1 t2 ht2).elim
  rw [dist_eq_length_of_isPath hT hcomb, Walk.length_append, Walk.length_reverse]
  dsimp only [pA, pB]
  rw [Walk.length_cons, Walk.length_cons]
  dsimp only [pA0, pB0]
  rw [Walk.length_copy, Walk.length_copy, cfg.walkArmA_aux_length, cfg.walkArmB_aux_length]

lemma dist_A_B_T' (hT : T.IsTree) (i : Fin cfg.a) (j : Fin cfg.b) :
    cfg.graftGraph.dist (cfg.armA i) (cfg.armB j) = i.val + cfg.b - j.val := by
  let pA : cfg.graftGraph.Walk (cfg.armA ⟨0, cfg.ha⟩) (cfg.armA i) :=
    Walk.copy (cfg.walkArmA_aux cfg.graftGraph cfg.hstepA_T' i.val 0 (by omega))
      (by congr 1) (by congr 1; apply Fin.ext; simp)
  have hpA : pA.IsPath := (Walk.isPath_copy _ _ _).mpr
    (cfg.walkArmA_aux_isPath cfg.graftGraph cfg.hstepA_T' _ _ _)
  let pB : cfg.graftGraph.Walk (cfg.armB j) cfg.bTip :=
    Walk.copy (cfg.walkArmB_aux cfg.graftGraph cfg.hstepB_T' (cfg.b - 1 - j.val) j.val (by omega))
      (by congr 1) (by congr 1; apply Fin.ext; dsimp [bTip]; omega)
  have hpB : pB.IsPath := (Walk.isPath_copy _ _ _).mpr
    (cfg.walkArmB_aux_isPath cfg.graftGraph cfg.hstepB_T' _ _ _)
  let pLink : cfg.graftGraph.Walk (cfg.armA ⟨0, cfg.ha⟩) (cfg.armB j) :=
    Walk.cons cfg.adj_armA0_bTip_T' pB.reverse
  have hpLink : pLink.IsPath := by
    dsimp only [pLink]
    rw [Walk.cons_isPath_iff]
    refine ⟨hpB.reverse, fun hmem => ?_⟩
    dsimp only [pB] at hmem
    rw [Walk.support_reverse, List.mem_reverse, Walk.support_copy] at hmem
    obtain ⟨t, ht, _, _⟩ := cfg.walkArmB_aux_support cfg.graftGraph cfg.hstepB_T' _ _ _ _ hmem
    exact cfg.armA_ne_armB _ t ht
  have hcomb : (pA.reverse.append pLink).IsPath := by
    apply isPath_append_of_disjoint hpA.reverse hpLink
    intro u hu1 hu2
    dsimp only [pA] at hu1
    rw [Walk.support_reverse, List.mem_reverse, Walk.support_copy] at hu1
    dsimp only [pLink] at hu2
    rw [Walk.support_cons, List.mem_cons] at hu2
    rcases hu2 with rfl | hu2'
    · rfl
    · dsimp only [pB] at hu2'
      rw [Walk.support_reverse, List.mem_reverse, Walk.support_copy] at hu2'
      obtain ⟨t1, rfl, _, _⟩ := cfg.walkArmA_aux_support cfg.graftGraph cfg.hstepA_T' _ _ _ _ hu1
      obtain ⟨t2, ht2, _, _⟩ := cfg.walkArmB_aux_support cfg.graftGraph cfg.hstepB_T' _ _ _ _ hu2'
      exact (cfg.armA_ne_armB t1 t2 ht2).elim
  rw [dist_eq_length_of_isPath (cfg.graft_isTree hT) hcomb, Walk.length_append, Walk.length_reverse]
  dsimp only [pLink]
  rw [Walk.length_cons, Walk.length_reverse]
  dsimp only [pA, pB]
  rw [Walk.length_copy, Walk.length_copy, cfg.walkArmA_aux_length, cfg.walkArmB_aux_length]
  omega

lemma dist_A_C_T' (hT : T.IsTree) (i : Fin cfg.a) {z : V} (hz : z ∈ cfg.setC) :
    cfg.graftGraph.dist (cfg.armA i) z = (i.val + 1) + cfg.b + T.dist cfg.v z := by
  obtain ⟨q, hq, _⟩ := hT.existsUnique_path cfg.v z
  have hqC := cfg.path_C_stays_in_C cfg.mem_setC_v hz hq
  let q' := cfg.liftWalkC q hqC
  let pA : cfg.graftGraph.Walk (cfg.armA ⟨0, cfg.ha⟩) (cfg.armA i) :=
    Walk.copy (cfg.walkArmA_aux cfg.graftGraph cfg.hstepA_T' i.val 0 (by omega))
      (by congr 1) (by congr 1; apply Fin.ext; simp)
  have hpA : pA.IsPath := (Walk.isPath_copy _ _ _).mpr
    (cfg.walkArmA_aux_isPath cfg.graftGraph cfg.hstepA_T' _ _ _)
  let pB0 : cfg.graftGraph.Walk (cfg.armB ⟨0, cfg.hb⟩) cfg.bTip :=
    Walk.copy (cfg.walkArmB_aux cfg.graftGraph cfg.hstepB_T' (cfg.b - 1) 0 (by have := cfg.hb; omega))
      (by congr 1) (by congr 1; apply Fin.ext; dsimp [bTip]; have := cfg.hb; omega)
  have hpB0 : pB0.IsPath := (Walk.isPath_copy _ _ _).mpr
    (cfg.walkArmB_aux_isPath cfg.graftGraph cfg.hstepB_T' _ _ _)
  let pB : cfg.graftGraph.Walk cfg.v cfg.bTip := Walk.cons cfg.adj_v_b0_T' pB0
  have hpB : pB.IsPath := by
    dsimp only [pB]
    rw [Walk.cons_isPath_iff]
    refine ⟨hpB0, fun hmem => ?_⟩
    dsimp only [pB0] at hmem
    rw [Walk.support_copy] at hmem
    obtain ⟨t, ht, _, _⟩ := cfg.walkArmB_aux_support cfg.graftGraph cfg.hstepB_T' _ _ _ _ hmem
    exact cfg.armB_ne_v t ht.symm
  let pBC : cfg.graftGraph.Walk cfg.bTip z := pB.reverse.append q'
  have hpBC : pBC.IsPath := by
    apply isPath_append_of_disjoint hpB.reverse (cfg.liftWalkC_isPath hq hqC)
    intro u hu1 hu2
    rw [Walk.support_reverse, List.mem_reverse] at hu1
    dsimp only [pB] at hu1
    rw [Walk.support_cons, List.mem_cons] at hu1
    rcases hu1 with rfl | hu1'
    · rfl
    · dsimp only [pB0] at hu1'
      rw [Walk.support_copy] at hu1'
      obtain ⟨t, rfl, _, _⟩ := cfg.walkArmB_aux_support cfg.graftGraph cfg.hstepB_T' _ _ _ _ hu1'
      rw [cfg.liftWalkC_support] at hu2
      have := hqC _ hu2
      simp [setC, setB] at this
  let pLink : cfg.graftGraph.Walk (cfg.armA ⟨0, cfg.ha⟩) z :=
    Walk.cons cfg.adj_armA0_bTip_T' pBC
  have hpLink : pLink.IsPath := by
    dsimp only [pLink]
    rw [Walk.cons_isPath_iff]
    refine ⟨hpBC, fun hmem => ?_⟩
    rw [Walk.mem_support_append_iff] at hmem
    rcases hmem with h1 | h2
    · rw [Walk.support_reverse, List.mem_reverse] at h1
      dsimp only [pB] at h1
      rw [Walk.support_cons, List.mem_cons] at h1
      rcases h1 with h1 | h1'
      · exact cfg.armA_ne_v _ h1
      · dsimp only [pB0] at h1'
        rw [Walk.support_copy] at h1'
        obtain ⟨t, ht, _, _⟩ := cfg.walkArmB_aux_support cfg.graftGraph cfg.hstepB_T' _ _ _ _ h1'
        exact cfg.armA_ne_armB _ t ht
    · rw [cfg.liftWalkC_support] at h2
      have := hqC _ h2
      simp [setC, setA] at this
  have hcomb : (pA.reverse.append pLink).IsPath := by
    apply isPath_append_of_disjoint hpA.reverse hpLink
    intro u hu1 hu2
    dsimp only [pA] at hu1
    rw [Walk.support_reverse, List.mem_reverse, Walk.support_copy] at hu1
    dsimp only [pLink] at hu2
    rw [Walk.support_cons, List.mem_cons] at hu2
    rcases hu2 with rfl | hu2'
    · rfl
    · obtain ⟨t1, rfl, _, _⟩ := cfg.walkArmA_aux_support cfg.graftGraph cfg.hstepA_T' _ _ _ _ hu1
      rw [Walk.mem_support_append_iff] at hu2'
      rcases hu2' with h1 | h2
      · rw [Walk.support_reverse, List.mem_reverse] at h1
        dsimp only [pB] at h1
        rw [Walk.support_cons, List.mem_cons] at h1
        rcases h1 with h1 | h1'
        · exact (cfg.armA_ne_v t1 h1).elim
        · dsimp only [pB0] at h1'
          rw [Walk.support_copy] at h1'
          obtain ⟨t2, ht2, _, _⟩ := cfg.walkArmB_aux_support cfg.graftGraph cfg.hstepB_T' _ _ _ _ h1'
          exact (cfg.armA_ne_armB t1 t2 ht2).elim
      · rw [cfg.liftWalkC_support] at h2
        have := hqC _ h2
        simp [setC, setA] at this
  rw [dist_eq_length_of_isPath (cfg.graft_isTree hT) hcomb, Walk.length_append, Walk.length_reverse]
  dsimp only [pLink, pBC, pB]
  rw [Walk.length_cons, Walk.length_append, Walk.length_reverse, Walk.length_cons]
  dsimp only [pA, pB0]
  rw [Walk.length_copy, Walk.length_copy, cfg.walkArmA_aux_length, cfg.walkArmB_aux_length,
    cfg.liftWalkC_length, dist_eq_length_of_isPath hT hq]
  have := cfg.hb
  omega

/-! ### Exact transmission formulas under grafting -/

/-- Partition any sum over `V` into sums over `Fin a` (`armA`), `Fin b` (`armB`), and `setC`. -/
lemma sum_univ_partition (f : V → ℤ) :
    ∑ u : V, f u =
      (∑ i : Fin cfg.a, f (cfg.armA i)) +
      (∑ j : Fin cfg.b, f (cfg.armB j)) +
      (∑ z ∈ cfg.setC, f z) := by
  have hunion : (Finset.univ : Finset V) = (cfg.setA ∪ cfg.setB) ∪ cfg.setC := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_union, setC, Finset.mem_sdiff, true_and, true_iff]
    tauto
  have hdisj1 : Disjoint (cfg.setA ∪ cfg.setB) cfg.setC := by
    rw [setC]; exact Finset.disjoint_sdiff
  have hdisjAB : Disjoint cfg.setA cfg.setB := cfg.hdisjAB
  rw [hunion, Finset.sum_union hdisj1, Finset.sum_union hdisjAB]
  congr 1; congr 1
  · rw [setA, Finset.sum_image (fun _ _ _ _ h => cfg.armA.injective h)]
  · rw [setB, Finset.sum_image (fun _ _ _ _ h => cfg.armB.injective h)]

private lemma sum_fin_val_plus_one (k : ℕ) :
    2 * ∑ i : Fin k, ((i.val : ℤ) + 1) = (k : ℤ) * ((k : ℤ) + 1) := by
  have hbij : ∑ i : Fin k, ((i.val : ℤ) + 1) = ∑ j ∈ Finset.Icc 1 k, (j : ℤ) := by
    apply Finset.sum_nbij (fun i : Fin k => i.val + 1)
    · intro i _; rw [Finset.mem_Icc]; omega
    · intro i₁ _ i₂ _ h; dsimp only at h; exact Fin.ext (by omega)
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_Icc] at hj
      refine ⟨⟨j - 1, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      dsimp only; omega
    · intro i _; push_cast; rfl
  rw [hbij, sum_Icc_linear]

private lemma sum_fin_abs_sub_minus_val (k : ℕ) (i : Fin k) :
    ∑ t : Fin k, ((Int.natAbs ((i.val : ℤ) - (t.val : ℤ)) : ℤ) - ((t.val : ℤ) + 1)) =
      ((i.val : ℤ) + 1) * (((i.val : ℤ) + 1) - (k : ℤ) - 1) := by
  have hsplit : ∑ t : Fin k, ((Int.natAbs ((i.val : ℤ) - (t.val : ℤ)) : ℤ) - ((t.val : ℤ) + 1)) =
      (∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val ≤ i.val),
        ((i.val : ℤ) - 2 * (t.val : ℤ) - 1)) +
      (∑ t ∈ Finset.univ.filter (fun t : Fin k => i.val < t.val),
        (-((i.val : ℤ) + 1))) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t : Fin k => t.val ≤ i.val)]
    congr 1
    · apply Finset.sum_congr rfl
      intro t ht
      have hle : t.val ≤ i.val := (Finset.mem_filter.mp ht).2
      have habs : (Int.natAbs ((i.val : ℤ) - (t.val : ℤ)) : ℤ) = (i.val : ℤ) - (t.val : ℤ) := by omega
      omega
    · have hf : Finset.univ.filter (fun t : Fin k => ¬ t.val ≤ i.val) =
          Finset.univ.filter (fun t : Fin k => i.val < t.val) := by
        ext t; simp
      rw [hf]
      apply Finset.sum_congr rfl
      intro t ht
      have hlt : i.val < t.val := (Finset.mem_filter.mp ht).2
      have habs : (Int.natAbs ((i.val : ℤ) - (t.val : ℤ)) : ℤ) = (t.val : ℤ) - (i.val : ℤ) := by omega
      omega
  rw [hsplit]
  have h1 : ∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val ≤ i.val),
      ((i.val : ℤ) - 2 * (t.val : ℤ) - 1) = -((i.val : ℤ) + 1) := by
    have hbij : ∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val ≤ i.val),
        ((i.val : ℤ) - 2 * (t.val : ℤ) - 1) =
        ∑ s ∈ Finset.Icc 1 (i.val + 1), ((i.val : ℤ) + 1 - 2 * (s : ℤ)) := by
      apply Finset.sum_nbij (fun t : Fin k => t.val + 1)
      · intro t ht; rw [Finset.mem_filter] at ht; rw [Finset.mem_Icc]; omega
      · intro t₁ _ t₂ _ h; dsimp only at h; exact Fin.ext (by omega)
      · intro s hs
        rw [Finset.mem_coe, Finset.mem_Icc] at hs
        have hilt := i.isLt
        refine ⟨⟨s - 1, by omega⟩, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩), ?_⟩
        dsimp only; omega
      · intro t _; push_cast; ring
    rw [hbij, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, ← Finset.mul_sum,
      sum_Icc_linear]
    have hc : i.val + 1 + 1 - 1 = i.val + 1 := by omega
    rw [hc, nsmul_eq_mul]
    push_cast; ring
  have h2 : ∑ t ∈ Finset.univ.filter (fun t : Fin k => i.val < t.val),
      (-((i.val : ℤ) + 1)) = ((k : ℤ) - ((i.val : ℤ) + 1)) * (-((i.val : ℤ) + 1)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun t : Fin k => i.val < t.val)).card = k - (i.val + 1) := by
      have hbij : (Finset.univ.filter (fun t : Fin k => i.val < t.val)).card =
          (Finset.Icc (i.val + 1) (k - 1)).card := by
        apply Finset.card_nbij (fun t : Fin k => t.val)
        · intro t ht
          have ht' := (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
          dsimp only
          exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by have := t.isLt; omega⟩)
        · intro t₁ _ t₂ _ h; exact Fin.ext h
        · intro s hs
          obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.mp (Finset.mem_coe.mp hs)
          have hilt := i.isLt
          exact ⟨⟨s, by omega⟩, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩), rfl⟩
      rw [hbij, Nat.card_Icc]; have := i.isLt; omega
    rw [hcard]
    have hsub : ((k - (i.val + 1) : ℕ) : ℤ) = (k : ℤ) - ((i.val : ℤ) + 1) := by omega
    rw [hsub]
  rw [h1, h2]
  ring

lemma delta_trans_A (hT : T.IsTree) (i : Fin cfg.a) :
    (transmission cfg.graftGraph (cfg.armA i) : ℤ) - (transmission T (cfg.armA i) : ℤ) =
      (cfg.b : ℤ) * (cfg.r : ℤ) := by
  unfold transmission
  push_cast
  rw [← Finset.sum_sub_distrib, cfg.sum_univ_partition]
  have hA : ∑ k : Fin cfg.a,
      ((cfg.graftGraph.dist (cfg.armA i) (cfg.armA k) : ℤ) - (T.dist (cfg.armA i) (cfg.armA k) : ℤ)) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    rw [cfg.dist_A_A_T' hT, cfg.dist_A_A_T hT, sub_self]
  have hB : ∑ j : Fin cfg.b,
      ((cfg.graftGraph.dist (cfg.armA i) (cfg.armB j) : ℤ) - (T.dist (cfg.armA i) (cfg.armB j) : ℤ)) =
      -(cfg.b : ℤ) := by
    have hterm : ∀ j : Fin cfg.b,
        ((cfg.graftGraph.dist (cfg.armA i) (cfg.armB j) : ℤ) - (T.dist (cfg.armA i) (cfg.armB j) : ℤ)) =
          (cfg.b : ℤ) - 2 * ((j.val : ℤ) + 1) := by
      intro j
      rw [cfg.dist_A_B_T' hT, cfg.dist_A_B_T hT]
      have hj : j.val < cfg.b := j.isLt
      omega
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum, sum_fin_val_plus_one]
    simp only [nsmul_eq_mul]; ring
  have hC : ∑ z ∈ cfg.setC,
      ((cfg.graftGraph.dist (cfg.armA i) z : ℤ) - (T.dist (cfg.armA i) z : ℤ)) =
      (cfg.b : ℤ) * ((cfg.r : ℤ) + 1) := by
    have hterm : ∀ z ∈ cfg.setC,
        ((cfg.graftGraph.dist (cfg.armA i) z : ℤ) - (T.dist (cfg.armA i) z : ℤ)) = (cfg.b : ℤ) := by
      intro z hz
      rw [cfg.dist_A_C_T' hT i hz, cfg.dist_A_C_T hT i hz]; omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, cfg.card_setC_eq, nsmul_eq_mul]
    push_cast; ring
  rw [hA, hB, hC]; ring

lemma delta_trans_B (hT : T.IsTree) (j : Fin cfg.b) :
    (transmission cfg.graftGraph (cfg.armB j) : ℤ) - (transmission T (cfg.armB j) : ℤ) =
      (cfg.a : ℤ) * ((cfg.b : ℤ) - 2 * ((j.val : ℤ) + 1)) := by
  unfold transmission
  push_cast
  rw [← Finset.sum_sub_distrib, cfg.sum_univ_partition]
  have hA : ∑ i : Fin cfg.a,
      ((cfg.graftGraph.dist (cfg.armB j) (cfg.armA i) : ℤ) - (T.dist (cfg.armB j) (cfg.armA i) : ℤ)) =
      (cfg.a : ℤ) * ((cfg.b : ℤ) - 2 * ((j.val : ℤ) + 1)) := by
    have hterm : ∀ i : Fin cfg.a,
        ((cfg.graftGraph.dist (cfg.armB j) (cfg.armA i) : ℤ) - (T.dist (cfg.armB j) (cfg.armA i) : ℤ)) =
          (cfg.b : ℤ) - 2 * ((j.val : ℤ) + 1) := by
      intro i
      rw [SimpleGraph.dist_comm, SimpleGraph.dist_comm (u := cfg.armB j),
        cfg.dist_A_B_T' hT, cfg.dist_A_B_T hT]
      have hj : j.val < cfg.b := j.isLt
      omega
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hB : ∑ k : Fin cfg.b,
      ((cfg.graftGraph.dist (cfg.armB j) (cfg.armB k) : ℤ) - (T.dist (cfg.armB j) (cfg.armB k) : ℤ)) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    rw [cfg.dist_B_B_T' hT, cfg.dist_B_B_T hT, sub_self]
  have hC : ∑ z ∈ cfg.setC,
      ((cfg.graftGraph.dist (cfg.armB j) z : ℤ) - (T.dist (cfg.armB j) z : ℤ)) = 0 := by
    apply Finset.sum_eq_zero; intro z hz
    rw [cfg.dist_B_C_T' hT j hz, cfg.dist_B_C_T hT j hz, sub_self]
  rw [hA, hB, hC]; ring

lemma delta_trans_C (hT : T.IsTree) {z : V} (hz : z ∈ cfg.setC) :
    (transmission cfg.graftGraph z : ℤ) - (transmission T z : ℤ) =
      (cfg.a : ℤ) * (cfg.b : ℤ) := by
  unfold transmission
  push_cast
  rw [← Finset.sum_sub_distrib, cfg.sum_univ_partition]
  have hA : ∑ i : Fin cfg.a,
      ((cfg.graftGraph.dist z (cfg.armA i) : ℤ) - (T.dist z (cfg.armA i) : ℤ)) =
      (cfg.a : ℤ) * (cfg.b : ℤ) := by
    have hterm : ∀ i : Fin cfg.a,
        ((cfg.graftGraph.dist z (cfg.armA i) : ℤ) - (T.dist z (cfg.armA i) : ℤ)) = (cfg.b : ℤ) := by
      intro i
      rw [SimpleGraph.dist_comm, SimpleGraph.dist_comm (u := z),
        cfg.dist_A_C_T' hT i hz, cfg.dist_A_C_T hT i hz]; omega
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hB : ∑ j : Fin cfg.b,
      ((cfg.graftGraph.dist z (cfg.armB j) : ℤ) - (T.dist z (cfg.armB j) : ℤ)) = 0 := by
    apply Finset.sum_eq_zero; intro j _
    rw [SimpleGraph.dist_comm, SimpleGraph.dist_comm (u := z),
      cfg.dist_B_C_T' hT j hz, cfg.dist_B_C_T hT j hz, sub_self]
  have hC : ∑ w ∈ cfg.setC,
      ((cfg.graftGraph.dist z w : ℤ) - (T.dist z w : ℤ)) = 0 := by
    apply Finset.sum_eq_zero; intro w hw
    rw [cfg.dist_C_C_T' hT hz hw, sub_self]
  rw [hA, hB, hC]; ring

lemma trans_A_sub_v (hT : T.IsTree) (i : Fin cfg.a) :
    (transmission T (cfg.armA i) : ℤ) - (transmission T cfg.v : ℤ) =
      ((i.val : ℤ) + 1) * ((cfg.r : ℤ) + (cfg.b : ℤ) - (cfg.a : ℤ) + ((i.val : ℤ) + 1)) := by
  unfold transmission
  push_cast
  rw [← Finset.sum_sub_distrib, cfg.sum_univ_partition]
  have hA : ∑ t : Fin cfg.a, ((T.dist (cfg.armA i) (cfg.armA t) : ℤ) - (T.dist cfg.v (cfg.armA t) : ℤ)) =
      ((i.val : ℤ) + 1) * (((i.val : ℤ) + 1) - (cfg.a : ℤ) - 1) := by
    have hterm : ∀ t : Fin cfg.a,
        ((T.dist (cfg.armA i) (cfg.armA t) : ℤ) - (T.dist cfg.v (cfg.armA t) : ℤ)) =
          (Int.natAbs ((i.val : ℤ) - (t.val : ℤ)) : ℤ) - ((t.val : ℤ) + 1) := by
      intro t
      rw [cfg.dist_A_A_T hT, SimpleGraph.dist_comm, cfg.dist_A_C_T hT t cfg.mem_setC_v]
      simp
    rw [Finset.sum_congr rfl (fun t _ => hterm t), sum_fin_abs_sub_minus_val]
  have hB : ∑ j : Fin cfg.b, ((T.dist (cfg.armA i) (cfg.armB j) : ℤ) - (T.dist cfg.v (cfg.armB j) : ℤ)) =
      (cfg.b : ℤ) * ((i.val : ℤ) + 1) := by
    have hterm : ∀ j : Fin cfg.b,
        ((T.dist (cfg.armA i) (cfg.armB j) : ℤ) - (T.dist cfg.v (cfg.armB j) : ℤ)) = ((i.val : ℤ) + 1) := by
      intro j
      rw [cfg.dist_A_B_T hT, SimpleGraph.dist_comm, cfg.dist_B_C_T hT j cfg.mem_setC_v]
      simp
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hC : ∑ z ∈ cfg.setC, ((T.dist (cfg.armA i) z : ℤ) - (T.dist cfg.v z : ℤ)) =
      ((cfg.r : ℤ) + 1) * ((i.val : ℤ) + 1) := by
    have hterm : ∀ z ∈ cfg.setC, ((T.dist (cfg.armA i) z : ℤ) - (T.dist cfg.v z : ℤ)) = ((i.val : ℤ) + 1) := by
      intro z hz
      rw [cfg.dist_A_C_T hT i hz]; omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, cfg.card_setC_eq, nsmul_eq_mul]
    push_cast; ring
  rw [hA, hB, hC]; ring

lemma trans_B_sub_v (hT : T.IsTree) (j : Fin cfg.b) :
    (transmission T (cfg.armB j) : ℤ) - (transmission T cfg.v : ℤ) =
      ((j.val : ℤ) + 1) * ((cfg.r : ℤ) + (cfg.a : ℤ) - (cfg.b : ℤ) + ((j.val : ℤ) + 1)) := by
  unfold transmission
  push_cast
  rw [← Finset.sum_sub_distrib, cfg.sum_univ_partition]
  have hA : ∑ i : Fin cfg.a, ((T.dist (cfg.armB j) (cfg.armA i) : ℤ) - (T.dist cfg.v (cfg.armA i) : ℤ)) =
      (cfg.a : ℤ) * ((j.val : ℤ) + 1) := by
    have hterm : ∀ i : Fin cfg.a,
        ((T.dist (cfg.armB j) (cfg.armA i) : ℤ) - (T.dist cfg.v (cfg.armA i) : ℤ)) = ((j.val : ℤ) + 1) := by
      intro i
      rw [SimpleGraph.dist_comm (u := cfg.armB j), cfg.dist_A_B_T hT,
        SimpleGraph.dist_comm (u := cfg.v), cfg.dist_A_C_T hT i cfg.mem_setC_v]
      simp
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hB : ∑ t : Fin cfg.b, ((T.dist (cfg.armB j) (cfg.armB t) : ℤ) - (T.dist cfg.v (cfg.armB t) : ℤ)) =
      ((j.val : ℤ) + 1) * (((j.val : ℤ) + 1) - (cfg.b : ℤ) - 1) := by
    have hterm : ∀ t : Fin cfg.b,
        ((T.dist (cfg.armB j) (cfg.armB t) : ℤ) - (T.dist cfg.v (cfg.armB t) : ℤ)) =
          (Int.natAbs ((j.val : ℤ) - (t.val : ℤ)) : ℤ) - ((t.val : ℤ) + 1) := by
      intro t
      rw [cfg.dist_B_B_T hT, SimpleGraph.dist_comm, cfg.dist_B_C_T hT t cfg.mem_setC_v]
      simp
    rw [Finset.sum_congr rfl (fun t _ => hterm t), sum_fin_abs_sub_minus_val]
  have hC : ∑ z ∈ cfg.setC, ((T.dist (cfg.armB j) z : ℤ) - (T.dist cfg.v z : ℤ)) =
      ((cfg.r : ℤ) + 1) * ((j.val : ℤ) + 1) := by
    have hterm : ∀ z ∈ cfg.setC, ((T.dist (cfg.armB j) z : ℤ) - (T.dist cfg.v z : ℤ)) = ((j.val : ℤ) + 1) := by
      intro z hz
      rw [cfg.dist_B_C_T hT j hz]; omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, cfg.card_setC_eq, nsmul_eq_mul]
    push_cast; ring
  rw [hA, hB, hC]; ring

/-! ### Strict monotonicity of `twoHT` (and `htIndex`) under grafting -/

/-- Pair contribution `(n - 1) * dist(x, y) + |D(y) - D(x)|` in `ℤ`. -/
private noncomputable def pairVal (G : SimpleGraph V) (x y : V) : ℤ :=
  ((Fintype.card V - 1 : ℕ) : ℤ) * (G.dist x y : ℤ) +
    |(transmission G y : ℤ) - (transmission G x : ℤ)|

/-- Pointwise A–B lower bound for `a ≥ 2` (factored out to keep tactic context lean). -/
private lemma delta_AB_lower (hT : T.IsTree) (i : Fin cfg.a) (j : Fin cfg.b) :
    ((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) * ((cfg.b : ℤ) - 2 * ((j.val : ℤ) + 1)) +
    (if i.val < j.val then
      ((cfg.b : ℤ) + 2 * ((i.val : ℤ) + 1) - 2 * ((j.val : ℤ) + 1)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) +
      (2 * ((i.val : ℤ) + 1) * (((i.val : ℤ) + 1) + (cfg.b : ℤ)) - 2 * ((j.val : ℤ) + 1) ^ 2) -
      2 * ((j.val : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ))
    else
      -2 * ((j.val : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ))) ≤
    pairVal cfg.graftGraph (cfg.armA i) (cfg.armB j) - pairVal T (cfg.armA i) (cfg.armB j) := by
  have hm : ((Fintype.card V - 1 : ℕ) : ℤ) = (cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ) := by
    have := cfg.card_V_eq; omega
  have hr_ge_a : cfg.a ≤ cfg.r := cfg.a_le_r
  dsimp only [pairVal]
  rw [cfg.dist_A_B_T hT i j, cfg.dist_A_B_T' hT i j, hm]
  set I : ℤ := (i.val : ℤ) + 1
  set J : ℤ := (j.val : ℤ) + 1
  have hI1 : 1 ≤ I := by omega
  have hJ1 : 1 ≤ J := by omega
  have hJb : J ≤ cfg.b := by have := j.isLt; omega
  have hIa : I ≤ cfg.a := by have := i.isLt; omega
  have hdist_diff : ((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) * ((i.val + cfg.b - j.val : ℕ) : ℤ) -
      ((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) * ((i.val + 1 + (j.val + 1) : ℕ) : ℤ) =
      ((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) * ((cfg.b : ℤ) - 2 * J) := by
    have hjlt : j.val < cfg.b := j.isLt
    have hsub : ((i.val + cfg.b - j.val : ℕ) : ℤ) = (i.val : ℤ) + (cfg.b : ℤ) - (j.val : ℤ) := by omega
    rw [hsub]; push_cast; ring
  have hX := cfg.trans_A_sub_v hT i
  have hY := cfg.trans_B_sub_v hT j
  have hdA := cfg.delta_trans_A hT i
  have hdB := cfg.delta_trans_B hT j
  set u : ℤ := (transmission T (cfg.armA i) : ℤ) - (transmission T (cfg.armB j) : ℤ)
  set w : ℤ := (cfg.b : ℤ) * ((cfg.r : ℤ) - (cfg.a : ℤ)) + 2 * (cfg.a : ℤ) * J
  set u' : ℤ := (transmission cfg.graftGraph (cfg.armA i) : ℤ) -
      (transmission cfg.graftGraph (cfg.armB j) : ℤ)
  have hu_eq : u = I * ((cfg.r : ℤ) + (cfg.b : ℤ) - (cfg.a : ℤ) + I) -
      J * ((cfg.r : ℤ) + (cfg.a : ℤ) - (cfg.b : ℤ) + J) := by linarith only [hX, hY]
  have hu'_eq : u' = u + w := by linarith only [hdA, hdB]
  have hu'_fac : u' = ((cfg.b : ℤ) + I - J) * ((cfg.r : ℤ) + I + J - (cfg.a : ℤ)) := by
    rw [hu'_eq, hu_eq]; ring
  have hu'_pos : 0 < u' := by
    rw [hu'_fac]; apply mul_pos <;> omega
  have hw_pos : 0 < w := by
    have h1 : 0 ≤ (cfg.b : ℤ) * ((cfg.r : ℤ) - (cfg.a : ℤ)) := mul_nonneg (by omega) (by omega)
    have h2 : 0 < 2 * (cfg.a : ℤ) * J := mul_pos (mul_pos (by omega) (by have := cfg.ha; omega)) (by omega)
    omega
  have habs_symm1 : |(transmission T (cfg.armB j) : ℤ) - (transmission T (cfg.armA i) : ℤ)| = |u| := by
    rw [abs_sub_comm]
  have habs_symm2 : |(transmission cfg.graftGraph (cfg.armB j) : ℤ) -
      (transmission cfg.graftGraph (cfg.armA i) : ℤ)| = u' := by
    rw [abs_sub_comm, abs_of_pos hu'_pos]
  rw [habs_symm1, habs_symm2]
  have hsum_uu' : u' + u = ((cfg.b : ℤ) + 2 * I - 2 * J) * ((cfg.r : ℤ) - (cfg.a : ℤ)) +
      (2 * I * (I + (cfg.b : ℤ)) - 2 * J ^ 2) - 2 * J * ((cfg.a : ℤ) - (cfg.b : ℤ)) := by
    rw [hu'_eq, hu_eq]; ring
  have hgoal_rew :
      ((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) * ((i.val + cfg.b - j.val : ℕ) : ℤ) + u' -
      (((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) * ((i.val + 1 + (j.val + 1) : ℕ) : ℤ) + |u|) =
      ((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) * ((cfg.b : ℤ) - 2 * J) + (u' - |u|) := by
    rw [← hdist_diff]; ring
  rw [hgoal_rew]
  split_ifs with hij
  · have hu_neg : u < 0 := by
      have : u = (I - J) * ((cfg.r : ℤ) + I + J) - (I + J) * ((cfg.a : ℤ) - (cfg.b : ℤ)) := by
        rw [hu_eq]; ring
      rw [this]
      have h12 : (I - J) * ((cfg.r : ℤ) + I + J) < 0 := mul_neg_of_neg_of_pos (by omega) (by omega)
      have h3 : 0 ≤ (I + J) * ((cfg.a : ℤ) - (cfg.b : ℤ)) :=
        mul_nonneg (by omega) (by have := cfg.hba; omega)
      omega
    rw [abs_of_neg hu_neg]
    have hlt_eq : u' - -u = u' + u := by ring
    rw [hlt_eq, hsum_uu']
  · have hIJ : J ≤ I := by omega
    have hb0 : (0 : ℤ) ≤ (cfg.b : ℤ) := by omega
    have h1 : 0 ≤ ((cfg.b : ℤ) + 2 * I - 2 * J) * ((cfg.r : ℤ) - (cfg.a : ℤ)) :=
      mul_nonneg (by omega) (by omega)
    have h2 : 0 ≤ 2 * I * (I + (cfg.b : ℤ)) - 2 * J ^ 2 := by nlinarith only [hIJ, hJ1, hb0]
    have h3 : -2 * J * ((cfg.a : ℤ) - (cfg.b : ℤ)) ≤ u' + u := by linarith only [hsum_uu', h1, h2]
    have h4 : -2 * J * ((cfg.a : ℤ) - (cfg.b : ℤ)) ≤ w := by
      have hnn : 0 ≤ 2 * J * ((cfg.a : ℤ) - (cfg.b : ℤ)) := mul_nonneg (by omega) (by have := cfg.hba; omega)
      linarith only [hw_pos, hnn]
    have h5 : -2 * J * ((cfg.a : ℤ) - (cfg.b : ℤ)) ≤ u' - |u| := by
      rcases le_or_gt 0 u with hu0 | hu0
      · rw [abs_of_nonneg hu0]; linarith only [hu'_eq, h4]
      · rw [abs_of_neg hu0]; linarith only [h3]
    exact add_le_add le_rfl h5

/-- Case 2 (`a ≥ 2`) summed A–B lower bound (factored out to avoid heartbeat saturation). -/
private lemma case2_AB_bound (hT : T.IsTree) :
    -6 * (cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) +
    ((cfg.b : ℤ) * ((cfg.b : ℤ) - 1) * ((cfg.b : ℤ) - 2)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) -
    2 * (cfg.b : ℤ) * ((cfg.b : ℤ) ^ 2 - 1) -
    6 * (cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.b : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ)) ≤
    6 * ∑ i : Fin cfg.a, ∑ j : Fin cfg.b,
      (pairVal cfg.graftGraph (cfg.armA i) (cfg.armB j) - pairVal T (cfg.armA i) (cfg.armB j)) := by
  have hΔ_split : ∀ (i : Fin cfg.a) (j : Fin cfg.b),
      ((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) * ((cfg.b : ℤ) - 2 * ((j.val : ℤ) + 1)) +
      (if i.val < j.val then
        ((cfg.b : ℤ) + 2 * ((i.val : ℤ) + 1) - 2 * ((j.val : ℤ) + 1)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) +
        (2 * ((i.val : ℤ) + 1) * (((i.val : ℤ) + 1) + (cfg.b : ℤ)) - 2 * ((j.val : ℤ) + 1) ^ 2) -
        2 * ((j.val : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ))
      else
        -2 * ((j.val : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ))) ≤
      pairVal cfg.graftGraph (cfg.armA i) (cfg.armB j) - pairVal T (cfg.armA i) (cfg.armB j) :=
    fun i j => cfg.delta_AB_lower hT i j
  have hsum_le :
      (∑ i : Fin cfg.a, ∑ j : Fin cfg.b,
        (((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) * ((cfg.b : ℤ) - 2 * ((j.val : ℤ) + 1)) +
        (if i.val < j.val then
          ((cfg.b : ℤ) + 2 * ((i.val : ℤ) + 1) - 2 * ((j.val : ℤ) + 1)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) +
          (2 * ((i.val : ℤ) + 1) * (((i.val : ℤ) + 1) + (cfg.b : ℤ)) - 2 * ((j.val : ℤ) + 1) ^ 2) -
          2 * ((j.val : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ))
        else
          -2 * ((j.val : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ))))) ≤
      ∑ i : Fin cfg.a, ∑ j : Fin cfg.b,
        (pairVal cfg.graftGraph (cfg.armA i) (cfg.armB j) - pairVal T (cfg.armA i) (cfg.armB j)) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hΔ_split i j))
  have hdist_sum : ∑ _i : Fin cfg.a, ∑ j : Fin cfg.b,
      (((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) * ((cfg.b : ℤ) - 2 * ((j.val : ℤ) + 1))) =
      -(cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) := by
    have hinner : ∑ j : Fin cfg.b, ((cfg.b : ℤ) - 2 * ((j.val : ℤ) + 1)) = -(cfg.b : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Finset.mul_sum, sum_fin_val_plus_one]
      simp only [nsmul_eq_mul]; ring
    simp_rw [← Finset.mul_sum, hinner]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hd_sum : ∑ _i : Fin cfg.a, ∑ j : Fin cfg.b,
      (-2 * ((j.val : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ))) =
      -(cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.b : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ)) := by
    have hinner : ∑ j : Fin cfg.b, (-2 * ((j.val : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ))) =
        -(cfg.b : ℤ) * ((cfg.b : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ)) := by
      have hrew : ∑ j : Fin cfg.b, (-2 * ((j.val : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ))) =
          -((cfg.a : ℤ) - (cfg.b : ℤ)) * (2 * ∑ j : Fin cfg.b, ((j.val : ℤ) + 1)) := by
        rw [Finset.mul_sum, Finset.mul_sum]; congr 1; ext j; ring
      rw [hrew, sum_fin_val_plus_one]; ring
    rw [Finset.sum_congr rfl (fun _ _ => hinner), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]; ring
  have hlt_sum : 6 * ∑ i : Fin cfg.a, ∑ j : Fin cfg.b,
      (if i.val < j.val then
        ((cfg.b : ℤ) + 2 * ((i.val : ℤ) + 1) - 2 * ((j.val : ℤ) + 1)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) +
        (2 * ((i.val : ℤ) + 1) * (((i.val : ℤ) + 1) + (cfg.b : ℤ)) - 2 * ((j.val : ℤ) + 1) ^ 2)
      else 0) =
      ((cfg.b : ℤ) * ((cfg.b : ℤ) - 1) * ((cfg.b : ℤ) - 2)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) -
      2 * (cfg.b : ℤ) * ((cfg.b : ℤ) ^ 2 - 1) := by
    rw [Finset.sum_comm]
    have hbij : ∑ j : Fin cfg.b, ∑ i : Fin cfg.a,
        (if i.val < j.val then
          ((cfg.b : ℤ) + 2 * ((i.val : ℤ) + 1) - 2 * ((j.val : ℤ) + 1)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) +
          (2 * ((i.val : ℤ) + 1) * (((i.val : ℤ) + 1) + (cfg.b : ℤ)) - 2 * ((j.val : ℤ) + 1) ^ 2)
        else 0) =
        ∑ j ∈ Finset.Icc 1 cfg.b, ∑ i ∈ Finset.Icc 1 (j - 1),
          (((cfg.b : ℤ) + 2 * (i : ℤ) - 2 * (j : ℤ)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) +
          (2 * (i : ℤ) * ((i : ℤ) + (cfg.b : ℤ)) - 2 * (j : ℤ) ^ 2)) := by
      apply Finset.sum_nbij (fun j : Fin cfg.b => j.val + 1)
      · intro j _; rw [Finset.mem_Icc]; have := j.isLt; omega
      · intro j₁ _ j₂ _ h; dsimp only at h; exact Fin.ext (by omega)
      · intro y hy
        obtain ⟨hy1, hy2⟩ := Finset.mem_Icc.mp (Finset.mem_coe.mp hy)
        exact ⟨⟨y - 1, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by dsimp only; omega⟩
      · intro j _
        rw [← Finset.sum_filter]
        apply Finset.sum_nbij (fun i : Fin cfg.a => i.val + 1)
        · intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          rw [Finset.mem_Icc]; omega
        · intro i₁ _ i₂ _ h; dsimp only at h; exact Fin.ext (by omega)
        · intro x hx
          obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp (Finset.mem_coe.mp hx)
          have hba := cfg.hba
          have hjlt := j.isLt
          exact ⟨⟨x - 1, by omega⟩,
            Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩), by dsimp only; omega⟩
        · intro i _; push_cast; rfl
    rw [hbij]
    simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [mul_add, ← mul_assoc, sum_lt_coeff_s, show (6 : ℤ) = 2 * 3 by norm_num, mul_assoc 2 3,
      sum_lt_const]
    ring
  have hrew_lhs : ∑ i : Fin cfg.a, ∑ j : Fin cfg.b,
      (((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) * ((cfg.b : ℤ) - 2 * ((j.val : ℤ) + 1)) +
      (if i.val < j.val then
        ((cfg.b : ℤ) + 2 * ((i.val : ℤ) + 1) - 2 * ((j.val : ℤ) + 1)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) +
        (2 * ((i.val : ℤ) + 1) * (((i.val : ℤ) + 1) + (cfg.b : ℤ)) - 2 * ((j.val : ℤ) + 1) ^ 2) -
        2 * ((j.val : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ))
      else
        -2 * ((j.val : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ)))) =
      (∑ i : Fin cfg.a, ∑ j : Fin cfg.b,
        (((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) * ((cfg.b : ℤ) - 2 * ((j.val : ℤ) + 1)))) +
      (∑ i : Fin cfg.a, ∑ j : Fin cfg.b,
        (if i.val < j.val then
          ((cfg.b : ℤ) + 2 * ((i.val : ℤ) + 1) - 2 * ((j.val : ℤ) + 1)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) +
          (2 * ((i.val : ℤ) + 1) * (((i.val : ℤ) + 1) + (cfg.b : ℤ)) - 2 * ((j.val : ℤ) + 1) ^ 2)
        else 0)) +
      (∑ i : Fin cfg.a, ∑ j : Fin cfg.b,
        (-2 * ((j.val : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ)))) := by
    simp_rw [← Finset.sum_add_distrib]
    congr 1; ext i; congr 1; ext j
    split_ifs <;> ring
  rw [hrew_lhs, hdist_sum, hd_sum] at hsum_le
  linarith

/-- Lemma 3.2: Every valid pendant-path grafting move strictly increases `htIndex`. -/
theorem graft_htIndex_strict_lt (hT : T.IsTree) :
    htIndex T < htIndex cfg.graftGraph := by
  have pairVal_symm : ∀ (G : SimpleGraph V) (x y : V), pairVal G y x = pairVal G x y := by
    intro G x y; unfold pairVal; rw [SimpleGraph.dist_comm, abs_sub_comm]
  have twoHT_cast : ∀ (G : SimpleGraph V), (twoHT G : ℤ) = ∑ x : V, ∑ y : V, pairVal G x y := by
    intro G; unfold twoHT pairVal; push_cast; rfl
  rw [htIndex_lt_iff]
  suffices h : (0 : ℤ) < (twoHT cfg.graftGraph : ℤ) - (twoHT T : ℤ) by omega
  rw [twoHT_cast, twoHT_cast, ← Finset.sum_sub_distrib]
  have hsub_inner : ∀ x : V,
      (∑ y : V, pairVal cfg.graftGraph x y) - (∑ y : V, pairVal T x y) =
        ∑ y : V, (pairVal cfg.graftGraph x y - pairVal T x y) :=
    fun _ => (Finset.sum_sub_distrib _ _).symm
  simp_rw [hsub_inner]
  let Δ : V → V → ℤ := fun x y => pairVal cfg.graftGraph x y - pairVal T x y
  have hΔ_symm : ∀ x y, Δ y x = Δ x y := fun x y => by simp [Δ, pairVal_symm]
  -- Partition the double sum over `(A ∪ B ∪ C) × (A ∪ B ∪ C)`
  have hpart : (∑ x : V, ∑ y : V, Δ x y) =
      (∑ i : Fin cfg.a, ∑ k : Fin cfg.a, Δ (cfg.armA i) (cfg.armA k)) +
      (∑ j : Fin cfg.b, ∑ k : Fin cfg.b, Δ (cfg.armB j) (cfg.armB k)) +
      (∑ z ∈ cfg.setC, ∑ w ∈ cfg.setC, Δ z w) +
      2 * (∑ i : Fin cfg.a, ∑ z ∈ cfg.setC, Δ (cfg.armA i) z) +
      2 * (∑ j : Fin cfg.b, ∑ z ∈ cfg.setC, Δ (cfg.armB j) z) +
      2 * (∑ i : Fin cfg.a, ∑ j : Fin cfg.b, Δ (cfg.armA i) (cfg.armB j)) := by
    rw [cfg.sum_univ_partition]
    simp_rw [cfg.sum_univ_partition]
    have hCA : (∑ z ∈ cfg.setC, ∑ i : Fin cfg.a, Δ z (cfg.armA i)) =
        ∑ i : Fin cfg.a, ∑ z ∈ cfg.setC, Δ (cfg.armA i) z := by
      rw [Finset.sum_comm]; congr 1; ext i; congr 1; ext z; exact hΔ_symm _ _
    have hCB : (∑ z ∈ cfg.setC, ∑ j : Fin cfg.b, Δ z (cfg.armB j)) =
        ∑ j : Fin cfg.b, ∑ z ∈ cfg.setC, Δ (cfg.armB j) z := by
      rw [Finset.sum_comm]; congr 1; ext j; congr 1; ext z; exact hΔ_symm _ _
    have hBA : (∑ j : Fin cfg.b, ∑ i : Fin cfg.a, Δ (cfg.armB j) (cfg.armA i)) =
        ∑ i : Fin cfg.a, ∑ j : Fin cfg.b, Δ (cfg.armA i) (cfg.armB j) := by
      rw [Finset.sum_comm]; congr 1; ext i; congr 1; ext j; exact hΔ_symm _ _
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hCA, hCB, hBA]
    ring
  rw [hpart]
  -- Zero blocks: A-A and C-C
  have hAA : ∑ i : Fin cfg.a, ∑ k : Fin cfg.a, Δ (cfg.armA i) (cfg.armA k) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro k _
    have h1 := cfg.delta_trans_A hT i
    have h2 := cfg.delta_trans_A hT k
    have hd1 := cfg.dist_A_A_T hT i k
    have hd2 := cfg.dist_A_A_T' hT i k
    have hsub : (transmission cfg.graftGraph (cfg.armA k) : ℤ) -
        (transmission cfg.graftGraph (cfg.armA i) : ℤ) =
        (transmission T (cfg.armA k) : ℤ) - (transmission T (cfg.armA i) : ℤ) := by linarith
    simp [Δ, pairVal, hd1, hd2, hsub]
  have hCC : ∑ z ∈ cfg.setC, ∑ w ∈ cfg.setC, Δ z w = 0 := by
    apply Finset.sum_eq_zero; intro z hz
    apply Finset.sum_eq_zero; intro w hw
    have h1 := cfg.delta_trans_C hT hz
    have h2 := cfg.delta_trans_C hT hw
    have hd := cfg.dist_C_C_T' hT hz hw
    have hsub : (transmission cfg.graftGraph w : ℤ) - (transmission cfg.graftGraph z : ℤ) =
        (transmission T w : ℤ) - (transmission T z : ℤ) := by linarith
    simp [Δ, pairVal, hd, hsub]
  rw [hAA, hCC, zero_add, add_zero]
  have hm : ((Fintype.card V - 1 : ℕ) : ℤ) = (cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ) := by
    have := cfg.card_V_eq; omega
  have hr_ge_a : cfg.a ≤ cfg.r := cfg.a_le_r
  -- Split into Case 1 (`a = 1`, hence `b = 1`) and Case 2 (`a ≥ 2`)
  by_cases ha1 : cfg.a = 1
  · -- Case 1: `a = b = 1`
    have hb1 : cfg.b = 1 := by have := cfg.hb; have := cfg.hba; omega
    let i0 : Fin cfg.a := ⟨0, cfg.ha⟩
    let j0 : Fin cfg.b := ⟨0, cfg.hb⟩
    have hfinA : ∀ f : Fin cfg.a → ℤ, ∑ i : Fin cfg.a, f i = f i0 := by
      intro f
      have huniq : (Finset.univ : Finset (Fin cfg.a)) = {i0} := by
        ext i; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; ext; omega
      rw [huniq, Finset.sum_singleton]
    have hfinB : ∀ f : Fin cfg.b → ℤ, ∑ j : Fin cfg.b, f j = f j0 := by
      intro f
      have huniq : (Finset.univ : Finset (Fin cfg.b)) = {j0} := by
        ext j; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; ext; omega
      rw [huniq, Finset.sum_singleton]
    rw [hfinB, hfinB, hfinA, hfinB, hfinA, hfinB]
    have hBB : Δ (cfg.armB j0) (cfg.armB j0) = 0 := by simp [Δ, pairVal]
    rw [hBB, zero_add]
    -- Arm symmetry: `D(A_1) = D(B_1)`
    have hsymm : (transmission T (cfg.armA i0) : ℤ) = (transmission T (cfg.armB j0) : ℤ) := by
      have hA := cfg.trans_A_sub_v hT i0
      have hB := cfg.trans_B_sub_v hT j0
      simp only [i0, j0, ha1, hb1] at hA hB
      linarith
    -- Combined `(A_1, z) + (B_1, z)` gain for each `z ∈ C` is `≥ 1`
    have hC_sum : (cfg.r : ℤ) + 1 ≤
        (∑ z ∈ cfg.setC, Δ (cfg.armA i0) z) + (∑ z ∈ cfg.setC, Δ (cfg.armB j0) z) := by
      rw [← Finset.sum_add_distrib]
      have hpt : ∀ z ∈ cfg.setC, (1 : ℤ) ≤ Δ (cfg.armA i0) z + Δ (cfg.armB j0) z := by
        intro z hz
        have hda1 := cfg.dist_A_C_T hT i0 hz
        have hda2 := cfg.dist_A_C_T' hT i0 hz
        have hdb1 := cfg.dist_B_C_T hT j0 hz
        have hdb2 := cfg.dist_B_C_T' hT j0 hz
        have hta := cfg.delta_trans_A hT i0
        have htb := cfg.delta_trans_B hT j0
        have htc := cfg.delta_trans_C hT hz
        have ha1Z : (cfg.a : ℤ) = 1 := by omega
        have hb1Z : (cfg.b : ℤ) = 1 := by omega
        simp only [i0, j0, hb1] at hda1 hda2 hdb1 hdb2
        rw [hb1Z] at hta
        rw [ha1Z, hb1Z] at htb
        simp only [j0] at htb
        rw [ha1Z, hb1Z] at htc
        dsimp [Δ, pairVal]
        rw [hda1, hda2, hdb1, hdb2, hm, ha1Z, hb1Z]
        set u : ℤ := (transmission T z : ℤ) - (transmission T (cfg.armA i0) : ℤ)
        have huB : (transmission T z : ℤ) - (transmission T (cfg.armB j0) : ℤ) = u := by
          rw [← hsymm]
        have huA' : (transmission cfg.graftGraph z : ℤ) - (transmission cfg.graftGraph (cfg.armA i0) : ℤ) =
            u + (1 - (cfg.r : ℤ)) := by linarith
        have huB' : (transmission cfg.graftGraph z : ℤ) - (transmission cfg.graftGraph (cfg.armB j0) : ℤ) =
            u + 2 := by push_cast at htb; linarith
        rw [huB, huA', huB']
        have htri : |2 * u + (3 - (cfg.r : ℤ))| ≤ |u + (1 - (cfg.r : ℤ))| + |u + 2| := by
          calc |2 * u + (3 - (cfg.r : ℤ))|
              = |(u + (1 - (cfg.r : ℤ))) + (u + 2)| := by ring_nf
            _ ≤ |u + (1 - (cfg.r : ℤ))| + |u + 2| := abs_add_le _ _
        have htri2 : 2 * |u| - |(cfg.r : ℤ) - 3| ≤ |2 * u + (3 - (cfg.r : ℤ))| := by
          have h1 := abs_sub_abs_le_abs_sub (2 * u) ((cfg.r : ℤ) - 3)
          have h2 : 2 * u - ((cfg.r : ℤ) - 3) = 2 * u + (3 - (cfg.r : ℤ)) := by ring
          have h3 : |2 * u| = 2 * |u| := by rw [abs_mul]; norm_num
          rw [h2, h3] at h1
          linarith
        have hrcase : (1 : ℤ) ≤ ((cfg.r : ℤ) + 2) - |(cfg.r : ℤ) - 3| := by
          have hr1 : 1 ≤ cfg.r := by omega
          rcases le_or_gt (cfg.r : ℤ) 3 with hle | hgt
          · rw [abs_of_nonpos (by omega)]; omega
          · rw [abs_of_pos (by omega)]; omega
        push_cast
        linarith
      calc (cfg.r : ℤ) + 1 = ∑ _z ∈ cfg.setC, (1 : ℤ) := by
            rw [Finset.sum_const, cfg.card_setC_eq, nsmul_eq_mul, mul_one]; push_cast; rfl
        _ ≤ ∑ z ∈ cfg.setC, (Δ (cfg.armA i0) z + Δ (cfg.armB j0) z) :=
            Finset.sum_le_sum hpt
    -- Single `(A_1, B_1)` pair has exact change `-1`
    have hAB : Δ (cfg.armA i0) (cfg.armB j0) = -1 := by
      have hd1 := cfg.dist_A_B_T hT i0 j0
      have hd2 := cfg.dist_A_B_T' hT i0 j0
      have hta := cfg.delta_trans_A hT i0
      have htb := cfg.delta_trans_B hT j0
      have ha1Z : (cfg.a : ℤ) = 1 := by omega
      have hb1Z : (cfg.b : ℤ) = 1 := by omega
      simp only [i0, j0, hb1] at hd1 hd2
      rw [hb1Z] at hta
      rw [ha1Z, hb1Z] at htb
      simp only [j0] at htb
      dsimp [Δ, pairVal]
      rw [hd1, hd2, hm, ha1Z, hb1Z]
      have hdiff0 : (transmission T (cfg.armB j0) : ℤ) - (transmission T (cfg.armA i0) : ℤ) = 0 := by
        linarith
      have hdiff1 : (transmission cfg.graftGraph (cfg.armB j0) : ℤ) -
          (transmission cfg.graftGraph (cfg.armA i0) : ℤ) = -((cfg.r : ℤ) + 1) := by
        push_cast at htb; linarith
      rw [hdiff0, hdiff1, abs_zero, abs_neg, abs_of_nonneg (by omega)]
      push_cast; ring
    have hr1 : (1 : ℤ) ≤ (cfg.r : ℤ) := by omega
    linarith
  · -- Case 2: `a ≥ 2` (`1 ≤ b ≤ a ≤ r`)
    have ha2 : 2 ≤ cfg.a := by have := cfg.ha; omega
    -- 1. A-C bound
    have hAC : (cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.r : ℤ) + 1) * (2 * (cfg.a : ℤ) + (cfg.b : ℤ)) ≤
        ∑ i : Fin cfg.a, ∑ z ∈ cfg.setC, Δ (cfg.armA i) z := by
      have hpt : ∀ (i : Fin cfg.a) (z : V), z ∈ cfg.setC →
          (cfg.b : ℤ) * (2 * (cfg.a : ℤ) + (cfg.b : ℤ)) ≤ Δ (cfg.armA i) z := by
        intro i z hz
        dsimp [Δ, pairVal]
        rw [cfg.dist_A_C_T hT i hz, cfg.dist_A_C_T' hT i hz, hm]
        have hta := cfg.delta_trans_A hT i
        have htc := cfg.delta_trans_C hT hz
        set u := (transmission T z : ℤ) - (transmission T (cfg.armA i) : ℤ)
        set w := (cfg.b : ℤ) * ((cfg.a : ℤ) - (cfg.r : ℤ))
        have hu' : (transmission cfg.graftGraph z : ℤ) - (transmission cfg.graftGraph (cfg.armA i) : ℤ) =
            u + w := by linarith
        rw [hu']
        have htri : -|w| ≤ |u + w| - |u| := by
          have := abs_sub_abs_le_abs_sub (u + w) w
          simp only [add_sub_cancel_right] at this
          have := abs_add_le (u + w) (-w)
          simp only [add_neg_cancel_right, abs_neg] at this
          linarith
        have habsw : |w| = (cfg.b : ℤ) * ((cfg.r : ℤ) - (cfg.a : ℤ)) := by
          have hw0 : w ≤ 0 := by nlinarith
          rw [abs_of_nonpos hw0]; ring
        push_cast
        linarith
      calc (cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.r : ℤ) + 1) * (2 * (cfg.a : ℤ) + (cfg.b : ℤ))
          = ∑ _i : Fin cfg.a, ∑ _z ∈ cfg.setC, ((cfg.b : ℤ) * (2 * (cfg.a : ℤ) + (cfg.b : ℤ))) := by
            rw [Finset.sum_const, Finset.sum_const, cfg.card_setC_eq, Finset.card_univ,
              Fintype.card_fin]
            simp only [nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ i : Fin cfg.a, ∑ z ∈ cfg.setC, Δ (cfg.armA i) z :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun z hz => hpt i z hz))
    -- 2. B-C bound
    have hBC : -((cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.r : ℤ) + 1) * ((cfg.b : ℤ) + 1)) ≤
        ∑ j : Fin cfg.b, ∑ z ∈ cfg.setC, Δ (cfg.armB j) z := by
      have hpt : ∀ (j : Fin cfg.b) (z : V), z ∈ cfg.setC →
          -(2 * (cfg.a : ℤ) * ((j.val : ℤ) + 1)) ≤ Δ (cfg.armB j) z := by
        intro j z hz
        dsimp [Δ, pairVal]
        rw [cfg.dist_B_C_T hT j hz, cfg.dist_B_C_T' hT j hz]
        have htb := cfg.delta_trans_B hT j
        have htc := cfg.delta_trans_C hT hz
        set u := (transmission T z : ℤ) - (transmission T (cfg.armB j) : ℤ)
        set w := 2 * (cfg.a : ℤ) * ((j.val : ℤ) + 1)
        have hu' : (transmission cfg.graftGraph z : ℤ) - (transmission cfg.graftGraph (cfg.armB j) : ℤ) =
            u + w := by linarith
        rw [hu']
        have htri : -|w| ≤ |u + w| - |u| := by
          have := abs_add_le (u + w) (-w)
          simp only [add_neg_cancel_right, abs_neg] at this
          linarith
        have habsw : |w| = w := abs_of_nonneg (by positivity)
        linarith
      have hsum_eq : ∑ j : Fin cfg.b, ∑ _z ∈ cfg.setC, (-(2 * (cfg.a : ℤ) * ((j.val : ℤ) + 1))) =
          -((cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.r : ℤ) + 1) * ((cfg.b : ℤ) + 1)) := by
        simp_rw [Finset.sum_const, cfg.card_setC_eq, nsmul_eq_mul]
        have hlin := sum_fin_val_plus_one cfg.b
        have hpull : ∑ j : Fin cfg.b,
            (((cfg.r + 1 : ℕ) : ℤ) * -(2 * (cfg.a : ℤ) * ((j.val : ℤ) + 1))) =
            -(((cfg.r + 1 : ℕ) : ℤ) * (cfg.a : ℤ)) * (2 * ∑ j : Fin cfg.b, ((j.val : ℤ) + 1)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          congr 1; ext j; ring
        rw [hpull, hlin]; push_cast; ring
      rw [← hsum_eq]
      exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun z hz => hpt j z hz))
    -- 3. B-B bound (note ordered sum counts each unordered pair twice!)
    have hBB : -(2 * (cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.b : ℤ) ^ 2 - 1)) ≤
        3 * ∑ j : Fin cfg.b, ∑ k : Fin cfg.b, Δ (cfg.armB j) (cfg.armB k) := by
      have hpt : ∀ j k : Fin cfg.b,
          -(2 * (cfg.a : ℤ) * (Int.natAbs ((k.val : ℤ) - (j.val : ℤ)) : ℤ)) ≤
            Δ (cfg.armB j) (cfg.armB k) := by
        intro j k
        dsimp [Δ, pairVal]
        rw [cfg.dist_B_B_T hT j k, cfg.dist_B_B_T' hT j k]
        have h1 := cfg.delta_trans_B hT j
        have h2 := cfg.delta_trans_B hT k
        set u := (transmission T (cfg.armB k) : ℤ) - (transmission T (cfg.armB j) : ℤ)
        set w := 2 * (cfg.a : ℤ) * ((j.val : ℤ) - (k.val : ℤ))
        have hu' : (transmission cfg.graftGraph (cfg.armB k) : ℤ) -
            (transmission cfg.graftGraph (cfg.armB j) : ℤ) = u + w := by linarith
        rw [hu']
        have htri : -|w| ≤ |u + w| - |u| := by
          have := abs_add_le (u + w) (-w)
          simp only [add_neg_cancel_right, abs_neg] at this
          linarith
        have habsw : |w| = 2 * (cfg.a : ℤ) * (Int.natAbs ((k.val : ℤ) - (j.val : ℤ)) : ℤ) := by
          have h1' : |w| = |2 * (cfg.a : ℤ)| * |(j.val : ℤ) - (k.val : ℤ)| := abs_mul _ _
          rw [h1', abs_of_nonneg (by positivity), abs_sub_comm, ← Int.natCast_natAbs]
        linarith
      have hsum_abs : 3 * ∑ j : Fin cfg.b, ∑ k : Fin cfg.b,
          (Int.natAbs ((k.val : ℤ) - (j.val : ℤ)) : ℤ) =
          (cfg.b : ℤ) * ((cfg.b : ℤ) ^ 2 - 1) := by
        have hord : ∑ j : Fin cfg.b, ∑ k : Fin cfg.b, (Int.natAbs ((k.val : ℤ) - (j.val : ℤ)) : ℤ) =
            2 * ∑ j ∈ Finset.Icc 1 cfg.b, ∑ k ∈ Finset.Icc (j + 1) cfg.b, ((k : ℤ) - (j : ℤ)) := by
          have hbij : ∑ j : Fin cfg.b, ∑ k : Fin cfg.b,
              (Int.natAbs ((k.val : ℤ) - (j.val : ℤ)) : ℤ) =
              ∑ j ∈ Finset.Icc 1 cfg.b, ∑ k ∈ Finset.Icc 1 cfg.b,
                (Int.natAbs ((k : ℤ) - (j : ℤ)) : ℤ) := by
            apply Finset.sum_nbij (fun j : Fin cfg.b => j.val + 1)
            · intro j _; rw [Finset.mem_Icc]; omega
            · intro j₁ _ j₂ _ h; dsimp only at h; exact Fin.ext (by omega)
            · intro x hx
              rw [Finset.mem_coe, Finset.mem_Icc] at hx
              refine ⟨⟨x - 1, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
              dsimp only; omega
            · intro j _
              apply Finset.sum_nbij (fun k : Fin cfg.b => k.val + 1)
              · intro k _; rw [Finset.mem_Icc]; omega
              · intro k₁ _ k₂ _ h; dsimp only at h; exact Fin.ext (by omega)
              · intro y hy
                rw [Finset.mem_coe, Finset.mem_Icc] at hy
                refine ⟨⟨y - 1, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
                dsimp only; omega
              · intro k _
                push_cast
                have : ((k.val : ℤ) + 1) - ((j.val : ℤ) + 1) = (k.val : ℤ) - (j.val : ℤ) := by ring
                rw [this]
          rw [hbij]
          have hsp : ∀ j ∈ Finset.Icc 1 cfg.b,
              ∑ k ∈ Finset.Icc 1 cfg.b, (Int.natAbs ((k : ℤ) - (j : ℤ)) : ℤ) =
                (∑ k ∈ Finset.Icc (j + 1) cfg.b, ((k : ℤ) - (j : ℤ))) +
                (∑ k ∈ Finset.Icc 1 (j - 1), ((j : ℤ) - (k : ℤ))) := by
            intro j hj
            have hj' := Finset.mem_Icc.mp hj
            have hun : Finset.Icc 1 cfg.b =
                insert j (Finset.Icc (j + 1) cfg.b ∪ Finset.Icc 1 (j - 1)) := by
              ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_union]; omega
            have hni : j ∉ Finset.Icc (j + 1) cfg.b ∪ Finset.Icc 1 (j - 1) := by
              simp only [Finset.mem_union, Finset.mem_Icc]; omega
            have hdisj : Disjoint (Finset.Icc (j + 1) cfg.b) (Finset.Icc 1 (j - 1)) := by
              rw [Finset.disjoint_left]; intro k h1 h2
              simp only [Finset.mem_Icc] at h1 h2; omega
            rw [hun, Finset.sum_insert hni, Finset.sum_union hdisj, sub_self, Int.natAbs_zero,
              Nat.cast_zero, zero_add]
            congr 1
            · apply Finset.sum_congr rfl; intro k hk
              have := (Finset.mem_Icc.mp hk).1; omega
            · apply Finset.sum_congr rfl; intro k hk
              have := (Finset.mem_Icc.mp hk).2; omega
          rw [Finset.sum_congr rfl hsp, Finset.sum_add_distrib]
          have hswap : (∑ j ∈ Finset.Icc 1 cfg.b, ∑ k ∈ Finset.Icc 1 (j - 1), ((j : ℤ) - (k : ℤ))) =
              ∑ k ∈ Finset.Icc 1 cfg.b, ∑ j ∈ Finset.Icc (k + 1) cfg.b, ((j : ℤ) - (k : ℤ)) := by
            have h1 : ∀ j ∈ Finset.Icc 1 cfg.b,
                ∑ k ∈ Finset.Icc 1 (j - 1), ((j : ℤ) - (k : ℤ)) =
                  ∑ k ∈ Finset.Icc 1 cfg.b, if k < j then ((j : ℤ) - (k : ℤ)) else 0 := by
              intro j hj
              rw [← Finset.sum_filter]
              have hf : (Finset.Icc 1 cfg.b).filter (fun k => k < j) = Finset.Icc 1 (j - 1) := by
                ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; have := (Finset.mem_Icc.mp hj).2; omega
              rw [hf]
            have h2 : ∀ k ∈ Finset.Icc 1 cfg.b,
                ∑ j ∈ Finset.Icc (k + 1) cfg.b, ((j : ℤ) - (k : ℤ)) =
                  ∑ j ∈ Finset.Icc 1 cfg.b, if k < j then ((j : ℤ) - (k : ℤ)) else 0 := by
              intro k hk
              rw [← Finset.sum_filter]
              have hf : (Finset.Icc 1 cfg.b).filter (fun j => k < j) = Finset.Icc (k + 1) cfg.b := by
                ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; have := (Finset.mem_Icc.mp hk).1; omega
              rw [hf]
            rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl h2]
          rw [hswap]; ring
        rw [hord, ← mul_assoc, show (3 : ℤ) * 2 = 6 by norm_num, sum_pairs_diff]
      have hle : ∑ j : Fin cfg.b, ∑ k : Fin cfg.b,
          (-(2 * (cfg.a : ℤ) * (Int.natAbs ((k.val : ℤ) - (j.val : ℤ)) : ℤ))) ≤
          ∑ j : Fin cfg.b, ∑ k : Fin cfg.b, Δ (cfg.armB j) (cfg.armB k) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hpt j k))
      have hpull : ∑ j : Fin cfg.b, ∑ k : Fin cfg.b,
          (-(2 * (cfg.a : ℤ) * (Int.natAbs ((k.val : ℤ) - (j.val : ℤ)) : ℤ))) =
          -(2 * (cfg.a : ℤ)) * ∑ j : Fin cfg.b, ∑ k : Fin cfg.b,
            (Int.natAbs ((k.val : ℤ) - (j.val : ℤ)) : ℤ) := by
        rw [Finset.mul_sum]; congr 1; ext j; rw [Finset.mul_sum]; congr 1; ext k; ring
      rw [hpull] at hle
      nlinarith
    -- 4. A-B exact + closed-form polynomial bound
    have hAB : -6 * (cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) +
        ((cfg.b : ℤ) * ((cfg.b : ℤ) - 1) * ((cfg.b : ℤ) - 2)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) -
        2 * (cfg.b : ℤ) * ((cfg.b : ℤ) ^ 2 - 1) -
        6 * (cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.b : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ)) ≤
        6 * ∑ i : Fin cfg.a, ∑ j : Fin cfg.b, Δ (cfg.armA i) (cfg.armB j) :=
      cfg.case2_AB_bound hT
    -- Combine all four bounds and apply `graft_poly_pos`!
    have hpoly := graft_poly_pos ha2 cfg.hb cfg.hba cfg.a_le_r
    have hid : (12 * (cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.a : ℤ) - 1) +
        (cfg.b : ℤ) * ((cfg.b : ℤ) - 1) * ((cfg.b : ℤ) - 2)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) +
        2 * (cfg.b : ℤ) * (6 * ((cfg.a : ℤ) - (cfg.b : ℤ)) ^ 3 +
          (15 * (cfg.b : ℤ) - 6) * ((cfg.a : ℤ) - (cfg.b : ℤ)) ^ 2 +
          2 * ((cfg.b : ℤ) - 1) * (7 * (cfg.b : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ)) +
          (5 * (cfg.b : ℤ) ^ 3 - 7 * (cfg.b : ℤ) ^ 2 - 2 * (cfg.b : ℤ) + 1)) =
        6 * ((cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.r : ℤ) + 1) * (2 * (cfg.a : ℤ) + (cfg.b : ℤ)) -
          (cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.r : ℤ) + 1) * ((cfg.b : ℤ) + 1)) -
        2 * (cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.b : ℤ) ^ 2 - 1) +
        (-6 * (cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.a : ℤ) + (cfg.b : ℤ) + (cfg.r : ℤ)) +
          ((cfg.b : ℤ) * ((cfg.b : ℤ) - 1) * ((cfg.b : ℤ) - 2)) * ((cfg.r : ℤ) - (cfg.a : ℤ)) -
          2 * (cfg.b : ℤ) * ((cfg.b : ℤ) ^ 2 - 1) -
          6 * (cfg.a : ℤ) * (cfg.b : ℤ) * ((cfg.b : ℤ) + 1) * ((cfg.a : ℤ) - (cfg.b : ℤ))) := by
      ring
    linarith

end GraftConfig

end GraftMove

section TreeStructure

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Every vertex in a tree on `n ≥ 2` vertices has degree at least `1`. -/
private lemma degree_pos_of_isTree {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) (u : V) : 1 ≤ T.degree u := by
  obtain ⟨v, huv⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) u
  obtain ⟨w, hw⟩ := before_exists hT huv.symm
  rw [← T.card_neighborFinset_eq_degree]
  exact Finset.card_pos.mpr ⟨w, (mem_neighborFinset T u w).mpr hw.1⟩

omit [DecidableEq V] in
/-- Handshaking lemma on trees: `∑ u, deg u = 2 * (n - 1)`. -/
private lemma sum_degree_isTree {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) : ∑ u : V, T.degree u = 2 * (Fintype.card V - 1) := by
  rw [T.sum_degrees_eq_twice_card_edges]
  have hTcard := (SimpleGraph.isTree_iff_connected_and_card.mp hT).2
  have h1 : Nat.card T.edgeSet = T.edgeFinset.card := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  rw [h1, Nat.card_eq_fintype_card] at hTcard
  omega

/-- In a tree on `n ≥ 2` vertices, `leafCount T ≥ 2`, and `leafCount T = 2 ↔ ∀ u, T.degree u ≤ 2`. -/
private lemma leafCount_tree_props {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    2 ≤ leafCount T ∧ (leafCount T = 2 ↔ ∀ u : V, T.degree u ≤ 2) := by
  classical
  have hdeg1 : ∀ u : V, 1 ≤ T.degree u := degree_pos_of_isTree hT hn
  have hsum := sum_degree_isTree hT
  have hbal : (∑ u : V, ((T.degree u : ℤ) - 2)) = -2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (∑ u : V, (T.degree u : ℤ)) = 2 * ((Fintype.card V : ℤ) - 1) := by
      have hcast : (∑ u : V, (T.degree u : ℤ)) = (∑ u : V, T.degree u : ℕ) := by push_cast; rfl
      rw [hcast, hsum]; omega
    linarith
  let L := Finset.univ.filter (fun u : V => T.degree u = 1)
  let B := Finset.univ.filter (fun u : V => 3 ≤ T.degree u)
  have hsplit : ∑ u : V, ((T.degree u : ℤ) - 2) =
      -(L.card : ℤ) + ∑ u ∈ B, ((T.degree u : ℤ) - 2) := by
    have hL : ∑ u ∈ L, ((T.degree u : ℤ) - 2) = -(L.card : ℤ) := by
      have : ∀ u ∈ L, ((T.degree u : ℤ) - 2) = -1 := by
        intro u hu; have := (Finset.mem_filter.mp hu).2; omega
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; ring
    have h2 : ∑ u ∈ Finset.univ.filter (fun u : V => T.degree u = 2),
        ((T.degree u : ℤ) - 2) = 0 := by
      apply Finset.sum_eq_zero; intro u hu; have := (Finset.mem_filter.mp hu).2; omega
    have hun : (Finset.univ : Finset V) =
        L ∪ (Finset.univ.filter (fun u : V => T.degree u = 2) ∪ B) := by
      ext u; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, L, B, true_and, true_iff]
      have := hdeg1 u; omega
    have hd1 : Disjoint L (Finset.univ.filter (fun u : V => T.degree u = 2) ∪ B) := by
      rw [Finset.disjoint_left]; intro u h1 h2
      simp only [Finset.mem_filter, Finset.mem_union, L, B] at h1 h2; omega
    have hd2 : Disjoint (Finset.univ.filter (fun u : V => T.degree u = 2)) B := by
      rw [Finset.disjoint_left]; intro u h1 h2
      simp only [Finset.mem_filter, B] at h1 h2; omega
    rw [hun, Finset.sum_union hd1, Finset.sum_union hd2, hL, h2, zero_add]
  have hBnn : 0 ≤ ∑ u ∈ B, ((T.degree u : ℤ) - 2) :=
    Finset.sum_nonneg (fun u hu => by have := (Finset.mem_filter.mp hu).2; omega)
  have hL_eq : (leafCount T : ℤ) = (L.card : ℤ) := by
    have hnat : leafCount T = L.card := by
      unfold leafCount; convert rfl
    exact_mod_cast hnat
  refine ⟨by omega, ?_⟩
  constructor
  · intro h2 u
    have hB0 : ∑ x ∈ B, ((T.degree x : ℤ) - 2) = 0 := by linarith
    by_contra hgt
    have huB : u ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ u, by omega⟩
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x hx => by have := (Finset.mem_filter.mp hx).2; omega)).mp hB0 u huB
    omega
  · intro hle2
    have hBe : B = ∅ := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, B]
      have := hle2 u; omega
    rw [hBe, Finset.sum_empty, add_zero] at hsplit
    omega

omit [Fintype V] [DecidableEq V] in
/-- Triangle inequality for `SimpleGraph.dist` on any connected graph. -/
private lemma dist_triangle {G : SimpleGraph V} (hC : G.Connected) (x y z : V) :
    G.dist x z ≤ G.dist x y + G.dist y z := by
  obtain ⟨p1, hp1⟩ := hC.exists_walk_length_eq_dist x y
  obtain ⟨p2, hp2⟩ := hC.exists_walk_length_eq_dist y z
  have := G.dist_le (p1.append p2)
  rw [Walk.length_append, hp1, hp2] at this
  exact this

/-- Helper: following unique children away from a root `p` in a degree-`≤ 2` subtree builds
a maximal pendant path. -/
private lemma build_pendant_arm {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) (p v u₀ : V) (hvu₀ : T.Adj v u₀) (hdep0 : T.dist u₀ p = T.dist v p + 1)
    (hdeg_sub : ∀ x : V, T.dist v x = 1 + T.dist u₀ x → T.degree x ≤ 2) :
    ∃ (k : ℕ) (hk : 1 ≤ k) (arm : Fin k ↪ V),
      arm ⟨0, hk⟩ = u₀ ∧
      (∀ i : Fin k, T.dist p (arm i) = T.dist v p + (i.val + 1)) ∧
      (∀ (i : Fin k) (w : V), T.Adj (arm i) w ↔
        (i.val = 0 ∧ w = v) ∨
        (∃ h : 0 < i.val, w = arm ⟨i.val - 1, by omega⟩) ∨
        (∃ h : i.val + 1 < k, w = arm ⟨i.val + 1, h⟩)) := by
  -- Every vertex `x` reachable from `u₀` away from `v` has `T.dist p x = T.dist v p + 1 + T.dist u₀ x`
  -- and at most one neighbor farther from `p`.
  have hdist_p_add : ∀ x : V, T.dist v x = 1 + T.dist u₀ x →
      T.dist p x = T.dist v p + 1 + T.dist u₀ x := by
    intro x hx
    obtain ⟨q1, hq1⟩ := hT.connected.exists_walk_length_eq_dist p v
    obtain ⟨q2, hq2⟩ := hT.connected.exists_walk_length_eq_dist u₀ x
    have hp1 : q1.IsPath := q1.isPath_of_length_eq_dist hq1
    have hp2 : q2.IsPath := q2.isPath_of_length_eq_dist hq2
    let q2' : T.Walk v x := q2.cons hvu₀
    have hp2' : q2'.IsPath := q2'.isPath_of_length_eq_dist (by simp [q2', hq2]; omega)
    have hcomb : (q1.append q2').IsPath := by
      apply isPath_append_of_disjoint hp1 hp2'
      intro y hy1 hy2
      by_contra hyv
      have hy_q2 : y ∈ q2.support := by
        simp only [q2', Walk.support_cons, List.mem_cons] at hy2
        exact hy2.resolve_left hyv
      have hdy1 : T.dist p y + T.dist y v = T.dist p v := by
        have hlen := congrArg Walk.length (Walk.take_spec q1 hy1)
        rw [Walk.length_append, hq1] at hlen
        have hle1 := T.dist_le (q1.takeUntil y hy1)
        have hle2 := T.dist_le (q1.dropUntil y hy1)
        have htri := dist_triangle hT.connected p y v
        omega
      have hlen_u0y : T.dist u₀ y + 1 = T.dist v y := by
        have h3 := congrArg Walk.length (Walk.take_spec q2 hy_q2)
        rw [Walk.length_append, hq2] at h3
        have hle_a := T.dist_le (q2.takeUntil y hy_q2)
        have hle_b := T.dist_le (q2.dropUntil y hy_q2)
        have htri_u := dist_triangle hT.connected u₀ y x
        have htri_v := dist_triangle hT.connected v y x
        have hvu := dist_eq_one_of_adj hvu₀
        have htri_vu := dist_triangle hT.connected v u₀ y
        have htri_uv := dist_triangle hT.connected u₀ v y
        rw [SimpleGraph.dist_comm (u := u₀) (v := v)] at htri_uv
        omega
      have htri_p : T.dist p u₀ ≤ T.dist p y + T.dist y u₀ := dist_triangle hT.connected p y u₀
      rw [SimpleGraph.dist_comm (u := p) (v := u₀), SimpleGraph.dist_comm (u := y) (v := u₀)] at htri_p
      rw [SimpleGraph.dist_comm (u := p) (v := v), SimpleGraph.dist_comm (u := y) (v := v)] at hdy1
      have hvy_pos : 1 ≤ T.dist v y := by
        by_contra h0
        have : v = y := (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp (by omega)).resolve_right
          (not_not.mpr (hT.connected v y))
        exact hyv this.symm
      omega
    rw [dist_eq_length_of_isPath hT hcomb, Walk.length_append, Walk.length_cons, hq1, hq2,
      SimpleGraph.dist_comm (u := p) (v := v)]
    omega
  -- Let `S = {x : V | T.dist v x = 1 + T.dist u₀ x}`!
  let S : Finset V := Finset.univ.filter (fun x : V => T.dist v x = 1 + T.dist u₀ x)
  have hu₀S : u₀ ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.dist_self, add_zero]
    exact dist_eq_one_of_adj hvu₀
  have hS_inj : ∀ x ∈ S, ∀ y ∈ S, T.dist u₀ x = T.dist u₀ y → x = y := by
    -- Induction on `d = T.dist u₀ x`
    intro x hx y hy hdeq
    generalize hd : T.dist u₀ x = d
    rw [hd] at hdeq
    induction d generalizing x y with
    | zero =>
      have hx0 : x = u₀ := (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hd).resolve_right
        (not_not.mpr (hT.connected u₀ x)) |>.symm
      have hy0 : y = u₀ := (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hdeq.symm).resolve_right
        (not_not.mpr (hT.connected u₀ y)) |>.symm
      exact hx0.trans hy0.symm
    | succ d ih =>
      have hxu : x ≠ u₀ := fun h => by subst h; simp at hd
      have hyu : y ≠ u₀ := fun h => by subst h; simp at hdeq
      obtain ⟨px, hpx⟩ := before_exists hT hxu
      obtain ⟨py, hpy⟩ := before_exists hT hyu
      have hpx_S : px ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        have htri1 := dist_triangle hT.connected v u₀ px
        have hvu := dist_eq_one_of_adj hvu₀
        have htri2 := dist_triangle hT.connected v px x
        have hpxx := dist_eq_one_of_adj hpx.1.symm
        have hpxd := hpx.2
        rw [SimpleGraph.dist_comm (u := px) (v := u₀), SimpleGraph.dist_comm (u := x) (v := u₀)] at hpxd
        omega
      have hpy_S : py ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        have htri1 := dist_triangle hT.connected v u₀ py
        have hvu := dist_eq_one_of_adj hvu₀
        have htri2 := dist_triangle hT.connected v py y
        have hpyy := dist_eq_one_of_adj hpy.1.symm
        have hpyd := hpy.2
        rw [SimpleGraph.dist_comm (u := py) (v := u₀), SimpleGraph.dist_comm (u := y) (v := u₀)] at hpyd
        omega
      have hdpx : T.dist u₀ px = d := by
        have := hpx.2
        rw [SimpleGraph.dist_comm (u := px) (v := u₀), SimpleGraph.dist_comm (u := x) (v := u₀)] at this
        omega
      have hdpy : T.dist u₀ py = d := by
        have := hpy.2
        rw [SimpleGraph.dist_comm (u := py) (v := u₀), SimpleGraph.dist_comm (u := y) (v := u₀)] at this
        omega
      have hpeq : px = py := ih px hpx_S py hpy_S hdpy.symm hdpx
      subst hpeq
      have hpx_v : px ≠ v := by
        intro h; subst h
        have := (Finset.mem_filter.mp hpx_S).2
        simp only [SimpleGraph.dist_self] at this
        omega
      obtain ⟨par, hpar⟩ := before_exists hT hpx_v
      have hdeg := hdeg_sub px (Finset.mem_filter.mp hpx_S).2
      have hpar_ne_x : par ≠ x := by
        intro h; subst h
        have h1 := hpar.2
        have h2 := (Finset.mem_filter.mp hpx_S).2
        have h3 := (Finset.mem_filter.mp hx).2
        rw [SimpleGraph.dist_comm (u := par) (v := v), SimpleGraph.dist_comm (u := px) (v := v)] at h1
        omega
      have hpar_ne_y : par ≠ y := by
        intro h; subst h
        have h1 := hpar.2
        have h2 := (Finset.mem_filter.mp hpx_S).2
        have h3 := (Finset.mem_filter.mp hy).2
        rw [SimpleGraph.dist_comm (u := par) (v := v), SimpleGraph.dist_comm (u := px) (v := v)] at h1
        omega
      by_contra hxy
      have hsub : ({par, x, y} : Finset V) ⊆ T.neighborFinset px := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rw [SimpleGraph.mem_neighborFinset]
        rcases hw with rfl | rfl | rfl
        · exact hpar.1
        · exact hpx.1.symm
        · exact hpy.1.symm
      have hcard3 : ({par, x, y} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hpar_ne_x, hpar_ne_y]),
          Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
      rw [← T.card_neighborFinset_eq_degree] at hdeg
      have := Finset.card_le_card hsub
      omega
  -- Also `S` is downward-closed in `dist u₀`
  have hS_down : ∀ {t : ℕ}, (∃ x ∈ S, T.dist u₀ x = t + 1) → ∃ y ∈ S, T.dist u₀ y = t := by
    rintro t ⟨x, hx, hdx⟩
    have hxu : x ≠ u₀ := fun h => by subst h; simp at hdx
    obtain ⟨px, hpx⟩ := before_exists hT hxu
    refine ⟨px, ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have htri1 := dist_triangle hT.connected v u₀ px
      have hvu := dist_eq_one_of_adj hvu₀
      have htri2 := dist_triangle hT.connected v px x
      have hpxx := dist_eq_one_of_adj hpx.1.symm
      have hpxd := hpx.2
      rw [SimpleGraph.dist_comm (u := px) (v := u₀), SimpleGraph.dist_comm (u := x) (v := u₀)] at hpxd
      omega
    · have := hpx.2
      rw [SimpleGraph.dist_comm (u := px) (v := u₀), SimpleGraph.dist_comm (u := x) (v := u₀)] at this
      omega
  -- So the distances `{dist u₀ x | x ∈ S}` form `{0, 1, ..., k - 1}` where `k = S.card`!
  set k := S.card
  have hk : 1 ≤ k := Finset.card_pos.mpr ⟨u₀, hu₀S⟩
  have hex_at : ∀ t < k, ∃ x ∈ S, T.dist u₀ x = t := by
    -- Image `S.image (T.dist u₀)` has cardinality `k` (by `hS_inj`) and is downward closed!
    have himg_card : (S.image (T.dist u₀)).card = k :=
      Finset.card_image_of_injOn (fun x hx y hy h => hS_inj x hx y hy h)
    have hdown_img : ∀ {m : ℕ}, m + 1 ∈ S.image (T.dist u₀) → m ∈ S.image (T.dist u₀) := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨x, hx, hdx⟩
      obtain ⟨y, hy, hdy⟩ := hS_down ⟨x, hx, hdx⟩
      exact Finset.mem_image.mpr ⟨y, hy, hdy⟩
    have hdown_le : ∀ {m n : ℕ}, m ≤ n → n ∈ S.image (T.dist u₀) → m ∈ S.image (T.dist u₀) := by
      intro m n hmn hn
      induction hmn with
      | refl => exact hn
      | step _ ih => exact ih (hdown_img hn)
    have heq_range : S.image (T.dist u₀) = Finset.range k := by
      by_contra hne
      -- If not `Finset.range k`, some `m ≥ k` lies in `S.image (T.dist u₀)` (since cardinalities equal `k`),
      -- so by downward closure `Finset.range (m + 1) ⊆ S.image`, contradicting `card = k`!
      have hnot_sub : ¬ S.image (T.dist u₀) ⊆ Finset.range k := by
        intro hsub
        exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [himg_card, Finset.card_range]))
      obtain ⟨m, hm_in, hm_not⟩ := Finset.not_subset.mp hnot_sub
      have hmk : k ≤ m := by simp only [Finset.mem_range] at hm_not; omega
      have hsub2 : Finset.range (k + 1) ⊆ S.image (T.dist u₀) := by
        intro t ht
        rw [Finset.mem_range] at ht
        exact hdown_le (by omega) hm_in
      have hcard_le := Finset.card_le_card hsub2
      rw [Finset.card_range, himg_card] at hcard_le
      omega
    intro t ht
    have hmem : t ∈ S.image (T.dist u₀) := by rw [heq_range, Finset.mem_range]; exact ht
    exact Finset.mem_image.mp hmem
  -- Define `arm : Fin k ↪ V` choosing the unique `x ∈ S` at distance `i.val` from `u₀`!
  let f : Fin k → V := fun i => Classical.choose (hex_at i.val i.isLt)
  have hf_S : ∀ i : Fin k, f i ∈ S := fun i => (Classical.choose_spec (hex_at i.val i.isLt)).1
  have hf_dist : ∀ i : Fin k, T.dist u₀ (f i) = i.val :=
    fun i => (Classical.choose_spec (hex_at i.val i.isLt)).2
  have hf_inj : Function.Injective f := by
    intro i j hij
    have := hf_dist i
    rw [hij, hf_dist j] at this
    exact Fin.ext this.symm
  let arm : Fin k ↪ V := ⟨f, hf_inj⟩
  have harm0 : arm ⟨0, hk⟩ = u₀ :=
    hS_inj (arm ⟨0, hk⟩) (hf_S ⟨0, hk⟩) u₀ hu₀S (by
      show T.dist u₀ (f ⟨0, hk⟩) = T.dist u₀ u₀
      rw [hf_dist ⟨0, hk⟩, SimpleGraph.dist_self])
  have harm_step : ∀ (t : ℕ) (ht : t + 1 < k),
      T.Adj (arm ⟨t, by omega⟩) (arm ⟨t + 1, ht⟩) := by
    intro t ht
    have hne : arm ⟨t + 1, ht⟩ ≠ u₀ := by
      intro h
      have h1 := hf_dist ⟨t + 1, ht⟩
      change T.dist u₀ (arm ⟨t + 1, ht⟩) = t + 1 at h1
      rw [h, SimpleGraph.dist_self] at h1
      omega
    obtain ⟨px, hpx⟩ := before_exists hT hne
    have hpx_S : px ∈ S := by
      have hx := hf_S ⟨t + 1, ht⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have htri1 := dist_triangle hT.connected v u₀ px
      have hvu := dist_eq_one_of_adj hvu₀
      have htri2 := dist_triangle hT.connected v px (arm ⟨t + 1, ht⟩)
      have hpxx := dist_eq_one_of_adj hpx.1.symm
      have hpxd := hpx.2
      rw [SimpleGraph.dist_comm (u := px) (v := u₀),
        SimpleGraph.dist_comm (u := arm ⟨t + 1, ht⟩) (v := u₀)] at hpxd
      change T.dist v (arm ⟨t + 1, ht⟩) = 1 + T.dist u₀ (arm ⟨t + 1, ht⟩) at hx
      omega
    have hdpx : T.dist u₀ px = t := by
      have h1 := hpx.2
      have h2 := hf_dist ⟨t + 1, ht⟩
      rw [SimpleGraph.dist_comm (u := px) (v := u₀),
        SimpleGraph.dist_comm (u := arm ⟨t + 1, ht⟩) (v := u₀)] at h1
      change T.dist u₀ (arm ⟨t + 1, ht⟩) = t + 1 at h2
      omega
    have hpeq : px = arm ⟨t, by omega⟩ :=
      hS_inj px hpx_S (arm ⟨t, by omega⟩) (hf_S _) (hdpx.trans (hf_dist ⟨t, by omega⟩).symm)
    rw [← hpeq]
    exact hpx.1.symm
  refine ⟨k, hk, arm, harm0, ?_, ?_⟩
  · intro i
    have h1 := hdist_p_add (arm i) (Finset.mem_filter.mp (hf_S i)).2
    have h2 := hf_dist i
    dsimp [arm] at *; omega
  · intro i w
    constructor
    · intro hadj
      have hiS := (Finset.mem_filter.mp (hf_S i)).2
      rcases before_or hT v hadj with hcl | hfa
      · -- `w` is closer to `v` than `arm i`
        by_cases hi0 : i.val = 0
        · have heq : arm i = u₀ := by
            have : i = ⟨0, hk⟩ := Fin.ext hi0; rw [this, harm0]
          rw [heq] at hcl
          have hv_bef : Before T v u₀ v :=
            ⟨hvu₀.symm, by rw [SimpleGraph.dist_self, dist_eq_one_of_adj hvu₀.symm]⟩
          exact Or.inl ⟨hi0, before_unique hT hcl hv_bef⟩
        · have hi_pos : 0 < i.val := by omega
          have hprev_adj := (harm_step (i.val - 1) (by omega)).symm
          have hi_eq : (⟨i.val - 1 + 1, by omega⟩ : Fin k) = i := Fin.ext (by dsimp; omega)
          rw [hi_eq] at hprev_adj
          have hprev_S := (Finset.mem_filter.mp (hf_S ⟨i.val - 1, by omega⟩)).2
          have hprev_bef : Before T v (arm i) (arm ⟨i.val - 1, by omega⟩) := by
            refine ⟨hprev_adj, ?_⟩
            rw [SimpleGraph.dist_comm (u := arm ⟨i.val - 1, by omega⟩) (v := v),
              SimpleGraph.dist_comm (u := arm i) (v := v)]
            change T.dist v (f ⟨i.val - 1, by omega⟩) + 1 = T.dist v (f i)
            rw [hprev_S, hiS]
            have h1 := hf_dist i
            have h2 := hf_dist ⟨i.val - 1, by omega⟩
            dsimp only at h1 h2; omega
          exact Or.inr (Or.inl ⟨hi_pos, before_unique hT hcl hprev_bef⟩)
      · -- `w` is farther from `v` than `arm i`
        have hw_dist_v : T.dist v w = T.dist v (arm i) + 1 := by
          have := hfa.2
          rw [SimpleGraph.dist_comm (u := arm i) (v := v), SimpleGraph.dist_comm (u := w) (v := v)] at this
          omega
        have hw_dist_u0 : T.dist u₀ w = i.val + 1 := by
          have h1 := hT.dist_eq_dist_add_one_of_adj u₀ hadj
          have h2 := hf_dist i
          have htri := dist_triangle hT.connected v u₀ w
          have hvu := dist_eq_one_of_adj hvu₀
          dsimp [arm] at *
          rcases h1 with h1 | h1 <;> omega
        have hwS : w ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          have h2 := hf_dist i
          dsimp [arm] at *; omega
        have hlt : i.val + 1 < k := by
          by_contra hge
          have hmem : i.val + 1 ∈ S.image (T.dist u₀) :=
            Finset.mem_image.mpr ⟨w, hwS, hw_dist_u0⟩
          have himg_card : (S.image (T.dist u₀)).card = k :=
            Finset.card_image_of_injOn (fun x hx y hy h => hS_inj x hx y hy h)
          have hsub : Finset.range (k + 1) ⊆ S.image (T.dist u₀) := by
            intro t ht
            rw [Finset.mem_range] at ht
            by_cases htk : t < k
            · obtain ⟨x, hx, hdx⟩ := hex_at t htk
              exact Finset.mem_image.mpr ⟨x, hx, hdx⟩
            · have : t = k := by omega
              subst this
              have : i.val + 1 = k := by omega
              rw [← this]; exact hmem
          have hcard_le := Finset.card_le_card hsub
          rw [Finset.card_range, himg_card] at hcard_le
          omega
        exact Or.inr (Or.inr ⟨hlt, hS_inj w hwS (arm ⟨i.val + 1, hlt⟩) (hf_S _)
          (hw_dist_u0.trans (hf_dist ⟨i.val + 1, hlt⟩).symm)⟩)
    · rintro (⟨hi0, rfl⟩ | ⟨hpos, rfl⟩ | ⟨hlt, rfl⟩)
      · have : i = ⟨0, hk⟩ := Fin.ext hi0
        rw [this, harm0]; exact hvu₀.symm
      · have h := (harm_step (i.val - 1) (by omega)).symm
        have hi_eq : (⟨i.val - 1 + 1, by omega⟩ : Fin k) = i := Fin.ext (by dsimp; omega)
        rwa [hi_eq] at h
      · exact harm_step i.val hlt

omit [Fintype V] [DecidableEq V] in
/-- Any walk starting outside a vertex set `S` and ending in `S` crosses an edge into `S`. -/
private lemma exists_edge_entering_set {T : SimpleGraph V} {S : List V} {z p₀ : V}
    (hp₀ : p₀ ∈ S) (wlk : T.Walk z p₀) (hz : z ∉ S) :
    ∃ x w : V, x ∉ S ∧ w ∈ S ∧ T.Adj x w := by
  induction wlk with
  | nil => exact (hz hp₀).elim
  | @cons a b _ hadj rest ih =>
    by_cases hb : b ∈ S
    · exact ⟨a, b, hz, hb, hadj⟩
    · exact ih hp₀ hb

/-- Lemma 4.1: Every finite tree with a vertex of degree `≥ 3` admits a valid `GraftConfig`. -/
theorem exists_graftConfig_of_deg_ge_three {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) (hbranch : ∃ u : V, 3 ≤ T.degree u) :
    Nonempty (GraftConfig T) := by
  classical
  obtain ⟨u_br, hu_br⟩ := hbranch
  have : Nonempty V := ⟨u_br⟩
  -- Pick a diameter pair `(p₀, q₀)` maximizing `T.dist`
  obtain ⟨⟨p₀, q₀⟩, _, hdiam⟩ :=
    Finset.exists_max_image (Finset.univ ×ˢ Finset.univ : Finset (V × V))
      (fun xy => T.dist xy.1 xy.2) (Finset.univ_nonempty.product Finset.univ_nonempty)
  set L := T.dist p₀ q₀
  have hle_L : ∀ x y : V, T.dist x y ≤ L :=
    fun x y => hdiam (x, y) (Finset.mem_product.mpr ⟨Finset.mem_univ x, Finset.mem_univ y⟩)
  -- The unique `p₀`–`q₀` path must contain a vertex `w` of degree `≥ 3`
  obtain ⟨P, hP, _⟩ := hT.existsUnique_path p₀ q₀
  have hex_w : ∃ w ∈ P.support, 3 ≤ T.degree w := by
    by_contra hno
    push Not at hno
    by_cases huP : u_br ∈ P.support
    · exact absurd hu_br (not_le.mpr (hno u_br huP))
    · obtain ⟨q, _, _⟩ := hT.existsUnique_path u_br p₀
      obtain ⟨x, w, hxP, hwP, hxw⟩ := exists_edge_entering_set (Walk.start_mem_support P) q huP
      by_cases hwp : w = p₀
      · subst hwp
        have hp' : (P.cons hxw).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hP, hxP⟩
        have hd := dist_eq_length_of_isPath hT hp'
        have hL := hle_L x q₀
        have hPlen := dist_eq_length_of_isPath hT hP
        simp only [Walk.length_cons] at hd
        omega
      · by_cases hwq : w = q₀
        · subst hwq
          have hp' : (P.reverse.cons hxw).IsPath :=
            (Walk.cons_isPath_iff _ _).mpr ⟨hP.reverse, by simpa [Walk.support_reverse] using hxP⟩
          have hd := dist_eq_length_of_isPath hT hp'
          have hL := hle_L x p₀
          have hPlen := dist_eq_length_of_isPath hT hP
          simp only [Walk.length_cons, Walk.length_reverse] at hd
          omega
        · -- `w` is an interior vertex of `P`, so `w` has two distinct neighbors `a, b ∈ P.support`!
          have hne_p : w ≠ p₀ := hwp
          have hne_q : w ≠ q₀ := hwq
          let P1 := P.takeUntil w hwP
          let P2 := P.dropUntil w hwP
          have hP1 : P1.IsPath := hP.takeUntil hwP
          have hP2 : P2.IsPath := hP.dropUntil hwP
          generalize hP1r : P1.reverse = R1
          cases R1 with
          | nil => exact (hne_p rfl).elim
          | @cons _ a _ hwa rest1 =>
            generalize hP2eq : P2 = R2
            cases R2 with
            | nil => exact (hne_q rfl).elim
            | @cons _ b _ hwb rest2 =>
              have haP : a ∈ P.support := by
                have hmem : a ∈ P1.reverse.support := by
                  rw [hP1r]; exact List.mem_cons_of_mem _ (Walk.start_mem_support rest1)
                rw [Walk.support_reverse, List.mem_reverse] at hmem
                exact Walk.support_takeUntil_subset_support P hwP hmem
              have hbP : b ∈ P.support := by
                have hmem : b ∈ P2.support := by
                  rw [hP2eq]; exact List.mem_cons_of_mem _ (Walk.start_mem_support rest2)
                exact Walk.support_dropUntil_subset_support P hwP hmem
              have hab : a ≠ b := by
                intro heq; subst heq
                have hnd := hP.support_nodup
                rw [← Walk.take_spec P hwP, Walk.support_append, List.nodup_append] at hnd
                have ha1 : a ∈ P1.support := by
                  have : a ∈ P1.reverse.support := by
                    rw [hP1r]; exact List.mem_cons_of_mem _ (Walk.start_mem_support rest1)
                  simpa [Walk.support_reverse] using this
                have ha2 : a ∈ P2.support.tail := by
                  rw [hP2eq]; exact Walk.start_mem_support rest2
                exact hnd.2.2 a ha1 a ha2 rfl
              have hxa : x ≠ a := fun h => hxP (h ▸ haP)
              have hxb : x ≠ b := fun h => hxP (h ▸ hbP)
              have hsub : ({x, a, b} : Finset V) ⊆ T.neighborFinset w := by
                intro z hz
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rw [SimpleGraph.mem_neighborFinset]
                rcases hz with rfl | rfl | rfl
                · exact hxw.symm
                · exact hwa
                · exact hwb
              have hcard3 : ({x, a, b} : Finset V).card = 3 := by
                rw [Finset.card_insert_of_notMem (by simp [hxa, hxb]),
                  Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
              have hle2 := hno w hwP
              rw [← T.card_neighborFinset_eq_degree] at hle2
              have := Finset.card_le_card hsub
              omega
  obtain ⟨w, hwP, hw_deg⟩ := hex_w
  have hw_sum : T.dist p₀ w + T.dist q₀ w = L := by
    have hlen := congrArg Walk.length (Walk.take_spec P hwP)
    rw [Walk.length_append, ← dist_eq_length_of_isPath hT hP] at hlen
    have h1 := dist_eq_length_of_isPath hT (hP.takeUntil hwP)
    have h2 := dist_eq_length_of_isPath hT (hP.dropUntil hwP)
    rw [SimpleGraph.dist_comm (u := q₀) (v := w)]; omega
  -- Choose root `p ∈ {p₀, q₀}` maximizing distance to `w`, so `2 * T.dist p w ≥ L`
  obtain ⟨p, hp_half⟩ : ∃ p : V, L ≤ 2 * T.dist p w := by
    rcases le_total (T.dist p₀ w) (T.dist q₀ w) with h | h
    · exact ⟨q₀, by omega⟩
    · exact ⟨p₀, by omega⟩
  -- Pick a deepest branching vertex `v` (`3 ≤ T.degree v`) from `p`
  let B := Finset.univ.filter (fun x : V => 3 ≤ T.degree x)
  have hwB : w ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw_deg⟩
  obtain ⟨v, hvB, hv_max⟩ := Finset.exists_max_image B (fun x => T.dist p x) ⟨w, hwB⟩
  have hv_deg : 3 ≤ T.degree v := (Finset.mem_filter.mp hvB).2
  have hv_half : L ≤ 2 * T.dist p v := by
    have := hv_max w hwB; omega
  have hL_pos : 1 ≤ L := by
    rw [← T.card_neighborFinset_eq_degree] at hv_deg
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (T.neighborFinset v).card)
    have hadj := (mem_neighborFinset T v u).mp hu
    have := hle_L v u
    rw [dist_eq_one_of_adj hadj] at this; exact this
  have hvp : v ≠ p := by
    intro h; subst h; simp at hv_half; omega
  obtain ⟨par, hpar⟩ := before_exists hT hvp
  -- Pick two distinct children `u₁, u₂` of `v` away from `p`
  have hpar_mem : par ∈ T.neighborFinset v := (mem_neighborFinset T v par).mpr hpar.1
  have hch_card : 2 ≤ ((T.neighborFinset v).erase par).card := by
    rw [Finset.card_erase_of_mem hpar_mem, T.card_neighborFinset_eq_degree]; omega
  obtain ⟨u₁, hu₁, u₂, hu₂, hu₁₂⟩ := Finset.one_lt_card.mp (by omega : 1 < ((T.neighborFinset v).erase par).card)
  have hu₁_adj : T.Adj v u₁ := (mem_neighborFinset T v u₁).mp (Finset.mem_erase.mp hu₁).2
  have hu₂_adj : T.Adj v u₂ := (mem_neighborFinset T v u₂).mp (Finset.mem_erase.mp hu₂).2
  have hu₁_dep : T.dist u₁ p = T.dist v p + 1 := by
    rcases before_or hT p hu₁_adj with h1 | h2
    · exact ((Finset.mem_erase.mp hu₁).1 (before_unique hT h1 hpar)).elim
    · exact h2.2.symm
  have hu₂_dep : T.dist u₂ p = T.dist v p + 1 := by
    rcases before_or hT p hu₂_adj with h1 | h2
    · exact ((Finset.mem_erase.mp hu₂).1 (before_unique hT h1 hpar)).elim
    · exact h2.2.symm
  have hdeg_sub : ∀ {u₀ : V}, T.Adj v u₀ → T.dist u₀ p = T.dist v p + 1 →
      ∀ x : V, T.dist v x = 1 + T.dist u₀ x → T.degree x ≤ 2 := by
    intro u₀ hvu₀ hdep0 x hx
    obtain ⟨q1, hq1⟩ := hT.connected.exists_walk_length_eq_dist p v
    obtain ⟨q2, hq2⟩ := hT.connected.exists_walk_length_eq_dist u₀ x
    have hp1 : q1.IsPath := q1.isPath_of_length_eq_dist hq1
    have hp2' : (q2.cons hvu₀).IsPath :=
      (q2.cons hvu₀).isPath_of_length_eq_dist (by simp [hq2]; omega)
    have hcomb : (q1.append (q2.cons hvu₀)).IsPath := by
      apply isPath_append_of_disjoint hp1 hp2'
      intro y hy1 hy2
      by_contra hyv
      have hy_q2 : y ∈ q2.support := (List.mem_cons.mp hy2).resolve_left hyv
      have hdy1 : T.dist p y + T.dist y v = T.dist p v := by
        have hlen := congrArg Walk.length (Walk.take_spec q1 hy1)
        rw [Walk.length_append, hq1] at hlen
        have hle1 := T.dist_le (q1.takeUntil y hy1)
        have hle2 := T.dist_le (q1.dropUntil y hy1)
        have htri := dist_triangle hT.connected p y v
        omega
      have hlen_u0y : T.dist u₀ y + 1 = T.dist v y := by
        have h3 := congrArg Walk.length (Walk.take_spec q2 hy_q2)
        rw [Walk.length_append, hq2] at h3
        have hle_a := T.dist_le (q2.takeUntil y hy_q2)
        have hle_b := T.dist_le (q2.dropUntil y hy_q2)
        have htri_u := dist_triangle hT.connected u₀ y x
        have htri_v := dist_triangle hT.connected v y x
        have hvu := dist_eq_one_of_adj hvu₀
        have htri_vu := dist_triangle hT.connected v u₀ y
        have htri_uv := dist_triangle hT.connected u₀ v y
        rw [SimpleGraph.dist_comm (u := u₀) (v := v)] at htri_uv
        omega
      have htri_p := dist_triangle hT.connected p y u₀
      rw [SimpleGraph.dist_comm (u := p) (v := u₀), SimpleGraph.dist_comm (u := y) (v := u₀)] at htri_p
      rw [SimpleGraph.dist_comm (u := p) (v := v), SimpleGraph.dist_comm (u := y) (v := v)] at hdy1
      have hvy_pos : 1 ≤ T.dist v y := by
        by_contra h0
        have : v = y := (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp (by omega)).resolve_right
          (not_not.mpr (hT.connected v y))
        exact hyv this.symm
      omega
    have hpx : T.dist p x = T.dist p v + 1 + T.dist u₀ x := by
      rw [dist_eq_length_of_isPath hT hcomb, Walk.length_append, Walk.length_cons, hq1, hq2]
      omega
    by_contra hgt
    have hxB : x ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ x, by omega⟩
    have := hv_max x hxB
    omega
  obtain ⟨k₁, hk₁, arm₁, harm₁0, harm₁_dep, harm₁_adj⟩ :=
    build_pendant_arm hT p v u₁ hu₁_adj hu₁_dep (hdeg_sub hu₁_adj hu₁_dep)
  obtain ⟨k₂, hk₂, arm₂, harm₂0, harm₂_dep, harm₂_adj⟩ :=
    build_pendant_arm hT p v u₂ hu₂_adj hu₂_dep (hdeg_sub hu₂_adj hu₂_dep)
  -- The two arms are disjoint!
  have hdisj12 : Disjoint (Finset.univ.image arm₁) (Finset.univ.image arm₂) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨j, _, heq⟩
    have hstep1 : ∀ (t : ℕ) (ht : t + 1 < k₁), T.Adj (arm₁ ⟨t, by omega⟩) (arm₁ ⟨t + 1, ht⟩) :=
      fun t ht => (harm₁_adj ⟨t, by omega⟩ _).mpr (Or.inr (Or.inr ⟨ht, rfl⟩))
    have hstep2 : ∀ (t : ℕ) (ht : t + 1 < k₂), T.Adj (arm₂ ⟨t, by omega⟩) (arm₂ ⟨t + 1, ht⟩) :=
      fun t ht => (harm₂_adj ⟨t, by omega⟩ _).mpr (Or.inr (Or.inr ⟨ht, rfl⟩))
    have hwalk_snd_concat : ∀ {x y z : V} (q : T.Walk x y), 0 < q.length → ∀ (e : T.Adj y z),
        (q.concat e).snd = q.snd := by
      intro x y z q hq e
      cases q with
      | nil => simp at hq
      | cons _ _ => simp [Walk.concat, Walk.snd]
    have hwalk_snd_copy : ∀ {x y x' y' : V} (q : T.Walk x y) (hx : x = x') (hy : y = y'),
        0 < q.length → (Walk.copy q hx hy).snd = q.snd := by
      intro x y x' y' q hx hy hq
      subst hx; subst hy
      cases q with
      | nil => simp at hq
      | cons _ _ => rfl
    have hmk' : ∀ {k : ℕ} (hk : 1 ≤ k) (arm : Fin k ↪ V) (u₀ : V)
        (h0 : arm ⟨0, hk⟩ = u₀) (hvu : T.Adj v u₀)
        (hdep : ∀ t : Fin k, T.dist p (arm t) = T.dist v p + (t.val + 1))
        (hst : ∀ (t : ℕ) (ht : t + 1 < k), T.Adj (arm ⟨t, by omega⟩) (arm ⟨t + 1, ht⟩))
        (idx : Fin k), ∃ q : T.Walk v (arm idx), q.IsPath ∧ q.length = idx.val + 1 ∧ q.snd = u₀ := by
      intro k hk arm u₀ h0 hvu hdep hst ⟨t, ht⟩
      induction t with
      | zero =>
        refine ⟨Walk.cons (h0.symm ▸ hvu) Walk.nil, ?_, rfl, by simp [h0]⟩
        rw [Walk.cons_isPath_iff]
        refine ⟨Walk.IsPath.nil, fun hmem => ?_⟩
        simp only [Walk.support_nil, List.mem_singleton] at hmem
        have := hdep ⟨0, ht⟩
        rw [← hmem, SimpleGraph.dist_comm (u := p) (v := v)] at this; omega
      | succ t ih =>
        obtain ⟨q, hq, hqlen, hsnd⟩ := ih (by omega)
        refine ⟨q.concat (hst t ht), ?_, by simp [hqlen], ?_⟩
        · rw [Walk.concat_isPath_iff]
          refine ⟨hq, fun hmem => ?_⟩
          have htri := dist_triangle hT.connected p v (arm ⟨t + 1, ht⟩)
          have hle_vw : T.dist v (arm ⟨t + 1, ht⟩) ≤ q.length := by
            have hlen := congrArg Walk.length (Walk.take_spec q hmem)
            rw [Walk.length_append] at hlen
            have := T.dist_le (q.takeUntil _ hmem)
            omega
          have hd := hdep ⟨t + 1, ht⟩
          rw [SimpleGraph.dist_comm (u := v) (v := p)] at hd
          dsimp only at hd hqlen; omega
        · rw [hwalk_snd_concat q (by omega) (hst t ht), hsnd]
    obtain ⟨q1, hq1, _, hsnd1⟩ := hmk' hk₁ arm₁ u₁ harm₁0 hu₁_adj harm₁_dep hstep1 i
    obtain ⟨q2, hq2, hq2len, hsnd2⟩ := hmk' hk₂ arm₂ u₂ harm₂0 hu₂_adj harm₂_dep hstep2 j
    have hq2' : (Walk.copy q2 rfl heq).IsPath := (Walk.isPath_copy _ _ _).mpr hq2
    have hpeq := (hT.existsUnique_path v (arm₁ i)).unique hq1 hq2'
    have hsnd_eq := congrArg Walk.snd hpeq
    have hsnd_copy : (Walk.copy q2 rfl heq).snd = q2.snd :=
      hwalk_snd_copy q2 rfl heq (by omega)
    rw [hsnd1, hsnd_copy, hsnd2] at hsnd_eq
    exact hu₁₂ hsnd_eq
  -- Bound `k₁, k₂ ≤ T.dist p v` and show `T.dist p v + 1 ≤ |C|`!
  have hle_dpv : ∀ {k : ℕ} (hk : 1 ≤ k) (arm : Fin k ↪ V)
      (hdep : ∀ t : Fin k, T.dist p (arm t) = T.dist v p + (t.val + 1)),
      k ≤ T.dist p v := by
    intro k hk arm hdep
    have h1 := hdep ⟨k - 1, by omega⟩
    have h2 := hle_L p (arm ⟨k - 1, by omega⟩)
    rw [SimpleGraph.dist_comm (u := v) (v := p)] at h1
    dsimp only at h1; omega
  have hk₁_le : k₁ ≤ T.dist p v := hle_dpv hk₁ arm₁ harm₁_dep
  have hk₂_le : k₂ ≤ T.dist p v := hle_dpv hk₂ arm₂ harm₂_dep
  obtain ⟨qp, hqp, _⟩ := hT.existsUnique_path p v
  have hC_ge : T.dist p v + 1 ≤
      (Finset.univ \ (Finset.univ.image arm₁ ∪ Finset.univ.image arm₂)).card := by
    have hsub : qp.support.toFinset ⊆
        Finset.univ \ (Finset.univ.image arm₁ ∪ Finset.univ.image arm₂) := by
      intro x hx
      rw [List.mem_toFinset] at hx
      have hdx : T.dist p x ≤ T.dist p v := by
        have hlen := congrArg Walk.length (Walk.take_spec qp hx)
        rw [Walk.length_append, ← dist_eq_length_of_isPath hT hqp] at hlen
        have := T.dist_le (qp.takeUntil x hx)
        omega
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and,
        not_or, not_exists]
      refine ⟨fun i h => ?_, fun j h => ?_⟩
      · have := harm₁_dep i; rw [h, SimpleGraph.dist_comm (u := v) (v := p)] at this; omega
      · have := harm₂_dep j; rw [h, SimpleGraph.dist_comm (u := v) (v := p)] at this; omega
    have hcard_qp : qp.support.toFinset.card = T.dist p v + 1 := by
      rw [List.toFinset_card_of_nodup hqp.support_nodup, Walk.length_support,
        dist_eq_length_of_isPath hT hqp]
    rw [← hcard_qp]
    exact Finset.card_le_card hsub
  have hv_not1 : v ∉ Finset.univ.image arm₁ := by
    intro h; rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
    have := harm₁_dep i; rw [hi, SimpleGraph.dist_comm (u := v) (v := p)] at this; omega
  have hv_not2 : v ∉ Finset.univ.image arm₂ := by
    intro h; rcases Finset.mem_image.mp h with ⟨j, _, hj⟩
    have := harm₂_dep j; rw [hj, SimpleGraph.dist_comm (u := v) (v := p)] at this; omega
  -- Pick the longer arm as `armA` and shorter as `armB`
  rcases le_total k₂ k₁ with hle | hle
  · exact ⟨{
      v := v, a := k₁, b := k₂, ha := hk₁, hb := hk₂, hba := hle,
      armA := arm₁, armB := arm₂, hdisjAB := hdisj12,
      hvA := hv_not1, hvB := hv_not2,
      hC_card := by omega,
      hadjA := harm₁_adj, hadjB := harm₂_adj }⟩
  · exact ⟨{
      v := v, a := k₂, b := k₁, ha := hk₂, hb := hk₁, hba := hle,
      armA := arm₂, armB := arm₁, hdisjAB := hdisj12.symm,
      hvA := hv_not2, hvB := hv_not1,
      hC_card := by
        rw [Finset.union_comm]; omega,
      hadjA := harm₂_adj, hadjB := harm₁_adj }⟩

omit [DecidableEq V] in
/-- Every finite tree in which all vertices have degree `≤ 2` is isomorphic to `pathGraph n`. -/
theorem isTree_iso_pathGraph_of_deg_le_two {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) (hle2 : ∀ u : V, T.degree u ≤ 2) :
    Nonempty (T ≃g pathGraph (Fintype.card V)) := by
  classical
  set n := Fintype.card V
  by_cases hn0 : n = 0
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn0
    have : IsEmpty (Fin n) := by rw [hn0]; infer_instance
    exact ⟨{
      toEquiv := Equiv.equivOfIsEmpty V (Fin n)
      map_rel_iff' := fun {a _} => isEmptyElim a }⟩
  · by_cases hn1 : n = 1
    · have hcard : Fintype.card V = Fintype.card (Fin n) := by simp [n]
      let e : V ≃ Fin n := Fintype.equivOfCardEq hcard
      refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
      intro a b
      have hab : a = b := Fintype.card_le_one_iff.mp (by omega) a b
      subst hab
      simp [SimpleGraph.irrefl]
    · have hn2 : 2 ≤ n := by omega
      have hleaf := (leafCount_tree_props hT hn2).2.mpr hle2
      have hex_leaf : ∃ x₀ : V, T.degree x₀ = 1 := by
        have hlc : leafCount T = (Finset.univ.filter (fun u : V => T.degree u = 1)).card := by
          unfold leafCount; convert rfl
        have hpos : 0 < (Finset.univ.filter (fun u : V => T.degree u = 1)).card := by omega
        obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hpos
        exact ⟨x₀, (Finset.mem_filter.mp hx₀).2⟩
      obtain ⟨x₀, hx₀_deg⟩ := hex_leaf
      -- `x₀` has a unique neighbor `u₀`
      have hx₀_nf : (T.neighborFinset x₀).card = 1 := by
        rw [T.card_neighborFinset_eq_degree, hx₀_deg]
      obtain ⟨u₀, hu₀_eq⟩ := Finset.card_eq_one.mp hx₀_nf
      have hxu₀ : T.Adj x₀ u₀ := by
        have : u₀ ∈ T.neighborFinset x₀ := by rw [hu₀_eq]; exact Finset.mem_singleton_self u₀
        exact (mem_neighborFinset T x₀ u₀).mp this
      have hdep0 : T.dist u₀ x₀ = T.dist x₀ x₀ + 1 := by
        rw [SimpleGraph.dist_self, zero_add, dist_eq_one_of_adj hxu₀.symm]
      obtain ⟨k, hk, arm, harm0, harm_dep, harm_adj⟩ :=
        build_pendant_arm hT x₀ x₀ u₀ hxu₀ hdep0 (fun x _ => hle2 x)
      -- Show every vertex `x ≠ x₀` lies in `Finset.univ.image arm`!
      have hcover : ∀ x : V, x ≠ x₀ → x ∈ Finset.univ.image arm := by
        intro x hne
        obtain ⟨q, hq⟩ := hT.connected.exists_walk_length_eq_dist x₀ x
        cases q with
        | nil => exact (hne rfl).elim
        | @cons _ w _ hxw rest =>
          have hwu₀ : w = u₀ := by
            have : w ∈ T.neighborFinset x₀ := (mem_neighborFinset T x₀ w).mpr hxw
            rw [hu₀_eq, Finset.mem_singleton] at this; exact this
          rcases hwu₀.symm with rfl
          have hdist_eq : T.dist x₀ x = 1 + T.dist u₀ x := by
            have h1 := T.dist_le rest
            have h2 := dist_triangle hT.connected x₀ u₀ x
            have h3 := dist_eq_one_of_adj hxu₀
            simp only [Walk.length_cons] at hq
            omega
          clear rest hq hxw
          generalize hd : T.dist u₀ x = d
          induction d generalizing x with
          | zero =>
            have hxu : x = u₀ := (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hd).resolve_right
              (not_not.mpr (hT.connected u₀ x)) |>.symm
            subst hxu
            exact Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, harm0⟩
          | succ d ih =>
            have hxu : x ≠ u₀ := fun h => by subst h; simp at hd
            obtain ⟨px, hpx⟩ := before_exists hT hxu
            have hpx_ne : px ≠ x₀ := by
              intro h
              rw [h] at hpx
              have := hpx.2
              rw [dist_eq_one_of_adj hxu₀, SimpleGraph.dist_comm (u := x) (v := u₀)] at this
              have htri := dist_triangle hT.connected x₀ u₀ x
              have := dist_eq_one_of_adj hpx.1
              rw [SimpleGraph.dist_comm (u := x) (v := x₀)] at this
              omega
            have hdpx : T.dist u₀ px = d := by
              have := hpx.2
              rw [SimpleGraph.dist_comm (u := px) (v := u₀), SimpleGraph.dist_comm (u := x) (v := u₀)] at this
              omega
            have hpx_dist : T.dist x₀ px = 1 + T.dist u₀ px := by
              have htri1 := dist_triangle hT.connected x₀ u₀ px
              have htri2 := dist_triangle hT.connected x₀ px x
              have h1 := dist_eq_one_of_adj hxu₀
              have h2 := dist_eq_one_of_adj hpx.1.symm
              omega
            obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (ih px hpx_ne hpx_dist hdpx)
            -- `x` is adjacent to `arm i = px`, so by `harm_adj` either `x = x₀` or `x ∈ image arm`!
            have hadj_i : T.Adj (arm i) x := by rw [hi]; exact hpx.1.symm
            rcases (harm_adj i x).mp hadj_i with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
            · exact (hne rfl).elim
            · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
            · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
      have hx₀_not : x₀ ∉ Finset.univ.image arm := by
        intro h; rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
        have := harm_dep i; rw [hi] at this; simp at this
      have huniv : (Finset.univ : Finset V) = insert x₀ (Finset.univ.image arm) := by
        ext x
        simp only [Finset.mem_univ, Finset.mem_insert, true_iff]
        by_cases hx : x = x₀
        · exact Or.inl hx
        · exact Or.inr (hcover x hx)
      have hn_eq : n = k + 1 := by
        have hcard := congrArg Finset.card huniv
        rw [Finset.card_univ, Finset.card_insert_of_notMem hx₀_not,
          Finset.card_image_of_injective _ arm.injective, Finset.card_univ, Fintype.card_fin] at hcard
        exact hcard
      -- Define bijection `g : Fin n → V` sending `0 ↦ x₀` and `i + 1 ↦ arm i`!
      let g : Fin n → V := fun idx =>
        if h0 : idx.val = 0 then x₀ else arm ⟨idx.val - 1, by omega⟩
      have hg_inj : Function.Injective g := by
        intro i j hij
        dsimp [g] at hij
        split_ifs at hij with hi hj hj
        · exact Fin.ext (by omega)
        · exact (hx₀_not (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hij.symm⟩)).elim
        · exact (hx₀_not (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hij⟩)).elim
        · have heq := congrArg Fin.val (arm.injective hij)
          dsimp only at heq
          exact Fin.ext (by omega)
      have hg_bij : Function.Bijective g :=
        (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_inj, by simp [n]⟩
      let e : Fin n ≃ V := Equiv.ofBijective g hg_bij
      have he_iso : pathGraph n ≃g T := {
        toEquiv := e
        map_rel_iff' := by
          intro i j
          change T.Adj (g i) (g j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)
          dsimp [g]
          split_ifs with hi hj hj
          · simp [SimpleGraph.irrefl]; omega
          · rw [SimpleGraph.adj_comm, harm_adj]
            constructor
            · rintro (⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
              · dsimp only at h1; omega
              · exact (hx₀_not (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h2.symm⟩)).elim
              · exact (hx₀_not (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h2.symm⟩)).elim
            · intro h; left; exact ⟨by dsimp only; omega, rfl⟩
          · rw [harm_adj]
            constructor
            · rintro (⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
              · dsimp only at h1; omega
              · exact (hx₀_not (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h2.symm⟩)).elim
              · exact (hx₀_not (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h2.symm⟩)).elim
            · intro h; left; exact ⟨by dsimp only; omega, rfl⟩
          · rw [harm_adj]
            constructor
            · rintro (⟨_, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
              · exact (hx₀_not (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h2⟩)).elim
              · have := congrArg Fin.val (arm.injective h2); dsimp only at this h1; omega
              · have := congrArg Fin.val (arm.injective h2); dsimp only at this h1; omega
            · rintro (h | h)
              · right; right; exact ⟨by dsimp only; omega, by congr 1; ext; dsimp only; omega⟩
              · right; left; exact ⟨by dsimp only; omega, by congr 1; ext; dsimp only; omega⟩
      }
      exact ⟨he_iso.symm⟩

omit [DecidableEq V] in
/-- Every graph isomorphic to `pathGraph n` has every vertex of degree `≤ 2`. -/
private lemma deg_le_two_of_iso_pathGraph {T : SimpleGraph V} [DecidableRel T.Adj]
    (e : T ≃g pathGraph (Fintype.card V)) (u : V) : T.degree u ≤ 2 := by
  have hdeg : T.degree u = (pathGraph (Fintype.card V)).degree (e u) := (e.degree_eq u).symm
  rw [hdeg, ← SimpleGraph.card_neighborFinset_eq_degree]
  let i := e u
  let S : Finset (Fin (Fintype.card V)) :=
    (Finset.univ.filter (fun j : Fin (Fintype.card V) => i.val + 1 = j.val)) ∪
    (Finset.univ.filter (fun j : Fin (Fintype.card V) => j.val + 1 = i.val))
  have hsub : (pathGraph (Fintype.card V)).neighborFinset i ⊆ S := by
    intro j hj
    rw [SimpleGraph.mem_neighborFinset] at hj
    simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hj
  have h1 : (Finset.univ.filter (fun j : Fin (Fintype.card V) => i.val + 1 = j.val)).card ≤ 1 :=
    Finset.card_le_one.mpr (fun a ha b hb => Fin.ext (by
      have := (Finset.mem_filter.mp ha).2
      have := (Finset.mem_filter.mp hb).2; omega))
  have h2 : (Finset.univ.filter (fun j : Fin (Fintype.card V) => j.val + 1 = i.val)).card ≤ 1 :=
    Finset.card_le_one.mpr (fun a ha b hb => Fin.ext (by
      have := (Finset.mem_filter.mp ha).2
      have := (Finset.mem_filter.mp hb).2; omega))
  have hS : S.card ≤ 2 := le_trans (Finset.card_union_le _ _) (by omega)
  exact le_trans (Finset.card_le_card hsub) hS

end TreeStructure

section MainTheorems

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Strong induction on `leafCount T`: every finite tree `T` satisfies
`htIndex T ≤ htIndex (pathGraph (Fintype.card V))`, with strict inequality whenever
`T` is not isomorphic to `pathGraph (Fintype.card V)`. -/
private theorem palacios_induction :
    ∀ (L : ℕ) (T : SimpleGraph V), T.IsTree → leafCount T = L →
      htIndex T ≤ htIndex (pathGraph (Fintype.card V)) ∧
      (¬ Nonempty (T ≃g pathGraph (Fintype.card V)) →
        htIndex T < htIndex (pathGraph (Fintype.card V))) := by
  intro L
  induction L using Nat.strongRecOn with
  | ind L ih =>
    classical
    intro T hT hL
    by_cases hn2 : Fintype.card V < 2
    · -- `n ≤ 1`: every vertex has degree `0 ≤ 2`, so `T ≃g pathGraph n`
      have hle2 : ∀ u : V, T.degree u ≤ 2 := by
        intro u
        have hlt : T.degree u < Fintype.card V := T.degree_lt_card_verts u
        omega
      obtain ⟨e⟩ := isTree_iso_pathGraph_of_deg_le_two hT hle2
      exact ⟨le_of_eq (htIndex_iso e), fun h => (h ⟨e⟩).elim⟩
    · have hn : 2 ≤ Fintype.card V := by omega
      by_cases hdeg : ∀ u : V, T.degree u ≤ 2
      · obtain ⟨e⟩ := isTree_iso_pathGraph_of_deg_le_two hT hdeg
        exact ⟨le_of_eq (htIndex_iso e), fun h => (h ⟨e⟩).elim⟩
      · push Not at hdeg
        obtain ⟨u, hu⟩ := hdeg
        obtain ⟨cfg⟩ := exists_graftConfig_of_deg_ge_three hT ⟨u, by omega⟩
        have hT' : cfg.graftGraph.IsTree := cfg.graft_isTree hT
        have hL' : leafCount cfg.graftGraph + 1 = L := hL ▸ cfg.graft_leafCount hT
        have hlt_step : htIndex T < htIndex cfg.graftGraph := cfg.graft_htIndex_strict_lt hT
        have hih := (ih (leafCount cfg.graftGraph) (by omega) cfg.graftGraph hT' rfl).1
        exact ⟨le_trans (le_of_lt hlt_step) hih, fun _ => lt_of_lt_of_le hlt_step hih⟩

/-- **Main Theorem (Palacios–Tamura–Wiberg–Petojević Conjecture, arXiv:2611.34295v1, §3):**
For every finite tree `T` on vertex set `V`, the hitting-time index satisfies
`htIndex T ≤ htIndex (pathGraph (Fintype.card V))`. -/
theorem palacios_tree_hitting_time_le {T : SimpleGraph V} (hT : T.IsTree) :
    htIndex T ≤ htIndex (pathGraph (Fintype.card V)) :=
  (palacios_induction (leafCount T) T hT rfl).1

/-- **Strictness:** Every non-path finite tree `T` has strictly smaller hitting-time index
than the path `P_n`. -/
theorem palacios_tree_hitting_time_strict_lt {T : SimpleGraph V} (hT : T.IsTree)
    (hnotpath : ¬ Nonempty (T ≃g pathGraph (Fintype.card V))) :
    htIndex T < htIndex (pathGraph (Fintype.card V)) :=
  (palacios_induction (leafCount T) T hT rfl).2 hnotpath

/-- **Unique Maximality Characterization:** Among all finite trees `T` on `V`,
`htIndex T = htIndex (pathGraph (Fintype.card V))` if and only if `T ≃g pathGraph (Fintype.card V)`. -/
theorem palacios_tree_hitting_time_eq_iff {T : SimpleGraph V} (hT : T.IsTree) :
    htIndex T = htIndex (pathGraph (Fintype.card V)) ↔
      Nonempty (T ≃g pathGraph (Fintype.card V)) := by
  constructor
  · intro heq
    by_contra hnot
    exact ne_of_lt (palacios_tree_hitting_time_strict_lt hT hnot) heq
  · rintro ⟨e⟩
    exact htIndex_iso e

end MainTheorems

end PalaciosHittingTimeTrees
