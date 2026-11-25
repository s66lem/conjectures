import Conjectures.StableKneserK3.HiltonMilner
import Conjectures.StableKneserK3.Counting

namespace StableKneserK3

open Finset

variable {V : Type*} [DecidableEq V]

/-- Sum of the assigned nonnegative integer weights. -/
def weight (w : Finset V → ℕ) (F : Finset (Finset V)) := ∑ t ∈ F, w t

omit [DecidableEq V] in
private theorem weight_mono {w : Finset V → ℕ} {F T : Finset (Finset V)} (h : F ⊆ T) :
    weight w F ≤ weight w T := sum_le_sum_of_subset h

omit [DecidableEq V] in
private theorem weight_bound {F : Finset (Finset V)} {w : Finset V → ℕ} {M : ℕ}
    (h : ∀ t ∈ F, w t ≤ M) : weight w F ≤ F.card*M := by
  simpa [weight] using sum_le_sum h

private theorem with_exceptions {F X E T : Finset (Finset V)} {w : Finset V → ℕ} {M k : ℕ}
    (h : F ⊆ X ∪ E) (hT : F ⊆ T) (hM : ∀ t ∈ T, w t ≤ M) (he : E.card ≤ k) :
    weight w F ≤ weight w X + k*M := by
  have hdiff : F \ X ⊆ E := fun t ht => (mem_union.mp (h (mem_sdiff.mp ht).1)).resolve_left (mem_sdiff.mp ht).2
  have hsplit : weight w F = weight w (F \ X) + weight w (F ∩ X) := by
    simp only [weight, ← sum_union (disjoint_sdiff_inter F X),sdiff_union_inter]
  rw [hsplit]
  have h₁ := weight_bound (F := F \ X) (fun t ht => hM t (hT (mem_sdiff.mp ht).1))
  have h₂ := weight_mono (w := w) (inter_subset_right (s₁ := F) (s₂ := X))
  have h₃ := Nat.mul_le_mul_right M ((card_le_card hdiff).trans he)
  omega

/-- The two links on four points have at most six edges between them, counting overlaps twice. -/
private theorem four_link_count [Fintype V] (hn : 4 ≤ Fintype.card V)
    {A B : Finset (Finset V)} {D : Finset V} (hD : D.card ≤ 4)
    (hA : EdgesOn D A) (hB : EdgesOn D B) (hc : Cross A B) : A.card + B.card ≤ 6 := by
  classical
  obtain ⟨U,hDU,hU⟩ := Finset.exists_superset_card_eq hD hn
  let C := B.image (fun e => U \ e)
  have hdis : Disjoint A C := by
    apply disjoint_left.mpr
    intro e he hc'
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hc'
    exact hc _ he f hf disjoint_sdiff_self_left
  have hcard : C.card = B.card := card_image_of_injOn (fun a ha b hb he =>
    (Finset.sdiff_sdiff_eq_self ((hB a ha).1.trans hDU)).symm.trans
      ((congrArg (fun t => U \ t) he).trans (Finset.sdiff_sdiff_eq_self ((hB b hb).1.trans hDU))))
  have sub : A ∪ C ⊆ U.powersetCard 2 := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact mem_powersetCard.mpr ⟨(hA e he).1.trans hDU, (hA e he).2⟩
    · obtain ⟨b,hb,rfl⟩ := mem_image.mp he
      exact mem_powersetCard.mpr ⟨sdiff_subset,by rw [card_sdiff_of_subset ((hB b hb).1.trans hDU),
        hU,(hB b hb).2]⟩
  have h := card_le_card sub
  rwa [card_union_of_disjoint hdis,hcard,card_powersetCard,hU] at h

/-- Numerical checks on the four transversal templates and the covering-number-three case. -/
structure WeightBounds [Fintype V] (T : Finset (Finset V)) (w : Finset V → ℕ) (M B : ℕ) : Prop where
  member : ∀ t ∈ T, w t ≤ M
  small : 10*M ≤ B
  exceptional : ∀ a ∈ T, ∀ x ∉ a,
    weight w (T.filter (fun s => s = a ∨ x ∈ s ∧ ¬Disjoint s a)) ≤ B
  majority : ∀ x y z : V, x ≠ y → x ≠ z → y ≠ z →
    weight w (T.filter (fun s => x ∈ s ∧ y ∈ s ∨ x ∈ s ∧ z ∈ s ∨ y ∈ s ∧ z ∈ s)) ≤ B
  fork : ∀ x y z : V, x ≠ y → x ≠ z → y ≠ z →
    weight w (T.filter (fun s => y ∈ s ∧ (x ∈ s ∨ z ∈ s))) + 3*M ≤ B
  pair : ∀ x y : V, x ≠ y → weight w (T.filter (fun s => x ∈ s ∧ y ∈ s)) + 6*M ≤ B

private theorem link_mem {F : Finset (Finset V)} {x y : V} {t : Finset V}
    (ht : t ∈ F) (hx : x ∈ t) (hy : y ∉ t) : t.erase x ∈ link F x y :=
  mem_image.mpr ⟨t,mem_filter.mpr ⟨ht,hx,hy⟩,rfl⟩

private theorem of_template [Fintype V] {F T : Finset (Finset V)} {w : Finset V → ℕ} {M B : ℕ}
    (hn : 4 ≤ Fintype.card V) (hT : F ⊆ T) (bounds : WeightBounds T w M B)
    (hu : ∀ t ∈ F, t.card = 3) (hi : (F : Set (Finset V)).Intersecting) (hns : ∀ z, ∃ t ∈ F, z ∉ t)
    {x y : V} (hxy : x ≠ y) (hcov : ∀ t ∈ F, x ∈ t ∨ y ∈ t)
    (h : LinkTemplate (link F x y) (link F y x)) : weight w F ≤ B := by
  classical
  rcases h with sing | ⟨z,hA,hB⟩ | ⟨z,u,v,_,_,_,hA,hB⟩ | ⟨D,hD,hA,hB⟩
  · obtain ⟨a,ha,hya⟩ := hns y
    have hxa := (hcov a ha).resolve_right hya
    apply (weight_mono (T := T.filter _) ?_).trans (bounds.exceptional a (hT ha) y hya)
    intro s hs
    apply mem_filter.mpr ⟨hT hs,?_⟩
    by_cases hy : y ∈ s
    · exact Or.inr ⟨hy,hi hs ha⟩
    · have hx := (hcov s hs).resolve_right hy
      have eq := card_le_one.mp sing.le _ (link_mem hs hx hy) _ (link_mem ha hxa hya)
      exact Or.inl ((insert_erase hx).symm.trans ((congrArg (insert x) eq).trans (insert_erase hxa)))
  · obtain ⟨e,he⟩ := link_nonempty hcov hns
    have hz := (link_edges hu x y e he).1 (hA e he)
    have hz' : z ≠ x ∧ z ≠ y := by simpa using hz
    apply (weight_mono (T := T.filter _) ?_).trans (bounds.majority x y z hxy hz'.1.symm hz'.2.symm)
    intro t ht
    apply mem_filter.mpr ⟨hT ht,?_⟩
    rcases hcov t ht with hx | hy
    · by_cases hy : y ∈ t
      · exact Or.inl ⟨hx,hy⟩
      · exact Or.inr (Or.inl ⟨hx,mem_of_mem_erase (hA _ (link_mem ht hx hy))⟩)
    · by_cases hx : x ∈ t
      · exact Or.inl ⟨hx,hy⟩
      · exact Or.inr (Or.inr ⟨hy,mem_of_mem_erase (hB _ (link_mem ht hy hx))⟩)
  · let E : Finset (Finset V) := {insert x {z,u},insert x {z,v},insert y {u,v}}
    have hzu : {z,u} ∈ link F x y := by rw [hA]; simp
    have hz := (link_edges hu x y _ hzu).1 (by simp : z ∈ ({z,u} : Finset V))
    have hz' : z ≠ x ∧ z ≠ y := by simpa using hz
    apply (with_exceptions (F := F) (E := E) ?_ hT bounds.member ?_).trans
      (bounds.fork x y z hxy hz'.1.symm hz'.2.symm)
    · intro t ht
      by_cases hy : y ∈ t
      · by_cases hx : x ∈ t
        · exact mem_union_left _ (mem_filter.mpr ⟨hT ht,hy,Or.inl hx⟩)
        · rcases hB _ (link_mem ht hy hx) with hz | he
          · exact mem_union_left _ (mem_filter.mpr ⟨hT ht,hy,Or.inr (mem_of_mem_erase hz)⟩)
          · exact mem_union_right _ (by have h := congrArg (insert y) he; rw [insert_erase hy] at h; simp [E,h])
      · have hx := (hcov t ht).resolve_right hy
        have he := link_mem ht hx hy
        rw [hA] at he
        simp only [mem_insert,mem_singleton] at he
        rcases he with he | he <;> have h := congrArg (insert x) he <;> rw [insert_erase hx] at h <;>
          exact mem_union_right _ (by simp [E,h])
    · exact (card_insert_le ..).trans (by
        have := card_insert_le (insert x {z,v} : Finset V) {insert y {u,v}}
        simp at this
        omega)
  · let A := link F x y
    let C := link F y x
    let E := A.image (insert x) ∪ C.image (insert y)
    have hnum := four_link_count hn hD (fun e he => ⟨hA e he,(link_edges hu x y e he).2⟩)
      (fun e he => ⟨hB e he,(link_edges hu y x e he).2⟩) (link_cross hi x y)
    apply (with_exceptions (F := F) (E := E) ?_ hT bounds.member ?_).trans (bounds.pair x y hxy)
    · intro t ht
      rcases hcov t ht with hx | hy
      · by_cases hy : y ∈ t
        · exact mem_union_left _ (mem_filter.mpr ⟨hT ht,hx,hy⟩)
        · exact mem_union_right _ (mem_union_left _ (mem_image.mpr ⟨_,link_mem ht hx hy,insert_erase hx⟩))
      · by_cases hx : x ∈ t
        · exact mem_union_left _ (mem_filter.mpr ⟨hT ht,hx,hy⟩)
        · exact mem_union_right _ (mem_union_right _ (mem_image.mpr ⟨_,link_mem ht hy hx,insert_erase hy⟩))
    · exact (card_union_le ..).trans ((Nat.add_le_add card_image_le card_image_le).trans hnum)

/-- A weight certificate bounds every nonstar color class, including nonmaximal classes. -/
theorem WeightBounds.sound [Fintype V] {T F : Finset (Finset V)} {w : Finset V → ℕ} {M B : ℕ}
    (bounds : WeightBounds T w M B) (hn : 4 ≤ Fintype.card V) (hT : F ⊆ T)
    (hu : ∀ t ∈ F, t.card = 3) (hi : (F : Set (Finset V)).Intersecting) (hns : ∀ x, ∃ t ∈ F, x ∉ t) :
    weight w F ≤ B := by
  by_cases h : PairTransversal F
  · obtain ⟨x,y,hxy,hcov⟩ := h
    rcases link_classification hu hi hns hcov with h | h
    · exact of_template hn hT bounds hu hi hns hxy hcov h
    · exact of_template hn hT bounds hu hi hns hxy.symm (fun t ht => (hcov t ht).symm) h
  · have hs := no_pair_bound_ten hu hi h
    exact (weight_bound (fun t ht => bounds.member t (hT ht))).trans ((Nat.mul_le_mul_right M hs).trans bounds.small)

/-- If the total weight exceeds the combined capacity of the nonstar families,
some entire color class has a common ground vertex. -/
theorem weighted_coloring_has_star [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {w : Finset V → ℕ} {M B q : ℕ} (hn : 4 ≤ Fintype.card V)
    (bounds : WeightBounds (stableTriples G) w M B) (htotal : q * B < weight w (stableTriples G))
    (c : Triple G → Fin q) (hc : IsProperColoring G q c) :
    ∃ i x, ∀ s, c s = i → x ∈ s.val := by
  classical
  by_contra! h
  have hp : (stableTriples G).Nonempty := by
    by_contra! he
    simp [he, weight] at htotal
  obtain ⟨a, ha⟩ := hp
  let col (s : Finset V) := if hs : StableTriple G s then c ⟨s, hs⟩
    else c ⟨a, (mem_stableTriples G).mp ha⟩
  have he (s : Triple G) : col s.val = c s := by simp [col, s.property]
  let family (i : Fin q) := (stableTriples G).filter (fun s => col s = i)
  have hf (i : Fin q) : weight w (family i) ≤ B := by
    have mem {s} (hs : s ∈ family i) := (mem_stableTriples G).mp (mem_filter.mp hs).1
    apply bounds.sound hn (filter_subset ..) (fun s hs => (mem hs).1)
    · intro s hs t ht hd
      let u : Triple G := ⟨s, mem hs⟩
      let v : Triple G := ⟨t, mem ht⟩
      exact hc u v hd ((he u).symm.trans (((mem_filter.mp hs).2.trans (mem_filter.mp ht).2.symm).trans (he v)))
    · intro x
      obtain ⟨s, hs, hx⟩ := h i x
      exact ⟨s.val, mem_filter.mpr ⟨(mem_stableTriples G).mpr s.property, (he s).trans hs⟩, hx⟩
  have cap : (∑ i, weight w (family i)) ≤ ∑ _i : Fin q, B := sum_le_sum (fun i _ => hf i)
  simp only [weight, family, sum_fiberwise_of_maps_to (fun _ _ => mem_univ _), sum_const,
    card_univ, Fintype.card_fin, smul_eq_mul] at cap
  exact htotal.not_ge cap

end StableKneserK3

