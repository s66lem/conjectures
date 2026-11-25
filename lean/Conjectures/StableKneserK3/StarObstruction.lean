import Conjectures.StableKneserK3.Anchors
import Conjectures.StableKneserK3.Cycles

namespace StableKneserK3

open Finset SimpleGraph

/-- Independent ground sets of the prescribed size. -/
abbrev StableSet {V : Type*} (G : SimpleGraph V) (k : ℕ) :=
  {s : Finset V // s.card = k ∧ ∀ x ∈ s, ∀ y ∈ s, ¬G.Adj x y}

def Proper {V : Type*} {G : SimpleGraph V} {k q : ℕ} (c : StableSet G k → Fin q) : Prop :=
  ∀ s t, Disjoint s.val t.val → c s ≠ c t

private def pushSet {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ}
    (f : V ↪ W) (hf : ∀ ⦃x y⦄, H.Adj (f x) (f y) → G.Adj x y) (s : StableSet G k) :
    StableSet H k := by
  refine ⟨s.val.map f, by simpa using s.property.1, ?_⟩
  intro a ha b hb h
  obtain ⟨x,hx,rfl⟩ := mem_map.mp ha
  obtain ⟨y,hy,rfl⟩ := mem_map.mp hb
  exact s.property.2 x hx y hy (hf h)

def baseSet {V : Type*} {G : SimpleGraph V} {k : ℕ} (s : StableSet G k) :
    StableSet (withIsolate G) k := pushSet Function.Embedding.inl (fun _ _ h => h) s

private theorem omit_color {V : Type*} {G : SimpleGraph V} {k q : ℕ} (c : StableSet G k → Fin q)
    (hc : Proper c) (i : Fin q) (hi : ∀ s, c s ≠ i) : ∃ d : StableSet G k → Fin (q-1), Proper d := by
  classical
  let e := Fintype.equivFinOfCardEq (α := {j : Fin q // j ≠ i}) (n := q-1) (by simp)
  exact ⟨fun s => e ⟨c s,hi s⟩, fun s t hd h => hc s t hd (congrArg Subtype.val (e.injective h))⟩

private theorem center_set {m k q : ℕ} (hm : 2 ≤ m) (hq : q < m) (hk : 2*k-1 ≤ q)
    (cent : Fin q ↪ Fin m) : ∃ s : StableSet (cycleGraph m) k, ∀ x ∈ s.val, x ∈ Set.range cent := by
  classical
  let _ : NeZero m := ⟨by omega⟩
  let C := univ.map cent
  have hC : C.card = q := by simp [C]
  have hproper : C ≠ univ := by intro h; rw [h,card_univ,Fintype.card_fin] at hC; omega
  obtain ⟨z,hz⟩ : ∃ z, z ∉ C := by
    by_contra! h
    exact hproper (eq_univ_of_forall h)
  let D := C.filter (fun x => (x-z).val % 2 = 0)
  let O := C.filter (fun x => ¬ (x-z).val % 2 = 0)
  have hc : D.card + O.card = q := (card_filter_add_card_filter_not _).trans hC
  have hrot (a b : Fin m) (h : (cycleGraph m).Adj a b) :
      (cycleGraph m).Adj (a-z) (b-z) := by
    rw [cycleGraph_adj']
    simpa only [sub_sub_sub_cancel_right] using cycleGraph_adj'.mp h
  have independent {a b : Fin m} (ha : a ∈ C) (hb : b ∈ C) (he : (a-z).val % 2 = (b-z).val % 2) :
      ¬(cycleGraph m).Adj a b := by
    intro h
    have h₁ : (a-z).val ≠ 0 := fun hh => hz (sub_eq_zero.mp (show a-z=0 from Fin.ext hh) ▸ ha)
    have h₂ : (b-z).val ≠ 0 := fun hh => hz (sub_eq_zero.mp (show b-z=0 from Fin.ext hh) ▸ hb)
    have := (cycle_adj_values hm).mp (hrot a b h)
    omega
  have pick (S : Finset (Fin m)) (hs : k ≤ S.card) (hsub : S ⊆ C)
      (hpar : ∀ x ∈ S, ∀ y ∈ S, (x-z).val % 2 = (y-z).val % 2) :
      ∃ s : StableSet (cycleGraph m) k, ∀ x ∈ s.val, x ∈ Set.range cent := by
    obtain ⟨T,hT,hkT⟩ := exists_subset_card_eq hs
    refine ⟨⟨T,hkT,fun x hx y hy => independent (hsub (hT hx)) (hsub (hT hy))
      (hpar _ (hT hx) _ (hT hy))⟩,?_⟩
    intro x hx
    obtain ⟨i,_,he⟩ := mem_map.mp (hsub (hT hx))
    exact ⟨i,he⟩
  by_cases hd : k ≤ D.card
  · exact pick D hd (filter_subset ..) (fun _ hx _ hy => (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
  · apply pick O (by omega) (filter_subset ..)
    intro x hx y hy
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    change (x-z).val % 2 ≠ 0 at hx'
    change (y-z).val % 2 ≠ 0 at hy'
    omega

private def substitute {V : Type*} [DecidableEq V] (a : V) : V ↪ V ⊕ Unit where
  toFun x := if x = a then .inr () else .inl x
  inj' := by
    intro x y h
    dsimp only at h
    split at h <;> split at h <;> simp_all

private def movedSet {V : Type*} [DecidableEq V] {G : SimpleGraph V} {k : ℕ} (x : V)
    (s : StableSet G k) : StableSet (withIsolate G) k :=
  pushSet (substitute x) (by
    intro a b h
    change (withIsolate G).Adj (if a = x then .inr () else .inl a) (if b = x then .inr () else .inl b) at h
    split at h <;> split at h <;> first | exact h | cases h) s

private theorem unchanged {V : Type*} [DecidableEq V] {G : SimpleGraph V} {k : ℕ} {x : V}
    {s : StableSet G k} (hx : x ∉ s.val) : movedSet x s = baseSet s := by
  apply Subtype.ext
  change s.val.map (substitute x) = s.val.map Function.Embedding.inl
  simp only [map_eq_image]
  apply image_congr
  intro a ha
  have h : a ≠ x := fun e => hx (e ▸ ha)
  change (if a = x then Sum.inr () else Sum.inl a) = _
  rw [if_neg h]
  rfl

/-- The Section 2 star coloring cannot extend beyond its length threshold. -/
theorem section_two_obstruction {m k : ℕ} (hk : 2 ≤ k) (hm : 4*k-3 ≤ m)
    (hSchrijver : ¬ ∃ d : StableSet (cycleGraph m) k → Fin (m-2*k+1), Proper d)
    (c : StableSet (withIsolate (cycleGraph m)) k → Fin (m-2*k+2)) (hc : Proper c) :
    ¬ ∃ center : Fin (m-2*k+2) → Fin m, ∀ s : StableSet (cycleGraph m) k, center (c (baseSet s)) ∈ s.val := by
  classical
  rintro ⟨center,hcenter⟩
  let q := m-2*k+2
  have hmin : ¬ ∃ d : StableSet (cycleGraph m) k → Fin (q-1), Proper d := by
    rwa [show q-1=m-2*k+1 by rfl]
  let d (s : StableSet (cycleGraph m) k) := c (baseSet s)
  have hd : Proper d := fun _ _ h => hc _ _ ((disjoint_map _).mpr h)
  have hcen (s) : center (d s) ∈ s.val := hcenter s
  have cinj : Function.Injective center := by
    intro i j hij
    by_contra hne
    let d' (t : StableSet (cycleGraph m) k) := if d t = i then j else d t
    have hd' : Proper d' := by
      intro s t hst h
      have hs := hcen s
      have ht := hcen t
      dsimp only [d'] at h
      split at h <;> split at h
      · rename_i h₁ h₂; exact hd _ _ hst (h₁.trans h₂.symm)
      · rename_i h₁ _; rw [h₁,hij,h] at hs; exact disjoint_left.mp hst hs ht
      · rename_i _ h₂; rw [h₂,hij,← h] at ht; exact disjoint_left.mp hst hs ht
      · exact hd _ _ hst h
    exact hmin (omit_color d' hd' i (fun s => by simp only [d']; split <;> first | assumption | exact Ne.symm hne))
  obtain ⟨T,hT⟩ := center_set (m := m) (k := k) (q := q) (by omega) (by dsimp [q]; omega)
    (by dsimp [q]; omega) ⟨center,cinj⟩
  let i := d T
  let x := center i
  let p (s : StableSet (cycleGraph m) k) := c (movedSet x s)
  have hp : Proper p := fun _ _ h => hc _ _ ((disjoint_map _).mpr h)
  have forced (s) (hs : p s = i) : x ∈ s.val := by
    by_contra ha
    have he : p s = d s := congrArg c (unchanged ha)
    apply ha
    change center i ∈ _
    rw [← he.symm.trans hs]
    exact hcen s
  have alt (s) (hs : p s = i) : ∃ j : Fin q, j ≠ i ∧ center j ∈ s.val := by
    have hmeet : ¬ Disjoint (movedSet x s).val (baseSet T).val := fun h => hc _ _ h hs
    obtain ⟨a,h₁,h₂⟩ := not_disjoint_iff.mp hmeet
    obtain ⟨u,hu,rfl⟩ := mem_map.mp h₁
    obtain ⟨v,hv,he⟩ := mem_map.mp h₂
    change Sum.inl v = (if u = x then Sum.inr () else Sum.inl u) at he
    split at he
    · cases he
    · rename_i hux
      obtain rfl := Sum.inl.inj he
      obtain ⟨j,hj⟩ := hT _ hv
      change center j = v at hj
      exact ⟨j,fun h => hux ((h ▸ hj).symm),hj.symm ▸ hu⟩
  let c' (s : StableSet (cycleGraph m) k) := if h : p s = i then (alt s h).choose else p s
  have avoids (s) : c' s ≠ i := by
    dsimp only [c']
    split
    · exact (alt s ‹p s = i›).choose_spec.1
    · assumption
  have unchanged_center (s) (hx : x ∉ s.val) : center (c' s) ∈ s.val := by
    have h := congrArg c (unchanged (G := cycleGraph m) hx)
    change p s = d s at h
    simpa only [c', dif_neg (fun he => hx (forced s he)), h] using hcen s
  have mixed (s t) (hs : p s = i) (hst : Disjoint s.val t.val) (he : c' s = c' t) : False := by
    have hxs := forced s hs
    have hxt : x ∉ t.val := disjoint_left.mp hst hxs
    have hcs : center (c' s) ∈ s.val := by simpa [c',hs] using (alt s hs).choose_spec.2
    rw [he] at hcs
    exact disjoint_left.mp hst hcs (unchanged_center t hxt)
  apply hmin (omit_color c' ?_ i avoids)
  intro s t hst he
  by_cases hs : p s = i
  · exact mixed s t hs hst he
  by_cases ht : p t = i
  · exact mixed t s ht hst.symm he.symm
  exact hp _ _ hst (by simpa only [c',dif_neg hs,dif_neg ht] using he)

end StableKneserK3

