import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card

namespace StableKneserK3

open Finset

variable {V : Type*} [DecidableEq V]

/-- A pair of ground points meeting every triple. -/
def PairTransversal (F : Finset (Finset V)) : Prop :=
  ∃ x y : V, x ≠ y ∧ ∀ t ∈ F, x ∈ t ∨ y ∈ t

private theorem cover_bound {α β : Type*} [DecidableEq α] {S : Finset α} {T : Finset β}
    {B : β → Finset α} (h : ∀ s ∈ S, ∃ t ∈ T, s ∈ B t) {k : ℕ}
    (hk : ∀ t ∈ T, (B t).card ≤ k) : S.card ≤ T.card * k := by
  calc
    S.card ≤ (T.biUnion B).card := card_le_card (fun s hs => mem_biUnion.mpr (h s hs))
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _ ∈ T, k := sum_le_sum hk
    _ = _ := by simp

/-- If a pair is contained in a triple, the other point determines that triple. -/
private theorem triple_from_points {s : Finset V} (hs : s.card = 3) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    s = {a,b,c} := by
  symm
  apply eq_of_subset_of_card_le (by simp [insert_subset_iff, ha, hb, hc])
  simp [hs, hab, hac, hbc]

/-- The elementary branching bound for intersecting triples of covering number three. -/
theorem no_pair_bound_twenty_seven {F : Finset (Finset V)}
    (hu : ∀ t ∈ F, t.card = 3) (hi : (F : Set (Finset V)).Intersecting)
    (hpair : ¬ PairTransversal F) : F.card ≤ 27 := by
  classical
  obtain hF | hF := F.eq_empty_or_nonempty
  · simp [hF]
  obtain ⟨A, hA⟩ := hF
  let through (x : V) := F.filter (fun t => x ∈ t)
  have degree (x : V) (hx : x ∈ A) : (through x).card ≤ 9 := by
    have hother : ∃ y ∈ A, x ≠ y := by
      by_contra! hn
      have sub : A ⊆ {x} := fun z hz => mem_singleton.mpr (hn z hz).symm
      have hle := card_le_card sub
      simp [hu A hA] at hle
    obtain ⟨y, _, hxy⟩ := hother
    have miss (a b : V) (hab : a ≠ b) : ∃ t ∈ F, a ∉ t ∧ b ∉ t := by
      by_contra! h
      exact hpair ⟨a,b,hab,fun t ht => or_iff_not_imp_left.mpr (h t ht)⟩
    obtain ⟨B, hB, hxB, _⟩ := miss x y hxy
    let both (b : V) := (through x).filter (fun t => b ∈ t)
    have cover (s) (hs : s ∈ through x) : ∃ b ∈ B, s ∈ both b := by
      obtain ⟨b, hb, hb'⟩ := not_disjoint_iff.mp (hi hB (mem_filter.mp hs).1)
      exact ⟨b,hb,mem_filter.mpr ⟨hs,hb'⟩⟩
    have lim (b : V) (hb : b ∈ B) : (both b).card ≤ 3 := by
      have hxb : x ≠ b := fun e => hxB (e ▸ hb)
      obtain ⟨C, hC, hxC, hbC⟩ := miss x b hxb
      have sub : both b ⊆ C.image (fun c => {x,b,c}) := by
        intro s hs
        obtain ⟨hsx, hbs⟩ := mem_filter.mp hs
        obtain ⟨hsF, hxs⟩ := mem_filter.mp hsx
        obtain ⟨c, hc, hcs⟩ := not_disjoint_iff.mp (hi hC hsF)
        exact mem_image.mpr ⟨c, hc, (triple_from_points (hu s hsF) hxb
          (fun e => hxC (e ▸ hc)) (fun e => hbC (e ▸ hc)) hxs hbs hcs).symm⟩
      exact (card_le_card sub).trans (card_image_le.trans (hu C hC).le)
    simpa [hu B hB] using cover_bound cover lim
  have cover (s) (hs : s ∈ F) : ∃ a ∈ A, s ∈ through a := by
    obtain ⟨a, ha, has⟩ := not_disjoint_iff.mp (hi hA hs)
    exact ⟨a,ha,mem_filter.mpr ⟨hs,has⟩⟩
  simpa [hu A hA] using cover_bound cover degree

def EdgesOn (U : Finset V) (L : Finset (Finset V)) : Prop :=
  ∀ e ∈ L, e ⊆ U ∧ e.card = 2

def Cross (A B : Finset (Finset V)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ¬Disjoint a b

omit [DecidableEq V] in
private theorem cross_symm {A B : Finset (Finset V)} (h : Cross A B) : Cross B A :=
  fun b hb a ha hd => h a ha b hb hd.symm

private theorem edge_eq {e : Finset V} (hc : e.card = 2) {a b : V}
    (ha : a ∈ e) (hb : b ∈ e) (hne : a ≠ b) : e = {a,b} := by
  symm
  apply eq_of_subset_of_card_le (by simp [insert_subset_iff, ha, hb])
  simp [hc, hne]

private theorem other_end {e : Finset V} (hc : e.card = 2) {x : V} (hx : x ∈ e) :
    ∃ y ∈ e, y ≠ x ∧ e = {x,y} := by
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
  rcases mem_insert.mp hx with rfl | hx
  · exact ⟨b, by simp, hab.symm, rfl⟩
  obtain rfl := mem_singleton.mp hx
  exact ⟨a, by simp, hab, pair_comm ..⟩

private theorem adjacent_edges {e f : Finset V} (he : e.card = 2) (hf : f.card = 2)
    (hne : e ≠ f) (hi : ¬Disjoint e f) :
    ∃ a b c, b ≠ a ∧ c ≠ a ∧ b ≠ c ∧ e = {a,b} ∧ f = {a,c} := by
  obtain ⟨a, ha, ha'⟩ := not_disjoint_iff.mp hi
  obtain ⟨b, _, hb, h1⟩ := other_end he ha
  obtain ⟨c, _, hc, h2⟩ := other_end hf ha'
  exact ⟨a,b,c,hb,hc,by rintro rfl; exact hne (h1.trans h2.symm),h1,h2⟩

private def pairStar (U : Finset V) (a : V) : Finset (Finset V) :=
  (U.erase a).image (fun b => {a,b})

private theorem in_pairStar {e U : Finset V} (he : e.card = 2) (hU : e ⊆ U)
    {a : V} (ha : a ∈ e) : e ∈ pairStar U a := by
  obtain ⟨b, hb, hba, heq⟩ := other_end he ha
  exact mem_image.mpr ⟨b,mem_erase.mpr ⟨hba,hU hb⟩,heq.symm⟩

private theorem pairStar_bound {U : Finset V} {a : V} (ha : a ∈ U) :
    (pairStar U a).card ≤ U.card - 1 :=
  card_image_le.trans (card_erase_of_mem ha).le

private theorem meets_pair {e : Finset V} {a b : V} (h : ¬Disjoint {a,b} e) :
    a ∈ e ∨ b ∈ e := by
  obtain ⟨x,hx,he⟩ := not_disjoint_iff.mp h
  simpa using (show ∃ x ∈ ({a,b} : Finset V), x ∈ e from ⟨x,hx,he⟩)

private theorem single_edge_bound {U : Finset V} {L : Finset (Finset V)}
    (hL : EdgesOn U L) {a b : V} (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b)
    (hits : ∀ e ∈ L, ¬Disjoint {a,b} e) : L.card ≤ (U.card-1) + (U.card-2) := by
  have hsub : L ⊆ pairStar U a ∪ pairStar (U.erase a) b := by
    intro e he
    by_cases h : a ∈ e
    · exact mem_union_left _ (in_pairStar (hL e he).2 (hL e he).1 h)
    · exact mem_union_right _ (in_pairStar (hL e he).2
        (show e ⊆ U.erase a from fun x hx => mem_erase.mpr ⟨fun hxa => h (hxa ▸ hx), (hL e he).1 hx⟩)
        ((meets_pair (hits e he)).resolve_left h))
  have hb' := pairStar_bound (mem_erase.mpr ⟨hab.symm,hb⟩)
  rw [card_erase_of_mem ha] at hb'
  have h := (card_le_card hsub).trans (card_union_le _ _)
  have := pairStar_bound ha
  omega

private theorem four_bound {U : Finset V} {L : Finset (Finset V)} (hL : EdgesOn U L)
    {e f : Finset V} (he : e.card = 2) (hf : f.card = 2) (hd : Disjoint e f)
    (hits : ∀ t ∈ L, ¬Disjoint e t ∧ ¬Disjoint f t) : L.card ≤ 4 := by
  have sub : L ⊆ (e ×ˢ f).image (fun p : V × V => {p.1,p.2}) := by
    intro t ht
    obtain ⟨x,hx,hxt⟩ := not_disjoint_iff.mp (hits t ht).1
    obtain ⟨y,hy,hyt⟩ := not_disjoint_iff.mp (hits t ht).2
    have hxy : x ≠ y := fun h => disjoint_left.mp hd hx (h ▸ hy)
    exact mem_image.mpr ⟨(x,y),mem_product.mpr ⟨hx,hy⟩,(edge_eq (hL t ht).2 hxt hyt hxy).symm⟩
  have h := (card_le_card sub).trans card_image_le
  simpa [he,hf] using h

private theorem adjacent_cover {U : Finset V} {L : Finset (Finset V)} (hL : EdgesOn U L)
    {a b c : V} (hbc : b ≠ c) (hits : ∀ t ∈ L, ¬Disjoint {a,b} t ∧ ¬Disjoint {a,c} t) :
    L ⊆ insert {b,c} (pairStar U a) := by
  intro t ht
  by_cases ha : a ∈ t
  · exact mem_insert_of_mem (in_pairStar (hL t ht).2 (hL t ht).1 ha)
  · exact mem_insert.mpr (Or.inl (edge_eq (hL t ht).2
      ((meets_pair (hits t ht).1).resolve_left ha) ((meets_pair (hits t ht).2).resolve_left ha) hbc))

private theorem intersecting_edges_bound {U : Finset V} {L : Finset (Finset V)}
    (hn : 4 ≤ U.card) (hL : EdgesOn U L) (hi : Cross L L) : L.card ≤ U.card-1 := by
  by_cases hsmall : L.card ≤ 1
  · omega
  obtain ⟨e,he,f,hf,hef⟩ := one_lt_card.mp (by omega : 1 < L.card)
  obtain ⟨a,b,c,hba,hca,hbc,rfl,rfl⟩ := adjacent_edges (hL e he).2 (hL f hf).2 hef (hi e he f hf)
  have ha : a ∈ U := (hL _ he).1 (by simp)
  by_cases hstar : ∀ t ∈ L, a ∈ t
  · exact (card_le_card (fun t ht => in_pairStar (hL t ht).2 (hL t ht).1 (hstar t ht))).trans
      (pairStar_bound ha)
  push Not at hstar
  obtain ⟨t,ht,hat⟩ := hstar
  obtain rfl : t = {b,c} := edge_eq (hL t ht).2 ((meets_pair (hi _ he t ht)).resolve_left hat)
    ((meets_pair (hi _ hf t ht)).resolve_left hat) hbc
  have sub : L ⊆ {{a,b},{a,c},{b,c}} := by
    intro s hs
    have hcard := (hL s hs).2
    have h1 := meets_pair (hi _ he s hs)
    have h2 := meets_pair (hi _ hf s hs)
    have h3 := meets_pair (hi _ ht s hs)
    simp only [mem_insert, mem_singleton]
    by_cases ha : a ∈ s
    · rcases h3 with hb | hc
      · exact Or.inl (edge_eq hcard ha hb hba.symm)
      · exact Or.inr (Or.inl (edge_eq hcard ha hc hca.symm))
    · exact Or.inr (Or.inr (edge_eq hcard (h1.resolve_left ha) (h2.resolve_left ha) hbc))
  have h := card_le_card sub
  have h3 : ({{a,b},{a,c},{b,c}} : Finset (Finset V)).card ≤ 3 :=
    (card_insert_le ..).trans (by have := card_insert_le ({a,c} : Finset V) {{b,c}}; simp at *; omega)
  omega

private theorem two_edges_bound {U : Finset V} {A B : Finset (Finset V)} (hU : 4 ≤ U.card)
    (hA : EdgesOn U A) (hB : EdgesOn U B) (hcross : Cross B A) (hb : 1 < B.card) :
    A.card ≤ U.card := by
  obtain ⟨e,he,f,hf,hef⟩ := one_lt_card.mp hb
  have hits := fun t (ht : t ∈ A) => And.intro (hcross e he t ht) (hcross f hf t ht)
  by_cases hd : Disjoint e f
  · exact (four_bound hA (hB e he).2 (hB f hf).2 hd hits).trans hU
  obtain ⟨a,b,c,_,_,hbc,rfl,rfl⟩ := adjacent_edges (hB e he).2 (hB f hf).2 hef hd
  have h := (card_le_card (adjacent_cover hA hbc hits)).trans (card_insert_le ..)
  have ha := pairStar_bound ((hB _ he).1 (by simp : a ∈ ({a,b} : Finset V)))
  omega

private theorem cross_edges_bound {U : Finset V} {A B : Finset (Finset V)} (hU : 5 ≤ U.card)
    (hA : EdgesOn U A) (hB : EdgesOn U B) (ha : A.Nonempty) (hb : B.Nonempty)
    (hc : Cross A B) : A.card + B.card ≤ 2*U.card-2 := by
  have singleton_bound {X Y : Finset (Finset V)} (hX : EdgesOn U X) (hY : EdgesOn U Y)
      (hxy : Cross X Y) (hne : X.Nonempty) (hsmall : X.card ≤ 1) :
      X.card + Y.card ≤ 2*U.card-2 := by
    obtain ⟨e,he⟩ := hne
    obtain ⟨x,y,hne,rfl⟩ := card_eq_two.mp (hX e he).2
    have h := single_edge_bound hY ((hX _ he).1 (by simp : x ∈ ({x,y} : Finset V)))
      ((hX _ he).1 (by simp)) hne (hxy _ he)
    omega
  by_cases h1 : A.card ≤ 1
  · exact singleton_bound hA hB hc ha h1
  by_cases h2 : B.card ≤ 1
  · have := singleton_bound hB hA (cross_symm hc) hb h2; omega
  have noninter {X Y : Finset (Finset V)} (hX : EdgesOn U X) (hY : EdgesOn U Y)
      (hxy : Cross X Y) (hm : 1 < Y.card) (hi : ¬Cross X X) :
      X.card + Y.card ≤ 2*U.card-2 := by
    simp only [Cross, not_forall, not_not] at hi
    obtain ⟨a,ha,b,hb,hd⟩ := hi
    have hu := two_edges_bound (by omega) hX hY (cross_symm hxy) hm
    have hv := four_bound hY (hX _ ha).2 (hX _ hb).2 hd
      (fun t ht => ⟨hxy _ ha t ht, hxy _ hb t ht⟩)
    by_cases disY : Cross Y Y
    · have hv' : Y.card ≤ 3 := by
        by_contra! hbig
        have sub : Y ⊆ (a ×ˢ b).image (fun p : V × V => {p.1,p.2}) := by
          intro t ht
          obtain ⟨x,hx,hxt⟩ := not_disjoint_iff.mp (hxy _ ha t ht)
          obtain ⟨y,hy,hyt⟩ := not_disjoint_iff.mp (hxy _ hb t ht)
          exact mem_image.mpr ⟨(x,y),mem_product.mpr ⟨hx,hy⟩,
            (edge_eq (hY t ht).2 hxt hyt (fun h => disjoint_left.mp hd hx (h ▸ hy))).symm⟩
        have eq := eq_of_subset_of_card_le sub (card_image_le.trans (by
          simpa [(hX _ ha).2,(hX _ hb).2] using (show 4 ≤ Y.card by omega)))
        obtain ⟨a₁,a₂,ha₁₂,aeq⟩ := card_eq_two.mp (hX _ ha).2
        obtain ⟨b₁,b₂,hb₁₂,beq⟩ := card_eq_two.mp (hX _ hb).2
        have mem (x) (hx : x ∈ a) (y) (hy : y ∈ b) : {x,y} ∈ Y := by
          rw [eq]; exact mem_image.mpr ⟨(x,y),mem_product.mpr ⟨hx,hy⟩, rfl⟩
        have ha₁ : a₁ ∈ a := by simp [aeq]
        have ha₂ : a₂ ∈ a := by simp [aeq]
        have hb₁ : b₁ ∈ b := by simp [beq]
        have hb₂ : b₂ ∈ b := by simp [beq]
        apply disY _ (mem _ ha₁ _ hb₁) _ (mem _ ha₂ _ hb₂)
        have h₁ : a₁ ≠ b₂ := fun h => disjoint_left.mp hd ha₁ (h ▸ hb₂)
        have h₂ : b₁ ≠ a₂ := fun h => disjoint_left.mp hd (h ▸ ha₂) hb₁
        simp [ha₁₂.symm,hb₁₂.symm,h₁.symm,h₂.symm]
      omega
    · simp only [Cross, not_forall, not_not] at disY
      obtain ⟨c,hc,d,hd',hcd⟩ := disY
      have := four_bound hX (hY _ hc).2 (hY _ hd').2 hcd
        (fun t ht => ⟨(cross_symm hxy) _ hc t ht, (cross_symm hxy) _ hd' t ht⟩)
      omega
  by_cases iA : Cross A A
  · by_cases iB : Cross B B
    · have := intersecting_edges_bound (by omega) hA iA
      have := intersecting_edges_bound (by omega) hB iB
      omega
    · have := noninter hB hA (cross_symm hc) (by omega) iB; omega
  · exact noninter hA hB hc (by omega) iA

/-- Delete the first center from members containing it and avoiding the other center. -/
def link (F : Finset (Finset V)) (x y : V) :=
  (F.filter (fun t => x ∈ t ∧ y ∉ t)).image (fun t => t.erase x)

theorem link_edges [Fintype V] {F : Finset (Finset V)} (hu : ∀ t ∈ F, t.card = 3)
    (x y : V) : EdgesOn ({x,y}ᶜ) (link F x y) := by
  intro e he
  obtain ⟨t,ht,rfl⟩ := mem_image.mp he
  obtain ⟨htF,hx,hy⟩ := mem_filter.mp ht
  refine ⟨?_, by rw [card_erase_of_mem hx, hu t htF]⟩
  intro z hz
  obtain ⟨hzx,hzt⟩ := mem_erase.mp hz
  simp [hzx, show z ≠ y from fun h => hy (h ▸ hzt)]

theorem link_nonempty {F : Finset (Finset V)} {x y : V}
    (hcov : ∀ t ∈ F, x ∈ t ∨ y ∈ t) (hn : ∀ z, ∃ t ∈ F, z ∉ t) :
    (link F x y).Nonempty := by
  obtain ⟨t,ht,hy⟩ := hn y
  exact ⟨_, mem_image.mpr ⟨t, mem_filter.mpr ⟨ht,(hcov t ht).resolve_right hy,hy⟩, rfl⟩⟩

theorem link_cross {F : Finset (Finset V)} (hi : (F : Set (Finset V)).Intersecting)
    (x y : V) : Cross (link F x y) (link F y x) := by
  intro e he f hf
  obtain ⟨s,hs,rfl⟩ := mem_image.mp he
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hf
  obtain ⟨hsF,_,hys⟩ := mem_filter.mp hs
  obtain ⟨htF,_,hxt⟩ := mem_filter.mp ht
  obtain ⟨z,hzs,hzt⟩ := not_disjoint_iff.mp (hi hsF htF)
  exact not_disjoint_iff.mpr ⟨z,mem_erase.mpr ⟨fun h => hxt (h ▸ hzt),hzs⟩,
    mem_erase.mpr ⟨fun h => hys (h ▸ hzs),hzt⟩⟩

/-- Hilton–Milner for a family of triples with a two-point transversal. -/
theorem hiltonMilner_of_pair [Fintype V] {F : Finset (Finset V)} (hn : 7 ≤ Fintype.card V)
    (hu : ∀ t ∈ F, t.card = 3) (hi : (F : Set (Finset V)).Intersecting)
    (hns : ∀ z, ∃ t ∈ F, z ∉ t) (hp : PairTransversal F) :
    F.card ≤ 3 * Fintype.card V - 8 := by
  classical
  obtain ⟨x,y,hxy,hcov⟩ := hp
  let U : Finset V := {x,y}ᶜ
  have hU : U.card = Fintype.card V - 2 := by rw [show U = {x,y}ᶜ from rfl, card_compl, card_pair hxy]
  have hY : EdgesOn U (link F y x) := by simpa [U, pair_comm y x] using link_edges hu y x
  have hsum := cross_edges_bound (U := U) (by omega) (link_edges hu x y) hY
    (link_nonempty hcov hns) (link_nonempty (fun t ht => (hcov t ht).symm) hns) (link_cross hi x y)
  let shared : Finset (Finset V) := U.image (fun z => {x,y,z})
  let lx := (link F x y).image (insert x)
  let ly := (link F y x).image (insert y)
  have lift {a b : V} {t : Finset V} (ht : t ∈ F) (ha : a ∈ t) (hb : b ∉ t) :
      t ∈ (link F a b).image (insert a) := mem_image.mpr
        ⟨_,mem_image.mpr ⟨t,mem_filter.mpr ⟨ht,ha,hb⟩,rfl⟩,insert_erase ha⟩
  have sub : F ⊆ shared ∪ (lx ∪ ly) := by
    intro t ht
    by_cases hx : x ∈ t <;> by_cases hy : y ∈ t
    · have hmore : ¬t ⊆ {x,y} := by
        intro h
        have hle := card_le_card h
        simp [hu t ht,hxy] at hle
      obtain ⟨z,hzt,hz⟩ := not_subset.mp hmore
      have hns : z ≠ x ∧ z ≠ y := by simpa using hz
      exact mem_union_left _ (mem_image.mpr ⟨z, mem_compl.mpr hz,
        (triple_from_points (hu t ht) hxy hns.1.symm hns.2.symm hx hy hzt).symm⟩)
    · exact mem_union_right _ (mem_union_left _ (lift ht hx hy))
    · exact mem_union_right _ (mem_union_right _ (lift ht hy hx))
    · exact ((hcov t ht).elim hx hy).elim
  have h := (card_le_card sub).trans (card_union_le _ _)
  have h' := card_union_le lx ly
  have hs : shared.card ≤ U.card := card_image_le
  have hx : lx.card ≤ (link F x y).card := card_image_le
  have hy : ly.card ≤ (link F y x).card := card_image_le
  omega

/-- The large-order Hilton–Milner inequality needed for the order reduction. -/
theorem hiltonMilner_large [Fintype V] {F : Finset (Finset V)} (hn : 12 ≤ Fintype.card V)
    (hu : ∀ t ∈ F, t.card = 3) (hi : (F : Set (Finset V)).Intersecting)
    (hns : ∀ x, ∃ t ∈ F, x ∉ t) : F.card ≤ 3 * Fintype.card V - 8 := by
  by_cases h : PairTransversal F
  · exact hiltonMilner_of_pair (by omega) hu hi hns h
  · have := no_pair_bound_twenty_seven hu hi h
    omega

/-- Four shapes for the two cross-intersecting links, up to exchanging the two centers. -/
def LinkTemplate (A B : Finset (Finset V)) : Prop :=
  A.card = 1 ∨
  (∃ a, (∀ e ∈ A, a ∈ e) ∧ ∀ e ∈ B, a ∈ e) ∨
  (∃ a u v : V, a ≠ u ∧ a ≠ v ∧ u ≠ v ∧ A = {{a,u},{a,v}} ∧ ∀ e ∈ B, a ∈ e ∨ e = {u,v}) ∨
  (∃ D : Finset V, D.card ≤ 4 ∧ (∀ e ∈ A, e ⊆ D) ∧ ∀ e ∈ B, e ⊆ D)

private theorem triangle_support {A : Finset (Finset V)} {U : Finset V} (hA : EdgesOn U A)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hits : ∀ e ∈ A, ¬Disjoint {a,b} e ∧ ¬Disjoint {a,c} e ∧ ¬Disjoint {b,c} e) :
    ∀ e ∈ A, e ⊆ {a,b,c} := by
  intro e he
  obtain ⟨p₁,p₂,p₃⟩ := hits e he
  by_cases ha : a ∈ e
  · rcases meets_pair p₃ with hb | hc
    · rw [edge_eq (hA _ he).2 ha hb hab]; simp [insert_subset_iff]
    · rw [edge_eq (hA _ he).2 ha hc hac]; simp [insert_subset_iff]
  · rw [edge_eq (hA _ he).2 ((meets_pair p₁).resolve_left ha) ((meets_pair p₂).resolve_left ha) hbc]
    simp

private theorem template_of_intersecting_link {U : Finset V} {A B : Finset (Finset V)}
    (hA : EdgesOn U A) (hB : EdgesOn U B) (hi : Cross A A) (hc : Cross A B) (hn : 1 < A.card) :
    LinkTemplate A B := by
  obtain ⟨e,he,f,hf,hef⟩ := one_lt_card.mp hn
  obtain ⟨a,u,v,hua,hva,huv,rfl,rfl⟩ := adjacent_edges (hA _ he).2 (hA _ hf).2 hef (hi _ he _ hf)
  by_cases star : ∀ e ∈ A, a ∈ e
  · by_cases both : ∀ e ∈ B, a ∈ e
    · exact Or.inr (Or.inl ⟨a,star,both⟩)
    push Not at both
    obtain ⟨b,hb,hab⟩ := both
    obtain rfl : b = {u,v} := edge_eq (hB _ hb).2 ((meets_pair (hc _ he _ hb)).resolve_left hab)
      ((meets_pair (hc _ hf _ hb)).resolve_left hab) huv
    refine Or.inr (Or.inr (Or.inl ⟨a,u,v,hua.symm,hva.symm,huv,?_,?_⟩))
    · ext g
      constructor
      · intro hg
        rcases meets_pair ((cross_symm hc) _ hb _ hg) with hu | hv
        · exact mem_insert.mpr (Or.inl (edge_eq (hA _ hg).2 (star _ hg) hu hua.symm))
        · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (edge_eq (hA _ hg).2 (star _ hg) hv hva.symm)))
      · intro hg
        rcases mem_insert.mp hg with rfl | hg
        · exact he
        obtain rfl := mem_singleton.mp hg
        exact hf
    · intro t ht
      by_cases hat : a ∈ t
      · exact Or.inl hat
      exact Or.inr (edge_eq (hB _ ht).2 ((meets_pair (hc _ he _ ht)).resolve_left hat)
        ((meets_pair (hc _ hf _ ht)).resolve_left hat) huv)
  push Not at star
  obtain ⟨g,hg,hag⟩ := star
  obtain rfl : g = {u,v} := edge_eq (hA _ hg).2 ((meets_pair (hi _ he _ hg)).resolve_left hag)
    ((meets_pair (hi _ hf _ hg)).resolve_left hag) huv
  refine Or.inr (Or.inr (Or.inr ⟨{a,u,v},?_,?_,?_⟩))
  · simp [hua.symm,hva.symm,huv]
  · exact triangle_support hA hua.symm hva.symm huv (fun t ht => ⟨hi _ he _ ht,hi _ hf _ ht,hi _ hg _ ht⟩)
  · exact triangle_support hB hua.symm hva.symm huv (fun t ht => ⟨hc _ he _ ht,hc _ hf _ ht,hc _ hg _ ht⟩)

private theorem supported_by_disjoint {U : Finset V} {A B : Finset (Finset V)}
    (hB : EdgesOn U B) (hc : Cross A B) {e f : Finset V} (he : e ∈ A) (hf : f ∈ A)
    (hd : Disjoint e f) : ∀ t ∈ B, t ⊆ e ∪ f := by
  intro t ht
  obtain ⟨x,hx,hxt⟩ := not_disjoint_iff.mp (hc _ he _ ht)
  obtain ⟨y,hy,hyt⟩ := not_disjoint_iff.mp (hc _ hf _ ht)
  rw [edge_eq (hB _ ht).2 hxt hyt (fun h => disjoint_left.mp hd hx (h ▸ hy))]
  exact insert_subset (mem_union_left _ hx) (singleton_subset_iff.mpr (mem_union_right _ hy))

/-- With a transversal pair, the two nonempty links fall into one of the four templates. -/
theorem link_classification [Fintype V] {F : Finset (Finset V)} (hu : ∀ t ∈ F, t.card = 3)
    (hi : (F : Set (Finset V)).Intersecting) (hns : ∀ z, ∃ t ∈ F, z ∉ t)
    {x y : V} (hcov : ∀ t ∈ F, x ∈ t ∨ y ∈ t) :
    LinkTemplate (link F x y) (link F y x) ∨ LinkTemplate (link F y x) (link F x y) := by
  classical
  let A := link F x y
  let B := link F y x
  let U : Finset V := {x,y}ᶜ
  have hA : EdgesOn U A := link_edges hu x y
  have hB : EdgesOn U B := by simpa [U,B,pair_comm y x] using link_edges hu y x
  have hc : Cross A B := link_cross hi x y
  have ha : 0 < A.card := card_pos.mpr (link_nonempty hcov hns)
  have hb : 0 < B.card := card_pos.mpr (link_nonempty (fun t ht => (hcov t ht).symm) hns)
  by_cases hs : A.card = 1
  · exact Or.inl (Or.inl hs)
  by_cases ht : B.card = 1
  · exact Or.inr (Or.inl ht)
  by_cases h₁ : Cross A A
  · exact Or.inl (template_of_intersecting_link hA hB h₁ hc (show 1 < A.card by omega))
  by_cases h₂ : Cross B B
  · exact Or.inr (template_of_intersecting_link hB hA h₂ (cross_symm hc) (show 1 < B.card by omega))
  simp only [Cross, not_forall, not_not] at h₁ h₂
  obtain ⟨a,ha,b,hb,hab⟩ := h₁
  obtain ⟨c,hc',d,hd,hcd⟩ := h₂
  have hsup := supported_by_disjoint hB hc ha hb hab
  have hsup' := supported_by_disjoint hA (cross_symm hc) hc' hd hcd
  have sub := union_subset (hsup c hc') (hsup d hd)
  exact Or.inl (Or.inr (Or.inr (Or.inr ⟨a ∪ b,by rw [card_union_of_disjoint hab,(hA _ ha).2,(hA _ hb).2],
    fun t ht => (hsup' t ht).trans sub,hsup⟩)))

end StableKneserK3

