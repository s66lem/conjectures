import Conjectures.FanelliMoscardelli.Repairs

namespace FanelliMoscardelli.Market
open Roommates Finset
open scoped Classical
variable {m : ℕ} {p : Market m}
local notation "V" => Agent m
local notation "E" => Edge p
local notation "J" => active p
local notation "I" => (active p)ᶜ
local notation "x" => mid p
local notation "r" => p.partnerRank

private theorem exists_worst {i : V} (hi : i ∈ J) :
    ∃ u, E i u ∧ ∀ v, E i v → r i v ≤ r i u := by
  obtain ⟨v,hv⟩ := mem_active.mp hi
  let N := univ.filter (E i)
  obtain ⟨u, hu, hd⟩ := exists_max_image N (r i) ⟨v,mem_filter.mpr ⟨mem_univ _,hv⟩⟩
  exact ⟨u,(mem_filter.mp hu).2,fun a ha ↦ hd _ (mem_filter.mpr ⟨mem_univ _,ha⟩)⟩

variable (p) in
noncomputable def worst (i : V) := if h : i ∈ J then (exists_worst h).choose else i
variable (p) in
noncomputable def d (i : V) := r i (worst p i)
theorem worst_edge {i : V} (hi : i ∈ J) : E i (worst p i) := by
  simpa only [worst,dif_pos hi] using (exists_worst hi).choose_spec.1
theorem le_d {i v : V} (he : E i v) : r i v ≤ d p i := by
  have hi := mem_active.mpr ⟨_,he⟩
  simpa only [d,worst,dif_pos hi] using (exists_worst hi).choose_spec.2 v he
theorem d_le {i : V} (hi : i ∈ J) : d p i ≤ m := (worst_edge hi).1

variable (p) in
def Accept (i j : V) := r i j < d p i + m
def Eligible (q i y : V) := Edge p q y ∧ r q i < r q y + m

namespace Frame
variable (F : Frame p)
local notation "g" => F.g

def Small (i : V) := ∀ j, E i j → j = g i

theorem small_neighbor {i j : V} (hi : F.Small i) (h : E i j) : F.Small j := by
  intro k hk
  have hji := hi j h
  have h' := F.flip hk
  rw [hji,F.twice] at h'
  have heq := hi _ h'
  have := F.inv.injective heq
  rw [hji,F.twice]; assumption

theorem small_component {i j : V} (hi : F.Small i) (hr : F.Related i j) : j = i ∨ j = g i := by
  rcases hr with h|h
  · exact Or.inr (hi _ h)
  · exact Or.inl (F.inv.injective (hi _ h))

theorem rank_two {i : V} (hi : ¬F.Small i) : 2 ≤ d p i := by
  by_contra! hn
  apply hi
  intro j hj
  have hgi := F.adj _ (mem_active.mpr ⟨j,hj⟩)
  have h₁ := le_d hj
  have h₂ := le_d hgi
  apply rank_inj p i
  have := rank_pos p i j
  have := rank_pos p i (g i)
  omega

/-- Any acceptable isolated vertex identifies the unique neighbor of the source
and forces that neighbor's middle choice. -/
theorem isolate_rule (hm : 0<m) (bad : ¬Solved p) {y w : V} (hy : y ∈ J)
    (hw : w ∈ I) (ha : Accept p y w) :
    F.Small y ∧ x (g y) = w ∧ r w (g y) ≤ m ∧ m < r w y := by
  let u := worst p y
  have he : E y u := worst_edge hy
  have hC : r y w < r y u + m := ha
  obtain ⟨hxu,hr⟩ := repair_one hm bad (edge_symm p he) hw hC
  have hu := mem_active.mpr ⟨y,edge_symm p he⟩
  have hwy : y ≠ w := by have := mem_compl.mp hw; grind
  have hru : r w u ≤ m := by have := rank_other p hwy; omega
  have hry : m < r w y := by have := rank_pos p w u; omega
  have hmid : r u w = m + 1 := by rw [← hxu,rank_mid]
  have hfirst : r u y = 1 := by
    have hh := rank_pos p u y
    by_contra! hn
    obtain ⟨_,hh'⟩ := repair_one hm bad he hw (by omega : r u w < r u y + m)
    omega
  have hunique : ∀ v, E u v → v = y := by
    intro v hv
    by_contra hn
    have hne : r u v ≠ r u y := fun h ↦ hn (rank_inj p _ h)
    have := rank_pos p u v
    obtain ⟨_,hh⟩ := repair_one hm bad (edge_symm p hv) hw (by omega : r u w < r u v+m)
    have := rank_pos p w v
    omega
  have hgu := hunique _ (F.adj _ hu)
  have hgy : g y = u := hgu ▸ F.inv u
  have sm : F.Small u := fun v hv ↦ (hunique _ hv).trans hgu.symm
  exact ⟨F.small_neighbor sm (edge_symm p he), hgy ▸ hxu,hgy ▸ hru,hry⟩

/-- Both orientations of the two-edge repair determine the middle choices. -/
theorem good_rule (hm : 0 < m) (bad : ¬Solved p) {i q u y : V} (far : ¬F.Related i q)
    (htop : r i q ≤ m) (hu : E i u) (hy : Eligible (p := p) q i y) :
    x y = u ∧ r u y ≤ m ∧ x u = q ∧ r q u + m ≤ r q i := by
  obtain ⟨w,hw,hwx⟩ := other_isolate hm bad (x y)
  have hiq : r i q < r i u+m := by have := rank_pos p i u; omega
  have far' : ¬F.Related q i := fun h ↦ far (F.symm h)
  have hb := repair_two F hm bad (edge_symm p hy.1) hu hw far' hy.2 hiq hwx
  have h₁ : x y = u ∧ r u y ≤ m := by
    rcases hb with ⟨_,hh⟩ | ⟨he,hh⟩
    · have := rank_pos p i y; omega
    · have huJ := mem_active.mpr ⟨i,edge_symm p hu⟩
      have hwu : w ≠ u := by have := mem_compl.mp hw; grind
      have := rank_other p hwu
      exact ⟨he,by omega⟩
  obtain ⟨v,hv,hvx⟩ := other_isolate hm bad (x u)
  have hb' := repair_two F hm bad (edge_symm p hu) hy.1 hv far hiq hy.2 hvx
  rcases hb' with hh|⟨hxy,_⟩
  · exact ⟨h₁.1,h₁.2,hh⟩
  · have h := h₁.2
    rw [← hxy,rank_mid] at h
    omega

theorem no_good_big (hm : 0 < m) (bad : ¬Solved p) {i q : V} (hi : i ∈ J) (hq : q ∈ J)
    (far : ¬F.Related i q) (ht : r i q ≤ m) (ha : Accept p q i) : F.Small q := by
  by_contra big
  let u := g i
  have hu : E i u := F.adj _ hi
  have process : ∀ y, Eligible (p := p) q i y →
      x i = y ∧ x q = i := by
    intro y hy
    have h := F.good_rule hm bad far ht hu hy
    have hbig : ¬ F.Small y := fun hs ↦ big (F.small_neighbor hs (edge_symm p hy.1))
    have hmid : r y u = m+1 := by rw [← h.1,rank_mid]
    have far' : ¬F.Related u y := fun hh ↦ far (F.trans (Or.inl hu) (F.trans hh (Or.inl (edge_symm p hy.1))))
    let z := worst p y
    have hyJ := mem_active.mpr ⟨q,edge_symm p hy.1⟩
    have hzy : E y z := worst_edge hyJ
    have hd₂ := F.rank_two hbig
    have hyz : Eligible (p := p) y u z := ⟨hzy, by change _ < d p y + m; omega⟩
    have h' := F.good_rule hm bad far' h.2.1 (edge_symm p hu) hyz
    have hf : r y i = 1 := by have := h'.2.2.2; have := rank_pos p y i; omega
    have hqi : q ≠ i := by intro eq; exact far (by simpa only [← eq] using F.self hi)
    have hne : r y q ≠ r y i := fun eq ↦ hqi (rank_inj p _ eq)
    have hyq : Eligible (p := p) y u q := ⟨edge_symm p hy.1,by have := rank_pos p y q; omega⟩
    have h'' := F.good_rule hm bad far' h.2.1 (edge_symm p hu) hyq
    exact ⟨h'.2.2.1,h''.1⟩
  let y := worst p q
  have hy : Eligible (p := p) q i y := ⟨worst_edge hq,ha⟩
  have hh := process y hy
  have hmid : r q i = m+1 := by rw [← hh.2,rank_mid]
  have hstart := F.good_rule hm bad far ht hu hy
  have first : r q u = 1 := by have := hstart.2.2.2; have := rank_pos p q u; omega
  have all : ∀ z, E q z → x i = z := by
    intro z hz
    have hzu : z ≠ u := by
      intro e
      apply far
      exact F.trans (Or.inl hu) (Or.inl (edge_symm p (e ▸ hz)))
    have hne : r q z ≠ r q u := fun eq ↦ hzu (rank_inj p _ eq)
    exact (process z ⟨hz,by have := rank_pos p q z; omega⟩).1
  exact big (fun z hz ↦ (all z hz).symm.trans (all _ (F.adj _ hq)))

theorem mutual_rule (hm : 0 < m) (bad : ¬Solved p) {i q : V} (hi : i ∈ J) (hq : q ∈ J)
    (far : ¬F.Related i q) (h₁ : Accept p i q) (h₂ : Accept p q i) :
    F.Small i ∧ F.Related (x (g i)) q := by
  let s := worst p i
  let t := worst p q
  have hs : E i s := worst_edge hi
  have ht : E q t := worst_edge hq
  obtain ⟨w,hw,hwx⟩ := other_isolate hm bad (x s)
  have hh := repair_two F hm bad (edge_symm p hs) ht hw far h₁ h₂ hwx
  have hsJ := mem_active.mpr ⟨i,edge_symm p hs⟩
  have hdata : F.Related (x s) q ∧ r (x s) s ≤ m := by
    rcases hh with ⟨e,hb⟩|⟨e,hb⟩
    · rw [e]
      have hiq : i ≠ q := by intro eq; exact far (by simpa only [← eq] using F.self hi)
      have := rank_other p hiq
      exact ⟨F.self hq,by omega⟩
    · rw [e]
      have htJ := mem_active.mpr ⟨q,edge_symm p ht⟩
      have hwt : w ≠ t := by have := mem_compl.mp hw; grind
      have := rank_other p hwt
      exact ⟨Or.inl (edge_symm p ht),by omega⟩
  have sm : F.Small i := by
    by_contra hn
    have bigs : ¬F.Small s := fun h ↦ hn (F.small_neighbor h (edge_symm p hs))
    have hfar : ¬F.Related (x s) s := fun h ↦ far (F.trans (Or.inl hs) (F.trans (F.symm h) hdata.1))
    have hxJ : x s ∈ J := by rcases hh with ⟨e,_⟩|⟨e,_⟩; rw [e]; exact hq; rw [e]; exact mem_active.mpr ⟨q,edge_symm p ht⟩
    have hacc : Accept p s (x s) := by unfold Accept; rw [rank_mid]; have := F.rank_two bigs; omega
    exact bigs (F.no_good_big hm bad hxJ hsJ hfar hdata.2 hacc)
  exact ⟨sm, sm _ hs ▸ hdata.1⟩

end Frame
end FanelliMoscardelli.Market
