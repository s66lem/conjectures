import Conjectures.FanelliMoscardelli.Residual

namespace FanelliMoscardelli.Market
open Roommates Finset
variable {m : ℕ} {p : Market m}
local notation "V" => Agent m
local notation "E" => Edge p
local notation "x" => mid p
local notation "f" => first p

theorem extend {S : Finset V} (h : Pairs S E) :
    ∃ T : Finset V, Disjoint S T ∧ Pairs T E ∧ Packed p (S ∪ T)ᶜ := by
  classical
  let A := univ.filter (fun T : Finset V ↦ Disjoint S T ∧ Pairs T E)
  obtain ⟨T, hT, hmax⟩ := exists_max_image A card
    (⟨∅, by simp [A, Pairs.empty]⟩ : A.Nonempty)
  obtain ⟨hd, ht⟩ := (mem_filter.mp hT).2
  refine ⟨T,hd,ht,⟨by simpa using h.union ht hd, ?_⟩⟩
  intro a ha b hb he
  simp only [mem_compl, mem_union, not_or] at ha hb
  have hab : a ≠ b := fun eq ↦ edge_irrefl p b (eq ▸ he)
  let U := T ∪ {a,b}
  have hU : U ∈ A := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ht.union (Pairs.pair he (edge_symm p he)) ?_⟩
    · exact Finset.disjoint_union_right.mpr ⟨hd, by simp [Finset.disjoint_right, ha, hb]⟩
    · simp [Finset.disjoint_right, ha, hb]
  have hlt : T ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, fun eq ↦ ha.2
    (eq ▸ (show a ∈ U by simp [U]))⟩
  exact (not_lt_of_ge (hmax _ hU)) (card_lt_card hlt)

/-- The alternating exchange covers a vertex and then forces its two consecutive
predecessors to compete for the only newly exposed vertex. -/
theorem Packed.isolated {W : Finset V} (h : Packed p W) (hm : 0 < m)
    (bad : ¬Solved p) {w : V} (hw : w ∈ W) (y : V) : ¬ E w y := by
  intro hwy
  have hy : y ∉ W := fun hy ↦ h.indep _ hw _ hy hwy
  obtain ⟨g,hg⟩ := h.cover
  let z := g y
  obtain ⟨hz,hzy,hyz⟩ := hg y (mem_compl.mpr hy)
  change z ∈ Wᶜ at hz
  change g z = y at hzy
  change E y z at hyz
  let R := Wᶜ \ {y,z}
  have hr : Pairs R E := by
    refine ⟨g, fun i hi ↦ ?_⟩
    obtain ⟨hi',hne⟩ := mem_sdiff.mp hi
    obtain ⟨hgi,hii,hei⟩ := hg i hi'
    refine ⟨mem_sdiff.mpr ⟨hgi,?_⟩,hii,hei⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hne ⊢
    change g z = y at hzy
    have : g y = z := rfl
    grind
  let S := R ∪ {w,y}
  have hS : Pairs S E := hr.union (Pairs.pair hwy (edge_symm p hwy)) (by
    simp [Finset.disjoint_right,R,hw])
  obtain ⟨T, hd, hT, hp⟩ := extend hS
  have cy := h.cycles hm bad
  have cy' := hp.cycles hm bad
  let a := f w
  let b := f a
  have ha : a ∈ W := cy.first_mem w hw
  have hb : b ∈ W := cy.first_mem a ha
  have hxa : x a = w := cy.mid_first w hw
  have hxb : x b = a := cy.mid_first a ha
  have haw : a ≠ w := fun e ↦ mid_ne p hm a (hxa.trans e.symm)
  have hba : b ≠ a := fun e ↦ mid_ne p hm b (hxb.trans e.symm)
  have hbw : b ≠ w := by
    intro he
    have hh := rank_first p a
    change p.partnerRank a b = 1 at hh
    rw [he, ← hxa, rank_mid] at hh
    omega
  have hwt : w ∈ S ∪ T := by simp [S]
  have back : ∀ v, x v ∈ S ∪ T → v ∈ S ∪ T := by
    intro v hv
    by_contra hn
    exact (mem_compl.mp (cy'.mid_mem _ (mem_compl.mpr hn))) hv
  have hat : a ∈ T := by
    have := back a (hxa ▸ hwt)
    simp [S,R,ha,haw] at this
    grind
  have hbt : b ∈ T := by
    have := back b (hxb ▸ mem_union_right S hat)
    simp [S,R,hb,hbw] at this
    grind
  obtain ⟨t,ht⟩ := hT
  have onlyZ : ∀ v ∈ W, v ∈ T → t v = z := by
    intro v hv hvt
    obtain ⟨htv,_,he⟩ := ht v hvt
    have h₁ : t v ∉ W := fun hmem ↦ h.indep v hv _ hmem he
    have h₂ : t v ∉ S := fun hmem ↦ Finset.disjoint_left.mp hd hmem htv
    simp [S,R,h₁] at h₂
    tauto
  have h₁ := (ht a hat).2.1
  have h₂ := (ht b hbt).2.1
  rw [onlyZ a ha hat] at h₁
  rw [onlyZ b hb hbt] at h₂
  exact hba (h₂.symm.trans h₁)

variable (p) in
noncomputable def active : Finset V := by
  classical
  exact univ.filter (fun i ↦ ∃ j, E i j)

@[simp] theorem mem_active {i : V} : i ∈ active p ↔ ∃ j, E i j := by classical simp [active]

theorem packed_iff_compl {W : Finset V} (h : Packed p W) (hm : 0 < m) (bad : ¬Solved p) :
    Wᶜ = active p := by
  obtain ⟨g,hg⟩ := h.cover
  ext i
  simp only [mem_compl, mem_active]
  exact ⟨fun hn ↦ ⟨g i, (hg _ (mem_compl.mpr hn)).2.2⟩,
    fun ⟨y,he⟩ hi ↦ h.isolated hm bad hi y he⟩

theorem residual_packed (hm : 0 < m) (bad : ¬Solved p) : Packed p (active p)ᶜ := by
  obtain ⟨T,_,_,hp⟩ := extend (p := p) Pairs.empty
  have eq := packed_iff_compl hp hm bad
  rw [← eq, compl_compl]
  exact hp

/-- Every prescribed partial graph matching extends over all active vertices. -/
theorem residual_extend (hm : 0 < m) (bad : ¬Solved p) {S : Finset V} (hs : Pairs S E) :
    Pairs (active p \ S) E := by
  obtain ⟨T,hd,hT,hp⟩ := extend hs
  have eq := packed_iff_compl hp hm bad
  rw [compl_compl] at eq
  have : (S ∪ T) \ S = T := by ext; simp only [mem_sdiff,mem_union]; have := Finset.disjoint_left.mp hd; grind
  rwa [← eq, this]

end FanelliMoscardelli.Market
