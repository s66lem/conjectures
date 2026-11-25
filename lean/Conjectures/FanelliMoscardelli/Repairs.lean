import Conjectures.FanelliMoscardelli.RandomMatching

namespace FanelliMoscardelli.Market
open Roommates Finset
open scoped Classical
variable {m : ℕ} {p : Market m}
local notation "V" => Agent m
local notation "E" => Edge p
local notation "J" => active p
local notation "I" => (active p)ᶜ
local notation "x" => mid p
local notation "f" => first p
local notation "r" => p.partnerRank

theorem isolate_count (hm : 0 < m) (bad : ¬ Solved p) : 3 ≤ (I).card := by
  have hp := residual_packed hm bad
  have hc := hp.cycles hm bad
  have evt := hp.cover.card_even (fun i _ ↦ edge_irrefl p i)
  rw [compl_compl] at evt
  obtain ⟨k,hk⟩ := evt
  have hcard := card_compl_add_card J
  simp only [Fintype.card_fin] at hcard
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < (I).card by omega)
  have h₁ := hc.first_mem w hw
  have h₂ := hc.mid_mem w hw
  have h₃ := mid_ne p hm w
  have h₄ : f w ≠ w := by
    intro h
    have := rank_first p w
    rw [h,CompleteProfile.partnerRank_self] at this
    omega
  have h₅ : f w ≠ x w := by
    intro h
    have := rank_first p w
    rw [h,rank_mid] at this
    omega
  have hsub : ({w,f w,x w} : Finset V) ⊆ I := by intro a; simp only [mem_insert,mem_singleton]; grind
  simpa [Finset.card_insert_of_notMem,Ne.symm h₄,Ne.symm h₃,h₅] using card_le_card hsub

theorem active_nonempty (hm : 3 ≤ m) (bad : ¬Solved p) : (J).Nonempty := by
  have hcm := residual_packed (by omega : 0<m) bad
  have cy := hcm.cycles (by omega) bad
  by_contra hn
  have hem := not_nonempty_iff_eq_empty.mp hn
  have hall : ∀ v : V, v ∈ I := by simp [hem]
  let u : V := 0
  have hsub : univ.filter (fun j ↦ r u j ≤ m) ⊆ {f u} := by
    intro j hj
    have h := cy.other u (hall _) j (hall _)
    have := (mem_filter.mp hj).2
    simp only [mem_singleton]; by_contra hne; have := h hne; omega
  have := card_le_card hsub
  rw [card_choices p u (by omega),card_singleton] at this
  omega

private theorem fill_isolates (hm : 0 < m) (bad : ¬Solved p) {s w : V}
    (hs : s ∈ J) (hw : w ∈ I) :
    Pairs ((I).erase w) (fun i j ↦ i ≠ j ∧ (i = x s → r i j < r i s + m)) := by
  have hp := residual_packed hm bad
  have cy := hp.cycles hm bad
  have even := hp.even_erase hw
  by_cases hxs : x s ∈ (I).erase w
  · obtain ⟨hne,hi⟩ := mem_erase.mp hxs
    have hs' := rank_pos p (x s) s
    have hfs : f (x s) ≠ s := by
      have := mem_compl.mp (cy.first_mem _ hi)
      grind
    have hr : 1 < r (x s) s := by
      have h := rank_first p (x s)
      have h' : r (x s) (f (x s)) ≠ r (x s) s := fun e ↦ hfs (rank_inj p _ e)
      omega
    have hh : ∃ a ∈ (I).erase w, x s ≠ a ∧ r (x s) a < r (x s) s + m := by
      by_cases he : f (x s) = w
      · refine ⟨x (x s), mem_erase.mpr ⟨?_,cy.mid_mem _ hi⟩,(mid_ne p hm _).symm,?_⟩
        · intro e
          have hh := rank_mid p (x s)
          rw [e, ← he, rank_first] at hh
          omega
        · rw [rank_mid]; omega
      · refine ⟨f (x s), mem_erase.mpr ⟨he,cy.first_mem _ hi⟩,?_,?_⟩
        · intro e
          have hh := rank_first p (x s)
          rw [← e, CompleteProfile.partnerRank_self] at hh
          omega
        · rw [rank_first]; omega
    obtain ⟨a,ha,hne',har⟩ := hh
    apply (force_pair even hxs ha hne').mono
    intro i hi j hj hij
    exact ⟨hij.1, fun e ↦ by subst i; rwa [hij.2 rfl]⟩
  · apply (Pairs.of_even even).mono
    intro i hi j hj hij
    exact ⟨hij,fun eq ↦ False.elim (hxs (eq ▸ hi))⟩

/-- Put a prescribed local repair beside a graph matching and a protected
pairing of the isolates. Failure can only come from the special assignments. -/
private theorem local_failure (hm : 0 < m) (bad : ¬Solved p)
    {s w : V} {K : Finset V} {D : V → V → Prop} (hs : s ∈ J) (hw : w ∈ I)
    (hK : K ⊆ J) (cover : Pairs (J \ K) E) (repair : Pairs (insert w K) D)
    (single : ∀ i, D i i → i = s)
    (safe : ∀ i j a b, E i j → D i a → D j b → r i a < r i j+m ∨ r j b < r j i+m) :
    ∃ a, D (x s) a ∧ r (x s) s + m ≤ r (x s) a := by
  let R i j := (i ∈ J \ K ∧ E i j) ∨ D i j ∨
    (i ∈ (I).erase w ∧ i ≠ j ∧ (i = x s → r i j < r i s + m))
  have h₁ : Pairs (J \ K) R := cover.mono (by intro i hi j hj he; exact Or.inl ⟨hi,he⟩)
  have h₂ : Pairs (insert w K) R := repair.mono (by intro i hi j hj hd; exact Or.inr (Or.inl hd))
  have h₃ : Pairs ((I).erase w) R := (fill_isolates hm bad hs hw).mono (by
    intro i hi j hj hd; exact Or.inr (Or.inr ⟨hi,hd⟩))
  have hw' := mem_compl.mp hw
  have eq : ((J \ K) ∪ insert w K) ∪ (I).erase w = univ := by
    ext i; simp only [mem_union,mem_sdiff,mem_insert,mem_erase,mem_compl,mem_univ,iff_true]; grind
  have h₁₂ : Disjoint (J \ K) (insert w K) := by
    simp only [Finset.disjoint_left,mem_sdiff,mem_insert]; grind
  have h₁₂₃ : Disjoint ((J \ K) ∪ insert w K) ((I).erase w) := by
    simp only [Finset.disjoint_left,mem_sdiff,mem_union,mem_insert,mem_erase,mem_compl]
    have hh := fun i (hi : i ∈ K) ↦ hK hi
    grind
  by_contra hn
  apply bad
  apply criterion p (u := s) (eq ▸ (h₁.union h₂ h₁₂).union h₃ h₁₂₃)
  · intro i hi
    have := edge_irrefl p i
    simp only [R] at hi
    grind
  · intro i j a b he hir hjr
    have hi := mem_active.mpr ⟨j,he⟩
    have hj := mem_active.mpr ⟨i,edge_symm p he⟩
    have pos₁ := rank_pos p i j
    have pos₂ := rank_pos p j i
    simp only [R,mem_erase,mem_compl] at hir hjr
    rcases hir with ⟨_,hh⟩ | hh | hh
    · exact Or.inl (by have := hh.1; omega)
    · rcases hjr with ⟨_,hh'⟩ | hh' | hh'
      · exact Or.inr (by have := hh'.1; omega)
      · exact safe _ _ _ _ he hh hh'
      · exact (hh'.1.2 hj).elim
    · exact (hh.1.2 hi).elim
  · intro a ha
    have := rank_pos p (x s) s
    rcases ha with ⟨_,hh⟩ | hh | hh
    · have := hh.1; omega
    · by_contra hge; exact hn ⟨a,hh,by omega⟩
    · exact hh.2.2 rfl

theorem repair_one (hm : 0 < m) (bad : ¬Solved p) {u y w : V} (he : E u y) (hw : w ∈ I)
    (hclose : r y w < r y u + m) :
    x u = w ∧ r w u + m ≤ r w y := by
  have hu := mem_active.mpr ⟨y,he⟩
  have hy := mem_active.mpr ⟨u,edge_symm p he⟩
  have hw' := mem_compl.mp hw
  have huy : u ≠ y := fun e ↦ edge_irrefl p y (e ▸ he)
  let D i j := (i = u ∧ j = u) ∨ (i = y ∧ j = w) ∨ (i = w ∧ j = y)
  let K : Finset V := {u,y}
  have hK : K ⊆ J := by intro i; simp only [K,mem_insert,mem_singleton]; grind
  have hcover := residual_extend hm bad (Pairs.pair he (edge_symm p he))
  have hr : Pairs (insert w K) D := by
    have eq : insert w K = {u} ∪ ({y,w} : Finset V) := by ext; simp [K]; tauto
    rw [eq]
    exact (Pairs.single (a := u) (by simp [D])).union
      (Pairs.pair (a := y) (b := w) (by simp [D]) (by simp [D]))
      (by simp; grind)
  obtain ⟨a,ha,hblock⟩ := local_failure hm bad hu hw hK hcover hr (by simp [D]; grind) (by
    intro i j a b hij hi hj
    have hiJ := mem_active.mpr ⟨j,hij⟩
    have hjJ := mem_active.mpr ⟨i,edge_symm p hij⟩
    have hneq : i ≠ j := fun e ↦ edge_irrefl p j (e ▸ hij)
    simp only [D] at hi hj
    grind)
  have hx := mid_ne p hm u
  have hxy : x u ≠ y := by
    intro e
    have hh := he.1
    rw [← e,rank_mid] at hh
    omega
  simp only [D] at ha
  grind

theorem repair_two_either (F : Frame p) (hm : 0 < m) (bad : ¬Solved p)
    {s e q t w : V} (he : E s e) (hq : E q t) (hw : w ∈ I) (far : ¬ F.Related e q)
    (hc₁ : r e q < r e s + m) (hc₂ : r q e < r q t + m ∨ r t w < r t q + m) (hwx : w ≠ x s) :
    (x s = q ∧ r q s + m ≤ r q e) ∨ (x s = t ∧ r t s + m ≤ r t w) := by
  have hs := mem_active.mpr ⟨e,he⟩
  have heJ := mem_active.mpr ⟨s,edge_symm p he⟩
  have hqJ := mem_active.mpr ⟨t,hq⟩
  have ht := mem_active.mpr ⟨q,edge_symm p hq⟩
  have hw' := mem_compl.mp hw
  have h₁ : F.Related e s := Or.inl (edge_symm p he)
  have h₂ : F.Related t q := Or.inl (edge_symm p hq)
  have cross : ∀ i ∈ ({s,e} : Finset V), ∀ j ∈ ({q,t} : Finset V), ¬F.Related i j := by
    intro i hi j hj h
    have hr₁ : F.Related e i := by
      simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl|rfl
      · exact h₁
      · exact F.self heJ
    have hr₂ : F.Related j q := by
      simp only [mem_insert,mem_singleton] at hj
      rcases hj with rfl|rfl
      · exact F.self hqJ
      · exact h₂
    exact far (F.trans (F.trans hr₁ h) hr₂)
  have dis : Disjoint ({s,e} : Finset V) {q,t} := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; apply cross _ hi _ hj
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl|rfl
    · exact F.self hs
    · exact F.self heJ
  have hd := Finset.disjoint_left.mp dis
  simp only [mem_insert,mem_singleton] at hd cross
  have hse : s ≠ e := fun eq ↦ edge_irrefl p e (eq ▸ he)
  have hqt : q ≠ t := fun eq ↦ edge_irrefl p t (eq ▸ hq)
  let K : Finset V := {s,e} ∪ {q,t}
  let D i j := (i = s ∧ j = s) ∨ (i = e ∧ j = q) ∨ (i = q ∧ j = e) ∨
    (i = t ∧ j = w) ∨ (i = w ∧ j = t)
  have hK : K ⊆ J := by intro i; simp only [K,mem_union,mem_insert,mem_singleton]; grind
  have cover := F.finish ((Pairs.pair he (edge_symm p he)).union (Pairs.pair hq (edge_symm p hq)) dis)
  have repair : Pairs (insert w K) D := by
    have eq : insert w K = ({s} ∪ {e,q}) ∪ ({t,w} : Finset V) := by ext; simp [K]; tauto
    rw [eq]
    refine ((Pairs.single (a := s) (by simp [D])).union
      (Pairs.pair (a := e) (b := q) (by simp [D]) (by simp [D])) ?_).union
      (Pairs.pair (a := t) (b := w) (by simp [D]) (by simp [D])) ?_ <;>
      simp only [Finset.disjoint_left,mem_union,mem_insert,mem_singleton] <;> grind
  obtain ⟨a,ha,hh⟩ := local_failure hm bad hs hw hK cover repair (by simp [D]; grind) (by
    intro i j a b hij hi hj
    have hiJ := mem_active.mpr ⟨j,hij⟩
    have hjJ := mem_active.mpr ⟨i,edge_symm p hij⟩
    have hneq : i ≠ j := fun eq ↦ edge_irrefl p j (eq ▸ hij)
    have hr₁ : F.Related i j := Or.inl hij
    have hr₂ := F.symm hr₁
    simp only [D] at hi hj
    grind)
  have hx := mid_ne p hm s
  have hxe : x s ≠ e := by intro eq; have := he.1; rw [← eq,rank_mid] at this; omega
  simp only [D] at ha
  grind

theorem repair_two (F : Frame p) (hm : 0 < m) (bad : ¬Solved p)
    {s e q t w : V} (he : E s e) (hq : E q t) (hw : w ∈ I) (far : ¬ F.Related e q)
    (hc₁ : r e q < r e s + m) (hc₂ : r q e < r q t + m) (hwx : w ≠ x s) :
    (x s = q ∧ r q s + m ≤ r q e) ∨ (x s = t ∧ r t s + m ≤ r t w) :=
  repair_two_either F hm bad he hq hw far hc₁ (Or.inl hc₂) hwx

theorem other_isolate (hm : 0<m) (bad : ¬Solved p) (z : V) : ∃ w ∈ I, w ≠ z := by
  by_contra! hn
  have hsub : I ⊆ {z} := by simpa only [Finset.subset_iff,mem_singleton] using hn
  have hcard := card_le_card hsub
  have := isolate_count hm bad
  simp only [card_singleton] at hcard
  omega

end FanelliMoscardelli.Market
