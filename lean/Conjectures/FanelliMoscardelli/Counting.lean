import Conjectures.FanelliMoscardelli.Arcs

namespace FanelliMoscardelli.Market.Frame
open Roommates Finset
open scoped Classical
variable {m : ℕ} {p : Market m} (F : Frame p)
local notation "V" => Agent m
local notation "E" => Edge p
local notation "J" => active p
local notation "I" => (active p)ᶜ
local notation "x" => mid p
local notation "r" => p.partnerRank
local notation "g" => F.g
local notation "A" => Accept p
noncomputable def comp (i : V) := (J).filter (F.Related i)
noncomputable def outside (i : V) := (J).filter (fun j ↦ ¬F.Related i j)
noncomputable def out (i : V) := (F.outside i).filter (A i)
noncomputable def incoming (i : V) := (F.outside i).filter (fun j ↦ A j i)
noncomputable def both (i : V) := F.out i ∩ F.incoming i
variable (p) in
noncomputable def exc (i : V) := (I).filter (A i)

private theorem both_rule (hm : 0 < m) (bad : ¬Solved p) {i j : V} (hi : i ∈ J)
    (hb : j ∈ F.both i) : F.Small i ∧ F.Small j ∧ F.Related (x (g i)) j := by
  simp only [both,out,incoming,outside,mem_inter,mem_filter] at hb
  have h₁ := F.mutual_rule hm bad hi hb.1.1.1 hb.1.1.2 hb.1.2 hb.2.2
  have h₂ := F.mutual_rule hm bad hb.1.1.1 hi (fun h ↦ hb.1.1.2 (F.symm h)) hb.2.2 hb.1.2
  exact ⟨h₁.1,h₂.1,h₁.2⟩

/-- An acceptable isolate consumes both units of the row's allowance for
mutual pairs. Vertices in larger components have neither kind of partner. -/
private theorem row_caps (hm : 0<m) (bad : ¬Solved p) {i : V} (hi : i ∈ J) :
    2*(exc p i).card + (F.both i).card ≤ 2 ∧
    (¬F.Small i → (exc p i).card = 0 ∧ (F.both i).card = 0) := by
  have hr := fun (j : V) (hj : j ∈ F.both i) ↦ F.both_rule hm bad hi hj
  have hs := fun (w : V) (hw : w ∈ exc p i) ↦
    F.isolate_rule hm bad hi (mem_filter.mp hw).1 (mem_filter.mp hw).2
  have hex : (exc p i).card ≤ 1 := card_le_one.mpr (fun a ha b hb ↦ (hs a ha).2.1.symm.trans (hs b hb).2.1)
  refine ⟨?_, fun hn ↦ ⟨?_,?_⟩⟩
  · rcases (F.both i).eq_empty_or_nonempty with he|⟨j,hj⟩
    · rw [he,card_empty]; omega
    have hj' := hr j hj
    have hxJ : x (g i) ∈ J := by
      rcases hj'.2.2 with h|h <;> exact mem_active.mpr ⟨_,h⟩
    have hem : exc p i = ∅ := eq_empty_iff_forall_notMem.mpr (fun w hw ↦
      (mem_compl.mp (mem_filter.mp hw).1) ((hs w hw).2.1 ▸ hxJ))
    have hsub : F.both i ⊆ {j,g j} := by
      intro k hk
      exact mem_insert.mpr (by
        simpa only [mem_singleton] using F.small_component hj'.2.1 (F.trans (F.symm hj'.2.2) (hr _ hk).2.2))
    have hh := card_le_card hsub
    have hl := card_insert_le j ({g j} : Finset V)
    rw [card_singleton] at hl
    rw [hem,card_empty]
    omega
  · exact card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr (fun w hw ↦ hn (hs w hw).1))
  · exact card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr (fun j hj ↦ hn (hr j hj).1))

private theorem row_size {i : V} (hi : i ∈ J) :
    d p i + m ≤ (exc p i).card + (F.comp i).card + (F.out i).card := by
  have hd := d_le hi
  have hpos : 0 < d p i := rank_pos p i _
  let B := univ.filter (A i)
  have eq : B = univ.filter (fun j ↦ r i j ≤ d p i + m - 1) := by
    ext j; simp only [B,mem_filter,mem_univ,true_and,Accept]; omega
  have hc : B.card = d p i + m - 1 := by rw [eq,card_choices p i (by omega)]
  have hnot : i ∉ B := by simp only [B,mem_filter,mem_univ,true_and,Accept,CompleteProfile.partnerRank_self]; omega
  have hsub : insert i B ⊆ (exc p i ∪ F.comp i) ∪ F.out i := by
    have hre := F.self hi
    intro j
    simp only [B,exc,comp,out,outside,mem_insert,mem_filter,mem_compl,mem_univ,true_and,mem_union]
    grind
  have h := ((card_le_card hsub).trans (card_union_le ..))
  have h' := card_union_le (exc p i) (F.comp i)
  rw [card_insert_of_notMem hnot,hc] at h
  omega

private theorem two_d {i : V} (hi : i ∈ J) : (F.comp i).card ≤ 2*d p i := by
  have hd := d_le hi
  have hsub : (J).filter (E i) ⊆ univ.filter (fun j ↦ r i j ≤ d p i) := by
    intro j hj
    exact mem_filter.mpr ⟨mem_univ _,le_d (mem_filter.mp hj).2⟩
  have h := card_le_card hsub
  rw [card_choices p i (by omega)] at h
  exact (F.size_le_twice_degree i).trans (by omega)

theorem small_size {i : V} (hi : i ∈ J) (hs : F.Small i) : (F.comp i).card = 2 := by
  have eq : F.comp i = {i,g i} := by
    ext j
    simp only [comp,mem_filter,mem_insert,mem_singleton]
    constructor
    · exact fun h ↦ F.small_component hs h.2
    · rintro (rfl|rfl)
      · exact ⟨hi,F.self hi⟩
      · exact ⟨F.g_mem hi,Or.inl (F.adj _ hi)⟩
  rw [eq]
  simp [Ne.symm (F.g_ne hi)]

private theorem row_bound (hm : 0 < m) (bad : ¬Solved p) {i : V} (hi : i ∈ J) :
    (F.outside i).card + (F.both i).card ≤ 2*(F.out i).card := by
  have hc := card_filter_add_card_filter_not (s := J) (F.Related i)
  change (F.comp i).card + (F.outside i).card = (J).card at hc
  have hsize := F.row_size hi
  have hdeg := F.two_d hi
  have hn := card_compl_add_card J
  simp only [Fintype.card_fin] at hn
  have ht := isolate_count hm bad
  have hcap := (F.row_caps hm bad hi).1
  omega

private theorem arc_balance : ∑ i ∈ J, (F.out i).card = ∑ j ∈ J, (F.incoming j).card := by
  classical
  have hout (i : V) : (F.out i).card = ∑ j ∈ J, if ¬F.Related i j ∧ A i j then 1 else 0 := by
    simp [out,outside,filter_filter,Finset.sum_boole]
  have hin (j : V) : (F.incoming j).card = ∑ i ∈ J, if ¬F.Related i j ∧ A i j then 1 else 0 := by
    simp only [incoming,outside,filter_filter,Finset.sum_boole]
    congr 1
    ext i
    simp only [mem_filter]
    have h₁ := F.symm (a := i) (b := j)
    have h₂ := F.symm (a := j) (b := i)
    tauto
  simp_rw [hout,hin]
  exact sum_comm

/-- Every row has outdegree at least its indegree. Summing over all rows
forces equality at each vertex and exhausts all cross-component pairs. -/
private theorem row_eq (hm : 0<m) (bad : ¬Solved p) {i : V} (hi : i ∈ J) :
    (F.outside i).card + (F.both i).card = 2*(F.out i).card ∧
    F.outside i ⊆ F.out i ∪ F.incoming i := by
  have localCount (j : V) : (F.out j ∪ F.incoming j).card + (F.both j).card =
      (F.out j).card + (F.incoming j).card := card_union_add_card_inter ..
  have sub (j : V) : F.out j ∪ F.incoming j ⊆ F.outside j :=
    union_subset (filter_subset ..) (filter_subset ..)
  have le (j : V) (hj : j ∈ J) : (F.incoming j).card ≤ (F.out j).card := by
    have := F.row_bound hm bad hj
    have := card_le_card (sub j)
    have := localCount j
    omega
  have h := le i hi
  have eq : (F.incoming i).card = (F.out i).card := by
    by_contra hn
    have hlt := sum_lt_sum le ⟨i,hi,lt_of_le_of_ne h hn⟩
    exact hlt.ne F.arc_balance.symm
  have hr := F.row_bound hm bad hi
  have hh := localCount i
  have hs := card_le_card (sub i)
  exact ⟨by omega, (eq_of_subset_of_card_le (sub i) (by omega)).ge⟩

theorem row_rigid (hm : 0 < m) (bad : ¬Solved p) {i : V} (hi : i ∈ J) :
    F.Small i ∧ d p i = 1 ∧ (I).card = 3 := by
  have he := (F.row_eq hm bad hi).1
  have hc := card_filter_add_card_filter_not (s := J) (F.Related i)
  change (F.comp i).card + (F.outside i).card = (J).card at hc
  have hsize := F.row_size hi
  have hdeg := F.two_d hi
  have hn := card_compl_add_card J
  simp only [Fintype.card_fin] at hn
  have ht := isolate_count hm bad
  have hcap := F.row_caps hm bad hi
  have hs : F.Small i := by
    by_contra hh
    obtain ⟨h₁,h₂⟩ := hcap.2 hh
    omega
  have h₂ := F.small_size hi hs
  have hp : 0 < d p i := rank_pos p i _
  exact ⟨hs,by omega,by omega⟩

include F in
theorem accept_iff_top (hm : 0 < m) (bad : ¬Solved p) {i : V} (hi : i ∈ J) (j : V) :
    A i j ↔ r i j ≤ m := by
  unfold Accept
  rw [(F.row_rigid hm bad hi).2.1]
  omega

include F in
theorem has_exception (hm : 0 < m) (bad : ¬Solved p) {i : V} (hi : i ∈ J) :
    ∃ w ∈ I, A i w := by
  have hem : F.both i = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    simp only [both,out,incoming,outside,mem_inter,mem_filter] at hj
    apply hj.1.1.2
    exact Or.inl ⟨(F.accept_iff_top hm bad hi j).mp hj.1.2,
      (F.accept_iff_top hm bad hj.1.1.1 i).mp hj.2.2⟩
  have he := (F.row_eq hm bad hi).1
  rw [hem,card_empty] at he
  have hc := card_filter_add_card_filter_not (s := J) (F.Related i)
  change (F.comp i).card + (F.outside i).card = (J).card at hc
  obtain ⟨hs,hd,hI⟩ := F.row_rigid hm bad hi
  have hsize := F.row_size hi
  have hn := card_compl_add_card J
  simp only [Fintype.card_fin] at hn
  have h₂ := F.small_size hi hs
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < (exc p i).card by omega)
  exact ⟨w,(mem_filter.mp hw).1,(mem_filter.mp hw).2⟩

theorem tournament (hm : 0 < m) (bad : ¬Solved p) {i j : V} (hi : i ∈ J) (hj : j ∈ J)
    (far : ¬F.Related i j) : r i j ≤ m ∨ r j i ≤ m := by
  have h := (F.row_eq hm bad hi).2 (mem_filter.mpr ⟨hj,far⟩)
  rcases mem_union.mp h with ho|hin
  · exact Or.inl ((F.accept_iff_top hm bad hi _).mp (mem_filter.mp ho).2)
  · exact Or.inr ((F.accept_iff_top hm bad hj _).mp (mem_filter.mp hin).2)

end FanelliMoscardelli.Market.Frame
