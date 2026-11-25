import Conjectures.Roommates
import Conjectures.FanelliMoscardelli.Counting

/-!
# Odd-market stability threshold

A maximal mutual-top matching either admits a stable completion or forces the
isolated agents into cycles. In the latter case, local repairs and a row count
force every nontrivial component to be a mutual first-choice pair. The final
color argument below rules out this remaining case for markets of size at least seven.
-/

namespace FanelliMoscardelli
open Roommates Finset

namespace Market.Frame
variable {m : ℕ} {p : Market m} (F : Frame p)
local notation "V" => Agent m
local notation "J" => active p
local notation "I" => (active p)ᶜ
local notation "x" => mid p
local notation "g" => F.g
local notation "r" => p.partnerRank

private theorem color (hm : 0<m) (bad : ¬Solved p) {i : V} (hi : i ∈ J) :
    x i ∈ I ∧ r (x i) i ≤ m ∧ m < r (x i) (g i) ∧ r (g i) (x i) ≤ m := by
  have hg := F.g_mem hi
  obtain ⟨w,hw,ha⟩ := F.has_exception hm bad hg
  obtain ⟨_,he,h₁,h₂⟩ := F.isolate_rule hm bad hg hw ha
  rw [F.twice] at he h₁
  rw [he]
  exact ⟨hw,h₁,h₂,(F.accept_iff_top hm bad hg _).mp ha⟩

private theorem partner_colors (hm : 0<m) (bad : ¬Solved p) {i : V} (hi : i ∈ J) :
    x i ≠ x (g i) := by
  intro eq
  have h₁ := (F.color hm bad hi).2.2.1
  have h₂ := (F.color hm bad (F.g_mem hi)).2.1
  rw [eq] at h₁
  omega

/-- A top choice in a different component must have the color of the
source's partner, since otherwise the two-edge repair is stable. -/
private theorem arc_color (hm : 0<m) (bad : ¬Solved p) {i a : V} (hi : i ∈ J)
    (ha : a ∈ J) (far : ¬F.Related i a) (htop : r i a ≤ m) : x a = x (g i) := by
  by_contra hne
  have hca := F.color hm bad ha
  have hci := F.color hm bad (F.g_mem hi)
  have h₁ : r i a < r i (g i) + m := by have := rank_pos p i (g i); omega
  have h₂ : r (g a) (x a) < r (g a) a + m := by
    have := rank_pos p (g a) a
    have := hca.2.2.2
    omega
  have hh := repair_two_either F hm bad (edge_symm p (F.adj _ hi)) (F.adj _ ha)
    hca.1 far h₁ (Or.inr h₂) hne
  have hn := mem_compl.mp hci.1
  have hg := F.g_mem ha
  rcases hh with ⟨e,_⟩|⟨e,_⟩ <;> rw [e] at hn <;> contradiction

include F in
private theorem finish_odd (hm : 3 ≤ m) (bad : ¬Solved p) : False := by
  classical
  have hm' : 0 < m := by omega
  obtain ⟨i,hi⟩ := active_nonempty hm bad
  have hI := (F.row_rigid hm' bad hi).2.2
  have hcomp := F.small_size hi (F.row_rigid hm' bad hi).1
  have hn := card_compl_add_card J
  simp only [Fintype.card_fin] at hn
  have hc := card_filter_add_card_filter_not (s := J) (F.Related i)
  change (F.comp i).card + (F.outside i).card = (J).card at hc
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < (F.outside i).card by omega)
  obtain ⟨haJ,hfar⟩ := mem_filter.mp ha
  have contradiction_of_arc : ∀ z ∈ J, ∀ b ∈ J, ¬F.Related z b → r z b ≤ m → False := by
    intro z hz b hb hzb ht
    have he := F.arc_color hm' bad hz hb hzb ht
    have hgb := F.g_mem hb
    have hfar' : ¬ F.Related z (g b) := fun h ↦ hzb ((F.related_g ..).mp h)
    rcases F.tournament hm' bad hz hgb hfar' with h | h
    · have he' := F.arc_color hm' bad hz hgb hfar' h
      exact F.partner_colors hm' bad hb (he.trans he'.symm)
    · have he' := F.arc_color hm' bad hgb hz (fun hh ↦ hfar' (F.symm hh)) h
      rw [F.twice] at he'
      exact F.partner_colors hm' bad hz (he'.trans he)
  rcases F.tournament hm' bad hi haJ hfar with h | h
  · exact contradiction_of_arc i hi a haJ hfar h
  · exact contradiction_of_arc a haJ i hi (fun hh ↦ hfar (F.symm hh)) h

end Market.Frame

/-- Every complete strict profile on an odd market of size at least seven
admits an `m`-stable matching. -/
theorem stabilityThreshold_odd_le (m : ℕ) (hm : 3 ≤ m) :
    Roommates.stabilityThreshold (2 * m + 1) ≤ m := by
  apply Roommates.stabilityThreshold_le (by omega)
  intro p
  change Market.Solved p
  by_contra bad
  obtain ⟨F⟩ := Market.frame (by omega : 0 < m) bad
  exact F.finish_odd hm bad

/-- Refutes the proposed eventual equality for the stability threshold. -/
theorem not_stability_threshold_tight :
    ¬ (∃ N₀ : ℕ, 3 ≤ N₀ ∧
        ∀ N ≥ N₀, Roommates.stabilityThreshold N = (N + 1) / 2) := by
  rintro ⟨N₀, h₀, tight⟩
  have upper := stabilityThreshold_odd_le N₀ h₀
  rw [tight (2*N₀+1) (by omega)] at upper
  omega

end FanelliMoscardelli
