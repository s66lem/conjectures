import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Rank-score veto core distortion

The upper bound conjectured in M. August Rossi, *Regularizing the Veto Core*
(arXiv:2610.26535). Positions start at zero.
-/

noncomputable section

namespace RossiVetoCore

open Finset
open scoped BigOperators

variable {n m : ℕ}

abbrev Profile (n m : ℕ) := Fin n → Fin m ≃ Fin m

def pos (rank : Profile n m) (u : Fin n) (c : Fin m) : Fin m := rank u c

structure IsScoringVector [NeZero m] (s : Fin m → ℝ) : Prop where
  first : s 0 = 1
  nonneg : ∀ j, 0 ≤ s j
  antitone : Antitone s

def S_sum (s : Fin m → ℝ) : ℝ := ∑ j, s j

def lastPos (m : ℕ) [NeZero m] : Fin m := ⟨m - 1, by have := NeZero.pos m; omega⟩

def T_sum [NeZero m] (s : Fin m → ℝ) : ℝ := S_sum s - s (lastPos m)

def q_score (rank : Profile n m) (s : Fin m → ℝ) (c : Fin m) : ℝ :=
  (∑ u, s (rank u c)) / ((n : ℝ) * S_sum s)

abbrev Distance (n m : ℕ) := (Fin n ⊕ Fin m) → (Fin n ⊕ Fin m) → ℝ

structure IsPseudometric (d : Distance n m) : Prop where
  self : ∀ x, d x x = 0
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z

def Consistent (d : Distance n m) (rank : Profile n m) : Prop :=
  ∀ u x y, d (.inl u) (.inr x) < d (.inl u) (.inr y) →
    (pos rank u x).val < (pos rank u y).val

def InRankScoreVetoCore (rank : Profile n m) (s : Fin m → ℝ) (a : Fin m) : Prop :=
  ∀ (voters : Finset (Fin n)) (D : Finset (Fin m)), D ≠ univ →
    (∀ u ∈ voters, ∀ c ∈ D, (pos rank u c).val < (pos rank u a).val) →
    (voters.card : ℝ) / n ≤ 1 - ∑ c ∈ D, q_score rank s c

def socialCost (d : Distance n m) (c : Fin m) : ℝ := ∑ u, d (.inl u) (.inr c)

private theorem dist_nonneg {d : Distance n m} (hd : IsPseudometric d) (x y) :
    0 ≤ d x y := by
  have h := hd.triangle x y x
  rw [hd.self, hd.symm y x] at h
  linarith

private theorem weak_order {d : Distance n m} {rank : Profile n m}
    (h : Consistent d rank) {u x y} (hle : rank u x ≤ rank u y) :
    d (.inl u) (.inr x) ≤ d (.inl u) (.inr y) :=
  le_of_not_gt fun hlt => (not_lt_of_ge hle) (h u y x hlt)

/-- Consecutive gaps between levels express each value as a sum of threshold indicators. -/
private theorem layer_weights (levels : Finset ℝ) (base : ℝ)
    (hbase : ∀ t ∈ levels, base ≤ t) :
    ∃ w : ℝ → ℝ, (∀ t ∈ levels, 0 ≤ w t) ∧
      ∀ x ∈ levels, x - base = ∑ t ∈ levels, if t ≤ x then w t else 0 := by
  classical
  induction levels using Finset.induction_on_min generalizing base with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert a rest hmin ih =>
    have ha : a ∉ rest := fun h => lt_irrefl a (hmin a h)
    obtain ⟨w, hw, hx⟩ := ih a fun t ht => (hmin t ht).le
    let v := Function.update w a (a - base)
    have hv (t) (ht : t ∈ rest) : v t = w t :=
      Function.update_of_ne (hmin t ht).ne' _ _
    have hva : v a = a - base := Function.update_self ..
    refine ⟨v, ?_, ?_⟩
    · intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · rw [hva]
        exact sub_nonneg.mpr (hbase _ (mem_insert_self ..))
      · rw [hv t ht]
        exact hw t ht
    · intro x hxmem
      rw [sum_insert ha, hva]
      have heq : (∑ t ∈ rest, if t ≤ x then v t else 0) =
          ∑ t ∈ rest, if t ≤ x then w t else 0 :=
        sum_congr rfl fun t ht => by rw [hv t ht]
      rw [heq]
      rcases mem_insert.mp hxmem with rfl | ht
      · simp only [le_refl, if_true]
        rw [sum_eq_zero fun t ht => if_neg (hmin t ht).not_ge, add_zero]
      · rw [if_pos (hmin x ht).le, ← hx x ht]
        ring

/-- Finite upper-tail dominance implies dominance of the weighted sums. -/
private theorem layer_sum_le {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) (p : ι → ℝ) (q : κ → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j)
    (h : ∀ t : ℝ, (∑ i, if t ≤ x i then p i else 0) ≤
      ∑ j, if t ≤ y j then q j else 0) :
    (∑ i, p i * x i) ≤ ∑ j, q j * y j := by
  classical
  let levels := univ.image x ∪ univ.image y
  have hxmem (i) : x i ∈ levels := mem_union_left _ (mem_image_of_mem _ (mem_univ i))
  have hymem (j) : y j ∈ levels := mem_union_right _ (mem_image_of_mem _ (mem_univ j))
  obtain ⟨w, hw, heq⟩ := layer_weights levels 0 (by
    intro t ht
    rcases mem_union.mp ht with h | h
    · obtain ⟨i, _, rfl⟩ := mem_image.mp h; exact hx i
    · obtain ⟨j, _, rfl⟩ := mem_image.mp h; exact hy j)
  simp only [sub_zero] at heq
  have expand {α : Type} [Fintype α] (f g : α → ℝ) (hf : ∀ i, f i ∈ levels) :
      (∑ i, g i * f i) = ∑ t ∈ levels, (∑ i, if t ≤ f i then g i else 0) * w t := by
    calc
      _ = ∑ i, ∑ t ∈ levels, (if t ≤ f i then g i else 0) * w t := by
        apply sum_congr rfl
        intro i _
        conv_lhs => rw [heq _ (hf i), mul_sum]
        apply sum_congr rfl
        intro t _
        split_ifs <;> simp
      _ = _ := by rw [sum_comm]; simp only [sum_mul]
  rw [expand x p hxmem, expand y q hymem]
  exact sum_le_sum fun t ht => mul_le_mul_of_nonneg_right (h t) (hw t ht)

private theorem score_sum_pos [NeZero m] {s : Fin m → ℝ} (hs : IsScoringVector s) :
    0 < S_sum s := by
  have h := single_le_sum (fun j _ => hs.nonneg j) (mem_univ (0 : Fin m))
  rw [hs.first] at h
  exact zero_lt_one.trans_le h

private theorem total_score (rank : Profile n m) (s : Fin m → ℝ) :
    (∑ c, ∑ u, s (rank u c)) = (n : ℝ) * S_sum s := by
  rw [sum_comm]
  simp only [Equiv.sum_comp, S_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem core_cost_bound [NeZero m] {rank : Profile n m} {s : Fin m → ℝ}
    (hn : 0 < n) (hs : IsScoringVector s) {a : Fin m}
    (hcore : InRankScoreVetoCore rank s a) (x : Fin n → ℝ) (ρ : Fin m → ℝ)
    (hx : ∀ u, 0 ≤ x u) (hρ : ∀ c, 0 ≤ ρ c)
    (hpref : ∀ u c, rank u a ≤ rank u c → x u ≤ ρ c) :
    S_sum s * (∑ u, x u) ≤ ∑ u, ∑ c, s (rank u c) * ρ c := by
  classical
  let score (c : Fin m) := ∑ u, s (rank u c)
  have hscore (c) : 0 ≤ score c := sum_nonneg fun u _ => hs.nonneg (rank u c)
  have hS := score_sum_pos hs
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have htotal : ∑ c, score c = (n : ℝ) * S_sum s := total_score rank s
  have htail (t : ℝ) : (∑ u, if t ≤ x u then S_sum s else 0) ≤
      ∑ c, if t ≤ ρ c then score c else 0 := by
    let U := univ.filter (fun u => t ≤ x u)
    let D := univ.filter (fun c => ¬ t ≤ ρ c)
    rw [← sum_filter, ← sum_filter]
    by_cases hempty : U = ∅
    · change (∑ _ ∈ U, S_sum s) ≤ _
      rw [hempty, sum_empty]
      exact sum_nonneg fun c _ => hscore c
    obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.mpr hempty
    have htua : t ≤ ρ a := (mem_filter.mp hu).2.trans (hpref u a le_rfl)
    have hD : D ≠ univ := fun h => (mem_filter.mp (h ▸ mem_univ a : a ∈ D)).2 htua
    have hc := hcore U D hD (by
      intro v hv c hc
      exact lt_of_not_ge fun hle => (mem_filter.mp hc).2
        ((mem_filter.mp hv).2.trans (hpref v c hle)))
    have hsplit : (∑ c ∈ D, score c) + (∑ c ∈ univ.filter (fun c => t ≤ ρ c), score c) =
        (n : ℝ) * S_sum s := by
      rw [← htotal]
      simpa [D] using sum_filter_add_sum_filter_not univ (fun c => ¬ t ≤ ρ c) score
    simp only [q_score, ← sum_div] at hc
    change (U.card : ℝ) / n ≤ 1 - (∑ c ∈ D, score c) / ((n : ℝ) * S_sum s) at hc
    have hc' := (le_sub_iff_add_le.mp hc)
    field_simp [hn'.ne', hS.ne', hn', hS] at hc'
    change (∑ _ ∈ U, S_sum s) ≤ _
    rw [sum_const, nsmul_eq_mul]
    linarith
  have h := layer_sum_le x ρ (fun _ => S_sum s) score hx hρ htail
  rw [mul_sum]
  refine h.trans_eq ?_
  simp only [score, sum_mul]
  rw [sum_comm]

/-- Each voter contributes their excess cost at every position except first,
and at most twice their distance to `b` at every candidate except `b`. -/
private theorem voter_score_bound [NeZero m] (r : Fin m ≃ Fin m) {s : Fin m → ℝ}
    (hs : IsScoringVector s) (ρ : Fin m → ℝ) (b : Fin m) (x L : ℝ)
    (hx : 0 ≤ x) (hL : 0 ≤ L) (hb : ρ b = 0)
    (hfirst : ρ (r.symm 0) ≤ L) (hall : ∀ c, ρ c ≤ x + L) :
    (∑ c, s (r c) * ρ c) ≤ (S_sum s - 1) * x + T_sum s * L := by
  classical
  let f := r.symm 0
  let w (c : Fin m) := s (r c)
  have hsum : ∑ c, w c = S_sum s := r.sum_comp s
  have hpoint (c) : ρ c ≤ (if c = f then 0 else x) + (if c = b then 0 else L) := by
    by_cases hcb : c = b
    · subst c
      rw [hb]
      split_ifs <;> linarith
    · by_cases hcf : c = f
      · rw [if_neg hcb, if_pos hcf, zero_add, hcf]
        exact hfirst
      · simpa [hcf, hcb] using hall c
  have sum_except (k : Fin m) (z : ℝ) :
      (∑ c, w c * (if c = k then 0 else z)) = (S_sum s - w k) * z := by
    calc
      _ = ∑ c, (w c * z - (if c = k then w c * z else 0)) := by
        apply sum_congr rfl
        intro c _
        split_ifs <;> simp
      _ = _ := by rw [sum_sub_distrib, ← sum_mul, hsum]; simp; ring
  have hlast : s (lastPos m) ≤ w b := hs.antitone (by
    change (r b).val ≤ m - 1
    have := (r b).isLt
    omega)
  calc
    _ ≤ ∑ c, w c * ((if c = f then 0 else x) + (if c = b then 0 else L)) :=
      sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hpoint c) (hs.nonneg _)
    _ = (S_sum s - 1) * x + (S_sum s - w b) * L := by
      simp only [mul_add, sum_add_distrib, sum_except]
      simp [w, f, hs.first]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right (sub_le_sub_left hlast _) hL)

/-- Rossi's rank-score veto core distortion bound for arbitrary real scoring vectors. -/
theorem rank_score_veto_core_distortion_upper (hn : 1 ≤ n) (hm : 2 ≤ m)
    (rank : Profile n m) (s : Fin m → ℝ)
    (hs : letI : NeZero m := ⟨by omega⟩; IsScoringVector s)
    (d : Distance n m) (hd : IsPseudometric d) (hcons : Consistent d rank)
    (a b : Fin m) (hcore : InRankScoreVetoCore rank s a) :
    letI : NeZero m := ⟨by omega⟩
    socialCost d a ≤ (1 + 2 * T_sum s) * socialCost d b := by
  classical
  let inst : NeZero m := ⟨by omega⟩
  let δ := d (.inr b) (.inr a)
  let ρ (c : Fin m) := min (d (.inr b) (.inr c)) δ
  let cost (u : Fin n) (c : Fin m) := d (.inl u) (.inr c)
  let x (u : Fin n) := max 0 (cost u a - cost u b)
  have hx (u) : 0 ≤ x u := le_max_left ..
  have hx' (u) : cost u a - cost u b ≤ x u := le_max_right ..
  have hδ : 0 ≤ δ := dist_nonneg hd _ _
  have hρ (c) : 0 ≤ ρ c := le_min (dist_nonneg hd _ _) hδ
  have hb : ρ b = 0 := by simp [ρ, hd.self, min_eq_left hδ]
  have htriangle (u : Fin n) (c : Fin m) : d (.inr b) (.inr c) ≤ cost u b + cost u c := by
    simpa only [cost, hd.symm (.inr b) (.inl u)] using hd.triangle (.inr b) (.inl u) (.inr c)
  have hpref (u c) (hle : rank u a ≤ rank u c) : x u ≤ ρ c := by
    have hac : cost u a ≤ cost u c := weak_order hcons hle
    have ht (k : Fin m) : cost u k ≤ cost u b + d (.inr b) (.inr k) :=
      hd.triangle (.inl u) (.inr b) (.inr k)
    refine max_le (hρ c) (le_min ?_ ?_)
    · linarith [ht c]
    · dsimp [δ]; linarith [ht a]
  have hcoreSum := core_cost_bound hn hs hcore x ρ hx hρ hpref
  have hper (u : Fin n) : (∑ c, s (rank u c) * ρ c) ≤
      (S_sum s - 1) * x u + T_sum s * (2 * cost u b) := by
    have hcost : 0 ≤ cost u b := dist_nonneg hd _ _
    apply voter_score_bound (rank u) hs ρ b (x u) (2 * cost u b) (hx u) (by linarith) hb
    · let f := (rank u).symm 0
      have htop : cost u f ≤ cost u b := weak_order hcons (by simp [f])
      exact (min_le_left ..).trans (by linarith [htriangle u f])
    · intro c
      exact (min_le_right ..).trans (by linarith [htriangle u a, hx' u])
  have hsum := hcoreSum.trans (sum_le_sum fun u _ => hper u)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum] at hsum
  have hcostSum : socialCost d a ≤ socialCost d b + ∑ u, x u := by
    rw [socialCost, socialCost, ← sum_add_distrib]
    exact sum_le_sum fun u _ => by change cost u a ≤ cost u b + x u; linarith [hx' u]
  change (∑ u, cost u a) ≤ (1 + 2 * T_sum s) * ∑ u, cost u b
  change (∑ u, cost u a) ≤ (∑ u, cost u b) + ∑ u, x u at hcostSum
  linarith

#print axioms rank_score_veto_core_distortion_upper


private theorem sum_two_blocs (k l : ℕ) (x y : ℝ) :
    (∑ u : Fin (k + l), if u.val < k then x else y) = k * x + l * y := by
  rw [Fin.sum_univ_add]
  simp [Fin.val_castAdd, Fin.val_natAdd, nsmul_eq_mul]

/-- Lemma 5. If the nonnegative rational `T_sum s` is written as `l / k`,
two blocs of sizes `k` and `l` attain the upper bound with positive optimal cost.
Here `m + 2` ranges over all admissible candidate counts. -/
theorem rank_score_veto_core_distortion_attained (m k l : ℕ) (hk : 0 < k)
    (s : Fin (m + 2) → ℝ) (hs : IsScoringVector s)
    (hT : T_sum s = (l : ℝ) / k) :
    ∃ (rank : Profile (k + l) (m + 2)) (d : Distance (k + l) (m + 2)) (a b : Fin (m + 2)),
      IsPseudometric d ∧ Consistent d rank ∧ InRankScoreVetoCore rank s a ∧
      0 < socialCost d b ∧ (∀ c, socialCost d b ≤ socialCost d c) ∧
      socialCost d a = (1 + 2 * T_sum s) * socialCost d b := by
  classical
  let a : Fin (m + 2) := 0
  let b := Fin.last (m + 1)
  let rank : Profile (k + l) (m + 2) := fun u =>
    if u.val < k then Equiv.refl _ else finRotate _
  let location : Fin (k + l) ⊕ Fin (m + 2) → ℝ := Sum.elim
    (fun u => if u.val < k then 0 else 1) (fun c => if c = b then 1 else -1)
  let d : Distance (k + l) (m + 2) := fun x y => |location x - location y|
  have hba : b ≠ a := by
    intro h
    have := congrArg Fin.val h
    simp [b, a] at this
  have hlast : finRotate (m + 2) b = 0 := finRotate_last
  have hsecond : (finRotate (m + 2) a).val = 1 := by
    rw [show a = 0 from rfl, finRotate_apply_zero]
    exact Fin.val_one _
  have top (c : Fin (m + 2)) : finRotate _ c = 0 ↔ c = b := by
    rw [← hlast, Equiv.apply_eq_iff_eq]
  have hcost (u : Fin (k + l)) (c : Fin (m + 2)) :
      d (.inl u) (.inr c) = if u.val < k then 1 else if c = b then 0 else 2 := by
    dsimp [d, location]
    split_ifs <;> norm_num
  have hsc (c : Fin (m + 2)) :
      socialCost d c = k + l * (if c = b then 0 else 2) := by
    simp only [socialCost, hcost, sum_two_blocs, mul_one]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : 0 < ((k + l : ℕ) : ℝ) := by positivity
  have hS := score_sum_pos hs
  have hbscore : q_score rank s b = (k : ℝ) / (k + l) := by
    have hr (u : Fin (k + l)) : s (rank u b) =
        if u.val < k then s (lastPos _) else 1 := by
      by_cases h : u.val < k
      · simp [rank, h]; rfl
      · simp [rank, h, hlast, hs.first]
    have heq := (eq_div_iff hk'.ne').mp hT
    change (S_sum s - s (lastPos _)) * k = l at heq
    simp only [q_score, hr, sum_two_blocs, mul_one, Nat.cast_add]
    rw [div_eq_div_iff (mul_pos (by positivity) hS).ne' (by positivity)]
    rw [show (k : ℝ) * s (lastPos _) + l = k * S_sum s by linarith [heq]]
    ring
  refine ⟨rank, d, a, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun x => by simp [d], fun x y => abs_sub_comm _ _, fun x y z => abs_sub_le ..⟩
  · intro u c e h
    simp only [hcost] at h
    by_cases hmid : u.val < k
    · simp [hmid] at h
    · have hc : c = b := by by_contra hne; simp [hmid, hne] at h; split_ifs at h <;> linarith
      have he : e ≠ b := by rintro rfl; simp [hc] at h
      have hpos := mt (top e).mp he
      simpa [pos, rank, hmid, hc, hlast] using (Fin.pos_iff_ne_zero.mpr hpos)
  · intro V D _ hbetter
    have hVcard : (V.card : ℝ) ≤ (k + l : ℕ) := by
      exact_mod_cast (show V.card ≤ k + l by simpa using V.card_le_univ)
    rcases D.eq_empty_or_nonempty with rfl | hD
    · simpa using (div_le_one hn).2 hVcard
    rcases V.eq_empty_or_nonempty with rfl | hV
    · have htotal : ∑ c, q_score rank s c = 1 := by
        simp only [q_score, ← sum_div, total_score, div_self (mul_pos hn hS).ne']
      have hle : ∑ c ∈ D, q_score rank s c ≤ ∑ c, q_score rank s c :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun c _ _ =>
          div_nonneg (sum_nonneg fun u _ => hs.nonneg _) (mul_pos hn hS).le
      rw [htotal] at hle
      simpa using sub_nonneg.mpr hle
    have hmid (u) (hu : u ∈ V) : ¬ u.val < k := by
      intro h
      obtain ⟨c, hc⟩ := hD
      simpa [pos, rank, h, a] using hbetter u hu c hc
    obtain ⟨u, hu⟩ := hV
    have hsub : D ⊆ {b} := by
      intro c hc
      have hp := hbetter u hu c hc
      simp only [pos, rank, if_neg (hmid u hu), hsecond] at hp
      exact mem_singleton.mpr ((top c).mp (Fin.ext (by change _ = 0; omega)))
    have hDb : D = {b} := by
      obtain ⟨c, hc⟩ := hD
      have he := mem_singleton.mp (hsub hc)
      exact Subset.antisymm hsub (singleton_subset_iff.mpr (he ▸ hc))
    have hcount : (V.card : ℝ) ≤ l := by
      calc
        _ = ∑ u ∈ V, (1 : ℝ) := by simp
        _ = ∑ u ∈ V, (if u.val < k then (0 : ℝ) else 1) :=
          sum_congr rfl fun u hu => (if_neg (hmid u hu)).symm
        _ ≤ ∑ u : Fin (k + l), (if u.val < k then (0 : ℝ) else 1) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun u _ _ => by split_ifs <;> norm_num
        _ = _ := by simp [sum_two_blocs]
    rw [hDb, sum_singleton, hbscore, Nat.cast_add]
    rw [le_sub_iff_add_le, ← add_div, div_le_one (by positivity)]
    linarith
  · simpa [hsc] using hk'
  · intro c
    rw [hsc, hsc, if_pos rfl, mul_zero, add_zero]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (by split_ifs <;> norm_num))
  · rw [hsc, hsc, if_neg hba.symm, if_pos rfl, mul_zero, add_zero]
    linarith [(eq_div_iff hk'.ne').mp hT]

#print axioms rank_score_veto_core_distortion_attained

end RossiVetoCore
