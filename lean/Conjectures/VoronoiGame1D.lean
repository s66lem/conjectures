import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The one-round discrete Voronoi game on the real line, with ties going to the
first player. The voter multiset retains multiplicities. -/

namespace VoronoiGame1D

noncomputable section
open scoped Classical

def minDist (X : Finset ℝ) (hX : X.Nonempty) (v : ℝ) : ℝ :=
  X.inf' hX (fun x => |v - x|)

def captures (P : Finset ℝ) (q v : ℝ) : Prop :=
  ∀ p ∈ P, |v - q| < |v - p|

theorem minDist_lt_iff (P Q : Finset ℝ) (hP : P.Nonempty) (hQ : Q.Nonempty) (v : ℝ) :
    minDist Q hQ v < minDist P hP v ↔ ∃ q ∈ Q, captures P q v := by
  unfold minDist
  rw [Finset.inf'_lt_iff]
  simp only [Finset.lt_inf'_iff, captures]

private def tally (V : Multiset ℝ) (f : ℝ → Prop) : ℕ := (V.filter f).card

def pScore (V : Multiset ℝ) (P Q : Finset ℝ) : ℕ :=
  tally V (fun v => ¬ ∃ q ∈ Q, captures P q v)

def P_wins (V : Multiset ℝ) (k ℓ : ℕ) : Prop :=
  ∃ P : Finset ℝ, P.card = k ∧ ∀ Q : Finset ℝ, Q.card = ℓ → V.card ≤ 2 * pScore V P Q

def AlwaysWins (k ℓ : ℕ) : Prop :=
  ∀ V : Multiset ℝ, 0 < V.card → P_wins V k ℓ

private theorem tally_mono {V : Multiset ℝ} {f g : ℝ → Prop} (h : ∀ v, f v → g v) :
    tally V f ≤ tally V g :=
  Multiset.card_le_card (Multiset.monotone_filter_right V h)

private theorem tally_le (V : Multiset ℝ) (f : ℝ → Prop) : tally V f ≤ V.card :=
  Multiset.card_le_card (Multiset.filter_le ..)

private theorem tally_zero {V : Multiset ℝ} {f : ℝ → Prop} (h : ∀ v ∈ V, ¬ f v) :
    tally V f = 0 := by
  simp [tally, Multiset.filter_eq_nil.mpr h]

private theorem tally_add (A B : Multiset ℝ) (f : ℝ → Prop) :
    tally (A + B) f = tally A f + tally B f := by simp [tally]

private theorem tally_union_le (V : Multiset ℝ) (f g : ℝ → Prop) :
    tally V (fun v => f v ∨ g v) ≤ tally V f + tally V g := by
  induction V using Multiset.induction_on with
  | empty => simp [tally]
  | cons v V ih =>
    by_cases hf : f v <;> by_cases hg : g v <;> simp_all [tally] <;> omega

private theorem tally_complement (V : Multiset ℝ) (f : ℝ → Prop) :
    tally V f + tally V (fun v => ¬ f v) = V.card := by
  induction V using Multiset.induction_on with
  | empty => simp [tally]
  | cons v V ih => by_cases hf : f v <;> simp_all [tally] <;> omega

private theorem response_bound (V : Multiset ℝ) (P Q : Finset ℝ) (B : ℕ)
    (h : ∀ q, tally V (captures P q) ≤ B) :
    tally V (fun v => ∃ q ∈ Q, captures P q v) ≤ Q.card * B := by
  induction Q using Finset.induction_on with
  | empty => simp [tally]
  | @insert q Q hq ih =>
    simp only [Finset.exists_mem_insert, Finset.card_insert_of_notMem hq, Nat.add_mul, one_mul]
    exact (tally_union_le ..).trans (by have := h q; omega)

private theorem captures_anti {P S : Finset ℝ} (h : P ⊆ S) {q v : ℝ} :
    captures S q v → captures P q v := fun hv p hp => hv p (h hp)

private theorem separates {P : Finset ℝ} {p q v : ℝ} (hp : p ∈ P)
    (h : (v ≤ p ∧ p ≤ q) ∨ (q ≤ p ∧ p ≤ v)) : ¬ captures P q v := by
  intro hc
  have := hc p hp
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> grind [abs_of_nonneg, abs_of_nonpos]

/-- After at most k placements, each open gap holds at most B voters.
The recursive pivot is the voter immediately following the first B entries. -/
private theorem balanced (B k : ℕ) (L : List ℝ) (hs : L.Pairwise (· ≤ ·))
    (hn : L.length < (k + 1) * (B + 1)) :
    ∃ P : Finset ℝ, P.card ≤ k ∧ ∀ q, tally L (captures P q) ≤ B := by
  induction k generalizing L with
  | zero =>
    refine ⟨∅, by simp, fun q => (tally_le ..).trans ?_⟩
    simpa using (show L.length ≤ B by simp at hn; omega)
  | succ k ih =>
    by_cases hshort : L.length ≤ B
    · exact ⟨∅, by simp, fun q => (tally_le ..).trans (by simpa using hshort)⟩
    let A := L.take B
    have ha : A.length = B := by simp [A, Nat.min_eq_left (by omega : B ≤ L.length)]
    have hsplit := L.take_append_drop B
    cases he : L.drop B with
    | nil =>
      have := List.length_drop (l := L) (i := B)
      rw [he] at this
      simp at this
      omega
    | cons p T =>
      have hL : A ++ p :: T = L := by simpa [A, he] using hsplit
      rw [← hL, List.pairwise_append, List.pairwise_cons] at hs
      obtain ⟨_, ⟨hpT, hsT⟩, hAp⟩ := hs
      have hlen := congrArg List.length hL
      simp only [List.length_append, List.length_cons, ha] at hlen
      rw [Nat.succ_add, Nat.succ_mul] at hn
      obtain ⟨S, hS, hbound⟩ := ih T hsT (by omega)
      let P := insert p S
      have hp : p ∈ P := Finset.mem_insert_self ..
      refine ⟨P, (Finset.card_insert_le ..).trans (by omega), fun q => ?_⟩
      rw [← hL]
      change tally ((A : Multiset ℝ) + ↑(p :: T)) _ ≤ B
      rw [tally_add]
      rcases le_total p q with hpq | hqp
      · have hz : tally ↑(p :: T) (captures P q) ≤ B := by
          have hz' : tally ({p} : Multiset ℝ) (captures P q) = 0 :=
            tally_zero (by intro v hv; simp only [Multiset.mem_singleton] at hv; subst v
                           exact separates hp (Or.inl ⟨le_rfl, hpq⟩))
          change tally (({p} : Multiset ℝ) + ↑T) _ ≤ B
          rw [tally_add, hz', zero_add]
          exact (tally_mono (fun _ => captures_anti (Finset.subset_insert p S))).trans (hbound q)
        have hzA : tally ↑A (captures P q) = 0 :=
          tally_zero (fun v hv => separates hp (Or.inl ⟨hAp v hv p (by simp), hpq⟩))
        omega
      · have hz : tally ↑(p :: T) (captures P q) = 0 := by
          apply tally_zero
          intro v hv
          apply separates hp (Or.inr ⟨hqp, ?_⟩)
          rcases List.mem_cons.mp hv with rfl | hv
          · exact le_rfl
          · exact hpT v hv
        have := tally_le (A : Multiset ℝ) (captures P q)
        simpa [hz, ← ha] using this

theorem alwaysWins_two_mul_sub_one (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : AlwaysWins (2 * ℓ - 1) ℓ := by
  intro V _
  let B := V.card / (2 * ℓ)
  let L := V.sort (· ≤ ·)
  have hL : (L : Multiset ℝ) = V := Multiset.sort_eq ..
  have hlen : L.length = V.card := by rw [← hL]; rfl
  have hdiv := Nat.lt_mul_div_succ V.card (show 0 < 2 * ℓ by omega)
  obtain ⟨S, hS, hb⟩ := balanced B (2 * ℓ - 1) L (Multiset.pairwise_sort ..) (by
    rw [hlen, show 2 * ℓ - 1 + 1 = 2 * ℓ by omega]; exact hdiv)
  obtain ⟨P, hSP, hP⟩ := Infinite.exists_superset_card_eq S _ hS
  refine ⟨P, hP, fun Q hQ => ?_⟩
  rw [hL] at hb
  have hw := response_bound V P Q B (fun q => (tally_mono (fun _ => captures_anti hSP)).trans (hb q))
  rw [hQ] at hw
  have hscore : tally V (fun v => ∃ q ∈ Q, captures P q v) + pScore V P Q = V.card :=
    tally_complement V _
  have hB : (2 * ℓ) * B ≤ V.card := Nat.mul_div_le .. 
  rw [Nat.mul_assoc] at hB
  omega


def powersOfTwo (n : ℕ) : Multiset ℝ := (Finset.range n).val.map (fun t => (2 : ℝ) ^ t)

@[simp] theorem card_powersOfTwo (n : ℕ) : (powersOfTwo n).card = n := by
  simp [powersOfTwo]

/-- Label a gap by its right endpoint, or by none for the rightmost gap.
Temporarily assigning an endpoint voter to the gap on its left charges that
voter and any geometric loss to the same endpoint. -/
private def rightEnd (P : Finset ℝ) (v : ℝ) : Option ℝ :=
  if h : (P.filter (v ≤ ·)).Nonempty then some ((P.filter (v ≤ ·)).min' h) else none

private theorem rightEnd_none {P : Finset ℝ} {v : ℝ} :
    rightEnd P v = none ↔ ∀ p ∈ P, p < v := by
  unfold rightEnd
  split_ifs with h
  · obtain ⟨p, hp⟩ := h
    obtain ⟨hp, hv⟩ := Finset.mem_filter.mp hp
    simp only [false_iff]
    exact fun H => (H p hp).not_ge hv
  · simp only [true_iff]
    intro p hp
    exact lt_of_not_ge (fun hv => h ⟨p, Finset.mem_filter.mpr ⟨hp, hv⟩⟩)

private theorem rightEnd_some {P : Finset ℝ} {v r : ℝ} :
    rightEnd P v = some r ↔ r ∈ P ∧ v ≤ r ∧ ∀ p ∈ P, p < r → p < v := by
  unfold rightEnd
  split_ifs with h
  · simp only [Option.some.injEq]
    let S := P.filter (v ≤ ·)
    have hm := Finset.mem_filter.mp (S.min'_mem h)
    constructor
    · rintro rfl
      refine ⟨hm.1, hm.2, fun p hp hpr => lt_of_not_ge (fun hv => ?_)⟩
      exact hpr.not_ge (S.min'_le p (Finset.mem_filter.mpr ⟨hp, hv⟩))
    · rintro ⟨hr, hv, H⟩
      exact le_antisymm (S.min'_le r (Finset.mem_filter.mpr ⟨hr, hv⟩))
        (le_of_not_gt (fun hh => (H _ hm.1 hh).not_ge hm.2))
  · simp only [false_iff]
    rintro ⟨hr, hv, _⟩
    exact h ⟨r, Finset.mem_filter.mpr ⟨hr, hv⟩⟩

private def gaps (P : Finset ℝ) : Finset (Option ℝ) := insert none (P.image some)

private theorem mem_gaps (P : Finset ℝ) (v : ℝ) : rightEnd P v ∈ gaps P := by
  cases he : rightEnd P v with
  | none => simp [gaps]
  | some r => simp [gaps, (rightEnd_some.mp he).1]

private theorem card_gaps (P : Finset ℝ) : (gaps P).card = P.card + 1 := by
  simp [gaps, Finset.card_image_of_injective _ (Option.some_injective ℝ)]

private def usable (P : Finset ℝ) : Option ℝ → ℝ → Prop
  | none, _ => True
  | some r, v => v < r ∧ (2 * v ≤ r ∨ ∀ p ∈ P, r ≤ p)

private def fiber (P : Finset ℝ) (n : ℕ) (i : Option ℝ) : Finset ℕ :=
  (Finset.range n).filter (fun t => rightEnd P (2 ^ t) = i)

private def saved (P : Finset ℝ) (n : ℕ) (i : Option ℝ) : Finset ℕ :=
  (fiber P n i).filter (fun t => usable P i (2 ^ t))

private theorem doubling {s t : ℕ} (h : s < t) : 2 * (2 : ℝ)^s ≤ 2^t := by
  calc 2 * (2 : ℝ)^s = 2^(s+1) := by rw [pow_succ, mul_comm]
       _ ≤ 2^t := pow_le_pow_right₀ (by norm_num) h

private theorem fiber_bound (P : Finset ℝ) (n : ℕ) (i : Option ℝ) :
    (fiber P n i).card ≤ (saved P n i).card + (if i = none then 0 else 1) := by
  cases i with
  | none =>
    have he : saved P n none = fiber P n none := Finset.filter_eq_self.mpr (fun _ _ => trivial)
    simp [he]
  | some r =>
    let F := fiber P n (some r)
    let bad := F.filter (fun t => ¬ usable P (some r) (2^t))
    have impossible : ∀ s ∈ bad, ∀ t ∈ bad, s < t → False := by
      intro s hs t ht hst
      obtain ⟨_, hs⟩ := Finset.mem_filter.mp hs
      obtain ⟨ht, _⟩ := Finset.mem_filter.mp ht
      have hend := (rightEnd_some.mp (Finset.mem_filter.mp ht).2).2.1
      have hd := doubling hst
      have hpos : 0 < (2 : ℝ)^s := by positivity
      exact hs ⟨by linarith, Or.inl (hd.trans hend)⟩
    have hbad : bad.card ≤ 1 := Finset.card_le_one.mpr (by
      intro s hs t ht
      rcases lt_trichotomy s t with h | h | h
      · exact (impossible _ hs _ ht h).elim
      · exact h
      · exact (impossible _ ht _ hs h).elim)
    have heq := Finset.card_filter_add_card_filter_not (s := F) (p := fun t => usable P (some r) (2^t))
    change (saved P n (some r)).card + bad.card = F.card at heq
    simpa only [Option.some_ne_none, if_false] using
      (show F.card ≤ (saved P n (some r)).card + 1 by omega)

private theorem open_gap_point (P : Finset ℝ) {i : Option ℝ} (hi : i ∈ gaps P) :
    ∃ q, rightEnd P q = i ∧ q ∉ P := by
  cases i with
  | none =>
    by_cases h : P.Nonempty
    · refine ⟨P.max' h + 1, rightEnd_none.mpr (fun p hp => ?_), ?_⟩
      · have := P.le_max' p hp; linarith
      · intro hp
        have := P.le_max' _ hp; linarith
    · simp_all [Finset.not_nonempty_iff_eq_empty, rightEnd]
  | some r =>
    have hr : r ∈ P := by simpa [gaps] using hi
    let L := P.filter (· < r)
    by_cases h : L.Nonempty
    · let m := L.max' h
      have hm : m < r := (Finset.mem_filter.mp (L.max'_mem h)).2
      have hleft : ∀ p ∈ P, p < r → p ≤ m := fun p hp hpr =>
        L.le_max' p (Finset.mem_filter.mpr ⟨hp, hpr⟩)
      refine ⟨(m+r)/2, rightEnd_some.mpr ⟨hr, by linarith, ?_⟩, ?_⟩
      · intro p hp hpr; have := hleft p hp hpr; linarith
      · intro hp; have := hleft _ hp (by linarith); linarith
    · have hmin : ∀ p ∈ P, ¬p < r := fun p hp hpr => h ⟨p, Finset.mem_filter.mpr ⟨hp, hpr⟩⟩
      exact ⟨r-1, rightEnd_some.mpr ⟨hr, by linarith, fun p hp hpr => (hmin p hp hpr).elim⟩,
        fun hp => hmin _ hp (by linarith)⟩

private theorem capture_gap (P : Finset ℝ) (n : ℕ) {i : Option ℝ} (hi : i ∈ gaps P) :
    ∃ q, rightEnd P q = i ∧ q ∉ P ∧ ∀ t ∈ saved P n i, captures P q (2^t) := by
  let S := saved P n i
  by_cases h : S.Nonempty
  · have info (t : ℕ) (ht : t ∈ S) :
        rightEnd P (2^t) = i ∧ usable P i (2^t) := by
      obtain ⟨hf, hu⟩ := Finset.mem_filter.mp ht
      exact ⟨(Finset.mem_filter.mp hf).2, hu⟩
    cases i with
    | none =>
      let s := S.min' h
      have he := (info s (S.min'_mem h)).1
      have hl := rightEnd_none.mp he
      refine ⟨2^s, he, fun hp => (hl _ hp).false, ?_⟩
      intro t ht p hp
      have hst : (2 : ℝ)^s ≤ 2^t := pow_le_pow_right₀ (by norm_num) (S.min'_le t ht)
      have hps := hl p hp
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    | some r =>
      by_cases hfirst : ∀ p ∈ P, r ≤ p
      · let s := S.max' h
        obtain ⟨he, hu⟩ := info s (S.max'_mem h)
        have hsr : (2 : ℝ)^s < r := hu.1
        refine ⟨2^s, he, fun hp => hsr.not_ge (hfirst _ hp), ?_⟩
        intro t ht p hp
        have hts : (2 : ℝ)^t ≤ 2^s := pow_le_pow_right₀ (by norm_num) (S.le_max' t ht)
        have hrp := hfirst p hp
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
      · let s := S.min' h
        obtain ⟨he, hu⟩ := info s (S.min'_mem h)
        have hsr : (2 : ℝ)^s < r := hu.1
        have hl := (rightEnd_some.mp he).2.2
        refine ⟨2^s, he, fun hp => (hl _ hp hsr).false, ?_⟩
        intro t ht p hp
        have hst : (2 : ℝ)^s ≤ 2^t := pow_le_pow_right₀ (by norm_num) (S.min'_le t ht)
        rw [abs_of_nonneg (by linarith)]
        by_cases hpr : p < r
        · have hps := hl p hp hpr
          rw [abs_of_nonneg (by linarith)]; linarith
        · have hd : 2 * (2 : ℝ)^t ≤ r := (info t ht).2.2.resolve_right hfirst
          have hpos : 0 < (2 : ℝ)^s := by positivity
          rw [abs_of_nonpos (by linarith)]; linarith
  · obtain ⟨q, he, hp⟩ := open_gap_point P hi
    exact ⟨q, he, hp, fun t ht => (h ⟨t, ht⟩).elim⟩


/-- Repeatedly selecting a maximum gives the requested number of heaviest gaps. -/
private theorem top_subset {α : Type*} (w : α → ℕ) (G : Finset α) (k : ℕ) (hk : k ≤ G.card) :
    ∃ J ⊆ G, J.card = k ∧ ∀ x ∈ G, x ∉ J → ∀ y ∈ J, w x ≤ w y := by
  induction k generalizing G with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨a, ha, hmax⟩ := G.exists_max_image w (Finset.card_pos.mp (by omega))
    obtain ⟨J, hJ, hcard, htop⟩ := ih (G.erase a) (by rw [Finset.card_erase_of_mem ha]; omega)
    have haJ : a ∉ J := fun h => Finset.notMem_erase a G (hJ h)
    refine ⟨insert a J, Finset.insert_subset ha (hJ.trans (Finset.erase_subset ..)),
      by rw [Finset.card_insert_of_notMem haJ, hcard], ?_⟩
    intro x hx hxJ y hy
    have hxa : x ≠ a := fun h => hxJ (by simp [h])
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hmax x hx
    · exact htop x (Finset.mem_erase.mpr ⟨hxa, hx⟩) (fun h => hxJ (Finset.mem_insert_of_mem h)) y hy

private theorem total_saved (P : Finset ℝ) (n : ℕ) :
    n ≤ (∑ i ∈ gaps P, (saved P n i).card) + P.card := by
  have hpartition : n = ∑ i ∈ gaps P, (fiber P n i).card := by
    simpa only [Finset.card_range, fiber] using
      (Finset.card_eq_sum_card_fiberwise (s := Finset.range n) (t := gaps P)
        (f := fun t => rightEnd P (2^t)) (fun t _ => mem_gaps P _))
  have hsum := Finset.sum_le_sum (s := gaps P) (fun i _ => fiber_bound P n i)
  rw [Finset.sum_add_distrib] at hsum
  have hcharge : (∑ i ∈ gaps P, (if i = none then 0 else 1 : ℕ)) = P.card := by
    rw [gaps, Finset.sum_insert (by simp)]
    simp only [if_true, zero_add]
    calc
      _ = ∑ _i ∈ P.image some, 1 := Finset.sum_congr rfl (by
        intro i hi
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hi
        rfl)
      _ = P.card := by simp [Finset.card_image_of_injective _ (Option.some_injective ℝ)]
  rw [hcharge, ← hpartition] at hsum
  exact hsum

private theorem filter_decision_irrel {α : Type*} (f : α → Prop) (V : Multiset α)
    (d e : DecidablePred f) : @Multiset.filter α f d V = @Multiset.filter α f e V := by
  rw [Subsingleton.elim d e]

/-- The sum a of the selected gains and the smallest selected gain d satisfy
three integer inequalities whenever P can hold a majority. -/
private theorem necessary_counts {k K ℓ n : ℕ} (hk : k ≤ K) (hℓ : 0 < ℓ)
    (hsize : ℓ ≤ K + 1) (hw : P_wins (powersOfTwo n) k ℓ) :
    ∃ a d : ℕ, ℓ * d ≤ a ∧ n ≤ K + a + (K + 1 - ℓ) * d ∧ 2 * a ≤ n := by
  obtain ⟨P₀, hP₀, hwin⟩ := hw
  obtain ⟨P, hsub, hP⟩ := Infinite.exists_superset_card_eq P₀ K (hP₀.trans_le hk)
  let G := gaps P
  let w := fun i => (saved P n i).card
  have hG : G.card = K + 1 := (card_gaps P).trans (by rw [hP])
  obtain ⟨J, hJ, hcard, htop⟩ := top_subset w G ℓ (by omega)
  obtain ⟨b, hb, hmin⟩ := J.exists_min_image w (Finset.card_pos.mp (by omega))
  let a := ∑ i ∈ J, w i
  let d := w b
  have hminSum : ℓ * d ≤ a := by simpa [hcard] using J.card_nsmul_le_sum w d hmin
  have hrest : (∑ i ∈ G \ J, w i) ≤ (K+1-ℓ)*d := by
    simpa [Finset.card_sdiff_of_subset hJ, hG, hcard] using
      (G \ J).sum_le_card_nsmul w d (fun i hi => htop i (Finset.mem_sdiff.mp hi).1
        (Finset.mem_sdiff.mp hi).2 b hb)
  have htotal := total_saved P n
  change n ≤ (∑ i ∈ G, w i) + P.card at htotal
  rw [← Finset.sum_sdiff hJ, hP] at htotal
  refine ⟨a, d, hminSum, by dsimp [a]; omega, ?_⟩
  choose q hq using fun i : G => capture_gap P n i.property
  let point (i : Option ℝ) : ℝ := if h : i ∈ G then q ⟨i, h⟩ else 0
  have hpoint (i) (hi : i ∈ J) :
      rightEnd P (point i) = i ∧ ∀ t ∈ saved P n i, captures P₀ (point i) (2^t) := by
    simpa only [point, dif_pos (hJ hi)] using
      And.intro (hq ⟨i, hJ hi⟩).1 (fun t ht => captures_anti hsub ((hq ⟨i, hJ hi⟩).2.2 t ht))
  let Q := J.image point
  have hQ : Q.card = ℓ := (Finset.card_image_of_injOn (by
    intro i hi j hj he
    exact (hpoint i hi).1.symm.trans ((congrArg (rightEnd P) he).trans (hpoint j hj).1))).trans hcard
  have hv := hwin Q hQ
  let taken := (Finset.range n).filter (fun t => ∃ q ∈ Q, captures P₀ q (2^t))
  have hresp : a ≤ taken.card := by
    have hdisj : (J : Set (Option ℝ)).PairwiseDisjoint (saved P n) := by
      intro i _ j _ hij
      apply Finset.disjoint_left.mpr
      intro t hti htj
      have hi := (Finset.mem_filter.mp (Finset.mem_filter.mp hti).1).2
      have hj := (Finset.mem_filter.mp (Finset.mem_filter.mp htj).1).2
      exact hij (hi.symm.trans hj)
    change (∑ i ∈ J, (saved P n i).card) ≤ taken.card
    rw [← Finset.card_biUnion hdisj]
    apply Finset.card_le_card
    intro t ht
    obtain ⟨i, hi, ht⟩ := Finset.mem_biUnion.mp ht
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1,
      point i, Finset.mem_image_of_mem _ hi, (hpoint i hi).2 t ht⟩
  let kept := (Finset.range n).filter (fun t => ¬ ∃ q ∈ Q, captures P₀ q (2^t))
  have hscore : pScore (powersOfTwo n) P₀ Q = kept.card := by
    unfold pScore tally powersOfTwo kept
    rw [Multiset.filter_map, Multiset.card_map, Finset.card_def, Finset.filter_val]
    apply congrArg Multiset.card
    exact filter_decision_irrel _ _ _ _
  have hpart : taken.card + kept.card = n := by
    simpa only [Finset.card_range] using Finset.card_filter_add_card_filter_not
      (s := Finset.range n) (p := fun t => ∃ q ∈ Q, captures P₀ q (2^t))
  rw [card_powersOfTwo, hscore] at hv
  omega

theorem powers_of_two_defeat (ℓ k n : ℕ) (hℓ : 2 ≤ ℓ) (_hk : 1 ≤ k)
    (hk : k ≤ 2 * ℓ - 2) (hn : 4 * ℓ * (ℓ - 1) + 1 ≤ n) :
    ¬ P_wins (powersOfTwo n) k ℓ := by
  intro hw
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show ℓ ≠ 0 by omega)
  obtain ⟨a, d, hmin, htotal, hhalf⟩ := necessary_counts (K := 2*m)
    (by omega : k ≤ 2*m) (by omega) (by omega) hw
  rw [show 2*m+1-(m+1) = m by omega] at htotal
  rw [Nat.succ_mul] at hmin
  have hd : d ≤ 2*m := by omega
  have hmd := Nat.mul_le_mul_left m hd
  simp only [Nat.succ_sub_one] at hn
  nlinarith

theorem l3_n17_counterexample : ¬ P_wins (powersOfTwo 17) 4 3 := by
  intro hw
  obtain ⟨a, d, hmin, htotal, hhalf⟩ := necessary_counts (K := 4) (by decide) (by decide) (by decide) hw
  omega

private theorem exists_winning (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ k : ℕ, 1 ≤ k ∧ AlwaysWins k ℓ :=
  ⟨2*ℓ-1, by omega, alwaysWins_two_mul_sub_one ℓ hℓ⟩

def facilityAdvantage (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : ℕ := Nat.find (exists_winning ℓ hℓ)

theorem facilityAdvantage_eq (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : facilityAdvantage ℓ hℓ = 2 * ℓ - 1 := by
  apply le_antisymm
  · exact Nat.find_min' (exists_winning ℓ hℓ) ⟨by omega, alwaysWins_two_mul_sub_one ℓ hℓ⟩
  · obtain ⟨hk, hw⟩ : 1 ≤ facilityAdvantage ℓ hℓ ∧ AlwaysWins (facilityAdvantage ℓ hℓ) ℓ :=
      Nat.find_spec (exists_winning ℓ hℓ)
    by_contra! hlt
    let n := 4 * ℓ * (ℓ-1) + 1
    exact powers_of_two_defeat ℓ _ n (by omega) hk (by omega) le_rfl
      (hw (powersOfTwo n) (by simp [n]))

theorem facilityAdvantage_ne_succ (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    facilityAdvantage ℓ (by omega) ≠ ℓ + 1 := by
  rw [facilityAdvantage_eq]; omega

theorem not_maharaj_conjecture1 : ¬ (∀ ℓ : ℕ, ∀ _ : ℓ ≥ 2,
    facilityAdvantage ℓ (by omega) = ℓ + 1) :=
  fun h => facilityAdvantage_ne_succ 3 (by decide) (h 3 (by decide))

#print axioms powers_of_two_defeat
#print axioms l3_n17_counterexample
#print axioms alwaysWins_two_mul_sub_one
#print axioms facilityAdvantage_eq
#print axioms facilityAdvantage_ne_succ
#print axioms not_maharaj_conjecture1

end
end VoronoiGame1D
