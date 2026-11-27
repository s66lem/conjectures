import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Complete Resolution of Dufour–Heubach Conjecture 1 on Slow A-Nim
# (INTEGERS 26 (2026) #G3 / arXiv:2404.06608v3)

In *On the P-positions of some infinite families of Slow A-Nim*
(INTEGERS 26 (2026), #G3, Section 6; arXiv:2404.06608v3, Conjecture 1 / `con:atleastk`),
M. Dufour and S. Heubach conjectured an explicit `(s, o)` characterization of the
P-positions of `SN(n, {k, ..., n})`.

We prove TWO results completely in Lean 4:
1. **Disproof of Conjecture 1** (`conjecture1_false_parity`, `conjecture1_false_infinite_family`):
   - At `n = 4, k = 2`, the reduced position `(0, 1, 2, 2)` is a P-position, yet
     Conjecture 1 classifies it as an N-position because its middle set requires
     `o ≡ n (mod 2)`.
   - For every odd `k ≥ 3` and `n ≥ (3k - 1) / 2`, the reduced position with
     `(3k - 1) / 2` stacks of height `2` (and the remaining stacks empty) is a
     P-position, yet Conjecture 1 classifies it as an N-position because its middle
     set requires `1 ≤ o`.
2. **Exact Corrected Characterization for All `(n, k, p)`** (`isP_iff_div_eq`,
   `isP_iff_correctedSO_of_reduced`):
   For every `n ≥ 1`, `1 ≤ k ≤ n`, and every position `p : Fin n → ℕ` (reduced or not),
   letting `p~ := reduction k p` be the playable reduction (chopping stacks at the
   maximal `t` with `k * t ≤ ∑ i, min (p i) t`), `D(q) := ∑ i, (q i + 1) / 2`, and
   `E(q) := ∑ i, q i / 2`, we prove:
     `IsP k p ↔ D (reduction k p) / k = E (reduction k p) / k`.
   For reduced positions, this is equivalent to removing both erroneous clauses from
   the middle set of Conjecture 1:
     `s ≤ 2 * k - 2 ∧ o ≤ min s (2 * k - 2 - s)` where `s = (∑ i, p i) % (2 * k)`.
-/

namespace DufourHeubachSlowANim

open scoped BigOperators

/-- Total number of tokens in a position `p : Fin n → ℕ`. -/
def total {n : ℕ} (p : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, p i

/-- Sum of ceiling halves `D(p) = ∑ ⌈p_i / 2⌉`. -/
def D {n : ℕ} (p : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, (p i + 1) / 2

/-- Sum of floor halves `E(p) = ∑ ⌊p_i / 2⌋`. -/
def E {n : ℕ} (p : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, p i / 2

/-- Number of odd stacks `o(p)`. -/
def oddCount {n : ℕ} (p : Fin n → ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin n => p i % 2 = 1).card

/-- A legal move in `SN(n, {k, ..., n})` chooses a subset `S` of at least `k`
nonempty stacks and removes one token from each stack in `S`. -/
def LegalMove {n : ℕ} (k : ℕ) (p : Fin n → ℕ) (S : Finset (Fin n)) : Prop :=
  k ≤ S.card ∧ ∀ i ∈ S, 0 < p i

/-- Resulting position after removing one token from each stack in `S`. -/
def move {n : ℕ} (p : Fin n → ℕ) (S : Finset (Fin n)) : Fin n → ℕ :=
  fun i => if i ∈ S then p i - 1 else p i

/-- Reduced (NIRB) condition: `k * p i ≤ ∑ j, p j` for every stack `i`. -/
def IsReduced {n : ℕ} (k : ℕ) (p : Fin n → ℕ) : Prop :=
  ∀ i : Fin n, k * p i ≤ total p

/-- Chopping every stack of `p` at height `t`. -/
def chop {n : ℕ} (p : Fin n → ℕ) (t : ℕ) : Fin n → ℕ :=
  fun i => min (p i) t

/-- Largest chop height `t ≤ total p` satisfying `k * t ≤ ∑ i, min (p i) t`. -/
def redHeight {n : ℕ} (k : ℕ) (p : Fin n → ℕ) : ℕ :=
  ((Finset.range (total p + 1)).filter fun t => k * t ≤ total (chop p t)).max'
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), by simp [total, chop]⟩⟩

/-- The playable reduction `p~` of a position `p` (Dufour–Heubach, Lemma 3). -/
def reduction {n : ℕ} (k : ℕ) (p : Fin n → ℕ) : Fin n → ℕ :=
  chop p (redHeight k p)

private lemma sum_ite_const_nat {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (c : ℕ) :
    (∑ i : Fin n, if P i then c else 0) = (Finset.univ.filter P).card * c := by
  rw [← Finset.sum_filter]
  exact Finset.sum_const_nat fun _ _ => rfl

private lemma card_eq_sum_ite {n : ℕ} (S : Finset (Fin n)) :
    S.card = ∑ i : Fin n, if i ∈ S then 1 else 0 := by
  rw [sum_ite_const_nat, Nat.mul_one]
  congr 1
  ext i
  simp

private lemma move_total_lt {n : ℕ} {k : ℕ} (hk : 0 < k) {p : Fin n → ℕ} {S : Finset (Fin n)}
    (hS : LegalMove k p S) : total (move p S) < total p := by
  have hle : ∀ i : Fin n, move p S i ≤ p i := by
    intro i; dsimp only [move]; split_ifs <;> omega
  obtain ⟨i0, hi0⟩ : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hk hS.1)
  have hlt : move p S i0 < p i0 := by
    have hp := hS.2 i0 hi0
    dsimp only [move]
    rw [if_pos hi0]
    omega
  exact Finset.sum_lt_sum (fun i _ => hle i) ⟨i0, Finset.mem_univ i0, hlt⟩

/-- Normal-play P-position predicate of `SN(n, {k, ..., n})`, defined by well-founded
recursion on total token count `total p` (requires `0 < k`). -/
def IsP {n : ℕ} (k : ℕ) (hk : 0 < k) (p : Fin n → ℕ) : Prop :=
  ∀ S : Finset (Fin n), LegalMove k p S → ¬ IsP k hk (move p S)
termination_by total p
decreasing_by
  exact move_total_lt hk ‹LegalMove k p S›

/-- Printed Conjecture 1 predicate of Dufour–Heubach (INTEGERS 26 (2026) #G3, Sec. 6). -/
def Conjecture1Pred {n : ℕ} (k : ℕ) (p : Fin n → ℕ) : Prop :=
  let s := total p % (2 * k)
  let o := oddCount p
  (s % 2 = o % 2 ∧ s + 1 < k ∧ o ≤ s) ∨
  (s + 1 = k ∧ o % 2 = n % 2 ∧ 1 ≤ o ∧ o + 1 ≤ k) ∨
  (s % 2 = o % 2 ∧ k ≤ s ∧ s + 1 < 2 * k ∧ o + s ≤ 2 * (k - 1))

/-- Corrected `(s, o)` predicate (removing both erroneous clauses from the middle set). -/
def CorrectedSOPred {n : ℕ} (k : ℕ) (p : Fin n → ℕ) : Prop :=
  let s := total p % (2 * k)
  let o := oddCount p
  s + 2 ≤ 2 * k ∧ o ≤ s ∧ o + s + 2 ≤ 2 * k

private lemma D_add_E {n : ℕ} (p : Fin n → ℕ) : D p + E p = total p := by
  dsimp only [D, E, total]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  omega

private lemma E_le_D {n : ℕ} (p : Fin n → ℕ) : E p ≤ D p := by
  refine Finset.sum_le_sum fun i _ => ?_
  omega

private lemma D_sub_E {n : ℕ} (p : Fin n → ℕ) : D p = E p + oddCount p := by
  dsimp only [D, E, oddCount]
  have hcard : (Finset.univ.filter fun i : Fin n => p i % 2 = 1).card =
      ∑ i : Fin n, if p i % 2 = 1 then 1 else 0 := by
    rw [sum_ite_const_nat, Nat.mul_one]
  rw [hcard, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

private lemma redHeight_spec {n : ℕ} {k : ℕ} (hk : 0 < k) (p : Fin n → ℕ) :
    k * redHeight k p ≤ total (reduction k p) ∧
    ∀ t : ℕ, k * t ≤ total (chop p t) → t ≤ redHeight k p := by
  set S := (Finset.range (total p + 1)).filter fun t => k * t ≤ total (chop p t)
  have hmem : redHeight k p ∈ S := Finset.max'_mem S _
  refine ⟨(Finset.mem_filter.mp hmem).2, fun t ht => ?_⟩
  have htle : t ≤ total p := by
    have hch : total (chop p t) ≤ total p :=
      Finset.sum_le_sum fun i _ => Nat.min_le_left _ _
    have h1 : t ≤ k * t := Nat.le_mul_of_pos_left t hk
    omega
  exact Finset.le_max' S t (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ht⟩)

private lemma reduction_isReduced {n : ℕ} {k : ℕ} (hk : 0 < k) (p : Fin n → ℕ) :
    IsReduced k (reduction k p) := by
  intro i
  have h1 := (redHeight_spec hk p).1
  have h2 : reduction k p i ≤ redHeight k p := Nat.min_le_right _ _
  exact (Nat.mul_le_mul_left k h2).trans h1

private lemma reduction_of_isReduced {n : ℕ} {k : ℕ} (hk : 0 < k) {p : Fin n → ℕ}
    (hred : IsReduced k p) : reduction k p = p := by
  ext i
  by_cases hle : p i ≤ redHeight k p
  · exact Nat.min_eq_left hle
  · exfalso
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ i⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ p hne
    have hch : chop p (p j) = p := by
      ext l; exact Nat.min_eq_left (hj l (Finset.mem_univ l))
    have hmj : p j ≤ redHeight k p := (redHeight_spec hk p).2 (p j) (by rw [hch]; exact hred j)
    have hij : p i ≤ p j := hj i (Finset.mem_univ i)
    omega

private lemma chop_succ_sum {n : ℕ} (p : Fin n → ℕ) (t : ℕ) :
    total (chop p (t + 1)) = total (chop p t) + (Finset.univ.filter fun i : Fin n => t < p i).card := by
  dsimp only [total, chop]
  have hcard : (Finset.univ.filter fun i : Fin n => t < p i).card =
      ∑ i : Fin n, if t < p i then 1 else 0 := by
    rw [sum_ite_const_nat, Nat.mul_one]
  rw [hcard, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

private lemma redHeight_succ_gt {n : ℕ} {k : ℕ} (hk : 0 < k) (p : Fin n → ℕ) :
    total (reduction k p) + (Finset.univ.filter fun i : Fin n => redHeight k p < p i).card <
      k * (redHeight k p + 1) := by
  have hnot : ¬ (k * (redHeight k p + 1) ≤ total (chop p (redHeight k p + 1))) := by
    intro hle
    have := (redHeight_spec hk p).2 (redHeight k p + 1) hle
    omega
  rw [chop_succ_sum] at hnot
  dsimp only [reduction]
  omega

private lemma high_card_lt_k {n : ℕ} {k : ℕ} (hk : 0 < k) (p : Fin n → ℕ) :
    (Finset.univ.filter fun i : Fin n => redHeight k p < p i).card < k := by
  have h1 := (redHeight_spec hk p).1
  have h2 := redHeight_succ_gt hk p
  nlinarith

private lemma redHeight_eq_zero_iff {n : ℕ} {k : ℕ} (hk : 0 < k) (p : Fin n → ℕ) :
    redHeight k p = 0 ↔ (Finset.univ.filter fun i : Fin n => 0 < p i).card < k := by
  constructor
  · intro h0
    have hlt := high_card_lt_k hk p
    simpa [h0] using hlt
  · intro hlt
    by_contra hne
    have hge1 : 1 ≤ redHeight k p := Nat.pos_of_ne_zero hne
    have hle := (redHeight_spec hk p).1
    have htot : total (chop p (redHeight k p)) ≤
        redHeight k p * (Finset.univ.filter fun i : Fin n => 0 < p i).card := by
      dsimp only [total, chop]
      have hterm : ∀ i : Fin n, min (p i) (redHeight k p) ≤
          if 0 < p i then redHeight k p else 0 := by
        intro i; split_ifs <;> omega
      calc
        ∑ i : Fin n, min (p i) (redHeight k p)
            ≤ ∑ i : Fin n, (if 0 < p i then redHeight k p else 0) :=
              Finset.sum_le_sum fun i _ => hterm i
        _ = (Finset.univ.filter fun i : Fin n => 0 < p i).card * redHeight k p :=
              sum_ite_const_nat (fun i => 0 < p i) (redHeight k p)
        _ = redHeight k p * (Finset.univ.filter fun i : Fin n => 0 < p i).card := Nat.mul_comm _ _
    have hmul : k * redHeight k p ≤
        redHeight k p * (Finset.univ.filter fun i : Fin n => 0 < p i).card :=
      hle.trans htot
    nlinarith

private lemma move_redHeight_lt {n : ℕ} {k : ℕ} (hk : 0 < k) {p : Fin n → ℕ} {S : Finset (Fin n)}
    (hS : LegalMove k p S) : redHeight k (move p S) < redHeight k p := by
  have ht_pos : 0 < redHeight k p := by
    by_contra h0
    have htz : redHeight k p = 0 := by omega
    have hlt := (redHeight_eq_zero_iff hk p).mp htz
    have hsub : S ⊆ Finset.univ.filter fun i : Fin n => 0 < p i := by
      intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hS.2 i hi⟩
    have hcard := Finset.card_le_card hsub
    have hkS := hS.1
    omega
  have hle_t : redHeight k (move p S) ≤ redHeight k p := by
    have h1 := (redHeight_spec hk (move p S)).1
    have h2 : total (chop (move p S) (redHeight k (move p S))) ≤
        total (chop p (redHeight k (move p S))) := by
      refine Finset.sum_le_sum fun i _ => ?_
      dsimp only [chop, move]; split_ifs <;> omega
    exact (redHeight_spec hk p).2 _ (h1.trans h2)
  have hne_t : redHeight k (move p S) ≠ redHeight k p := by
    intro heq
    have hvalid : k * redHeight k p ≤ total (chop (move p S) (redHeight k p)) := by
      simpa [reduction, heq] using (redHeight_spec hk (move p S)).1
    set H := Finset.univ.filter fun i : Fin n => redHeight k p < p i
    have hdrop : total (chop (move p S) (redHeight k p)) + (S \ H).card ≤
        total (chop p (redHeight k p)) := by
      have hcard : (S \ H).card = ∑ i : Fin n, if i ∈ S \ H then 1 else 0 :=
        card_eq_sum_ite (S \ H)
      dsimp only [total, chop, move]
      rw [hcard, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hiS : i ∈ S
      · by_cases hiH : i ∈ H
        · have hnot : i ∉ S \ H := by simp [hiH]
          have hgt : redHeight k p < p i := (Finset.mem_filter.mp hiH).2
          rw [if_pos hiS, if_neg hnot]; omega
        · have hmem : i ∈ S \ H := Finset.mem_sdiff.mpr ⟨hiS, hiH⟩
          have hle : p i ≤ redHeight k p := by
            have : ¬ redHeight k p < p i := fun h => hiH (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
            omega
          have hppos := hS.2 i hiS
          rw [if_pos hiS, if_pos hmem]; omega
      · have hnot : i ∉ S \ H := by simp [hiS]
        rw [if_neg hiS, if_neg hnot]; omega
    have hunion : k ≤ H.card + (S \ H).card := by
      have hsub : S ⊆ H ∪ (S \ H) := by
        intro i hi; by_cases h : i ∈ H
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, h⟩)
      calc
        k ≤ S.card := hS.1
        _ ≤ (H ∪ (S \ H)).card := Finset.card_le_card hsub
        _ ≤ H.card + (S \ H).card := Finset.card_union_le _ _
    have hgt : total (chop p (redHeight k p)) + H.card < k * (redHeight k p + 1) :=
      redHeight_succ_gt hk p
    nlinarith
  omega

private lemma reduction_move_eq {n : ℕ} {k : ℕ} (hk : 0 < k) {p : Fin n → ℕ} {S : Finset (Fin n)}
    (hS : LegalMove k p S) :
    reduction k (move p S) = reduction k (move (reduction k p) S) := by
  have ht_pos : 0 < redHeight k p := Nat.pos_of_ne_zero fun h0 => by
    have hlt := (redHeight_eq_zero_iff hk p).mp h0
    have hsub : S ⊆ Finset.univ.filter fun i : Fin n => 0 < p i := fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hS.2 i hi⟩
    have := Finset.card_le_card hsub
    have hkS := hS.1
    omega
  have hS' : LegalMove k (reduction k p) S := by
    refine ⟨hS.1, fun i hi => ?_⟩
    have hp := hS.2 i hi
    dsimp only [reduction, chop]
    omega
  have hchop_eq : ∀ s : ℕ, s < redHeight k p →
      chop (move p S) s = chop (move (reduction k p) S) s := by
    intro s hs
    ext i
    dsimp only [chop, move, reduction]
    split_ifs <;> omega
  have hlt1 : redHeight k (move p S) < redHeight k p := move_redHeight_lt hk hS
  have hred_t : redHeight k (reduction k p) = redHeight k p := by
    have h1 : k * redHeight k p ≤ total (chop (reduction k p) (redHeight k p)) := by
      have hch : chop (reduction k p) (redHeight k p) = reduction k p := by
        ext i; dsimp only [chop, reduction]; omega
      rw [hch]
      exact (redHeight_spec hk p).1
    have h2 : redHeight k (reduction k p) ≤ redHeight k p := by
      have hspec := (redHeight_spec hk (reduction k p)).1
      have hmono : total (chop (reduction k p) (redHeight k (reduction k p))) ≤
          total (chop p (redHeight k (reduction k p))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        dsimp only [chop, reduction]; omega
      exact (redHeight_spec hk p).2 _ (hspec.trans hmono)
    exact le_antisymm h2 ((redHeight_spec hk (reduction k p)).2 (redHeight k p) h1)
  have hlt2 : redHeight k (move (reduction k p) S) < redHeight k p := by
    have := move_redHeight_lt hk hS'
    rwa [hred_t] at this
  have hht_eq : redHeight k (move p S) = redHeight k (move (reduction k p) S) := by
    apply le_antisymm
    · refine (redHeight_spec hk (move (reduction k p) S)).2 _ ?_
      rw [← hchop_eq _ hlt1]
      exact (redHeight_spec hk (move p S)).1
    · refine (redHeight_spec hk (move p S)).2 _ ?_
      rw [hchop_eq _ hlt2]
      exact (redHeight_spec hk (move (reduction k p) S)).1
  dsimp only [reduction]
  rw [hht_eq]
  exact hchop_eq _ hlt2

/-- **Key Even-Below-`t` Lemma:** If every stack of `q` with height `≤ redHeight k q`
is even, then `D (reduction k q) / k = E (reduction k q) / k`. -/
private lemma div_eq_of_even_le_redHeight {n : ℕ} {k : ℕ} (hk : 0 < k) (q : Fin n → ℕ)
    (heven : ∀ i : Fin n, q i ≤ redHeight k q → q i % 2 = 0) :
    D (reduction k q) / k = E (reduction k q) / k := by
  set qt := reduction k q
  rcases Nat.even_or_odd' (redHeight k q) with ⟨r, ht | ht⟩
  · have hDE : D qt = E qt := by
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only [qt, reduction, chop]
      rw [ht]
      by_cases hle : q i ≤ 2 * r
      · have he := heven i (by omega)
        rw [Nat.min_eq_left hle]
        omega
      · rw [Nat.min_eq_right (by omega)]
        omega
    rw [hDE]
  · set H := Finset.univ.filter fun i : Fin n => redHeight k q < q i
    have hH_lt : H.card < k := high_card_lt_k hk q
    have hlow : k * (2 * r + 1) ≤ total qt := by
      have := (redHeight_spec hk q).1
      rwa [ht] at this
    have hhigh : total qt + H.card < k * (2 * r + 2) := by
      have h := redHeight_succ_gt hk q
      change total qt + H.card < k * (redHeight k q + 1) at h
      rw [ht] at h
      have hmul : k * (2 * r + 1 + 1) = k * (2 * r + 2) := by ring
      omega
    have hodd_eq : oddCount qt = H.card := by
      dsimp only [oddCount]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, H, qt, reduction, chop]
      by_cases hle : q i ≤ redHeight k q
      · have he := heven i hle
        rw [Nat.min_eq_left hle]
        omega
      · rw [Nat.min_eq_right (by omega), ht]
        omega
    have hsum : D qt + E qt = total qt := D_add_E qt
    have hdiff : D qt = E qt + H.card := by rw [D_sub_E qt, hodd_eq]
    have hleDE : E qt ≤ D qt := E_le_D qt
    have hD_lt : D qt < k * (r + 1) := by nlinarith
    have hE_ge : k * r ≤ E qt := by nlinarith
    have hD_div : D qt / k = r := by
      apply Nat.div_eq_of_lt_le <;> nlinarith
    have hE_div : E qt / k = r := by
      apply Nat.div_eq_of_lt_le <;> nlinarith
    rw [hD_div, hE_div]

/-- **Direction 1 (P → N):** From any reduced position `p` with `D p / k = E p / k`,
every legal move `q = move p S` has `D (reduction k q) / k ≠ E (reduction k q) / k`. -/
theorem step_P_to_N {n : ℕ} {k : ℕ} (hk : 0 < k) {p : Fin n → ℕ}
    (hred : IsReduced k p) (hP : D p / k = E p / k)
    {S : Finset (Fin n)} (hS : LegalMove k p S) :
    D (reduction k (move p S)) / k ≠ E (reduction k (move p S)) / k := by
  set m := E p / k
  have hEm_lo : k * m ≤ E p := by
    have := Nat.div_mul_le_self (E p) k
    rw [Nat.mul_comm]
    exact this
  have hDm_hi : D p < k * (m + 1) := by
    have h2 : D p < D p / k * k + k := Nat.lt_div_mul_add hk
    rw [hP] at h2
    nlinarith
  have hEm_hi : E p < k * (m + 1) := lt_of_le_of_lt (E_le_D p) hDm_hi
  have hp_le : ∀ i : Fin n, p i ≤ 2 * m + 1 := by
    intro i
    have h1 := hred i
    have htot : total p = D p + E p := (D_add_E p).symm
    have hlt : k * p i < k * (2 * m + 2) := by nlinarith
    have h2 : p i < 2 * m + 2 := Nat.lt_of_mul_lt_mul_left hlt
    omega
  set q := move p S
  have hEq_lt : E q < k * m := by
    have hpoint : ∀ i : Fin n, q i / 2 + (if i ∈ S then 1 else 0) ≤ (p i + 1) / 2 := by
      intro i
      dsimp only [q, move]
      split_ifs with hi
      · have hp := hS.2 i hi; omega
      · omega
    have hsum : E q + S.card ≤ D p := by
      have hcard : S.card = ∑ i : Fin n, if i ∈ S then 1 else 0 := card_eq_sum_ite S
      dsimp only [E, D]
      rw [hcard, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => hpoint i
    have hkS := hS.1
    nlinarith
  set t := redHeight k q
  set qt := reduction k q
  set H := Finset.univ.filter fun i : Fin n => t < q i
  by_cases hH_empty : H = ∅
  · have hqt_eq : qt = q := by
      ext i
      dsimp only [qt, reduction, chop]
      have hle : q i ≤ t := by
        by_contra hgt
        have hmem : i ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega⟩
        rw [hH_empty] at hmem
        exact Finset.notMem_empty i hmem
      exact Nat.min_eq_left hle
    have hDq_ge : k * m ≤ D q := by
      have hpoint : ∀ i : Fin n, p i / 2 ≤ (q i + 1) / 2 := by
        intro i; dsimp only [q, move]; split_ifs <;> omega
      exact hEm_lo.trans (Finset.sum_le_sum fun i _ => hpoint i)
    rw [hqt_eq]
    have hE_div : E q / k < m := (Nat.div_lt_iff_lt_mul hk).mpr (by nlinarith)
    have hD_div : m ≤ D q / k := (Nat.le_div_iff_mul_le hk).mpr (by nlinarith)
    omega
  · obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.mpr hH_empty
    have hi0_gt : t < q i0 := (Finset.mem_filter.mp hi0).2
    have hqi0_le : q i0 ≤ 2 * m + 1 := by
      have hle : q i0 ≤ p i0 := by dsimp only [q, move]; split_ifs <;> omega
      exact hle.trans (hp_le i0)
    have ht_le : t ≤ 2 * m := by omega
    set c := (t + 1) / 2
    have hc_le : c ≤ m := by omega
    have hH_lt : H.card < k := high_card_lt_k hk q
    have hD_ge : k * c + (k - H.card) * (m - c) ≤ D qt := by
      have hpoint : ∀ i : Fin n,
          p i / 2 + (if i ∈ H then c else 0) ≤ (qt i + 1) / 2 + (if i ∈ H then m else 0) := by
        intro i
        dsimp only [qt, reduction, chop]
        by_cases hiH : i ∈ H
        · have hgt : t < q i := (Finset.mem_filter.mp hiH).2
          have hpi := hp_le i
          rw [if_pos hiH, if_pos hiH, Nat.min_eq_right (by omega)]
          omega
        · have hle : q i ≤ t := by
            have : ¬ t < q i := fun h => hiH (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
            omega
          rw [if_neg hiH, if_neg hiH, Nat.min_eq_left hle]
          dsimp only [q, move]; split_ifs <;> omega
      have hsum : E p + H.card * c ≤ D qt + H.card * m := by
        have hHc : H.card * c = ∑ i : Fin n, if i ∈ H then c else 0 := by
          rw [sum_ite_const_nat]; congr 2; ext i; simp
        have hHm : H.card * m = ∑ i : Fin n, if i ∈ H then m else 0 := by
          rw [sum_ite_const_nat]; congr 2; ext i; simp
        dsimp only [E, D]
        rw [hHc, hHm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => hpoint i
      have hmul : (k - H.card) * (m - c) + H.card * m + k * c = k * m + H.card * c := by
        zify [le_of_lt hH_lt, hc_le]
        ring
      omega
    have hE_lt : E qt < k * c := by
      by_cases hcm : c = m
      · have hle : E qt ≤ E q := by
          refine Finset.sum_le_sum fun i _ => ?_
          dsimp only [qt, reduction, chop]
          exact Nat.div_le_div_right (Nat.min_le_left _ _)
        rw [hcm]
        exact lt_of_le_of_lt hle hEq_lt
      · have hcm1 : c + 1 ≤ m := by omega
        have hhigh : total qt + H.card < k * (t + 1) := redHeight_succ_gt hk q
        have hsum : D qt + E qt = total qt := D_add_E qt
        have ht2c : t ≤ 2 * c := by omega
        have h1 : D qt + E qt + H.card < k * (2 * c + 1) := by
          have : k * (t + 1) ≤ k * (2 * c + 1) := Nat.mul_le_mul_left k (by omega)
          omega
        have h2 : k - H.card ≤ (k - H.card) * (m - c) := by
          have hpos : 1 ≤ m - c := by omega
          nlinarith
        have hHk : (k - H.card) + H.card = k := Nat.sub_add_cancel (le_of_lt hH_lt)
        have hkc : k * (2 * c + 1) = k * c + k * c + k := by ring
        omega
    have hD_ge_kc : k * c ≤ D qt := by omega
    have hE_div : E qt / k < c := (Nat.div_lt_iff_lt_mul hk).mpr (by nlinarith)
    have hD_div : c ≤ D qt / k := (Nat.le_div_iff_mul_le hk).mpr (by nlinarith)
    omega

/-- **Direction 2 (N → P):** From any reduced position `p` with `D p / k ≠ E p / k`,
there exists a legal move `S` such that `D (reduction k (move p S)) / k = E (reduction k (move p S)) / k`. -/
theorem step_N_to_P {n : ℕ} {k : ℕ} (hk : 0 < k) {p : Fin n → ℕ}
    (hred : IsReduced k p) (hN : D p / k ≠ E p / k) :
    ∃ S : Finset (Fin n), LegalMove k p S ∧
      D (reduction k (move p S)) / k = E (reduction k (move p S)) / k := by
  set O := Finset.univ.filter fun i : Fin n => p i % 2 = 1
  by_cases hOk : k ≤ O.card
  · have hleg : LegalMove k p O := by
      refine ⟨hOk, fun i hi => ?_⟩
      have hmod := (Finset.mem_filter.mp hi).2
      omega
    refine ⟨O, hleg, div_eq_of_even_le_redHeight hk (move p O) fun i _ => ?_⟩
    dsimp only [move]
    by_cases hi : i ∈ O
    · have hmod := (Finset.mem_filter.mp hi).2
      rw [if_pos hi]; omega
    · have hmod : p i % 2 ≠ 1 := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
      rw [if_neg hi]; omega
  · have hO_lt : O.card < k := by omega
    set m := E p / k
    have hD_eq : D p = E p + O.card := D_sub_E p
    have hEm_lo : k * m ≤ E p := by
      have := Nat.div_mul_le_self (E p) k
      rw [Nat.mul_comm]
      exact this
    have hEm_hi : E p < k * (m + 1) := by
      have hlt := Nat.lt_div_mul_add (a := E p) hk
      have hmul : k * (m + 1) = E p / k * k + k := by dsimp only [m]; ring
      omega
    have hDm_lo : k * (m + 1) ≤ D p := by
      by_contra hlt
      have hdiv : D p / k = m := by
        apply Nat.div_eq_of_lt_le
        · have := E_le_D p; nlinarith
        · nlinarith
      exact hN hdiv
    have htot_pos : 0 < total p := by
      have := D_add_E p
      have : k ≤ D p := by nlinarith
      omega
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have : total p = 0 := by simp [total, hempty]
      omega
    obtain ⟨imax, _, himax⟩ := Finset.exists_max_image Finset.univ p hne
    set M := p imax
    have hM_pos : 0 < M := by
      by_contra h0
      have hMz : M = 0 := by omega
      have : total p = 0 := Finset.sum_eq_zero fun i _ => by
        have := himax i (Finset.mem_univ i); omega
      omega
    set NZ := Finset.univ.filter fun i : Fin n => 0 < p i
    have hNZ_ge : k ≤ NZ.card := by
      have hsum_le : total p ≤ NZ.card * M := by
        dsimp only [total]
        calc
          ∑ i : Fin n, p i ≤ ∑ i : Fin n, (if 0 < p i then M else 0) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have := himax i (Finset.mem_univ i)
            split_ifs <;> omega
          _ = NZ.card * M := sum_ite_const_nat (fun i => 0 < p i) M
      have hkm : k * M ≤ total p := hred imax
      nlinarith
    set MaxS := Finset.univ.filter fun i : Fin n => p i = M
    set S0 := O ∪ MaxS
    have hS0_sub : S0 ⊆ NZ := by
      intro i hi
      simp only [NZ, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_union.mp hi with hO | hMax
      · have := (Finset.mem_filter.mp hO).2; omega
      · have := (Finset.mem_filter.mp hMax).2; omega
    have hDE_move : ∀ S : Finset (Fin n), O ⊆ S → S ⊆ NZ →
        D (move p S) = E p ∧ E (move p S) + (S.card - O.card) = E p := by
      intro S hOS hSNZ
      have hD_mv : D (move p S) = E p := by
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [move]
        by_cases hiS : i ∈ S
        · rw [if_pos hiS]
          have hp := (Finset.mem_filter.mp (hSNZ hiS)).2
          omega
        · rw [if_neg hiS]
          have hnotO : i ∉ O := fun h => hiS (hOS h)
          have hmod : p i % 2 ≠ 1 := fun h => hnotO (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
          omega
      have hE_mv : E (move p S) + (S \ O).card = E p := by
        have hcard : (S \ O).card = ∑ i : Fin n, if i ∈ S \ O then 1 else 0 :=
          card_eq_sum_ite (S \ O)
        dsimp only [E]
        rw [hcard, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [move]
        by_cases hiS : i ∈ S
        · have hp := (Finset.mem_filter.mp (hSNZ hiS)).2
          by_cases hiO : i ∈ O
          · have hmod := (Finset.mem_filter.mp hiO).2
            have hnot : i ∉ S \ O := by simp [hiO]
            rw [if_pos hiS, if_neg hnot]; omega
          · have hmod : p i % 2 ≠ 1 := fun h => hiO (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
            have hmem : i ∈ S \ O := Finset.mem_sdiff.mpr ⟨hiS, hiO⟩
            rw [if_pos hiS, if_pos hmem]; omega
        · have hnot : i ∉ S \ O := by simp [hiS]
          rw [if_neg hiS, if_neg hnot]; omega
      rw [Finset.card_sdiff_of_subset hOS] at hE_mv
      exact ⟨hD_mv, hE_mv⟩
    by_cases hS0_le : S0.card ≤ k
    · have hrem : k - S0.card ≤ (NZ \ S0).card := by
        rw [Finset.card_sdiff_of_subset hS0_sub]; omega
      obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hrem
      set S := S0 ∪ T
      have hdisj : Disjoint S0 T := Finset.disjoint_sdiff.mono_right hT_sub
      have hS_card : S.card = k := by
        rw [Finset.card_union_of_disjoint hdisj, hT_card]; omega
      have hS_sub : S ⊆ NZ := Finset.union_subset hS0_sub (hT_sub.trans Finset.sdiff_subset)
      have hleg : LegalMove k p S :=
        ⟨by omega, fun i hi => (Finset.mem_filter.mp (hS_sub hi)).2⟩
      have hOS : O ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
      obtain ⟨hD_mv, hE_mv⟩ := hDE_move S hOS hS_sub
      have hq_red : IsReduced k (move p S) := by
        intro i
        have htot_mv : total (move p S) = total p - k := by
          have h1 := D_add_E (move p S)
          have h2 := D_add_E p
          omega
        have hqi : move p S i ≤ M - 1 := by
          have hle := himax i (Finset.mem_univ i)
          dsimp only [move]
          by_cases hiM : p i = M
          · have hiS : i ∈ S :=
              Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiM⟩))
            rw [if_pos hiS]; omega
          · split_ifs <;> omega
        have hkm : k * M ≤ total p := hred imax
        have hkm_sub : k * (M - 1) + k = k * M := by
          have hM1 : M - 1 + 1 = M := by omega
          calc
            k * (M - 1) + k = k * (M - 1 + 1) := by ring
            _ = k * M := by rw [hM1]
        have hle1 : k * (M - 1) ≤ total p - k := by omega
        exact (Nat.mul_le_mul_left k hqi).trans (by rw [htot_mv]; exact hle1)
      refine ⟨S, hleg, ?_⟩
      rw [reduction_of_isReduced hk hq_red]
      have hsub : (S.card - O.card) + O.card = k := by omega
      have hkm1 : k * (m + 1) = k * m + k := by ring
      have hE_ge : k * m ≤ E (move p S) := by omega
      have hE_lt : E (move p S) < k * (m + 1) := by omega
      have hD_div : D (move p S) / k = m := by rw [hD_mv]
      have hE_div : E (move p S) / k = m := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm]; exact hE_ge
        · rw [Nat.mul_comm]; exact hE_lt
      rw [hD_div, hE_div]
    · have hM_even : M % 2 = 0 := by
        by_contra hodd
        have hMax_sub : MaxS ⊆ O := by
          intro i hi
          have heq := (Finset.mem_filter.mp hi).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega⟩
        have hS0_eq : S0 = O := Finset.union_eq_left.mpr hMax_sub
        rw [hS0_eq] at hS0_le
        omega
      set r := M / 2
      have hM_eq : M = 2 * r := by omega
      have hr_le : r ≤ m + 1 := by
        have hkm : k * (2 * r) ≤ total p := by rw [← hM_eq]; exact hred imax
        have htot : total p = D p + E p := (D_add_E p).symm
        have hlt : k * (2 * r) < k * (2 * m + 4) := by nlinarith
        have h2r : 2 * r < 2 * m + 4 := Nat.lt_of_mul_lt_mul_left hlt
        omega
      by_cases hrm : r ≤ m
      · have hdisjOM : Disjoint O MaxS := by
          rw [Finset.disjoint_left]
          intro i hiO hiM
          have h1 := (Finset.mem_filter.mp hiO).2
          have h2 := (Finset.mem_filter.mp hiM).2
          omega
        have hMax_ge : k - O.card ≤ MaxS.card := by
          have : S0.card = O.card + MaxS.card := Finset.card_union_of_disjoint hdisjOM
          omega
        obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hMax_ge
        set S := O ∪ T
        have hdisjOT : Disjoint O T := hdisjOM.mono_right hT_sub
        have hS_card : S.card = k := by
          rw [Finset.card_union_of_disjoint hdisjOT, hT_card]; omega
        have hS_sub : S ⊆ NZ := Finset.union_subset
          (Finset.subset_union_left.trans hS0_sub)
          (hT_sub.trans (Finset.subset_union_right.trans hS0_sub))
        have hleg : LegalMove k p S :=
          ⟨by omega, fun i hi => (Finset.mem_filter.mp (hS_sub hi)).2⟩
        obtain ⟨hD_mv, hE_mv⟩ := hDE_move S Finset.subset_union_left hS_sub
        have hsub : (S.card - O.card) + O.card = k := by omega
        have hkm1 : k * (m + 1) = k * m + k := by ring
        have hE_ge : k * m ≤ E (move p S) := by omega
        have hq_red : IsReduced k (move p S) := by
          intro i
          have hqi : move p S i ≤ 2 * m := by
            have h1 : move p S i ≤ p i := by dsimp only [move]; split_ifs <;> omega
            have h2 : p i ≤ 2 * r := by rw [← hM_eq]; exact himax i (Finset.mem_univ i)
            omega
          have htot : total (move p S) = D (move p S) + E (move p S) := (D_add_E _).symm
          have h2km_eq : k * (2 * m) = k * m + k * m := by ring
          have h2km : k * (2 * m) ≤ total (move p S) := by omega
          exact (Nat.mul_le_mul_left k hqi).trans h2km
        refine ⟨S, hleg, ?_⟩
        rw [reduction_of_isReduced hk hq_red]
        have hD_div : D (move p S) / k = m := by rw [hD_mv]
        have hE_lt : E (move p S) < k * (m + 1) := by omega
        have hE_div : E (move p S) / k = m :=
          Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hE_ge) (by rw [Nat.mul_comm]; exact hE_lt)
        rw [hD_div, hE_div]
      · have hr_eq : r = m + 1 := by omega
        have hM2 : M = 2 * m + 2 := by omega
        have hleg : LegalMove k p S0 :=
          ⟨by omega, fun i hi => (Finset.mem_filter.mp (hS0_sub hi)).2⟩
        refine ⟨S0, hleg, ?_⟩
        set q := move p S0
        obtain ⟨hD_mv, hE_mv⟩ := hDE_move S0 Finset.subset_union_left hS0_sub
        change D q = E p at hD_mv
        change E q + (S0.card - O.card) = E p at hE_mv
        by_cases hq_red : IsReduced k q
        · rw [reduction_of_isReduced hk hq_red]
          have hq_max : q imax = 2 * m + 1 := by
            have himax_mem : imax ∈ S0 :=
              Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ imax, rfl⟩)
            dsimp only [q, move]
            rw [if_pos himax_mem]; omega
          have htot_ge : k * (2 * m + 1) ≤ total q := by
            have := hq_red imax; rwa [hq_max] at this
          have hsum := D_add_E q
          have hE_ge : k * m ≤ E q := by
            have h1 : k * (2 * m + 1) = k * (m + 1) + k * m := by ring
            omega
          have hE_lt : E q < k * (m + 1) := by omega
          have hD_div : D q / k = m := by rw [hD_mv]
          have hE_div : E q / k = m :=
            Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hE_ge) (by rw [Nat.mul_comm]; exact hE_lt)
          rw [hD_div, hE_div]
        · have ht_le : redHeight k q ≤ 2 * m := by
            by_contra hgt
            apply hq_red
            intro i
            have hqi : q i ≤ 2 * m + 1 := by
              have hle := himax i (Finset.mem_univ i)
              dsimp only [q, move]
              by_cases hiM : p i = M
              · have hiS : i ∈ S0 :=
                  Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiM⟩)
                rw [if_pos hiS]; omega
              · split_ifs <;> omega
            have h1 := (redHeight_spec hk q).1
            have hch_le : total (reduction k q) ≤ total q :=
              Finset.sum_le_sum fun j _ => Nat.min_le_left _ _
            have h2 : k * q i ≤ k * redHeight k q := Nat.mul_le_mul_left k (by omega)
            exact h2.trans (h1.trans hch_le)
          refine div_eq_of_even_le_redHeight hk q fun i hqi_le => ?_
          have hle2m : q i ≤ 2 * m := hqi_le.trans ht_le
          dsimp only [q, move] at hle2m ⊢
          by_cases hiO : i ∈ O
          · have hiS : i ∈ S0 := Finset.mem_union_left _ hiO
            have hmod := (Finset.mem_filter.mp hiO).2
            rw [if_pos hiS]; omega
          · by_cases hiM : i ∈ MaxS
            · have hiS : i ∈ S0 := Finset.mem_union_right _ hiM
              have heq := (Finset.mem_filter.mp hiM).2
              exfalso
              rw [if_pos hiS] at hle2m
              omega
            · have hnotS : i ∉ S0 := fun h => by
                rcases Finset.mem_union.mp h with h1 | h2
                · exact hiO h1
                · exact hiM h2
              have hmod : p i % 2 ≠ 1 := fun h => hiO (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
              rw [if_neg hnotS]; omega

/-- **Main Characterization Theorem (Exact Resolution of Dufour–Heubach Conjecture 1):**
For every `n : ℕ`, every `k > 0`, and every position `p : Fin n → ℕ` (reduced or not),
`p` is a P-position of `SN(n, {k, ..., n})` if and only if its playable reduction
`p~ = reduction k p` satisfies `D(p~) / k = E(p~) / k`. -/
theorem isP_iff_div_eq {n : ℕ} {k : ℕ} (hk : 0 < k) (p : Fin n → ℕ) :
    IsP k hk p ↔ D (reduction k p) / k = E (reduction k p) / k := by
  induction hN : total p using Nat.strong_induction_on generalizing p with
  | h N ih =>
    subst hN
    rw [IsP]
    constructor
    · intro hP
      by_contra hne
      have hred := reduction_isReduced hk p
      obtain ⟨S, hS_red, hS_eq⟩ := step_N_to_P hk hred hne
      have hS_p : LegalMove k p S := by
        refine ⟨hS_red.1, fun i hi => ?_⟩
        have hpos := hS_red.2 i hi
        dsimp only [reduction, chop] at hpos
        omega
      have hlt : total (move p S) < total p := move_total_lt hk hS_p
      have hmove_P : IsP k hk (move p S) := by
        rw [ih _ hlt (move p S) rfl, reduction_move_eq hk hS_p]
        exact hS_eq
      exact hP S hS_p hmove_P
    · intro hEq S hS_p
      have hS_red : LegalMove k (reduction k p) S := by
        have ht_pos : 0 < redHeight k p := by
          by_contra h0
          have hlt := (redHeight_eq_zero_iff hk p).mp (by omega)
          have hsub : S ⊆ Finset.univ.filter fun i : Fin n => 0 < p i := fun i hi =>
            Finset.mem_filter.mpr ⟨Finset.mem_univ i, hS_p.2 i hi⟩
          have := Finset.card_le_card hsub
          have hkS := hS_p.1
          omega
        refine ⟨hS_p.1, fun i hi => ?_⟩
        have hpos := hS_p.2 i hi
        dsimp only [reduction, chop]
        omega
      have hne := step_P_to_N hk (reduction_isReduced hk p) hEq hS_red
      rw [← reduction_move_eq hk hS_p] at hne
      have hlt : total (move p S) < total p := move_total_lt hk hS_p
      rw [ih _ hlt (move p S) rfl]
      exact hne

/-- Equivalence between `D p / k = E p / k` and the corrected `(s, o)` predicate. -/
theorem div_eq_iff_correctedSO {n : ℕ} {k : ℕ} (hk : 0 < k) (p : Fin n → ℕ) :
    D p / k = E p / k ↔ CorrectedSOPred k p := by
  dsimp only [CorrectedSOPred]
  have hsum : D p + E p = total p := D_add_E p
  have hdiff : D p = E p + oddCount p := D_sub_E p
  set q := E p / k
  set r := E p % k
  have hEr : E p = k * q + r := (Nat.div_add_mod (E p) k).symm
  have hr_lt : r < k := Nat.mod_lt (E p) hk
  constructor
  · intro hdiv
    have hD_lt : D p < k * (q + 1) := by
      have := Nat.lt_div_mul_add (a := D p) hk
      rw [hdiv] at this
      nlinarith
    have ho_lt : r + oddCount p < k := by nlinarith
    have htot_eq : total p = (2 * k) * q + (2 * r + oddCount p) := by nlinarith
    have hrem_lt : 2 * r + oddCount p < 2 * k := by omega
    have hs_eq : total p % (2 * k) = 2 * r + oddCount p := by
      rw [htot_eq, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hrem_lt
    rw [hs_eq]
    omega
  · rintro ⟨hs1, hs2, hs3⟩
    set s := total p % (2 * k)
    set t := total p / (2 * k)
    have htot : total p = 2 * k * t + s := (Nat.div_add_mod (total p) (2 * k)).symm
    have h2E : 2 * E p + oddCount p = 2 * k * t + s := by omega
    have hE_ge : k * t ≤ E p := by nlinarith
    have hD_lt : D p < k * (t + 1) := by nlinarith
    have hleDE : E p ≤ D p := E_le_D p
    have hD_div : D p / k = t := by
      apply Nat.div_eq_of_lt_le <;> nlinarith
    have hE_div : E p / k = t := by
      apply Nat.div_eq_of_lt_le <;> nlinarith
    exact hD_div.trans hE_div.symm

/-- For every reduced position, `IsP` is equivalent to the corrected `(s, o)` predicate. -/
theorem isP_iff_correctedSO_of_reduced {n : ℕ} {k : ℕ} (hk : 0 < k) {p : Fin n → ℕ}
    (hred : IsReduced k p) :
    IsP k hk p ↔ CorrectedSOPred k p := by
  rw [isP_iff_div_eq hk p, reduction_of_isReduced hk hred, div_eq_iff_correctedSO hk p]

/-- **Disproof 1 (Parity Clause Failure):** For `n = 4, k = 2`, the position `(0, 1, 2, 2)`
is reduced and a genuine P-position of `SN(4, {2, 3, 4})`, yet Dufour–Heubach Conjecture 1
classifies it as an N-position. -/
theorem conjecture1_false_parity :
    let p : Fin 4 → ℕ := ![0, 1, 2, 2]
    IsReduced 2 p ∧ IsP 2 (by decide) p ∧ ¬ Conjecture1Pred 2 p := by
  intro p
  have htot : total p = 5 := by decide
  have hD : D p = 3 := by decide
  have hE : E p = 2 := by decide
  have ho : oddCount p = 1 := by decide
  have hred : IsReduced 2 p := by
    intro i; fin_cases i <;> simp [p, htot]
  refine ⟨hred, ?_, ?_⟩
  · rw [isP_iff_div_eq (by decide) p, reduction_of_isReduced (by decide) hred, hD, hE]
  · simp only [Conjecture1Pred, htot, ho]
    omega

/-- **Disproof 2 (Infinite Family Breaking `1 ≤ o`):** For every odd `k ≥ 3` and every
`n ≥ (3k - 1) / 2`, the position with `(3k - 1) / 2` stacks of height `2` and the rest
empty is reduced and a genuine P-position of `SN(n, {k, ..., n})`, yet Conjecture 1
classifies it as an N-position. -/
theorem conjecture1_false_infinite_family {k n : ℕ} (hk3 : 3 ≤ k) (hk_odd : k % 2 = 1)
    (hn : (3 * k - 1) / 2 ≤ n) :
    let r := (3 * k - 1) / 2
    let p : Fin n → ℕ := fun i => if i.val < r then 2 else 0
    IsReduced k p ∧ IsP k (by omega) p ∧ ¬ Conjecture1Pred k p := by
  intro r p
  have hr2 : 2 * r = 3 * k - 1 := by omega
  have hcard : (Finset.univ.filter fun i : Fin n => i.val < r).card = r := by
    have hbij : (Finset.univ.filter fun i : Fin n => i.val < r).card =
        (Finset.range r).card := by
      refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
      · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · intro i _ j _ h; exact Fin.ext h
      · intro m hm
        have hmr : m < r := Finset.mem_range.mp hm
        exact ⟨⟨m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmr⟩, rfl⟩
    simpa using hbij
  have htot : total p = 3 * k - 1 := by
    dsimp only [total, p]
    rw [sum_ite_const_nat, hcard]
    omega
  have hD : D p = r := by
    dsimp only [D, p]
    have hterm : ∀ i : Fin n, ((if i.val < r then 2 else 0) + 1) / 2 = if i.val < r then 1 else 0 := by
      intro i; split_ifs <;> omega
    simp_rw [hterm]
    rw [sum_ite_const_nat, Nat.mul_one, hcard]
  have hE : E p = r := by
    dsimp only [E, p]
    have hterm : ∀ i : Fin n, (if i.val < r then 2 else 0) / 2 = if i.val < r then 1 else 0 := by
      intro i; split_ifs <;> omega
    simp_rw [hterm]
    rw [sum_ite_const_nat, Nat.mul_one, hcard]
  have ho : oddCount p = 0 := by
    dsimp only [oddCount, p]
    have hempty : (Finset.univ.filter fun i : Fin n => (if i.val < r then 2 else 0) % 2 = 1) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      by_cases h : i.val < r <;> simp [h]
    rw [hempty, Finset.card_empty]
  have hred : IsReduced k p := by
    intro i
    rw [htot]
    dsimp only [p]
    split_ifs
    · omega
    · simp
  refine ⟨hred, ?_, ?_⟩
  · rw [isP_iff_div_eq (by omega) p, reduction_of_isReduced (by omega) hred, hD, hE]
  · simp only [Conjecture1Pred, htot, ho]
    have hmod : (3 * k - 1) % (2 * k) = k - 1 := by
      have heq : 3 * k - 1 = 2 * k * 1 + (k - 1) := by omega
      rw [heq, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega

end DufourHeubachSlowANim
