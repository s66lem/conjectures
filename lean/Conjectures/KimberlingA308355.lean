import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Resolution of the OEIS A308355 and A025065 Conjectures (Kimberling, 2019)

OEIS A128628 lists, in row `n ≥ 1`, the number of parts of every integer partition of `n`,
ordered in descending lexicographic order of weakly decreasing part tuples (OEIS A080577).
OEIS A308355 is the limiting row sequence of A128628 as `n → ∞`.
OEIS A025065 counts palindromic partitions of `n` (partitions whose parts can be permuted
into a palindrome).

- **OEIS A308355 Conjecture** (displayed on A308355): claims the length of the maximal initial
  segment of A308355 identical to row `n` of A128628 is `A025065(n + 1)` for `n ≥ 1`.
  We **disprove** this for every odd `n ≥ 1` (e.g., at `n = 5`, the exact agreement is `4`,
  while `A025065(6) = 7`; at `n = 1`, `1` vs `2`; at `n = 3`, `2` vs `4`) and prove it holds
  if and only if `n` is even.
- **OEIS A025065 Conjecture** (Clark Kimberling, May 24, 2019): proves that the exact maximal
  common prefix length of row `n` of A128628 and the limiting sequence A308355 is `A025065(n)`
  for every `n ≥ 1`.
-/

namespace KimberlingA308355

/-! ## Section 1: Partitions in Descending Lexicographic Order (OEIS A080577 / A128628) -/

/-- All weakly decreasing partitions of `total` with every part `≤ cap`, in descending
lexicographic order. -/
def partitionsCap : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | _ + 1, 0 => []
  | n + 1, c + 1 =>
      if _h : c + 1 ≤ n + 1 then
        (partitionsCap (n + 1 - (c + 1)) (c + 1)).map ((c + 1) :: ·) ++
          partitionsCap (n + 1) c
      else
        partitionsCap (n + 1) c
termination_by n c => n + c
decreasing_by all_goals omega

/-- All partitions of `n` in descending lexicographic order. -/
def partitions (n : ℕ) : List (List ℕ) :=
  partitionsCap n n

/-- Row `n` of OEIS A128628: part counts of all partitions of `n` in descending lex order. -/
def rowA128628 (n : ℕ) : List ℕ :=
  (partitions n).map List.length

/-- Unrestricted `r`-th block `B(r)` of the limiting sequence A308355. -/
def block (r : ℕ) : List ℕ :=
  (partitions r).map (fun t => t.length + 1)

/-- Concatenation of blocks `B(0), ..., B(R)`. -/
def limitPrefix (R : ℕ) : List ℕ :=
  (List.range (R + 1)).flatMap block

/-- A valid partition of `n` with parts bounded by `c`: positive, weakly decreasing, sum `n`. -/
def IsValidPart (n c : ℕ) (l : List ℕ) : Prop :=
  (∀ x ∈ l, 0 < x ∧ x ≤ c) ∧ l.Pairwise (· ≥ ·) ∧ l.sum = n

lemma partitionsCap_zero (c : ℕ) : partitionsCap 0 c = [[]] := by
  cases c <;> simp [partitionsCap]

lemma partitionsCap_succ_zero (n : ℕ) : partitionsCap (n + 1) 0 = [] := by
  simp [partitionsCap]

lemma partitionsCap_eq_of_le {n c : ℕ} (h : n ≤ c) :
    partitionsCap n c = partitionsCap n n := by
  induction c with
  | zero =>
      have hn : n = 0 := by omega
      subst hn; rfl
  | succ c ih =>
      rcases eq_or_lt_of_le h with rfl | hlt
      · rfl
      · cases n with
        | zero => simp [partitionsCap_zero]
        | succ m =>
            rw [partitionsCap, dif_neg (by omega)]
            exact ih (by omega)

lemma mem_partitionsCap_iff : ∀ (n c : ℕ) (l : List ℕ),
    l ∈ partitionsCap n c ↔ IsValidPart n c l := by
  intro n c
  induction hsum : n + c using Nat.strong_induction_on generalizing n c with
  | h s ih =>
      intro l
      cases n with
      | zero =>
          rw [partitionsCap_zero]
          simp only [List.mem_singleton, IsValidPart]
          constructor
          · rintro rfl; exact ⟨by simp, List.Pairwise.nil, rfl⟩
          · rintro ⟨hpos, _, hsum0⟩
            cases l with
            | nil => rfl
            | cons a t =>
                have ha := (hpos a (by simp)).1
                simp at hsum0; omega
      | succ m =>
          cases c with
          | zero =>
              rw [partitionsCap_succ_zero]
              simp only [List.not_mem_nil, false_iff, IsValidPart]
              rintro ⟨hpos, _, hsum0⟩
              cases l with
              | nil => simp at hsum0
              | cons a t =>
                  have ⟨h1, h2⟩ := hpos a (by simp)
                  omega
          | succ c' =>
              rw [partitionsCap]
              by_cases hle : c' + 1 ≤ m + 1
              · rw [dif_pos hle, List.mem_append, List.mem_map]
                have ih1 : ∀ t, t ∈ partitionsCap (m + 1 - (c' + 1)) (c' + 1) ↔
                    IsValidPart (m + 1 - (c' + 1)) (c' + 1) t :=
                  ih (m + 1 - (c' + 1) + (c' + 1)) (by omega) _ _ rfl
                have ih2 : l ∈ partitionsCap (m + 1) c' ↔ IsValidPart (m + 1) c' l :=
                  ih (m + 1 + c') (by omega) _ _ rfl l
                simp_rw [ih1, ih2]
                constructor
                · rintro (⟨t, ⟨htpos, htpair, htsum⟩, rfl⟩ | ⟨hpos, hpair, hsum0⟩)
                  · refine ⟨?_, ?_, ?_⟩
                    · intro x hx
                      simp only [List.mem_cons] at hx
                      rcases hx with rfl | hx
                      · exact ⟨by omega, le_rfl⟩
                      · exact htpos x hx
                    · exact List.pairwise_cons.mpr ⟨fun y hy => (htpos y hy).2, htpair⟩
                    · simp only [List.sum_cons]; omega
                  · exact ⟨fun x hx => ⟨(hpos x hx).1, by have := (hpos x hx).2; omega⟩, hpair, hsum0⟩
                · rintro ⟨hpos, hpair, hsum0⟩
                  cases l with
                  | nil => simp at hsum0
                  | cons a t =>
                      have ha := hpos a (by simp)
                      rcases eq_or_lt_of_le ha.2 with rfl | hlt
                      · left
                        refine ⟨t, ⟨?_, (List.pairwise_cons.mp hpair).2, ?_⟩, rfl⟩
                        · intro x hx
                          exact ⟨(hpos x (List.mem_cons_of_mem _ hx)).1,
                            (List.pairwise_cons.mp hpair).1 x hx⟩
                        · simp only [List.sum_cons] at hsum0; omega
                      · right
                        refine ⟨fun x hx => ?_, hpair, hsum0⟩
                        simp only [List.mem_cons] at hx
                        rcases hx with rfl | hx
                        · exact ⟨ha.1, by omega⟩
                        · have hle_a := (List.pairwise_cons.mp hpair).1 x hx
                          exact ⟨(hpos x (List.mem_cons_of_mem _ hx)).1, by omega⟩
              · rw [dif_neg hle, ih (m + 1 + c') (by omega) _ _ rfl]
                constructor
                · rintro ⟨hpos, hpair, hsum0⟩
                  exact ⟨fun x hx => ⟨(hpos x hx).1, by have := (hpos x hx).2; omega⟩, hpair, hsum0⟩
                · rintro ⟨hpos, hpair, hsum0⟩
                  refine ⟨fun x hx => ⟨(hpos x hx).1, ?_⟩, hpair, hsum0⟩
                  have hle_sum : x ≤ l.sum := List.single_le_sum (fun _ _ => Nat.zero_le _) x hx
                  omega

lemma nodup_partitionsCap : ∀ (n c : ℕ), (partitionsCap n c).Nodup := by
  intro n c
  induction hsum : n + c using Nat.strong_induction_on generalizing n c with
  | h s ih =>
      cases n with
      | zero => rw [partitionsCap_zero]; simp
      | succ m =>
          cases c with
          | zero => rw [partitionsCap_succ_zero]; simp
          | succ c' =>
              rw [partitionsCap]
              by_cases hle : c' + 1 ≤ m + 1
              · rw [dif_pos hle, List.nodup_append]
                refine ⟨(ih _ (by omega) _ _ rfl).map (fun _ _ h => List.cons.inj h |>.2),
                  ih _ (by omega) _ _ rfl, ?_⟩
                intro l₁ hl1 l₂ hl2 heq
                subst heq
                rw [List.mem_map] at hl1
                rcases hl1 with ⟨t, _, rfl⟩
                rw [mem_partitionsCap_iff] at hl2
                have := (hl2.1 (c' + 1) (by simp)).2
                omega
              · rw [dif_neg hle]
                exact ih _ (by omega) _ _ rfl

lemma partitions_nonempty (n : ℕ) : (partitions n) ≠ [] := by
  cases n with
  | zero => simp [partitions, partitionsCap_zero]
  | succ m =>
      intro hempty
      have hmem : [m + 1] ∈ partitions (m + 1) := by
        rw [partitions, mem_partitionsCap_iff]
        exact ⟨fun x hx => by simp at hx; subst hx; exact ⟨by omega, le_rfl⟩,
          by simp, by simp⟩
      rw [hempty] at hmem
      simp at hmem

lemma head_partitions_succ (r : ℕ) :
    ∃ rest, partitions (r + 1) = [r + 1] :: rest := by
  unfold partitions
  rw [partitionsCap, dif_pos le_rfl, Nat.sub_self, partitionsCap_zero]
  exact ⟨partitionsCap (r + 1) r, rfl⟩

lemma head_block_succ (r : ℕ) : ∃ rest, block (r + 1) = 2 :: rest := by
  rcases head_partitions_succ r with ⟨rest, hrest⟩
  exact ⟨rest.map (fun t => t.length + 1), by simp [block, hrest]⟩

/-- Block decomposition of `partitionsCap n c` for `1 ≤ n` and `c ≤ n`. -/
lemma partitionsCap_eq_flatMap (n c : ℕ) (hn : 1 ≤ n) (hc : c ≤ n) :
    partitionsCap n c =
      (List.range c).flatMap fun j =>
        let r := n - (c - j)
        (partitionsCap r (c - j)).map ((c - j) :: ·) := by
  induction c with
  | zero =>
      cases n with
      | zero => omega
      | succ m => simp [partitionsCap_succ_zero]
  | succ c ih =>
      cases n with
      | zero => omega
      | succ m =>
          rw [partitionsCap, dif_pos hc]
          rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
          simp only [Nat.sub_zero]
          congr 1
          rw [ih (by omega)]
          refine List.flatMap_congr fun j _ => ?_
          simp only [Nat.succ_sub_succ_eq_sub]

/-- Row `n` (`n ≥ 1`) decomposes into blocks indexed by remainder `r = 0, ..., n - 1`. -/
lemma rowA128628_eq_flatMap (n : ℕ) (hn : 1 ≤ n) :
    rowA128628 n =
      (List.range n).flatMap fun r =>
        (partitionsCap r (n - r)).map (fun t => t.length + 1) := by
  unfold rowA128628 partitions
  rw [partitionsCap_eq_flatMap n n hn le_rfl, List.map_flatMap]
  refine List.flatMap_congr fun r hr => ?_
  rw [List.mem_range] at hr
  have hsub : n - (n - r) = r := by omega
  rw [hsub, List.map_map]
  rfl

/-- For `2 * R ≤ n` (`n ≥ 1`), `limitPrefix R` is a prefix of `rowA128628 n`. -/
lemma limitPrefix_isPrefix_row (n R : ℕ) (hn : 1 ≤ n) (hR : 2 * R ≤ n) :
    limitPrefix R <+: rowA128628 n := by
  have hRn : R + 1 ≤ n := by omega
  rw [rowA128628_eq_flatMap n hn, limitPrefix]
  have hsplit : List.range n = List.range (R + 1) ++ (List.range (n - (R + 1))).map (· + (R + 1)) := by
    have h1 : n = (R + 1) + (n - (R + 1)) := by omega
    conv_lhs => rw [h1, List.range_add]
    simp [add_comm]
  rw [hsplit, List.flatMap_append]
  have hpref : (List.range (R + 1)).flatMap (fun r => (partitionsCap r (n - r)).map (fun t => t.length + 1)) =
      (List.range (R + 1)).flatMap block := by
    refine List.flatMap_congr fun r hr => ?_
    rw [List.mem_range] at hr
    rw [block, partitions, partitionsCap_eq_of_le (by omega)]
  rw [hpref]
  exact List.prefix_append _ _

private lemma list_sum_map_range (g : ℕ → ℕ) (k : ℕ) :
    ((List.range k).map g).sum = ∑ r ∈ Finset.range k, g r := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        Finset.sum_range_succ, ih]

/-- Length of `limitPrefix R` is `∑_{r=0}^R |partitions r|`. -/
lemma length_limitPrefix (R : ℕ) :
    (limitPrefix R).length = ∑ r ∈ Finset.range (R + 1), (partitions r).length := by
  unfold limitPrefix
  rw [List.length_flatMap, list_sum_map_range]
  refine Finset.sum_congr rfl fun r _ => by simp [block]

lemma length_limitPrefix_ge (R : ℕ) : R + 1 ≤ (limitPrefix R).length := by
  rw [length_limitPrefix]
  calc
    R + 1 = ∑ _r ∈ Finset.range (R + 1), 1 := by simp
    _ ≤ ∑ r ∈ Finset.range (R + 1), (partitions r).length := by
        refine Finset.sum_le_sum fun r _ => ?_
        exact List.length_pos_of_ne_nil (partitions_nonempty r)

lemma limitPrefix_mono {R₁ R₂ : ℕ} (h : R₁ ≤ R₂) :
    limitPrefix R₁ <+: limitPrefix R₂ := by
  unfold limitPrefix
  have hsplit : List.range (R₂ + 1) =
      List.range (R₁ + 1) ++ (List.range (R₂ - R₁)).map (· + (R₁ + 1)) := by
    have h1 : R₂ + 1 = (R₁ + 1) + (R₂ - R₁) := by omega
    conv_lhs => rw [h1, List.range_add]
    simp [add_comm]
  rw [hsplit, List.flatMap_append]
  exact List.prefix_append _ _

/-- The limiting sequence OEIS A308355, indexed from `0`. -/
def seqA308355 (i : ℕ) : ℕ :=
  (limitPrefix i)[i]'(by have := length_limitPrefix_ge i; omega)

lemma getElem?_limitPrefix_eq_seqA308355 {R i : ℕ} (hi : i < (limitPrefix R).length) :
    (limitPrefix R)[i]? = some (seqA308355 i) := by
  have hget : ∀ R₁ R₂, R₁ ≤ R₂ → i < (limitPrefix R₁).length →
      (limitPrefix R₁)[i]? = (limitPrefix R₂)[i]? := by
    intro R₁ R₂ h12 hi1
    rcases limitPrefix_mono h12 with ⟨t, ht⟩
    rw [← ht, List.getElem?_append_left hi1]
  rw [seqA308355]
  by_cases hRi : R ≤ i
  · rw [hget R i hRi hi, List.getElem?_eq_getElem]
  · rw [← hget i R (by omega) (by have := length_limitPrefix_ge i; omega), List.getElem?_eq_getElem]

/-- **Existence of the row limit (A308355):** for every index `i`, row `n` of A128628 stabilizes
at `seqA308355 i` for all `n ≥ max 1 (2 * i)`. -/
theorem a308355_is_row_limit (i : ℕ) :
    ∀ n ≥ max 1 (2 * i), (rowA128628 n)[i]? = some (seqA308355 i) := by
  intro n hn
  rcases limitPrefix_isPrefix_row n i (by omega) (by omega) with ⟨t, ht⟩
  have hlt : i < (limitPrefix i).length := by have := length_limitPrefix_ge i; omega
  rw [← ht, List.getElem?_append_left hlt, getElem?_limitPrefix_eq_seqA308355 hlt]

/-! ## Section 2: Exact Agreement Length Between Row `n` of A128628 and A308355 -/

/-- The exact maximal common prefix length of `rowA128628 n` and `seqA308355` is
`S(n) = ∑_{r=0}^{⌊n/2⌋} p(r)`. -/
theorem row_agrees_with_limit_upto_half (n : ℕ) (hn : 1 ≤ n) :
    let S := ∑ r ∈ Finset.range (n / 2 + 1), (partitions r).length
    (S ≤ (rowA128628 n).length) ∧
    (∀ i < S, (rowA128628 n)[i]? = some (seqA308355 i)) ∧
    ((rowA128628 n)[S]? ≠ some (seqA308355 S)) := by
  dsimp only
  set m := n / 2
  set S := ∑ r ∈ Finset.range (m + 1), (partitions r).length
  have hS_len : (limitPrefix m).length = S := length_limitPrefix m
  rcases limitPrefix_isPrefix_row n m hn (by omega) with ⟨tail, htail⟩
  have hle : S ≤ (rowA128628 n).length := by
    rw [← htail, List.length_append, hS_len]; omega
  have hagree : ∀ i < S, (rowA128628 n)[i]? = some (seqA308355 i) := by
    intro i hi
    rw [← htail, List.getElem?_append_left (by omega)]
    exact getElem?_limitPrefix_eq_seqA308355 (by omega)
  refine ⟨hle, hagree, ?_⟩
  by_cases hn2 : n ≤ 2
  · have hlen_eq : (rowA128628 n).length = S := by
      dsimp only [S, m]
      have h12 : n = 1 ∨ n = 2 := by omega
      rcases h12 with rfl | rfl <;>
        simp [rowA128628, partitions, partitionsCap, Finset.sum_range_succ]
    rw [List.getElem?_eq_none (by omega)]
    simp
  · have hn3 : 3 ≤ n := by omega
    have hlim_S : seqA308355 S = 2 := by
      rcases head_block_succ m with ⟨rest, hrest⟩
      have hpref_m1 : limitPrefix (m + 1) = limitPrefix m ++ block (m + 1) := by
        unfold limitPrefix
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      have hS_lt : S < (limitPrefix (m + 1)).length := by
        rw [hpref_m1, List.length_append, hS_len, hrest]; simp
      have hget := getElem?_limitPrefix_eq_seqA308355 (R := m + 1) (i := S) hS_lt
      rw [hpref_m1, List.getElem?_append_right (by omega), hS_len, Nat.sub_self, hrest] at hget
      simpa using hget.symm
    rw [hlim_S]
    have hrow_split : rowA128628 n =
        limitPrefix m ++
        ((partitionsCap (m + 1) (n - (m + 1))).map (fun t => t.length + 1) ++
          ((List.range (n - (m + 2))).map (· + (m + 2))).flatMap
            (fun r => (partitionsCap r (n - r)).map (fun t => t.length + 1))) := by
      rw [rowA128628_eq_flatMap n hn]
      have hrange : List.range n =
          List.range (m + 1) ++ ((m + 1) :: (List.range (n - (m + 2))).map (· + (m + 2))) := by
        apply List.ext_getElem
        · simp; omega
        · intro i hi1 hi2
          rw [List.getElem_range]
          by_cases him : i < m + 1
          · rw [List.getElem_append_left (by simp; omega), List.getElem_range]
          · rw [List.getElem_append_right (by simp; omega)]
            simp only [List.length_range]
            by_cases hi_eq : i = m + 1
            · subst hi_eq; simp
            · have hpos : 0 < i - (m + 1) := by omega
              have hidx : i - (m + 1) = (i - (m + 2)) + 1 := by omega
              simp only [hidx, List.getElem_cons_succ, List.getElem_map, List.getElem_range]
              omega
      rw [hrange, List.flatMap_append, List.flatMap_cons]
      congr 1
      unfold limitPrefix
      refine List.flatMap_congr fun r hr => ?_
      rw [List.mem_range] at hr
      rw [block, partitions, partitionsCap_eq_of_le (by omega)]
    rw [hrow_split, List.getElem?_append_right (by omega), hS_len, Nat.sub_self]
    have hblk_ne : partitionsCap (m + 1) (n - (m + 1)) ≠ [] := by
      intro hemp
      have hmem : List.replicate (m + 1) 1 ∈ partitionsCap (m + 1) (n - (m + 1)) := by
        rw [mem_partitionsCap_iff]
        refine ⟨fun x hx => ?_, ?_, ?_⟩
        · rw [List.mem_replicate] at hx; rcases hx with ⟨_, rfl⟩; exact ⟨by omega, by omega⟩
        · exact List.pairwise_replicate.mpr (Or.inr le_rfl)
        · simp
      rw [hemp] at hmem; simp at hmem
    cases hcases : partitionsCap (m + 1) (n - (m + 1)) with
    | nil => exact absurd hcases hblk_ne
    | cons t ts =>
        simp only [List.map_cons, List.cons_append, List.getElem?_cons_zero]
        have ht_valid : IsValidPart (m + 1) (n - (m + 1)) t := by
          rw [← mem_partitionsCap_iff, hcases]; simp
        have ht_len : 2 ≤ t.length := by
          rcases ht_valid with ⟨htpos, _, htsum⟩
          cases t with
          | nil => simp at htsum
          | cons a rest =>
              cases rest with
              | nil =>
                  have ha := (htpos a (by simp)).2
                  simp at htsum; omega
              | cons b rest' => simp
        intro hsome
        injection hsome with heq_len
        omega

/-! ## Section 3: Palindromic Partitions Bijection (`A025065(n) = ∑_{r=0}^{⌊n/2⌋} p(r)`) -/

/-- A partition is palindromic iff its parts can be permuted into a palindrome. -/
def IsPalindromic (l : List ℕ) : Prop :=
  ∃ p : List ℕ, p.Perm l ∧ p.reverse = p

/-- OEIS A025065: number of palindromic partitions of `n`. -/
noncomputable def A025065 (n : ℕ) : ℕ :=
  open Classical in ((partitions n).filter (fun l => IsPalindromic l)).length

private lemma count_cons_eq (a z : ℕ) (l : List ℕ) :
    (a :: l).count z = l.count z + if a = z then 1 else 0 := by
  rw [List.count_cons]
  by_cases h : a = z
  · subst h; simp
  · have hne : (a == z) = false := beq_false_of_ne h
    simp [hne, h]

private lemma odd_count_unique_of_palindrome {p : List ℕ} (hpal : p.reverse = p) :
    ∀ x y : ℕ, p.count x % 2 = 1 → p.count y % 2 = 1 → x = y := by
  induction hlen : p.length using Nat.strong_induction_on generalizing p with
  | h len ih =>
      intro x y hx hy
      cases p with
      | nil => simp at hx
      | cons a rest =>
          cases hrev : rest.reverse with
          | nil =>
              have hrest : rest = [] := by simpa using congrArg List.reverse hrev
              subst hrest
              rw [count_cons_eq, List.count_nil, zero_add] at hx hy
              by_cases hax : a = x <;> by_cases hay : a = y <;> simp_all
          | cons b mid_rev =>
              have hrest : rest = mid_rev.reverse ++ [b] := by
                have := congrArg List.reverse hrev
                simpa using this
              rw [hrest] at hpal
              have hpal' : b :: (mid_rev ++ [a]) = a :: (mid_rev.reverse ++ [b]) := by
                simpa [List.reverse_append] using hpal
              have hab : b = a := List.cons.inj hpal' |>.1
              subst hab
              have hmid_eq : mid_rev = mid_rev.reverse := by
                have htail := List.cons.inj hpal' |>.2
                exact List.append_inj_left' htail rfl
              have hcount : ∀ z, (b :: (mid_rev.reverse ++ [b])).count z =
                  mid_rev.count z + (if b = z then 2 else 0) := by
                intro z
                rw [count_cons_eq, List.count_append, List.count_reverse, count_cons_eq,
                  List.count_nil, zero_add]
                split_ifs <;> omega
              rw [hrest, hcount] at hx hy
              have hx' : mid_rev.count x % 2 = 1 := by split_ifs at hx <;> omega
              have hy' : mid_rev.count y % 2 = 1 := by split_ifs at hy <;> omega
              have hlen_mid : mid_rev.length < len := by
                rw [← hlen, hrest]; simp
              exact ih mid_rev.length hlen_mid hmid_eq.symm rfl x y hx' hy'

/-- Characterization: a list can be permuted into a palindrome iff at most one value has odd count. -/
theorem isPalindromic_iff_atMostOneOdd (l : List ℕ) :
    IsPalindromic l ↔ ∀ x y : ℕ, l.count x % 2 = 1 → l.count y % 2 = 1 → x = y := by
  constructor
  · rintro ⟨p, hperm, hrev⟩ x y hx hy
    rw [← hperm.count_eq] at hx hy
    exact odd_count_unique_of_palindrome hrev x y hx hy
  · intro huniq
    induction hlen : l.length using Nat.strong_induction_on generalizing l with
    | h len ih =>
        cases l with
        | nil => exact ⟨[], List.Perm.refl _, rfl⟩
        | cons a rest =>
            by_cases ha_mem : a ∈ rest
            · rcases List.mem_iff_append.mp ha_mem with ⟨u, v, rfl⟩
              have hperm1 : (a :: (u ++ a :: v)).Perm (a :: a :: (u ++ v)) :=
                (List.perm_middle (l₁ := u) (l₂ := v) (a := a)).cons a
              have huniq' : ∀ x y, (u ++ v).count x % 2 = 1 → (u ++ v).count y % 2 = 1 → x = y := by
                intro x y hx hy
                have hcnt : ∀ z, (a :: (u ++ a :: v)).count z = (u ++ v).count z + (if a = z then 2 else 0) := by
                  intro z
                  rw [hperm1.count_eq, count_cons_eq, count_cons_eq]
                  split_ifs <;> omega
                exact huniq x y (by rw [hcnt]; split_ifs <;> omega) (by rw [hcnt]; split_ifs <;> omega)
              have hlen' : (u ++ v).length < len := by rw [← hlen]; simp
              rcases ih (u ++ v).length hlen' (u ++ v) huniq' rfl with ⟨p, hp_perm, hp_rev⟩
              refine ⟨a :: (p ++ [a]), ?_, ?_⟩
              · have h1 : (a :: (p ++ [a])).Perm (a :: a :: p) :=
                  (List.perm_append_singleton a p).cons a
                have h2 : (a :: a :: p).Perm (a :: a :: (u ++ v)) := (hp_perm.cons a).cons a
                exact (h1.trans h2).trans hperm1.symm
              · simp [List.reverse_append, hp_rev]
            · have ha_cnt : (a :: rest).count a = 1 := by
                rw [List.count_cons_self, List.count_eq_zero.mpr ha_mem]
              have hrest_even : ∀ x, rest.count x % 2 = 0 := by
                intro x
                by_cases hxa : x = a
                · subst hxa; rw [List.count_eq_zero.mpr ha_mem]
                · by_contra hodd
                  have h1 : rest.count x % 2 = 1 := by omega
                  have h2 : (a :: rest).count x % 2 = 1 := by
                    rw [List.count_cons_of_ne (Ne.symm hxa)]; exact h1
                  exact hxa (huniq x a h2 (by rw [ha_cnt]))
              cases rest with
              | nil => exact ⟨[a], List.Perm.refl _, rfl⟩
              | cons b rest' =>
                  have hb_ge2 : 2 ≤ (b :: rest').count b := by
                    have hpos : 0 < (b :: rest').count b := List.count_pos_iff.mpr (by simp)
                    have hev := hrest_even b
                    omega
                  have hb_mem : b ∈ rest' := by
                    rw [List.count_cons_self] at hb_ge2
                    exact List.count_pos_iff.mp (by omega)
                  rcases List.mem_iff_append.mp hb_mem with ⟨u, v, rfl⟩
                  have hperm1 : (a :: b :: (u ++ b :: v)).Perm (b :: b :: (a :: (u ++ v))) := by
                    have h1 : (u ++ b :: v).Perm (b :: (u ++ v)) := List.perm_middle
                    have h2 : (a :: b :: (u ++ b :: v)).Perm (a :: b :: b :: (u ++ v)) :=
                      (h1.cons b).cons a
                    have h3 : (a :: b :: b :: (u ++ v)).Perm (b :: a :: b :: (u ++ v)) :=
                      List.Perm.swap b a _
                    have h4 : (b :: a :: b :: (u ++ v)).Perm (b :: b :: a :: (u ++ v)) :=
                      (List.Perm.swap b a _).cons b
                    exact (h2.trans h3).trans h4
                  have huniq' : ∀ x y, (a :: (u ++ v)).count x % 2 = 1 →
                      (a :: (u ++ v)).count y % 2 = 1 → x = y := by
                    intro x y hx hy
                    have hcnt : ∀ z, (a :: b :: (u ++ b :: v)).count z =
                        (a :: (u ++ v)).count z + (if b = z then 2 else 0) := by
                      intro z
                      rw [hperm1.count_eq, count_cons_eq, count_cons_eq]
                      split_ifs <;> omega
                    exact huniq x y (by rw [hcnt]; split_ifs <;> omega) (by rw [hcnt]; split_ifs <;> omega)
                  have hlen' : (a :: (u ++ v)).length < len := by rw [← hlen]; simp
                  rcases ih (a :: (u ++ v)).length hlen' (a :: (u ++ v)) huniq' rfl with ⟨p, hp_perm, hp_rev⟩
                  refine ⟨b :: (p ++ [b]), ?_, ?_⟩
                  · have h1 : (b :: (p ++ [b])).Perm (b :: b :: p) :=
                      (List.perm_append_singleton b p).cons b
                    have h2 : (b :: b :: p).Perm (b :: b :: (a :: (u ++ v))) := (hp_perm.cons b).cons b
                    exact (h1.trans h2).trans hperm1.symm
                  · simp [List.reverse_append, hp_rev]

private def sortDesc (l : List ℕ) : List ℕ :=
  l.insertionSort (· ≥ ·)

private lemma sortDesc_perm (l : List ℕ) : (sortDesc l).Perm l :=
  List.perm_insertionSort (· ≥ ·) l

private lemma sortDesc_pairwise (l : List ℕ) : (sortDesc l).Pairwise (· ≥ ·) :=
  List.pairwise_insertionSort (· ≥ ·) l

private lemma eq_of_perm_pairwise_ge {l₁ l₂ : List ℕ} (hperm : l₁.Perm l₂)
    (h1 : l₁.Pairwise (· ≥ ·)) (h2 : l₂.Pairwise (· ≥ ·)) : l₁ = l₂ :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h2 h1) h1 h2 hperm

private def halfSorted : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | x :: y :: rest => if x = y then x :: halfSorted rest else halfSorted (y :: rest)

private lemma mem_halfSorted_subset : ∀ (m : List ℕ) {w : ℕ}, w ∈ halfSorted m → w ∈ m
  | [], _, hw => by simp [halfSorted] at hw
  | [_], _, hw => by simp [halfSorted] at hw
  | x :: y :: rest, w, hw => by
      simp only [halfSorted] at hw
      split_ifs at hw with hxy
      · simp only [List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · left; rfl
        · right; right; exact mem_halfSorted_subset rest hw
      · exact List.mem_cons_of_mem x (mem_halfSorted_subset (y :: rest) hw)

private lemma halfSorted_pairwise : ∀ l : List ℕ, l.Pairwise (· ≥ ·) → (halfSorted l).Pairwise (· ≥ ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.Pairwise.nil
  | x :: y :: rest, hpair => by
      simp only [halfSorted]
      split_ifs with hxy
      · subst hxy
        have hrest : rest.Pairwise (· ≥ ·) := (List.pairwise_cons.mp (List.pairwise_cons.mp hpair).2).2
        refine List.pairwise_cons.mpr ⟨?_, halfSorted_pairwise rest hrest⟩
        intro z hz
        exact (List.pairwise_cons.mp hpair).1 z (List.mem_cons_of_mem x (mem_halfSorted_subset rest hz))
      · exact halfSorted_pairwise (y :: rest) (List.pairwise_cons.mp hpair).2

private lemma count_halfSorted : ∀ (l : List ℕ), l.Pairwise (· ≥ ·) → ∀ z : ℕ,
    (halfSorted l).count z = l.count z / 2
  | [], _, z => by simp [halfSorted]
  | [a], _, z => by
      simp only [halfSorted, List.count_nil, count_cons_eq, zero_add]
      split_ifs <;> rfl
  | a :: b :: t, hpair, z => by
      have hpair_bt : (b :: t).Pairwise (· ≥ ·) := (List.pairwise_cons.mp hpair).2
      have hpair_t : t.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hpair_bt).2
      simp only [halfSorted]
      split_ifs with hab
      · subst hab
        rw [count_cons_eq, count_halfSorted t hpair_t z, count_cons_eq, count_cons_eq]
        split_ifs <;> omega
      · have ha_gt : ∀ w ∈ b :: t, w < a := by
          intro w hw
          have hba := (List.pairwise_cons.mp hpair).1 b (by simp)
          rcases List.mem_cons.mp hw with rfl | hwt
          · omega
          · have hwb := (List.pairwise_cons.mp hpair_bt).1 w hwt
            omega
        rw [count_halfSorted (b :: t) hpair_bt z]
        conv_rhs => rw [count_cons_eq]
        by_cases hza : a = z
        · subst hza
          have hnot : a ∉ b :: t := fun hm => lt_irrefl a (ha_gt a hm)
          rw [if_pos rfl, List.count_eq_zero.mpr hnot]
        · rw [if_neg hza, add_zero]

private lemma sum_eq_two_mul_halfSorted_add_center {l : List ℕ}
    (hpos : ∀ x ∈ l, 0 < x) (hpair : l.Pairwise (· ≥ ·)) (hpal : IsPalindromic l) :
    2 * (halfSorted l).sum ≤ l.sum ∧
    (∀ z : ℕ, l.count z = 2 * (halfSorted l).count z +
      (if l.sum - 2 * (halfSorted l).sum = z ∧ 0 < z then 1 else 0)) := by
  have huniq := (isPalindromic_iff_atMostOneOdd l).mp hpal
  have hcnt : ∀ z, (halfSorted l).count z = l.count z / 2 := count_halfSorted l hpair
  have hsum_count : ∀ m : List ℕ, ∀ s : Finset ℕ, (∀ x ∈ m, x ∈ s) →
      m.sum = ∑ z ∈ s, z * m.count z := by
    intro m s hs
    induction m with
    | nil => simp
    | cons a t ih =>
        rw [List.sum_cons, ih (fun x hx => hs x (List.mem_cons_of_mem a hx))]
        have ha_mem : a ∈ s := hs a (by simp)
        have hstep : ∑ z ∈ s, z * (a :: t).count z =
            a + ∑ z ∈ s, z * t.count z := by
          rw [← Finset.add_sum_erase _ _ ha_mem, ← Finset.add_sum_erase _ _ ha_mem]
          rw [List.count_cons_self, mul_add, mul_one]
          have hrest : ∑ z ∈ s.erase a, z * (a :: t).count z = ∑ z ∈ s.erase a, z * t.count z := by
            refine Finset.sum_congr rfl fun z hz => ?_
            have hza : z ≠ a := (Finset.mem_erase.mp hz).1
            rw [List.count_cons_of_ne (Ne.symm hza)]
          rw [hrest]; ring
        omega
  set s : Finset ℕ := l.toFinset
  have hl_sum : l.sum = ∑ z ∈ s, z * l.count z := hsum_count l s (fun x hx => List.mem_toFinset.mpr hx)
  have hh_sum : (halfSorted l).sum = ∑ z ∈ s, z * (halfSorted l).count z :=
    hsum_count (halfSorted l) s (fun x hx => List.mem_toFinset.mpr (mem_halfSorted_subset l hx))
  have hle : 2 * (halfSorted l).sum ≤ l.sum := by
    rw [hl_sum, hh_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    rw [hcnt z]; have : 2 * (l.count z / 2) ≤ l.count z := Nat.mul_div_le _ 2
    nlinarith
  refine ⟨hle, ?_⟩
  by_cases hex : ∃ c : ℕ, l.count c % 2 = 1
  · rcases hex with ⟨c, hc⟩
    have hc_in : c ∈ l := List.count_pos_iff.mp (by omega)
    have hc_pos : 0 < c := hpos c hc_in
    have hc_mem : c ∈ s := List.mem_toFinset.mpr hc_in
    have hdiff : l.sum - 2 * (halfSorted l).sum = c := by
      have heq : l.sum = 2 * (halfSorted l).sum + c := by
        rw [hl_sum, hh_sum, Finset.mul_sum]
        rw [← Finset.add_sum_erase _ _ hc_mem, ← Finset.add_sum_erase _ _ hc_mem]
        have hother : ∑ z ∈ s.erase c, z * l.count z =
            ∑ z ∈ s.erase c, 2 * (z * (halfSorted l).count z) := by
          refine Finset.sum_congr rfl fun z hz => ?_
          have hzc : z ≠ c := (Finset.mem_erase.mp hz).1
          have hev : l.count z % 2 = 0 := by
            by_contra hodd; exact hzc (huniq z c (by omega) hc)
          have hmul : l.count z = 2 * (halfSorted l).count z := by rw [hcnt z]; omega
          rw [hmul]; ring
        have hcmul : l.count c = 2 * (halfSorted l).count c + 1 := by rw [hcnt c]; omega
        rw [hother, hcmul]; ring
      omega
    intro z
    rw [hdiff, hcnt z]
    by_cases hzc : c = z
    · subst hzc
      rw [if_pos ⟨rfl, hc_pos⟩]; omega
    · have hev : l.count z % 2 = 0 := by
        by_contra hodd; exact hzc (huniq z c (by omega) hc).symm
      rw [if_neg (by rintro ⟨h1, _⟩; exact hzc h1)]
      omega
  · push Not at hex
    have hdiff : l.sum - 2 * (halfSorted l).sum = 0 := by
      have heq : l.sum = 2 * (halfSorted l).sum := by
        rw [hl_sum, hh_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        have hev : l.count z % 2 = 0 := by have := hex z; omega
        have hmul : l.count z = 2 * (halfSorted l).count z := by rw [hcnt z]; omega
        rw [hmul]; ring
      omega
    intro z
    rw [hdiff, hcnt z, if_neg (by rintro ⟨h1, h2⟩; omega)]
    have hev : l.count z % 2 = 0 := by have := hex z; omega
    omega

/-- Double every part of `t` and insert a central part `n - 2 * t.sum` if positive, sorted descending. -/
private def doubleWithCenter (n : ℕ) (t : List ℕ) : List ℕ :=
  let c := n - 2 * t.sum
  sortDesc (if 0 < c then c :: (t ++ t) else t ++ t)

/-- **Exact Palindromic Partition Count (`A025065`):**
`A025065(n) = ∑_{r=0}^{⌊n/2⌋} p(r)` for every `n`. -/
theorem A025065_eq_sum_partitions (n : ℕ) :
    A025065 n = ∑ r ∈ Finset.range (n / 2 + 1), (partitions r).length := by
  open Classical in
  unfold A025065
  set P_pal : Finset (List ℕ) := ((partitions n).filter (fun l => IsPalindromic l)).toFinset
  set T_half : Finset ((_ : ℕ) × List ℕ) :=
    (Finset.range (n / 2 + 1)).sigma fun r => (partitions r).toFinset
  have hL : ((partitions n).filter (fun l => IsPalindromic l)).length = P_pal.card :=
    (List.toFinset_card_of_nodup ((nodup_partitionsCap n n).filter _)).symm
  have hR : (∑ r ∈ Finset.range (n / 2 + 1), (partitions r).length) = T_half.card := by
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact (List.toFinset_card_of_nodup (nodup_partitionsCap r r)).symm
  rw [hL, hR]
  refine Finset.card_bij'
    (fun l _ => ⟨(halfSorted l).sum, halfSorted l⟩)
    (fun rt _ => doubleWithCenter n rt.2)
    ?_ ?_ ?_ ?_
  · intro l hl
    simp only [P_pal, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      partitions, mem_partitionsCap_iff] at hl
    rcases hl with ⟨⟨hpos, hpair, hsum⟩, hpal⟩
    have hspec := sum_eq_two_mul_halfSorted_add_center (fun x hx => (hpos x hx).1) hpair hpal
    simp only [T_half, Finset.mem_sigma, Finset.mem_range, List.mem_toFinset,
      partitions, mem_partitionsCap_iff]
    refine ⟨by omega, ?_, halfSorted_pairwise l hpair, rfl⟩
    intro x hx
    have hxl := mem_halfSorted_subset l hx
    exact ⟨(hpos x hxl).1, List.single_le_sum (fun _ _ => Nat.zero_le _) x hx⟩
  · intro ⟨r, t⟩ hrt
    simp only [T_half, Finset.mem_sigma, Finset.mem_range, List.mem_toFinset,
      partitions, mem_partitionsCap_iff] at hrt
    rcases hrt with ⟨hr, htpos, htpair, htsum⟩
    simp only [P_pal, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      partitions, mem_partitionsCap_iff]
    set c := n - 2 * t.sum
    set raw := if 0 < c then c :: (t ++ t) else t ++ t
    have hperm : (doubleWithCenter n t).Perm raw := sortDesc_perm raw
    have hsum_raw : raw.sum = n := by
      dsimp only [raw, c]; split_ifs <;> simp [htsum] <;> omega
    have hpos_raw : ∀ x ∈ raw, 0 < x ∧ x ≤ n := by
      intro x hx
      dsimp only [raw, c] at hx
      split_ifs at hx with hc
      · simp only [List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · exact ⟨hc, by omega⟩
        · exact ⟨(htpos x hx).1, by have := (htpos x hx).2; omega⟩
        · exact ⟨(htpos x hx).1, by have := (htpos x hx).2; omega⟩
      · simp only [List.mem_append] at hx
        rcases hx with hx | hx <;> exact ⟨(htpos x hx).1, by have := (htpos x hx).2; omega⟩
    refine ⟨⟨fun x hx => hpos_raw x (hperm.subset hx), sortDesc_pairwise raw,
      hperm.sum_eq.trans hsum_raw⟩, ?_⟩
    rw [isPalindromic_iff_atMostOneOdd]
    intro x y hx hy
    rw [hperm.count_eq] at hx hy
    dsimp only [raw] at hx hy
    split_ifs at hx hy with hc
    · have hcnt : ∀ z, (c :: (t ++ t)).count z = 2 * t.count z + (if c = z then 1 else 0) := by
        intro z; rw [count_cons_eq, List.count_append]; omega
      rw [hcnt] at hx hy
      split_ifs at hx hy <;> omega
    · rw [List.count_append] at hx hy; omega
  · intro l hl
    simp only [P_pal, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      partitions, mem_partitionsCap_iff] at hl
    rcases hl with ⟨⟨hpos, hpair, hsum⟩, hpal⟩
    have hspec := sum_eq_two_mul_halfSorted_add_center (fun x hx => (hpos x hx).1) hpair hpal
    refine eq_of_perm_pairwise_ge ?_ (sortDesc_pairwise _) hpair
    refine (sortDesc_perm _).trans ?_
    rw [List.perm_iff_count]
    intro z
    have hcnt := hspec.2 z
    rw [hsum] at hcnt
    dsimp only
    split_ifs with hc
    · rw [count_cons_eq, List.count_append, hcnt]
      by_cases hcz : n - 2 * (halfSorted l).sum = z
      · subst hcz; rw [if_pos rfl, if_pos ⟨rfl, hc⟩]; omega
      · rw [if_neg hcz, if_neg (by rintro ⟨h1, _⟩; exact hcz h1)]; omega
    · rw [List.count_append, hcnt, if_neg (by rintro ⟨h1, h2⟩; omega)]; omega
  · intro ⟨r, t⟩ hrt
    simp only [T_half, Finset.mem_sigma, Finset.mem_range, List.mem_toFinset,
      partitions, mem_partitionsCap_iff] at hrt
    rcases hrt with ⟨hr, htpos, htpair, htsum⟩
    have hpair_d : (doubleWithCenter n t).Pairwise (· ≥ ·) := sortDesc_pairwise _
    have hperm_d : (doubleWithCenter n t).Perm (if 0 < n - 2 * t.sum then (n - 2 * t.sum) :: (t ++ t) else t ++ t) :=
      sortDesc_perm _
    have hhalf_eq : halfSorted (doubleWithCenter n t) = t := by
      refine eq_of_perm_pairwise_ge ?_ (halfSorted_pairwise _ hpair_d) htpair
      rw [List.perm_iff_count]
      intro z
      rw [count_halfSorted _ hpair_d z, hperm_d.count_eq]
      split_ifs with hc
      · rw [count_cons_eq, List.count_append]; split_ifs <;> omega
      · rw [List.count_append]; omega
    exact Sigma.ext (by dsimp only; rw [hhalf_eq, htsum]) (heq_of_eq hhalf_eq)

/-! ## Section 4: Main Theorems (Resolution of OEIS A308355 and A025065 Conjectures) -/

/-- **Main Theorem 1 (OEIS A025065 Conjecture proved for all `n ≥ 1`):**
For every `n ≥ 1`, the exact length of the maximal initial segment of A308355 identical to
row `n` of A128628 is `A025065(n)`. -/
theorem exact_agreement_eq_A025065 (n : ℕ) (hn : 1 ≤ n) :
    (A025065 n ≤ (rowA128628 n).length) ∧
    (∀ i < A025065 n, (rowA128628 n)[i]? = some (seqA308355 i)) ∧
    ((rowA128628 n)[A025065 n]? ≠ some (seqA308355 (A025065 n))) := by
  rw [A025065_eq_sum_partitions n]
  exact row_agrees_with_limit_upto_half n hn

/-- **Main Theorem 2 (OEIS A308355 Conjecture disproved for every odd `n ≥ 1`):**
`A025065(n) = A025065(n + 1)` if and only if `n` is even. For every odd `n = 2m + 1`,
`A025065(n + 1) = A025065(n) + p(m + 1) > A025065(n)`, so the displayed conjecture on
OEIS A308355 fails for every odd `n ≥ 1` (and holds for every even `n ≥ 2`). -/
theorem a308355_conjecture_iff_even (n : ℕ) :
    A025065 n = A025065 (n + 1) ↔ Even n := by
  rw [A025065_eq_sum_partitions n, A025065_eq_sum_partitions (n + 1)]
  constructor
  · intro heq
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rcases hodd with ⟨m, rfl⟩
    have h1 : (2 * m + 1) / 2 = m := by omega
    have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have hsum_eq : ∑ r ∈ Finset.range ((2 * m + 1 + 1) / 2 + 1), (partitions r).length =
        (∑ r ∈ Finset.range ((2 * m + 1) / 2 + 1), (partitions r).length) +
        (partitions (m + 1)).length := by
      rw [h1, h2, Finset.sum_range_succ]
    have hpos : 1 ≤ (partitions (m + 1)).length :=
      List.length_pos_of_ne_nil (partitions_nonempty (m + 1))
    omega
  · rintro ⟨m, rfl⟩
    have h1 : (m + m) / 2 = m := by omega
    have h2 : (m + m + 1) / 2 = m := by omega
    rw [h1, h2]

/-- Explicit counterexample at `n = 5`: exact agreement is `4`, while `A025065(6) = 7`. -/
theorem counterexample_n5 :
    A025065 5 = 4 ∧ A025065 6 = 7 ∧
    rowA128628 5 = [1, 2, 2, 3, 3, 4, 5] ∧
    (List.range 7).map seqA308355 = [1, 2, 2, 3, 2, 3, 4] := by
  rw [A025065_eq_sum_partitions 5, A025065_eq_sum_partitions 6]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Finset.sum_range_succ, partitions, partitionsCap]
  · simp [Finset.sum_range_succ, partitions, partitionsCap]
  · simp [rowA128628, partitions, partitionsCap]
  · simp [List.range_succ, seqA308355, limitPrefix, block, partitions, partitionsCap]

end KimberlingA308355
