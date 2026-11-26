import Mathlib

/-!
# Vasilyev (arXiv:2611.20344v2), Question 7.1: Refutation of `2^ℓ < 3^(a+1)`

Negative resolution of Question 7.1 in O. Vasilyev, *Up or down at every integer:
Collatz-type maps of arbitrary sets and the up-down graph*, arXiv:2611.20344v2
(math.NT, 18 Nov 2026), Section 7.

## Main Result

For a finite subset `S : Finset ℕ`, define `T S x = if x ∈ S then U x else D x`, where
`U x = (3 * x + 1) / 2 = ⌈3x / 2⌉` and `D x = (x + 1) / 2 = ⌈x / 2⌉`.
Question 7.1 asks whether every primitive cycle of length `ℓ` with `a` up-steps
satisfies `2 ^ ℓ < 3 ^ (a + 1)` (equivalently `a = ⌊ℓ log₃ 2⌋`).

We exhibit an explicit 382-vertex simple cycle stored in 8 chunks of length ≤ 48
(so every kernel `decide` lookup has recursion depth ≤ 48) and prove
`vasilyev_question_7_1_disproof`:
1. Every vertex is `≥ 2` and all `382` vertices are pairwise distinct (via an `O(n)`
   strictly increasing sorted-rank certificate),
2. Every consecutive step `(x_i, x_{(i+1) % 382})` is `U` or `D`,
3. Taking `S : Finset ℕ` to be the finite set of `240` up-vertices, `T S` maps
   `x_i ↦ x_{(i+1) % 382}` for all `i`, giving a primitive cycle of exact period `382`,
4. Exactly `a = 240` vertices of the cycle lie in `S`, and
5. `3 ^ (a + 1) < 2 ^ ℓ` (specifically `3 ^ 241 < 2 ^ 382 < 3 ^ 242`).
-/

namespace VasilyevUpDownCycles

/-- Upward step `U(x) = ⌈3x / 2⌉ = ⌊(3x + 1) / 2⌋`. -/
def U (x : ℕ) : ℕ := (3 * x + 1) / 2

/-- Downward step `D(x) = ⌈x / 2⌉ = ⌊(x + 1) / 2⌋`. -/
def D (x : ℕ) : ℕ := (x + 1) / 2

/-- Vasilyev's Collatz-type map `T_S` for a finite subset `S : Finset ℕ`. -/
def T (S : Finset ℕ) (x : ℕ) : ℕ :=
  if x ∈ S then U x else D x

/-! ### Section 1: Chunked Storage (8 chunks of ≤ 48 elements) for Fast Kernel Reduction -/

private def cycleChunk : Nat → List ℕ
  | 0 => [2, 3, 5, 8, 12, 18, 27, 41, 62, 93, 140, 210, 315, 473, 710, 1065, 1598, 2397, 3596, 5394,
          2697, 1349, 675, 338, 169, 85, 43, 22, 11, 6, 9, 14, 21, 32, 48, 72, 108, 162, 243, 365,
          548, 822, 1233, 1850, 2775, 4163, 6245, 9368]
  | 1 => [4684, 2342, 1171, 586, 293, 147, 74, 37, 19, 10, 15, 23, 35, 53, 80, 120, 180, 270, 405,
          608, 912, 1368, 2052, 3078, 4617, 6926, 10389, 15584, 23376, 35064, 52596, 78894, 118341,
          177512, 266268, 399402, 599103, 898655, 1347983, 2021975, 3032963, 4549445, 6824168,
          10236252, 15354378, 23031567, 34547351, 51821027]
  | 2 => [77731541, 116597312, 174895968, 262343952, 393515928, 590273892, 885410838, 1328116257,
          1992174386, 2988261579, 4482392369, 6723588554, 10085382831, 15128074247, 22692111371,
          34038167057, 51057250586, 76585875879, 114878813819, 172318220729, 258477331094,
          129238665547, 64619332774, 32309666387, 16154833194, 8077416597, 4038708299, 2019354150,
          1009677075, 504838538, 252419269, 126209635, 63104818, 31552409, 15776205, 7888103,
          3944052, 1972026, 986013, 493007, 246504, 123252, 61626, 30813, 15407, 7704, 3852, 1926]
  | 3 => [963, 482, 241, 121, 61, 31, 16, 24, 36, 54, 81, 122, 183, 275, 413, 620, 310, 155, 78, 39,
          20, 30, 45, 68, 102, 153, 230, 115, 58, 29, 44, 66, 99, 149, 224, 336, 504, 756, 1134,
          1701, 2552, 3828, 5742, 8613, 12920, 19380, 29070, 43605]
  | 4 => [65408, 98112, 147168, 220752, 331128, 496692, 745038, 1117557, 1676336, 2514504, 3771756,
          5657634, 8486451, 4243226, 2121613, 1060807, 530404, 265202, 132601, 66301, 33151, 16576,
          8288, 4144, 2072, 1036, 518, 259, 130, 65, 33, 50, 75, 38, 57, 86, 129, 194, 291, 437,
          656, 984, 1476, 2214, 3321, 4982, 7473, 11210]
  | 5 => [16815, 25223, 37835, 56753, 85130, 127695, 191543, 287315, 430973, 646460, 323230, 161615,
          80808, 40404, 20202, 10101, 5051, 2526, 1263, 632, 316, 158, 79, 40, 60, 90, 135, 203,
          305, 458, 687, 1031, 1547, 2321, 3482, 5223, 7835, 11753, 17630, 26445, 39668, 59502,
          89253, 133880, 200820, 301230, 451845, 677768]
  | 6 => [338884, 169442, 84721, 42361, 21181, 10591, 5296, 2648, 1324, 662, 331, 166, 83, 42, 63,
          95, 143, 215, 323, 485, 728, 364, 182, 91, 46, 69, 104, 156, 234, 351, 527, 791, 1187,
          1781, 2672, 4008, 6012, 9018, 13527, 20291, 30437, 45656, 68484, 102726, 51363, 25682,
          12841, 6421]
  | 7 => [3211, 1606, 803, 402, 201, 101, 51, 77, 116, 174, 261, 392, 588, 882, 441, 221, 111, 56,
          84, 126, 189, 284, 426, 639, 959, 1439, 2159, 3239, 4859, 7289, 10934, 16401, 24602,
          12301, 6151, 3076, 1538, 769, 385, 193, 97, 49, 25, 13, 7, 4]
  | _ => []

private def sortedChunk : Nat → List ℕ
  | 0 => [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 25, 27,
          29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 53, 54, 56]
  | 1 => [57, 58, 60, 61, 62, 63, 65, 66, 68, 69, 72, 74, 75, 77, 78, 79, 80, 81, 83, 84, 85, 86,
          90, 91, 93, 95, 97, 99, 101, 102, 104, 108, 111, 115, 116, 120, 121, 122, 126, 129, 130,
          135, 140, 143, 147, 149, 153, 155]
  | 2 => [156, 158, 162, 166, 169, 174, 180, 182, 183, 189, 193, 194, 201, 203, 210, 215, 221, 224,
          230, 234, 241, 243, 259, 261, 270, 275, 284, 291, 293, 305, 310, 315, 316, 323, 331, 336,
          338, 351, 364, 365, 385, 392, 402, 405, 413, 426, 437, 441]
  | 3 => [458, 473, 482, 485, 504, 518, 527, 548, 586, 588, 608, 620, 632, 639, 656, 662, 675, 687,
          710, 728, 756, 769, 791, 803, 822, 882, 912, 959, 963, 984, 1031, 1036, 1065, 1134, 1171,
          1187, 1233, 1263, 1324, 1349, 1368, 1439, 1476, 1538, 1547, 1598, 1606, 1701]
  | 4 => [1781, 1850, 1926, 2052, 2072, 2159, 2214, 2321, 2342, 2397, 2526, 2552, 2648, 2672, 2697,
          2775, 3076, 3078, 3211, 3239, 3321, 3482, 3596, 3828, 3852, 4008, 4144, 4163, 4617, 4684,
          4859, 4982, 5051, 5223, 5296, 5394, 5742, 6012, 6151, 6245, 6421, 6926, 7289, 7473, 7704,
          7835, 8288, 8613]
  | 5 => [9018, 9368, 10101, 10389, 10591, 10934, 11210, 11753, 12301, 12841, 12920, 13527, 15407,
          15584, 16401, 16576, 16815, 17630, 19380, 20202, 20291, 21181, 23376, 24602, 25223, 25682,
          26445, 29070, 30437, 30813, 33151, 35064, 37835, 39668, 40404, 42361, 43605, 45656, 51363,
          52596, 56753, 59502, 61626, 65408, 66301, 68484, 78894, 80808]
  | 6 => [84721, 85130, 89253, 98112, 102726, 118341, 123252, 127695, 132601, 133880, 147168,
          161615, 169442, 177512, 191543, 200820, 220752, 246504, 265202, 266268, 287315, 301230,
          323230, 331128, 338884, 399402, 430973, 451845, 493007, 496692, 530404, 599103, 646460,
          677768, 745038, 898655, 986013, 1060807, 1117557, 1347983, 1676336, 1972026, 2021975,
          2121613, 2514504, 3032963, 3771756, 3944052]
  | 7 => [4243226, 4549445, 5657634, 6824168, 7888103, 8486451, 10236252, 15354378, 15776205,
          23031567, 31552409, 34547351, 51821027, 63104818, 77731541, 116597312, 126209635,
          174895968, 252419269, 262343952, 393515928, 504838538, 590273892, 885410838, 1009677075,
          1328116257, 1992174386, 2019354150, 2988261579, 4038708299, 4482392369, 6723588554,
          8077416597, 10085382831, 15128074247, 16154833194, 22692111371, 32309666387, 34038167057,
          51057250586, 64619332774, 76585875879, 114878813819, 129238665547, 172318220729, 258477331094]
  | _ => []

private def rankChunk : Nat → List ℕ
  | 0 => [0, 1, 3, 6, 10, 15, 23, 35, 52, 72, 90, 110, 127, 145, 162, 176, 189, 201, 214, 227,
          206, 183, 160, 132, 100, 68, 37, 19, 9, 4, 7, 12, 18, 27, 41, 58, 79, 98, 117, 135,
          151, 168, 180, 193, 207, 219, 231, 241]
  | 1 => [221, 200, 178, 152, 124, 92, 59, 31, 16, 8, 13, 20, 29, 45, 64, 83, 102, 120, 139, 154,
          170, 184, 195, 209, 220, 233, 243, 253, 262, 271, 279, 286, 293, 301, 307, 313, 319, 323,
          327, 330, 333, 337, 339, 342, 343, 345, 347, 348]
  | 2 => [350, 351, 353, 355, 356, 358, 359, 361, 362, 364, 366, 367, 369, 370, 372, 374, 375, 377,
          378, 380, 381, 379, 376, 373, 371, 368, 365, 363, 360, 357, 354, 352, 349, 346, 344, 340,
          335, 329, 324, 316, 305, 294, 282, 269, 252, 236, 216, 194]
  | 3 => [172, 146, 116, 84, 51, 26, 14, 21, 30, 46, 65, 85, 104, 121, 140, 155, 126, 95, 62, 33,
          17, 25, 39, 56, 77, 94, 114, 81, 49, 24, 38, 55, 75, 93, 113, 131, 148, 164, 177, 191,
          203, 215, 228, 239, 250, 258, 267, 276]
  | 4 => [283, 291, 298, 304, 311, 317, 322, 326, 328, 332, 334, 338, 341, 336, 331, 325, 318, 306,
          296, 284, 270, 255, 238, 218, 196, 175, 149, 118, 88, 54, 28, 43, 60, 32, 48, 69, 87, 107,
          123, 142, 158, 173, 186, 198, 212, 223, 235, 246]
  | 5 => [256, 264, 272, 280, 289, 295, 302, 308, 314, 320, 310, 299, 287, 274, 259, 242, 224, 202,
          181, 156, 128, 97, 63, 34, 50, 70, 89, 109, 125, 144, 161, 174, 188, 199, 213, 225, 237,
          247, 257, 266, 273, 281, 290, 297, 303, 309, 315, 321]
  | 6 => [312, 300, 288, 275, 261, 244, 226, 204, 182, 159, 130, 99, 66, 36, 53, 73, 91, 111, 129,
          147, 163, 134, 103, 71, 40, 57, 78, 96, 115, 133, 150, 166, 179, 192, 205, 217, 229, 240,
          251, 260, 268, 277, 285, 292, 278, 265, 249, 232]
  | 7 => [210, 190, 167, 138, 108, 76, 44, 61, 82, 101, 119, 137, 153, 169, 143, 112, 80, 47, 67,
          86, 105, 122, 141, 157, 171, 185, 197, 211, 222, 234, 245, 254, 263, 248, 230, 208, 187,
          165, 136, 106, 74, 42, 22, 11, 5, 2]
  | _ => []

private def invRankChunk : Nat → List ℕ
  | 0 => [0, 1, 381, 2, 29, 380, 3, 30, 57, 28, 4, 379, 31, 58, 150, 5, 56, 164, 32, 27, 59, 151,
          378, 6, 173, 165, 149, 33, 222, 60, 152, 55, 225, 163, 263, 7, 301, 26, 174, 166, 312,
          34, 377, 223, 342, 61, 153, 353]
  | 1 => [226, 172, 264, 148, 8, 302, 221, 175, 167, 313, 35, 54, 224, 343, 162, 262, 62, 154, 300,
          354, 25, 227, 265, 311, 9, 303, 376, 176, 341, 168, 314, 36, 352, 171, 344, 63, 147, 155,
          355, 228, 220, 266, 10, 304, 53, 177, 169, 161]
  | 2 => [315, 261, 37, 299, 24, 345, 64, 310, 156, 356, 375, 229, 340, 267, 11, 305, 351, 178, 170,
          316, 146, 38, 219, 346, 65, 157, 357, 230, 52, 268, 160, 12, 260, 306, 298, 179, 23, 317,
          309, 39, 374, 347, 339, 66, 158, 358, 231, 350]
  | 3 => [269, 13, 145, 307, 180, 218, 318, 40, 51, 348, 67, 159, 259, 359, 232, 297, 22, 270, 14,
          308, 181, 373, 319, 338, 41, 349, 68, 360, 144, 233, 271, 217, 15, 182, 50, 320, 42, 258,
          296, 21, 69, 361, 234, 372, 272, 16, 337, 183]
  | 4 => [321, 43, 143, 70, 216, 362, 235, 273, 49, 17, 257, 184, 295, 322, 20, 44, 371, 71, 336,
          363, 236, 274, 18, 185, 142, 323, 215, 45, 72, 48, 364, 237, 256, 275, 294, 19, 186, 324,
          370, 46, 335, 73, 365, 238, 141, 276, 214, 187]
  | 5 => [325, 47, 255, 74, 293, 366, 239, 277, 369, 334, 188, 326, 140, 75, 367, 213, 240, 278,
          189, 254, 327, 292, 76, 368, 241, 333, 279, 190, 328, 139, 212, 77, 242, 280, 253, 291,
          191, 329, 332, 78, 243, 281, 138, 192, 211, 330, 79, 252]
  | 6 => [290, 244, 282, 193, 331, 80, 137, 245, 210, 283, 194, 251, 289, 81, 246, 284, 195, 136,
          209, 82, 247, 285, 250, 196, 288, 83, 248, 286, 135, 197, 208, 84, 249, 287, 198, 85,
          134, 207, 199, 86, 200, 133, 87, 206, 201, 88, 202, 132]
  | 7 => [205, 89, 203, 90, 131, 204, 91, 92, 130, 93, 129, 94, 95, 128, 96, 97, 127, 98, 126, 99,
          100, 125, 101, 102, 124, 103, 104, 123, 105, 122, 106, 107, 121, 108, 109, 120, 110, 119,
          111, 112, 118, 113, 114, 117, 115, 116]
  | _ => []

/-- `i`-th vertex of the 382-vertex counterexample cycle (`O(48)` lookup depth). -/
def cycleAt (i : ℕ) : ℕ := (cycleChunk (i / 48)).getD (i % 48) 0

private def sortedAt (i : ℕ) : ℕ := (sortedChunk (i / 48)).getD (i % 48) 0
private def rankAt (i : ℕ) : ℕ := (rankChunk (i / 48)).getD (i % 48) 0
private def invRankAt (i : ℕ) : ℕ := (invRankChunk (i / 48)).getD (i % 48) 0

/-! ### Section 2: Kernel Verification of Distinctness, Steps, Up-Count, and `3^241 < 2^382` -/

private def checkSortedRange (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all fun d =>
    let i := lo + d
    decide (sortedAt i < sortedAt (i + 1))

private lemma sorted_adj_0 : checkSortedRange 0 96 = true := by decide
private lemma sorted_adj_1 : checkSortedRange 96 192 = true := by decide
private lemma sorted_adj_2 : checkSortedRange 192 288 = true := by decide
private lemma sorted_adj_3 : checkSortedRange 288 381 = true := by decide

private lemma sortedAt_step {i : ℕ} (hi : i < 381) : sortedAt i < sortedAt (i + 1) := by
  have hfrom : ∀ lo hi', checkSortedRange lo hi' = true → lo ≤ i → i < hi' →
      sortedAt i < sortedAt (i + 1) := by
    intro lo hi' hchk hlo hhi
    simp only [checkSortedRange, List.all_eq_true, decide_eq_true_eq] at hchk
    have h := hchk (i - lo) (List.mem_range.mpr (by omega))
    rwa [show lo + (i - lo) = i by omega] at h
  by_cases h1 : i < 96
  · exact hfrom 0 96 sorted_adj_0 (by omega) h1
  · by_cases h2 : i < 192
    · exact hfrom 96 192 sorted_adj_1 (by omega) h2
    · by_cases h3 : i < 288
      · exact hfrom 192 288 sorted_adj_2 (by omega) h3
      · exact hfrom 288 381 sorted_adj_3 (by omega) hi

private lemma sortedAt_strictMono {i j : ℕ} (hij : i < j) (hj : j < 382) :
    sortedAt i < sortedAt j := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases heq : i = j
      · subst heq; exact sortedAt_step (by omega)
      · exact lt_trans (ih (by omega) (by omega)) (sortedAt_step (by omega))

private def checkRankRange (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all fun d =>
    let i := lo + d
    let r := rankAt i
    decide (r < 382) && (invRankAt r == i) && (sortedAt r == cycleAt i)

private lemma rank_0 : checkRankRange 0 96 = true := by decide
private lemma rank_1 : checkRankRange 96 192 = true := by decide
private lemma rank_2 : checkRankRange 192 288 = true := by decide
private lemma rank_3 : checkRankRange 288 382 = true := by decide

private lemma rankAt_spec {i : ℕ} (hi : i < 382) :
    rankAt i < 382 ∧ invRankAt (rankAt i) = i ∧ sortedAt (rankAt i) = cycleAt i := by
  have hfrom : ∀ lo hi', checkRankRange lo hi' = true → lo ≤ i → i < hi' →
      rankAt i < 382 ∧ invRankAt (rankAt i) = i ∧ sortedAt (rankAt i) = cycleAt i := by
    intro lo hi' hchk hlo hhi
    simp only [checkRankRange, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hchk
    have h := hchk (i - lo) (List.mem_range.mpr (by omega))
    rw [show lo + (i - lo) = i by omega] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  by_cases h1 : i < 96
  · exact hfrom 0 96 rank_0 (by omega) h1
  · by_cases h2 : i < 192
    · exact hfrom 96 192 rank_1 (by omega) h2
    · by_cases h3 : i < 288
      · exact hfrom 192 288 rank_2 (by omega) h3
      · exact hfrom 288 382 rank_3 (by omega) hi

/-- All `382` vertices `cycleAt i` (`i : Fin 382`) are pairwise distinct. -/
theorem cycleAt_injective : Function.Injective (fun i : Fin 382 => cycleAt i.val) := by
  intro i j hij
  obtain ⟨hri, hinv_i, hval_i⟩ := rankAt_spec i.isLt
  obtain ⟨hrj, hinv_j, hval_j⟩ := rankAt_spec j.isLt
  have hsort_eq : sortedAt (rankAt i.val) = sortedAt (rankAt j.val) := by
    rw [hval_i, hval_j]; exact hij
  have hrank_eq : rankAt i.val = rankAt j.val := by
    rcases lt_trichotomy (rankAt i.val) (rankAt j.val) with hlt | heq | hgt
    · exact absurd hsort_eq (ne_of_lt (sortedAt_strictMono hlt hrj))
    · exact heq
    · exact absurd hsort_eq (ne_of_gt (sortedAt_strictMono hgt hri))
  exact Fin.ext (by rw [← hinv_i, hrank_eq, hinv_j])

private def checkStepRange (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all fun d =>
    let i := lo + d
    let x := cycleAt i
    let y := cycleAt ((i + 1) % 382)
    decide (2 ≤ x) && (y == U x || y == D x)

private lemma step_0 : checkStepRange 0 96 = true := by decide
private lemma step_1 : checkStepRange 96 192 = true := by decide
private lemma step_2 : checkStepRange 192 288 = true := by decide
private lemma step_3 : checkStepRange 288 382 = true := by decide

/-- Every vertex is `≥ 2` and every step is `U` or `D`. -/
theorem cycleAt_valid_steps (i : Fin 382) :
    2 ≤ cycleAt i.val ∧
    (cycleAt ((i.val + 1) % 382) = U (cycleAt i.val) ∨
     cycleAt ((i.val + 1) % 382) = D (cycleAt i.val)) := by
  have hfrom : ∀ lo hi', checkStepRange lo hi' = true → lo ≤ i.val → i.val < hi' →
      2 ≤ cycleAt i.val ∧
      (cycleAt ((i.val + 1) % 382) = U (cycleAt i.val) ∨
       cycleAt ((i.val + 1) % 382) = D (cycleAt i.val)) := by
    intro lo hi' hchk hlo hhi
    simp only [checkStepRange, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hchk
    have h := hchk (i.val - lo) (List.mem_range.mpr (by omega))
    rwa [show lo + (i.val - lo) = i.val by omega] at h
  by_cases h1 : i.val < 96
  · exact hfrom 0 96 step_0 (by omega) h1
  · by_cases h2 : i.val < 192
    · exact hfrom 96 192 step_1 (by omega) h2
    · by_cases h3 : i.val < 288
      · exact hfrom 192 288 step_2 (by omega) h3
      · exact hfrom 288 382 step_3 (by omega) i.isLt

private def countUpsRange (lo hi : ℕ) : ℕ :=
  (List.range (hi - lo)).countP fun d =>
    let i := lo + d
    cycleAt ((i + 1) % 382) == U (cycleAt i)

private lemma ups_0 : countUpsRange 0 96 = 76 := by decide
private lemma ups_1 : countUpsRange 96 192 = 54 := by decide
private lemma ups_2 : countUpsRange 192 288 = 62 := by decide
private lemma ups_3 : countUpsRange 288 382 = 48 := by decide

private lemma countUpsRange_eq_card (lo hi : ℕ) (hle : lo ≤ hi) (hhi : hi ≤ 382) :
    countUpsRange lo hi =
      (Finset.univ.filter fun i : Fin 382 =>
        lo ≤ i.val ∧ i.val < hi ∧ cycleAt ((i.val + 1) % 382) = U (cycleAt i.val)).card := by
  unfold countUpsRange
  rw [List.countP_eq_length_filter]
  have hnd : ((List.range (hi - lo)).filter (fun d =>
      cycleAt ((lo + d + 1) % 382) == U (cycleAt (lo + d)))).Nodup :=
    (List.nodup_range).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  refine Finset.card_bij (fun (d : ℕ) hd =>
      ⟨lo + d, by
        simp only [List.mem_toFinset, List.mem_filter, List.mem_range] at hd
        omega⟩) ?_ ?_ ?_
  · intro d hd
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq] at hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, by omega, hd.2⟩
  · intro d₁ _ d₂ _ hEq
    have := congrArg Fin.val hEq; dsimp at this; omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨j.val - lo, ?_, Fin.ext (by dsimp; omega)⟩
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq]
    rw [show lo + (j.val - lo) = j.val by omega]
    exact ⟨by omega, hj.2.2⟩

/-- Exact up-step count of the cycle: `a = 240`. -/
theorem cycleAt_up_count :
    (Finset.univ.filter fun i : Fin 382 =>
      cycleAt ((i.val + 1) % 382) = U (cycleAt i.val)).card = 240 := by
  let P : Fin 382 → Prop := fun i => cycleAt ((i.val + 1) % 382) = U (cycleAt i.val)
  let S (lo hi : ℕ) : Finset (Fin 382) :=
    Finset.univ.filter fun i : Fin 382 => lo ≤ i.val ∧ i.val < hi ∧ P i
  have hpart : ∀ a b c : ℕ, a ≤ b → b ≤ c →
      (S a c).card = (S a b).card + (S b c).card := by
    intro a b c hab hbc
    have hunion : S a c = S a b ∪ S b c := by
      ext i; simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hdisj : Disjoint (S a b) (S b c) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2; omega
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hfull : (Finset.univ.filter P) = S 0 382 := by
    ext i; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Nat.zero_le, i.isLt]
  rw [hfull, hpart 0 96 382 (by omega) (by omega), hpart 96 192 382 (by omega) (by omega),
    hpart 192 288 382 (by omega) (by omega)]
  have c0 := countUpsRange_eq_card 0 96 (by omega) (by omega)
  have c1 := countUpsRange_eq_card 96 192 (by omega) (by omega)
  have c2 := countUpsRange_eq_card 192 288 (by omega) (by omega)
  have c3 := countUpsRange_eq_card 288 382 (by omega) (by omega)
  change (S 0 96).card + ((S 96 192).card + ((S 192 288).card + (S 288 382).card)) = 240
  rw [← c0, ← c1, ← c2, ← c3, ups_0, ups_1, ups_2, ups_3]

/-- Exact inequality refuting Vasilyev Question 7.1: `3 ^ 241 < 2 ^ 382 < 3 ^ 242`. -/
theorem ratio_exceeds_three : 3 ^ (240 + 1) < 2 ^ 382 ∧ 2 ^ 382 < 3 ^ (240 + 2) := by
  have h2 : (2 : ℕ) ^ 382 = 2 ^ 191 * 2 ^ 191 := by rw [← pow_add]
  rw [h2]
  constructor <;> decide

/-! ### Section 3: Main Theorem — Primitive Cycle of `T_S` Refuting Question 7.1 -/

/-- The finite set `S` of `240` up-vertices of the counterexample cycle. -/
def counterexampleSet : Finset ℕ :=
  (Finset.univ.filter fun i : Fin 382 =>
    cycleAt ((i.val + 1) % 382) = U (cycleAt i.val)).image (fun i : Fin 382 => cycleAt i.val)

private lemma mem_counterexampleSet_iff (i : Fin 382) :
    cycleAt i.val ∈ counterexampleSet ↔ cycleAt ((i.val + 1) % 382) = U (cycleAt i.val) := by
  unfold counterexampleSet
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hjup, hjeq⟩
    have hji : j = i := cycleAt_injective hjeq
    subst hji; exact hjup
  · intro hup
    exact ⟨i, hup, rfl⟩

private lemma T_counterexample_step (i : Fin 382) :
    T counterexampleSet (cycleAt i.val) = cycleAt ((i.val + 1) % 382) := by
  unfold T
  by_cases hmem : cycleAt i.val ∈ counterexampleSet
  · rw [if_pos hmem]
    exact ((mem_counterexampleSet_iff i).mp hmem).symm
  · rw [if_neg hmem]
    rcases (cycleAt_valid_steps i).2 with hU | hD
    · exact absurd ((mem_counterexampleSet_iff i).mpr hU) hmem
    · exact hD.symm

private lemma T_counterexample_orbit (k : ℕ) :
    (T counterexampleSet)^[k] 2 = cycleAt (k % 382) := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih,
        T_counterexample_step ⟨k % 382, Nat.mod_lt _ (by omega)⟩]
      congr 1; simp [Nat.add_mod]

/-- **Main Theorem (Negative resolution of Vasilyev Question 7.1, arXiv:2611.20344v2):**
There exists a finite subset `S : Finset ℕ`, a cycle length `ℓ = 382`, an up-step count
`a = 240`, and a starting positive integer `x₀ = 2` such that:
1. The orbit `k ↦ (T S)^[k] x₀` has exact primitive period `ℓ = 382` (all `382` points
   in the cycle are positive (`≥ 1`) and pairwise distinct, and `(T S)^[382] x₀ = x₀`),
2. Exactly `a = 240` vertices in the cycle belong to `S` (up-steps), and
3. `3 ^ (a + 1) < 2 ^ ℓ` (refuting `2 ^ ℓ < 3 ^ (a + 1)`). -/
theorem vasilyev_question_7_1_disproof :
    ∃ (S : Finset ℕ) (ℓ a x₀ : ℕ),
      0 < ℓ ∧
      (∀ k : Fin ℓ, 1 ≤ (T S)^[k.val] x₀) ∧
      Function.Injective (fun k : Fin ℓ => (T S)^[k.val] x₀) ∧
      (T S)^[ℓ] x₀ = x₀ ∧
      (Finset.univ.filter fun k : Fin ℓ => (T S)^[k.val] x₀ ∈ S).card = a ∧
      3 ^ (a + 1) < 2 ^ ℓ := by
  refine ⟨counterexampleSet, 382, 240, 2, by omega, ?_, ?_, ?_, ?_, ratio_exceeds_three.1⟩
  · intro k
    rw [T_counterexample_orbit k.val, Nat.mod_eq_of_lt k.isLt]
    have := (cycleAt_valid_steps k).1
    omega
  · intro i j hij
    dsimp only at hij
    rw [T_counterexample_orbit i.val, T_counterexample_orbit j.val,
      Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hij
    exact cycleAt_injective hij
  · rw [T_counterexample_orbit 382]; rfl
  · rw [← cycleAt_up_count]
    apply congrArg Finset.card
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [T_counterexample_orbit k.val, Nat.mod_eq_of_lt k.isLt]
    exact mem_counterexampleSet_iff k

end VasilyevUpDownCycles
