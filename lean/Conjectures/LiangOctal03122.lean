import Mathlib

/-!
# Complete Resolution of Liang's Conjecture 4.1 (`arXiv:2611.29198v1`, Misère Octal Game `0.3122`)

Reference: Kai Liang, "Quaternary games with infinite misère quotients",
arXiv:2611.29198v1 [math.CO] (22 Nov 2026), Section 4.1, Conjecture 4.1.

Verbatim Conjecture 4.1:
> "In `0.3122`, the slice `o(2, 2, x, y)` depends only on `(x mod 7, y mod 7, [|x - y| ≤ 4])`,
> a table of `7 × 7 × 2 = 98` values."

Rules of octal game `0.3122`: from a single heap of size `h`, a player may remove the entire
heap if `h ∈ {1, 2}`, or replace `h` by `h - k` for `k ∈ {1, 3, 4}` when `k < h`. Heaps never
split. Under misère play, the empty position is an `N`-position, and a nonempty position is a
`P`-position iff none of its options is a `P`-position.

We prove:
1. **Literal Disproof (`liang_conjecture_4_1_literal_disproof`):** Without a lower bound on `x, y`,
   Conjecture 4.1 is false: `o(2, 2, 7, 2) = N` while `o(2, 2, 14, 2) = P`, despite both sharing
   key `(0, 2, false)`.
2. **Proof for All `x, y ≥ 3` (`liang_conjecture_4_1_ge_3`):** For all `x, y ≥ 3`,
   `isMisereP (posOf4 2 2 x y) ↔ closedFormP x y = true`, where `closedFormP` depends only on
   `(x % 7, y % 7, decide (Int.natAbs (x - y) ≤ 4))`.
-/

namespace LiangOctal03122

/-! ### Section 1: Exact Definition of Octal Game `0.3122` and Misère Play -/

/-- One legal move in octal game `0.3122` on a finite multiset of positive heaps. -/
inductive Step03122 : Multiset ℕ → Multiset ℕ → Prop
  | remove (s : Multiset ℕ) (h : ℕ) (hh : h = 1 ∨ h = 2) :
      Step03122 (h ::ₘ s) s
  | sub (s : Multiset ℕ) (h k : ℕ) (hk : k = 1 ∨ k = 3 ∨ k = 4) (hlt : k < h) :
      Step03122 (h ::ₘ s) ((h - k) ::ₘ s)

lemma Step03122.sum_lt {s t : Multiset ℕ} (h : Step03122 s t) : t.sum < s.sum := by
  cases h with
  | remove s h hh =>
      rw [Multiset.sum_cons]
      omega
  | sub s h k hk hlt =>
      rw [Multiset.sum_cons, Multiset.sum_cons]
      omega

/-- Exact misère `P`-position predicate: the empty position is `N`, and a nonempty position
is `P` iff every legal option is `N` (not `P`). -/
def isMisereP (s : Multiset ℕ) : Prop :=
  s ≠ 0 ∧ ∀ t, Step03122 s t → ¬ isMisereP t
termination_by s.sum
decreasing_by exact Step03122.sum_lt ‹_›

lemma isMisereP_iff (s : Multiset ℕ) :
    isMisereP s ↔ s ≠ 0 ∧ ∀ t, Step03122 s t → ¬ isMisereP t := by
  rw [isMisereP]

/-- Insert a heap if nonzero (`0` denotes an absent heap). -/
def addHeap (h : ℕ) (s : Multiset ℕ) : Multiset ℕ :=
  if h = 0 then s else h ::ₘ s

/-- The multiset of positive heaps among `{a, b, c, d}`. -/
def posOf4 (a b c d : ℕ) : Multiset ℕ :=
  addHeap a (addHeap b (addHeap c (addHeap d 0)))

private lemma addHeap_comm (x y : ℕ) (s : Multiset ℕ) :
    addHeap x (addHeap y s) = addHeap y (addHeap x s) := by
  unfold addHeap
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy, Multiset.cons_swap]

private lemma posOf4_sum (a b c d : ℕ) : (posOf4 a b c d).sum = a + b + c + d := by
  unfold posOf4 addHeap
  split_ifs <;> simp <;> omega

private lemma posOf4_eq_zero_iff (a b c d : ℕ) :
    posOf4 a b c d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  unfold posOf4 addHeap
  split_ifs <;> simp_all

/-! ### Section 2: Canonical 4-Tuple Representation and Closed Family `F` -/

/-- Compare-swap placing the larger value first. -/
def swapMax (x y : ℕ) : ℕ × ℕ :=
  if y ≤ x then (x, y) else (y, x)

/-- 4-element descending sort via a 5-comparator network. -/
def canon4 (a b c d : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let p1 := swapMax a b
  let p2 := swapMax c d
  let p3 := swapMax p1.1 p2.1
  let p4 := swapMax p1.2 p2.2
  let p5 := swapMax p3.2 p4.1
  (p3.1, p5.1, p5.2, p4.2)

private lemma addHeap_swapMax (x y : ℕ) (s : Multiset ℕ) :
    addHeap (swapMax x y).1 (addHeap (swapMax x y).2 s) = addHeap x (addHeap y s) := by
  unfold swapMax
  split_ifs
  · rfl
  · exact addHeap_comm y x s

private lemma posOf4_canon4 (a b c d : ℕ) :
    let q := canon4 a b c d
    posOf4 q.1 q.2.1 q.2.2.1 q.2.2.2 = posOf4 a b c d := by
  dsimp only [canon4]
  unfold posOf4
  calc addHeap (swapMax (swapMax a b).1 (swapMax c d).1).1
        (addHeap (swapMax (swapMax (swapMax a b).1 (swapMax c d).1).2
            (swapMax (swapMax a b).2 (swapMax c d).2).1).1
          (addHeap (swapMax (swapMax (swapMax a b).1 (swapMax c d).1).2
              (swapMax (swapMax a b).2 (swapMax c d).2).1).2
            (addHeap (swapMax (swapMax a b).2 (swapMax c d).2).2 0)))
      = addHeap (swapMax (swapMax a b).1 (swapMax c d).1).1
          (addHeap (swapMax (swapMax a b).1 (swapMax c d).1).2
            (addHeap (swapMax (swapMax a b).2 (swapMax c d).2).1
              (addHeap (swapMax (swapMax a b).2 (swapMax c d).2).2 0))) := by
          rw [addHeap_swapMax]
    _ = addHeap (swapMax a b).1 (addHeap (swapMax c d).1
          (addHeap (swapMax a b).2 (addHeap (swapMax c d).2 0))) := by
          rw [addHeap_swapMax, addHeap_swapMax]
    _ = addHeap (swapMax a b).1 (addHeap (swapMax a b).2
          (addHeap (swapMax c d).1 (addHeap (swapMax c d).2 0))) := by
          rw [addHeap_comm (swapMax c d).1 (swapMax a b).2]
    _ = addHeap a (addHeap b (addHeap c (addHeap d 0))) := by
          rw [addHeap_swapMax, addHeap_swapMax]

private lemma canon4_sorted (a b c d : ℕ) :
    let q := canon4 a b c d
    q.2.2.2 ≤ q.2.2.1 ∧ q.2.2.1 ≤ q.2.1 ∧ q.2.1 ≤ q.1 := by
  dsimp only [canon4, swapMax]
  split_ifs <;> omega

private lemma canon4_of_sorted {a b c d : ℕ} (h1 : b ≤ a) (h2 : c ≤ b) (h3 : d ≤ c) :
    canon4 a b c d = (a, b, c, d) := by
  dsimp only [canon4, swapMax]
  split_ifs <;> ext <;> dsimp only <;> omega

private lemma canon4_hi_lo {a b c d : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : c ≤ 2) (hd : d ≤ 2) :
    canon4 a b c d = (max a b, min a b, max c d, min c d) := by
  by_cases hab : b ≤ a <;> by_cases hcd : d ≤ c
  · rw [max_eq_left hab, min_eq_right hab, max_eq_left hcd, min_eq_right hcd]
    dsimp only [canon4, swapMax]; split_ifs <;> ext <;> dsimp only <;> omega
  · rw [max_eq_left hab, min_eq_right hab, max_eq_right (by omega : c ≤ d), min_eq_left (by omega : c ≤ d)]
    dsimp only [canon4, swapMax]; split_ifs <;> ext <;> dsimp only <;> omega
  · rw [max_eq_right (by omega : a ≤ b), min_eq_left (by omega : a ≤ b), max_eq_left hcd, min_eq_right hcd]
    dsimp only [canon4, swapMax]; split_ifs <;> ext <;> dsimp only <;> omega
  · rw [max_eq_right (by omega : a ≤ b), min_eq_left (by omega : a ≤ b),
        max_eq_right (by omega : c ≤ d), min_eq_left (by omega : c ≤ d)]
    dsimp only [canon4, swapMax]; split_ifs <;> ext <;> dsimp only <;> omega

private lemma canon4_small_preserved {a b c d : ℕ} (hc : c ≤ 2) (hd : d ≤ 2) :
    let q := canon4 a b c d
    q.2.2.1 ≤ 2 ∧ q.2.2.2 ≤ 2 := by
  dsimp only [canon4, swapMax]
  split_ifs <;> omega

/-- All legal single-heap replacements for a single heap `h` (`0` means removed). -/
def heapMoves (h : ℕ) : List ℕ :=
  (if h = 1 ∨ h = 2 then [0] else []) ++
  (if 1 < h then [h - 1] else []) ++
  (if 3 < h then [h - 3] else []) ++
  (if 4 < h then [h - 4] else [])

private lemma mem_heapMoves_iff (h r : ℕ) :
    r ∈ heapMoves h ↔
      (r = 0 ∧ (h = 1 ∨ h = 2)) ∨
      (∃ k, (k = 1 ∨ k = 3 ∨ k = 4) ∧ k < h ∧ r = h - k) := by
  unfold heapMoves
  simp only [List.mem_append]
  constructor
  · intro hm
    rcases hm with ((hm | hm) | hm) | hm
    · split_ifs at hm with hh
      · simp at hm; left; exact ⟨hm, hh⟩
      · simp at hm
    · split_ifs at hm with hh
      · simp at hm; right; exact ⟨1, Or.inl rfl, hh, hm⟩
      · simp at hm
    · split_ifs at hm with hh
      · simp at hm; right; exact ⟨3, Or.inr (Or.inl rfl), hh, hm⟩
      · simp at hm
    · split_ifs at hm with hh
      · simp at hm; right; exact ⟨4, Or.inr (Or.inr rfl), hh, hm⟩
      · simp at hm
  · rintro (⟨rfl, hh⟩ | ⟨k, rfl | rfl | rfl, hlt, rfl⟩)
    · left; left; left; rw [if_pos hh]; simp
    · left; left; right; rw [if_pos hlt]; simp
    · left; right; rw [if_pos hlt]; simp
    · right; rw [if_pos hlt]; simp

/-- Explicit list of canonicalized options of `(h1, h2, h3, h4)`. -/
def options4 (h1 h2 h3 h4 : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (heapMoves h1).map (fun r => canon4 r h2 h3 h4) ++
  (heapMoves h2).map (fun r => canon4 h1 r h3 h4) ++
  (heapMoves h3).map (fun r => canon4 h1 h2 r h4) ++
  (heapMoves h4).map (fun r => canon4 h1 h2 h3 r)

private lemma mem_addHeap_iff (x h : ℕ) (s : Multiset ℕ) :
    x ∈ addHeap h s ↔ (h ≠ 0 ∧ x = h) ∨ x ∈ s := by
  unfold addHeap
  split_ifs with h0
  · simp [h0]
  · simp [h0]

private lemma step_addHeap_of_heapMove {h r : ℕ} {s : Multiset ℕ} (hr : r ∈ heapMoves h) :
    Step03122 (addHeap h s) (addHeap r s) := by
  rcases (mem_heapMoves_iff h r).mp hr with ⟨rfl, hh⟩ | ⟨k, hk, hlt, rfl⟩
  · have hne : h ≠ 0 := by omega
    unfold addHeap; rw [if_neg hne, if_pos rfl]
    exact Step03122.remove s h hh
  · have hne : h ≠ 0 := by omega
    have hrne : h - k ≠ 0 := by omega
    unfold addHeap; rw [if_neg hne, if_neg hrne]
    exact Step03122.sub s h k hk hlt

private lemma step_posOf4_iff (h1 h2 h3 h4 : ℕ) (t : Multiset ℕ) :
    Step03122 (posOf4 h1 h2 h3 h4) t ↔
      ∃ q ∈ options4 h1 h2 h3 h4, t = posOf4 q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  constructor
  · intro hstep
    have hcases : ∀ (a b c d : ℕ) (h : ℕ) (s : Multiset ℕ),
        posOf4 a b c d = h ::ₘ s →
        (a = h ∧ s = addHeap b (addHeap c (addHeap d 0))) ∨
        (b = h ∧ s = addHeap a (addHeap c (addHeap d 0))) ∨
        (c = h ∧ s = addHeap a (addHeap b (addHeap d 0))) ∨
        (d = h ∧ s = addHeap a (addHeap b (addHeap c 0))) := by
      intro a b c d h s heq
      have hmem : h ∈ posOf4 a b c d := by rw [heq]; exact Multiset.mem_cons_self h s
      unfold posOf4 at heq hmem
      rw [mem_addHeap_iff, mem_addHeap_iff, mem_addHeap_iff, mem_addHeap_iff] at hmem
      rcases hmem with ⟨ha, rfl⟩ | ⟨hb, rfl⟩ | ⟨hc, rfl⟩ | ⟨hd, rfl⟩ | hbot
      · left; refine ⟨rfl, ?_⟩
        unfold addHeap at heq; rw [if_neg ha] at heq
        exact Multiset.cons_inj_right _ |>.mp heq.symm
      · right; left; refine ⟨rfl, ?_⟩
        rw [addHeap_comm a h] at heq
        unfold addHeap at heq; rw [if_neg hb] at heq
        exact Multiset.cons_inj_right _ |>.mp heq.symm
      · right; right; left; refine ⟨rfl, ?_⟩
        rw [addHeap_comm b h, addHeap_comm a h] at heq
        unfold addHeap at heq; rw [if_neg hc] at heq
        exact Multiset.cons_inj_right _ |>.mp heq.symm
      · right; right; right; refine ⟨rfl, ?_⟩
        rw [addHeap_comm c h, addHeap_comm b h, addHeap_comm a h] at heq
        unfold addHeap at heq; rw [if_neg hd] at heq
        exact Multiset.cons_inj_right _ |>.mp heq.symm
      · exact absurd hbot (Multiset.notMem_zero h)
    generalize hsrc : posOf4 h1 h2 h3 h4 = src at hstep
    cases hstep with
    | remove _ h hh =>
        have h0 : 0 ∈ heapMoves h := (mem_heapMoves_iff h 0).mpr (Or.inl ⟨rfl, hh⟩)
        rcases hcases h1 h2 h3 h4 h t hsrc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨canon4 0 h2 h3 h4, ?_, ?_⟩
          · simp only [options4, List.mem_append, List.mem_map]; left; left; left; exact ⟨0, h0, rfl⟩
          · rw [posOf4_canon4]; unfold posOf4; simp [addHeap]
        · refine ⟨canon4 h1 0 h3 h4, ?_, ?_⟩
          · simp only [options4, List.mem_append, List.mem_map]; left; left; right; exact ⟨0, h0, rfl⟩
          · rw [posOf4_canon4]; unfold posOf4; rw [addHeap_comm h1 0]; simp [addHeap]
        · refine ⟨canon4 h1 h2 0 h4, ?_, ?_⟩
          · simp only [options4, List.mem_append, List.mem_map]; left; right; exact ⟨0, h0, rfl⟩
          · rw [posOf4_canon4]; unfold posOf4; rw [addHeap_comm h2 0, addHeap_comm h1 0]; simp [addHeap]
        · refine ⟨canon4 h1 h2 h3 0, ?_, ?_⟩
          · simp only [options4, List.mem_append, List.mem_map]; right; exact ⟨0, h0, rfl⟩
          · rw [posOf4_canon4]; unfold posOf4; simp [addHeap]
    | @sub s h k hk hlt =>
        have hr : h - k ∈ heapMoves h := (mem_heapMoves_iff h (h - k)).mpr (Or.inr ⟨k, hk, hlt, rfl⟩)
        have hrne : h - k ≠ 0 := by omega
        rcases hcases h1 h2 h3 h4 h s hsrc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨canon4 (h1 - k) h2 h3 h4, ?_, ?_⟩
          · simp only [options4, List.mem_append, List.mem_map]; left; left; left; exact ⟨h1 - k, hr, rfl⟩
          · rw [posOf4_canon4]; unfold posOf4; simp [addHeap, hrne]
        · refine ⟨canon4 h1 (h2 - k) h3 h4, ?_, ?_⟩
          · simp only [options4, List.mem_append, List.mem_map]; left; left; right; exact ⟨h2 - k, hr, rfl⟩
          · rw [posOf4_canon4]; unfold posOf4; rw [addHeap_comm h1 (h2 - k)]; simp [addHeap, hrne]
        · refine ⟨canon4 h1 h2 (h3 - k) h4, ?_, ?_⟩
          · simp only [options4, List.mem_append, List.mem_map]; left; right; exact ⟨h3 - k, hr, rfl⟩
          · rw [posOf4_canon4]; unfold posOf4; rw [addHeap_comm h2 (h3 - k), addHeap_comm h1 (h3 - k)]; simp [addHeap, hrne]
        · refine ⟨canon4 h1 h2 h3 (h4 - k), ?_, ?_⟩
          · simp only [options4, List.mem_append, List.mem_map]; right; exact ⟨h4 - k, hr, rfl⟩
          · rw [posOf4_canon4]; unfold posOf4
            rw [addHeap_comm h3 (h4 - k), addHeap_comm h2 (h4 - k), addHeap_comm h1 (h4 - k)]
            simp [addHeap, hrne]
  · rintro ⟨q, hq, rfl⟩
    simp only [options4, List.mem_append, List.mem_map] at hq
    rcases hq with ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩
    · rw [posOf4_canon4]; exact step_addHeap_of_heapMove hr
    · rw [posOf4_canon4]; unfold posOf4
      rw [addHeap_comm h1 h2, addHeap_comm h1 r]
      exact step_addHeap_of_heapMove hr
    · rw [posOf4_canon4]; unfold posOf4
      rw [addHeap_comm h2 h3, addHeap_comm h1 h3, addHeap_comm h2 r, addHeap_comm h1 r]
      exact step_addHeap_of_heapMove hr
    · rw [posOf4_canon4]; unfold posOf4
      rw [addHeap_comm h3 h4, addHeap_comm h2 h4, addHeap_comm h1 h4,
        addHeap_comm h3 r, addHeap_comm h2 r, addHeap_comm h1 r]
      exact step_addHeap_of_heapMove hr

/-! ### Section 3: Exact Finite Table (`h1 ≤ 31`) and Reduction Operator `Φ` -/

/-- Index `0..5` for the six sorted pairs `(h3, h4)` with `h4 ≤ h3 ≤ 2`. -/
def smallIdx (h3 h4 : ℕ) : ℕ :=
  if h3 = 0 then 0
  else if h3 = 1 then (if h4 = 0 then 1 else 2)
  else if h4 = 0 then 3 else if h4 = 1 then 4 else 5

/-- Bitmask table of exact misère `P`-positions for `h1 ≤ 31`, `h2 ≤ h1`, `(h3, h4)` indexed by `smallIdx`. -/
def tableMasks (s : ℕ) : Array ℕ :=
  match s with
  | 0 => #[0, 1, 4, 9, 2, 40, 66, 20, 321, 532, 1065, 642, 5160, 8514, 2068, 41281,
           68116, 136233, 82562, 660520, 1089858, 264212, 5284161, 8718868, 17437737,
           10568322, 84546600, 139501890, 33818644, 676372801, 1116015124, 2232030249]
  | 1 => #[1, 2, 0, 2, 17, 4, 9, 160, 10, 32, 322, 2065, 644, 1033, 20640, 1034,
           4128, 41282, 264209, 82564, 132105, 2642080, 132106, 528416, 5284162,
           33818641, 10568324, 16909321, 338186400, 16909322, 67637280, 676372802]
  | 2 => #[0, 1, 4, 9, 2, 40, 66, 20, 321, 532, 1065, 642, 5160, 8514, 2068, 41281,
           68116, 136233, 82562, 660520, 1089858, 264212, 5284161, 8718868, 17437737,
           10568322, 84546600, 139501890, 33818644, 676372801, 1116015124, 2232030249]
  | 3 => #[0, 0, 1, 4, 8, 2, 32, 65, 20, 265, 532, 1064, 2114, 4256, 8513, 16916,
           34057, 68116, 136232, 272450, 544928, 1089857, 2179604, 4359433, 8718868,
           17437736, 34875458, 69750944, 139501889, 279003668, 558007561, 1116015124]
  | 4 => #[0, 0, 2, 0, 0, 17, 4, 10, 128, 66, 128, 4, 17, 2564, 1034, 4256,
           8258, 16512, 41220, 17, 330244, 132106, 266400, 1056834, 2113664, 5284100,
           17, 42273284, 16909322, 33820832, 135274562, 270549120]
  | _ => #[1, 2, 4, 9, 20, 40, 66, 128, 321, 532, 1065, 2562, 5160, 8514, 16404, 41281,
           68116, 136233, 328322, 660520, 1089858, 2099220, 5284161, 8718868, 17437737,
           42025602, 84546600, 139501890, 268699668, 676372801, 1116015124, 2232030249]

/-- Direct O(1) table lookup for `h1 ≤ 31`. -/
def tableLookup (h1 h2 h3 h4 : ℕ) : Bool :=
  Nat.testBit ((tableMasks (smallIdx h3 h4)).getD h1 0) h2

/-- Closed-form two-stage period-7 reduction `ρ(h1, h2)` with thresholds `D = 13, G = 5, C = 8`. -/
def reducePair (h1 h2 : ℕ) : ℕ × ℕ :=
  let a := if 20 ≤ h2 then h1 - 7 * ((h2 - 13) / 7) else h1
  let b := if 20 ≤ h2 then h2 - 7 * ((h2 - 13) / 7) else h2
  if 12 ≤ a - b ∧ 15 ≤ a then
    let j := min ((a - b - 5) / 7) ((a - 8) / 7)
    (a - 7 * j, b)
  else (a, b)

/-- Claimed misère `P`-position indicator `Φ` on canonical positions in `F`. -/
def phi (h1 h2 h3 h4 : ℕ) : Bool :=
  let r := reducePair h1 h2
  tableLookup r.1 r.2 h3 h4

/-! ### Section 4: Lemma 1 (Shift Invariance) and Lemma 2 (Translation) -/

/-- **Lemma 1(a):** Diagonal 7-shift invariance of `reducePair`. -/
lemma reducePair_diag_shift {h1 h2 : ℕ} (h20 : 20 ≤ h2) (_hle : h2 ≤ h1) :
    reducePair h1 h2 = reducePair (h1 - 7) (h2 - 7) := by
  unfold reducePair
  by_cases h27 : 20 ≤ h2 - 7
  · have hdiv : (h2 - 13) / 7 = (h2 - 7 - 13) / 7 + 1 := by omega
    have h1eq : h1 - 7 * ((h2 - 13) / 7) = h1 - 7 - 7 * ((h2 - 7 - 13) / 7) := by omega
    have h2eq : h2 - 7 * ((h2 - 13) / 7) = h2 - 7 - 7 * ((h2 - 7 - 13) / 7) := by omega
    simp only [if_pos h20, if_pos h27, h1eq, h2eq]
  · have hdiv : (h2 - 13) / 7 = 1 := by omega
    simp only [if_pos h20, if_neg h27, hdiv, Nat.mul_one]

/-- **Lemma 1(b):** Top-heap 7-shift invariance of `reducePair`. -/
lemma reducePair_top_shift {h1 h2 : ℕ} (hgap : 12 ≤ h1 - h2) (h15 : 15 ≤ h1) :
    reducePair h1 h2 = reducePair (h1 - 7) h2 := by
  unfold reducePair
  by_cases h20 : 20 ≤ h2
  · simp only [if_pos h20]
    set i := (h2 - 13) / 7
    have hi_le : 7 * i ≤ h2 - 13 := Nat.mul_div_le (h2 - 13) 7
    have hb_ge : 13 ≤ h2 - 7 * i := by omega
    have h1_sub : h1 - 7 - 7 * i = (h1 - 7 * i) - 7 := by omega
    set a := h1 - 7 * i
    set b := h2 - 7 * i
    have hab : 12 ≤ a - b := by omega
    have ha15 : 15 ≤ a := by omega
    rw [h1_sub, if_pos ⟨hab, ha15⟩]
    by_cases hcond2 : 12 ≤ (a - 7) - b ∧ 15 ≤ a - 7
    · rw [if_pos hcond2]
      have hmin : min ((a - b - 5) / 7) ((a - 8) / 7) =
          min (((a - 7) - b - 5) / 7) (((a - 7) - 8) / 7) + 1 := by omega
      exact Prod.ext (by omega) rfl
    · rw [if_neg hcond2]
      have hmin : min ((a - b - 5) / 7) ((a - 8) / 7) = 1 := by omega
      exact Prod.ext (by omega) rfl
  · simp only [if_neg h20]
    rw [if_pos (And.intro hgap h15)]
    by_cases hcond2 : 12 ≤ (h1 - 7) - h2 ∧ 15 ≤ h1 - 7
    · rw [if_pos hcond2]
      have hmin : min ((h1 - h2 - 5) / 7) ((h1 - 8) / 7) =
          min (((h1 - 7) - h2 - 5) / 7) (((h1 - 7) - 8) / 7) + 1 := by omega
      exact Prod.ext (by omega) rfl
    · rw [if_neg hcond2]
      have hmin : min ((h1 - h2 - 5) / 7) ((h1 - 8) / 7) = 1 := by omega
      exact Prod.ext (by omega) rfl

lemma phi_diag_shift {h1 h2 h3 h4 : ℕ} (h20 : 20 ≤ h2) (hle : h2 ≤ h1) :
    phi h1 h2 h3 h4 = phi (h1 - 7) (h2 - 7) h3 h4 := by
  unfold phi; rw [reducePair_diag_shift h20 hle]

lemma phi_top_shift {h1 h2 h3 h4 : ℕ} (hgap : 12 ≤ h1 - h2) (h15 : 15 ≤ h1) :
    phi h1 h2 h3 h4 = phi (h1 - 7) h2 h3 h4 := by
  unfold phi; rw [reducePair_top_shift hgap h15]

/-- Recursion checker for `phi` at a single canonical position `(h1, h2, h3, h4)`. -/
def checkPos (h1 h2 h3 h4 : ℕ) : Bool :=
  let want := (h1 != 0 || h2 != 0 || h3 != 0 || h4 != 0) &&
    (options4 h1 h2 h3 h4).all (fun q => !(phi q.1 q.2.1 q.2.2.1 q.2.2.2))
  phi h1 h2 h3 h4 == want

/-- Check `checkPos` on all canonical `W`-positions with `lo ≤ h1 ≤ hi`. -/
def checkWindowRange (lo hi : ℕ) : Bool :=
  let smalls : List (ℕ × ℕ) := [(0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2)]
  (List.range (hi + 1 - lo)).all fun d =>
    let h1 := lo + d
    (List.range (min (h1 + 1) 24)).all fun h2 =>
      if h1 - h2 < 16 ∨ h1 < 19 then
        smalls.all fun (h3, h4) =>
          if h3 ≤ h2 then checkPos h1 h2 h3 h4 else true
      else true

private lemma checkW_0_9 : checkWindowRange 0 9 = true := by decide
private lemma checkW_10_19 : checkWindowRange 10 19 = true := by decide
private lemma checkW_20_29 : checkWindowRange 20 29 = true := by decide
private lemma checkW_30_38 : checkWindowRange 30 38 = true := by decide

private lemma checkWindowRange_sound {lo hi h1 h2 h3 h4 : ℕ}
    (hcheck : checkWindowRange lo hi = true)
    (hlo : lo ≤ h1) (hhi : h1 ≤ hi)
    (h12 : h2 ≤ h1) (h23 : h3 ≤ h2) (h34 : h4 ≤ h3) (hc : h3 ≤ 2)
    (hW1 : h2 < 24) (hW2 : h1 - h2 < 16 ∨ h1 < 19) :
    checkPos h1 h2 h3 h4 = true := by
  simp only [checkWindowRange, List.all_eq_true] at hcheck
  have hd : h1 - lo ∈ List.range (hi + 1 - lo) := List.mem_range.mpr (by omega)
  have hstep1 := hcheck (h1 - lo) hd
  rw [show lo + (h1 - lo) = h1 by omega] at hstep1
  have hh2 : h2 ∈ List.range (min (h1 + 1) 24) := List.mem_range.mpr (by omega)
  have hstep2 := hstep1 h2 hh2
  rw [if_pos hW2] at hstep2
  have hsm : (h3, h4) ∈ ([(0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2)] : List (ℕ × ℕ)) := by
    have : h3 = 0 ∨ h3 = 1 ∨ h3 = 2 := by omega
    rcases this with rfl | rfl | rfl
    · have : h4 = 0 := by omega
      subst this; simp
    · have : h4 = 0 ∨ h4 = 1 := by omega
      rcases this with rfl | rfl <;> simp
    · have : h4 = 0 ∨ h4 = 1 ∨ h4 = 2 := by omega
      rcases this with rfl | rfl | rfl <;> simp
  rw [List.all_eq_true] at hstep2
  have hstep3 := hstep2 (h3, h4) hsm
  simpa [if_pos h23] using hstep3

private lemma checkPos_of_window {h1 h2 h3 h4 : ℕ}
    (h12 : h2 ≤ h1) (h23 : h3 ≤ h2) (h34 : h4 ≤ h3) (hc : h3 ≤ 2)
    (hW1 : h2 < 24) (hW2 : h1 - h2 < 16 ∨ h1 < 19) :
    checkPos h1 h2 h3 h4 = true := by
  have h38 : h1 ≤ 38 := by omega
  by_cases ha : h1 ≤ 9
  · exact checkWindowRange_sound checkW_0_9 (by omega) ha h12 h23 h34 hc hW1 hW2
  · by_cases hb : h1 ≤ 19
    · exact checkWindowRange_sound checkW_10_19 (by omega) hb h12 h23 h34 hc hW1 hW2
    · by_cases hc' : h1 ≤ 29
      · exact checkWindowRange_sound checkW_20_29 (by omega) hc' h12 h23 h34 hc hW1 hW2
      · exact checkWindowRange_sound checkW_30_38 (by omega) h38 h12 h23 h34 hc hW1 hW2

private lemma heapMoves_shift {h : ℕ} (hge : 12 ≤ h) :
    heapMoves (h - 7) = (heapMoves h).map (fun r => r - 7) := by
  have h1 : heapMoves (h - 7) = [h - 7 - 1, h - 7 - 3, h - 7 - 4] := by
    unfold heapMoves
    rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    rfl
  have h2 : heapMoves h = [h - 1, h - 3, h - 4] := by
    unfold heapMoves
    rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    rfl
  rw [h1, h2]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  exact ⟨by omega, by omega, by omega⟩

/-- **Lemma 2 + Induction:** `checkPos h1 h2 h3 h4 = true` holds for EVERY canonical position in `F`. -/
lemma checkPos_all :
    ∀ (s h1 h2 h3 h4 : ℕ), h1 + h2 = s →
      h2 ≤ h1 → h3 ≤ h2 → h4 ≤ h3 → h3 ≤ 2 →
      checkPos h1 h2 h3 h4 = true := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro h1 h2 h3 h4 hsum h12 h23 h34 hc
    by_cases h24 : 24 ≤ h2
    · -- Case A (diagonal translation): compare with `(h1 - 7, h2 - 7, h3, h4)`!
      have hprev := ih (h1 - 7 + (h2 - 7)) (by omega) (h1 - 7) (h2 - 7) h3 h4 rfl
        (by omega) (by omega) h34 hc
      have hphi_eq : phi h1 h2 h3 h4 = phi (h1 - 7) (h2 - 7) h3 h4 :=
        phi_diag_shift (by omega) h12
      have hne1 : (h1 != 0 || h2 != 0 || h3 != 0 || h4 != 0) = true := by
        have : h1 ≠ 0 := by omega
        simp [this]
      have hne2 : ((h1 - 7) != 0 || (h2 - 7) != 0 || h3 != 0 || h4 != 0) = true := by
        have : h1 - 7 ≠ 0 := by omega
        simp [this]
      have hall_eq :
          (options4 h1 h2 h3 h4).all (fun q => !(phi q.1 q.2.1 q.2.2.1 q.2.2.2)) =
          (options4 (h1 - 7) (h2 - 7) h3 h4).all (fun q => !(phi q.1 q.2.1 q.2.2.1 q.2.2.2)) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true, Bool.not_eq_true']
        have hcanon_diag : ∀ a b c d : ℕ, 20 ≤ a → 20 ≤ b → c ≤ 2 → d ≤ 2 →
            let q := canon4 a b c d
            let q' := canon4 (a - 7) (b - 7) c d
            q' = (q.1 - 7, q.2.1 - 7, q.2.2.1, q.2.2.2) ∧ 20 ≤ q.2.1 ∧ q.2.1 ≤ q.1 := by
          intro a b c d ha hb hc' hd'
          dsimp only
          rw [canon4_hi_lo (by omega) (by omega) hc' hd', canon4_hi_lo (by omega) (by omega) hc' hd']
          refine ⟨Prod.ext (by dsimp only; omega) (Prod.ext (by dsimp only; omega) (Prod.ext rfl rfl)), by dsimp only; omega, by dsimp only; omega⟩
        constructor
        · intro hall q hq
          simp only [options4, List.mem_append, List.mem_map] at hq
          rcases hq with ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩
          · rw [heapMoves_shift (by omega), List.mem_map] at hr
            rcases hr with ⟨r0, hr0, rfl⟩
            have hr0_ge : 20 ≤ r0 := by
              rcases (mem_heapMoves_iff h1 r0).mp hr0 with ⟨_, hh⟩ | ⟨k, hk, _, rfl⟩ <;> omega
            obtain ⟨heq, hq20, hqle⟩ := hcanon_diag r0 h2 h3 h4 hr0_ge (by omega) hc (by omega)
            rw [heq, ← phi_diag_shift hq20 hqle]
            exact hall _ (by simp only [options4, List.mem_append, List.mem_map]; left; left; left; exact ⟨r0, hr0, rfl⟩)
          · rw [heapMoves_shift (by omega), List.mem_map] at hr
            rcases hr with ⟨r0, hr0, rfl⟩
            have hr0_ge : 20 ≤ r0 := by
              rcases (mem_heapMoves_iff h2 r0).mp hr0 with ⟨_, hh⟩ | ⟨k, hk, _, rfl⟩ <;> omega
            obtain ⟨heq, hq20, hqle⟩ := hcanon_diag h1 r0 h3 h4 (by omega) hr0_ge hc (by omega)
            rw [heq, ← phi_diag_shift hq20 hqle]
            exact hall _ (by simp only [options4, List.mem_append, List.mem_map]; left; left; right; exact ⟨r0, hr0, rfl⟩)
          · have hr_le : r ≤ 2 := by
              rcases (mem_heapMoves_iff h3 r).mp hr with ⟨rfl, _⟩ | ⟨k, hk, _, rfl⟩ <;> omega
            obtain ⟨heq, hq20, hqle⟩ := hcanon_diag h1 h2 r h4 (by omega) (by omega) hr_le (by omega)
            rw [heq, ← phi_diag_shift hq20 hqle]
            exact hall _ (by simp only [options4, List.mem_append, List.mem_map]; left; right; exact ⟨r, hr, rfl⟩)
          · have hr_le : r ≤ 2 := by
              rcases (mem_heapMoves_iff h4 r).mp hr with ⟨rfl, _⟩ | ⟨k, hk, _, rfl⟩ <;> omega
            obtain ⟨heq, hq20, hqle⟩ := hcanon_diag h1 h2 h3 r (by omega) (by omega) hc hr_le
            rw [heq, ← phi_diag_shift hq20 hqle]
            exact hall _ (by simp only [options4, List.mem_append, List.mem_map]; right; exact ⟨r, hr, rfl⟩)
        · intro hall q hq
          simp only [options4, List.mem_append, List.mem_map] at hq
          rcases hq with ((⟨r0, hr0, rfl⟩ | ⟨r0, hr0, rfl⟩) | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩
          · have hr0_ge : 20 ≤ r0 := by
              rcases (mem_heapMoves_iff h1 r0).mp hr0 with ⟨_, hh⟩ | ⟨k, hk, _, rfl⟩ <;> omega
            obtain ⟨heq, hq20, hqle⟩ := hcanon_diag r0 h2 h3 h4 hr0_ge (by omega) hc (by omega)
            rw [phi_diag_shift hq20 hqle]
            have hmem : canon4 (r0 - 7) (h2 - 7) h3 h4 ∈ options4 (h1 - 7) (h2 - 7) h3 h4 := by
              simp only [options4, List.mem_append, List.mem_map]; left; left; left
              exact ⟨r0 - 7, by rw [heapMoves_shift (by omega)]; exact List.mem_map_of_mem hr0, rfl⟩
            simpa [heq] using hall _ hmem
          · have hr0_ge : 20 ≤ r0 := by
              rcases (mem_heapMoves_iff h2 r0).mp hr0 with ⟨_, hh⟩ | ⟨k, hk, _, rfl⟩ <;> omega
            obtain ⟨heq, hq20, hqle⟩ := hcanon_diag h1 r0 h3 h4 (by omega) hr0_ge hc (by omega)
            rw [phi_diag_shift hq20 hqle]
            have hmem : canon4 (h1 - 7) (r0 - 7) h3 h4 ∈ options4 (h1 - 7) (h2 - 7) h3 h4 := by
              simp only [options4, List.mem_append, List.mem_map]; left; left; right
              exact ⟨r0 - 7, by rw [heapMoves_shift (by omega)]; exact List.mem_map_of_mem hr0, rfl⟩
            simpa [heq] using hall _ hmem
          · have hr_le : r ≤ 2 := by
              rcases (mem_heapMoves_iff h3 r).mp hr with ⟨rfl, _⟩ | ⟨k, hk, _, rfl⟩ <;> omega
            obtain ⟨heq, hq20, hqle⟩ := hcanon_diag h1 h2 r h4 (by omega) (by omega) hr_le (by omega)
            rw [phi_diag_shift hq20 hqle]
            have hmem : canon4 (h1 - 7) (h2 - 7) r h4 ∈ options4 (h1 - 7) (h2 - 7) h3 h4 := by
              simp only [options4, List.mem_append, List.mem_map]; left; right; exact ⟨r, hr, rfl⟩
            simpa [heq] using hall _ hmem
          · have hr_le : r ≤ 2 := by
              rcases (mem_heapMoves_iff h4 r).mp hr with ⟨rfl, _⟩ | ⟨k, hk, _, rfl⟩ <;> omega
            obtain ⟨heq, hq20, hqle⟩ := hcanon_diag h1 h2 h3 r (by omega) (by omega) hc hr_le
            rw [phi_diag_shift hq20 hqle]
            have hmem : canon4 (h1 - 7) (h2 - 7) h3 r ∈ options4 (h1 - 7) (h2 - 7) h3 h4 := by
              simp only [options4, List.mem_append, List.mem_map]; right; exact ⟨r, hr, rfl⟩
            simpa [heq] using hall _ hmem
      unfold checkPos at hprev ⊢
      rw [hphi_eq, hne1, hall_eq]
      simpa [hne2] using hprev
    · by_cases htop : 16 ≤ h1 - h2 ∧ 19 ≤ h1
      · -- Case B (top-heap translation): compare with `(h1 - 7, h2, h3, h4)`!
        have hprev := ih (h1 - 7 + h2) (by omega) (h1 - 7) h2 h3 h4 rfl
          (by omega) h23 h34 hc
        have hphi_eq : phi h1 h2 h3 h4 = phi (h1 - 7) h2 h3 h4 :=
          phi_top_shift (by omega) (by omega)
        have hne1 : (h1 != 0 || h2 != 0 || h3 != 0 || h4 != 0) = true := by
          have : h1 ≠ 0 := by omega
          simp [this]
        have hne2 : ((h1 - 7) != 0 || h2 != 0 || h3 != 0 || h4 != 0) = true := by
          have : h1 - 7 ≠ 0 := by omega
          simp [this]
        have hcanon_top : ∀ a b c d : ℕ, 15 ≤ a → 12 ≤ a - b → c ≤ 2 → d ≤ 2 →
            let q := canon4 a b c d
            let q' := canon4 (a - 7) b c d
            q' = (q.1 - 7, q.2.1, q.2.2.1, q.2.2.2) ∧ 12 ≤ q.1 - q.2.1 ∧ 15 ≤ q.1 := by
          intro a b c d ha hgap hc' hd'
          dsimp only
          have h1 : canon4 a b c d = (a, max b (max c d), max (min b (max c d)) (min c d), min (min b (max c d)) (min c d)) := by
            dsimp only [canon4, swapMax]; split_ifs <;> ext <;> dsimp only <;> omega
          have h2 : canon4 (a - 7) b c d = (a - 7, max b (max c d), max (min b (max c d)) (min c d), min (min b (max c d)) (min c d)) := by
            dsimp only [canon4, swapMax]; split_ifs <;> ext <;> dsimp only <;> omega
          rw [h1, h2]
          refine ⟨rfl, by dsimp only; omega, by dsimp only; omega⟩
        have hall_eq :
            (options4 h1 h2 h3 h4).all (fun q => !(phi q.1 q.2.1 q.2.2.1 q.2.2.2)) =
            (options4 (h1 - 7) h2 h3 h4).all (fun q => !(phi q.1 q.2.1 q.2.2.1 q.2.2.2)) := by
          apply Bool.eq_iff_iff.mpr
          simp only [List.all_eq_true, Bool.not_eq_true']
          constructor
          · intro hall q hq
            simp only [options4, List.mem_append, List.mem_map] at hq
            rcases hq with ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩
            · rw [heapMoves_shift (by omega), List.mem_map] at hr
              rcases hr with ⟨r0, hr0, rfl⟩
              have hr0_ge : 15 ≤ r0 ∧ 12 ≤ r0 - h2 := by
                rcases (mem_heapMoves_iff h1 r0).mp hr0 with ⟨_, hh⟩ | ⟨k, hk, _, rfl⟩ <;> omega
              obtain ⟨heq, hqg, hq15⟩ := hcanon_top r0 h2 h3 h4 hr0_ge.1 hr0_ge.2 hc (by omega)
              rw [heq, ← phi_top_shift hqg hq15]
              exact hall _ (by simp only [options4, List.mem_append, List.mem_map]; left; left; left; exact ⟨r0, hr0, rfl⟩)
            · have hr_le : r ≤ h2 := by
                rcases (mem_heapMoves_iff h2 r).mp hr with ⟨rfl, _⟩ | ⟨k, hk, _, rfl⟩ <;> omega
              obtain ⟨heq, hqg, hq15⟩ := hcanon_top h1 r h3 h4 (by omega) (by omega) hc (by omega)
              rw [heq, ← phi_top_shift hqg hq15]
              exact hall _ (by simp only [options4, List.mem_append, List.mem_map]; left; left; right; exact ⟨r, hr, rfl⟩)
            · have hr_le : r ≤ 2 := by
                rcases (mem_heapMoves_iff h3 r).mp hr with ⟨rfl, _⟩ | ⟨k, hk, _, rfl⟩ <;> omega
              obtain ⟨heq, hqg, hq15⟩ := hcanon_top h1 h2 r h4 (by omega) (by omega) hr_le (by omega)
              rw [heq, ← phi_top_shift hqg hq15]
              exact hall _ (by simp only [options4, List.mem_append, List.mem_map]; left; right; exact ⟨r, hr, rfl⟩)
            · have hr_le : r ≤ 2 := by
                rcases (mem_heapMoves_iff h4 r).mp hr with ⟨rfl, _⟩ | ⟨k, hk, _, rfl⟩ <;> omega
              obtain ⟨heq, hqg, hq15⟩ := hcanon_top h1 h2 h3 r (by omega) (by omega) hc hr_le
              rw [heq, ← phi_top_shift hqg hq15]
              exact hall _ (by simp only [options4, List.mem_append, List.mem_map]; right; exact ⟨r, hr, rfl⟩)
          · intro hall q hq
            simp only [options4, List.mem_append, List.mem_map] at hq
            rcases hq with ((⟨r0, hr0, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩
            · have hr0_ge : 15 ≤ r0 ∧ 12 ≤ r0 - h2 := by
                rcases (mem_heapMoves_iff h1 r0).mp hr0 with ⟨_, hh⟩ | ⟨k, hk, _, rfl⟩ <;> omega
              obtain ⟨heq, hqg, hq15⟩ := hcanon_top r0 h2 h3 h4 hr0_ge.1 hr0_ge.2 hc (by omega)
              rw [phi_top_shift hqg hq15]
              have hmem : canon4 (r0 - 7) h2 h3 h4 ∈ options4 (h1 - 7) h2 h3 h4 := by
                simp only [options4, List.mem_append, List.mem_map]; left; left; left
                exact ⟨r0 - 7, by rw [heapMoves_shift (by omega)]; exact List.mem_map_of_mem hr0, rfl⟩
              simpa [heq] using hall _ hmem
            · have hr_le : r ≤ h2 := by
                rcases (mem_heapMoves_iff h2 r).mp hr with ⟨rfl, _⟩ | ⟨k, hk, _, rfl⟩ <;> omega
              obtain ⟨heq, hqg, hq15⟩ := hcanon_top h1 r h3 h4 (by omega) (by omega) hc (by omega)
              rw [phi_top_shift hqg hq15]
              have hmem : canon4 (h1 - 7) r h3 h4 ∈ options4 (h1 - 7) h2 h3 h4 := by
                simp only [options4, List.mem_append, List.mem_map]; left; left; right; exact ⟨r, hr, rfl⟩
              simpa [heq] using hall _ hmem
            · have hr_le : r ≤ 2 := by
                rcases (mem_heapMoves_iff h3 r).mp hr with ⟨rfl, _⟩ | ⟨k, hk, _, rfl⟩ <;> omega
              obtain ⟨heq, hqg, hq15⟩ := hcanon_top h1 h2 r h4 (by omega) (by omega) hr_le (by omega)
              rw [phi_top_shift hqg hq15]
              have hmem : canon4 (h1 - 7) h2 r h4 ∈ options4 (h1 - 7) h2 h3 h4 := by
                simp only [options4, List.mem_append, List.mem_map]; left; right; exact ⟨r, hr, rfl⟩
              simpa [heq] using hall _ hmem
            · have hr_le : r ≤ 2 := by
                rcases (mem_heapMoves_iff h4 r).mp hr with ⟨rfl, _⟩ | ⟨k, hk, _, rfl⟩ <;> omega
              obtain ⟨heq, hqg, hq15⟩ := hcanon_top h1 h2 h3 r (by omega) (by omega) hc hr_le
              rw [phi_top_shift hqg hq15]
              have hmem : canon4 (h1 - 7) h2 h3 r ∈ options4 (h1 - 7) h2 h3 h4 := by
                simp only [options4, List.mem_append, List.mem_map]; right; exact ⟨r, hr, rfl⟩
              simpa [heq] using hall _ hmem
        unfold checkPos at hprev ⊢
        rw [hphi_eq, hne1, hall_eq]
        simpa [hne2] using hprev
      · -- Case C: inside the finite window `W`!
        exact checkPos_of_window h12 h23 h34 hc (by omega) (by omega)

/-- **Exact Soundness (`Φ = o` on all of `F`):**
For every canonical `(h1, h2, h3, h4)` in `F`, `isMisereP (posOf4 h1 h2 h3 h4) ↔ phi h1 h2 h3 h4 = true`. -/
theorem phi_iff_isMisereP :
    ∀ (s h1 h2 h3 h4 : ℕ), h1 + h2 + h3 + h4 = s →
      h2 ≤ h1 → h3 ≤ h2 → h4 ≤ h3 → h3 ≤ 2 →
      (isMisereP (posOf4 h1 h2 h3 h4) ↔ phi h1 h2 h3 h4 = true) := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro h1 h2 h3 h4 hsum h12 h23 h34 hc
    have hchk := checkPos_all (h1 + h2) h1 h2 h3 h4 rfl h12 h23 h34 hc
    unfold checkPos at hchk
    rw [beq_iff_eq] at hchk
    have hne_iff : posOf4 h1 h2 h3 h4 ≠ 0 ↔ (((h1 ≠ 0 ∨ h2 ≠ 0) ∨ h3 ≠ 0) ∨ h4 ≠ 0) := by
      rw [ne_eq, posOf4_eq_zero_iff]; tauto
    rw [isMisereP_iff, hchk, hne_iff]
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne,
      List.all_eq_true, Bool.not_eq_true']
    refine and_congr Iff.rfl ?_
    constructor
    · intro hall q hq
      have hstep : Step03122 (posOf4 h1 h2 h3 h4) (posOf4 q.1 q.2.1 q.2.2.1 q.2.2.2) :=
        (step_posOf4_iff h1 h2 h3 h4 _).mpr ⟨q, hq, rfl⟩
      have hlt : q.1 + q.2.1 + q.2.2.1 + q.2.2.2 < s := by
        have := hstep.sum_lt
        rw [posOf4_sum, posOf4_sum] at this; omega
      have hq_in : q.2.2.2 ≤ q.2.2.1 ∧ q.2.2.1 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.2.2.1 ≤ 2 := by
        simp only [options4, List.mem_append, List.mem_map] at hq
        rcases hq with ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩
        · have hs := canon4_sorted r h2 h3 h4
          have hsm := canon4_small_preserved (a := r) (b := h2) (c := h3) (d := h4) hc (by omega)
          exact ⟨hs.1, hs.2.1, hs.2.2, hsm.1⟩
        · have hs := canon4_sorted h1 r h3 h4
          have hsm := canon4_small_preserved (a := h1) (b := r) (c := h3) (d := h4) hc (by omega)
          exact ⟨hs.1, hs.2.1, hs.2.2, hsm.1⟩
        · have hr2 : r ≤ 2 := by
            rcases (mem_heapMoves_iff h3 r).mp hr with ⟨rfl, _⟩ | ⟨k, _, _, rfl⟩ <;> omega
          have hs := canon4_sorted h1 h2 r h4
          have hsm := canon4_small_preserved (a := h1) (b := h2) (c := r) (d := h4) hr2 (by omega)
          exact ⟨hs.1, hs.2.1, hs.2.2, hsm.1⟩
        · have hr2 : r ≤ 2 := by
            rcases (mem_heapMoves_iff h4 r).mp hr with ⟨rfl, _⟩ | ⟨k, _, _, rfl⟩ <;> omega
          have hs := canon4_sorted h1 h2 h3 r
          have hsm := canon4_small_preserved (a := h1) (b := h2) (c := h3) (d := r) hc hr2
          exact ⟨hs.1, hs.2.1, hs.2.2, hsm.1⟩
      have hiff := ih _ hlt q.1 q.2.1 q.2.2.1 q.2.2.2 rfl hq_in.2.2.1 hq_in.2.1 hq_in.1 hq_in.2.2.2
      have hnot := hall _ hstep
      cases hval : phi q.1 q.2.1 q.2.2.1 q.2.2.2
      · rfl
      · exact absurd (hiff.mpr hval) hnot
    · intro hall t hstep
      obtain ⟨q, hq, rfl⟩ := (step_posOf4_iff h1 h2 h3 h4 t).mp hstep
      have hlt : q.1 + q.2.1 + q.2.2.1 + q.2.2.2 < s := by
        have := hstep.sum_lt
        rw [posOf4_sum, posOf4_sum] at this; omega
      have hq_in : q.2.2.2 ≤ q.2.2.1 ∧ q.2.2.1 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.2.2.1 ≤ 2 := by
        simp only [options4, List.mem_append, List.mem_map] at hq
        rcases hq with ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩
        · have hs := canon4_sorted r h2 h3 h4
          have hsm := canon4_small_preserved (a := r) (b := h2) (c := h3) (d := h4) hc (by omega)
          exact ⟨hs.1, hs.2.1, hs.2.2, hsm.1⟩
        · have hs := canon4_sorted h1 r h3 h4
          have hsm := canon4_small_preserved (a := h1) (b := r) (c := h3) (d := h4) hc (by omega)
          exact ⟨hs.1, hs.2.1, hs.2.2, hsm.1⟩
        · have hr2 : r ≤ 2 := by
            rcases (mem_heapMoves_iff h3 r).mp hr with ⟨rfl, _⟩ | ⟨k, _, _, rfl⟩ <;> omega
          have hs := canon4_sorted h1 h2 r h4
          have hsm := canon4_small_preserved (a := h1) (b := h2) (c := r) (d := h4) hr2 (by omega)
          exact ⟨hs.1, hs.2.1, hs.2.2, hsm.1⟩
        · have hr2 : r ≤ 2 := by
            rcases (mem_heapMoves_iff h4 r).mp hr with ⟨rfl, _⟩ | ⟨k, _, _, rfl⟩ <;> omega
          have hs := canon4_sorted h1 h2 h3 r
          have hsm := canon4_small_preserved (a := h1) (b := h2) (c := h3) (d := r) hc hr2
          exact ⟨hs.1, hs.2.1, hs.2.2, hsm.1⟩
      have hiff := ih _ hlt q.1 q.2.1 q.2.2.1 q.2.2.2 rfl hq_in.2.2.1 hq_in.2.1 hq_in.1 hq_in.2.2.2
      rw [hiff, hall q hq]
      decide

/-! ### Section 5: Main Theorems — Literal Disproof and Sharp `x, y ≥ 3` Proof -/

/-- Exact 98-entry closed form for `o(2, 2, x, y)` when `x, y ≥ 3`, depending solely on
`(x % 7, y % 7, [|x - y| ≤ 4])`. -/
def closedFormKey (r1 r2 : ℕ) (nearDiag : Bool) : Bool :=
  let base :=
    (r1 == 1 && r2 == 1) || (r1 == 2 && r2 == 2) || (r1 == 3 && r2 == 3) ||
    (r1 == 5 && r2 == 5) || (r1 == 6 && r2 == 6) ||
    (r1 == 1 && r2 == 6) || (r1 == 6 && r2 == 1) ||
    (r1 == 2 && r2 == 4) || (r1 == 4 && r2 == 2) ||
    (r1 == 3 && r2 == 5) || (r1 == 5 && r2 == 3)
  let extra :=
    if nearDiag then (r1 == 0 && r2 == 0) || (r1 == 4 && r2 == 4)
    else (r1 == 0 && r2 == 4) || (r1 == 4 && r2 == 0)
  base || extra

def closedFormP (x y : ℕ) : Bool :=
  closedFormKey (x % 7) (y % 7) (decide (x - y ≤ 4 ∧ y - x ≤ 4))

private lemma checkCanonicalClosedForm :
    (List.range 31).all (fun x =>
      (List.range (x + 1)).all (fun y =>
        if 3 ≤ y then
          tableLookup x y 2 2 == closedFormP x y
        else true)) = true := by decide

/-- **Theorem 1 (Literal Disproof of Liang Conjecture 4.1):**
Without a lower bound on `x, y`, the slice `o(2, 2, x, y)` does NOT depend only on
`(x % 7, y % 7, [|x - y| ≤ 4])`: `o(2, 2, 7, 2) = N` while `o(2, 2, 14, 2) = P`, even though
`(7, 2)` and `(14, 2)` have identical key `(0, 2, false)`. -/
theorem liang_conjecture_4_1_literal_disproof :
    7 % 7 = 14 % 7 ∧
    ¬ (7 - 2 ≤ 4 ∧ 2 - 7 ≤ 4) ∧
    ¬ (14 - 2 ≤ 4 ∧ 2 - 14 ≤ 4) ∧
    ¬ isMisereP (posOf4 2 2 7 2) ∧
    isMisereP (posOf4 2 2 14 2) := by
  have hpos7 : posOf4 2 2 7 2 = posOf4 7 2 2 2 := by
    have := posOf4_canon4 2 2 7 2
    simpa [canon4, swapMax] using this.symm
  have hpos14 : posOf4 2 2 14 2 = posOf4 14 2 2 2 := by
    have := posOf4_canon4 2 2 14 2
    simpa [canon4, swapMax] using this.symm
  have h7 := phi_iff_isMisereP 13 7 2 2 2 rfl (by omega) (by omega) (by omega) (by omega)
  have h14 := phi_iff_isMisereP 20 14 2 2 2 rfl (by omega) (by omega) (by omega) (by omega)
  refine ⟨rfl, by omega, by omega, ?_, ?_⟩
  · rw [hpos7, h7]; decide
  · rw [hpos14, h14]; decide

/-- **Theorem 2 (Complete Proof of Liang Conjecture 4.1 for all `x, y ≥ 3`):**
For all integers `x, y ≥ 3`, `o(2, 2, x, y) = P` iff `closedFormKey (x % 7) (y % 7) [|x - y| ≤ 4] = true`. -/
theorem liang_conjecture_4_1_ge_3 {x y : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) :
    isMisereP (posOf4 2 2 x y) ↔
      closedFormKey (x % 7) (y % 7) (decide (x - y ≤ 4 ∧ y - x ≤ 4)) = true := by
  have hsymm : ∀ a b : ℕ, 3 ≤ a → 3 ≤ b → b ≤ a →
      (isMisereP (posOf4 a b 2 2) ↔ closedFormP a b = true) := by
    intro a b ha hb hba
    rw [phi_iff_isMisereP (a + b + 2 + 2) a b 2 2 rfl hba (by omega) (by omega) (by omega)]
    unfold phi
    set r := reducePair a b
    have hr_props : 3 ≤ r.2 ∧ r.2 ≤ r.1 ∧ r.1 ≤ 30 ∧
        r.1 % 7 = a % 7 ∧ r.2 % 7 = b % 7 ∧
        (r.1 - r.2 ≤ 4 ↔ a - b ≤ 4) := by
      dsimp only [r, reducePair]
      by_cases h20 : 20 ≤ b
      · simp only [if_pos h20]
        set i := (b - 13) / 7
        have hi1 : 7 * i ≤ b - 13 := Nat.mul_div_le (b - 13) 7
        have hi2 : b - 13 < 7 * i + 7 := by omega
        set a1 := a - 7 * i
        set b1 := b - 7 * i
        have hb1_lo : 13 ≤ b1 := by omega
        have hb1_hi : b1 ≤ 19 := by omega
        have ha1_mod : a1 % 7 = a % 7 := by omega
        have hb1_mod : b1 % 7 = b % 7 := by omega
        have hdiff1 : a1 - b1 = a - b := by omega
        by_cases hcond : 12 ≤ a1 - b1 ∧ 15 ≤ a1
        · rw [if_pos hcond]
          set j := min ((a1 - b1 - 5) / 7) ((a1 - 8) / 7)
          have hj1 : 7 * j ≤ a1 - b1 - 5 := by
            have : j ≤ (a1 - b1 - 5) / 7 := min_le_left _ _
            have := Nat.mul_div_le (a1 - b1 - 5) 7
            omega
          have hj2 : 7 * j ≤ a1 - 8 := by
            have : j ≤ (a1 - 8) / 7 := min_le_right _ _
            have := Nat.mul_div_le (a1 - 8) 7
            omega
          have hj_hi : a1 - 7 * j ≤ 30 := by
            rcases min_cases ((a1 - b1 - 5) / 7) ((a1 - 8) / 7) with ⟨hmin, _⟩ | ⟨hmin, _⟩
            · have : a1 - b1 - 5 < 7 * ((a1 - b1 - 5) / 7) + 7 := by omega
              omega
            · have : a1 - 8 < 7 * ((a1 - 8) / 7) + 7 := by omega
              omega
          refine ⟨by omega, by omega, hj_hi, by omega, hb1_mod, by omega⟩
        · rw [if_neg hcond]
          refine ⟨by omega, by omega, by omega, ha1_mod, hb1_mod, by omega⟩
      · simp only [if_neg h20]
        by_cases hcond : 12 ≤ a - b ∧ 15 ≤ a
        · rw [if_pos hcond]
          set j := min ((a - b - 5) / 7) ((a - 8) / 7)
          have hj1 : 7 * j ≤ a - b - 5 := by
            have : j ≤ (a - b - 5) / 7 := min_le_left _ _
            have := Nat.mul_div_le (a - b - 5) 7
            omega
          have hj2 : 7 * j ≤ a - 8 := by
            have : j ≤ (a - 8) / 7 := min_le_right _ _
            have := Nat.mul_div_le (a - 8) 7
            omega
          have hj_hi : a - 7 * j ≤ 30 := by
            rcases min_cases ((a - b - 5) / 7) ((a - 8) / 7) with ⟨hmin, _⟩ | ⟨hmin, _⟩
            · have : a - b - 5 < 7 * ((a - b - 5) / 7) + 7 := by omega
              omega
            · have : a - 8 < 7 * ((a - 8) / 7) + 7 := by omega
              omega
          refine ⟨by omega, by omega, hj_hi, by omega, rfl, by omega⟩
        · rw [if_neg hcond]
          refine ⟨by omega, by omega, by omega, rfl, rfl, Iff.rfl⟩
    have hchk := checkCanonicalClosedForm
    simp only [List.all_eq_true] at hchk
    have h1 := hchk r.1 (List.mem_range.mpr (by omega)) r.2 (List.mem_range.mpr (by omega))
    rw [if_pos hr_props.1, beq_iff_eq] at h1
    rw [h1]
    unfold closedFormP
    have hdec : decide (r.1 - r.2 ≤ 4 ∧ r.2 - r.1 ≤ 4) = decide (a - b ≤ 4 ∧ b - a ≤ 4) := by
      apply decide_eq_decide.mpr
      have h01 : r.2 - r.1 = 0 := by omega
      have h02 : b - a = 0 := by omega
      rw [h01, h02]
      simp [hr_props.2.2.2.2.2]
    rw [hr_props.2.2.2.1, hr_props.2.2.2.2.1, hdec]
  have hkey_comm : ∀ a b : Fin 7, ∀ f : Bool,
      closedFormKey a.val b.val f = closedFormKey b.val a.val f := by decide
  by_cases hxy : y ≤ x
  · have hpos : posOf4 2 2 x y = posOf4 x y 2 2 := by
      have := posOf4_canon4 2 2 x y
      have hc : canon4 2 2 x y = (x, y, 2, 2) := by
        dsimp only [canon4, swapMax]; split_ifs <;> ext <;> dsimp only <;> omega
      rw [hc] at this; exact this.symm
    rw [hpos]
    exact hsymm x y hx hy hxy
  · have hpos : posOf4 2 2 x y = posOf4 y x 2 2 := by
      have := posOf4_canon4 2 2 x y
      have hc : canon4 2 2 x y = (y, x, 2, 2) := by
        dsimp only [canon4, swapMax]; split_ifs <;> ext <;> dsimp only <;> omega
      rw [hc] at this; exact this.symm
    rw [hpos, hsymm y x hy hx (by omega)]
    unfold closedFormP
    rw [hkey_comm ⟨y % 7, Nat.mod_lt y (by omega)⟩ ⟨x % 7, Nat.mod_lt x (by omega)⟩,
      show decide (y - x ≤ 4 ∧ x - y ≤ 4) =
        decide (x - y ≤ 4 ∧ y - x ≤ 4) by apply decide_eq_decide.mpr; exact and_comm]

end LiangOctal03122
