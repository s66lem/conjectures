import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic

/-!
# Proof of Conjecture 1 of Easlick (`arXiv:2610.40321v2`)

In *Computer-Assisted Results for $n$-Sided Non-Transitive Dice Taking Face Values in $[n]$*
(`arXiv:2610.40321v2`, November 2026), Terry Easlick defines the directed graph $G_n$ whose
vertices are all non-standard $n$-sided dice with face values in $\{1, \dots, n\}$ (represented
as non-decreasing $n$-tuples) and whose directed edges $D_{\mathbf{x}} \to D_{\mathbf{y}}$
record a **minimal** winning advantage strictly greater than $1/2$:
$$\sum_{i=1}^n \sum_{j=1}^n \mathbf{1}_{\{x_i > y_j\}} = \left\lfloor \frac{n^2}{2} \right\rfloor + 1.$$

Easlick proved by exhaustive search (Theorem 1) that $G_3, G_4, G_5$ are acyclic and $G_6$ has
maximum directed cycle length $6$ (with two unique $6$-cycles), and posed:

**Conjecture 1 (`arXiv:2610.40321v2`).** *$n = 6$ is the largest $n \ge 3$ such that the set of
non-standard $n$-sided dice admits a non-transitive cycle of maximum length $n$ with uniform and
minimal winning advantage.*

We prove that every integer $n \ge 7$ admits a simple directed cycle of length $\ge n + 1$ in
$G_n$ (so its maximum cycle length strictly exceeds $n$), settling Conjecture 1 when combined
with Easlick's Theorem 1 for $3 \le n \le 6$:
- For every odd $n \ge 11$, an explicit 3-die zipper family yields a simple cycle of length
  $3(n - 7) \ge n + 1$ in $G_n$ (`odd_cycle_exists`).
- For every even $n \ge 16$, an explicit 3-die zipper family yields a simple cycle of length
  $3(n - 10) \ge n + 1$ in $G_n$ (`even_cycle_exists`).
- For the six remaining small values $n \in \{7, 8, 9, 10, 12, 14\}$, explicit simple cycles of
  length $n + 1$ are verified directly in the Lean kernel (`cycle_7` .. `cycle_14`).
- Combined in `easlick_conjecture1`, every $n \ge 7$ has a simple cycle of length $\ge n + 1$
  in $G_n$. We also verify the $6$-cycles at $n = 6$ (`n6_has_cycle_6`) and generalize Easlick's
  involutive antiautomorphism (Prollary 1) to all $n \ge 3$ (`flipDie_antiautomorphism`).

All proofs use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) with zero
`sorry` and zero `native_decide`.
-/

namespace EaslickNontransitiveDice

/-- A non-standard `n`-sided die taking face values in `{1, ..., n}`, stored in
non-decreasing order (Easlick Definition 1). -/
@[ext]
structure Die (n : ℕ) where
  faces : List ℕ
  len_eq : faces.length = n
  in_range : ∀ x ∈ faces, 1 ≤ x ∧ x ≤ n
  sorted : faces.Pairwise (· ≤ ·)

/-- Pairwise strict-win count `∑_{a ∈ xs} ∑_{b ∈ ys} 1_{a > b}`. -/
def wins (xs ys : List ℕ) : ℕ :=
  (xs.map fun a => ys.countP (fun b => decide (a > b))).sum

/-- Minimal winning-pair count strictly exceeding `n^2 / 2` (Easlick Eq. (5)). -/
def minAdvTarget (n : ℕ) : ℕ := n ^ 2 / 2 + 1

/-- Directed edge `u → v` in Easlick's minimal-advantage graph `G_n`. -/
def MinAdvEdge (n : ℕ) (u v : Die n) : Prop :=
  wins u.faces v.faces = minAdvTarget n

/-- A simple non-transitive directed cycle of length `k ≥ 3` in `G_n` with uniform and
minimal winning advantage (Easlick Definition 2). -/
def IsMinAdvCycle (n : ℕ) (cyc : List (Die n)) : Prop :=
  3 ≤ cyc.length ∧
  cyc.Nodup ∧
  ∀ i : Fin cyc.length,
    MinAdvEdge n (cyc.get i)
      (cyc.get ⟨(i.1 + 1) % cyc.length, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.2)⟩)

/-! ### Threshold and Double-Sum Equivalence -/

theorem minAdvTarget_gt_half (n : ℕ) : n ^ 2 < 2 * minAdvTarget n := by
  unfold minAdvTarget; omega

theorem minAdvTarget_le_of_gt_half (n w : ℕ) (hw : n ^ 2 < 2 * w) : minAdvTarget n ≤ w := by
  unfold minAdvTarget; omega

private lemma countP_eq_card_fin (ys : List ℕ) (p : ℕ → Bool) :
    ys.countP p = ((Finset.univ : Finset (Fin ys.length)).filter (fun j => p (ys.get j))).card := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    rw [List.countP_cons, ih]
    simp only [Finset.card_filter]
    change (∑ i : Fin ys.length, if p (ys.get i) = true then 1 else 0) +
        (if p y = true then 1 else 0) =
      ∑ i : Fin (ys.length + 1), if p ((y :: ys).get i) = true then 1 else 0
    rw [Fin.sum_univ_succ]
    simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
      Fin.val_succ, List.getElem_cons_succ]
    exact Nat.add_comm _ _

private lemma sum_map_eq_sum_fin (xs : List ℕ) (f : ℕ → ℕ) :
    (xs.map f).sum = ∑ i : Fin xs.length, f (xs.get i) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, ih]
    change f x + ∑ i : Fin xs.length, f (xs.get i) =
      ∑ i : Fin (xs.length + 1), f ((x :: xs).get i)
    rw [Fin.sum_univ_succ]
    rfl

/-- Exact equivalence between `wins d₁.faces d₂.faces` and the cardinality of winning
face-index pairs `{(i, j) ∈ Fin n × Fin n | d₁[i] > d₂[j]}`. -/
theorem wins_eq_card_pairs {n : ℕ} (d₁ d₂ : Die n) :
    wins d₁.faces d₂.faces =
      ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p => d₁.faces.get (p.1.cast d₁.len_eq.symm) >
                  d₂.faces.get (p.2.cast d₂.len_eq.symm))).card := by
  unfold wins
  rw [sum_map_eq_sum_fin]
  have h1 : ∀ i : Fin d₁.faces.length,
      d₂.faces.countP (fun b => decide (d₁.faces.get i > b)) =
        ((Finset.univ : Finset (Fin d₂.faces.length)).filter
          (fun j => d₁.faces.get i > d₂.faces.get j)).card := by
    intro i
    rw [countP_eq_card_fin]
    congr 1; ext j; simp
  simp_rw [h1]
  have heq : (Finset.univ : Finset (Fin n × Fin n)) =
      (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)) := rfl
  rw [heq, Finset.card_filter, Finset.sum_product]
  refine Fintype.sum_equiv (finCongr d₁.len_eq) _ _ ?_
  intro i
  rw [Finset.card_filter]
  refine Fintype.sum_equiv (finCongr d₂.len_eq) _ _ ?_
  intro j
  simp [finCongr]

/-! ### Algebraic Helpers for `wins` and `List.replicate` Blocks -/

lemma wins_append_left (xs₁ xs₂ ys : List ℕ) :
    wins (xs₁ ++ xs₂) ys = wins xs₁ ys + wins xs₂ ys := by
  simp [wins, List.map_append, List.sum_append]

lemma wins_append_right (xs ys₁ ys₂ : List ℕ) :
    wins xs (ys₁ ++ ys₂) = wins xs ys₁ + wins xs ys₂ := by
  induction xs with
  | nil => simp [wins]
  | cons a xs ih =>
    simp only [wins, List.map_cons, List.sum_cons, List.countP_append] at ih ⊢
    omega

lemma wins_replicate_left (k v : ℕ) (ys : List ℕ) :
    wins (List.replicate k v) ys = k * ys.countP (fun b => decide (v > b)) := by
  simp [wins, List.map_replicate, List.sum_replicate]

lemma wins_replicate_replicate (k m v w : ℕ) :
    wins (List.replicate k v) (List.replicate m w) = if v > w then k * m else 0 := by
  rw [wins_replicate_left, List.countP_replicate]
  by_cases h : v > w <;> simp [h]

lemma wins_singleton_replicate (v m w : ℕ) :
    wins [v] (List.replicate m w) = if v > w then m else 0 := by
  simpa using wins_replicate_replicate 1 m v w

lemma wins_replicate_singleton (k v w : ℕ) :
    wins (List.replicate k v) [w] = if v > w then k else 0 := by
  simpa using wins_replicate_replicate k 1 v w

lemma wins_singleton_singleton (v w : ℕ) :
    wins [v] [w] = if v > w then 1 else 0 := by
  simpa using wins_replicate_replicate 1 1 v w

lemma pairwise_le_replicate (k v : ℕ) : (List.replicate k v).Pairwise (· ≤ ·) := by
  rw [List.pairwise_replicate]
  exact Or.inr le_rfl

lemma pairwise_le_append_iff {xs ys : List ℕ} :
    (xs ++ ys).Pairwise (· ≤ ·) ↔
      xs.Pairwise (· ≤ ·) ∧ ys.Pairwise (· ≤ ·) ∧ ∀ a ∈ xs, ∀ b ∈ ys, a ≤ b :=
  List.pairwise_append

/-! ### Generalized Involutive Antiautomorphism (Easlick Prollary 1 for all `n ≥ 3`) -/

/-- Face-reversal map `f(x₁, ..., xₙ) = (n + 1 - xₙ, ..., n + 1 - x₁)`. -/
def flipDie {n : ℕ} (d : Die n) : Die n where
  faces := (d.faces.map (fun x => n + 1 - x)).reverse
  len_eq := by simp [d.len_eq]
  in_range := by
    intro y hy
    rw [List.mem_reverse, List.mem_map] at hy
    rcases hy with ⟨x, hx, rfl⟩
    have := d.in_range x hx
    omega
  sorted := by
    rw [List.pairwise_reverse, List.pairwise_map]
    refine d.sorted.imp_of_mem ?_
    intro a b ha hb hab
    have h1 := d.in_range a ha
    have h2 := d.in_range b hb
    omega

theorem flipDie_involutive {n : ℕ} (d : Die n) : flipDie (flipDie d) = d := by
  apply Die.ext
  simp only [flipDie, List.map_reverse, List.reverse_reverse, List.map_map]
  conv_rhs => rw [← List.map_id d.faces]
  apply List.map_congr_left
  intro x hx
  have := d.in_range x hx
  simp only [Function.comp_apply, id_eq]
  omega

private lemma wins_reverse_left (xs ys : List ℕ) : wins xs.reverse ys = wins xs ys := by
  simp [wins, List.map_reverse, List.sum_reverse]

private lemma wins_reverse_right (xs ys : List ℕ) : wins xs ys.reverse = wins xs ys := by
  simp [wins, List.countP_reverse]

private lemma wins_nil_right (xs : List ℕ) : wins xs [] = 0 := by
  induction xs with
  | nil => simp [wins]
  | cons x xs ih => simp [wins] at ih ⊢

private lemma wins_flip_aux (n : ℕ) (xs ys : List ℕ)
    (hxs : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ n) (hys : ∀ y ∈ ys, 1 ≤ y ∧ y ≤ n) :
    wins (ys.map (fun y => n + 1 - y)) (xs.map (fun x => n + 1 - x)) = wins xs ys := by
  induction xs with
  | nil =>
    simpa [wins] using wins_nil_right (ys.map (fun y => n + 1 - y))
  | cons a xs ih =>
    have ha := hxs a (List.mem_cons_self ..)
    have hxs' : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ n := fun x hx => hxs x (List.mem_cons_of_mem a hx)
    simp only [List.map_cons]
    have hstep : wins (ys.map (fun y => n + 1 - y)) ((n + 1 - a) :: xs.map (fun x => n + 1 - x)) =
        wins (ys.map (fun y => n + 1 - y)) [n + 1 - a] +
          wins (ys.map (fun y => n + 1 - y)) (xs.map (fun x => n + 1 - x)) := by
      simpa using wins_append_right (ys.map (fun y => n + 1 - y)) [n + 1 - a]
        (xs.map (fun x => n + 1 - x))
    rw [hstep, ih hxs']
    have hcons : wins (a :: xs) ys = wins [a] ys + wins xs ys := by
      simpa using wins_append_left [a] xs ys
    rw [hcons]
    congr 1
    clear ih hstep hcons hxs hxs' xs
    induction ys with
    | nil => simp [wins]
    | cons b ys ihy =>
      have hb := hys b (List.mem_cons_self ..)
      have hys' : ∀ y ∈ ys, 1 ≤ y ∧ y ≤ n := fun y hy => hys y (List.mem_cons_of_mem b hy)
      rw [List.map_cons]
      have hL : wins ((n + 1 - b) :: ys.map (fun y => n + 1 - y)) [n + 1 - a] =
          wins [n + 1 - b] [n + 1 - a] + wins (ys.map (fun y => n + 1 - y)) [n + 1 - a] := by
        simpa using wins_append_left [n + 1 - b] (ys.map (fun y => n + 1 - y)) [n + 1 - a]
      have hR : wins [a] (b :: ys) = wins [a] [b] + wins [a] ys := by
        simpa using wins_append_right [a] [b] ys
      rw [hL, hR, ihy hys', wins_singleton_singleton, wins_singleton_singleton]
      have hiff : (n + 1 - b > n + 1 - a) ↔ (a > b) := by omega
      by_cases hab : a > b
      · simp [hab, hiff.mpr hab]
      · have h1 : ¬ (n + 1 - b > n + 1 - a) := fun h => hab (hiff.mp h)
        simp [hab, h1]

/-- `flipDie` is an involutive antiautomorphism of `G_n` for every `n`. -/
theorem flipDie_antiautomorphism {n : ℕ} (u v : Die n) :
    MinAdvEdge n (flipDie v) (flipDie u) ↔ MinAdvEdge n u v := by
  unfold MinAdvEdge flipDie
  dsimp only
  rw [wins_reverse_left, wins_reverse_right, wins_flip_aux n u.faces v.faces u.in_range v.in_range]

/-! ### Part 1: Infinite Odd Family (`n ≥ 11` odd, cycle length `3(n - 7)`) -/

section OddFamily

/-- Odd zipper die `A(x) = (1^k, 5^k, x)` for `n = 2k + 1` and `6 ≤ x ≤ n`. -/
def oddA (k x : ℕ) (hk : 3 ≤ k) (hx1 : 6 ≤ x) (hx2 : x ≤ 2 * k + 1) : Die (2 * k + 1) where
  faces := List.replicate k 1 ++ List.replicate k 5 ++ [x]
  len_eq := by simp; omega
  in_range := by
    intro v hv
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hv
    rcases hv with (⟨_, rfl⟩ | ⟨_, rfl⟩) | rfl <;> omega
  sorted := by
    rw [pairwise_le_append_iff]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · rw [pairwise_le_append_iff]
      refine ⟨pairwise_le_replicate k 1, pairwise_le_replicate k 5, ?_⟩
      intro a ha b hb
      rw [List.mem_replicate] at ha hb
      omega
    · intro a ha b hb
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at ha hb
      rcases ha with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> subst hb <;> omega

/-- Odd zipper die `B(y) = (2^(k-1), 3, 4^k, y)` for `n = 2k + 1` and `6 ≤ y ≤ n`. -/
def oddB (k y : ℕ) (hk : 3 ≤ k) (hy1 : 6 ≤ y) (hy2 : y ≤ 2 * k + 1) : Die (2 * k + 1) where
  faces := List.replicate (k - 1) 2 ++ [3] ++ List.replicate k 4 ++ [y]
  len_eq := by simp; omega
  in_range := by
    intro v hv
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hv
    rcases hv with ((⟨_, rfl⟩ | rfl) | ⟨_, rfl⟩) | rfl <;> omega
  sorted := by
    rw [pairwise_le_append_iff]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · rw [pairwise_le_append_iff]
      refine ⟨?_, pairwise_le_replicate k 4, ?_⟩
      · rw [pairwise_le_append_iff]
        refine ⟨pairwise_le_replicate (k - 1) 2, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        simp only [List.mem_replicate, List.mem_singleton] at ha hb
        omega
      · intro a ha b hb
        simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at ha hb
        rcases ha with ⟨_, rfl⟩ | rfl <;> omega
    · intro a ha b hb
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at ha hb
      rcases ha with (⟨_, rfl⟩ | rfl) | ⟨_, rfl⟩ <;> subst hb <;> omega

/-- Odd zipper die `C(z) = (2, 3^(2k-1), z)` for `n = 2k + 1` and `6 ≤ z ≤ n`. -/
def oddC (k z : ℕ) (hk : 3 ≤ k) (hz1 : 6 ≤ z) (hz2 : z ≤ 2 * k + 1) : Die (2 * k + 1) where
  faces := [2] ++ List.replicate (2 * k - 1) 3 ++ [z]
  len_eq := by simp; omega
  in_range := by
    intro v hv
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hv
    rcases hv with (rfl | ⟨_, rfl⟩) | rfl <;> omega
  sorted := by
    rw [pairwise_le_append_iff]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · rw [pairwise_le_append_iff]
      refine ⟨List.pairwise_singleton _ _, pairwise_le_replicate (2 * k - 1) 3, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton, List.mem_replicate] at ha hb
      omega
    · intro a ha b hb
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at ha hb
      rcases ha with rfl | ⟨_, rfl⟩ <;> subst hb <;> omega

private lemma minAdvTarget_odd (k : ℕ) : minAdvTarget (2 * k + 1) = 2 * k ^ 2 + 2 * k + 1 := by
  unfold minAdvTarget
  have h : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
  rw [h]; omega

lemma odd_edge_AB {k x y : ℕ} (hk : 3 ≤ k) (hx1 : 6 ≤ x) (hx2 : x ≤ 2 * k + 1)
    (hy1 : 6 ≤ y) (hy2 : y ≤ 2 * k + 1) (hxy : x > y) :
    MinAdvEdge (2 * k + 1) (oddA k x hk hx1 hx2) (oddB k y hk hy1 hy2) := by
  unfold MinAdvEdge oddA oddB
  dsimp only
  rw [minAdvTarget_odd]
  simp only [wins_append_left, wins_append_right, wins_replicate_replicate,
    wins_singleton_replicate, wins_replicate_singleton, wins_singleton_singleton]
  have h1 : x > 2 := by omega
  have h2 : x > 3 := by omega
  have h3 : x > 4 := by omega
  have h4 : ¬ (5 > y) := by omega
  have h5 : ¬ (1 > y) := by omega
  simp [hxy, h1, h2, h3, h4, h5]
  zify [show 1 ≤ k by omega]
  ring

lemma odd_edge_BC {k y z : ℕ} (hk : 3 ≤ k) (hy1 : 6 ≤ y) (hy2 : y ≤ 2 * k + 1)
    (hz1 : 6 ≤ z) (hz2 : z ≤ 2 * k + 1) (hyz : y ≤ z) :
    MinAdvEdge (2 * k + 1) (oddB k y hk hy1 hy2) (oddC k z hk hz1 hz2) := by
  unfold MinAdvEdge oddB oddC
  dsimp only
  rw [minAdvTarget_odd]
  simp only [wins_append_left, wins_append_right, wins_replicate_replicate,
    wins_singleton_replicate, wins_replicate_singleton, wins_singleton_singleton]
  have h1 : y > 2 := by omega
  have h2 : y > 3 := by omega
  have h3 : ¬ (y > z) := by omega
  have h4 : ¬ (2 > z) := by omega
  have h5 : ¬ (3 > z) := by omega
  have h6 : ¬ (4 > z) := by omega
  simp [h1, h2, h3, h4, h5, h6]
  zify [show 1 ≤ 2 * k by omega]
  ring

lemma odd_edge_CA {k z x : ℕ} (hk : 3 ≤ k) (hz1 : 6 ≤ z) (hz2 : z ≤ 2 * k + 1)
    (hx1 : 6 ≤ x) (hx2 : x ≤ 2 * k + 1) (hzx : z > x) :
    MinAdvEdge (2 * k + 1) (oddC k z hk hz1 hz2) (oddA k x hk hx1 hx2) := by
  unfold MinAdvEdge oddC oddA
  dsimp only
  rw [minAdvTarget_odd]
  simp only [wins_append_left, wins_append_right, wins_replicate_replicate,
    wins_singleton_replicate, wins_replicate_singleton, wins_singleton_singleton]
  have h1 : z > 1 := by omega
  have h2 : z > 5 := by omega
  have h3 : ¬ (2 > x) := by omega
  have h4 : ¬ (3 > x) := by omega
  simp [hzx, h1, h2, h3, h4]
  zify [show 1 ≤ 2 * k by omega]
  ring

private lemma oddA_ne_oddB {k x y : ℕ} (hk : 3 ≤ k) (hx1 : 6 ≤ x) (hx2 : x ≤ 2 * k + 1)
    (hy1 : 6 ≤ y) (hy2 : y ≤ 2 * k + 1) :
    oddA k x hk hx1 hx2 ≠ oddB k y hk hy1 hy2 := by
  intro h
  have h1 : 1 ∈ (oddA k x hk hx1 hx2).faces := by
    simp [oddA, show k ≠ 0 by omega]
  rw [h] at h1
  simp only [oddB, List.mem_append, List.mem_replicate, List.mem_singleton] at h1
  rcases h1 with ((⟨_, h'⟩ | h') | ⟨_, h'⟩) | h' <;> omega

private lemma oddA_ne_oddC {k x z : ℕ} (hk : 3 ≤ k) (hx1 : 6 ≤ x) (hx2 : x ≤ 2 * k + 1)
    (hz1 : 6 ≤ z) (hz2 : z ≤ 2 * k + 1) :
    oddA k x hk hx1 hx2 ≠ oddC k z hk hz1 hz2 := by
  intro h
  have h1 : 1 ∈ (oddA k x hk hx1 hx2).faces := by
    simp [oddA, show k ≠ 0 by omega]
  rw [h] at h1
  simp only [oddC, List.mem_append, List.mem_replicate, List.mem_singleton] at h1
  rcases h1 with (h' | ⟨_, h'⟩) | h' <;> omega

private lemma oddB_ne_oddC {k y z : ℕ} (hk : 3 ≤ k) (hy1 : 6 ≤ y) (hy2 : y ≤ 2 * k + 1)
    (hz1 : 6 ≤ z) (hz2 : z ≤ 2 * k + 1) :
    oddB k y hk hy1 hy2 ≠ oddC k z hk hz1 hz2 := by
  intro h
  have h4 : 4 ∈ (oddB k y hk hy1 hy2).faces := by
    simp [oddB, show k ≠ 0 by omega]
  rw [h] at h4
  simp only [oddC, List.mem_append, List.mem_replicate, List.mem_singleton] at h4
  rcases h4 with (h' | ⟨_, h'⟩) | h' <;> omega

private lemma oddA_inj {k x₁ x₂ : ℕ} (hk : 3 ≤ k) (h1 : 6 ≤ x₁) (h2 : x₁ ≤ 2 * k + 1)
    (h3 : 6 ≤ x₂) (h4 : x₂ ≤ 2 * k + 1)
    (heq : oddA k x₁ hk h1 h2 = oddA k x₂ hk h3 h4) : x₁ = x₂ := by
  have hf := congrArg Die.faces heq
  simp only [oddA, List.append_cancel_left_eq, List.cons.injEq, and_true] at hf
  exact hf

private lemma oddB_inj {k y₁ y₂ : ℕ} (hk : 3 ≤ k) (h1 : 6 ≤ y₁) (h2 : y₁ ≤ 2 * k + 1)
    (h3 : 6 ≤ y₂) (h4 : y₂ ≤ 2 * k + 1)
    (heq : oddB k y₁ hk h1 h2 = oddB k y₂ hk h3 h4) : y₁ = y₂ := by
  have hf := congrArg Die.faces heq
  simp only [oddB, List.append_cancel_left_eq, List.cons.injEq, and_true] at hf
  exact hf

private lemma oddC_inj {k z₁ z₂ : ℕ} (hk : 3 ≤ k) (h1 : 6 ≤ z₁) (h2 : z₁ ≤ 2 * k + 1)
    (h3 : 6 ≤ z₂) (h4 : z₂ ≤ 2 * k + 1)
    (heq : oddC k z₁ hk h1 h2 = oddC k z₂ hk h3 h4) : z₁ = z₂ := by
  have hf := congrArg Die.faces heq
  simp only [oddC, List.append_cancel_left_eq, List.cons.injEq, and_true] at hf
  exact hf

/-- Vertex `i` of the `3(2k - 6)`-cycle in `G_{2k+1}` for `k ≥ 5` (`n = 2k + 1 ≥ 11`). -/
def oddCycleVertex (k : ℕ) (hk : 5 ≤ k) (i : Fin (3 * (2 * k - 6))) : Die (2 * k + 1) :=
  let m := 2 * k - 6
  let q := i.1 / 3
  let r := i.1 % 3
  if r = 0 then
    oddB k (if q = 0 then 6 else 6 + m - q) (by omega) (by split_ifs <;> omega) (by split_ifs <;> omega)
  else if r = 1 then
    oddC k (6 + m + 1 - q) (by omega) (by omega) (by omega)
  else
    oddA k (6 + m - q) (by omega) (by omega) (by omega)

/-- For every odd `n ≥ 11`, `G_n` contains a simple minimal-advantage directed cycle
of length `3(n - 7) ≥ n + 1`. -/
theorem odd_cycle_exists (n : ℕ) (hn : 11 ≤ n) (hodd : n % 2 = 1) :
    ∃ cyc : List (Die n), cyc.length = 3 * (n - 7) ∧ IsMinAdvCycle n cyc := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  have hk : 5 ≤ k := by omega
  have hlen_eq : 3 * (2 * k - 6) = 3 * (2 * k + 1 - 7) := by omega
  refine ⟨List.ofFn (oddCycleVertex k hk), by rw [List.length_ofFn, hlen_eq], ?_, ?_, ?_⟩
  · rw [List.length_ofFn]; omega
  · rw [List.nodup_ofFn]
    intro i j hij
    ext
    unfold oddCycleVertex at hij
    dsimp only at hij
    by_cases hi0 : i.1 % 3 = 0 <;> by_cases hj0 : j.1 % 3 = 0
    · simp only [hi0, hj0, ↓reduceIte] at hij
      have hval := oddB_inj (k := k) _ _ _ _ _ hij
      split_ifs at hval <;> omega
    · by_cases hj1 : j.1 % 3 = 1
      · simp only [hi0, hj1, ↓reduceIte] at hij; norm_num at hij
        exact (oddB_ne_oddC (k := k) _ _ _ _ _ hij).elim
      · simp only [hi0, hj0, hj1, ↓reduceIte] at hij
        exact (oddA_ne_oddB (k := k) _ _ _ _ _ hij.symm).elim
    · by_cases hi1 : i.1 % 3 = 1
      · simp only [hi1, hj0, ↓reduceIte] at hij; norm_num at hij
        exact (oddB_ne_oddC (k := k) _ _ _ _ _ hij.symm).elim
      · simp only [hi0, hi1, hj0, ↓reduceIte] at hij
        exact (oddA_ne_oddB (k := k) _ _ _ _ _ hij).elim
    · by_cases hi1 : i.1 % 3 = 1 <;> by_cases hj1 : j.1 % 3 = 1
      · simp only [hi1, hj1, ↓reduceIte] at hij; norm_num at hij
        have hval := oddC_inj (k := k) _ _ _ _ _ hij
        omega
      · simp only [hi1, hj0, hj1, ↓reduceIte] at hij; norm_num at hij
        exact (oddA_ne_oddC (k := k) _ _ _ _ _ hij.symm).elim
      · simp only [hi0, hi1, hj1, ↓reduceIte] at hij; norm_num at hij
        exact (oddA_ne_oddC (k := k) _ _ _ _ _ hij).elim
      · simp only [hi0, hi1, hj0, hj1, ↓reduceIte] at hij
        have hval := oddA_inj (k := k) _ _ _ _ _ hij
        omega
  · intro idx
    simp only [List.get_eq_getElem, List.getElem_ofFn, List.length_ofFn]
    have hidx : idx.1 < 3 * (2 * k - 6) := by simpa [List.length_ofFn] using idx.2
    have hr : idx.1 % 3 = 0 ∨ idx.1 % 3 = 1 ∨ idx.1 % 3 = 2 := by omega
    rcases hr with hr0 | hr1 | hr2
    · have hnext_lt : idx.1 + 1 < 3 * (2 * k - 6) := by omega
      have hmod : (idx.1 + 1) % (3 * (2 * k - 6)) = idx.1 + 1 := Nat.mod_eq_of_lt hnext_lt
      have hnr : (idx.1 + 1) % 3 = 1 := by omega
      have hnq : (idx.1 + 1) / 3 = idx.1 / 3 := by omega
      simp only [oddCycleVertex, hr0, hmod, hnr, hnq, ↓reduceIte]
      norm_num
      apply odd_edge_BC
      split_ifs <;> omega
    · have hnext_lt : idx.1 + 1 < 3 * (2 * k - 6) := by omega
      have hmod : (idx.1 + 1) % (3 * (2 * k - 6)) = idx.1 + 1 := Nat.mod_eq_of_lt hnext_lt
      have hnr : (idx.1 + 1) % 3 = 2 := by omega
      have hnq : (idx.1 + 1) / 3 = idx.1 / 3 := by omega
      simp only [oddCycleVertex, hr1, hmod, hnr, hnq]
      norm_num
      apply odd_edge_CA
      omega
    · by_cases hlast : idx.1 + 1 = 3 * (2 * k - 6)
      · have hmod : (idx.1 + 1) % (3 * (2 * k - 6)) = 0 := by rw [hlast, Nat.mod_self]
        simp only [oddCycleVertex, hr2, hmod, Nat.zero_mod, Nat.zero_div]
        norm_num
        apply odd_edge_AB
        omega
      · have hnext_lt : idx.1 + 1 < 3 * (2 * k - 6) := by omega
        have hmod : (idx.1 + 1) % (3 * (2 * k - 6)) = idx.1 + 1 := Nat.mod_eq_of_lt hnext_lt
        have hnr : (idx.1 + 1) % 3 = 0 := by omega
        have hnq : (idx.1 + 1) / 3 = idx.1 / 3 + 1 := by omega
        have hnq_ne : idx.1 / 3 + 1 ≠ 0 := by omega
        simp only [oddCycleVertex, hr2, hmod, hnr, hnq, hnq_ne]
        norm_num
        apply odd_edge_AB
        omega

end OddFamily

/-! ### Part 2: Infinite Even Family (`n ≥ 16` even, cycle length `3(n - 10)`) -/

section EvenFamily

/-- Even zipper die `A(x) = (1^(k-1), 5, 8^(k-1), x)` for `n = 2k` and `9 ≤ x ≤ 2k`. -/
def evenA (k x : ℕ) (hk : 5 ≤ k) (hx1 : 9 ≤ x) (hx2 : x ≤ 2 * k) : Die (2 * k) where
  faces := List.replicate (k - 1) 1 ++ [5] ++ List.replicate (k - 1) 8 ++ [x]
  len_eq := by simp; omega
  in_range := by
    intro v hv
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hv
    rcases hv with ((⟨_, rfl⟩ | rfl) | ⟨_, rfl⟩) | rfl <;> omega
  sorted := by
    rw [pairwise_le_append_iff]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · rw [pairwise_le_append_iff]
      refine ⟨?_, pairwise_le_replicate (k - 1) 8, ?_⟩
      · rw [pairwise_le_append_iff]
        refine ⟨pairwise_le_replicate (k - 1) 1, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        simp only [List.mem_replicate, List.mem_singleton] at ha hb
        omega
      · intro a ha b hb
        simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at ha hb
        rcases ha with ⟨_, rfl⟩ | rfl <;> omega
    · intro a ha b hb
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at ha hb
      rcases ha with (⟨_, rfl⟩ | rfl) | ⟨_, rfl⟩ <;> subst hb <;> omega

/-- Even zipper die `B(y) = (2^(k-3), 3^2, 4, 7^(k-1), y)` for `n = 2k` and `9 ≤ y ≤ 2k`. -/
def evenB (k y : ℕ) (hk : 5 ≤ k) (hy1 : 9 ≤ y) (hy2 : y ≤ 2 * k) : Die (2 * k) where
  faces := List.replicate (k - 3) 2 ++ List.replicate 2 3 ++ [4] ++ List.replicate (k - 1) 7 ++ [y]
  len_eq := by simp; omega
  in_range := by
    intro v hv
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hv
    rcases hv with (((⟨_, rfl⟩ | ⟨_, rfl⟩) | rfl) | ⟨_, rfl⟩) | rfl <;> omega
  sorted := by
    rw [pairwise_le_append_iff]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · rw [pairwise_le_append_iff]
      refine ⟨?_, pairwise_le_replicate (k - 1) 7, ?_⟩
      · rw [pairwise_le_append_iff]
        refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
        · rw [pairwise_le_append_iff]
          refine ⟨pairwise_le_replicate (k - 3) 2, pairwise_le_replicate 2 3, ?_⟩
          intro a ha b hb
          simp only [List.mem_replicate] at ha hb
          omega
        · intro a ha b hb
          simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at ha hb
          rcases ha with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
      · intro a ha b hb
        simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at ha hb
        rcases ha with (⟨_, rfl⟩ | ⟨_, rfl⟩) | rfl <;> omega
    · intro a ha b hb
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at ha hb
      rcases ha with ((⟨_, rfl⟩ | ⟨_, rfl⟩) | rfl) | ⟨_, rfl⟩ <;> subst hb <;> omega

/-- Even zipper die `C(z) = (2, 3^(k-2), 6^k, z)` for `n = 2k` and `9 ≤ z ≤ 2k`. -/
def evenC (k z : ℕ) (hk : 5 ≤ k) (hz1 : 9 ≤ z) (hz2 : z ≤ 2 * k) : Die (2 * k) where
  faces := [2] ++ List.replicate (k - 2) 3 ++ List.replicate k 6 ++ [z]
  len_eq := by simp; omega
  in_range := by
    intro v hv
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hv
    rcases hv with ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) | rfl <;> omega
  sorted := by
    rw [pairwise_le_append_iff]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · rw [pairwise_le_append_iff]
      refine ⟨?_, pairwise_le_replicate k 6, ?_⟩
      · rw [pairwise_le_append_iff]
        refine ⟨List.pairwise_singleton _ _, pairwise_le_replicate (k - 2) 3, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton, List.mem_replicate] at ha hb
        omega
      · intro a ha b hb
        simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at ha hb
        rcases ha with rfl | ⟨_, rfl⟩ <;> omega
    · intro a ha b hb
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at ha hb
      rcases ha with (rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> subst hb <;> omega

private lemma minAdvTarget_even (k : ℕ) : minAdvTarget (2 * k) = 2 * k ^ 2 + 1 := by
  unfold minAdvTarget
  have h : (2 * k) ^ 2 = 2 * (2 * k ^ 2) := by ring
  rw [h]; omega

lemma even_edge_AB {k x y : ℕ} (hk : 5 ≤ k) (hx1 : 9 ≤ x) (hx2 : x ≤ 2 * k)
    (hy1 : 9 ≤ y) (hy2 : y ≤ 2 * k) (hxy : x > y) :
    MinAdvEdge (2 * k) (evenA k x hk hx1 hx2) (evenB k y hk hy1 hy2) := by
  unfold MinAdvEdge evenA evenB
  dsimp only
  rw [minAdvTarget_even]
  simp only [wins_append_left, wins_append_right, wins_replicate_replicate,
    wins_singleton_replicate, wins_replicate_singleton, wins_singleton_singleton]
  have h1 : x > 2 := by omega
  have h2 : x > 3 := by omega
  have h3 : x > 4 := by omega
  have h4 : x > 7 := by omega
  have h5 : ¬ (1 > y) := by omega
  have h6 : ¬ (5 > y) := by omega
  have h7 : ¬ (8 > y) := by omega
  simp [hxy, h1, h2, h3, h4, h5, h6, h7]
  zify [show 3 ≤ k by omega, show 1 ≤ k by omega]
  ring

lemma even_edge_BC {k y z : ℕ} (hk : 5 ≤ k) (hy1 : 9 ≤ y) (hy2 : y ≤ 2 * k)
    (hz1 : 9 ≤ z) (hz2 : z ≤ 2 * k) (hyz : y ≤ z) :
    MinAdvEdge (2 * k) (evenB k y hk hy1 hy2) (evenC k z hk hz1 hz2) := by
  unfold MinAdvEdge evenB evenC
  dsimp only
  rw [minAdvTarget_even]
  simp only [wins_append_left, wins_append_right, wins_replicate_replicate,
    wins_singleton_replicate, wins_replicate_singleton, wins_singleton_singleton]
  have h1 : y > 2 := by omega
  have h2 : y > 3 := by omega
  have h3 : y > 6 := by omega
  have h4 : ¬ (y > z) := by omega
  have h5 : ¬ (2 > z) := by omega
  have h6 : ¬ (3 > z) := by omega
  have h7 : ¬ (4 > z) := by omega
  have h8 : ¬ (7 > z) := by omega
  simp [h1, h2, h3, h4, h5, h6, h7, h8]
  zify [show 2 ≤ k by omega, show 1 ≤ k by omega]
  ring

lemma even_edge_CA {k z x : ℕ} (hk : 5 ≤ k) (hz1 : 9 ≤ z) (hz2 : z ≤ 2 * k)
    (hx1 : 9 ≤ x) (hx2 : x ≤ 2 * k) (hzx : z > x) :
    MinAdvEdge (2 * k) (evenC k z hk hz1 hz2) (evenA k x hk hx1 hx2) := by
  unfold MinAdvEdge evenC evenA
  dsimp only
  rw [minAdvTarget_even]
  simp only [wins_append_left, wins_append_right, wins_replicate_replicate,
    wins_singleton_replicate, wins_replicate_singleton, wins_singleton_singleton]
  have h1 : z > 1 := by omega
  have h2 : z > 5 := by omega
  have h3 : z > 8 := by omega
  have h4 : ¬ (2 > x) := by omega
  have h5 : ¬ (3 > x) := by omega
  have h6 : ¬ (6 > x) := by omega
  simp [hzx, h1, h2, h3, h4, h5, h6]
  zify [show 2 ≤ k by omega, show 1 ≤ k by omega]
  ring

private lemma evenA_ne_evenB {k x y : ℕ} (hk : 5 ≤ k) (hx1 : 9 ≤ x) (hx2 : x ≤ 2 * k)
    (hy1 : 9 ≤ y) (hy2 : y ≤ 2 * k) :
    evenA k x hk hx1 hx2 ≠ evenB k y hk hy1 hy2 := by
  intro h
  have h1 : 1 ∈ (evenA k x hk hx1 hx2).faces := by
    simp [evenA, show k - 1 ≠ 0 by omega]
  rw [h] at h1
  simp only [evenB, List.mem_append, List.mem_replicate, List.mem_singleton] at h1
  rcases h1 with (((⟨_, h'⟩ | ⟨_, h'⟩) | h') | ⟨_, h'⟩) | h' <;> omega

private lemma evenA_ne_evenC {k x z : ℕ} (hk : 5 ≤ k) (hx1 : 9 ≤ x) (hx2 : x ≤ 2 * k)
    (hz1 : 9 ≤ z) (hz2 : z ≤ 2 * k) :
    evenA k x hk hx1 hx2 ≠ evenC k z hk hz1 hz2 := by
  intro h
  have h1 : 1 ∈ (evenA k x hk hx1 hx2).faces := by
    simp [evenA, show k - 1 ≠ 0 by omega]
  rw [h] at h1
  simp only [evenC, List.mem_append, List.mem_replicate, List.mem_singleton] at h1
  rcases h1 with ((h' | ⟨_, h'⟩) | ⟨_, h'⟩) | h' <;> omega

private lemma evenB_ne_evenC {k y z : ℕ} (hk : 5 ≤ k) (hy1 : 9 ≤ y) (hy2 : y ≤ 2 * k)
    (hz1 : 9 ≤ z) (hz2 : z ≤ 2 * k) :
    evenB k y hk hy1 hy2 ≠ evenC k z hk hz1 hz2 := by
  intro h
  have h7 : 7 ∈ (evenB k y hk hy1 hy2).faces := by
    simp [evenB, show k - 1 ≠ 0 by omega]
  rw [h] at h7
  simp only [evenC, List.mem_append, List.mem_replicate, List.mem_singleton] at h7
  rcases h7 with ((h' | ⟨_, h'⟩) | ⟨_, h'⟩) | h' <;> omega

private lemma evenA_inj {k x₁ x₂ : ℕ} (hk : 5 ≤ k) (h1 : 9 ≤ x₁) (h2 : x₁ ≤ 2 * k)
    (h3 : 9 ≤ x₂) (h4 : x₂ ≤ 2 * k)
    (heq : evenA k x₁ hk h1 h2 = evenA k x₂ hk h3 h4) : x₁ = x₂ := by
  have hf := congrArg Die.faces heq
  simp only [evenA, List.append_cancel_left_eq, List.cons.injEq, and_true] at hf
  exact hf

private lemma evenB_inj {k y₁ y₂ : ℕ} (hk : 5 ≤ k) (h1 : 9 ≤ y₁) (h2 : y₁ ≤ 2 * k)
    (h3 : 9 ≤ y₂) (h4 : y₂ ≤ 2 * k)
    (heq : evenB k y₁ hk h1 h2 = evenB k y₂ hk h3 h4) : y₁ = y₂ := by
  have hf := congrArg Die.faces heq
  simp only [evenB, List.append_cancel_left_eq, List.cons.injEq, and_true] at hf
  exact hf

private lemma evenC_inj {k z₁ z₂ : ℕ} (hk : 5 ≤ k) (h1 : 9 ≤ z₁) (h2 : z₁ ≤ 2 * k)
    (h3 : 9 ≤ z₂) (h4 : z₂ ≤ 2 * k)
    (heq : evenC k z₁ hk h1 h2 = evenC k z₂ hk h3 h4) : z₁ = z₂ := by
  have hf := congrArg Die.faces heq
  simp only [evenC, List.append_cancel_left_eq, List.cons.injEq, and_true] at hf
  exact hf

/-- Vertex `i` of the `3(2k - 10)`-cycle in `G_{2k}` for `k ≥ 8` (`n = 2k ≥ 16`). -/
def evenCycleVertex (k : ℕ) (hk : 8 ≤ k) (i : Fin (3 * (2 * k - 10))) : Die (2 * k) :=
  let m := 2 * k - 10
  let q := i.1 / 3
  let r := i.1 % 3
  if r = 0 then
    evenB k (if q = 0 then 9 else 9 + m - q) (by omega) (by split_ifs <;> omega) (by split_ifs <;> omega)
  else if r = 1 then
    evenC k (9 + m + 1 - q) (by omega) (by omega) (by omega)
  else
    evenA k (9 + m - q) (by omega) (by omega) (by omega)

/-- For every even `n ≥ 16`, `G_n` contains a simple minimal-advantage directed cycle
of length `3(n - 10) ≥ n + 1`. -/
theorem even_cycle_exists (n : ℕ) (hn : 16 ≤ n) (heven : n % 2 = 0) :
    ∃ cyc : List (Die n), cyc.length = 3 * (n - 10) ∧ IsMinAdvCycle n cyc := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  have hk : 8 ≤ k := by omega
  refine ⟨List.ofFn (evenCycleVertex k hk), by rw [List.length_ofFn], ?_, ?_, ?_⟩
  · rw [List.length_ofFn]; omega
  · rw [List.nodup_ofFn]
    intro i j hij
    ext
    unfold evenCycleVertex at hij
    dsimp only at hij
    by_cases hi0 : i.1 % 3 = 0 <;> by_cases hj0 : j.1 % 3 = 0
    · simp only [hi0, hj0, ↓reduceIte] at hij
      have hval := evenB_inj (k := k) _ _ _ _ _ hij
      split_ifs at hval <;> omega
    · by_cases hj1 : j.1 % 3 = 1
      · simp only [hi0, hj1, ↓reduceIte] at hij; norm_num at hij
        exact (evenB_ne_evenC (k := k) _ _ _ _ _ hij).elim
      · simp only [hi0, hj0, hj1, ↓reduceIte] at hij
        exact (evenA_ne_evenB (k := k) _ _ _ _ _ hij.symm).elim
    · by_cases hi1 : i.1 % 3 = 1
      · simp only [hi1, hj0, ↓reduceIte] at hij; norm_num at hij
        exact (evenB_ne_evenC (k := k) _ _ _ _ _ hij.symm).elim
      · simp only [hi0, hi1, hj0, ↓reduceIte] at hij
        exact (evenA_ne_evenB (k := k) _ _ _ _ _ hij).elim
    · by_cases hi1 : i.1 % 3 = 1 <;> by_cases hj1 : j.1 % 3 = 1
      · simp only [hi1, hj1, ↓reduceIte] at hij; norm_num at hij
        have hval := evenC_inj (k := k) _ _ _ _ _ hij
        omega
      · simp only [hi1, hj0, hj1, ↓reduceIte] at hij; norm_num at hij
        exact (evenA_ne_evenC (k := k) _ _ _ _ _ hij.symm).elim
      · simp only [hi0, hi1, hj1, ↓reduceIte] at hij; norm_num at hij
        exact (evenA_ne_evenC (k := k) _ _ _ _ _ hij).elim
      · simp only [hi0, hi1, hj0, hj1, ↓reduceIte] at hij
        have hval := evenA_inj (k := k) _ _ _ _ _ hij
        omega
  · intro idx
    simp only [List.get_eq_getElem, List.getElem_ofFn, List.length_ofFn]
    have hidx : idx.1 < 3 * (2 * k - 10) := by simpa [List.length_ofFn] using idx.2
    have hr : idx.1 % 3 = 0 ∨ idx.1 % 3 = 1 ∨ idx.1 % 3 = 2 := by omega
    rcases hr with hr0 | hr1 | hr2
    · have hnext_lt : idx.1 + 1 < 3 * (2 * k - 10) := by omega
      have hmod : (idx.1 + 1) % (3 * (2 * k - 10)) = idx.1 + 1 := Nat.mod_eq_of_lt hnext_lt
      have hnr : (idx.1 + 1) % 3 = 1 := by omega
      have hnq : (idx.1 + 1) / 3 = idx.1 / 3 := by omega
      simp only [evenCycleVertex, hr0, hmod, hnr, hnq, ↓reduceIte]
      norm_num
      apply even_edge_BC
      split_ifs <;> omega
    · have hnext_lt : idx.1 + 1 < 3 * (2 * k - 10) := by omega
      have hmod : (idx.1 + 1) % (3 * (2 * k - 10)) = idx.1 + 1 := Nat.mod_eq_of_lt hnext_lt
      have hnr : (idx.1 + 1) % 3 = 2 := by omega
      have hnq : (idx.1 + 1) / 3 = idx.1 / 3 := by omega
      simp only [evenCycleVertex, hr1, hmod, hnr, hnq]
      norm_num
      apply even_edge_CA
      omega
    · by_cases hlast : idx.1 + 1 = 3 * (2 * k - 10)
      · have hmod : (idx.1 + 1) % (3 * (2 * k - 10)) = 0 := by rw [hlast, Nat.mod_self]
        simp only [evenCycleVertex, hr2, hmod, Nat.zero_mod, Nat.zero_div]
        norm_num
        apply even_edge_AB
        omega
      · have hnext_lt : idx.1 + 1 < 3 * (2 * k - 10) := by omega
        have hmod : (idx.1 + 1) % (3 * (2 * k - 10)) = idx.1 + 1 := Nat.mod_eq_of_lt hnext_lt
        have hnr : (idx.1 + 1) % 3 = 0 := by omega
        have hnq : (idx.1 + 1) / 3 = idx.1 / 3 + 1 := by omega
        have hnq_ne : idx.1 / 3 + 1 ≠ 0 := by omega
        simp only [evenCycleVertex, hr2, hmod, hnr, hnq, hnq_ne]
        norm_num
        apply even_edge_AB
        omega

end EvenFamily

/-! ### Part 3: Explicit Finite Cases (`n = 6, 7, 8, 9, 10, 12, 14`) -/

section SmallCases

/-- Boolean checker for a raw list of face-lists to form a valid simple cycle in `G_n`. -/
private def checkSorted : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a ≤ b) && checkSorted (b :: rest)

private lemma checkSorted_sound : ∀ xs : List ℕ, checkSorted xs = true → xs.Pairwise (· ≤ ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [checkSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    have hrest := checkSorted_sound (b :: rest) h.2
    rw [List.pairwise_cons] at hrest ⊢
    refine ⟨?_, List.pairwise_cons.mpr hrest⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h.1
    · exact h.1.trans (hrest.1 x hx')

private def checkRawDie (n : ℕ) (xs : List ℕ) : Bool :=
  decide (xs.length = n) && xs.all (fun x => decide (1 ≤ x) && decide (x ≤ n)) && checkSorted xs

private def rawToDie (n : ℕ) (xs : List ℕ) (h : checkRawDie n xs = true) : Die n where
  faces := xs
  len_eq := by
    simp only [checkRawDie, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  in_range := by
    simp only [checkRawDie, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    intro x hx
    exact h.1.2 x hx
  sorted := by
    simp only [checkRawDie, Bool.and_eq_true] at h
    exact checkSorted_sound xs h.2

private def checkEdgesAux (t : ℕ) (first : List ℕ) : List (List ℕ) → Bool
  | [] => true
  | [last] => decide (wins last first = t)
  | a :: b :: rest => decide (wins a b = t) && checkEdgesAux t first (b :: rest)

private def checkRawCycle (n : ℕ) (raw : List (List ℕ)) : Bool :=
  match raw with
  | [] => false
  | first :: _ =>
    decide (3 ≤ raw.length) &&
    raw.all (checkRawDie n) &&
    decide raw.Nodup &&
    checkEdgesAux (minAdvTarget n) first raw

private lemma checkEdgesAux_sound (t : ℕ) (first : List ℕ) :
    ∀ (L : List (List ℕ)), checkEdgesAux t first L = true →
      (∀ i (hi : i + 1 < L.length), wins (L[i]'(by omega)) (L[i + 1]'hi) = t) ∧
      (∀ hne : L ≠ [], wins (L[L.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil hne) Nat.one_pos)) first = t)
  | [], _ => ⟨fun _ hi => by simp at hi, fun hne => (hne rfl).elim⟩
  | [last], h => by
    simp only [checkEdgesAux, decide_eq_true_eq] at h
    refine ⟨fun i hi => by simp at hi, fun _ => by simpa using h⟩
  | a :: b :: rest, h => by
    simp only [checkEdgesAux, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨ih1, ih2⟩ := checkEdgesAux_sound t first (b :: rest) h.2
    refine ⟨?_, ?_⟩
    · intro i hi
      cases i with
      | zero => simpa using h.1
      | succ i' =>
        have hi' : i' + 1 < (b :: rest).length := by simp at hi ⊢; omega
        simpa using ih1 i' hi'
    · intro _
      have hne : (b :: rest) ≠ [] := List.cons_ne_nil _ _
      simpa using ih2 hne

private lemma of_checkRawCycle {n : ℕ} (raw : List (List ℕ))
    (h : checkRawCycle n raw = true) :
    ∃ cyc : List (Die n), cyc.length = raw.length ∧ IsMinAdvCycle n cyc := by
  cases raw with
  | nil => simp [checkRawCycle] at h
  | cons first tail =>
    simp only [checkRawCycle, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    rcases h with ⟨⟨⟨hlen3, hall⟩, hnodup⟩, hedges⟩
    let L := first :: tail
    have hLlen : L.length = (first :: tail).length := rfl
    let cyc : List (Die n) := L.attach.map (fun ⟨xs, hxs⟩ => rawToDie n xs (hall xs hxs))
    have hcycf : cyc.map Die.faces = L := by
      simp [cyc, rawToDie]
    have hcyclen : cyc.length = L.length := by
      simpa using congrArg List.length hcycf
    refine ⟨cyc, by omega, by omega, ?_, ?_⟩
    · have hnd : (cyc.map Die.faces).Nodup := by rw [hcycf]; exact hnodup
      exact List.Nodup.of_map Die.faces hnd
    · obtain ⟨hstep, hwrap⟩ := checkEdgesAux_sound (minAdvTarget n) first L hedges
      intro idx
      unfold MinAdvEdge
      have hface_get : ∀ j : Fin cyc.length,
          (cyc.get j).faces = L[j.1]'(by omega) := by
        intro j
        have h1 : (cyc.map Die.faces)[j.1]'(by simp [j.2]) = (cyc[j.1]'j.2).faces := by
          simp
        rw [List.get_eq_getElem, ← h1]
        congr 1
      rw [hface_get idx, hface_get ⟨(idx.1 + 1) % cyc.length, Nat.mod_lt _ (by omega)⟩]
      by_cases hlast : idx.1 + 1 = cyc.length
      · have hmod : (idx.1 + 1) % cyc.length = 0 := by rw [hlast, Nat.mod_self]
        have hidx_eq : idx.1 = L.length - 1 := by omega
        simp only [hmod]
        simp only [hidx_eq]
        simpa [L] using hwrap (List.cons_ne_nil first tail)
      · have hlt : idx.1 + 1 < cyc.length := by omega
        have hmod : (idx.1 + 1) % cyc.length = idx.1 + 1 := Nat.mod_eq_of_lt hlt
        simp only [hmod]
        exact hstep idx.1 (by omega)

private def rawCycle6_1 : List (List ℕ) :=
  [ [1,1,2,5,5,5], [1,3,4,4,4,4], [2,2,2,3,6,6],
    [1,1,2,5,5,6], [1,3,3,4,4,4], [2,2,3,3,3,6] ]

private def rawCycle7 : List (List ℕ) :=
  [ [1,1,1,3,3,4,7], [2,2,2,2,2,2,6], [1,1,1,3,5,5,5], [1,1,2,2,4,4,4],
    [1,1,3,3,3,3,3], [1,2,2,2,2,6,7], [1,1,1,3,5,5,6], [2,2,2,2,3,4,4] ]

private def rawCycle8 : List (List ℕ) :=
  [ [1,1,1,2,4,6,6,6], [1,1,3,3,3,3,3,5], [2,2,2,2,2,4,4,4],
    [1,1,1,3,3,3,7,8], [2,2,2,2,2,2,6,7], [1,1,1,2,5,5,5,6],
    [1,2,3,3,4,4,4,4], [1,2,3,3,3,3,3,8], [1,1,2,2,2,7,8,8] ]

private def rawCycle9 : List (List ℕ) :=
  [ [1,1,1,1,3,3,3,3,7], [2,2,2,2,2,2,2,2,6], [1,1,1,1,3,5,5,5,5],
    [1,1,2,2,2,4,4,4,4], [1,1,1,2,3,3,3,3,8], [2,2,2,2,2,2,2,2,7],
    [1,1,1,1,3,3,6,6,6], [2,2,2,2,2,2,2,4,5], [1,1,1,1,3,3,4,5,9],
    [2,2,2,2,2,2,2,2,8] ]

private def rawCycle10 : List (List ℕ) :=
  [ [1,1,1,1,2,4,4,4,4,4], [1,2,2,3,3,3,3,3,3,3], [1,2,2,2,2,2,2,5,6,6],
    [1,1,1,1,3,4,4,5,5,5], [1,2,2,3,3,3,3,3,3,4], [1,2,2,2,2,2,2,6,6,6],
    [1,1,1,1,2,5,5,5,5,6], [1,2,2,2,4,4,4,4,4,4], [1,3,3,3,3,3,3,3,5,5],
    [2,2,2,2,2,4,4,4,6,6], [1,1,2,2,2,2,3,5,5,5] ]

private def rawCycle12 : List (List ℕ) :=
  [ [1,1,1,1,1,2,4,4,4,4,4,4], [1,2,2,2,3,3,3,3,3,3,3,3], [1,1,1,2,2,2,2,2,6,6,6,6],
    [1,1,1,1,1,2,4,4,4,4,4,5], [1,2,3,3,3,3,3,3,3,3,3,3], [1,1,1,2,2,2,2,3,6,6,6,6],
    [1,1,1,1,1,3,4,4,4,5,5,5], [1,1,1,1,3,3,3,3,3,3,3,4], [2,2,2,2,2,2,2,2,2,3,6,6],
    [1,1,1,1,1,2,5,5,5,5,5,6], [1,2,2,2,2,2,2,4,4,4,4,4], [1,1,1,3,3,3,3,3,3,3,3,6],
    [1,1,1,2,2,2,2,2,5,6,6,6] ]

private def rawCycle14 : List (List ℕ) :=
  [ [2,2,2,3,3,3,3,6,6,6,6,6,6,8],
    [2,2,3,3,3,3,5,5,5,5,5,5,5,14],
    [1,1,1,1,1,1,4,7,7,7,7,7,7,13],
    [2,2,2,3,3,3,3,6,6,6,6,6,6,12],
    [2,2,3,3,3,3,5,5,5,5,5,5,5,13],
    [1,1,1,1,1,1,4,7,7,7,7,7,7,12],
    [2,2,2,3,3,3,3,6,6,6,6,6,6,11],
    [2,2,3,3,3,3,5,5,5,5,5,5,5,12],
    [1,1,1,1,1,1,4,7,7,7,7,7,7,11],
    [2,2,2,3,3,3,3,6,6,6,6,6,6,10],
    [2,2,3,3,3,3,5,5,5,5,5,5,5,11],
    [1,1,1,1,1,1,4,7,7,7,7,7,7,10],
    [2,2,2,3,3,3,3,6,6,6,6,6,6,9],
    [2,2,3,3,3,3,5,5,5,5,5,5,5,10],
    [1,1,1,1,1,1,4,7,7,7,7,7,7,9] ]

theorem n6_has_cycle_6 :
    ∃ cyc : List (Die 6), cyc.length = 6 ∧ IsMinAdvCycle 6 cyc :=
  of_checkRawCycle rawCycle6_1 (by decide)

theorem cycle_7 : ∃ cyc : List (Die 7), cyc.length = 8 ∧ IsMinAdvCycle 7 cyc :=
  of_checkRawCycle rawCycle7 (by decide)

theorem cycle_8 : ∃ cyc : List (Die 8), cyc.length = 9 ∧ IsMinAdvCycle 8 cyc :=
  of_checkRawCycle rawCycle8 (by decide)

theorem cycle_9 : ∃ cyc : List (Die 9), cyc.length = 10 ∧ IsMinAdvCycle 9 cyc :=
  of_checkRawCycle rawCycle9 (by decide)

theorem cycle_10 : ∃ cyc : List (Die 10), cyc.length = 11 ∧ IsMinAdvCycle 10 cyc :=
  of_checkRawCycle rawCycle10 (by decide)

theorem cycle_12 : ∃ cyc : List (Die 12), cyc.length = 13 ∧ IsMinAdvCycle 12 cyc :=
  of_checkRawCycle rawCycle12 (by decide)

theorem cycle_14 : ∃ cyc : List (Die 14), cyc.length = 15 ∧ IsMinAdvCycle 14 cyc :=
  of_checkRawCycle rawCycle14 (by decide)

end SmallCases

/-! ### Part 4: Complete Proof of Easlick's Conjecture 1 -/

/-- **Conjecture 1 of Easlick (`arXiv:2610.40321v2`), proved for all `n ≥ 7`.**
For every integer `n ≥ 7`, the minimal-advantage directed graph `G_n` on non-standard
`n`-sided dice with face values in `{1, ..., n}` admits a simple directed cycle of length
at least `n + 1` (hence its maximum cycle length strictly exceeds `n`). -/
theorem easlick_conjecture1 (n : ℕ) (hn : 7 ≤ n) :
    ∃ cyc : List (Die n), n + 1 ≤ cyc.length ∧ IsMinAdvCycle n cyc := by
  by_cases hpar : n % 2 = 1
  · by_cases h11 : 11 ≤ n
    · obtain ⟨cyc, hlen, hcyc⟩ := odd_cycle_exists n h11 hpar
      exact ⟨cyc, by omega, hcyc⟩
    · have hsmall : n = 7 ∨ n = 9 := by omega
      rcases hsmall with rfl | rfl
      · obtain ⟨cyc, hlen, hcyc⟩ := cycle_7; exact ⟨cyc, by omega, hcyc⟩
      · obtain ⟨cyc, hlen, hcyc⟩ := cycle_9; exact ⟨cyc, by omega, hcyc⟩
  · have hev : n % 2 = 0 := by omega
    by_cases h16 : 16 ≤ n
    · obtain ⟨cyc, hlen, hcyc⟩ := even_cycle_exists n h16 hev
      exact ⟨cyc, by omega, hcyc⟩
    · have hsmall : n = 8 ∨ n = 10 ∨ n = 12 ∨ n = 14 := by omega
      rcases hsmall with rfl | rfl | rfl | rfl
      · obtain ⟨cyc, hlen, hcyc⟩ := cycle_8; exact ⟨cyc, by omega, hcyc⟩
      · obtain ⟨cyc, hlen, hcyc⟩ := cycle_10; exact ⟨cyc, by omega, hcyc⟩
      · obtain ⟨cyc, hlen, hcyc⟩ := cycle_12; exact ⟨cyc, by omega, hcyc⟩
      · obtain ⟨cyc, hlen, hcyc⟩ := cycle_14; exact ⟨cyc, by omega, hcyc⟩

end EaslickNontransitiveDice
