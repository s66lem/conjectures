import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat

/-!
# Conjecture 7.1 of Benedetti–Menara (arXiv:2611.08071) for `r = 2`

A flag 1-layered family of 2-subsets of an `m`-set has at most `m − 1` layers.

The internal development works with a symmetric irreflexive relation `adj` and an edge
labelling `lam` that is symmetric on edges. Walks are maps `x : ℕ → V` with a length `k`;
step `n` is the edge `x n — x (n+1)` with label `lab lam x n`.

* `walk_bound`: a non-increasing walk with first label `p` and last label `q` forces
  `p + 2 ≤ #active + q` (Asratian–Kamalian style count on a shortest, lexicographically
  maximal walk; the shortest walk is automatically a path).
* `layers_le_active`: induction on the top label via the down-closed reachability set `Reach`.
-/

namespace FlagLayeredR2

open Finset

variable {V : Type*}

/-! ## Walks -/

/-- Label of step `n` of the walk `x`. -/
def lab (lam : V → V → ℕ) (x : ℕ → V) (n : ℕ) : ℕ := lam (x n) (x (n + 1))

/-- `x` is a walk of length `k` whose labels are non-increasing. -/
def Chain (adj : V → V → Prop) (lam : V → V → ℕ) (x : ℕ → V) (k : ℕ) : Prop :=
  (∀ n < k, adj (x n) (x (n + 1))) ∧ ∀ n, n + 1 < k → lab lam x (n + 1) ≤ lab lam x n

/-- Non-increasing walk of positive length with first label `p` and last label `q`. -/
def Good (adj : V → V → Prop) (lam : V → V → ℕ) (p q : ℕ) (x : ℕ → V) (k : ℕ) : Prop :=
  Chain adj lam x k ∧ 0 < k ∧ lab lam x 0 = p ∧ lab lam x (k - 1) = q

/-- `Good` walk with start vertex `s` and end vertex `e`. -/
def Seg (adj : V → V → Prop) (lam : V → V → ℕ) (x : ℕ → V) (k f l : ℕ) (s e : V) : Prop :=
  Good adj lam f l x k ∧ x 0 = s ∧ x k = e

def glue (a : ℕ → V) (k : ℕ) (b : ℕ → V) : ℕ → V := fun n => if n ≤ k then a n else b (n - k)

def edge (u v : V) : ℕ → V := fun n => if n = 0 then u else v

variable {adj : V → V → Prop} {lam : V → V → ℕ}

theorem glue_le {a b : ℕ → V} {k n : ℕ} (h : n ≤ k) : glue a k b n = a n := if_pos h

theorem glue_ge {a b : ℕ → V} {k n : ℕ} (hab : a k = b 0) (h : k ≤ n) :
    glue a k b n = b (n - k) := by
  unfold glue
  split_ifs with h'
  · obtain rfl : n = k := by omega
    simp [hab]
  · rfl

theorem lab_glue_lt {a b : ℕ → V} {k n : ℕ} (hn : n < k) :
    lab lam (glue a k b) n = lab lam a n := by
  simp only [lab]; rw [glue_le hn.le, glue_le (by omega : n + 1 ≤ k)]

theorem lab_glue_ge {a b : ℕ → V} {k n : ℕ} (hab : a k = b 0) (hn : k ≤ n) :
    lab lam (glue a k b) n = lab lam b (n - k) := by
  simp only [lab]
  rw [glue_ge hab hn, glue_ge hab (by omega : k ≤ n + 1), show n + 1 - k = n - k + 1 by omega]

theorem chain_glue {a b : ℕ → V} {k₁ k₂ : ℕ} (ha : Chain adj lam a k₁) (hb : Chain adj lam b k₂)
    (hab : a k₁ = b 0) (hj : 0 < k₁ → 0 < k₂ → lab lam b 0 ≤ lab lam a (k₁ - 1)) :
    Chain adj lam (glue a k₁ b) (k₁ + k₂) := by
  constructor
  · intro n hn
    by_cases h : n < k₁
    · rw [glue_le h.le, glue_le (by omega : n + 1 ≤ k₁)]; exact ha.1 n h
    · rw [glue_ge hab (by omega), glue_ge hab (by omega), show n + 1 - k₁ = n - k₁ + 1 by omega]
      exact hb.1 _ (by omega)
  · intro n hn
    by_cases h : n + 1 < k₁
    · rw [lab_glue_lt h, lab_glue_lt (by omega)]; exact ha.2 n h
    · by_cases h' : n + 1 = k₁
      · rw [lab_glue_ge hab (by omega), lab_glue_lt (by omega), show n + 1 - k₁ = 0 by omega,
          show n = k₁ - 1 by omega]
        exact hj (by omega) (by omega)
      · rw [lab_glue_ge hab (by omega), lab_glue_ge hab (by omega),
          show n + 1 - k₁ = n - k₁ + 1 by omega]
        exact hb.2 _ (by omega)

theorem seg_glue {a b : ℕ → V} {k₁ k₂ f₁ l₁ f₂ l₂ : ℕ} {s₁ e₁ s₂ e₂ : V}
    (ha : Seg adj lam a k₁ f₁ l₁ s₁ e₁) (hb : Seg adj lam b k₂ f₂ l₂ s₂ e₂) (he : e₁ = s₂)
    (hf : f₂ ≤ l₁) : Seg adj lam (glue a k₁ b) (k₁ + k₂) f₁ l₂ s₁ e₂ := by
  obtain ⟨⟨hca, hka, hfa, hla⟩, hsa, hea⟩ := ha
  obtain ⟨⟨hcb, hkb, hfb, hlb⟩, hsb, heb⟩ := hb
  have hab : a k₁ = b 0 := hea.trans (he.trans hsb.symm)
  refine ⟨⟨chain_glue hca hcb hab (fun _ _ => by rw [hfb, hla]; exact hf), by omega, ?_, ?_⟩, ?_, ?_⟩
  · rw [lab_glue_lt hka, hfa]
  · rw [lab_glue_ge hab (by omega), show k₁ + k₂ - 1 - k₁ = k₂ - 1 by omega, hlb]
  · rw [glue_le (Nat.zero_le _), hsa]
  · rw [glue_ge hab (by omega), Nat.add_sub_cancel_left, heb]

theorem seg_edge {u v : V} (h : adj u v) : Seg adj lam (edge u v) 1 (lam u v) (lam u v) u v := by
  refine ⟨⟨⟨fun n hn => ?_, fun n hn => by omega⟩, by omega, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp_all [edge, lab]

theorem seg_prefix {x : ℕ → V} {k i : ℕ} (hx : Chain adj lam x k) (hi : 0 < i) (hik : i ≤ k) :
    Seg adj lam x i (lab lam x 0) (lab lam x (i - 1)) (x 0) (x i) :=
  ⟨⟨⟨fun n hn => hx.1 n (by omega), fun n hn => hx.2 n (by omega)⟩, hi, rfl, rfl⟩, rfl, rfl⟩

theorem lab_shift {x : ℕ → V} {j n : ℕ} : lab lam (fun n => x (n + j)) n = lab lam x (n + j) := by
  simp only [lab]; rw [show n + 1 + j = n + j + 1 by omega]

theorem seg_suffix {x : ℕ → V} {k j : ℕ} (hx : Chain adj lam x k) (hj : j < k) :
    Seg adj lam (fun n => x (n + j)) (k - j) (lab lam x j) (lab lam x (k - 1)) (x j) (x k) := by
  refine ⟨⟨⟨fun n hn => ?_, fun n hn => ?_⟩, by omega, ?_, ?_⟩, ?_, ?_⟩
  · simp only; rw [show n + 1 + j = n + j + 1 by omega]; exact hx.1 _ (by omega)
  · rw [lab_shift, lab_shift, show n + 1 + j = n + j + 1 by omega]; exact hx.2 _ (by omega)
  · rw [lab_shift, Nat.zero_add]
  · rw [lab_shift, show k - j - 1 + j = k - 1 by omega]
  · simp
  · simp only; rw [Nat.sub_add_cancel hj.le]

theorem chain_mono {x : ℕ → V} {k : ℕ} (hx : Chain adj lam x k) {i j : ℕ} (hij : i ≤ j)
    (hj : j < k) : lab lam x j ≤ lab lam x i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (hx.2 j hj).trans (ih (by omega))

/-- A lexicographically maximal element among finitely-bounded label sequences. -/
theorem exists_lexmax {α : Type*} (S : α → Prop) (f : α → ℕ → ℕ) (p : ℕ) (hne : ∃ a, S a) :
    ∀ m, (∀ a, S a → ∀ i < m, f a i ≤ p) →
      ∃ a, S a ∧ ∀ b, S b → ∀ i < m, (∀ j < i, f b j = f a j) → f b i ≤ f a i := by
  intro m
  induction m with
  | zero => intro _; obtain ⟨a, ha⟩ := hne; exact ⟨a, ha, fun _ _ i hi => absurd hi (by omega)⟩
  | succ m ih =>
    intro hb
    obtain ⟨a, ha, hmax⟩ := ih (fun b hb' i hi => hb b hb' i (by omega))
    classical
    let P : ℕ → Prop := fun t => ∃ b, S b ∧ (∀ j < m, f b j = f a j) ∧ f b m = t
    have hPa : P (f a m) := ⟨a, ha, fun _ _ => rfl, rfl⟩
    obtain ⟨b, hbS, hba, hbm⟩ := Nat.findGreatest_spec (hb a ha m (by omega)) hPa
    refine ⟨b, hbS, fun c hc i hi hci => ?_⟩
    rcases Nat.lt_or_ge i m with him | him
    · rw [hba i him]
      exact hmax c hc i him (fun j hj => (hci j hj).trans (hba j (by omega)))
    · rw [show i = m by omega] at hci ⊢
      rw [hbm]
      exact Nat.le_findGreatest (hb c hc m (by omega))
        ⟨c, hc, fun j hj => (hci j hj).trans (hba j hj), rfl⟩

/-- Vertices with at least one incident edge. -/
noncomputable def active [Fintype V] (adj : V → V → Prop) : Finset V := by
  classical exact univ.filter (fun v => ∃ u, adj v u)

theorem mem_active [Fintype V] {v : V} : v ∈ active adj ↔ ∃ u, adj v u := by
  unfold active; simp

/-! ## The monotone walk count -/

theorem walk_bound [Fintype V] [DecidableEq V]
    (hsymm : ∀ u v, adj u v → adj v u) (hirr : ∀ v, ¬ adj v v)
    (hlam : ∀ u v, adj u v → lam u v = lam v u)
    (htf : ∀ u v w, adj u v → adj v w → ¬ adj u w)
    (hint : ∀ v u₁ u₂, adj v u₁ → adj v u₂ → ∀ t, lam v u₁ ≤ t → t ≤ lam v u₂ →
      ∃ w, adj v w ∧ lam v w = t)
    {p q : ℕ} {x₀ : ℕ → V} {k₁ : ℕ} (hex : Good adj lam p q x₀ k₁) :
    p + 2 ≤ (active adj).card + q := by
  classical
  have hex' : ∃ k, ∃ x, Good adj lam p q x k := ⟨k₁, x₀, hex⟩
  obtain ⟨k, hk, hmin⟩ : ∃ k, (∃ x, Good adj lam p q x k) ∧
      ∀ y k', Good adj lam p q y k' → k ≤ k' :=
    ⟨Nat.find hex', Nat.find_spec hex', fun y k' h => Nat.find_min' hex' ⟨y, h⟩⟩
  obtain ⟨x, hx, hlex⟩ := exists_lexmax (fun x => Good adj lam p q x k) (fun x i => lab lam x i) p
    hk k (fun y hy i hi => by rw [← hy.2.2.1]; exact chain_mono hy.1 (Nat.zero_le i) hi)
  obtain ⟨hc, hk0, hp, hq⟩ := hx
  have short : ∀ {y k' f l s e}, Seg adj lam y k' f l s e → f = p → l = q → k' < k → False :=
    fun {y k' f l s e} h hf hl hk' => by
      subst hf hl; exact absurd (hmin y k' h.1) (by omega)
  have hadj : ∀ n < k, adj (x n) (x (n + 1)) := hc.1
  have hmono : ∀ i j, i ≤ j → j < k → lab lam x j ≤ lab lam x i := fun i j h1 h2 =>
    chain_mono hc h1 h2
  have hrev : ∀ n < k, lam (x (n + 1)) (x n) = lab lam x n := fun n hn =>
    (hlam _ _ (hadj n hn)).symm
  have hladj : adj (x k) (x (k - 1)) := by
    have := hsymm _ _ (hadj (k - 1) (by omega)); rwa [Nat.sub_add_cancel hk0] at this
  have hllam : lam (x k) (x (k - 1)) = q := by
    have := hrev (k - 1) (by omega); rw [Nat.sub_add_cancel hk0] at this; rw [this, hq]
  have hpre := fun i (hi : 0 < i) (hik : i ≤ k) => seg_prefix hc hi hik
  have hsuf := fun j (hj : j < k) => seg_suffix hc hj
  -- The shortest walk is a path.
  have hinj : ∀ a b, a < b → b ≤ k → x a ≠ x b := by
    intro a b hab hbk he
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.lt_or_ge b k with hb | hb
      · have hb2 : 2 ≤ b := by
          by_contra h
          obtain rfl : b = 1 := by omega
          exact hirr _ (he ▸ hadj 0 (by omega))
        exact short (seg_glue (seg_edge (hsymm _ _ (hadj 0 (by omega)))) (hsuf b hb) he
          (by rw [hrev 0 (by omega)]; exact hmono 0 b (by omega) hb)) (by rw [hrev 0 hk0, hp])
          hq (by omega)
      · rw [show b = k by omega] at he
        rcases Nat.lt_or_ge k 3 with hk3 | hk3
        · have hk2 : k = 2 := by
            rcases (show k = 1 ∨ k = 2 by omega) with h | h
            · rw [h] at he; exact absurd (he ▸ hadj 0 (by omega)) (hirr _)
            · exact h
          refine short (hpre 1 (by omega) (by omega)) hp ?_ (by omega)
          rw [← hq, hk2]
          show lam (x 0) (x 1) = lam (x 1) (x 2)
          rw [hk2] at he
          rw [← he]; exact hlam _ _ (hadj 0 (by omega))
        · have h0 : adj (x 0) (x (k - 1)) := he ▸ hladj
          have h0l : lam (x 0) (x (k - 1)) = q := he ▸ hllam
          exact short (seg_glue (seg_edge (hsymm _ _ (hadj 0 (by omega)))) (seg_edge h0) rfl
            (by rw [h0l, hrev 0 (by omega), ← hq]; exact hmono 0 (k - 1) (by omega) (by omega)))
            (by rw [hrev 0 (by omega), hp]) h0l (by omega)
    · rcases Nat.lt_or_ge b k with hb | hb
      · exact short (seg_glue (hpre a ha (by omega)) (hsuf b hb) he
          (hmono (a - 1) b (by omega) hb)) hp hq (by omega)
      · rw [show b = k by omega] at he
        have ha2 : a + 2 ≤ k := by
          by_contra h
          obtain rfl : a = k - 1 := by omega
          exact hirr _ (he ▸ hladj)
        exact short (seg_glue (hpre a ha (by omega)) (seg_edge hladj) he
          (by rw [hllam, ← hq]; exact hmono (a - 1) (k - 1) (by omega) (by omega))) hp hllam
          (by omega)
  -- Neighbours of `x i` whose labels lie strictly between the two path labels at `x i`.
  set A : ℕ → Finset V := fun i => univ.filter (fun y => adj (x i) y ∧ lab lam x i < lam (x i) y ∧
    lam (x i) y < lab lam x (i - 1)) with hA
  have hmemA : ∀ i y, y ∈ A i ↔ adj (x i) y ∧ lab lam x i < lam (x i) y ∧
      lam (x i) y < lab lam x (i - 1) := fun i y => by simp [hA]
  have hcardA : ∀ i, 0 < i → i < k → lab lam x (i - 1) ≤ (A i).card + 1 + lab lam x i := by
    intro i hi hik
    have h1 : adj (x i) (x (i - 1)) := by
      have := hsymm _ _ (hadj (i - 1) (by omega)); rwa [Nat.sub_add_cancel hi] at this
    have h1l : lam (x i) (x (i - 1)) = lab lam x (i - 1) := by
      have := hrev (i - 1) (by omega); rwa [Nat.sub_add_cancel hi] at this
    have hsub : Ioo (lab lam x i) (lab lam x (i - 1)) ⊆ (A i).image (lam (x i)) := by
      intro t ht
      rw [mem_Ioo] at ht
      obtain ⟨w, hw, hwl⟩ := hint (x i) (x (i + 1)) (x (i - 1)) (hadj i hik) h1 t ht.1.le
        (h1l ▸ ht.2.le)
      exact mem_image.mpr ⟨w, (hmemA i w).mpr ⟨hw, hwl ▸ ht.1, hwl ▸ ht.2⟩, hwl⟩
    have := (card_le_card hsub).trans card_image_le
    rw [Nat.card_Ioo] at this
    omega
  -- Claim 1: no path vertex lies in any `A i`.
  have hC1 : ∀ i j, 0 < i → i < k → j ≤ k → x j ∉ A i := by
    intro i j hi hik hjk hmem
    obtain ⟨hij, hlo, hhi⟩ := (hmemA i (x j)).mp hmem
    have hji : lam (x j) (x i) = lam (x i) (x j) := (hlam _ _ hij).symm
    by_cases e1 : j = i
    · subst e1; exact hirr _ hij
    by_cases e2 : j = i + 1
    · subst e2; exact lt_irrefl _ hlo
    by_cases e3 : j + 1 = i
    · subst e3
      rw [Nat.add_sub_cancel] at hhi
      exact lt_irrefl _ (hji ▸ hhi)
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have hi3 : 3 ≤ i := by
        by_contra h
        obtain rfl : i = 2 := by omega
        exact htf _ _ _ (hadj 0 (by omega)) (hadj 1 (by omega)) (hsymm _ _ hij)
      exact short (seg_glue (seg_glue (seg_edge (hsymm _ _ (hadj 0 (by omega))))
          (seg_edge (hsymm _ _ hij)) rfl
          (by rw [hji, hrev 0 (by omega)]; exact hhi.le.trans (hmono 0 (i - 1) (by omega)
            (by omega)))) (hsuf i hik) rfl (by rw [hji]; exact hlo.le))
        (by rw [hrev 0 (by omega), hp]) hq (by omega)
    rcases Nat.lt_or_ge j i with hji' | hji'
    · exact short (seg_glue (seg_glue (hpre j hj0 (by omega)) (seg_edge (hsymm _ _ hij)) rfl
          (by rw [hji]; exact hhi.le.trans (hmono (j - 1) (i - 1) (by omega) (by omega))))
          (hsuf i hik) rfl (by rw [hji]; exact hlo.le)) hp hq (by omega)
    rcases Nat.lt_or_ge j k with hjk' | hjk'
    · exact short (seg_glue (seg_glue (hpre i hi hik.le) (seg_edge hij) rfl hhi.le)
          (hsuf j hjk') rfl ((hmono i j (by omega) hjk').trans hlo.le)) hp hq (by omega)
    · have hjk2 : j = k := by omega
      rw [hjk2] at hij hlo hhi
      have hi3 : i + 3 ≤ k := by
        by_contra h
        rw [show k = i + 2 by omega] at hij
        exact htf _ _ _ (hadj i hik) (hadj (i + 1) (by omega)) hij
      have hq' : lab lam x (k - 1) ≤ lam (x i) (x k) :=
        (hmono i (k - 1) (by omega) (by omega)).trans hlo.le
      exact short (seg_glue (seg_glue (hpre i hi hik.le) (seg_edge hij) rfl hhi.le)
          (seg_edge hladj) rfl (by rw [hllam, ← hq]; exact hq')) hp hllam (by omega)
  -- Claim 2: the sets `A i` are pairwise disjoint.
  have hC2 : ∀ i j v, 0 < i → i < j → j < k → v ∈ A i → v ∈ A j → False := by
    intro i j v hi hij hjk hvi hvj
    obtain ⟨hai, hloi, hhii⟩ := (hmemA i v).mp hvi
    obtain ⟨haj, hloj, hhij⟩ := (hmemA j v).mp hvj
    have hvl : lam v (x j) = lam (x j) v := hlam _ _ (hsymm _ _ haj)
    have hj2 : i + 2 ≤ j := by
      by_contra h
      obtain rfl : j = i + 1 := by omega
      exact htf _ _ _ (hadj i (by omega)) haj hai
    have e1 : x i = edge (x i) v 0 := rfl
    have hseg := seg_glue (seg_glue (seg_glue (hpre i hi (by omega)) (seg_edge hai) rfl hhii.le)
      (seg_edge (hsymm _ _ haj)) rfl (by
        rw [hvl]; exact hhij.le.trans ((hmono i (j - 1) (by omega) (by omega)).trans hloi.le)))
      (hsuf j hjk) rfl (by rw [hvl]; exact hloj.le)
    rcases Nat.lt_or_ge (i + 2) j with hj3 | hj3
    · exact short hseg hp hq (by omega)
    · rw [show i + 1 + 1 + (k - j) = k by omega, hp, hq] at hseg
      have := hlex _ hseg.1 i (by omega) (fun n hn => by
        rw [lab_glue_lt (by omega), lab_glue_lt (by omega), lab_glue_lt hn])
      rw [lab_glue_lt (by omega), lab_glue_lt (by omega), lab_glue_ge e1 le_rfl, Nat.sub_self]
        at this
      exact absurd hloi (not_lt.mpr (by simpa [lab, edge] using this))
  -- Counting.
  set T : ℕ → Finset V := fun m => univ.filter (fun y => (∃ n ≤ m, y = x n) ∨
    ∃ n, 0 < n ∧ n < m ∧ y ∈ A n) with hT
  have hmemT : ∀ m y, y ∈ T m ↔ (∃ n ≤ m, y = x n) ∨ ∃ n, 0 < n ∧ n < m ∧ y ∈ A n :=
    fun m y => by simp [hT]
  have hcount : ∀ m, 1 ≤ m → m ≤ k → p + 2 ≤ (T m).card + lab lam x (m - 1) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      have hsub : ({x 0, x 1} : Finset V) ⊆ T 1 := by
        intro y hy
        rw [mem_insert, mem_singleton] at hy
        rw [hmemT]
        rcases hy with rfl | rfl
        · exact Or.inl ⟨0, by omega, rfl⟩
        · exact Or.inl ⟨1, le_rfl, rfl⟩
      have := card_le_card hsub
      rw [card_pair_eq_two_iff.mpr (hinj 0 1 (by omega) (by omega))] at this
      simp only [Nat.sub_self, hp]
      omega
    | succ m hm ih =>
      intro hmk
      have ih := ih (by omega)
      have hsub : insert (x (m + 1)) (T m ∪ A m) ⊆ T (m + 1) := by
        intro y hy
        rw [mem_insert, mem_union] at hy
        rw [hmemT]
        rcases hy with rfl | hy | hy
        · exact Or.inl ⟨m + 1, le_rfl, rfl⟩
        · rcases (hmemT m y).mp hy with ⟨n, hn, rfl⟩ | ⟨n, hn0, hnm, hn⟩
          · exact Or.inl ⟨n, by omega, rfl⟩
          · exact Or.inr ⟨n, hn0, by omega, hn⟩
        · exact Or.inr ⟨m, by omega, by omega, hy⟩
      have hdisj : Disjoint (T m) (A m) := by
        rw [disjoint_left]
        intro y hyT hyA
        rcases (hmemT m y).mp hyT with ⟨n, hn, rfl⟩ | ⟨n, hn0, hnm, hn⟩
        · exact hC1 m n (by omega) (by omega) (by omega) hyA
        · exact hC2 n m y hn0 hnm (by omega) hn hyA
      have hnot : x (m + 1) ∉ T m ∪ A m := by
        rw [mem_union, not_or]
        refine ⟨fun h => ?_, hC1 m (m + 1) (by omega) (by omega) hmk⟩
        rcases (hmemT m _).mp h with ⟨n, hn, he⟩ | ⟨n, hn0, hnm, hn⟩
        · exact hinj n (m + 1) (by omega) hmk he.symm
        · exact hC1 n (m + 1) hn0 (by omega) hmk hn
      have := card_le_card hsub
      rw [card_insert_of_notMem hnot, card_union_of_disjoint hdisj] at this
      have hA' := hcardA m (by omega) (by omega)
      rw [Nat.add_sub_cancel]
      omega
  have hfin := hcount k hk0 le_rfl
  have hsubT : T k ⊆ active adj := by
    intro y hy
    rw [mem_active]
    rcases (hmemT k y).mp hy with ⟨n, hn, rfl⟩ | ⟨n, _, _, hn⟩
    · rcases Nat.lt_or_ge n k with h | h
      · exact ⟨_, hadj n h⟩
      · rw [show n = k by omega]
        exact ⟨_, hladj⟩
    · exact ⟨_, hsymm _ _ ((hmemA n y).mp hn).1⟩
  have := card_le_card hsubT
  rw [hq] at hfin
  omega

/-! ## Reachability in the time-expanded graph and the induction on the top label -/

/-- Nodes `(v, t)` reachable from level `N` by horizontal moves along label-`t` edges and
downward moves inside the label interval of `v`. -/
inductive Reach (adj : V → V → Prop) (lam : V → V → ℕ) (N : ℕ) : V → ℕ → Prop
  | top {u v : V} : adj u v → lam u v = N → Reach adj lam N u N
  | horiz {u v : V} {t : ℕ} : Reach adj lam N u t → adj u v → lam u v = t → Reach adj lam N v t
  | down {v w : V} {t : ℕ} : Reach adj lam N v (t + 1) → adj v w → lam v w = t →
      Reach adj lam N v t

theorem layers_le_active [Fintype V] [DecidableEq V] (N : ℕ) :
    ∀ (adj : V → V → Prop) (lam : V → V → ℕ),
    (∀ u v, adj u v → adj v u) → (∀ v, ¬ adj v v) →
    (∀ u v, adj u v → lam u v = lam v u) →
    (∀ u v w, adj u v → adj v w → ¬ adj u w) →
    (∀ v u₁ u₂, adj v u₁ → adj v u₂ → ∀ t, lam v u₁ ≤ t → t ≤ lam v u₂ →
      ∃ w, adj v w ∧ lam v w = t) →
    (∀ t ≤ N, ∃ u v, adj u v ∧ lam u v = t) →
    N + 2 ≤ (active adj).card := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro adj lam hsymm hirr hlam htf hint hsurj
  classical
  have R1 : ∀ v t, Reach adj lam N v t → ∃ u, adj v u ∧ lam v u = t := by
    intro v t h
    induction h with
    | top h hl => exact ⟨_, h, hl⟩
    | horiz _ h hl _ => exact ⟨_, hsymm _ _ h, (hlam _ _ h).symm.trans hl⟩
    | down _ h hl _ => exact ⟨_, h, hl⟩
  have R2 : ∀ w u t, Reach adj lam N w t → adj w u → lam w u ≤ t → Reach adj lam N w (lam w u) := by
    intro w u t hr hu hle
    obtain ⟨d, hd⟩ : ∃ d, t = lam w u + d := ⟨t - lam w u, by omega⟩
    subst hd
    induction d with
    | zero => simpa using hr
    | succ d ihd =>
      obtain ⟨u₂, hu₂, hl₂⟩ := R1 _ _ hr
      obtain ⟨w', hw', hl'⟩ := hint w u u₂ hu hu₂ (lam w u + d) (by omega) (by omega)
      exact ihd (Reach.down hr hw' hl') (by omega)
  -- The graph of edges whose nodes lie in the reachable set.
  let adjD : V → V → Prop := fun u v => adj u v ∧ Reach adj lam N u (lam u v)
  have hDsymm : ∀ u v, adjD u v → adjD v u := fun u v ⟨h, hr⟩ =>
    ⟨hsymm _ _ h, (hlam _ _ h) ▸ Reach.horiz hr h rfl⟩
  have R3 : ∀ v t, Reach adj lam N v t →
      ∃ y k f l s, Seg adjD lam y k f l s v ∧ f = N ∧ t ≤ l := by
    intro v t h
    induction h with
    | @top u v h hl =>
      have hvu : lam v u = N := (hlam _ _ h) ▸ hl
      exact ⟨_, _, _, _, _, seg_edge (adj := adjD) ⟨hsymm _ _ h, by rw [hvu]; exact Reach.top (hsymm _ _ h) hvu⟩,
        hvu, hvu.ge⟩
    | @horiz u v t hr h hl ihr =>
      obtain ⟨y, k, f, l, s, hs, hf, ht⟩ := ihr
      exact ⟨_, _, _, _, _, seg_glue hs (seg_edge (adj := adjD) ⟨h, hl ▸ hr⟩) rfl (hl ▸ ht), hf,
        hl.ge⟩
    | down _ _ _ ihr =>
      obtain ⟨y, k, f, l, s, hs, hf, ht⟩ := ihr
      exact ⟨y, k, f, l, s, hs, hf, by omega⟩
  obtain ⟨u₀, v₀, h₀, hl₀⟩ := hsurj N le_rfl
  have hex : ∃ c, ∃ z, Reach adj lam N z c := ⟨N, u₀, Reach.top h₀ hl₀⟩
  set c := Nat.find hex
  obtain ⟨z, hz⟩ : ∃ z, Reach adj lam N z c := Nat.find_spec hex
  have hcmin : ∀ v t, Reach adj lam N v t → c ≤ t := fun v t h => Nat.find_min' hex ⟨v, h⟩
  have hcN : c ≤ N := hcmin _ _ (Reach.top h₀ hl₀)
  obtain ⟨u, hu, hul⟩ := R1 _ _ hz
  obtain ⟨y, k, f, l, s, hs, hf, hcl⟩ := R3 _ _ hz
  have hwalk := seg_glue hs (seg_edge (adj := adjD) ⟨hu, hul ▸ hz⟩) rfl (hul ▸ hcl)
  have hD := walk_bound (adj := adjD) hDsymm (fun v h => hirr v h.1) (fun u v h => hlam u v h.1)
    (fun u v w h1 h2 h3 => htf u v w h1.1 h2.1 h3.1)
    (fun v u₁ u₂ h₁ h₂ t ht₁ ht₂ => by
      obtain ⟨w, hw, hwl⟩ := hint v u₁ u₂ h₁.1 h₂.1 t ht₁ ht₂
      exact ⟨w, ⟨hw, R2 v w _ h₂.2 hw (hwl ▸ ht₂)⟩, hwl⟩) hwalk.1
  rw [hf, hul] at hD
  have hDsub : active adjD ⊆ active adj := fun v hv => by
    obtain ⟨w, hw⟩ := mem_active.mp hv; exact mem_active.mpr ⟨w, hw.1⟩
  rcases Nat.eq_zero_or_pos c with hc0 | hc0
  · have := card_le_card hDsub; omega
  -- Layers below `c` form a smaller instance on vertices disjoint from the reachable ones.
  let adjL : V → V → Prop := fun u v => adj u v ∧ lam u v < c
  have hL := ih (c - 1) (by omega) adjL lam
    (fun u v h => ⟨hsymm _ _ h.1, (hlam _ _ h.1) ▸ h.2⟩) (fun v h => hirr v h.1)
    (fun u v h => hlam u v h.1) (fun u v w h1 h2 h3 => htf u v w h1.1 h2.1 h3.1)
    (fun v u₁ u₂ h₁ h₂ t ht₁ ht₂ => by
      obtain ⟨w, hw, hwl⟩ := hint v u₁ u₂ h₁.1 h₂.1 t ht₁ ht₂
      exact ⟨w, ⟨hw, by omega⟩, hwl⟩)
    (fun t ht => by
      obtain ⟨a, b, hab, habl⟩ := hsurj t (by omega)
      exact ⟨a, b, ⟨hab, by omega⟩, habl⟩)
  have hdisj : Disjoint (active adjL) (active adjD) := by
    rw [disjoint_left]
    intro v hvL hvD
    obtain ⟨a, ha, hal⟩ := mem_active.mp hvL
    obtain ⟨b, hb, hbr⟩ := mem_active.mp hvD
    have := hcmin _ _ hbr
    have := hcmin _ _ (R2 v a _ hbr ha (by omega))
    omega
  have hLsub : active adjL ⊆ active adj := fun v hv => by
    obtain ⟨w, hw⟩ := mem_active.mp hv; exact mem_active.mpr ⟨w, hw.1⟩
  have := card_le_card (union_subset hLsub hDsub)
  rw [card_union_of_disjoint hdisj] at this
  omega

/-! ## Exported statements -/

def TriangleFree (G : SimpleGraph V) : Prop :=
  ∀ u v w : V, G.Adj u v → G.Adj v w → ¬ G.Adj u w

def SurjectiveLayers (G : SimpleGraph V) (lam : V → V → ℕ) (N : ℕ) : Prop :=
  (∀ u v, G.Adj u v → lam u v ≤ N) ∧ (∀ t ≤ N, ∃ u v, G.Adj u v ∧ lam u v = t)

def IntervalAt (G : SimpleGraph V) (lam : V → V → ℕ) : Prop :=
  ∀ v : V, ∀ u₁ u₂ : V, G.Adj v u₁ → G.Adj v u₂ → ∀ t : ℕ, lam v u₁ ≤ t → t ≤ lam v u₂ →
    ∃ w : V, G.Adj v w ∧ lam v w = t

/-- `lam` is a labelling of the (undirected) edges of `G`. -/
def EdgeSymm (G : SimpleGraph V) (lam : V → V → ℕ) : Prop :=
  ∀ u v, G.Adj u v → lam u v = lam v u

/-- Non-increasing walk version of the monotone path count, on active vertices. -/
theorem monotone_walk_active_bound [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (lam : V → V → ℕ) (hsym : EdgeSymm G lam) (htf : TriangleFree G) (hint : IntervalAt G lam)
    (x : ℕ → V) (k : ℕ) (hk : 1 ≤ k) (hadj : ∀ n < k, G.Adj (x n) (x (n + 1)))
    (hmono : ∀ n, n + 1 < k → lam (x (n + 1)) (x (n + 2)) ≤ lam (x n) (x (n + 1))) :
    lam (x 0) (x 1) + 2 ≤ (active G.Adj).card + lam (x (k - 1)) (x k) := by
  have h := walk_bound (adj := G.Adj) (fun _ _ h => h.symm) (fun _ => G.irrefl) hsym htf hint
    (x₀ := x) (k₁ := k) (p := lab lam x 0) (q := lab lam x (k - 1)) ⟨⟨hadj, hmono⟩, hk, rfl, rfl⟩
  simpa only [lab, Nat.sub_add_cancel hk] using h

/-- Asratian–Kamalian type count: a non-increasing simple path with first label `p` and last
label `q` in a triangle-free interval-labelled graph forces `p - q + 2 ≤ |V|`. -/
theorem monotone_path_vertex_bound [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (lam : V → V → ℕ) (hsym : EdgeSymm G lam) (htf : TriangleFree G) (hint : IntervalAt G lam)
    (x : ℕ → V) (k : ℕ) (hk : 1 ≤ k) (hadj : ∀ n < k, G.Adj (x n) (x (n + 1)))
    (_hinj : ∀ a b, a ≤ k → b ≤ k → x a = x b → a = b)
    (hmono : ∀ n, n + 1 < k → lam (x (n + 1)) (x (n + 2)) ≤ lam (x n) (x (n + 1))) :
    lam (x 0) (x 1) - lam (x (k - 1)) (x k) + 2 ≤ Fintype.card V := by
  have h := monotone_walk_active_bound G lam hsym htf hint x k hk hadj hmono
  have := card_le_univ (active G.Adj)
  have hm := chain_mono (adj := G.Adj) (lam := lam) ⟨hadj, hmono⟩ (Nat.zero_le (k - 1)) (by omega)
  simp only [lab, Nat.zero_add, Nat.sub_add_cancel hk] at hm
  omega

theorem triangle_free_interval_layers_le_active [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (lam : V → V → ℕ) (N : ℕ) (hsym : EdgeSymm G lam) (htf : TriangleFree G)
    (hsurj : SurjectiveLayers G lam N) (hint : IntervalAt G lam) :
    N + 2 ≤ (active G.Adj).card :=
  layers_le_active N G.Adj lam (fun _ _ h => h.symm) (fun _ => G.irrefl) hsym htf hint hsurj.2

/-- Graph form of Conjecture 7.1 for `r = 2`: `N + 1` nonempty layers force `N + 1 ≤ |V| - 1`. -/
theorem triangle_free_interval_layers_le [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (lam : V → V → ℕ) (N : ℕ) (hsym : EdgeSymm G lam) (htf : TriangleFree G)
    (hsurj : SurjectiveLayers G lam N) (hint : IntervalAt G lam) :
    N + 2 ≤ Fintype.card V :=
  (triangle_free_interval_layers_le_active G lam N hsym htf hsurj hint).trans (card_le_univ _)

/-! ## The family formulation of §2 and §7 -/

/-- A flag 1-layered family of 2-subsets of `V` with layers `L 0, …, L N`: the layers are
nonempty, pairwise disjoint and consist of 2-sets; for every nonempty `S` the set of layers
containing a superset of `S` is an interval; and no three vertices have all three pairs in
the family. -/
def FlagOneLayered [DecidableEq V] {N : ℕ} (L : Fin (N + 1) → Finset (Finset V)) : Prop :=
  (∀ t, (L t).Nonempty) ∧
  (∀ t t', t ≠ t' → Disjoint (L t) (L t')) ∧
  (∀ t, ∀ F ∈ L t, F.card = 2) ∧
  (∀ S : Finset V, S.Nonempty → ∀ t₁ t t₂ : Fin (N + 1), t₁ ≤ t → t ≤ t₂ →
    (∃ F ∈ L t₁, S ⊆ F) → (∃ F ∈ L t₂, S ⊆ F) → ∃ F ∈ L t, S ⊆ F) ∧
  (∀ a b c : V, {a, b} ∈ univ.biUnion L → {b, c} ∈ univ.biUnion L → {a, c} ∈ univ.biUnion L →
    False)

/-- Edge relation of a family of 2-sets. -/
def famAdj [DecidableEq V] {N : ℕ} (L : Fin (N + 1) → Finset (Finset V)) (u v : V) : Prop :=
  ∃ t, ({u, v} : Finset V) ∈ L t

/-- Layer index of the pair `{u, v}` (0 if it is not in the family). -/
noncomputable def famLam [DecidableEq V] {N : ℕ} (L : Fin (N + 1) → Finset (Finset V))
    (u v : V) : ℕ := by
  classical exact if h : famAdj L u v then (h.choose : ℕ) else 0

theorem famLam_spec [DecidableEq V] {N : ℕ} {L : Fin (N + 1) → Finset (Finset V)}
    (hdisj : ∀ t t', t ≠ t' → Disjoint (L t) (L t')) {u v : V} {t : Fin (N + 1)}
    (h : ({u, v} : Finset V) ∈ L t) : famLam L u v = t := by
  have h' : famAdj L u v := ⟨t, h⟩
  unfold famLam
  rw [dif_pos h']
  by_contra hne
  exact disjoint_left.mp (hdisj _ _ (fun e => hne (congrArg Fin.val e))) h'.choose_spec h

/-- Conjecture 7.1 of arXiv:2611.08071 for `r = 2`: a flag 1-layered family of 2-subsets of
`V` with `N + 1` layers satisfies `N + 1 ≤ |V| - 1`. -/
theorem flag_one_layered_r2_le [Fintype V] [DecidableEq V] {N : ℕ}
    (L : Fin (N + 1) → Finset (Finset V)) (hL : FlagOneLayered L) : N + 2 ≤ Fintype.card V := by
  obtain ⟨hne, hdisj, hcard, hint, hflag⟩ := hL
  have pair_of : ∀ t, ∀ F ∈ L t, ∃ a b, a ≠ b ∧ F = {a, b} := fun t F hF =>
    card_eq_two.mp (hcard t F hF)
  have hsymm : ∀ u v, famAdj L u v → famAdj L v u := fun u v ⟨t, h⟩ =>
    ⟨t, by rw [pair_comm]; exact h⟩
  have hlam : ∀ u v, famAdj L u v → famLam L u v = famLam L v u := fun u v ⟨t, h⟩ => by
    rw [famLam_spec hdisj h, famLam_spec hdisj (by rw [pair_comm]; exact h)]
  have hmemU : ∀ u v, famAdj L u v → ({u, v} : Finset V) ∈ univ.biUnion L := fun u v ⟨t, h⟩ =>
    mem_biUnion.mpr ⟨t, mem_univ _, h⟩
  refine (layers_le_active N (famAdj L) (famLam L) hsymm ?_ hlam ?_ ?_ ?_).trans
    (card_le_univ _)
  · rintro v ⟨t, h⟩
    have := hcard t _ h
    simp at this
  · intro u v w h1 h2 h3
    exact hflag u v w (hmemU _ _ h1) (hmemU _ _ h2) (hmemU _ _ h3)
  · rintro v u₁ u₂ ⟨t₁, h₁⟩ ⟨t₂, h₂⟩ t ht₁ ht₂
    rw [famLam_spec hdisj h₁] at ht₁
    rw [famLam_spec hdisj h₂] at ht₂
    have htN : t < N + 1 := by have := t₂.isLt; omega
    obtain ⟨F, hF, hvF⟩ := hint {v} (singleton_nonempty v) t₁ ⟨t, htN⟩ t₂
      (Fin.le_iff_val_le_val.mpr ht₁) (Fin.le_iff_val_le_val.mpr ht₂)
      ⟨_, h₁, by simp⟩ ⟨_, h₂, by simp⟩
    obtain ⟨a, b, -, rfl⟩ := pair_of _ F hF
    have hv : v = a ∨ v = b := by simpa using hvF
    rcases hv with rfl | rfl
    · exact ⟨b, ⟨_, hF⟩, famLam_spec hdisj hF⟩
    · rw [pair_comm] at hF
      exact ⟨a, ⟨_, hF⟩, famLam_spec hdisj hF⟩
  · intro t ht
    obtain ⟨F, hF⟩ := hne ⟨t, by omega⟩
    obtain ⟨a, b, -, rfl⟩ := pair_of _ F hF
    exact ⟨a, b, ⟨_, hF⟩, famLam_spec hdisj hF⟩

/-! ## Tightness -/

/-- The edge `{i, i+1}` of the path on `Fin m`. -/
def pe (m i : ℕ) (h : i + 1 < m) : Finset (Fin m) := {⟨i, by omega⟩, ⟨i + 1, h⟩}

theorem mem_pe {m i : ℕ} {h : i + 1 < m} {a : Fin m} : a ∈ pe m i h ↔ a.val = i ∨ a.val = i + 1 := by
  simp [pe, Fin.ext_iff]

theorem pair_eq_pe {m i : ℕ} {h : i + 1 < m} {a b : Fin m} (he : ({a, b} : Finset (Fin m)) = pe m i h) :
    (a.val = i ∧ b.val = i + 1) ∨ (a.val = i + 1 ∧ b.val = i) := by
  have ha : a ∈ pe m i h := he ▸ mem_insert_self a {b}
  have hb : b ∈ pe m i h := he ▸ mem_insert_of_mem (mem_singleton_self b)
  have hx : (⟨i, by omega⟩ : Fin m) ∈ ({a, b} : Finset (Fin m)) := he ▸ by simp [pe]
  have hy : (⟨i + 1, h⟩ : Fin m) ∈ ({a, b} : Finset (Fin m)) := he ▸ by simp [pe]
  rw [mem_pe] at ha hb
  simp only [mem_insert, mem_singleton, Fin.ext_iff] at hx hy
  omega

/-- The path on `Fin m` with `lam i (i+1) = i` is a flag 1-layered family of 2-sets with
`m - 2 + 1 = m - 1` layers, so `flag_one_layered_r2_le` is attained. -/
theorem path_attains_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ L : Fin (m - 2 + 1) → Finset (Finset (Fin m)), FlagOneLayered L ∧
      m - 2 + 2 = Fintype.card (Fin m) := by
  have hlt : ∀ t : Fin (m - 2 + 1), t.val + 1 < m := fun t => by have := t.isLt; omega
  refine ⟨fun t => {pe m t.val (hlt t)}, ⟨fun t => singleton_nonempty _, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t t' htt
    rw [disjoint_singleton]
    intro he
    have h1 := pair_eq_pe he.symm
    simp only at h1
    have htt' : t.val ≠ t'.val := fun h => htt (Fin.ext h)
    omega
  · intro t F hF
    rw [mem_singleton] at hF
    rw [hF, pe, card_pair_eq_two_iff]
    simp [Fin.ext_iff]
  · intro S ⟨s, hs⟩ t₁ t t₂ h₁ h₂ ⟨F₁, hF₁, hS₁⟩ ⟨F₂, hF₂, hS₂⟩
    rw [mem_singleton] at hF₁ hF₂
    subst hF₁ hF₂
    have hs₁ := mem_pe.mp (hS₁ hs)
    have hs₂ := mem_pe.mp (hS₂ hs)
    rw [Fin.le_iff_val_le_val] at h₁ h₂
    by_cases ht : t.val = t₁.val
    · obtain rfl : t = t₁ := Fin.ext ht
      exact ⟨_, mem_singleton_self _, hS₁⟩
    · obtain rfl : t = t₂ := Fin.ext (by omega)
      exact ⟨_, mem_singleton_self _, hS₂⟩
  · intro a b c hab hbc hac
    simp only [mem_biUnion, mem_univ, mem_singleton, true_and] at hab hbc hac
    obtain ⟨t₁, h₁⟩ := hab
    obtain ⟨t₂, h₂⟩ := hbc
    obtain ⟨t₃, h₃⟩ := hac
    have := pair_eq_pe h₁
    have := pair_eq_pe h₂
    have := pair_eq_pe h₃
    omega
  · simp; omega

end FlagLayeredR2

#print axioms FlagLayeredR2.monotone_path_vertex_bound
#print axioms FlagLayeredR2.monotone_walk_active_bound
#print axioms FlagLayeredR2.triangle_free_interval_layers_le
#print axioms FlagLayeredR2.triangle_free_interval_layers_le_active
#print axioms FlagLayeredR2.flag_one_layered_r2_le
#print axioms FlagLayeredR2.path_attains_bound
