import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Disproof of Log-Concavity for Unicyclic Connected Zero Forcing Polynomials
# (Mukherjee–Ray, `arXiv:2611.10985v2`, Problem 6.2)

This file formalizes a complete negative resolution of the log-concavity
question in Problem 6.2 of S. Mukherjee and P. Ray, *On the connected zero
forcing polynomial of finite trees* (`arXiv:2611.10985v2`, 25 Nov 2026),
for the entire infinite family of tadpole graphs `T_{m, l}` (`m ≥ 3`, `l ≥ 0`).

Using Mathlib's `SimpleGraph`, `SimpleGraph.Connected`, and the standard
step-by-step zero forcing color-change rule:
1. `zf_meets_fort`: the Fort Lemma for arbitrary simple graphs.
2. `tadpole_czf_iff`: a subset `S ⊆ V(T_{m,l})` is a connected zero forcing set
   iff `(T_{m,l}.induce S).Connected` and `S` contains two adjacent cycle vertices.
3. `tadpole_czf_formula`: exact closed form
   `czfCoeff (tadpoleGraph m l hm) k = N_m(k) + ∑_{a=0}^l A_m(k - a)`.
4. `tadpole_czf_logConcave_iff`: `Z_C(T_{m,l}; x)` is log-concave iff `m ≤ 4 ∨ l ≤ 1`.
5. `tadpole_5_2_counterexample`: explicit 7-vertex unicyclic counterexample `T_{5,2}`
   with `Z_C = 5x² + 7x³ + 10x⁴ + 8x⁵ + 5x⁶ + x⁷` and `7² = 49 < 50 = 5 · 10`.
6. `unicyclic_not_logConcave_every_order_ge_7`: for every `n ≥ 7`, there exists a
   connected unicyclic graph on `Fin n` whose connected zero forcing polynomial
   is not log-concave.
-/

namespace MukherjeeRayUnicyclicZF

/-! ### 1. Standard Zero Forcing, Connected Zero Forcing, and the Fort Lemma -/

/-- One step of the zero forcing color-change rule: some colored vertex `v ∈ B`
has `w` as its unique uncolored neighbor in `G`. -/
def ZeroForcingStep {V : Type*} (G : SimpleGraph V) (B : Set V) (w : V) : Prop :=
  ∃ v ∈ B, G.Adj v w ∧ ∀ u : V, G.Adj v u → u ∉ B → u = w

/-- Reflexive-transitive closure of single-vertex zero forcing steps from `S`. -/
inductive ZFRound {V : Type*} (G : SimpleGraph V) (S : Set V) : Set V → Prop
  | base : ZFRound G S S
  | step {B : Set V} {w : V} : ZFRound G S B → ZeroForcingStep G B w → ZFRound G S (insert w B)

/-- `S` is a zero forcing set of `G` if finitely many forcing steps color all vertices. -/
def IsZeroForcingSet {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ZFRound G S Set.univ

/-- `S` is a connected zero forcing set of `G` if it is a zero forcing set and
induces a connected subgraph (using Mathlib's `SimpleGraph.Connected`). -/
def IsConnectedZFSet {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  IsZeroForcingSet G (S : Set V) ∧ (G.induce (S : Set V)).Connected

/-- Coefficient `Z_C(G, k)` of `x^k` in the connected zero forcing polynomial of `G`. -/
noncomputable def czfCoeff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : ℕ :=
  letI := Classical.decPred (IsConnectedZFSet G)
  ((Finset.univ : Finset (Finset V)).filter (fun S => S.card = k ∧ IsConnectedZFSet G S)).card

/-- Log-concavity of a coefficient sequence `(c 0, ..., c n)` on its positive indices. -/
def IsLogConcaveSeq (c : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n → c k ^ 2 ≥ c (k - 1) * c (k + 1)

/-- A nonempty subset `F` is a fort of `G` if every vertex outside `F` adjacent
to a vertex in `F` has at least two distinct neighbors in `F`. -/
def IsFort {V : Type*} (G : SimpleGraph V) (F : Set V) : Prop :=
  F.Nonempty ∧ ∀ v : V, v ∉ F → ∀ w ∈ F, G.Adj v w → ∃ w' ∈ F, w' ≠ w ∧ G.Adj v w'

private lemma zf_round_disjoint_fort {V : Type*} {G : SimpleGraph V} {S F : Set V}
    (hF : IsFort G F) (hdisj : Disjoint S F) {B : Set V} (hB : ZFRound G S B) :
    Disjoint B F := by
  induction hB with
  | base => exact hdisj
  | step _ hstep ih =>
    rcases hstep with ⟨v, hvB, hvw, huniq⟩
    rw [Set.disjoint_insert_left]
    refine ⟨?_, ih⟩
    intro hwF
    have hvF : v ∉ F := Set.disjoint_left.mp ih hvB
    rcases hF.2 v hvF _ hwF hvw with ⟨w', hw'F, hw'ne, hvw'⟩
    have hw'B : w' ∉ _ := Set.disjoint_right.mp ih hw'F
    exact hw'ne (huniq w' hvw' hw'B)

/-- **Fort Lemma:** Every zero forcing set intersects every fort. -/
theorem zf_meets_fort {V : Type*} {G : SimpleGraph V} {S F : Set V}
    (hZF : IsZeroForcingSet G S) (hF : IsFort G F) : (S ∩ F).Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hdisj : Disjoint S F := Set.disjoint_iff_inter_eq_empty.mpr hemp
  have huniv : Disjoint (Set.univ : Set V) F := zf_round_disjoint_fort hF hdisj hZF
  rcases hF.1 with ⟨x, hx⟩
  exact Set.disjoint_left.mp huniv (Set.mem_univ x) hx

private lemma zf_round_trans {V : Type*} {G : SimpleGraph V} {S B C : Set V}
    (h1 : ZFRound G S B) (h2 : ZFRound G B C) : ZFRound G S C := by
  induction h2 with
  | base => exact h1
  | step _ hstep ih => exact ZFRound.step ih hstep

private lemma zf_round_mono {V : Type*} {G : SimpleGraph V} {S₁ S₂ : Set V}
    (hsub : S₁ ⊆ S₂) {B : Set V} (hB : ZFRound G S₁ B) : ZFRound G S₂ (B ∪ S₂) := by
  induction hB with
  | base =>
    rw [Set.union_eq_right.mpr hsub]
    exact ZFRound.base
  | @step B' w _ hstep ih =>
    by_cases hw : w ∈ B' ∪ S₂
    · have heq : insert w B' ∪ S₂ = B' ∪ S₂ := by
        ext x; simp only [Set.mem_union, Set.mem_insert_iff]
        constructor
        · rintro ((rfl | h1) | h2)
          · exact hw
          · exact Or.inl h1
          · exact Or.inr h2
        · rintro (h1 | h2)
          · exact Or.inl (Or.inr h1)
          · exact Or.inr h2
      rw [heq]; exact ih
    · have heq : insert w B' ∪ S₂ = insert w (B' ∪ S₂) := Set.insert_union
      rw [heq]
      refine ZFRound.step ih ?_
      rcases hstep with ⟨v, hvB, hvw, huniq⟩
      refine ⟨v, Or.inl hvB, hvw, fun u hvu hu => ?_⟩
      exact huniq u hvu (fun huB => hu (Or.inl huB))

private lemma isZeroForcingSet_mono {V : Type*} {G : SimpleGraph V} {S₁ S₂ : Set V}
    (hsub : S₁ ⊆ S₂) (h1 : IsZeroForcingSet G S₁) : IsZeroForcingSet G S₂ := by
  have h := zf_round_mono hsub h1
  rw [Set.univ_union] at h
  exact h

/-! ### 2. Tadpole Graphs `T_{m, l}` (`m ≥ 3`, `l ≥ 0`) -/

/-- Adjacency relation on `Fin (m + l)` for the tadpole graph `T_{m, l}`:
vertices `0, ..., m - 1` form an `m`-cycle, and vertices `m, ..., m + l - 1` form
a pendant path attached at vertex `0`. -/
def tadpoleAdj (m l : ℕ) (u v : Fin (m + l)) : Prop :=
  (u.val < m ∧ v.val < m ∧
    ((u.val + 1) % m = v.val ∨ (v.val + 1) % m = u.val)) ∨
  (u.val = 0 ∧ v.val = m) ∨ (u.val = m ∧ v.val = 0) ∨
  (m ≤ u.val ∧ m ≤ v.val ∧ (u.val + 1 = v.val ∨ v.val + 1 = u.val))

instance (m l : ℕ) : DecidableRel (tadpoleAdj m l) := fun _ _ => by
  unfold tadpoleAdj
  infer_instance

/-- The tadpole graph `T_{m, l}` on `Fin (m + l)` for `m ≥ 3`. -/
def tadpoleGraph (m l : ℕ) (hm : 3 ≤ m) : SimpleGraph (Fin (m + l)) where
  Adj := tadpoleAdj m l
  symm := ⟨fun u v h => by
    rcases h with ⟨hu, hv, h1 | h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hu, hv, h1 | h2⟩
    · exact Or.inl ⟨hv, hu, Or.inr h1⟩
    · exact Or.inl ⟨hv, hu, Or.inl h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hv, hu, Or.inr h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hv, hu, Or.inl h2⟩))⟩
  loopless := ⟨fun v h => by
    rcases h with ⟨hv, _, h1 | h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨_, _, h1 | h2⟩
    · have : (v.val + 1) % m ≠ v.val := by
        by_cases hlast : v.val + 1 = m
        · rw [hlast, Nat.mod_self]; omega
        · rw [Nat.mod_eq_of_lt (by omega)]; omega
      exact this h1
    · have : (v.val + 1) % m ≠ v.val := by
        by_cases hlast : v.val + 1 = m
        · rw [hlast, Nat.mod_self]; omega
        · rw [Nat.mod_eq_of_lt (by omega)]; omega
      exact this h2
    · omega
    · omega
    · omega
    · omega⟩

instance (m l : ℕ) (hm : 3 ≤ m) : DecidableRel (tadpoleGraph m l hm).Adj :=
  fun u v => inferInstanceAs (Decidable (tadpoleAdj m l u v))

/-- Convenience constructor for cycle vertex `c_i` (`i < m`). -/
def cycV {m l : ℕ} (i : ℕ) (hi : i < m) : Fin (m + l) := ⟨i, by omega⟩

/-- Convenience constructor for tail vertex `t_{j+1}` (`j < l`). -/
def tailV {m l : ℕ} (j : ℕ) (hj : j < l) : Fin (m + l) := ⟨m + j, by omega⟩

lemma tadpole_adj_cyc_succ {m l : ℕ} (hm : 3 ≤ m) {i : ℕ} (hi : i < m) :
    (tadpoleGraph m l hm).Adj (cycV i hi) (cycV ((i + 1) % m) (Nat.mod_lt _ (by omega))) :=
  Or.inl ⟨hi, Nat.mod_lt _ (by omega), Or.inl rfl⟩

lemma tadpole_adj_zero_tail {m l : ℕ} (hm : 3 ≤ m) (hl : 0 < l) :
    (tadpoleGraph m l hm).Adj (cycV 0 (by omega)) (tailV 0 hl) :=
  Or.inr (Or.inl ⟨rfl, rfl⟩)

lemma tadpole_adj_tail_succ {m l : ℕ} (hm : 3 ≤ m) {j : ℕ} (hj : j + 1 < l) :
    (tadpoleGraph m l hm).Adj (tailV j (by omega)) (tailV (j + 1) hj) :=
  Or.inr (Or.inr (Or.inr ⟨by simp [tailV], by simp [tailV], Or.inl (by simp [tailV]; omega)⟩))

/-- Neighbors of an interior cycle vertex `c_i` (`1 ≤ i < m`) are exclusively
`c_{i - 1}` and `c_{(i + 1) % m}`. -/
lemma tadpole_adj_cyc_pos_iff {m l : ℕ} (hm : 3 ≤ m) {i : ℕ} (hi1 : 1 ≤ i) (him : i < m)
    (u : Fin (m + l)) :
    (tadpoleGraph m l hm).Adj (cycV i him) u ↔
      u.val = i - 1 ∨ u.val = (i + 1) % m := by
  constructor
  · intro h
    rcases h with ⟨_, hu, h1 | h2⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨hge, _, _⟩
    · exact Or.inr h1.symm
    · left
      by_cases hlast : u.val + 1 = m
      · rw [hlast, Nat.mod_self] at h2; dsimp [cycV] at h2; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at h2; dsimp [cycV] at h2; omega
    · dsimp [cycV] at h0; omega
    · dsimp [cycV] at h0; omega
    · dsimp [cycV] at hge; omega
  · rintro (hu1 | hu2)
    · refine Or.inl ⟨him, by omega, Or.inr ?_⟩
      dsimp [cycV]
      rw [hu1, Nat.sub_add_cancel hi1, Nat.mod_eq_of_lt him]
    · refine Or.inl ⟨him, ?_, Or.inl hu2.symm⟩
      rw [hu2]; exact Nat.mod_lt _ (by omega)

/-- Neighbors of `c_0` are `c_1`, `c_{m - 1}`, and (when `l > 0`) `t_1 = m`. -/
lemma tadpole_adj_zero_iff {m l : ℕ} (hm : 3 ≤ m) (u : Fin (m + l)) :
    (tadpoleGraph m l hm).Adj (cycV 0 (by omega)) u ↔
      u.val = 1 ∨ u.val = m - 1 ∨ u.val = m := by
  constructor
  · intro h
    rcases h with ⟨_, hu, h1 | h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨hge, _, _⟩
    · left; dsimp [cycV] at h1; rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
    · right; left
      by_cases hlast : u.val + 1 = m
      · omega
      · rw [Nat.mod_eq_of_lt (by omega)] at h2; dsimp [cycV] at h2; omega
    · exact Or.inr (Or.inr h2)
    · dsimp [cycV] at h1; omega
    · dsimp [cycV] at hge; omega
  · rintro (hu1 | hu2 | hu3)
    · refine Or.inl ⟨by dsimp [cycV]; omega, by omega, Or.inl ?_⟩
      dsimp [cycV]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · refine Or.inl ⟨by dsimp [cycV]; omega, by omega, Or.inr ?_⟩
      dsimp [cycV]; rw [hu2, Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.mod_self]
    · exact Or.inr (Or.inl ⟨rfl, hu3⟩)

/-- Neighbors of a tail vertex `t_{j+1} = m + j` (`j < l`). -/
lemma tadpole_adj_tail_iff {m l : ℕ} (hm : 3 ≤ m) {j : ℕ} (hj : j < l) (u : Fin (m + l)) :
    (tadpoleGraph m l hm).Adj (tailV j hj) u ↔
      (j = 0 ∧ u.val = 0) ∨ (1 ≤ j ∧ u.val = m + j - 1) ∨ u.val = m + j + 1 := by
  constructor
  · intro h
    rcases h with ⟨hu, _, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨_, hu, h1 | h2⟩
    · dsimp [tailV] at hu; omega
    · dsimp [tailV] at h1; omega
    · dsimp [tailV] at h1; exact Or.inl ⟨by omega, h2⟩
    · dsimp [tailV] at h1; exact Or.inr (Or.inr h1.symm)
    · dsimp [tailV] at h2; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · rintro (⟨hj0, hu0⟩ | ⟨hj1, hu1⟩ | hu2)
    · exact Or.inr (Or.inr (Or.inl ⟨by dsimp [tailV]; omega, hu0⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by dsimp [tailV]; omega, by omega, Or.inr (by dsimp [tailV]; omega)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by dsimp [tailV]; omega, by omega, Or.inl (by dsimp [tailV]; omega)⟩))

/-- `tadpoleGraph m l hm` is connected. -/
theorem tadpoleGraph_connected (m l : ℕ) (hm : 3 ≤ m) :
    (tadpoleGraph m l hm).Connected := by
  have hreach_cyc : ∀ (k : ℕ) (hk : k < m),
      (tadpoleGraph m l hm).Reachable (cycV 0 (by omega)) (cycV k hk) := by
    intro k
    induction k with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ t ih =>
      intro hkm
      have ht : t < m := by omega
      have hstep : (tadpoleGraph m l hm).Adj (cycV t ht) (cycV (t + 1) hkm) := by
        have h := tadpole_adj_cyc_succ (l := l) hm ht
        have heq : cycV (l := l) ((t + 1) % m) (Nat.mod_lt _ (by omega)) = cycV (l := l) (t + 1) hkm :=
          Fin.ext (Nat.mod_eq_of_lt hkm)
        rwa [heq] at h
      exact (ih ht).trans hstep.reachable
  have hreach_tail : ∀ (j : ℕ) (hj : j < l),
      (tadpoleGraph m l hm).Reachable (cycV 0 (by omega)) (tailV j hj) := by
    intro j
    induction j with
    | zero => intro hl; exact (tadpole_adj_zero_tail hm hl).reachable
    | succ t ih =>
      intro hj
      have hstep : (tadpoleGraph m l hm).Adj (tailV t (by omega)) (tailV (t + 1) hj) :=
        tadpole_adj_tail_succ hm hj
      exact (ih (by omega)).trans hstep.reachable
  have hreach0 : ∀ v : Fin (m + l), (tadpoleGraph m l hm).Reachable (cycV 0 (by omega)) v := by
    intro ⟨k, hk⟩
    by_cases hkm : k < m
    · exact hreach_cyc k hkm
    · have hj : k - m < l := by omega
      have heq : tailV (k - m) hj = ⟨k, hk⟩ := Fin.ext (by dsimp [tailV]; omega)
      rw [← heq]
      exact hreach_tail (k - m) hj
  let : Nonempty (Fin (m + l)) := ⟨cycV 0 (by omega)⟩
  exact ⟨fun u v => (hreach0 u).symm.trans (hreach0 v)⟩

/-- `tadpoleGraph m l hm` has exactly `m + l` edges (hence is unicyclic: connected with
`|E| = |V|`). -/
theorem tadpoleGraph_edge_card (m l : ℕ) (hm : 3 ≤ m) :
    ((tadpoleGraph m l hm).edgeFinset).card = m + l := by
  let f : Fin (m + l) → Sym2 (Fin (m + l)) := fun i =>
    if hi : i.val < m then
      s(cycV i.val hi, cycV ((i.val + 1) % m) (Nat.mod_lt _ (by omega)))
    else if h0 : i.val = m then
      s(cycV 0 (by omega), ⟨m, by omega⟩)
    else
      s(⟨i.val - 1, by omega⟩, i)
  have hf_mem : ∀ i : Fin (m + l), f i ∈ (tadpoleGraph m l hm).edgeFinset := by
    intro i
    rw [SimpleGraph.mem_edgeFinset]
    dsimp only [f]
    split_ifs with hi h0
    · exact tadpole_adj_cyc_succ hm hi
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨by dsimp; omega, by dsimp; omega, Or.inl (by dsimp; omega)⟩))
  have hf_inj : Function.Injective f := by
    intro i j hij
    dsimp only [f] at hij
    split_ifs at hij with hi hj hj0 hi0 hj' hi0' hj0'
    · rw [Sym2.eq_iff] at hij
      rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Fin.ext (congr_arg Fin.val h1)
      · have hv1 := congr_arg Fin.val h1
        have hv2 := congr_arg Fin.val h2
        dsimp [cycV] at hv1 hv2
        by_cases h1m : i.val + 1 = m <;> by_cases h2m : j.val + 1 = m
        · omega
        · rw [h1m, Nat.mod_self] at hv2; rw [Nat.mod_eq_of_lt (by omega)] at hv1; omega
        · rw [h2m, Nat.mod_self] at hv1; rw [Nat.mod_eq_of_lt (by omega)] at hv2; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hv1 hv2; omega
    · rw [Sym2.eq_iff] at hij
      rcases hij with ⟨_, h2⟩ | ⟨h1, _⟩
      · have := congr_arg Fin.val h2; dsimp [cycV] at this; have := Nat.mod_lt (i.val + 1) (by omega : 0 < m); omega
      · have := congr_arg Fin.val h1; dsimp [cycV] at this; omega
    · rw [Sym2.eq_iff] at hij
      rcases hij with ⟨_, h2⟩ | ⟨h1, _⟩
      · have := congr_arg Fin.val h2; dsimp [cycV] at this; have := Nat.mod_lt (i.val + 1) (by omega : 0 < m); omega
      · have := congr_arg Fin.val h1; dsimp [cycV] at this; omega
    · rw [Sym2.eq_iff] at hij
      rcases hij with ⟨_, h2⟩ | ⟨_, h2⟩
      · have := congr_arg Fin.val h2; dsimp [cycV] at this; have := Nat.mod_lt (j.val + 1) (by omega : 0 < m); omega
      · have := congr_arg Fin.val h2; dsimp [cycV] at this; omega
    · exact Fin.ext (by omega)
    · rw [Sym2.eq_iff] at hij
      rcases hij with ⟨h1, _⟩ | ⟨h1, _⟩
      · have := congr_arg Fin.val h1; dsimp [cycV] at this; omega
      · have := congr_arg Fin.val h1; dsimp [cycV] at this; omega
    · rw [Sym2.eq_iff] at hij
      rcases hij with ⟨_, h2⟩ | ⟨_, h2⟩
      · have := congr_arg Fin.val h2; dsimp [cycV] at this; have := Nat.mod_lt (j.val + 1) (by omega : 0 < m); omega
      · have := congr_arg Fin.val h2; dsimp [cycV] at this; omega
    · rw [Sym2.eq_iff] at hij
      rcases hij with ⟨h1, _⟩ | ⟨_, h2⟩
      · have := congr_arg Fin.val h1; dsimp [cycV] at this; omega
      · have := congr_arg Fin.val h2; dsimp [cycV] at this; omega
    · rw [Sym2.eq_iff] at hij
      rcases hij with ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · have hv1 := congr_arg Fin.val h1; have hv2 := congr_arg Fin.val h2; dsimp at hv1 hv2; omega
  have hf_surj : ∀ e ∈ (tadpoleGraph m l hm).edgeFinset, ∃ i : Fin (m + l), f i = e := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset] at he
      change tadpoleAdj m l u v at he
      rcases he with ⟨hu, hv, h1 | h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hu, hv, h1 | h2⟩
      · refine ⟨u, ?_⟩
        dsimp only [f]; rw [dif_pos hu]
        have hv_eq : cycV ((u.val + 1) % m) (Nat.mod_lt _ (by omega)) = v := Fin.ext h1
        rw [hv_eq]; rfl
      · refine ⟨v, ?_⟩
        dsimp only [f]; rw [dif_pos hv]
        have hu_eq : cycV ((v.val + 1) % m) (Nat.mod_lt _ (by omega)) = u := Fin.ext h2
        rw [hu_eq, Sym2.eq_swap]; rfl
      · refine ⟨v, ?_⟩
        dsimp only [f]; rw [dif_neg (by omega), dif_pos h2]
        have hu_eq : cycV 0 (by omega) = u := Fin.ext h1.symm
        have hv_eq : (⟨m, by omega⟩ : Fin (m + l)) = v := Fin.ext h2.symm
        rw [hu_eq, hv_eq]
      · refine ⟨u, ?_⟩
        dsimp only [f]; rw [dif_neg (by omega), dif_pos h1]
        have hu_eq : (⟨m, by omega⟩ : Fin (m + l)) = u := Fin.ext h1.symm
        have hv_eq : cycV 0 (by omega) = v := Fin.ext h2.symm
        rw [hu_eq, hv_eq, Sym2.eq_swap]
      · refine ⟨v, ?_⟩
        dsimp only [f]; rw [dif_neg (by omega), dif_neg (by omega)]
        have hu_eq : (⟨v.val - 1, by omega⟩ : Fin (m + l)) = u := Fin.ext (by dsimp; omega)
        rw [hu_eq]
      · refine ⟨u, ?_⟩
        dsimp only [f]; rw [dif_neg (by omega), dif_neg (by omega)]
        have hv_eq : (⟨u.val - 1, by omega⟩ : Fin (m + l)) = v := Fin.ext (by dsimp; omega)
        rw [hv_eq, Sym2.eq_swap]
  have himg : (Finset.univ : Finset (Fin (m + l))).image f = (tadpoleGraph m l hm).edgeFinset := by
    ext e
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ hf_mem i, hf_surj e⟩
  rw [← himg, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]

/-! ### 3. Characterization of Connected Zero Forcing Sets of `T_{m, l}` -/

/-- `S` contains two adjacent cycle vertices of `T_{m, l}`. -/
def HasAdjCyclePair (m l : ℕ) (S : Finset (Fin (m + l))) : Prop :=
  ∃ i : ℕ, ∃ hi : i < m,
    cycV i hi ∈ S ∧ cycV ((i + 1) % m) (Nat.mod_lt _ (by omega)) ∈ S

/-- Forward direction: every connected zero forcing set of `T_{m, l}` contains two
adjacent cycle vertices. -/
lemma czf_implies_adj_cycle_pair {m l : ℕ} (hm : 3 ≤ m) {S : Finset (Fin (m + l))}
    (hS : IsConnectedZFSet (tadpoleGraph m l hm) S) :
    HasAdjCyclePair m l S := by
  -- Fort 1: `F₁ = {c_1, ..., c_{m-1}}`
  let F1 : Set (Fin (m + l)) := {v | 1 ≤ v.val ∧ v.val < m}
  have hF1 : IsFort (tadpoleGraph m l hm) F1 := by
    refine ⟨⟨cycV 1 (by omega), ⟨by dsimp [cycV]; omega, by dsimp [cycV]; omega⟩⟩, ?_⟩
    intro v hv w hw hvw
    have hw1 : 1 ≤ w.val := hw.1
    have hwm : w.val < m := hw.2
    have hw_eq : w = cycV w.val hwm := Fin.ext rfl
    have hvw' : (tadpoleGraph m l hm).Adj (cycV w.val hwm) v := by rw [← hw_eq]; exact hvw.symm
    rcases (tadpole_adj_cyc_pos_iff hm hw1 hwm v).mp hvw' with hv1 | hv2
    · -- `v.val = w.val - 1`; since `v ∉ F1`, we must have `v.val = 0` and `w.val = 1`
      have hv0 : v.val = 0 := by
        by_contra hne
        exact hv ⟨by omega, by omega⟩
      have hw1' : w.val = 1 := by omega
      refine ⟨cycV (m - 1) (by omega), ⟨by dsimp [cycV]; omega, by dsimp [cycV]; omega⟩, ?_, ?_⟩
      · intro heq; have := congr_arg Fin.val heq; dsimp [cycV] at this; omega
      · have hv_eq : v = cycV 0 (by omega) := Fin.ext hv0
        rw [hv_eq, tadpole_adj_zero_iff]
        exact Or.inr (Or.inl rfl)
    · -- `v.val = (w.val + 1) % m`; since `v ∉ F1`, we must have `v.val = 0` and `w.val = m - 1`
      have hv0 : v.val = 0 := by
        by_contra hne
        have hlt : (w.val + 1) % m < m := Nat.mod_lt _ (by omega)
        exact hv ⟨by omega, by omega⟩
      have hwm' : w.val = m - 1 := by
        by_contra hne
        have hlt : w.val + 1 < m := by omega
        rw [Nat.mod_eq_of_lt hlt] at hv2; omega
      refine ⟨cycV 1 (by omega), ⟨by dsimp [cycV]; omega, by dsimp [cycV]; omega⟩, ?_, ?_⟩
      · intro heq; have := congr_arg Fin.val heq; dsimp [cycV] at this; omega
      · have hv_eq : v = cycV 0 (by omega) := Fin.ext hv0
        rw [hv_eq, tadpole_adj_zero_iff]
        exact Or.inl rfl
  rcases zf_meets_fort hS.1 hF1 with ⟨v0, hv0S, hv0F1⟩
  have hv01 : 1 ≤ v0.val := hv0F1.1
  have hv0m : v0.val < m := hv0F1.2
  have hv0_eq : v0 = cycV v0.val hv0m := Fin.ext rfl
  -- Fort 2: `F₂ = Set.univ \ {v0}`
  let F2 : Set (Fin (m + l)) := {v | v ≠ v0}
  have hF2 : IsFort (tadpoleGraph m l hm) F2 := by
    refine ⟨⟨cycV 0 (by omega), fun h => by have := congr_arg Fin.val h; dsimp [cycV] at this; omega⟩, ?_⟩
    intro v hv w hw hvw
    have hvv0 : v = v0 := by
      by_contra hne; exact hv hne
    rw [hvv0] at hvw ⊢
    rw [hv0_eq, tadpole_adj_cyc_pos_iff hm hv01 hv0m] at hvw
    rcases hvw with hw1 | hw2
    · refine ⟨cycV ((v0.val + 1) % m) (Nat.mod_lt _ (by omega)), ?_, ?_, ?_⟩
      · intro h; have := congr_arg Fin.val h; dsimp [cycV] at this
        by_cases hlast : v0.val + 1 = m
        · rw [hlast, Nat.mod_self] at this; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at this; omega
      · intro h; have := congr_arg Fin.val h; dsimp [cycV] at this
        by_cases hlast : v0.val + 1 = m
        · rw [hlast, Nat.mod_self] at this; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at this; omega
      · change (tadpoleGraph m l hm).Adj (cycV v0.val hv0m) _
        exact tadpole_adj_cyc_succ hm hv0m
    · refine ⟨cycV (v0.val - 1) (by omega), ?_, ?_, ?_⟩
      · intro h; have := congr_arg Fin.val h; dsimp [cycV] at this; omega
      · intro h; have := congr_arg Fin.val h; dsimp [cycV] at this
        by_cases hlast : v0.val + 1 = m
        · rw [hlast, Nat.mod_self] at hw2; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hw2; omega
      · change (tadpoleGraph m l hm).Adj (cycV v0.val hv0m) _
        rw [tadpole_adj_cyc_pos_iff hm hv01 hv0m]
        exact Or.inl rfl
  rcases zf_meets_fort hS.1 hF2 with ⟨u0, hu0S, hu0ne⟩
  -- Take a walk in `G.induce S` from `v0` to `u0 ≠ v0`; its first step is a neighbor of `v0` in `S`.
  have hreach : ((tadpoleGraph m l hm).induce (S : Set (Fin (m + l)))).Reachable
      ⟨v0, hv0S⟩ ⟨u0, hu0S⟩ := hS.2 ⟨v0, hv0S⟩ ⟨u0, hu0S⟩
  rcases hreach with ⟨walk⟩
  cases walk with
  | nil => exact absurd rfl hu0ne.symm
  | @cons _ w1 _ hadj _ =>
    have hw1_adj : (tadpoleGraph m l hm).Adj v0 w1.val := hadj
    rw [hv0_eq, tadpole_adj_cyc_pos_iff hm hv01 hv0m] at hw1_adj
    rcases hw1_adj with hprev | hnext
    · refine ⟨v0.val - 1, by omega, ?_, ?_⟩
      · have : cycV (v0.val - 1) (by omega : v0.val - 1 < m) = w1.val := Fin.ext hprev.symm
        rw [this]; exact w1.prop
      · have hmod : (v0.val - 1 + 1) % m = v0.val := by
          rw [Nat.sub_add_cancel hv01, Nat.mod_eq_of_lt hv0m]
        have : cycV ((v0.val - 1 + 1) % m) (Nat.mod_lt _ (by omega)) = v0 := Fin.ext hmod
        rw [this]; exact hv0S
    · refine ⟨v0.val, hv0m, ?_, ?_⟩
      · rwa [← hv0_eq]
      · have : cycV ((v0.val + 1) % m) (Nat.mod_lt _ (by omega)) = w1.val := Fin.ext hnext.symm
        rw [this]; exact w1.prop

/-- Backward direction: any subset containing two adjacent cycle vertices is a zero forcing set. -/
lemma adj_cycle_pair_implies_zf {m l : ℕ} (hm : 3 ≤ m) {S : Finset (Fin (m + l))}
    (hpair : HasAdjCyclePair m l S) :
    IsZeroForcingSet (tadpoleGraph m l hm) (S : Set (Fin (m + l))) := by
  -- Helper 1: forward propagation along `c_1, ..., c_{m-1}`
  have hfwd : ∀ (B : Set (Fin (m + l))) (k : ℕ) (hk : 1 ≤ k) (hkm : k < m),
      cycV (k - 1) (by omega) ∈ B → cycV k hkm ∈ B →
      ZFRound (tadpoleGraph m l hm) B (insert (cycV ((k + 1) % m) (Nat.mod_lt _ (by omega))) B) := by
    intro B k hk hkm hprev hcur
    refine ZFRound.step ZFRound.base ?_
    refine ⟨cycV k hkm, hcur, tadpole_adj_cyc_succ hm hkm, fun u hu huB => ?_⟩
    rw [tadpole_adj_cyc_pos_iff hm hk hkm] at hu
    rcases hu with h1 | h2
    · exact absurd (by have : u = cycV (k - 1) (by omega) := Fin.ext h1; rwa [this]) huB
    · exact Fin.ext h2
  -- Helper 2: backward propagation along `c_{m-1}, ..., c_1`
  have hbwd : ∀ (B : Set (Fin (m + l))) (k : ℕ) (hk : 1 ≤ k) (hkm : k < m),
      cycV k hkm ∈ B → cycV ((k + 1) % m) (Nat.mod_lt _ (by omega)) ∈ B →
      ZFRound (tadpoleGraph m l hm) B (insert (cycV (k - 1) (by omega)) B) := by
    intro B k hk hkm hcur hnext
    refine ZFRound.step ZFRound.base ?_
    refine ⟨cycV k hkm, hcur, (tadpole_adj_cyc_pos_iff hm hk hkm _).mpr (Or.inl rfl),
      fun u hu huB => ?_⟩
    rw [tadpole_adj_cyc_pos_iff hm hk hkm] at hu
    rcases hu with h1 | h2
    · exact Fin.ext h1
    · exact absurd (by have : u = cycV ((k + 1) % m) (Nat.mod_lt _ (by omega)) := Fin.ext h2; rwa [this]) huB
  -- Helper 3: once all `m` cycle vertices are colored, the tail is forced sequentially.
  let Cyc : Set (Fin (m + l)) := {v | v.val < m}
  have hcyc_forces_all : ZFRound (tadpoleGraph m l hm) Cyc Set.univ := by
    have hpref : ∀ a : ℕ, a ≤ l →
        ZFRound (tadpoleGraph m l hm) Cyc {v : Fin (m + l) | v.val < m + a} := by
      intro a
      induction a with
      | zero =>
        intro _; simpa [Cyc] using ZFRound.base
      | succ t ih =>
        intro ht
        have hprev := ih (by omega)
        have hstep : ZFRound (tadpoleGraph m l hm)
            {v : Fin (m + l) | v.val < m + t}
            (insert (tailV t (by omega)) {v : Fin (m + l) | v.val < m + t}) := by
          refine ZFRound.step ZFRound.base ?_
          cases t with
          | zero =>
            refine ⟨cycV 0 (by omega), by dsimp [cycV]; omega, tadpole_adj_zero_tail hm (by omega),
              fun u hu huB => ?_⟩
            rw [tadpole_adj_zero_iff] at hu
            rcases hu with h1 | h2 | h3
            · exact absurd (by show u.val < m + 0; omega) huB
            · exact absurd (by show u.val < m + 0; omega) huB
            · exact Fin.ext h3
          | succ s =>
            refine ⟨tailV s (by omega), by dsimp [tailV]; omega,
              tadpole_adj_tail_succ hm (by omega), fun u hu huB => ?_⟩
            rw [tadpole_adj_tail_iff hm (by omega)] at hu
            rcases hu with ⟨_, h0⟩ | ⟨_, h1⟩ | h2
            · exact absurd (by show u.val < m + (s + 1); omega) huB
            · exact absurd (by show u.val < m + (s + 1); omega) huB
            · exact Fin.ext (by dsimp [tailV]; omega)
        have heq : insert (tailV t (by omega)) {v : Fin (m + l) | v.val < m + t} =
            {v : Fin (m + l) | v.val < m + (t + 1)} := by
          ext v; simp only [Set.mem_insert_iff, Set.mem_ofPred_eq, Fin.ext_iff, tailV]
          omega
        rw [← heq]
        exact zf_round_trans hprev hstep
    have hfull := hpref l le_rfl
    have heq : {v : Fin (m + l) | v.val < m + l} = Set.univ := by
      ext v; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact v.isLt
    rwa [heq] at hfull
  -- Helper 4: from `{c_i, c_{(i+1) % m}}`, force all of `Cyc`.
  rcases hpair with ⟨i, hi, hiS, hi1S⟩
  have hsubS : ({cycV i hi, cycV ((i + 1) % m) (Nat.mod_lt _ (by omega))} : Set (Fin (m + l))) ⊆
      (S : Set (Fin (m + l))) := by
    intro v hv
    rcases hv with rfl | rfl
    · exact hiS
    · exact hi1S
  suffices hpair_zf : IsZeroForcingSet (tadpoleGraph m l hm)
      ({cycV i hi, cycV ((i + 1) % m) (Nat.mod_lt _ (by omega))} : Set (Fin (m + l))) by
    exact isZeroForcingSet_mono hsubS hpair_zf
  -- It suffices to reach `Cyc`, then apply `hcyc_forces_all`.
  suffices hreach_cyc : ZFRound (tadpoleGraph m l hm)
      ({cycV i hi, cycV ((i + 1) % m) (Nat.mod_lt _ (by omega))} : Set (Fin (m + l))) Cyc by
    exact zf_round_trans hreach_cyc hcyc_forces_all
  -- Forward sweep from `i + 1` to `m` and backward sweep from `i` to `0`
  by_cases hi0 : i = 0
  · subst hi0
    have hbase_eq : ({cycV 0 hi, cycV ((0 + 1) % m) (Nat.mod_lt _ (by omega))} : Set (Fin (m + l))) =
        {v : Fin (m + l) | v.val ≤ 1} := by
      ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, Fin.ext_iff, cycV]
      rw [Nat.mod_eq_of_lt (by omega : 0 + 1 < m)]
      omega
    rw [hbase_eq]
    have hgrow : ∀ t : ℕ, 1 ≤ t → t ≤ m - 1 →
        ZFRound (tadpoleGraph m l hm) {v : Fin (m + l) | v.val ≤ 1} {v : Fin (m + l) | v.val ≤ t} := by
      intro t ht1
      induction t, ht1 using Nat.le_induction with
      | base => intro _; exact ZFRound.base
      | succ k hk ih =>
        intro hkm
        have h1 := ih (by omega)
        have hstep := hfwd {v : Fin (m + l) | v.val ≤ k} k hk (by omega)
          (by dsimp [cycV]; omega) (by dsimp [cycV]; omega)
        have hmod : (k + 1) % m = k + 1 := Nat.mod_eq_of_lt (by omega)
        have heq : insert (cycV ((k + 1) % m) (Nat.mod_lt _ (by omega)))
            {v : Fin (m + l) | v.val ≤ k} = {v : Fin (m + l) | v.val ≤ k + 1} := by
          ext v; simp only [Set.mem_insert_iff, Set.mem_ofPred_eq, Fin.ext_iff, cycV, hmod]; omega
        rw [← heq]
        exact zf_round_trans h1 hstep
    have hend := hgrow (m - 1) (by omega) le_rfl
    have hcyc_eq : {v : Fin (m + l) | v.val ≤ m - 1} = Cyc := by
      ext v; simp only [Set.mem_ofPred_eq, Cyc]; omega
    rwa [hcyc_eq] at hend
  · by_cases him1 : i = m - 1
    · subst him1
      have hmod : (m - 1 + 1) % m = 0 := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.mod_self]
      have hbase_eq : ({cycV (m - 1) hi, cycV ((m - 1 + 1) % m) (Nat.mod_lt _ (by omega))} : Set (Fin (m + l))) =
          {v : Fin (m + l) | v.val = 0 ∨ (m - 1 ≤ v.val ∧ v.val < m)} := by
        ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, Fin.ext_iff, cycV, hmod]
        omega
      rw [hbase_eq]
      have hgrow : ∀ d : ℕ, d ≤ m - 2 →
          ZFRound (tadpoleGraph m l hm)
            {v : Fin (m + l) | v.val = 0 ∨ (m - 1 ≤ v.val ∧ v.val < m)}
            {v : Fin (m + l) | v.val = 0 ∨ (m - 1 - d ≤ v.val ∧ v.val < m)} := by
        intro d
        induction d with
        | zero => intro _; simpa using ZFRound.base
        | succ t ih =>
          intro ht
          have h1 := ih (by omega)
          have hk1 : 1 ≤ m - 1 - t := by omega
          have hkm : m - 1 - t < m := by omega
          have hstep := hbwd {v : Fin (m + l) | v.val = 0 ∨ (m - 1 - t ≤ v.val ∧ v.val < m)}
            (m - 1 - t) hk1 hkm
            (Or.inr ⟨by dsimp [cycV]; omega, by dsimp [cycV]; omega⟩)
            (by
              by_cases ht0 : t = 0
              · subst ht0; left; dsimp [cycV]; rw [Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.mod_self]
              · right; dsimp [cycV]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
          have heq : insert (cycV (m - 1 - t - 1) (by omega))
              {v : Fin (m + l) | v.val = 0 ∨ (m - 1 - t ≤ v.val ∧ v.val < m)} =
              {v : Fin (m + l) | v.val = 0 ∨ (m - 1 - (t + 1) ≤ v.val ∧ v.val < m)} := by
            ext v; simp only [Set.mem_insert_iff, Set.mem_ofPred_eq, Fin.ext_iff, cycV]; omega
          rw [← heq]
          exact zf_round_trans h1 hstep
      have hend := hgrow (m - 2) le_rfl
      have hcyc_eq : {v : Fin (m + l) | v.val = 0 ∨ (m - 1 - (m - 2) ≤ v.val ∧ v.val < m)} = Cyc := by
        ext v; simp only [Set.mem_ofPred_eq, Cyc]; omega
      rwa [hcyc_eq] at hend
    · -- General interior pair `1 ≤ i ≤ m - 2`: expand right to `m - 1` (and `0`), then left to `1`.
      have hi_ge : 1 ≤ i := by omega
      have hi_le : i + 1 ≤ m - 1 := by omega
      have hmod : (i + 1) % m = i + 1 := Nat.mod_eq_of_lt (by omega)
      have hbase_eq : ({cycV i hi, cycV ((i + 1) % m) (Nat.mod_lt _ (by omega))} : Set (Fin (m + l))) =
          {v : Fin (m + l) | i ≤ v.val ∧ v.val ≤ i + 1} := by
        ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, Fin.ext_iff, cycV, hmod]
        omega
      rw [hbase_eq]
      -- Step A: grow right from `i + 1` to `m - 1`
      have hright : ∀ t : ℕ, i + 1 ≤ t → t ≤ m - 1 →
          ZFRound (tadpoleGraph m l hm)
            {v : Fin (m + l) | i ≤ v.val ∧ v.val ≤ i + 1}
            {v : Fin (m + l) | i ≤ v.val ∧ v.val ≤ t} := by
        intro t ht1
        induction t, ht1 using Nat.le_induction with
        | base => intro _; exact ZFRound.base
        | succ k hk ih =>
          intro hkm
          have h1 := ih (by omega)
          have hstep := hfwd {v : Fin (m + l) | i ≤ v.val ∧ v.val ≤ k} k (by omega) (by omega)
            ⟨by dsimp [cycV]; omega, by dsimp [cycV]; omega⟩
            ⟨by dsimp [cycV]; omega, by dsimp [cycV]; omega⟩
          have hmodk : (k + 1) % m = k + 1 := Nat.mod_eq_of_lt (by omega)
          have heq : insert (cycV ((k + 1) % m) (Nat.mod_lt _ (by omega)))
              {v : Fin (m + l) | i ≤ v.val ∧ v.val ≤ k} =
              {v : Fin (m + l) | i ≤ v.val ∧ v.val ≤ k + 1} := by
            ext v; simp only [Set.mem_insert_iff, Set.mem_ofPred_eq, Fin.ext_iff, cycV, hmodk]; omega
          rw [← heq]
          exact zf_round_trans h1 hstep
      -- Step B: from `[i, m - 1]`, grow left down to `0`
      have hleft : ∀ d : ℕ, d ≤ i →
          ZFRound (tadpoleGraph m l hm)
            {v : Fin (m + l) | i ≤ v.val ∧ v.val ≤ m - 1}
            {v : Fin (m + l) | i - d ≤ v.val ∧ v.val ≤ m - 1} := by
        intro d
        induction d with
        | zero => intro _; simpa using ZFRound.base
        | succ t ih =>
          intro ht
          have h1 := ih (by omega)
          have hstep := hbwd {v : Fin (m + l) | i - t ≤ v.val ∧ v.val ≤ m - 1}
            (i - t) (by omega) (by omega)
            ⟨by dsimp [cycV]; omega, by dsimp [cycV]; omega⟩
            (by
              have hmod' : (i - t + 1) % m = i - t + 1 := Nat.mod_eq_of_lt (by omega)
              exact ⟨by dsimp [cycV]; omega, by dsimp [cycV]; omega⟩)
          have heq : insert (cycV (i - t - 1) (by omega))
              {v : Fin (m + l) | i - t ≤ v.val ∧ v.val ≤ m - 1} =
              {v : Fin (m + l) | i - (t + 1) ≤ v.val ∧ v.val ≤ m - 1} := by
            ext v; simp only [Set.mem_insert_iff, Set.mem_ofPred_eq, Fin.ext_iff, cycV]; omega
          rw [← heq]
          exact zf_round_trans h1 hstep
      have htot := zf_round_trans (hright (m - 1) hi_le le_rfl) (hleft i le_rfl)
      have hcyc_eq : {v : Fin (m + l) | i - i ≤ v.val ∧ v.val ≤ m - 1} = Cyc := by
        ext v; simp only [Set.mem_ofPred_eq, Cyc]; omega
      rwa [hcyc_eq] at htot

/-- **Theorem 1 (Characterization):** `S` is a connected zero forcing set of `T_{m, l}`
if and only if `T_{m, l}[S]` is connected and `S` contains two adjacent cycle vertices. -/
theorem tadpole_czf_iff {m l : ℕ} (hm : 3 ≤ m) (S : Finset (Fin (m + l))) :
    IsConnectedZFSet (tadpoleGraph m l hm) S ↔
      (tadpoleGraph m l hm |>.induce (S : Set (Fin (m + l)))).Connected ∧
        HasAdjCyclePair m l S :=
  ⟨fun h => ⟨h.2, czf_implies_adj_cycle_pair hm h⟩,
   fun ⟨hconn, hpair⟩ => ⟨adj_cycle_pair_implies_zf hm hpair, hconn⟩⟩

/-! ### 4. Exact Enumeration of Connected Zero Forcing Sets of `T_{m, l}` -/

/-- `A_m(b)`: number of connected cycle subsets of size `b` containing `c_0` (`b ≥ 2`). -/
def A_coeff (m b : ℕ) : ℕ :=
  if 2 ≤ b ∧ b ≤ m - 1 then b else if b = m then 1 else 0

/-- `N_m(b)`: number of connected cycle subsets of size `b` avoiding `c_0` (`b ≥ 2`). -/
def N_coeff (m b : ℕ) : ℕ :=
  if 2 ≤ b ∧ b ≤ m - 1 then m - b else 0

/-- Closed-form connected zero forcing coefficient `Z_C(T_{m, l}, k)`. -/
def tadpoleFormula (m l k : ℕ) : ℕ :=
  N_coeff m k + ∑ a ∈ Finset.range (l + 1), A_coeff m (k - a)

/-- Helper: Type N set (cycle arc `[p, p + b - 1]` inside `{1, ..., m - 1}`, no tail). -/
def mkTypeN (m l p b : ℕ) : Finset (Fin (m + l)) :=
  Finset.univ.filter (fun v => p ≤ v.val ∧ v.val < p + b)

/-- Helper: Type A proper set (cycle arc containing `0` of length `b` with `r` vertices
before `0`, plus tail prefix of length `a`). -/
def mkTypeAProp (m l a b r : ℕ) : Finset (Fin (m + l)) :=
  Finset.univ.filter (fun v =>
    v.val < b - r ∨ (m - r ≤ v.val ∧ v.val < m) ∨ (m ≤ v.val ∧ v.val < m + a))

/-- Helper: Type A full-cycle set (all `m` cycle vertices plus tail prefix of length `a`). -/
def mkTypeAFull (m l a : ℕ) : Finset (Fin (m + l)) :=
  Finset.univ.filter (fun v => v.val < m + a)

private lemma mkTypeN_spec {m l p b : ℕ} (hm : 3 ≤ m) (hp : 1 ≤ p) (hb2 : 2 ≤ b)
    (hpb : p + b ≤ m) :
    (mkTypeN m l p b).card = b ∧
    cycV 0 (by omega) ∉ mkTypeN m l p b ∧
    IsConnectedZFSet (tadpoleGraph m l hm) (mkTypeN m l p b) := by
  have hcard : (mkTypeN m l p b).card = b := by
    let f : Fin b → Fin (m + l) := fun t => ⟨p + t.val, by omega⟩
    have himg : Finset.univ.image f = mkTypeN m l p b := by
      ext v
      simp only [Finset.mem_image, Finset.mem_univ, true_and, mkTypeN, Finset.mem_filter]
      constructor
      · rintro ⟨t, rfl⟩; dsimp [f]; omega
      · intro ⟨h1, h2⟩; exact ⟨⟨v.val - p, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩
    rw [← himg, Finset.card_image_of_injective _ (fun x y h => Fin.ext (by
      have := congr_arg Fin.val h; dsimp [f] at this; omega)), Finset.card_univ, Fintype.card_fin]
  have h0 : cycV 0 (by omega) ∉ mkTypeN m l p b := by
    simp only [mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and, cycV]; omega
  refine ⟨hcard, h0, (tadpole_czf_iff hm _).mpr ⟨?_, ?_⟩⟩
  · -- Connectedness of `mkTypeN`: every `v` in `[p, p + b - 1]` is reachable from `p`.
    have hp_mem : (⟨p, by omega⟩ : Fin (m + l)) ∈ mkTypeN m l p b := by
      simp only [mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hreach_d : ∀ (d : ℕ) (hd : d < b),
        ((tadpoleGraph m l hm).induce (mkTypeN m l p b : Set (Fin (m + l)))).Reachable
          ⟨⟨p, by omega⟩, hp_mem⟩
          ⟨⟨p + d, by omega⟩, by
            simp only [Finset.mem_coe, mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ := by
      intro d
      induction d with
      | zero => intro _; exact SimpleGraph.Reachable.refl _
      | succ t ih =>
        intro ht
        have hprev_mem : (⟨p + t, by omega⟩ : Fin (m + l)) ∈ mkTypeN m l p b := by
          simp only [mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and]; omega
        have hadj : ((tadpoleGraph m l hm).induce (mkTypeN m l p b : Set (Fin (m + l)))).Adj
            ⟨⟨p + t, by omega⟩, hprev_mem⟩ ⟨⟨p + (t + 1), by omega⟩, by
              simp only [Finset.mem_coe, mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ := by
          refine Or.inl ⟨by dsimp; omega, by dsimp; omega, Or.inl ?_⟩
          dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega
        exact (ih (by omega)).trans hadj.reachable
    have hreach : ∀ v : (mkTypeN m l p b : Set (Fin (m + l))),
        ((tadpoleGraph m l hm).induce (mkTypeN m l p b : Set (Fin (m + l)))).Reachable
          ⟨⟨p, by omega⟩, hp_mem⟩ v := by
      rintro ⟨⟨k, hk⟩, hmem⟩
      simp only [Finset.mem_coe, mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have h := hreach_d (k - p) (by omega)
      have heq : (⟨⟨p + (k - p), by omega⟩, by
          simp only [Finset.mem_coe, mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ :
          (mkTypeN m l p b : Set (Fin (m + l)))) = ⟨⟨k, hk⟩, by
            simp only [Finset.mem_coe, mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and]; exact hmem⟩ :=
        Subtype.ext (Fin.ext (by dsimp; omega))
      rwa [heq] at h
    let : Nonempty (mkTypeN m l p b : Set (Fin (m + l))) := ⟨⟨⟨p, by omega⟩, hp_mem⟩⟩
    exact ⟨fun u v => (hreach u).symm.trans (hreach v)⟩
  · -- Adjacent cycle pair `{c_p, c_{p+1}}`
    refine ⟨p, by omega, ?_, ?_⟩
    · simp only [mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and, cycV]; omega
    · simp only [mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and, cycV]
      rw [Nat.mod_eq_of_lt (by omega)]; omega

private lemma mkTypeAProp_spec {m l a b r : ℕ} (hm : 3 ≤ m) (ha : a ≤ l)
    (hb2 : 2 ≤ b) (hbm : b ≤ m - 1) (hr : r < b) :
    (mkTypeAProp m l a b r).card = b + a ∧
    cycV 0 (by omega) ∈ mkTypeAProp m l a b r ∧
    IsConnectedZFSet (tadpoleGraph m l hm) (mkTypeAProp m l a b r) := by
  have hcard : (mkTypeAProp m l a b r).card = b + a := by
    let f : Fin (b + a) → Fin (m + l) := fun t =>
      if h1 : t.val < b - r then ⟨t.val, by omega⟩
      else if h2 : t.val < b then ⟨m - b + t.val, by omega⟩
      else ⟨m + (t.val - b), by omega⟩
    have hf_inj : Function.Injective f := by
      intro x y hxy
      have hv := congr_arg Fin.val hxy
      dsimp only [f] at hv
      split_ifs at hv <;> simp only at hv <;> exact Fin.ext (by omega)
    have himg : Finset.univ.image f = mkTypeAProp m l a b r := by
      ext v
      simp only [Finset.mem_image, Finset.mem_univ, true_and, mkTypeAProp, Finset.mem_filter]
      constructor
      · rintro ⟨t, rfl⟩
        dsimp only [f]
        split_ifs <;> simp only <;> omega
      · rintro (h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩)
        · refine ⟨⟨v.val, by omega⟩, Fin.ext ?_⟩
          dsimp only [f]; rw [dif_pos h1]
        · refine ⟨⟨v.val - (m - b), by omega⟩, Fin.ext ?_⟩
          dsimp only [f]; rw [dif_neg (by omega), dif_pos (by omega)]; dsimp; omega
        · refine ⟨⟨b + (v.val - m), by omega⟩, Fin.ext ?_⟩
          dsimp only [f]; rw [dif_neg (by omega), dif_neg (by omega)]; dsimp; omega
    rw [← himg, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  have h0_mem : cycV 0 (by omega) ∈ mkTypeAProp m l a b r := by
    simp only [mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and, cycV]; omega
  refine ⟨hcard, h0_mem, (tadpole_czf_iff hm _).mpr ⟨?_, ?_⟩⟩
  · -- Connectedness: every vertex reaches `c_0`.
    have hreach_L : ∀ (k : ℕ) (hk : k < b - r),
        ((tadpoleGraph m l hm).induce (mkTypeAProp m l a b r : Set (Fin (m + l)))).Reachable
          ⟨cycV 0 (by omega), h0_mem⟩
          ⟨⟨k, by omega⟩, by
            simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ := by
      intro k
      induction k with
      | zero => intro _; exact SimpleGraph.Reachable.refl _
      | succ t ih =>
        intro ht
        have hadj : ((tadpoleGraph m l hm).induce (mkTypeAProp m l a b r : Set (Fin (m + l)))).Adj
            ⟨⟨t, by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
            ⟨⟨t + 1, by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ := by
          refine Or.inl ⟨by dsimp; omega, by dsimp; omega, Or.inl ?_⟩
          dsimp; rw [Nat.mod_eq_of_lt (by omega)]
        exact (ih (by omega)).trans hadj.reachable
    have hreach_R : ∀ (d : ℕ) (hd : d < r),
        ((tadpoleGraph m l hm).induce (mkTypeAProp m l a b r : Set (Fin (m + l)))).Reachable
          ⟨cycV 0 (by omega), h0_mem⟩
          ⟨⟨m - 1 - d, by omega⟩, by
            simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ := by
      intro d
      induction d with
      | zero =>
        intro _
        have hadj : ((tadpoleGraph m l hm).induce (mkTypeAProp m l a b r : Set (Fin (m + l)))).Adj
            ⟨cycV 0 (by omega), h0_mem⟩
            ⟨⟨m - 1 - 0, by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ :=
          (tadpole_adj_zero_iff hm _).mpr (Or.inr (Or.inl (by dsimp)))
        exact hadj.reachable
      | succ t ih =>
        intro ht
        have hadj : ((tadpoleGraph m l hm).induce (mkTypeAProp m l a b r : Set (Fin (m + l)))).Adj
            ⟨⟨m - 1 - t, by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
            ⟨⟨m - 1 - (t + 1), by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ := by
          refine Or.inl ⟨by dsimp; omega, by dsimp; omega, Or.inr ?_⟩
          dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega
        exact (ih (by omega)).trans hadj.reachable
    have hreach_T : ∀ (j : ℕ) (hj : j < a),
        ((tadpoleGraph m l hm).induce (mkTypeAProp m l a b r : Set (Fin (m + l)))).Reachable
          ⟨cycV 0 (by omega), h0_mem⟩
          ⟨⟨m + j, by omega⟩, by
            simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ := by
      intro j
      induction j with
      | zero =>
        intro _
        have hadj : ((tadpoleGraph m l hm).induce (mkTypeAProp m l a b r : Set (Fin (m + l)))).Adj
            ⟨cycV 0 (by omega), h0_mem⟩
            ⟨⟨m + 0, by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ :=
          Or.inr (Or.inl ⟨rfl, rfl⟩)
        exact hadj.reachable
      | succ t ih =>
        intro ht
        have hadj : ((tadpoleGraph m l hm).induce (mkTypeAProp m l a b r : Set (Fin (m + l)))).Adj
            ⟨⟨m + t, by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
            ⟨⟨m + (t + 1), by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ :=
          Or.inr (Or.inr (Or.inr ⟨by dsimp; omega, by dsimp; omega, Or.inl (by dsimp; omega)⟩))
        exact (ih (by omega)).trans hadj.reachable
    have hreach : ∀ v : (mkTypeAProp m l a b r : Set (Fin (m + l))),
        ((tadpoleGraph m l hm).induce (mkTypeAProp m l a b r : Set (Fin (m + l)))).Reachable
          ⟨cycV 0 (by omega), h0_mem⟩ v := by
      rintro ⟨⟨k, hk⟩, hmem⟩
      simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rcases hmem with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
      · exact hreach_L k h1
      · have h := hreach_R (m - 1 - k) (by omega)
        have heq : (⟨⟨m - 1 - (m - 1 - k), by omega⟩, by
            simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ :
            (mkTypeAProp m l a b r : Set (Fin (m + l)))) = ⟨⟨k, hk⟩, by
              simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]
              exact Or.inr (Or.inl ⟨h2a, h2b⟩)⟩ :=
          Subtype.ext (Fin.ext (by dsimp; omega))
        rwa [heq] at h
      · have h := hreach_T (k - m) (by omega)
        have heq : (⟨⟨m + (k - m), by omega⟩, by
            simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ :
            (mkTypeAProp m l a b r : Set (Fin (m + l)))) = ⟨⟨k, hk⟩, by
              simp only [Finset.mem_coe, mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]
              exact Or.inr (Or.inr ⟨h3a, h3b⟩)⟩ :=
          Subtype.ext (Fin.ext (by dsimp; omega))
        rwa [heq] at h
    let : Nonempty (mkTypeAProp m l a b r : Set (Fin (m + l))) := ⟨⟨cycV 0 (by omega), h0_mem⟩⟩
    exact ⟨fun u v => (hreach u).symm.trans (hreach v)⟩
  · -- Adjacent cycle pair: `{0, 1}` if `r + 1 < b`, else `{m - 1, 0}`
    by_cases hr1 : r + 1 < b
    · refine ⟨0, by omega, h0_mem, ?_⟩
      simp only [mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and, cycV]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · refine ⟨m - 1, by omega, ?_, ?_⟩
      · simp only [mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and, cycV]; omega
      · have hmod : (m - 1 + 1) % m = 0 := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.mod_self]
        have : cycV (l := l) ((m - 1 + 1) % m) (Nat.mod_lt _ (by omega)) = cycV (l := l) 0 (by omega) := Fin.ext hmod
        rwa [this]

private lemma mkTypeAFull_spec {m l a : ℕ} (hm : 3 ≤ m) (ha : a ≤ l) :
    (mkTypeAFull m l a).card = m + a ∧
    cycV 0 (by omega) ∈ mkTypeAFull m l a ∧
    IsConnectedZFSet (tadpoleGraph m l hm) (mkTypeAFull m l a) := by
  have hcard : (mkTypeAFull m l a).card = m + a := by
    let f : Fin (m + a) → Fin (m + l) := fun t => ⟨t.val, by omega⟩
    have hf_inj : Function.Injective f := fun x y h => Fin.ext (by have := congr_arg Fin.val h; dsimp [f] at this; exact this)
    have himg : Finset.univ.image f = mkTypeAFull m l a := by
      ext v
      simp only [Finset.mem_image, Finset.mem_univ, true_and, mkTypeAFull, Finset.mem_filter]
      exact ⟨fun ⟨t, ht⟩ => ht ▸ t.isLt, fun hv => ⟨⟨v.val, hv⟩, Fin.ext rfl⟩⟩
    rw [← himg, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  have h0_mem : cycV 0 (by omega) ∈ mkTypeAFull m l a := by
    simp only [mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and, cycV]; omega
  refine ⟨hcard, h0_mem, (tadpole_czf_iff hm _).mpr ⟨?_, ?_⟩⟩
  · have hreach_C : ∀ (k : ℕ) (hk : k < m),
        ((tadpoleGraph m l hm).induce (mkTypeAFull m l a : Set (Fin (m + l)))).Reachable
          ⟨cycV 0 (by omega), h0_mem⟩
          ⟨⟨k, by omega⟩, by
            simp only [Finset.mem_coe, mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ := by
      intro k
      induction k with
      | zero => intro _; exact SimpleGraph.Reachable.refl _
      | succ t ih =>
        intro ht
        have hadj : ((tadpoleGraph m l hm).induce (mkTypeAFull m l a : Set (Fin (m + l)))).Adj
            ⟨⟨t, by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
            ⟨⟨t + 1, by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ := by
          refine Or.inl ⟨by dsimp; omega, by dsimp; omega, Or.inl ?_⟩
          dsimp; rw [Nat.mod_eq_of_lt (by omega)]
        exact (ih (by omega)).trans hadj.reachable
    have hreach_T : ∀ (j : ℕ) (hj : j < a),
        ((tadpoleGraph m l hm).induce (mkTypeAFull m l a : Set (Fin (m + l)))).Reachable
          ⟨cycV 0 (by omega), h0_mem⟩
          ⟨⟨m + j, by omega⟩, by
            simp only [Finset.mem_coe, mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ := by
      intro j
      induction j with
      | zero =>
        intro _
        have hadj : ((tadpoleGraph m l hm).induce (mkTypeAFull m l a : Set (Fin (m + l)))).Adj
            ⟨cycV 0 (by omega), h0_mem⟩
            ⟨⟨m + 0, by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ :=
          Or.inr (Or.inl ⟨rfl, rfl⟩)
        exact hadj.reachable
      | succ t ih =>
        intro ht
        have hadj : ((tadpoleGraph m l hm).induce (mkTypeAFull m l a : Set (Fin (m + l)))).Adj
            ⟨⟨m + t, by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
            ⟨⟨m + (t + 1), by omega⟩, by
              simp only [Finset.mem_coe, mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ :=
          Or.inr (Or.inr (Or.inr ⟨by dsimp; omega, by dsimp; omega, Or.inl (by dsimp; omega)⟩))
        exact (ih (by omega)).trans hadj.reachable
    have hreach : ∀ v : (mkTypeAFull m l a : Set (Fin (m + l))),
        ((tadpoleGraph m l hm).induce (mkTypeAFull m l a : Set (Fin (m + l)))).Reachable
          ⟨cycV 0 (by omega), h0_mem⟩ v := by
      rintro ⟨⟨k, hk⟩, hmem⟩
      simp only [Finset.mem_coe, mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      by_cases hkm : k < m
      · exact hreach_C k hkm
      · have h := hreach_T (k - m) (by omega)
        have heq : (⟨⟨m + (k - m), by omega⟩, by
            simp only [Finset.mem_coe, mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩ :
            (mkTypeAFull m l a : Set (Fin (m + l)))) = ⟨⟨k, hk⟩, by
              simp only [Finset.mem_coe, mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and]; exact hmem⟩ :=
          Subtype.ext (Fin.ext (by dsimp; omega))
        rwa [heq] at h
    let : Nonempty (mkTypeAFull m l a : Set (Fin (m + l))) := ⟨⟨cycV 0 (by omega), h0_mem⟩⟩
    exact ⟨fun u v => (hreach u).symm.trans (hreach v)⟩
  · refine ⟨0, by omega, h0_mem, ?_⟩
    simp only [mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and, cycV]
    rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- Helper: every connected subset `S` of `T_{m, l}` avoiding `c_0` and containing an
adjacent cycle pair is of the form `mkTypeN m l p b` with `1 ≤ p`, `2 ≤ b`, `p + b ≤ m`. -/
private lemma classify_typeN {m l : ℕ} (hm : 3 ≤ m) {S : Finset (Fin (m + l))}
    (hS : IsConnectedZFSet (tadpoleGraph m l hm) S) (h0 : cycV 0 (by omega) ∉ S) :
    ∃ p b : ℕ, 1 ≤ p ∧ 2 ≤ b ∧ p + b ≤ m ∧ S = mkTypeN m l p b := by
  have hchar := (tadpole_czf_iff hm S).mp hS
  rcases hchar.2 with ⟨i0, hi0, hi0S, hi1S⟩
  -- Every walk in `S` from `c_{i0}` stays in `{1, ..., m - 1}` because `c_0 ∉ S`.
  have hsub_cyc : ∀ v ∈ S, 1 ≤ v.val ∧ v.val < m := by
    intro v hvS
    have hne0 : v.val ≠ 0 := fun h => h0 (by convert hvS; exact Fin.ext h.symm)
    have hlt_m : v.val < m := by
      -- Walk in `S` from `v` to `c_{i0}` cannot leave `{v | v.val < m}` without passing `0`.
      have hreach := hchar.1 ⟨cycV i0 hi0, hi0S⟩ ⟨v, hvS⟩
      rcases hreach with ⟨w⟩
      have hstay : ∀ {x y : (S : Set (Fin (m + l)))},
          ((tadpoleGraph m l hm).induce (S : Set (Fin (m + l)))).Walk x y →
          x.val.val < m → y.val.val < m := by
        intro x y walk hx
        induction walk with
        | nil => exact hx
        | @cons a b c hadj _ ih =>
          apply ih
          have ha0 : a.val.val ≠ 0 := fun h => h0 (by convert Finset.mem_coe.mp a.prop; exact Fin.ext h.symm)
          have hba : (tadpoleGraph m l hm).Adj (cycV a.val.val hx) b.val := hadj
          rw [tadpole_adj_cyc_pos_iff hm (by omega) hx] at hba
          rcases hba with h1 | h2
          · omega
          · rw [h2]; exact Nat.mod_lt _ (by omega)
      exact hstay w (by dsimp [cycV]; exact hi0)
    exact ⟨by omega, hlt_m⟩
  have hS_ne : S.Nonempty := ⟨cycV i0 hi0, hi0S⟩
  let vals := S.image Fin.val
  have hvals_ne : vals.Nonempty := hS_ne.image _
  set p := vals.min' hvals_ne
  set q := vals.max' hvals_ne
  have hp_mem : p ∈ vals := Finset.min'_mem vals hvals_ne
  have hq_mem : q ∈ vals := Finset.max'_mem vals hvals_ne
  rcases Finset.mem_image.mp hp_mem with ⟨vp, hvpS, hvpeq⟩
  rcases Finset.mem_image.mp hq_mem with ⟨vq, hvqS, hvqeq⟩
  have hp1 : 1 ≤ p := by rw [← hvpeq]; exact (hsub_cyc vp hvpS).1
  have hqm : q < m := by rw [← hvqeq]; exact (hsub_cyc vq hvqS).2
  have hp_le_q : p ≤ q := Finset.min'_le vals q hq_mem
  have h2 : 2 ≤ q - p + 1 := by
    have hne : cycV i0 hi0 ≠ cycV ((i0 + 1) % m) (Nat.mod_lt _ (by omega)) :=
      (tadpoleGraph m l hm).ne_of_adj (tadpole_adj_cyc_succ hm hi0)
    have hcard2 : 2 ≤ S.card := by
      have : ({cycV i0 hi0, cycV ((i0 + 1) % m) (Nat.mod_lt _ (by omega))} : Finset _).card ≤ S.card :=
        Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
      rw [Finset.card_pair hne] at this; exact this
    have hval_le : S.card ≤ q - p + 1 := by
      have hsub : vals ⊆ Finset.Icc p q := by
        intro x hx
        exact Finset.mem_Icc.mpr ⟨Finset.min'_le vals x hx, Finset.le_max' vals x hx⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] at hc
      omega
    omega
  -- Intermediate value lemma along the walk in `S` from `vp` to `vq`: every `t ∈ [p, q]` lies in `S`.
  have hinter : ∀ t : ℕ, p ≤ t → t ≤ q → ∃ u ∈ S, u.val = t := by
    intro t hpt htq
    rcases hchar.1 ⟨vp, hvpS⟩ ⟨vq, hvqS⟩ with ⟨walk⟩
    have hwalk_iv : ∀ {x y : (S : Set (Fin (m + l)))},
        ((tadpoleGraph m l hm).induce (S : Set (Fin (m + l)))).Walk x y →
        x.val.val ≤ t → t ≤ y.val.val → ∃ u ∈ S, u.val = t := by
      intro x y w
      induction w with
      | @nil u => intro hxt hty; exact ⟨u.val, Finset.mem_coe.mp u.prop, by omega⟩
      | @cons a b c hadj _ ih =>
        intro hxt hty
        by_cases hbt : b.val.val ≤ t
        · exact ih hbt hty
        · have ha_bd := hsub_cyc a.val (Finset.mem_coe.mp a.prop)
          have hb_bd := hsub_cyc b.val (Finset.mem_coe.mp b.prop)
          have hadj' : (tadpoleGraph m l hm).Adj (cycV a.val.val ha_bd.2) b.val := hadj
          rw [tadpole_adj_cyc_pos_iff hm ha_bd.1 ha_bd.2] at hadj'
          rcases hadj' with h1 | h2
          · omega
          · have hlt : a.val.val + 1 < m := by
              by_contra hge
              have heqm : a.val.val + 1 = m := by omega
              rw [heqm, Nat.mod_self] at h2; omega
            rw [Nat.mod_eq_of_lt hlt] at h2
            exact ⟨a.val, Finset.mem_coe.mp a.prop, by omega⟩
    exact hwalk_iv walk (by rw [hvpeq]; omega) (by rw [hvqeq]; omega)
  refine ⟨p, q - p + 1, hp1, h2, by omega, ?_⟩
  ext v
  simp only [mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hvS
    have hvmem : v.val ∈ vals := Finset.mem_image.mpr ⟨v, hvS, rfl⟩
    have h1 := Finset.min'_le vals v.val hvmem
    have h2 := Finset.le_max' vals v.val hvmem
    omega
  · intro ⟨h1, h2⟩
    rcases hinter v.val h1 (by omega) with ⟨u, huS, huval⟩
    have : u = v := Fin.ext huval
    rwa [← this]

/-- Helper: every connected subset `S` of `T_{m, l}` containing `c_0` and an adjacent
cycle pair is either `mkTypeAFull m l a` or `mkTypeAProp m l a b r`. -/
private lemma classify_typeA {m l : ℕ} (hm : 3 ≤ m) {S : Finset (Fin (m + l))}
    (hS : IsConnectedZFSet (tadpoleGraph m l hm) S) (h0 : cycV 0 (by omega) ∈ S) :
    (∃ a : ℕ, a ≤ l ∧ S = mkTypeAFull m l a) ∨
    (∃ a b r : ℕ, a ≤ l ∧ 2 ≤ b ∧ b ≤ m - 1 ∧ r < b ∧ S = mkTypeAProp m l a b r) := by
  have hchar := (tadpole_czf_iff hm S).mp hS
  -- Part 1: Tail vertices in `S` form a prefix `{m, ..., m + a - 1}` for some `a ≤ l`.
  have htail_down : ∀ j : ℕ, (hj : j < l) → tailV j hj ∈ S →
      ∀ j' : ℕ, (hj' : j' ≤ j) → tailV j' (by omega) ∈ S := by
    intro j hj hjS j' hj'
    rcases hchar.1 ⟨cycV 0 (by omega), h0⟩ ⟨tailV j hj, hjS⟩ with ⟨walk⟩
    have hwalk_tail : ∀ {x y : (S : Set (Fin (m + l)))},
        ((tadpoleGraph m l hm).induce (S : Set (Fin (m + l)))).Walk x y →
        x.val.val < m + j' → m + j' ≤ y.val.val → tailV j' (by omega) ∈ S := by
      intro x y w hx hy
      induction w with
      | nil => omega
      | @cons u v z hadj _ ih =>
        by_cases hv : v.val.val < m + j'
        · exact ih hv hy
        · -- `u.val < m + j' ≤ v.val` and `u ~ v`, so `v.val = m + j'`!
          have hv_eq : v.val.val = m + j' := by
            have hadj' : tadpoleAdj m l u.val v.val := hadj
            rcases hadj' with ⟨_, hvm, _⟩ | ⟨_, hvm⟩ | ⟨_, hv0⟩ | ⟨_, _, h1 | h2⟩ <;> omega
          have : v.val = tailV j' (by omega) := Fin.ext hv_eq
          rw [← this]; exact Finset.mem_coe.mp v.prop
    by_cases hj'0 : j' = 0
    · subst hj'0
      exact hwalk_tail walk (by dsimp [cycV]; omega) (by dsimp [tailV]; omega)
    · exact hwalk_tail walk (by dsimp [cycV]; omega) (by dsimp [tailV]; omega)
  let tailSet := S.filter (fun v => m ≤ v.val)
  set a := tailSet.card
  have ha_le : a ≤ l := by
    have hsub : tailSet ⊆ Finset.univ.filter (fun v : Fin (m + l) => m ≤ v.val) :=
      Finset.filter_subset_filter _ (Finset.subset_univ _)
    have hcard_all : (Finset.univ.filter (fun v : Fin (m + l) => m ≤ v.val)).card = l := by
      let f : Fin l → Fin (m + l) := fun t => ⟨m + t.val, by omega⟩
      have himg : Finset.univ.image f = Finset.univ.filter (fun v : Fin (m + l) => m ≤ v.val) := by
        ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
        exact ⟨fun ⟨t, ht⟩ => by rw [← ht]; dsimp [f]; omega,
          fun hv => ⟨⟨v.val - m, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩⟩
      rw [← himg, Finset.card_image_of_injective _ (fun x y h => Fin.ext (by
        have := congr_arg Fin.val h; dsimp [f] at this; omega)), Finset.card_univ, Fintype.card_fin]
    exact le_trans (Finset.card_le_card hsub) (le_of_eq hcard_all)
  have htail_iff : ∀ v : Fin (m + l), m ≤ v.val → (v ∈ S ↔ v.val < m + a) := by
    -- Every `v ∈ tailSet` satisfies `v.val < m + a` by downward closure!
    have hle_a : ∀ v ∈ tailSet, v.val < m + a := by
      intro v hv
      have hvm : m ≤ v.val := (Finset.mem_filter.mp hv).2
      have hvS : v ∈ S := (Finset.mem_filter.mp hv).1
      set j := v.val - m
      have hj : j < l := by omega
      have hjS : tailV j hj ∈ S := by convert hvS; exact Fin.ext (by dsimp [tailV]; omega)
      let g : Fin (j + 1) → Fin (m + l) := fun t => ⟨m + t.val, by omega⟩
      have hsub : Finset.univ.image g ⊆ tailSet := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨t, _, rfl⟩
        refine Finset.mem_filter.mpr ⟨?_, by dsimp [g]; omega⟩
        exact htail_down j hj hjS t.val (by omega)
      have hcard_le := Finset.card_le_card hsub
      have hg_inj : Function.Injective g := fun x y h => Fin.ext (by
        have := congr_arg Fin.val h; dsimp [g] at this; omega)
      rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ, Fintype.card_fin] at hcard_le
      omega
    have htail_eq : tailSet = Finset.univ.filter (fun v : Fin (m + l) => m ≤ v.val ∧ v.val < m + a) := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2, hle_a v hv⟩
      · have hcard_rhs : (Finset.univ.filter (fun v : Fin (m + l) => m ≤ v.val ∧ v.val < m + a)).card = a := by
          let f : Fin a → Fin (m + l) := fun t => ⟨m + t.val, by omega⟩
          have himg : Finset.univ.image f =
              Finset.univ.filter (fun v : Fin (m + l) => m ≤ v.val ∧ v.val < m + a) := by
            ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
            exact ⟨fun ⟨t, ht⟩ => by rw [← ht]; dsimp [f]; omega,
              fun ⟨h1, h2⟩ => ⟨⟨v.val - m, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩⟩
          rw [← himg, Finset.card_image_of_injective _ (fun x y h => Fin.ext (by
            have := congr_arg Fin.val h; dsimp [f] at this; omega)), Finset.card_univ, Fintype.card_fin]
        omega
    intro v hvm
    have : v ∈ tailSet ↔ v ∈ S := by simp [tailSet, hvm]
    rw [← this, htail_eq]
    simp [hvm]
  -- Part 2: Cycle vertices in `S`
  let cycSet := S.filter (fun v => v.val < m)
  set b := cycSet.card
  have hb_le : b ≤ m := by
    have hsub : cycSet ⊆ Finset.univ.filter (fun v : Fin (m + l) => v.val < m) :=
      Finset.filter_subset_filter _ (Finset.subset_univ _)
    have hcard_all : (Finset.univ.filter (fun v : Fin (m + l) => v.val < m)).card = m := by
      let f : Fin m → Fin (m + l) := fun t => ⟨t.val, by omega⟩
      have hf_inj : Function.Injective f := fun x y h => Fin.ext (by have := congr_arg Fin.val h; dsimp [f] at this; exact this)
      have himg : Finset.univ.image f = Finset.univ.filter (fun v : Fin (m + l) => v.val < m) := by
        ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
        exact ⟨fun ⟨t, ht⟩ => ht ▸ t.isLt, fun hv => ⟨⟨v.val, hv⟩, Fin.ext rfl⟩⟩
      rw [← himg, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
    exact le_trans (Finset.card_le_card hsub) (le_of_eq hcard_all)
  have hb_ge2 : 2 ≤ b := by
    rcases hchar.2 with ⟨i0, hi0, hi0S, hi1S⟩
    have hne : cycV i0 hi0 ≠ cycV ((i0 + 1) % m) (Nat.mod_lt _ (by omega)) :=
      (tadpoleGraph m l hm).ne_of_adj (tadpole_adj_cyc_succ hm hi0)
    have hsub : ({cycV i0 hi0, cycV ((i0 + 1) % m) (Nat.mod_lt _ (by omega))} : Finset _) ⊆ cycSet := by
      intro v hv; simp at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hi0S, hi0⟩
      · exact Finset.mem_filter.mpr ⟨hi1S, Nat.mod_lt _ (by omega)⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hne] at this
  by_cases hbm : b = m
  · -- Full cycle: every `v` with `v.val < m` is in `S`.
    left
    have hcyc_full : cycSet = Finset.univ.filter (fun v : Fin (m + l) => v.val < m) := by
      refine Finset.eq_of_subset_of_card_le (Finset.filter_subset_filter _ (Finset.subset_univ _)) ?_
      have hcard_all : (Finset.univ.filter (fun v : Fin (m + l) => v.val < m)).card = m := by
        let f : Fin m → Fin (m + l) := fun t => ⟨t.val, by omega⟩
        have hf_inj : Function.Injective f := fun x y h => Fin.ext (by have := congr_arg Fin.val h; dsimp [f] at this; exact this)
        have himg : Finset.univ.image f = Finset.univ.filter (fun v : Fin (m + l) => v.val < m) := by
          ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
          exact ⟨fun ⟨t, ht⟩ => ht ▸ t.isLt, fun hv => ⟨⟨v.val, hv⟩, Fin.ext rfl⟩⟩
        rw [← himg, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
      omega
    refine ⟨a, ha_le, ?_⟩
    ext v
    simp only [mkTypeAFull, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hvm : v.val < m
    · have hvcyc : v ∈ cycSet := by rw [hcyc_full]; simp [hvm]
      exact ⟨fun _ => by omega, fun _ => (Finset.mem_filter.mp hvcyc).1⟩
    · exact htail_iff v (by omega)
  · -- Proper cycle arc containing `0`: there is some missing cycle vertex `g ∈ {1, ..., m - 1}`.
    right
    have hmiss : ∃ g : ℕ, ∃ hg : g < m, 1 ≤ g ∧ cycV g hg ∉ S := by
      by_contra hall
      push Not at hall
      have hsub : Finset.univ.filter (fun v : Fin (m + l) => v.val < m) ⊆ cycSet := by
        intro v hv
        have hvm : v.val < m := (Finset.mem_filter.mp hv).2
        refine Finset.mem_filter.mpr ⟨?_, hvm⟩
        by_cases hv0 : v.val = 0
        · convert h0; exact Fin.ext hv0
        · exact hall v.val hvm (by omega)
      have hcard_all : (Finset.univ.filter (fun v : Fin (m + l) => v.val < m)).card = m := by
        let f : Fin m → Fin (m + l) := fun t => ⟨t.val, by omega⟩
        have hf_inj : Function.Injective f := fun x y h => Fin.ext (by have := congr_arg Fin.val h; dsimp [f] at this; exact this)
        have himg : Finset.univ.image f = Finset.univ.filter (fun v : Fin (m + l) => v.val < m) := by
          ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
          exact ⟨fun ⟨t, ht⟩ => ht ▸ t.isLt, fun hv => ⟨⟨v.val, hv⟩, Fin.ext rfl⟩⟩
        rw [← himg, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
      have := Finset.card_le_card hsub
      omega
    rcases hmiss with ⟨g, hgm, hg1, hgnotS⟩
    have hleft_down : ∀ k : ℕ, (hk : k < g) → cycV k (by omega) ∈ S →
        ∀ t : ℕ, (ht : t ≤ k) → cycV t (by omega) ∈ S := by
      intro k hk hkS t ht
      have htm : t < m := by omega
      rcases hchar.1 ⟨cycV 0 (by omega), h0⟩ ⟨cycV k (by omega), hkS⟩ with ⟨walk⟩
      have hwalk : ∀ {x y : (S : Set (Fin (m + l)))},
          ((tadpoleGraph m l hm).induce (S : Set (Fin (m + l)))).Walk x y →
          (x.val.val ≤ t ∨ g < x.val.val) → (t ≤ y.val.val ∧ y.val.val < g) →
          cycV t htm ∈ S := by
        intro x y w
        induction w with
        | @nil u =>
          intro hx hy
          rcases hx with h1 | h2
          · have : u.val = cycV t htm := Fin.ext (by dsimp [cycV]; omega)
            rw [← this]; exact Finset.mem_coe.mp u.prop
          · omega
        | @cons u v z hadj _ ih =>
          intro hx hy
          by_cases hv : v.val.val ≤ t ∨ g < v.val.val
          · exact ih hv hy
          · have hvg : v.val.val ≠ g := fun h => hgnotS (by convert Finset.mem_coe.mp v.prop; exact Fin.ext h.symm)
            have hv_bd : t < v.val.val ∧ v.val.val < g := by omega
            have hu_eq : u.val.val = t := by
              have hadj' : (tadpoleGraph m l hm).Adj (cycV v.val.val (by omega)) u.val := hadj.symm
              rw [tadpole_adj_cyc_pos_iff hm (by omega) (by omega)] at hadj'
              rcases hadj' with h1 | h2
              · rcases hx with hx1 | hx2 <;> omega
              · rw [Nat.mod_eq_of_lt (by omega)] at h2
                rcases hx with hx1 | hx2 <;> omega
            have : u.val = cycV t htm := Fin.ext hu_eq
            rw [← this]; exact Finset.mem_coe.mp u.prop
      exact hwalk walk (Or.inl (by dsimp [cycV]; omega)) ⟨by dsimp [cycV]; omega, by dsimp [cycV]; omega⟩
    have hright_up : ∀ k : ℕ, (hk : k < m) → g < k → cycV k hk ∈ S →
        ∀ t : ℕ, (ht : t < m) → k ≤ t → cycV t ht ∈ S := by
      intro k hk hgk hkS t ht hkt
      rcases hchar.1 ⟨cycV 0 (by omega), h0⟩ ⟨cycV k hk, hkS⟩ with ⟨walk⟩
      have hwalk : ∀ {x y : (S : Set (Fin (m + l)))},
          ((tadpoleGraph m l hm).induce (S : Set (Fin (m + l)))).Walk x y →
          (x.val.val < g ∨ t ≤ x.val.val) → (g < y.val.val ∧ y.val.val ≤ t) →
          cycV t ht ∈ S := by
        intro x y w
        induction w with
        | @nil u =>
          intro hx hy
          rcases hx with h1 | h2
          · omega
          · have : u.val = cycV t ht := Fin.ext (by dsimp [cycV]; omega)
            rw [← this]; exact Finset.mem_coe.mp u.prop
        | @cons u v z hadj _ ih =>
          intro hx hy
          by_cases hv : v.val.val < g ∨ t ≤ v.val.val
          · exact ih hv hy
          · have hvg : v.val.val ≠ g := fun h => hgnotS (by convert Finset.mem_coe.mp v.prop; exact Fin.ext h.symm)
            have hv_bd : g < v.val.val ∧ v.val.val < t := by omega
            have hu_eq : u.val.val = t := by
              have hadj' : (tadpoleGraph m l hm).Adj (cycV v.val.val (by omega)) u.val := hadj.symm
              rw [tadpole_adj_cyc_pos_iff hm (by omega) (by omega)] at hadj'
              rcases hadj' with h1 | h2
              · rcases hx with hx1 | hx2 <;> omega
              · rw [Nat.mod_eq_of_lt (by omega)] at h2
                rcases hx with hx1 | hx2 <;> omega
            have : u.val = cycV t ht := Fin.ext hu_eq
            rw [← this]; exact Finset.mem_coe.mp u.prop
      exact hwalk walk (Or.inl (by dsimp [cycV]; omega)) ⟨by dsimp [cycV]; omega, by dsimp [cycV]; omega⟩
    -- Count how many cycle vertices in `S` have `val > g` (`r`) and `val < g` (`p_len`).
    let cycR := cycSet.filter (fun v => g < v.val)
    let cycL := cycSet.filter (fun v => v.val < g)
    set r := cycR.card
    set p_len := cycL.card
    have hsplit_cyc : b = p_len + r := by
      have hunion : cycSet = cycL ∪ cycR := by
        ext v; simp only [Finset.mem_union, cycL, cycR, Finset.mem_filter]
        constructor
        · intro hv
          have hvne : v.val ≠ g := fun h => hgnotS (by convert (Finset.mem_filter.mp hv).1; exact Fin.ext h.symm)
          by_cases hlt : v.val < g
          · exact Or.inl ⟨hv, hlt⟩
          · exact Or.inr ⟨hv, by omega⟩
        · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
      have hdisj : Disjoint cycL cycR := by
        rw [Finset.disjoint_left]; intro v h1 h2
        simp only [cycL, cycR, Finset.mem_filter] at h1 h2; omega
      change cycSet.card = cycL.card + cycR.card
      rw [hunion, Finset.card_union_of_disjoint hdisj]
    have h0_in_L : cycV 0 (by omega) ∈ cycL := by
      simp only [cycL, cycSet, Finset.mem_filter, cycV]; exact ⟨⟨h0, by omega⟩, by omega⟩
    have hp_pos : 1 ≤ p_len := Finset.one_le_card.mpr ⟨_, h0_in_L⟩
    have hr_lt_b : r < b := by omega
    have hcycL_eq : cycL = Finset.univ.filter (fun v : Fin (m + l) => v.val < p_len) := by
      have hsub : cycL ⊆ Finset.univ.filter (fun v : Fin (m + l) => v.val < p_len) := by
        intro v hv
        simp only [cycL, cycSet, Finset.mem_filter] at hv
        let gL : Fin (v.val + 1) → Fin (m + l) := fun t => ⟨t.val, by omega⟩
        have hsub' : Finset.univ.image gL ⊆ cycL := by
          intro u hu
          rcases Finset.mem_image.mp hu with ⟨t, _, rfl⟩
          simp only [cycL, cycSet, Finset.mem_filter]
          exact ⟨⟨hleft_down v.val hv.2 hv.1.1 t.val (by omega), by dsimp [gL]; omega⟩, by dsimp [gL]; omega⟩
        have hc := Finset.card_le_card hsub'
        have hgL_inj : Function.Injective gL := fun x y h => Fin.ext (by have := congr_arg Fin.val h; dsimp [gL] at this; exact this)
        rw [Finset.card_image_of_injective _ hgL_inj, Finset.card_univ, Fintype.card_fin] at hc
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      refine Finset.eq_of_subset_of_card_le hsub ?_
      have hcard_rhs : (Finset.univ.filter (fun v : Fin (m + l) => v.val < p_len)).card = p_len := by
        let f : Fin p_len → Fin (m + l) := fun t => ⟨t.val, by omega⟩
        have hf_inj : Function.Injective f := fun x y h => Fin.ext (by have := congr_arg Fin.val h; dsimp [f] at this; exact this)
        have himg : Finset.univ.image f = Finset.univ.filter (fun v : Fin (m + l) => v.val < p_len) := by
          ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
          exact ⟨fun ⟨t, ht⟩ => ht ▸ t.isLt, fun hv => ⟨⟨v.val, hv⟩, Fin.ext rfl⟩⟩
        rw [← himg, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
      omega
    have hcycR_eq : cycR = Finset.univ.filter (fun v : Fin (m + l) => m - r ≤ v.val ∧ v.val < m) := by
      have hsub : cycR ⊆ Finset.univ.filter (fun v : Fin (m + l) => m - r ≤ v.val ∧ v.val < m) := by
        intro v hv
        simp only [cycR, cycSet, Finset.mem_filter] at hv
        let gR : Fin (m - v.val) → Fin (m + l) := fun t => ⟨v.val + t.val, by omega⟩
        have hsub' : Finset.univ.image gR ⊆ cycR := by
          intro u hu
          rcases Finset.mem_image.mp hu with ⟨t, _, rfl⟩
          simp only [cycR, cycSet, Finset.mem_filter]
          exact ⟨⟨hright_up v.val hv.1.2 hv.2 hv.1.1 (v.val + t.val) (by omega) (by omega), by dsimp [gR]; omega⟩, by dsimp [gR]; omega⟩
        have hc := Finset.card_le_card hsub'
        have hgR_inj : Function.Injective gR := fun x y h => Fin.ext (by
          have := congr_arg Fin.val h; dsimp [gR] at this; omega)
        rw [Finset.card_image_of_injective _ hgR_inj, Finset.card_univ, Fintype.card_fin] at hc
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, hv.1.2⟩
      refine Finset.eq_of_subset_of_card_le hsub ?_
      have hcard_rhs : (Finset.univ.filter (fun v : Fin (m + l) => m - r ≤ v.val ∧ v.val < m)).card = r := by
        let f : Fin r → Fin (m + l) := fun t => ⟨m - r + t.val, by omega⟩
        have himg : Finset.univ.image f =
            Finset.univ.filter (fun v : Fin (m + l) => m - r ≤ v.val ∧ v.val < m) := by
          ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
          exact ⟨fun ⟨t, ht⟩ => by rw [← ht]; dsimp [f]; omega,
            fun ⟨h1, h2⟩ => ⟨⟨v.val - (m - r), by omega⟩, Fin.ext (by dsimp [f]; omega)⟩⟩
        rw [← himg, Finset.card_image_of_injective _ (fun x y h => Fin.ext (by
          have := congr_arg Fin.val h; dsimp [f] at this; omega)), Finset.card_univ, Fintype.card_fin]
      omega
    refine ⟨a, b, r, ha_le, hb_ge2, by omega, hr_lt_b, ?_⟩
    ext v
    simp only [mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hvm : v.val < m
    · have hp_eq : b - r = p_len := by omega
      rw [hp_eq]
      constructor
      · intro hvS
        have hvcyc : v ∈ cycSet := Finset.mem_filter.mpr ⟨hvS, hvm⟩
        have hvne : v.val ≠ g := fun h => hgnotS (by convert hvS; exact Fin.ext h.symm)
        by_cases hlt : v.val < g
        · have hvL : v ∈ cycL := Finset.mem_filter.mpr ⟨hvcyc, hlt⟩
          rw [hcycL_eq, Finset.mem_filter] at hvL
          exact Or.inl hvL.2
        · have hvR : v ∈ cycR := Finset.mem_filter.mpr ⟨hvcyc, by omega⟩
          rw [hcycR_eq, Finset.mem_filter] at hvR
          exact Or.inr (Or.inl hvR.2)
      · rintro (h1 | ⟨h2a, h2b⟩ | ⟨h3a, _⟩)
        · have hvL : v ∈ cycL := by rw [hcycL_eq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp hvL).1).1
        · have hvR : v ∈ cycR := by rw [hcycR_eq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2a, h2b⟩
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp hvR).1).1
        · omega
    · have htail := htail_iff v (by omega)
      rw [htail]
      omega

/-- **Theorem 2 (Exact Closed-Form Polynomial):**
For every `m ≥ 3`, `l ≥ 0`, and `k : ℕ`,
`czfCoeff (tadpoleGraph m l hm) k = N_coeff m k + ∑ a ∈ Finset.range (l + 1), A_coeff m (k - a)`. -/
theorem tadpole_czf_formula (m l : ℕ) (hm : 3 ≤ m) (k : ℕ) :
    czfCoeff (tadpoleGraph m l hm) k = tadpoleFormula m l k := by
  classical
  unfold czfCoeff tadpoleFormula
  set All := (Finset.univ : Finset (Finset (Fin (m + l)))).filter
    (fun S => S.card = k ∧ IsConnectedZFSet (tadpoleGraph m l hm) S)
  let AllN := All.filter (fun S => cycV 0 (by omega) ∉ S)
  let AllA := All.filter (fun S => cycV 0 (by omega) ∈ S)
  have hsplit : All.card = AllN.card + AllA.card := by
    have hunion : All = AllN ∪ AllA := by
      ext S; simp only [Finset.mem_union, AllN, AllA, Finset.mem_filter]; tauto
    have hdisj : Disjoint AllN AllA := by
      rw [Finset.disjoint_left]; intro S h1 h2
      simp only [AllN, AllA, Finset.mem_filter] at h1 h2; exact h1.2 h2.2
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  rw [hsplit]
  -- Count `AllN.card = N_coeff m k`
  have hN : AllN.card = N_coeff m k := by
    unfold N_coeff
    split_ifs with hk
    · -- `2 ≤ k ∧ k ≤ m - 1`: bijection with `p ∈ Finset.Icc 1 (m - k)`
      have hcard_Icc : (Finset.Icc 1 (m - k)).card = m - k := by simp
      rw [← hcard_Icc]
      symm
      refine Finset.card_bij (fun p _ => mkTypeN m l p k) ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_Icc] at hp
        have hsp := mkTypeN_spec (l := l) hm hp.1 hk.1 (by omega)
        simp only [AllN, All, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨hsp.1, hsp.2.2⟩, hsp.2.1⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        rw [Finset.mem_Icc] at hp₁ hp₂
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hmem : (⟨p₁, by omega⟩ : Fin (m + l)) ∈ mkTypeN m l p₁ k := by
            simp only [mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and]; omega
          rw [heq] at hmem
          simp only [mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and] at hmem; omega
        · have hmem : (⟨p₂, by omega⟩ : Fin (m + l)) ∈ mkTypeN m l p₂ k := by
            simp only [mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and]; omega
          rw [← heq] at hmem
          simp only [mkTypeN, Finset.mem_filter, Finset.mem_univ, true_and] at hmem; omega
      · intro S hS
        simp only [AllN, All, Finset.mem_filter, Finset.mem_univ, true_and] at hS
        rcases classify_typeN hm hS.1.2 hS.2 with ⟨p, b, hp1, hb2, hpb, rfl⟩
        have hsp := mkTypeN_spec (l := l) hm hp1 hb2 hpb
        have hbk : b = k := hsp.1.symm.trans hS.1.1
        subst hbk
        exact ⟨p, Finset.mem_Icc.mpr ⟨hp1, by omega⟩, rfl⟩
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro S hS
      simp only [AllN, All, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rcases classify_typeN hm hS.1.2 hS.2 with ⟨p, b, hp1, hb2, hpb, rfl⟩
      have hsp := mkTypeN_spec (l := l) hm hp1 hb2 hpb
      omega
  -- Count `AllA.card = ∑ a ∈ range (l + 1), A_coeff m (k - a)`
  have hA : AllA.card = ∑ a ∈ Finset.range (l + 1), A_coeff m (k - a) := by
    -- Partition `AllA` by tail length `a = (S.filter (fun v => m ≤ v.val)).card ∈ range (l + 1)`
    let tailLen : Finset (Fin (m + l)) → ℕ := fun S => (S.filter (fun v => m ≤ v.val)).card
    have hmap : ∀ S ∈ AllA, tailLen S ∈ Finset.range (l + 1) := by
      intro S hS
      simp only [AllA, All, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rw [Finset.mem_range]
      have hsub : S.filter (fun v => m ≤ v.val) ⊆ Finset.univ.filter (fun v : Fin (m + l) => m ≤ v.val) :=
        Finset.filter_subset_filter _ (Finset.subset_univ _)
      have hcard_all : (Finset.univ.filter (fun v : Fin (m + l) => m ≤ v.val)).card = l := by
        let f : Fin l → Fin (m + l) := fun t => ⟨m + t.val, by omega⟩
        have himg : Finset.univ.image f = Finset.univ.filter (fun v : Fin (m + l) => m ≤ v.val) := by
          ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
          exact ⟨fun ⟨t, ht⟩ => by rw [← ht]; dsimp [f]; omega,
            fun hv => ⟨⟨v.val - m, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩⟩
        rw [← himg, Finset.card_image_of_injective _ (fun x y h => Fin.ext (by
          have := congr_arg Fin.val h; dsimp [f] at this; omega)), Finset.card_univ, Fintype.card_fin]
      have := Finset.card_le_card hsub
      dsimp only [tailLen]
      omega
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_range] at ha
    have ha_le : a ≤ l := by omega
    -- Compute tailLen of `mkTypeAFull` and `mkTypeAProp`
    have htl_full : tailLen (mkTypeAFull m l a) = a := by
      let f : Fin a → Fin (m + l) := fun t => ⟨m + t.val, by omega⟩
      have himg : Finset.univ.image f = (mkTypeAFull m l a).filter (fun v => m ≤ v.val) := by
        ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, mkTypeAFull, Finset.mem_filter]
        exact ⟨fun ⟨t, ht⟩ => by rw [← ht]; dsimp [f]; omega,
          fun ⟨h1, h2⟩ => ⟨⟨v.val - m, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩⟩
      change ((mkTypeAFull m l a).filter (fun v => m ≤ v.val)).card = a
      rw [← himg, Finset.card_image_of_injective _ (fun x y h => Fin.ext (by
        have := congr_arg Fin.val h; dsimp [f] at this; omega)), Finset.card_univ, Fintype.card_fin]
    have htl_prop : ∀ b r, 2 ≤ b → b ≤ m - 1 → r < b → tailLen (mkTypeAProp m l a b r) = a := by
      intro b r _ hbm _
      let f : Fin a → Fin (m + l) := fun t => ⟨m + t.val, by omega⟩
      have himg : Finset.univ.image f = (mkTypeAProp m l a b r).filter (fun v => m ≤ v.val) := by
        ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, mkTypeAProp, Finset.mem_filter]
        exact ⟨fun ⟨t, ht⟩ => by rw [← ht]; dsimp [f]; omega,
          fun ⟨h1, h2⟩ => ⟨⟨v.val - m, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩⟩
      change ((mkTypeAProp m l a b r).filter (fun v => m ≤ v.val)).card = a
      rw [← himg, Finset.card_image_of_injective _ (fun x y h => Fin.ext (by
        have := congr_arg Fin.val h; dsimp [f] at this; omega)), Finset.card_univ, Fintype.card_fin]
    unfold A_coeff
    split_ifs with h1 h2
    · -- `2 ≤ k - a ∧ k - a ≤ m - 1` (and `a ≤ k` automatically since `k - a ≥ 2`)
      set b := k - a
      have hb2 : 2 ≤ b := h1.1
      have hbm : b ≤ m - 1 := h1.2
      have hba : b + a = k := by omega
      rw [← Finset.card_range b]
      symm
      refine Finset.card_bij (fun r _ => mkTypeAProp m l a b r) ?_ ?_ ?_
      · intro r hr
        rw [Finset.mem_range] at hr
        have hsp := mkTypeAProp_spec hm ha_le hb2 hbm hr
        simp only [AllA, All, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨⟨hsp.1.trans hba, hsp.2.2⟩, hsp.2.1⟩, htl_prop b r hb2 hbm hr⟩
      · intro r₁ hr₁ r₂ hr₂ heq
        rw [Finset.mem_range] at hr₁ hr₂
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hmem : (⟨b - r₂, by omega⟩ : Fin (m + l)) ∈ mkTypeAProp m l a b r₁ := by
            simp only [mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega
          rw [heq] at hmem
          simp only [mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and] at hmem; omega
        · have hmem : (⟨b - r₁, by omega⟩ : Fin (m + l)) ∈ mkTypeAProp m l a b r₂ := by
            simp only [mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and]; omega
          rw [← heq] at hmem
          simp only [mkTypeAProp, Finset.mem_filter, Finset.mem_univ, true_and] at hmem; omega
      · intro S hS
        simp only [AllA, All, Finset.mem_filter, Finset.mem_univ, true_and] at hS
        rcases classify_typeA hm hS.1.1.2 hS.1.2 with ⟨a', ha', rfl⟩ | ⟨a', b', r, ha', hb2, hbm, hr, rfl⟩
        · have hsp := mkTypeAFull_spec hm ha'
          have htl' : tailLen (mkTypeAFull m l a') = a' := by
            let f : Fin a' → Fin (m + l) := fun t => ⟨m + t.val, by omega⟩
            have himg : Finset.univ.image f = (mkTypeAFull m l a').filter (fun v => m ≤ v.val) := by
              ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, mkTypeAFull, Finset.mem_filter]
              exact ⟨fun ⟨t, ht⟩ => by rw [← ht]; dsimp [f]; omega,
                fun ⟨h1', h2'⟩ => ⟨⟨v.val - m, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩⟩
            change ((mkTypeAFull m l a').filter (fun v => m ≤ v.val)).card = a'
            rw [← himg, Finset.card_image_of_injective _ (fun x y h => Fin.ext (by
              have := congr_arg Fin.val h; dsimp [f] at this; omega)), Finset.card_univ, Fintype.card_fin]
          omega
        · have hsp := mkTypeAProp_spec hm ha' hb2 hbm hr
          have htl' : tailLen (mkTypeAProp m l a' b' r) = a' := by
            let f : Fin a' → Fin (m + l) := fun t => ⟨m + t.val, by omega⟩
            have himg : Finset.univ.image f = (mkTypeAProp m l a' b' r).filter (fun v => m ≤ v.val) := by
              ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, mkTypeAProp, Finset.mem_filter]
              exact ⟨fun ⟨t, ht⟩ => by rw [← ht]; dsimp [f]; omega,
                fun ⟨h1', h2'⟩ => ⟨⟨v.val - m, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩⟩
            change ((mkTypeAProp m l a' b' r).filter (fun v => m ≤ v.val)).card = a'
            rw [← himg, Finset.card_image_of_injective _ (fun x y h => Fin.ext (by
              have := congr_arg Fin.val h; dsimp [f] at this; omega)), Finset.card_univ, Fintype.card_fin]
          have haeq : a' = a := htl'.symm.trans hS.2
          subst haeq
          have hbeq : b' = b := by omega
          subst hbeq
          exact ⟨r, Finset.mem_range.mpr hr, rfl⟩
    · -- `k - a = m`: unique set `mkTypeAFull m l a`
      have hma : m + a = k := by omega
      have huniq : {S ∈ AllA | tailLen S = a} = {mkTypeAFull m l a} := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_singleton, AllA, All, Finset.mem_univ, true_and]
        constructor
        · intro hS
          rcases classify_typeA hm hS.1.1.2 hS.1.2 with ⟨a', ha', rfl⟩ | ⟨a', b', r, ha', hb2, hbm, hr, rfl⟩
          · have hsp := mkTypeAFull_spec hm ha'
            have haeq : a' = a := by omega
            subst haeq; rfl
          · have hsp := mkTypeAProp_spec hm ha' hb2 hbm hr
            have htl' : tailLen (mkTypeAProp m l a' b' r) = a' := by
              let f : Fin a' → Fin (m + l) := fun t => ⟨m + t.val, by omega⟩
              have himg : Finset.univ.image f = (mkTypeAProp m l a' b' r).filter (fun v => m ≤ v.val) := by
                ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, mkTypeAProp, Finset.mem_filter]
                exact ⟨fun ⟨t, ht⟩ => by rw [← ht]; dsimp [f]; omega,
                  fun ⟨h1', h2'⟩ => ⟨⟨v.val - m, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩⟩
              change ((mkTypeAProp m l a' b' r).filter (fun v => m ≤ v.val)).card = a'
              rw [← himg, Finset.card_image_of_injective _ (fun x y h => Fin.ext (by
                have := congr_arg Fin.val h; dsimp [f] at this; omega)), Finset.card_univ, Fintype.card_fin]
            omega
        · rintro rfl
          have hsp := mkTypeAFull_spec hm ha_le
          exact ⟨⟨⟨hsp.1.trans hma, hsp.2.2⟩, hsp.2.1⟩, htl_full⟩
      rw [huniq, Finset.card_singleton]
    · -- Otherwise: empty fiber
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro S hS
      simp only [AllA, All, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rcases classify_typeA hm hS.1.1.2 hS.1.2 with ⟨a', ha', rfl⟩ | ⟨a', b', r, ha', hb2, hbm, hr, rfl⟩
      · have hsp := mkTypeAFull_spec hm ha'
        have htl' : tailLen (mkTypeAFull m l a') = a' := by
          let f : Fin a' → Fin (m + l) := fun t => ⟨m + t.val, by omega⟩
          have himg : Finset.univ.image f = (mkTypeAFull m l a').filter (fun v => m ≤ v.val) := by
            ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, mkTypeAFull, Finset.mem_filter]
            exact ⟨fun ⟨t, ht⟩ => by rw [← ht]; dsimp [f]; omega,
              fun ⟨h1', h2'⟩ => ⟨⟨v.val - m, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩⟩
          change ((mkTypeAFull m l a').filter (fun v => m ≤ v.val)).card = a'
          rw [← himg, Finset.card_image_of_injective _ (fun x y h => Fin.ext (by
            have := congr_arg Fin.val h; dsimp [f] at this; omega)), Finset.card_univ, Fintype.card_fin]
        omega
      · have hsp := mkTypeAProp_spec hm ha' hb2 hbm hr
        have htl' : tailLen (mkTypeAProp m l a' b' r) = a' := by
          let f : Fin a' → Fin (m + l) := fun t => ⟨m + t.val, by omega⟩
          have himg : Finset.univ.image f = (mkTypeAProp m l a' b' r).filter (fun v => m ≤ v.val) := by
            ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, mkTypeAProp, Finset.mem_filter]
            exact ⟨fun ⟨t, ht⟩ => by rw [← ht]; dsimp [f]; omega,
              fun ⟨h1', h2'⟩ => ⟨⟨v.val - m, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩⟩
          change ((mkTypeAProp m l a' b' r).filter (fun v => m ≤ v.val)).card = a'
          rw [← himg, Finset.card_image_of_injective _ (fun x y h => Fin.ext (by
            have := congr_arg Fin.val h; dsimp [f] at this; omega)), Finset.card_univ, Fintype.card_fin]
        omega
  rw [hN, hA]

/-! ### 5. Exact Log-Concavity Criterion and Main Theorems -/

private lemma tadpoleFormula_2_3_4 {m l : ℕ} (hm : 5 ≤ m) (hl : 2 ≤ l) :
    tadpoleFormula m l 2 = m ∧
    tadpoleFormula m l 3 = m + 2 ∧
    tadpoleFormula m l 4 = m + 5 := by
  have hcut : ∀ (K : ℕ), K ≤ 4 →
      ∑ a ∈ Finset.range (l + 1), A_coeff m (K - a) =
        ∑ a ∈ Finset.range 3, A_coeff m (K - a) := by
    intro K hK
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun a ha hnot => ?_
    rw [Finset.mem_range] at ha hnot
    unfold A_coeff; split_ifs <;> omega
  refine ⟨?_, ?_, ?_⟩
  · unfold tadpoleFormula
    rw [hcut 2 (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, N_coeff, A_coeff]
    split_ifs <;> omega
  · unfold tadpoleFormula
    rw [hcut 3 (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, N_coeff, A_coeff]
    split_ifs <;> omega
  · unfold tadpoleFormula
    rw [hcut 4 (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, N_coeff, A_coeff]
    split_ifs <;> omega

private lemma tadpoleFormula_l0 {m k : ℕ} (hm : 3 ≤ m) :
    tadpoleFormula m 0 k = if 2 ≤ k ∧ k ≤ m - 1 then m else if k = m then 1 else 0 := by
  unfold tadpoleFormula N_coeff A_coeff
  simp only [zero_add, Finset.sum_range_one, Nat.sub_zero]
  split_ifs <;> omega

private lemma tadpoleFormula_l1 {m k : ℕ} (hm : 3 ≤ m) :
    tadpoleFormula m 1 k =
      if k = 2 then m
      else if 3 ≤ k ∧ k ≤ m - 1 then m + k - 1
      else if k = m then m
      else if k = m + 1 then 1
      else 0 := by
  unfold tadpoleFormula N_coeff A_coeff
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.sub_zero, zero_add]
  split_ifs <;> omega

private lemma tadpoleFormula_m3 {l k : ℕ} :
    tadpoleFormula 3 l k =
      if 2 ≤ k ∧ k ≤ l + 2 then 3
      else if k = l + 3 then 1
      else 0 := by
  unfold tadpoleFormula
  have hN : N_coeff 3 k = if k = 2 then 1 else 0 := by
    unfold N_coeff; split_ifs <;> omega
  have hA : ∀ x, A_coeff 3 x = if x = 2 then 2 else if x = 3 then 1 else 0 := by
    intro x; unfold A_coeff; split_ifs <;> omega
  rw [hN]
  have hsum : ∑ a ∈ Finset.range (l + 1), A_coeff 3 (k - a) =
      (if 2 ≤ k ∧ k ≤ l + 2 then 2 else 0) + (if 3 ≤ k ∧ k ≤ l + 3 then 1 else 0) := by
    have hrew : ∀ a, A_coeff 3 (k - a) =
        (if k - a = 2 then 2 else 0) + (if k - a = 3 then 1 else 0) := by
      intro a; rw [hA]; split_ifs <;> omega
    simp_rw [hrew, Finset.sum_add_distrib]
    have h1 : ∑ a ∈ Finset.range (l + 1), (if k - a = 2 then 2 else 0) =
        if 2 ≤ k ∧ k ≤ l + 2 then 2 else 0 := by
      split_ifs with hk
      · rw [Finset.sum_eq_single (k - 2)]
        · simp [show k - (k - 2) = 2 by omega]
        · intro a ha hne; rw [Finset.mem_range] at ha; simp [show k - a ≠ 2 by omega]
        · intro hnot; rw [Finset.mem_range] at hnot; omega
      · refine Finset.sum_eq_zero fun a ha => ?_
        rw [Finset.mem_range] at ha; simp [show k - a ≠ 2 by omega]
    have h2 : ∑ a ∈ Finset.range (l + 1), (if k - a = 3 then 1 else 0) =
        if 3 ≤ k ∧ k ≤ l + 3 then 1 else 0 := by
      split_ifs with hk
      · rw [Finset.sum_eq_single (k - 3)]
        · simp [show k - (k - 3) = 3 by omega]
        · intro a ha hne; rw [Finset.mem_range] at ha; simp [show k - a ≠ 3 by omega]
        · intro hnot; rw [Finset.mem_range] at hnot; omega
      · refine Finset.sum_eq_zero fun a ha => ?_
        rw [Finset.mem_range] at ha; simp [show k - a ≠ 3 by omega]
    rw [h1, h2]
  rw [hsum]
  split_ifs <;> omega

private lemma tadpoleFormula_m4 {l k : ℕ} (hl : 2 ≤ l) :
    tadpoleFormula 4 l k =
      if k = 2 then 4
      else if 3 ≤ k ∧ k ≤ l + 2 then 6
      else if k = l + 3 then 4
      else if k = l + 4 then 1
      else 0 := by
  unfold tadpoleFormula
  have hN : N_coeff 4 k = if k = 2 then 2 else if k = 3 then 1 else 0 := by
    unfold N_coeff; split_ifs <;> omega
  have hA : ∀ x, A_coeff 4 x = if x = 2 then 2 else if x = 3 then 3 else if x = 4 then 1 else 0 := by
    intro x; unfold A_coeff; split_ifs <;> omega
  rw [hN]
  have hrew : ∀ a, A_coeff 4 (k - a) =
      (if k - a = 2 then 2 else 0) + (if k - a = 3 then 3 else 0) + (if k - a = 4 then 1 else 0) := by
    intro a; rw [hA]; split_ifs <;> omega
  simp_rw [hrew, Finset.sum_add_distrib]
  have hsingle : ∀ (d c : ℕ), 1 ≤ d →
      ∑ a ∈ Finset.range (l + 1), (if k - a = d then c else 0) =
        if d ≤ k ∧ k ≤ l + d then c else 0 := by
    intro d c hd
    split_ifs with hk
    · rw [Finset.sum_eq_single (k - d)]
      · simp [show k - (k - d) = d by omega]
      · intro a ha hne; rw [Finset.mem_range] at ha; simp [show k - a ≠ d by omega]
      · intro hnot; rw [Finset.mem_range] at hnot; omega
    · refine Finset.sum_eq_zero fun a ha => ?_
      rw [Finset.mem_range] at ha; simp [show k - a ≠ d by omega]
  rw [hsingle 2 2 (by omega), hsingle 3 3 (by omega), hsingle 4 1 (by omega)]
  split_ifs <;> omega

private lemma lc_tadpoleFormula_l1 {m : ℕ} (hm : 3 ≤ m) :
    IsLogConcaveSeq (tadpoleFormula m 1) (m + 1) := by
  intro k hk1 hkn
  by_cases hk2 : k ≤ 2
  · have hcases : k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl
    · have h1 : tadpoleFormula m 1 1 = 0 := by
        unfold tadpoleFormula N_coeff A_coeff; simp; intro i hi; split_ifs <;> omega
      have h0 : tadpoleFormula m 1 0 = 0 := by
        unfold tadpoleFormula N_coeff A_coeff; simp; omega
      rw [h1, show 1 - 1 = 0 by rfl, h0]; simp
    · have h1 : tadpoleFormula m 1 2 = m := by rw [tadpoleFormula_l1 hm]; simp
      have h0 : tadpoleFormula m 1 1 = 0 := by
        unfold tadpoleFormula N_coeff A_coeff; simp; intro i hi; split_ifs <;> omega
      rw [h1, show 2 - 1 = 1 by rfl, h0]; simp
  · by_cases hkm : k ≤ m - 2
    · have hk3 : 3 ≤ k := by omega
      have h1 : tadpoleFormula m 1 k = m + k - 1 := by
        rw [tadpoleFormula_l1 hm]; split_ifs <;> omega
      have h2 : tadpoleFormula m 1 (k + 1) = m + (k + 1) - 1 := by
        rw [tadpoleFormula_l1 hm]; split_ifs <;> omega
      rw [h1, h2]
      by_cases hk3eq : k = 3
      · subst hk3eq
        have h0 : tadpoleFormula m 1 2 = m := by rw [tadpoleFormula_l1 hm]; simp
        rw [show 3 - 1 = 2 by rfl, h0]
        have hm4 : 4 ≤ m := by omega
        zify [show 1 ≤ m + 3 by omega, show 1 ≤ m + (3 + 1) by omega]; nlinarith
      · have h0 : tadpoleFormula m 1 (k - 1) = m + (k - 1) - 1 := by
          rw [tadpoleFormula_l1 hm]; split_ifs <;> omega
        rw [h0]
        zify [hk1, show 1 ≤ m + k by omega, show 1 ≤ m + (k - 1) by omega,
          show 1 ≤ m + (k + 1) by omega]; nlinarith
    · by_cases hkm1 : k = m - 1
      · subst k
        have h1 : tadpoleFormula m 1 (m - 1) = if m = 3 then 3 else 2 * m - 2 := by
          rw [tadpoleFormula_l1 hm]; split_ifs <;> omega
        have h2 : tadpoleFormula m 1 (m - 1 + 1) = m := by
          rw [tadpoleFormula_l1 hm]; split_ifs <;> omega
        have h0 : tadpoleFormula m 1 (m - 1 - 1) = if m = 3 then 0 else if m = 4 then 4 else 2 * m - 3 := by
          rw [tadpoleFormula_l1 hm]; split_ifs <;> omega
        rw [h1, h2, h0]
        by_cases hm3 : m = 3
        · subst hm3; norm_num
        · by_cases hm4 : m = 4
          · subst hm4; norm_num
          · simp only [hm3, hm4, ↓reduceIte]
            have hm5 : 5 ≤ m := by omega
            zify [show 2 ≤ 2 * m by omega, show 3 ≤ 2 * m by omega]; nlinarith
      · have hkeq : k = m := by omega
        subst k
        have h1 : tadpoleFormula m 1 m = m := by rw [tadpoleFormula_l1 hm]; split_ifs <;> omega
        have h2 : tadpoleFormula m 1 (m + 1) = 1 := by rw [tadpoleFormula_l1 hm]; split_ifs <;> omega
        have h0 : tadpoleFormula m 1 (m - 1) ≤ 2 * m := by
          rw [tadpoleFormula_l1 hm]; split_ifs <;> omega
        rw [h1, h2]
        nlinarith

/-- **Theorem 3 (Complete Log-Concavity Criterion for Tadpole Graphs):**
For every `m ≥ 3` and `l ≥ 0`, the connected zero forcing polynomial of the tadpole
graph `T_{m, l}` is log-concave **if and only if** `m ≤ 4` or `l ≤ 1`. -/
theorem tadpole_czf_logConcave_iff (m l : ℕ) (hm : 3 ≤ m) :
    IsLogConcaveSeq (czfCoeff (tadpoleGraph m l hm)) (m + l) ↔ m ≤ 4 ∨ l ≤ 1 := by
  have hrew : IsLogConcaveSeq (czfCoeff (tadpoleGraph m l hm)) (m + l) ↔
      IsLogConcaveSeq (tadpoleFormula m l) (m + l) := by
    unfold IsLogConcaveSeq
    simp_rw [tadpole_czf_formula m l hm]
  rw [hrew]
  constructor
  · intro hlc
    by_contra h
    push Not at h
    have hvals := tadpoleFormula_2_3_4 (by omega : 5 ≤ m) (by omega : 2 ≤ l)
    have h3 := hlc 3 (by omega) (by omega)
    rw [hvals.1, hvals.2.1, hvals.2.2] at h3
    nlinarith
  · rintro (hm4 | hl1)
    · by_cases hm3 : m = 3
      · subst hm3
        intro k hk1 hkn
        rw [tadpoleFormula_m3, tadpoleFormula_m3, tadpoleFormula_m3]
        split_ifs <;> omega
      · have hm4' : m = 4 := by omega
        subst hm4'
        by_cases hl2 : 2 ≤ l
        · intro k hk1 hkn
          rw [tadpoleFormula_m4 hl2, tadpoleFormula_m4 hl2, tadpoleFormula_m4 hl2]
          split_ifs <;> omega
        · by_cases hl0 : l = 0
          · subst hl0
            intro k hk1 hkn
            rw [tadpoleFormula_l0 hm, tadpoleFormula_l0 hm, tadpoleFormula_l0 hm]
            split_ifs <;> omega
          · have hl1' : l = 1 := by omega
            subst hl1'
            exact lc_tadpoleFormula_l1 hm
    · by_cases hl0 : l = 0
      · subst hl0
        intro k hk1 hkn
        rw [tadpoleFormula_l0 hm, tadpoleFormula_l0 hm, tadpoleFormula_l0 hm]
        split_ifs <;> first | omega | nlinarith
      · have hl1' : l = 1 := by omega
        subst hl1'
        exact lc_tadpoleFormula_l1 hm

/-- **Smallest Counterexample (`T_{5, 2}`, order 7):**
`Z_C(T_{5, 2}; x) = 5x² + 7x³ + 10x⁴ + 8x⁵ + 5x⁶ + x⁷` fails log-concavity at `k = 3`
(`7² = 49 < 50 = 5 · 10`). -/
theorem tadpole_5_2_counterexample :
    let G := tadpoleGraph 5 2 (by omega)
    G.Connected ∧
    G.edgeFinset.card = 7 ∧
    (List.range 8).map (czfCoeff G) = [0, 0, 5, 7, 10, 8, 5, 1] ∧
    czfCoeff G 3 ^ 2 < czfCoeff G 2 * czfCoeff G 4 ∧
    ¬ IsLogConcaveSeq (czfCoeff G) 7 := by
  dsimp only
  refine ⟨tadpoleGraph_connected 5 2 (by omega), tadpoleGraph_edge_card 5 2 (by omega), ?_, ?_, ?_⟩
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, tadpole_czf_formula]
    decide
  · rw [tadpole_czf_formula, tadpole_czf_formula, tadpole_czf_formula]
    decide
  · rw [tadpole_czf_logConcave_iff 5 2 (by omega)]
    omega

/-- **Main Disproof (Mukherjee–Ray Problem 6.2, `arXiv:2611.10985v2`):**
For every integer `n ≥ 7`, there exists a connected unicyclic graph `G` on `Fin n`
(`|E(G)| = n`) whose connected zero forcing polynomial is not log-concave. -/
theorem unicyclic_not_logConcave_every_order_ge_7 (n : ℕ) (hn : 7 ≤ n) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧
      G.edgeFinset.card = n ∧
      ¬ IsLogConcaveSeq (czfCoeff G) n := by
  obtain ⟨l, rfl⟩ : ∃ l, n = 5 + l := ⟨n - 5, by omega⟩
  refine ⟨tadpoleGraph 5 l (by omega), inferInstance,
    tadpoleGraph_connected 5 l (by omega),
    tadpoleGraph_edge_card 5 l (by omega), ?_⟩
  rw [tadpole_czf_logConcave_iff 5 l (by omega)]
  omega

end MukherjeeRayUnicyclicZF
