import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases

/-!
# Disproof of Chen–Zwicker Conjecture 1 for EF1_outer (arXiv:2402.05884, arXiv:2608.29902)

Conjecture 1 states that the EF1_outer spectrum of every connected graph is an initial string of
yes, then a (possibly empty) string of no, then yes forever.

`H` is `K_{2,3}` with parts `{0, 1}` and `{2, 3, 4}` plus the pendant leaves `5–2`, `6–3`, `7–4`.
For every valuation class between the single common binary valuation `beta = 1_{2,3,4}` and the
heterogeneous monotone valuations, the spectrum of `H` has no at `k = 2`, yes at `k = 3` and no at
`k = 4`.

Valuations are defined on all vertex subsets and monotone for inclusion. A valuation on connected
subsets that is monotone among them extends to all subsets by `S ↦ max {v T | T ⊆ S connected}`,
and EF1_outer only evaluates connected sets, so this is no loss of generality.

Proof outline.
* `k = 2`, `k = 4`: bitmask computations checked by `decide +kernel`, bridged to `Finset`s by
  `testBit_toMask` and `connM_of_conn` (a disconnected set has an explicit separating subset).
  For `k = 4` a counting argument reduces the claim to a property of single bundles.
* `k = 3`, heterogeneous monotone: `acc p b v` says that an agent with valuation `v` accepts block
  `b` of partition `p` (EF1_outer towards both other blocks). Single-agent lemmas `clN` are short
  clauses over these propositions, each proved by case analysis on comparisons. The main proof
  is a case split on acceptance propositions of the three agents; every leaf either contradicts a
  clause or exhibits an allocation in which every agent accepts its own block.
-/

namespace ChenZwickerEF1Outer

open Finset

/-! ## Definitions (Definition 2 of arXiv:2608.29902) -/

section Defs

variable {V : Type*} [DecidableEq V]

/-- A bundle is connected if it induces a connected subgraph; `∅` and singletons are connected.
Stated without subtypes: no nonempty proper subset is separated from the rest of the bundle.
See `isConnectedBundle_iff_connected` for the equivalence with Mathlib's notion. -/
def IsConnectedBundle (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ T ∈ S.powerset, T.Nonempty → T ≠ S → ∃ x ∈ T, ∃ y ∈ S \ T, G.Adj x y

/-- An allocation of `V` to `k` agents: pairwise disjoint connected bundles (possibly empty)
whose union is `V`. -/
def IsConnectedAllocation [Fintype V] (G : SimpleGraph V) (k : ℕ) (A : Fin k → Finset V) :
    Prop :=
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ univ.biUnion A = univ ∧
    ∀ i, IsConnectedBundle G (A i)

/-- Monotone valuation. -/
def IsMonotoneVal {α : Type*} [LinearOrder α] (v : Finset V → α) : Prop :=
  ∀ S T, S ⊆ T → v S ≤ v T

/-- EF1_outer (Definition 2): for all agents `i, j`, either `A j = ∅` or some `x ∈ A j` leaves
`A j \ {x}` connected and `v i (A j \ {x}) ≤ v i (A i)`. -/
def IsEF1Outer [Fintype V] {α : Type*} [LinearOrder α] (G : SimpleGraph V) (k : ℕ)
    (v : Fin k → Finset V → α) (A : Fin k → Finset V) : Prop :=
  IsConnectedAllocation G k A ∧ ∀ i j : Fin k, A j = ∅ ∨
    ∃ x ∈ A j, IsConnectedBundle G (A j \ {x}) ∧ v i (A j \ {x}) ≤ v i (A i)

end Defs

/-- Common binary additive valuation with weight `w x ∈ {0, 1}`. -/
def commonBinaryVal (w : Fin 8 → Bool) (S : Finset (Fin 8)) : ℕ :=
  (S.filter (fun x => w x = true)).card

/-- Weight 1 on the hubs `{2, 3, 4}`. -/
def hubW : Fin 8 → Bool := ![false, false, true, true, true, false, false, false]

/-- The common binary valuation `beta = 1_{2,3,4}`. -/
def beta (S : Finset (Fin 8)) : ℕ := commonBinaryVal hubW S

/-! ## Connectivity lemmas -/

section Conn

variable {V : Type*} [DecidableEq V]

theorem isConnectedBundle_empty (G : SimpleGraph V) : IsConnectedBundle G (∅ : Finset V) := by
  intro T hT hne _
  rw [mem_powerset, subset_empty] at hT
  exact absurd hT hne.ne_empty

theorem isConnectedBundle_singleton (G : SimpleGraph V) (x : V) : IsConnectedBundle G {x} := by
  intro T hT hne hneq
  rw [mem_powerset, subset_singleton_iff] at hT
  rcases hT with rfl | rfl
  · exact absurd rfl hne.ne_empty
  · exact absurd rfl hneq

theorem isConnectedBundle_insert {G : SimpleGraph V} {T : Finset V} (x y : V)
    (hT : IsConnectedBundle G T) (hx : x ∉ T) (hy : y ∈ T) (hxy : G.Adj x y) :
    IsConnectedBundle G (insert x T) := by
  intro U hU hne hneq
  rw [mem_powerset] at hU
  by_cases hxU : x ∈ U
  · by_cases hE : U.erase x = ∅
    · refine ⟨x, hxU, y, mem_sdiff.2 ⟨mem_insert_of_mem hy, fun hyU => ?_⟩, hxy⟩
      have : y ∈ U.erase x := mem_erase.2 ⟨fun h => hx (h ▸ hy), hyU⟩
      rw [hE] at this
      simp at this
    · have hsub : U.erase x ⊆ T := by
        intro z hz
        rcases mem_erase.1 hz with ⟨hzx, hzU⟩
        rcases mem_insert.1 (hU hzU) with h | h
        · exact absurd h hzx
        · exact h
      by_cases hET : U.erase x = T
      · exact absurd (show U = insert x T by rw [← hET, insert_erase hxU]) hneq
      · obtain ⟨a, ha, b, hb, hab⟩ := hT (U.erase x) (mem_powerset.2 hsub)
          (nonempty_iff_ne_empty.2 hE) hET
        refine ⟨a, mem_of_mem_erase ha, b, ?_, hab⟩
        rcases mem_sdiff.1 hb with ⟨hbT, hbU⟩
        refine mem_sdiff.2 ⟨mem_insert_of_mem hbT, fun hbU' => hbU (mem_erase.2 ⟨?_, hbU'⟩)⟩
        rintro rfl
        exact hx hbT
  · have hsub : U ⊆ T := by
      intro z hz
      rcases mem_insert.1 (hU hz) with h | h
      · exact absurd (h ▸ hz) hxU
      · exact h
    by_cases hUT : U = T
    · subst hUT
      exact ⟨y, hy, x, mem_sdiff.2 ⟨mem_insert_self _ _, hxU⟩, hxy.symm⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := hT U (mem_powerset.2 hsub) hne hUT
      exact ⟨a, ha, b, mem_sdiff.2 ⟨mem_insert_of_mem (mem_sdiff.1 hb).1, (mem_sdiff.1 hb).2⟩,
        hab⟩

/-- A walk in the induced graph from inside `T` to outside `T` crosses an edge out of `T`. -/
theorem walk_cross (G : SimpleGraph V) {S : Finset V} (T : Finset V) {u u' : (S : Set V)}
    (w : (G.induce (S : Set V)).Walk u u') (h1 : u.1 ∈ T) (h2 : u'.1 ∉ T) :
    ∃ x ∈ T, ∃ y ∈ S \ T, G.Adj x y := by
  induction w with
  | nil => exact absurd h1 h2
  | @cons u₀ m _ hadj _ ih =>
    by_cases hm : m.1 ∈ T
    · exact ih hm h2
    · exact ⟨u₀.1, h1, m.1, mem_sdiff.2 ⟨m.2, hm⟩, by simpa using hadj⟩

/-- For nonempty `S`, `IsConnectedBundle` is Mathlib's connectivity of the induced graph. -/
theorem isConnectedBundle_iff_connected (G : SimpleGraph V) {S : Finset V} (hS : S.Nonempty) :
    IsConnectedBundle G S ↔ (G.induce (S : Set V)).Connected := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp⟩ := hS
    let p' : (S : Set V) := ⟨p, hp⟩
    let R : Finset V := S.filter (fun y => ∃ hy : y ∈ (S : Set V),
      (G.induce (S : Set V)).Reachable p' ⟨y, hy⟩)
    have hRS : R = S := by
      by_contra hne
      obtain ⟨a, ha, b, hb, hab⟩ := h R (mem_powerset.2 (filter_subset _ _))
        ⟨p, mem_filter.2 ⟨hp, hp, SimpleGraph.Reachable.refl _⟩⟩ hne
      obtain ⟨-, haS, hreach⟩ := mem_filter.1 ha
      obtain ⟨hbS, hbR⟩ := mem_sdiff.1 hb
      exact hbR (mem_filter.2 ⟨hbS, hbS, hreach.trans (SimpleGraph.Adj.reachable (by simpa using hab))⟩)
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨p', fun q => ?_⟩
    have hq : q.1 ∈ R := by rw [hRS]; exact q.2
    obtain ⟨-, _, hr⟩ := mem_filter.1 hq
    exact hr
  · intro hc T hT hne hneq
    rw [mem_powerset] at hT
    obtain ⟨a, ha⟩ := hne
    obtain ⟨b, hbS, hbT⟩ : ∃ b ∈ S, b ∉ T := by
      by_contra hcon
      push Not at hcon
      exact hneq (Subset.antisymm hT hcon)
    obtain ⟨w⟩ := hc.preconnected ⟨a, hT ha⟩ ⟨b, hbS⟩
    exact walk_cross G T w ha hbT

end Conn

/-! ## The graph `H` -/

/-- Adjacency of `H`: `{0,1}` complete to `{2,3,4}`, leaves `5–2`, `6–3`, `7–4`. -/
def hAdjB (i j : Fin 8) : Bool :=
  [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 5), (3, 6), (4, 7)].contains (i.1, j.1) ||
  [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 5), (3, 6), (4, 7)].contains (j.1, i.1)

def H : SimpleGraph (Fin 8) where
  Adj i j := hAdjB i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel H.Adj := fun i j => inferInstanceAs (Decidable (hAdjB i j = true))

theorem H_connected : H.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  have e : ∀ i j : Fin 8, hAdjB i j = true → H.Reachable i j := fun i j h =>
    SimpleGraph.Adj.reachable h
  refine ⟨0, fun j => ?_⟩
  fin_cases j
  · exact SimpleGraph.Reachable.refl _
  · exact (e 0 2 rfl).trans (e 2 1 rfl)
  · exact e 0 2 rfl
  · exact e 0 3 rfl
  · exact e 0 4 rfl
  · exact (e 0 2 rfl).trans (e 2 5 rfl)
  · exact (e 0 3 rfl).trans (e 3 6 rfl)
  · exact (e 0 4 rfl).trans (e 4 7 rfl)

/-! ## Order-invariance of EF1_outer -/

theorem isEF1Outer_comp_strictMono {V : Type*} [DecidableEq V] [Fintype V] {α : Type*}
    [LinearOrder α] (G : SimpleGraph V) (k : ℕ) (f : Finset V → ℕ) {e : ℕ → α}
    (he : StrictMono e) (A : Fin k → Finset V) :
    IsEF1Outer G k (fun _ S => e (f S)) A ↔ IsEF1Outer G k (fun _ => f) A := by
  unfold IsEF1Outer
  simp only [he.le_iff_le]

/-! ## Bitmasks -/

def encB (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : ℕ :=
  cond b0 1 0 + cond b1 2 0 + cond b2 4 0 + cond b3 8 0 + cond b4 16 0 + cond b5 32 0 +
    cond b6 64 0 + cond b7 128 0

/-- Bitmask of a vertex set: bit `i` is set iff `i ∈ S`. -/
def toMask (S : Finset (Fin 8)) : ℕ :=
  encB (decide (0 ∈ S)) (decide (1 ∈ S)) (decide (2 ∈ S)) (decide (3 ∈ S)) (decide (4 ∈ S))
    (decide (5 ∈ S)) (decide (6 ∈ S)) (decide (7 ∈ S))

theorem encB_spec : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, encB b0 b1 b2 b3 b4 b5 b6 b7 < 256 ∧
    ∀ i : Fin 8, (encB b0 b1 b2 b3 b4 b5 b6 b7).testBit i.val =
      ![b0, b1, b2, b3, b4, b5, b6, b7] i := by
  decide +kernel

theorem toMask_lt (S : Finset (Fin 8)) : toMask S < 256 := (encB_spec _ _ _ _ _ _ _ _).1

theorem testBit_toMask (S : Finset (Fin 8)) (i : Fin 8) :
    (toMask S).testBit i.val = decide (i ∈ S) := by
  rw [toMask, (encB_spec _ _ _ _ _ _ _ _).2 i]
  fin_cases i <;> rfl

theorem mask_ext {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (h : ∀ i : Fin 8, a.testBit i.val = b.testBit i.val) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · exact h ⟨i, hi⟩
  · have h8 : 256 ≤ 2 ^ i :=
      (show (256 : ℕ) = 2 ^ 8 from rfl) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

/-- Clear bit `x`. -/
def clr (x : Fin 8) : ℕ := 255 ^^^ 2 ^ x.val

theorem clr_testBit : ∀ x i : Fin 8, (clr x).testBit i.val = decide (i ≠ x) := by decide +kernel

theorem toMask_sdiff (S : Finset (Fin 8)) (x : Fin 8) :
    toMask (S \ {x}) = toMask S &&& clr x := by
  refine mask_ext (toMask_lt _) (lt_of_le_of_lt Nat.and_le_left (toMask_lt _)) fun i => ?_
  rw [Nat.testBit_and, testBit_toMask, testBit_toMask, clr_testBit]
  simp [mem_sdiff]

theorem testBit_255 : ∀ i : Fin 8, (255 : ℕ).testBit i.val = true := by decide +kernel

theorem toMask_compl (S : Finset (Fin 8)) : toMask (univ \ S) = 255 ^^^ toMask S := by
  refine mask_ext (toMask_lt _) (Nat.xor_lt_two_pow (n := 8) (by norm_num) (toMask_lt S))
    fun i => ?_
  rw [Nat.testBit_xor, testBit_toMask, testBit_toMask, testBit_255]
  simp

theorem toMask_empty : toMask ∅ = 0 := rfl

theorem eq_filter_mask (S : Finset (Fin 8)) :
    S = univ.filter (fun i => (toMask S).testBit i.val = true) := by
  ext i
  simp [testBit_toMask]

/-- Number of set bits of `m` with weight `w`. -/
def cntM (w : Fin 8 → Bool) (m : ℕ) : ℕ :=
  (List.finRange 8).countP (fun i => w i && m.testBit i.val)

theorem cnt_hub : ∀ m < 256, ((univ.filter (fun i : Fin 8 => m.testBit i.val = true)).filter
    (fun x => hubW x = true)).card = cntM hubW m := by
  decide +kernel

theorem cnt_all : ∀ m < 256, (univ.filter (fun i : Fin 8 => m.testBit i.val = true)).card =
    cntM (fun _ => true) m := by
  decide +kernel

theorem beta_eq (S : Finset (Fin 8)) : beta S = cntM hubW (toMask S) := by
  have h := cnt_hub (toMask S) (toMask_lt S)
  rw [← eq_filter_mask S] at h
  exact h

theorem card_eq (S : Finset (Fin 8)) : S.card = cntM (fun _ => true) (toMask S) := by
  have h := cnt_all (toMask S) (toMask_lt S)
  rw [← eq_filter_mask S] at h
  exact h

/-! ### Connectivity on bitmasks -/

/-- Neighbourhood mask of the vertices in `r`. -/
def nbrs (r : ℕ) : ℕ :=
  cond (r.testBit 0) 28 0 ||| cond (r.testBit 1) 28 0 ||| cond (r.testBit 2) 35 0 |||
    cond (r.testBit 3) 67 0 ||| cond (r.testBit 4) 131 0 ||| cond (r.testBit 5) 4 0 |||
    cond (r.testBit 6) 8 0 ||| cond (r.testBit 7) 16 0

def stepM (m r : ℕ) : ℕ := r ||| (nbrs r &&& m)

/-- Vertices of `m` reachable inside `m` from its lowest vertex. -/
def reachM (m : ℕ) : ℕ :=
  stepM m (stepM m (stepM m (stepM m (stepM m (stepM m (stepM m (m &&& (256 - m))))))))

def connM (m : ℕ) : Bool := reachM m == m

/-- Separation certificate: the reach set `r` of `m` is a nonempty proper subset of `m` with
no edge to the rest of `m`. -/
def sepB (m : ℕ) : Bool :=
  (List.finRange 8).all (fun i => !(reachM m).testBit i.val || m.testBit i.val) &&
  (List.finRange 8).any (fun i => (reachM m).testBit i.val) &&
  (List.finRange 8).any (fun i => m.testBit i.val && !(reachM m).testBit i.val) &&
  (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
    !((reachM m).testBit i.val && m.testBit j.val && !(reachM m).testBit j.val) || !hAdjB i j))

theorem connM_sepB : ∀ m < 256, connM m = false → sepB m = true := by
  decide +kernel

theorem connM_sep (m : ℕ) (hm : m < 256) (hc : connM m = false) :
    (∀ i : Fin 8, (reachM m).testBit i.val = true → m.testBit i.val = true) ∧
    (∃ i : Fin 8, (reachM m).testBit i.val = true) ∧
    (∃ i : Fin 8, m.testBit i.val = true ∧ (reachM m).testBit i.val = false) ∧
    (∀ i j : Fin 8, (reachM m).testBit i.val = true → m.testBit j.val = true →
      (reachM m).testBit j.val = false → hAdjB i j = false) := by
  have h := connM_sepB m hm hc
  simp only [sepB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_finRange,
    true_and, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun i hi => ?_, h2, ?_, fun i j hi hj hj' => ?_⟩
  · rcases h1 i trivial with h | h
    · rw [hi] at h; exact absurd h (by decide)
    · exact h
  · obtain ⟨i, hi, hi'⟩ := h3
    exact ⟨i, hi, by simpa using hi'⟩
  · rcases h4 i trivial j trivial with h | h
    · simp [hi, hj, hj'] at h
    · exact h

theorem connM_of_conn {S : Finset (Fin 8)} (h : IsConnectedBundle H S) :
    connM (toMask S) = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  obtain ⟨h1, ⟨i0, hi0⟩, ⟨j0, hj0, hj0'⟩, h4⟩ := connM_sep _ (toMask_lt S) hc
  let T : Finset (Fin 8) := univ.filter (fun i => (reachM (toMask S)).testBit i.val = true)
  have hTS : T ⊆ S := fun i hi => by
    have := h1 i (mem_filter.1 hi).2
    rwa [testBit_toMask, decide_eq_true_iff] at this
  have hTne : T ≠ S := by
    intro hTe
    rw [testBit_toMask, decide_eq_true_iff] at hj0
    have : j0 ∈ T := hTe ▸ hj0
    rw [mem_filter] at this
    rw [this.2] at hj0'
    exact Bool.noConfusion hj0'
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    h T (mem_powerset.2 hTS) ⟨i0, mem_filter.2 ⟨mem_univ _, hi0⟩⟩ hTne
  rcases mem_sdiff.1 hy with ⟨hyS, hyT⟩
  have hyT' : (reachM (toMask S)).testBit y.val = false := by
    simpa [T] using hyT
  have := h4 x y (mem_filter.1 hx).2 (by rw [testBit_toMask]; simpa using hyS) hyT'
  change hAdjB x y = true at hxy
  rw [this] at hxy
  exact Bool.noConfusion hxy

/-- EF1_outer of an agent with valuation `beta` holding `a` towards the bundle `c`. -/
def ef1M (a c : ℕ) : Bool :=
  c == 0 || (List.finRange 8).any (fun x => c.testBit x.val && connM (c &&& clr x) &&
    decide (cntM hubW (c &&& clr x) ≤ cntM hubW a))

theorem ef1M_of {Si Sj : Finset (Fin 8)} (h : Sj = ∅ ∨ ∃ x ∈ Sj,
    IsConnectedBundle H (Sj \ {x}) ∧ beta (Sj \ {x}) ≤ beta Si) :
    ef1M (toMask Si) (toMask Sj) = true := by
  rcases h with rfl | ⟨x, hx, hc, hle⟩
  · simp [ef1M, toMask_empty]
  · have hc' := connM_of_conn hc
    rw [beta_eq, beta_eq, toMask_sdiff] at hle
    rw [toMask_sdiff] at hc'
    simp only [ef1M, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨x, List.mem_finRange x, ⟨by rw [testBit_toMask]; simpa using hx, hc'⟩, hle⟩

/-! ## `k = 2` and `k = 4`: no EF1_outer allocation for `beta` -/

theorem no_k2_mask : ∀ m < 256, ¬ (connM m = true ∧ connM (255 ^^^ m) = true ∧
    ef1M m (255 ^^^ m) = true ∧ ef1M (255 ^^^ m) m = true) := by
  decide +kernel

theorem H_no_k2_nat (A : Fin 2 → Finset (Fin 8)) : ¬ IsEF1Outer H 2 (fun _ => beta) A := by
  rintro ⟨⟨hdisj, hcov, hconn⟩, hef⟩
  have hA1 : A 1 = univ \ A 0 := by
    ext x
    simp only [mem_sdiff, mem_univ, true_and]
    constructor
    · intro h1 h0
      exact disjoint_left.1 (hdisj 0 1 (by decide)) h0 h1
    · intro h0
      have : x ∈ univ.biUnion A := hcov ▸ mem_univ x
      obtain ⟨i, -, hi⟩ := mem_biUnion.1 this
      fin_cases i
      · exact absurd hi h0
      · exact hi
  have e01 := ef1M_of (hef 0 1)
  have e10 := ef1M_of (hef 1 0)
  have c0 := connM_of_conn (hconn 0)
  have c1 := connM_of_conn (hconn 1)
  rw [hA1, toMask_compl] at e01 e10 c1
  exact no_k2_mask _ (toMask_lt _) ⟨c0, c1, e01, e10⟩

/-- `beta` has no EF1_outer 2-allocation, for `beta` composed with any strictly monotone map
`ℕ → α` (for instance the casts to `ℕ`, `ℚ`, `ℝ`). -/
theorem H_no_k2 {α : Type*} [LinearOrder α] (e : ℕ → α) (he : StrictMono e)
    (A : Fin 2 → Finset (Fin 8)) : ¬ IsEF1Outer H 2 (fun _ S => e (beta S)) A := fun h =>
  H_no_k2_nat A ((isEF1Outer_comp_strictMono H 2 beta he A).1 h)

/-- A bundle of the zero agent's EF1_outer view has at most one non-hub vertex. -/
theorem k4_bundle : ∀ m < 256, connM m = true → (m == 0 || cntM hubW m == 0 ||
    (List.finRange 8).any (fun x => m.testBit x.val && connM (m &&& clr x) &&
      cntM hubW (m &&& clr x) == 0)) = true →
    cntM (fun _ => true) m ≤ 1 + cntM hubW m := by
  decide +kernel

theorem H_no_k4_nat (A : Fin 4 → Finset (Fin 8)) : ¬ IsEF1Outer H 4 (fun _ => beta) A := by
  rintro ⟨⟨hdisj, hcov, hconn⟩, hef⟩
  have hpw : ((univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint A :=
    fun i _ j _ hij => hdisj i j hij
  have hcard : ∑ i, (A i).card = 8 := by
    rw [← card_biUnion hpw, hcov]
    rfl
  have hbeta : ∑ i, beta (A i) = 3 := by
    have hpw' : ((univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint
        (fun i => (A i).filter (fun x => hubW x = true)) :=
      fun i _ j _ hij => disjoint_filter_filter (hdisj i j hij)
    unfold beta commonBinaryVal
    rw [← card_biUnion hpw', ← filter_biUnion, hcov]
    rfl
  obtain ⟨i0, hi0⟩ : ∃ i0, beta (A i0) = 0 := by
    by_contra hne
    push Not at hne
    have : ∑ _i : Fin 4, 1 ≤ ∑ i, beta (A i) :=
      sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.2 (hne i)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
    omega
  have hb : ∀ j, (A j).card ≤ 1 + beta (A j) := by
    intro j
    rw [card_eq, beta_eq]
    apply k4_bundle _ (toMask_lt _) (connM_of_conn (hconn j))
    rcases hef i0 j with h | ⟨x, hx, hc, hle⟩
    · simp [h, toMask_empty]
    · have hc' := connM_of_conn hc
      have hle' : beta (A j \ {x}) = 0 := by
        have : beta (A j \ {x}) ≤ beta (A i0) := hle
        omega
      rw [beta_eq, toMask_sdiff] at hle'
      rw [toMask_sdiff] at hc'
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact Or.inr ⟨x, List.mem_finRange x, ⟨by rw [testBit_toMask]; simpa using hx, hc'⟩,
        hle'⟩
  have := sum_le_sum (s := univ) (fun j _ => hb j)
  rw [hcard, sum_add_distrib, hbeta] at this
  simp at this

/-- `beta` has no EF1_outer 4-allocation (composed with any strictly monotone `ℕ → α`). -/
theorem H_no_k4 {α : Type*} [LinearOrder α] (e : ℕ → α) (he : StrictMono e)
    (A : Fin 4 → Finset (Fin 8)) : ¬ IsEF1Outer H 4 (fun _ S => e (beta S)) A := fun h =>
  H_no_k4_nat A ((isEF1Outer_comp_strictMono H 4 beta he A).1 h)

/-! ## `k = 3`: from acceptance to EF1_outer -/

/-- An agent with valuation `v` accepts block `b` of the partition `P` if it is EF1_outer towards
every other block. -/
def AccP {α : Type*} [LinearOrder α] (v : Finset (Fin 8) → α) (P : Fin 3 → Finset (Fin 8))
    (b : Fin 3) : Prop :=
  ∀ c, c ≠ b → ∃ x ∈ P c, IsConnectedBundle H (P c \ {x}) ∧ v (P c \ {x}) ≤ v (P b)

/-- If agent `i` accepts block `σ i` of a connected partition, giving agent `i` block `σ i` is
EF1_outer. -/
theorem ef1_of_acc {α : Type*} [LinearOrder α] (P : Fin 3 → Finset (Fin 8))
    (hP : IsConnectedAllocation H 3 P)
    (hout : ∀ c, ∃ x ∈ P c, IsConnectedBundle H (P c \ {x})) (σ : Fin 3 → Fin 3)
    (hσ : Function.Injective σ) (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (hacc : ∀ i, AccP (v i) P (σ i)) :
    IsEF1Outer H 3 v (fun i => P (σ i)) := by
  obtain ⟨hdisj, hcov, hconn⟩ := hP
  have hsurj : Function.Surjective σ := Finite.injective_iff_surjective.1 hσ
  refine ⟨⟨fun i j hij => hdisj _ _ (hσ.ne hij), ?_, fun i => hconn _⟩, fun i j => Or.inr ?_⟩
  · ext x
    simp only [mem_biUnion, mem_univ, true_and, iff_true]
    have : x ∈ univ.biUnion P := hcov ▸ mem_univ x
    obtain ⟨c, -, hc⟩ := mem_biUnion.1 this
    obtain ⟨i, rfl⟩ := hsurj c
    exact ⟨i, hc⟩
  · by_cases hij : i = j
    · subst hij
      obtain ⟨x, hx, hc⟩ := hout (σ i)
      exact ⟨x, hx, hc, hv i _ _ sdiff_subset⟩
    · exact hacc i (σ j) (hσ.ne (Ne.symm hij))

/-! ## `k = 3`, heterogeneous monotone valuations (generated) -/

/-! ### Vertex sets and their connectivity -/

def s0 : Finset (Fin 8) := ∅
def s4 : Finset (Fin 8) := {2}
def s5 : Finset (Fin 8) := {2, 0}
def s6 : Finset (Fin 8) := {2, 1}
def s7 : Finset (Fin 8) := {1, 2, 0}
def s8 : Finset (Fin 8) := {3}
def s9 : Finset (Fin 8) := {3, 0}
def s11 : Finset (Fin 8) := {1, 3, 0}
def s13 : Finset (Fin 8) := {3, 2, 0}
def s15 : Finset (Fin 8) := {1, 3, 2, 0}
def s16 : Finset (Fin 8) := {4}
def s18 : Finset (Fin 8) := {4, 1}
def s19 : Finset (Fin 8) := {1, 4, 0}
def s22 : Finset (Fin 8) := {4, 2, 1}
def s23 : Finset (Fin 8) := {1, 4, 2, 0}
def s25 : Finset (Fin 8) := {4, 3, 0}
def s26 : Finset (Fin 8) := {4, 3, 1}
def s27 : Finset (Fin 8) := {1, 4, 3, 0}
def s32 : Finset (Fin 8) := {5}
def s36 : Finset (Fin 8) := {5, 2}
def s37 : Finset (Fin 8) := {5, 2, 0}
def s38 : Finset (Fin 8) := {5, 2, 1}
def s39 : Finset (Fin 8) := {5, 1, 2, 0}
def s45 : Finset (Fin 8) := {5, 3, 2, 0}
def s46 : Finset (Fin 8) := {5, 3, 2, 1}
def s47 : Finset (Fin 8) := {5, 1, 3, 2, 0}
def s53 : Finset (Fin 8) := {5, 4, 2, 0}
def s54 : Finset (Fin 8) := {5, 4, 2, 1}
def s55 : Finset (Fin 8) := {5, 1, 4, 2, 0}
def s64 : Finset (Fin 8) := {6}
def s72 : Finset (Fin 8) := {6, 3}
def s73 : Finset (Fin 8) := {6, 3, 0}
def s74 : Finset (Fin 8) := {6, 3, 1}
def s75 : Finset (Fin 8) := {6, 1, 3, 0}
def s77 : Finset (Fin 8) := {6, 3, 2, 0}
def s78 : Finset (Fin 8) := {6, 3, 2, 1}
def s79 : Finset (Fin 8) := {6, 1, 3, 2, 0}
def s89 : Finset (Fin 8) := {6, 4, 3, 0}
def s90 : Finset (Fin 8) := {6, 4, 3, 1}
def s91 : Finset (Fin 8) := {6, 1, 4, 3, 0}
def s128 : Finset (Fin 8) := {7}
def s144 : Finset (Fin 8) := {7, 4}
def s145 : Finset (Fin 8) := {7, 4, 0}
def s146 : Finset (Fin 8) := {7, 4, 1}
def s147 : Finset (Fin 8) := {7, 1, 4, 0}
def s149 : Finset (Fin 8) := {7, 4, 2, 0}
def s150 : Finset (Fin 8) := {7, 4, 2, 1}
def s151 : Finset (Fin 8) := {7, 1, 4, 2, 0}
def s153 : Finset (Fin 8) := {7, 4, 3, 0}
def s154 : Finset (Fin 8) := {7, 4, 3, 1}
def s155 : Finset (Fin 8) := {7, 1, 4, 3, 0}

theorem conn_s0 : IsConnectedBundle H s0 := isConnectedBundle_empty H
theorem conn_s4 : IsConnectedBundle H s4 :=
  isConnectedBundle_singleton H 2
theorem conn_s5 : IsConnectedBundle H s5 :=
  isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)
theorem conn_s6 : IsConnectedBundle H s6 :=
  isConnectedBundle_insert 2 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)
theorem conn_s7 : IsConnectedBundle H s7 :=
  isConnectedBundle_insert 1 2 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s8 : IsConnectedBundle H s8 :=
  isConnectedBundle_singleton H 3
theorem conn_s9 : IsConnectedBundle H s9 :=
  isConnectedBundle_insert 3 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)
theorem conn_s11 : IsConnectedBundle H s11 :=
  isConnectedBundle_insert 1 3 (isConnectedBundle_insert 3 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s13 : IsConnectedBundle H s13 :=
  isConnectedBundle_insert 3 0 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s15 : IsConnectedBundle H s15 :=
  isConnectedBundle_insert 1 2 (isConnectedBundle_insert 3 0 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s16 : IsConnectedBundle H s16 :=
  isConnectedBundle_singleton H 4
theorem conn_s18 : IsConnectedBundle H s18 :=
  isConnectedBundle_insert 4 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)
theorem conn_s19 : IsConnectedBundle H s19 :=
  isConnectedBundle_insert 1 4 (isConnectedBundle_insert 4 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s22 : IsConnectedBundle H s22 :=
  isConnectedBundle_insert 4 1 (isConnectedBundle_insert 2 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s23 : IsConnectedBundle H s23 :=
  isConnectedBundle_insert 1 2 (isConnectedBundle_insert 4 0 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s25 : IsConnectedBundle H s25 :=
  isConnectedBundle_insert 4 0 (isConnectedBundle_insert 3 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s26 : IsConnectedBundle H s26 :=
  isConnectedBundle_insert 4 1 (isConnectedBundle_insert 3 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s27 : IsConnectedBundle H s27 :=
  isConnectedBundle_insert 1 3 (isConnectedBundle_insert 4 0 (isConnectedBundle_insert 3 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s32 : IsConnectedBundle H s32 :=
  isConnectedBundle_singleton H 5
theorem conn_s36 : IsConnectedBundle H s36 :=
  isConnectedBundle_insert 5 2 (isConnectedBundle_singleton H 2) (by decide) (by decide) (by decide)
theorem conn_s37 : IsConnectedBundle H s37 :=
  isConnectedBundle_insert 5 2 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s38 : IsConnectedBundle H s38 :=
  isConnectedBundle_insert 5 2 (isConnectedBundle_insert 2 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s39 : IsConnectedBundle H s39 :=
  isConnectedBundle_insert 5 2 (isConnectedBundle_insert 1 2 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s45 : IsConnectedBundle H s45 :=
  isConnectedBundle_insert 5 2 (isConnectedBundle_insert 3 0 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s46 : IsConnectedBundle H s46 :=
  isConnectedBundle_insert 5 2 (isConnectedBundle_insert 3 1 (isConnectedBundle_insert 2 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s47 : IsConnectedBundle H s47 :=
  isConnectedBundle_insert 5 2 (isConnectedBundle_insert 1 2 (isConnectedBundle_insert 3 0 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s53 : IsConnectedBundle H s53 :=
  isConnectedBundle_insert 5 2 (isConnectedBundle_insert 4 0 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s54 : IsConnectedBundle H s54 :=
  isConnectedBundle_insert 5 2 (isConnectedBundle_insert 4 1 (isConnectedBundle_insert 2 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s55 : IsConnectedBundle H s55 :=
  isConnectedBundle_insert 5 2 (isConnectedBundle_insert 1 2 (isConnectedBundle_insert 4 0 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s64 : IsConnectedBundle H s64 :=
  isConnectedBundle_singleton H 6
theorem conn_s72 : IsConnectedBundle H s72 :=
  isConnectedBundle_insert 6 3 (isConnectedBundle_singleton H 3) (by decide) (by decide) (by decide)
theorem conn_s73 : IsConnectedBundle H s73 :=
  isConnectedBundle_insert 6 3 (isConnectedBundle_insert 3 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s74 : IsConnectedBundle H s74 :=
  isConnectedBundle_insert 6 3 (isConnectedBundle_insert 3 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s75 : IsConnectedBundle H s75 :=
  isConnectedBundle_insert 6 3 (isConnectedBundle_insert 1 3 (isConnectedBundle_insert 3 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s77 : IsConnectedBundle H s77 :=
  isConnectedBundle_insert 6 3 (isConnectedBundle_insert 3 0 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s78 : IsConnectedBundle H s78 :=
  isConnectedBundle_insert 6 3 (isConnectedBundle_insert 3 1 (isConnectedBundle_insert 2 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s79 : IsConnectedBundle H s79 :=
  isConnectedBundle_insert 6 3 (isConnectedBundle_insert 1 2 (isConnectedBundle_insert 3 0 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s89 : IsConnectedBundle H s89 :=
  isConnectedBundle_insert 6 3 (isConnectedBundle_insert 4 0 (isConnectedBundle_insert 3 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s90 : IsConnectedBundle H s90 :=
  isConnectedBundle_insert 6 3 (isConnectedBundle_insert 4 1 (isConnectedBundle_insert 3 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s91 : IsConnectedBundle H s91 :=
  isConnectedBundle_insert 6 3 (isConnectedBundle_insert 1 3 (isConnectedBundle_insert 4 0 (isConnectedBundle_insert 3 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s128 : IsConnectedBundle H s128 :=
  isConnectedBundle_singleton H 7
theorem conn_s144 : IsConnectedBundle H s144 :=
  isConnectedBundle_insert 7 4 (isConnectedBundle_singleton H 4) (by decide) (by decide) (by decide)
theorem conn_s145 : IsConnectedBundle H s145 :=
  isConnectedBundle_insert 7 4 (isConnectedBundle_insert 4 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s146 : IsConnectedBundle H s146 :=
  isConnectedBundle_insert 7 4 (isConnectedBundle_insert 4 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s147 : IsConnectedBundle H s147 :=
  isConnectedBundle_insert 7 4 (isConnectedBundle_insert 1 4 (isConnectedBundle_insert 4 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s149 : IsConnectedBundle H s149 :=
  isConnectedBundle_insert 7 4 (isConnectedBundle_insert 4 0 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s150 : IsConnectedBundle H s150 :=
  isConnectedBundle_insert 7 4 (isConnectedBundle_insert 4 1 (isConnectedBundle_insert 2 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s151 : IsConnectedBundle H s151 :=
  isConnectedBundle_insert 7 4 (isConnectedBundle_insert 1 2 (isConnectedBundle_insert 4 0 (isConnectedBundle_insert 2 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s153 : IsConnectedBundle H s153 :=
  isConnectedBundle_insert 7 4 (isConnectedBundle_insert 4 0 (isConnectedBundle_insert 3 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s154 : IsConnectedBundle H s154 :=
  isConnectedBundle_insert 7 4 (isConnectedBundle_insert 4 1 (isConnectedBundle_insert 3 1 (isConnectedBundle_singleton H 1) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
theorem conn_s155 : IsConnectedBundle H s155 :=
  isConnectedBundle_insert 7 4 (isConnectedBundle_insert 1 3 (isConnectedBundle_insert 4 0 (isConnectedBundle_insert 3 0 (isConnectedBundle_singleton H 0) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)

theorem sd_32_5 : s32 \ {5} = s0 := by decide +kernel
theorem rc_32_5 : IsConnectedBundle H (s32 \ {5}) := by rw [sd_32_5]; exact conn_s0
theorem sd_36_2 : s36 \ {2} = s32 := by decide +kernel
theorem rc_36_2 : IsConnectedBundle H (s36 \ {2}) := by rw [sd_36_2]; exact conn_s32
theorem sd_36_5 : s36 \ {5} = s4 := by decide +kernel
theorem rc_36_5 : IsConnectedBundle H (s36 \ {5}) := by rw [sd_36_5]; exact conn_s4
theorem sd_37_0 : s37 \ {0} = s36 := by decide +kernel
theorem rc_37_0 : IsConnectedBundle H (s37 \ {0}) := by rw [sd_37_0]; exact conn_s36
theorem sd_37_5 : s37 \ {5} = s5 := by decide +kernel
theorem rc_37_5 : IsConnectedBundle H (s37 \ {5}) := by rw [sd_37_5]; exact conn_s5
theorem sd_38_1 : s38 \ {1} = s36 := by decide +kernel
theorem rc_38_1 : IsConnectedBundle H (s38 \ {1}) := by rw [sd_38_1]; exact conn_s36
theorem sd_38_5 : s38 \ {5} = s6 := by decide +kernel
theorem rc_38_5 : IsConnectedBundle H (s38 \ {5}) := by rw [sd_38_5]; exact conn_s6
theorem sd_39_0 : s39 \ {0} = s38 := by decide +kernel
theorem rc_39_0 : IsConnectedBundle H (s39 \ {0}) := by rw [sd_39_0]; exact conn_s38
theorem sd_39_1 : s39 \ {1} = s37 := by decide +kernel
theorem rc_39_1 : IsConnectedBundle H (s39 \ {1}) := by rw [sd_39_1]; exact conn_s37
theorem sd_39_5 : s39 \ {5} = s7 := by decide +kernel
theorem rc_39_5 : IsConnectedBundle H (s39 \ {5}) := by rw [sd_39_5]; exact conn_s7
theorem sd_45_3 : s45 \ {3} = s37 := by decide +kernel
theorem rc_45_3 : IsConnectedBundle H (s45 \ {3}) := by rw [sd_45_3]; exact conn_s37
theorem sd_45_5 : s45 \ {5} = s13 := by decide +kernel
theorem rc_45_5 : IsConnectedBundle H (s45 \ {5}) := by rw [sd_45_5]; exact conn_s13
theorem sd_47_0 : s47 \ {0} = s46 := by decide +kernel
theorem rc_47_0 : IsConnectedBundle H (s47 \ {0}) := by rw [sd_47_0]; exact conn_s46
theorem sd_47_1 : s47 \ {1} = s45 := by decide +kernel
theorem rc_47_1 : IsConnectedBundle H (s47 \ {1}) := by rw [sd_47_1]; exact conn_s45
theorem sd_47_3 : s47 \ {3} = s39 := by decide +kernel
theorem rc_47_3 : IsConnectedBundle H (s47 \ {3}) := by rw [sd_47_3]; exact conn_s39
theorem sd_47_5 : s47 \ {5} = s15 := by decide +kernel
theorem rc_47_5 : IsConnectedBundle H (s47 \ {5}) := by rw [sd_47_5]; exact conn_s15
theorem sd_54_4 : s54 \ {4} = s38 := by decide +kernel
theorem rc_54_4 : IsConnectedBundle H (s54 \ {4}) := by rw [sd_54_4]; exact conn_s38
theorem sd_54_5 : s54 \ {5} = s22 := by decide +kernel
theorem rc_54_5 : IsConnectedBundle H (s54 \ {5}) := by rw [sd_54_5]; exact conn_s22
theorem sd_55_0 : s55 \ {0} = s54 := by decide +kernel
theorem rc_55_0 : IsConnectedBundle H (s55 \ {0}) := by rw [sd_55_0]; exact conn_s54
theorem sd_55_1 : s55 \ {1} = s53 := by decide +kernel
theorem rc_55_1 : IsConnectedBundle H (s55 \ {1}) := by rw [sd_55_1]; exact conn_s53
theorem sd_55_4 : s55 \ {4} = s39 := by decide +kernel
theorem rc_55_4 : IsConnectedBundle H (s55 \ {4}) := by rw [sd_55_4]; exact conn_s39
theorem sd_55_5 : s55 \ {5} = s23 := by decide +kernel
theorem rc_55_5 : IsConnectedBundle H (s55 \ {5}) := by rw [sd_55_5]; exact conn_s23
theorem sd_64_6 : s64 \ {6} = s0 := by decide +kernel
theorem rc_64_6 : IsConnectedBundle H (s64 \ {6}) := by rw [sd_64_6]; exact conn_s0
theorem sd_72_3 : s72 \ {3} = s64 := by decide +kernel
theorem rc_72_3 : IsConnectedBundle H (s72 \ {3}) := by rw [sd_72_3]; exact conn_s64
theorem sd_72_6 : s72 \ {6} = s8 := by decide +kernel
theorem rc_72_6 : IsConnectedBundle H (s72 \ {6}) := by rw [sd_72_6]; exact conn_s8
theorem sd_73_0 : s73 \ {0} = s72 := by decide +kernel
theorem rc_73_0 : IsConnectedBundle H (s73 \ {0}) := by rw [sd_73_0]; exact conn_s72
theorem sd_73_6 : s73 \ {6} = s9 := by decide +kernel
theorem rc_73_6 : IsConnectedBundle H (s73 \ {6}) := by rw [sd_73_6]; exact conn_s9
theorem sd_75_0 : s75 \ {0} = s74 := by decide +kernel
theorem rc_75_0 : IsConnectedBundle H (s75 \ {0}) := by rw [sd_75_0]; exact conn_s74
theorem sd_75_1 : s75 \ {1} = s73 := by decide +kernel
theorem rc_75_1 : IsConnectedBundle H (s75 \ {1}) := by rw [sd_75_1]; exact conn_s73
theorem sd_75_6 : s75 \ {6} = s11 := by decide +kernel
theorem rc_75_6 : IsConnectedBundle H (s75 \ {6}) := by rw [sd_75_6]; exact conn_s11
theorem sd_77_2 : s77 \ {2} = s73 := by decide +kernel
theorem rc_77_2 : IsConnectedBundle H (s77 \ {2}) := by rw [sd_77_2]; exact conn_s73
theorem sd_77_6 : s77 \ {6} = s13 := by decide +kernel
theorem rc_77_6 : IsConnectedBundle H (s77 \ {6}) := by rw [sd_77_6]; exact conn_s13
theorem sd_79_0 : s79 \ {0} = s78 := by decide +kernel
theorem rc_79_0 : IsConnectedBundle H (s79 \ {0}) := by rw [sd_79_0]; exact conn_s78
theorem sd_79_1 : s79 \ {1} = s77 := by decide +kernel
theorem rc_79_1 : IsConnectedBundle H (s79 \ {1}) := by rw [sd_79_1]; exact conn_s77
theorem sd_79_2 : s79 \ {2} = s75 := by decide +kernel
theorem rc_79_2 : IsConnectedBundle H (s79 \ {2}) := by rw [sd_79_2]; exact conn_s75
theorem sd_79_6 : s79 \ {6} = s15 := by decide +kernel
theorem rc_79_6 : IsConnectedBundle H (s79 \ {6}) := by rw [sd_79_6]; exact conn_s15
theorem sd_89_4 : s89 \ {4} = s73 := by decide +kernel
theorem rc_89_4 : IsConnectedBundle H (s89 \ {4}) := by rw [sd_89_4]; exact conn_s73
theorem sd_89_6 : s89 \ {6} = s25 := by decide +kernel
theorem rc_89_6 : IsConnectedBundle H (s89 \ {6}) := by rw [sd_89_6]; exact conn_s25
theorem sd_91_0 : s91 \ {0} = s90 := by decide +kernel
theorem rc_91_0 : IsConnectedBundle H (s91 \ {0}) := by rw [sd_91_0]; exact conn_s90
theorem sd_91_1 : s91 \ {1} = s89 := by decide +kernel
theorem rc_91_1 : IsConnectedBundle H (s91 \ {1}) := by rw [sd_91_1]; exact conn_s89
theorem sd_91_4 : s91 \ {4} = s75 := by decide +kernel
theorem rc_91_4 : IsConnectedBundle H (s91 \ {4}) := by rw [sd_91_4]; exact conn_s75
theorem sd_91_6 : s91 \ {6} = s27 := by decide +kernel
theorem rc_91_6 : IsConnectedBundle H (s91 \ {6}) := by rw [sd_91_6]; exact conn_s27
theorem sd_128_7 : s128 \ {7} = s0 := by decide +kernel
theorem rc_128_7 : IsConnectedBundle H (s128 \ {7}) := by rw [sd_128_7]; exact conn_s0
theorem sd_144_4 : s144 \ {4} = s128 := by decide +kernel
theorem rc_144_4 : IsConnectedBundle H (s144 \ {4}) := by rw [sd_144_4]; exact conn_s128
theorem sd_144_7 : s144 \ {7} = s16 := by decide +kernel
theorem rc_144_7 : IsConnectedBundle H (s144 \ {7}) := by rw [sd_144_7]; exact conn_s16
theorem sd_146_1 : s146 \ {1} = s144 := by decide +kernel
theorem rc_146_1 : IsConnectedBundle H (s146 \ {1}) := by rw [sd_146_1]; exact conn_s144
theorem sd_146_7 : s146 \ {7} = s18 := by decide +kernel
theorem rc_146_7 : IsConnectedBundle H (s146 \ {7}) := by rw [sd_146_7]; exact conn_s18
theorem sd_147_0 : s147 \ {0} = s146 := by decide +kernel
theorem rc_147_0 : IsConnectedBundle H (s147 \ {0}) := by rw [sd_147_0]; exact conn_s146
theorem sd_147_1 : s147 \ {1} = s145 := by decide +kernel
theorem rc_147_1 : IsConnectedBundle H (s147 \ {1}) := by rw [sd_147_1]; exact conn_s145
theorem sd_147_7 : s147 \ {7} = s19 := by decide +kernel
theorem rc_147_7 : IsConnectedBundle H (s147 \ {7}) := by rw [sd_147_7]; exact conn_s19
theorem sd_150_2 : s150 \ {2} = s146 := by decide +kernel
theorem rc_150_2 : IsConnectedBundle H (s150 \ {2}) := by rw [sd_150_2]; exact conn_s146
theorem sd_150_7 : s150 \ {7} = s22 := by decide +kernel
theorem rc_150_7 : IsConnectedBundle H (s150 \ {7}) := by rw [sd_150_7]; exact conn_s22
theorem sd_151_0 : s151 \ {0} = s150 := by decide +kernel
theorem rc_151_0 : IsConnectedBundle H (s151 \ {0}) := by rw [sd_151_0]; exact conn_s150
theorem sd_151_1 : s151 \ {1} = s149 := by decide +kernel
theorem rc_151_1 : IsConnectedBundle H (s151 \ {1}) := by rw [sd_151_1]; exact conn_s149
theorem sd_151_2 : s151 \ {2} = s147 := by decide +kernel
theorem rc_151_2 : IsConnectedBundle H (s151 \ {2}) := by rw [sd_151_2]; exact conn_s147
theorem sd_151_7 : s151 \ {7} = s23 := by decide +kernel
theorem rc_151_7 : IsConnectedBundle H (s151 \ {7}) := by rw [sd_151_7]; exact conn_s23
theorem sd_154_3 : s154 \ {3} = s146 := by decide +kernel
theorem rc_154_3 : IsConnectedBundle H (s154 \ {3}) := by rw [sd_154_3]; exact conn_s146
theorem sd_154_7 : s154 \ {7} = s26 := by decide +kernel
theorem rc_154_7 : IsConnectedBundle H (s154 \ {7}) := by rw [sd_154_7]; exact conn_s26
theorem sd_155_0 : s155 \ {0} = s154 := by decide +kernel
theorem rc_155_0 : IsConnectedBundle H (s155 \ {0}) := by rw [sd_155_0]; exact conn_s154
theorem sd_155_1 : s155 \ {1} = s153 := by decide +kernel
theorem rc_155_1 : IsConnectedBundle H (s155 \ {1}) := by rw [sd_155_1]; exact conn_s153
theorem sd_155_3 : s155 \ {3} = s147 := by decide +kernel
theorem rc_155_3 : IsConnectedBundle H (s155 \ {3}) := by rw [sd_155_3]; exact conn_s147
theorem sd_155_7 : s155 \ {7} = s27 := by decide +kernel
theorem rc_155_7 : IsConnectedBundle H (s155 \ {7}) := by rw [sd_155_7]; exact conn_s27

/-! ### Partitions -/

def P0 : Fin 3 → Finset (Fin 8) := ![s155, s36, s64]
theorem alloc0 : IsConnectedAllocation H 3 P0 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s155, conn_s36, conn_s64]⟩
theorem out0 : ∀ c, ∃ x ∈ P0 c, IsConnectedBundle H (P0 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_155_0⟩, ⟨2, by decide, rc_36_2⟩, ⟨6, by decide, rc_64_6⟩]
def P1 : Fin 3 → Finset (Fin 8) := ![s151, s72, s32]
theorem alloc1 : IsConnectedAllocation H 3 P1 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s151, conn_s72, conn_s32]⟩
theorem out1 : ∀ c, ∃ x ∈ P1 c, IsConnectedBundle H (P1 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_151_0⟩, ⟨3, by decide, rc_72_3⟩, ⟨5, by decide, rc_32_5⟩]
def P2 : Fin 3 → Finset (Fin 8) := ![s147, s36, s72]
theorem alloc2 : IsConnectedAllocation H 3 P2 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s147, conn_s36, conn_s72]⟩
theorem out2 : ∀ c, ∃ x ∈ P2 c, IsConnectedBundle H (P2 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_147_0⟩, ⟨2, by decide, rc_36_2⟩, ⟨3, by decide, rc_72_3⟩]
def P3 : Fin 3 → Finset (Fin 8) := ![s91, s36, s128]
theorem alloc3 : IsConnectedAllocation H 3 P3 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s91, conn_s36, conn_s128]⟩
theorem out3 : ∀ c, ∃ x ∈ P3 c, IsConnectedBundle H (P3 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_91_0⟩, ⟨2, by decide, rc_36_2⟩, ⟨7, by decide, rc_128_7⟩]
def P4 : Fin 3 → Finset (Fin 8) := ![s89, s38, s128]
theorem alloc4 : IsConnectedAllocation H 3 P4 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s89, conn_s38, conn_s128]⟩
theorem out4 : ∀ c, ∃ x ∈ P4 c, IsConnectedBundle H (P4 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨4, by decide, rc_89_4⟩, ⟨1, by decide, rc_38_1⟩, ⟨7, by decide, rc_128_7⟩]
def P5 : Fin 3 → Finset (Fin 8) := ![s79, s144, s32]
theorem alloc5 : IsConnectedAllocation H 3 P5 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s79, conn_s144, conn_s32]⟩
theorem out5 : ∀ c, ∃ x ∈ P5 c, IsConnectedBundle H (P5 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_79_0⟩, ⟨4, by decide, rc_144_4⟩, ⟨5, by decide, rc_32_5⟩]
def P6 : Fin 3 → Finset (Fin 8) := ![s77, s146, s32]
theorem alloc6 : IsConnectedAllocation H 3 P6 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s77, conn_s146, conn_s32]⟩
theorem out6 : ∀ c, ∃ x ∈ P6 c, IsConnectedBundle H (P6 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨2, by decide, rc_77_2⟩, ⟨1, by decide, rc_146_1⟩, ⟨5, by decide, rc_32_5⟩]
def P7 : Fin 3 → Finset (Fin 8) := ![s75, s36, s144]
theorem alloc7 : IsConnectedAllocation H 3 P7 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s75, conn_s36, conn_s144]⟩
theorem out7 : ∀ c, ∃ x ∈ P7 c, IsConnectedBundle H (P7 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_75_0⟩, ⟨2, by decide, rc_36_2⟩, ⟨4, by decide, rc_144_4⟩]
def P8 : Fin 3 → Finset (Fin 8) := ![s73, s150, s32]
theorem alloc8 : IsConnectedAllocation H 3 P8 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s73, conn_s150, conn_s32]⟩
theorem out8 : ∀ c, ∃ x ∈ P8 c, IsConnectedBundle H (P8 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_73_0⟩, ⟨2, by decide, rc_150_2⟩, ⟨5, by decide, rc_32_5⟩]
def P9 : Fin 3 → Finset (Fin 8) := ![s73, s146, s36]
theorem alloc9 : IsConnectedAllocation H 3 P9 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s73, conn_s146, conn_s36]⟩
theorem out9 : ∀ c, ∃ x ∈ P9 c, IsConnectedBundle H (P9 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_73_0⟩, ⟨1, by decide, rc_146_1⟩, ⟨2, by decide, rc_36_2⟩]
def P10 : Fin 3 → Finset (Fin 8) := ![s73, s54, s128]
theorem alloc10 : IsConnectedAllocation H 3 P10 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s73, conn_s54, conn_s128]⟩
theorem out10 : ∀ c, ∃ x ∈ P10 c, IsConnectedBundle H (P10 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_73_0⟩, ⟨4, by decide, rc_54_4⟩, ⟨7, by decide, rc_128_7⟩]
def P11 : Fin 3 → Finset (Fin 8) := ![s73, s38, s144]
theorem alloc11 : IsConnectedAllocation H 3 P11 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s73, conn_s38, conn_s144]⟩
theorem out11 : ∀ c, ∃ x ∈ P11 c, IsConnectedBundle H (P11 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_73_0⟩, ⟨1, by decide, rc_38_1⟩, ⟨4, by decide, rc_144_4⟩]
def P12 : Fin 3 → Finset (Fin 8) := ![s55, s72, s128]
theorem alloc12 : IsConnectedAllocation H 3 P12 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s55, conn_s72, conn_s128]⟩
theorem out12 : ∀ c, ∃ x ∈ P12 c, IsConnectedBundle H (P12 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_55_0⟩, ⟨3, by decide, rc_72_3⟩, ⟨7, by decide, rc_128_7⟩]
def P13 : Fin 3 → Finset (Fin 8) := ![s47, s144, s64]
theorem alloc13 : IsConnectedAllocation H 3 P13 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s47, conn_s144, conn_s64]⟩
theorem out13 : ∀ c, ∃ x ∈ P13 c, IsConnectedBundle H (P13 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_47_0⟩, ⟨4, by decide, rc_144_4⟩, ⟨6, by decide, rc_64_6⟩]
def P14 : Fin 3 → Finset (Fin 8) := ![s45, s146, s64]
theorem alloc14 : IsConnectedAllocation H 3 P14 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s45, conn_s146, conn_s64]⟩
theorem out14 : ∀ c, ∃ x ∈ P14 c, IsConnectedBundle H (P14 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨3, by decide, rc_45_3⟩, ⟨1, by decide, rc_146_1⟩, ⟨6, by decide, rc_64_6⟩]
def P15 : Fin 3 → Finset (Fin 8) := ![s39, s72, s144]
theorem alloc15 : IsConnectedAllocation H 3 P15 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s39, conn_s72, conn_s144]⟩
theorem out15 : ∀ c, ∃ x ∈ P15 c, IsConnectedBundle H (P15 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_39_0⟩, ⟨3, by decide, rc_72_3⟩, ⟨4, by decide, rc_144_4⟩]
def P16 : Fin 3 → Finset (Fin 8) := ![s37, s154, s64]
theorem alloc16 : IsConnectedAllocation H 3 P16 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s37, conn_s154, conn_s64]⟩
theorem out16 : ∀ c, ∃ x ∈ P16 c, IsConnectedBundle H (P16 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_37_0⟩, ⟨3, by decide, rc_154_3⟩, ⟨6, by decide, rc_64_6⟩]
def P17 : Fin 3 → Finset (Fin 8) := ![s37, s146, s72]
theorem alloc17 : IsConnectedAllocation H 3 P17 :=
  ⟨by decide +kernel, by decide +kernel, fun i => by
    fin_cases i
    exacts [conn_s37, conn_s146, conn_s72]⟩
theorem out17 : ∀ c, ∃ x ∈ P17 c, IsConnectedBundle H (P17 c \ {x}) := by
  intro c
  fin_cases c
  exacts [⟨0, by decide, rc_37_0⟩, ⟨1, by decide, rc_146_1⟩, ⟨3, by decide, rc_72_3⟩]

theorem sub_0_36 : s0 ⊆ s36 := by decide +kernel
theorem sub_0_37 : s0 ⊆ s37 := by decide +kernel
theorem sub_0_38 : s0 ⊆ s38 := by decide +kernel
theorem sub_0_45 : s0 ⊆ s45 := by decide +kernel
theorem sub_0_47 : s0 ⊆ s47 := by decide +kernel
theorem sub_0_54 : s0 ⊆ s54 := by decide +kernel
theorem sub_0_55 : s0 ⊆ s55 := by decide +kernel
theorem sub_0_72 : s0 ⊆ s72 := by decide +kernel
theorem sub_0_73 : s0 ⊆ s73 := by decide +kernel
theorem sub_0_77 : s0 ⊆ s77 := by decide +kernel
theorem sub_0_79 : s0 ⊆ s79 := by decide +kernel
theorem sub_0_89 : s0 ⊆ s89 := by decide +kernel
theorem sub_0_91 : s0 ⊆ s91 := by decide +kernel
theorem sub_0_144 : s0 ⊆ s144 := by decide +kernel
theorem sub_0_146 : s0 ⊆ s146 := by decide +kernel
theorem sub_0_150 : s0 ⊆ s150 := by decide +kernel
theorem sub_0_151 : s0 ⊆ s151 := by decide +kernel
theorem sub_0_154 : s0 ⊆ s154 := by decide +kernel
theorem sub_0_155 : s0 ⊆ s155 := by decide +kernel
theorem sub_4_5 : s4 ⊆ s5 := by decide +kernel
theorem sub_4_6 : s4 ⊆ s6 := by decide +kernel
theorem sub_4_7 : s4 ⊆ s7 := by decide +kernel
theorem sub_4_13 : s4 ⊆ s13 := by decide +kernel
theorem sub_4_22 : s4 ⊆ s22 := by decide +kernel
theorem sub_4_23 : s4 ⊆ s23 := by decide +kernel
theorem sub_4_36 : s4 ⊆ s36 := by decide +kernel
theorem sub_4_37 : s4 ⊆ s37 := by decide +kernel
theorem sub_4_38 : s4 ⊆ s38 := by decide +kernel
theorem sub_4_39 : s4 ⊆ s39 := by decide +kernel
theorem sub_4_45 : s4 ⊆ s45 := by decide +kernel
theorem sub_4_47 : s4 ⊆ s47 := by decide +kernel
theorem sub_4_54 : s4 ⊆ s54 := by decide +kernel
theorem sub_4_55 : s4 ⊆ s55 := by decide +kernel
theorem sub_4_77 : s4 ⊆ s77 := by decide +kernel
theorem sub_4_79 : s4 ⊆ s79 := by decide +kernel
theorem sub_4_149 : s4 ⊆ s149 := by decide +kernel
theorem sub_4_150 : s4 ⊆ s150 := by decide +kernel
theorem sub_4_151 : s4 ⊆ s151 := by decide +kernel
theorem sub_5_7 : s5 ⊆ s7 := by decide +kernel
theorem sub_5_13 : s5 ⊆ s13 := by decide +kernel
theorem sub_5_23 : s5 ⊆ s23 := by decide +kernel
theorem sub_5_37 : s5 ⊆ s37 := by decide +kernel
theorem sub_5_39 : s5 ⊆ s39 := by decide +kernel
theorem sub_5_45 : s5 ⊆ s45 := by decide +kernel
theorem sub_5_47 : s5 ⊆ s47 := by decide +kernel
theorem sub_5_53 : s5 ⊆ s53 := by decide +kernel
theorem sub_5_55 : s5 ⊆ s55 := by decide +kernel
theorem sub_5_77 : s5 ⊆ s77 := by decide +kernel
theorem sub_5_151 : s5 ⊆ s151 := by decide +kernel
theorem sub_6_7 : s6 ⊆ s7 := by decide +kernel
theorem sub_6_22 : s6 ⊆ s22 := by decide +kernel
theorem sub_6_38 : s6 ⊆ s38 := by decide +kernel
theorem sub_6_47 : s6 ⊆ s47 := by decide +kernel
theorem sub_6_54 : s6 ⊆ s54 := by decide +kernel
theorem sub_6_55 : s6 ⊆ s55 := by decide +kernel
theorem sub_6_79 : s6 ⊆ s79 := by decide +kernel
theorem sub_6_150 : s6 ⊆ s150 := by decide +kernel
theorem sub_7_23 : s7 ⊆ s23 := by decide +kernel
theorem sub_7_39 : s7 ⊆ s39 := by decide +kernel
theorem sub_7_47 : s7 ⊆ s47 := by decide +kernel
theorem sub_7_55 : s7 ⊆ s55 := by decide +kernel
theorem sub_7_79 : s7 ⊆ s79 := by decide +kernel
theorem sub_7_151 : s7 ⊆ s151 := by decide +kernel
theorem sub_8_9 : s8 ⊆ s9 := by decide +kernel
theorem sub_8_11 : s8 ⊆ s11 := by decide +kernel
theorem sub_8_13 : s8 ⊆ s13 := by decide +kernel
theorem sub_8_25 : s8 ⊆ s25 := by decide +kernel
theorem sub_8_26 : s8 ⊆ s26 := by decide +kernel
theorem sub_8_27 : s8 ⊆ s27 := by decide +kernel
theorem sub_8_45 : s8 ⊆ s45 := by decide +kernel
theorem sub_8_47 : s8 ⊆ s47 := by decide +kernel
theorem sub_8_72 : s8 ⊆ s72 := by decide +kernel
theorem sub_8_73 : s8 ⊆ s73 := by decide +kernel
theorem sub_8_75 : s8 ⊆ s75 := by decide +kernel
theorem sub_8_77 : s8 ⊆ s77 := by decide +kernel
theorem sub_8_79 : s8 ⊆ s79 := by decide +kernel
theorem sub_8_89 : s8 ⊆ s89 := by decide +kernel
theorem sub_8_90 : s8 ⊆ s90 := by decide +kernel
theorem sub_8_91 : s8 ⊆ s91 := by decide +kernel
theorem sub_8_153 : s8 ⊆ s153 := by decide +kernel
theorem sub_8_154 : s8 ⊆ s154 := by decide +kernel
theorem sub_8_155 : s8 ⊆ s155 := by decide +kernel
theorem sub_9_11 : s9 ⊆ s11 := by decide +kernel
theorem sub_9_13 : s9 ⊆ s13 := by decide +kernel
theorem sub_9_25 : s9 ⊆ s25 := by decide +kernel
theorem sub_9_27 : s9 ⊆ s27 := by decide +kernel
theorem sub_9_45 : s9 ⊆ s45 := by decide +kernel
theorem sub_9_47 : s9 ⊆ s47 := by decide +kernel
theorem sub_9_73 : s9 ⊆ s73 := by decide +kernel
theorem sub_9_75 : s9 ⊆ s75 := by decide +kernel
theorem sub_9_77 : s9 ⊆ s77 := by decide +kernel
theorem sub_9_79 : s9 ⊆ s79 := by decide +kernel
theorem sub_9_89 : s9 ⊆ s89 := by decide +kernel
theorem sub_9_91 : s9 ⊆ s91 := by decide +kernel
theorem sub_9_155 : s9 ⊆ s155 := by decide +kernel
theorem sub_11_15 : s11 ⊆ s15 := by decide +kernel
theorem sub_11_27 : s11 ⊆ s27 := by decide +kernel
theorem sub_11_47 : s11 ⊆ s47 := by decide +kernel
theorem sub_11_75 : s11 ⊆ s75 := by decide +kernel
theorem sub_11_79 : s11 ⊆ s79 := by decide +kernel
theorem sub_11_91 : s11 ⊆ s91 := by decide +kernel
theorem sub_11_155 : s11 ⊆ s155 := by decide +kernel
theorem sub_13_45 : s13 ⊆ s45 := by decide +kernel
theorem sub_13_47 : s13 ⊆ s47 := by decide +kernel
theorem sub_13_77 : s13 ⊆ s77 := by decide +kernel
theorem sub_13_79 : s13 ⊆ s79 := by decide +kernel
theorem sub_15_47 : s15 ⊆ s47 := by decide +kernel
theorem sub_15_79 : s15 ⊆ s79 := by decide +kernel
theorem sub_16_18 : s16 ⊆ s18 := by decide +kernel
theorem sub_16_19 : s16 ⊆ s19 := by decide +kernel
theorem sub_16_22 : s16 ⊆ s22 := by decide +kernel
theorem sub_16_23 : s16 ⊆ s23 := by decide +kernel
theorem sub_16_54 : s16 ⊆ s54 := by decide +kernel
theorem sub_16_55 : s16 ⊆ s55 := by decide +kernel
theorem sub_16_89 : s16 ⊆ s89 := by decide +kernel
theorem sub_16_90 : s16 ⊆ s90 := by decide +kernel
theorem sub_16_91 : s16 ⊆ s91 := by decide +kernel
theorem sub_16_144 : s16 ⊆ s144 := by decide +kernel
theorem sub_16_146 : s16 ⊆ s146 := by decide +kernel
theorem sub_16_147 : s16 ⊆ s147 := by decide +kernel
theorem sub_16_150 : s16 ⊆ s150 := by decide +kernel
theorem sub_16_151 : s16 ⊆ s151 := by decide +kernel
theorem sub_16_154 : s16 ⊆ s154 := by decide +kernel
theorem sub_16_155 : s16 ⊆ s155 := by decide +kernel
theorem sub_18_19 : s18 ⊆ s19 := by decide +kernel
theorem sub_18_22 : s18 ⊆ s22 := by decide +kernel
theorem sub_18_23 : s18 ⊆ s23 := by decide +kernel
theorem sub_18_26 : s18 ⊆ s26 := by decide +kernel
theorem sub_18_27 : s18 ⊆ s27 := by decide +kernel
theorem sub_18_54 : s18 ⊆ s54 := by decide +kernel
theorem sub_18_55 : s18 ⊆ s55 := by decide +kernel
theorem sub_18_90 : s18 ⊆ s90 := by decide +kernel
theorem sub_18_91 : s18 ⊆ s91 := by decide +kernel
theorem sub_18_146 : s18 ⊆ s146 := by decide +kernel
theorem sub_18_147 : s18 ⊆ s147 := by decide +kernel
theorem sub_18_150 : s18 ⊆ s150 := by decide +kernel
theorem sub_18_151 : s18 ⊆ s151 := by decide +kernel
theorem sub_18_154 : s18 ⊆ s154 := by decide +kernel
theorem sub_18_155 : s18 ⊆ s155 := by decide +kernel
theorem sub_19_23 : s19 ⊆ s23 := by decide +kernel
theorem sub_19_55 : s19 ⊆ s55 := by decide +kernel
theorem sub_19_91 : s19 ⊆ s91 := by decide +kernel
theorem sub_19_147 : s19 ⊆ s147 := by decide +kernel
theorem sub_19_151 : s19 ⊆ s151 := by decide +kernel
theorem sub_19_155 : s19 ⊆ s155 := by decide +kernel
theorem sub_22_54 : s22 ⊆ s54 := by decide +kernel
theorem sub_22_150 : s22 ⊆ s150 := by decide +kernel
theorem sub_22_151 : s22 ⊆ s151 := by decide +kernel
theorem sub_23_55 : s23 ⊆ s55 := by decide +kernel
theorem sub_23_151 : s23 ⊆ s151 := by decide +kernel
theorem sub_25_27 : s25 ⊆ s27 := by decide +kernel
theorem sub_25_89 : s25 ⊆ s89 := by decide +kernel
theorem sub_25_91 : s25 ⊆ s91 := by decide +kernel
theorem sub_26_154 : s26 ⊆ s154 := by decide +kernel
theorem sub_26_155 : s26 ⊆ s155 := by decide +kernel
theorem sub_27_91 : s27 ⊆ s91 := by decide +kernel
theorem sub_27_155 : s27 ⊆ s155 := by decide +kernel
theorem sub_32_36 : s32 ⊆ s36 := by decide +kernel
theorem sub_32_37 : s32 ⊆ s37 := by decide +kernel
theorem sub_32_38 : s32 ⊆ s38 := by decide +kernel
theorem sub_32_39 : s32 ⊆ s39 := by decide +kernel
theorem sub_32_45 : s32 ⊆ s45 := by decide +kernel
theorem sub_32_47 : s32 ⊆ s47 := by decide +kernel
theorem sub_32_53 : s32 ⊆ s53 := by decide +kernel
theorem sub_32_54 : s32 ⊆ s54 := by decide +kernel
theorem sub_32_55 : s32 ⊆ s55 := by decide +kernel
theorem sub_36_37 : s36 ⊆ s37 := by decide +kernel
theorem sub_36_38 : s36 ⊆ s38 := by decide +kernel
theorem sub_36_39 : s36 ⊆ s39 := by decide +kernel
theorem sub_36_45 : s36 ⊆ s45 := by decide +kernel
theorem sub_36_47 : s36 ⊆ s47 := by decide +kernel
theorem sub_36_53 : s36 ⊆ s53 := by decide +kernel
theorem sub_36_54 : s36 ⊆ s54 := by decide +kernel
theorem sub_36_55 : s36 ⊆ s55 := by decide +kernel
theorem sub_37_39 : s37 ⊆ s39 := by decide +kernel
theorem sub_37_45 : s37 ⊆ s45 := by decide +kernel
theorem sub_37_47 : s37 ⊆ s47 := by decide +kernel
theorem sub_37_53 : s37 ⊆ s53 := by decide +kernel
theorem sub_37_55 : s37 ⊆ s55 := by decide +kernel
theorem sub_38_39 : s38 ⊆ s39 := by decide +kernel
theorem sub_38_47 : s38 ⊆ s47 := by decide +kernel
theorem sub_38_54 : s38 ⊆ s54 := by decide +kernel
theorem sub_38_55 : s38 ⊆ s55 := by decide +kernel
theorem sub_39_47 : s39 ⊆ s47 := by decide +kernel
theorem sub_39_55 : s39 ⊆ s55 := by decide +kernel
theorem sub_53_55 : s53 ⊆ s55 := by decide +kernel
theorem sub_54_55 : s54 ⊆ s55 := by decide +kernel
theorem sub_64_72 : s64 ⊆ s72 := by decide +kernel
theorem sub_64_73 : s64 ⊆ s73 := by decide +kernel
theorem sub_64_74 : s64 ⊆ s74 := by decide +kernel
theorem sub_64_75 : s64 ⊆ s75 := by decide +kernel
theorem sub_64_77 : s64 ⊆ s77 := by decide +kernel
theorem sub_64_79 : s64 ⊆ s79 := by decide +kernel
theorem sub_64_89 : s64 ⊆ s89 := by decide +kernel
theorem sub_64_90 : s64 ⊆ s90 := by decide +kernel
theorem sub_64_91 : s64 ⊆ s91 := by decide +kernel
theorem sub_72_73 : s72 ⊆ s73 := by decide +kernel
theorem sub_72_74 : s72 ⊆ s74 := by decide +kernel
theorem sub_72_75 : s72 ⊆ s75 := by decide +kernel
theorem sub_72_77 : s72 ⊆ s77 := by decide +kernel
theorem sub_72_79 : s72 ⊆ s79 := by decide +kernel
theorem sub_72_89 : s72 ⊆ s89 := by decide +kernel
theorem sub_72_90 : s72 ⊆ s90 := by decide +kernel
theorem sub_72_91 : s72 ⊆ s91 := by decide +kernel
theorem sub_73_75 : s73 ⊆ s75 := by decide +kernel
theorem sub_73_77 : s73 ⊆ s77 := by decide +kernel
theorem sub_73_79 : s73 ⊆ s79 := by decide +kernel
theorem sub_73_89 : s73 ⊆ s89 := by decide +kernel
theorem sub_73_91 : s73 ⊆ s91 := by decide +kernel
theorem sub_74_75 : s74 ⊆ s75 := by decide +kernel
theorem sub_74_78 : s74 ⊆ s78 := by decide +kernel
theorem sub_74_79 : s74 ⊆ s79 := by decide +kernel
theorem sub_74_90 : s74 ⊆ s90 := by decide +kernel
theorem sub_74_91 : s74 ⊆ s91 := by decide +kernel
theorem sub_75_79 : s75 ⊆ s79 := by decide +kernel
theorem sub_75_91 : s75 ⊆ s91 := by decide +kernel
theorem sub_77_79 : s77 ⊆ s79 := by decide +kernel
theorem sub_78_79 : s78 ⊆ s79 := by decide +kernel
theorem sub_89_91 : s89 ⊆ s91 := by decide +kernel
theorem sub_90_91 : s90 ⊆ s91 := by decide +kernel
theorem sub_128_144 : s128 ⊆ s144 := by decide +kernel
theorem sub_128_145 : s128 ⊆ s145 := by decide +kernel
theorem sub_128_146 : s128 ⊆ s146 := by decide +kernel
theorem sub_128_147 : s128 ⊆ s147 := by decide +kernel
theorem sub_128_149 : s128 ⊆ s149 := by decide +kernel
theorem sub_128_150 : s128 ⊆ s150 := by decide +kernel
theorem sub_128_151 : s128 ⊆ s151 := by decide +kernel
theorem sub_128_154 : s128 ⊆ s154 := by decide +kernel
theorem sub_128_155 : s128 ⊆ s155 := by decide +kernel
theorem sub_144_145 : s144 ⊆ s145 := by decide +kernel
theorem sub_144_146 : s144 ⊆ s146 := by decide +kernel
theorem sub_144_147 : s144 ⊆ s147 := by decide +kernel
theorem sub_144_149 : s144 ⊆ s149 := by decide +kernel
theorem sub_144_150 : s144 ⊆ s150 := by decide +kernel
theorem sub_144_151 : s144 ⊆ s151 := by decide +kernel
theorem sub_144_153 : s144 ⊆ s153 := by decide +kernel
theorem sub_144_154 : s144 ⊆ s154 := by decide +kernel
theorem sub_144_155 : s144 ⊆ s155 := by decide +kernel
theorem sub_145_147 : s145 ⊆ s147 := by decide +kernel
theorem sub_145_149 : s145 ⊆ s149 := by decide +kernel
theorem sub_145_151 : s145 ⊆ s151 := by decide +kernel
theorem sub_145_155 : s145 ⊆ s155 := by decide +kernel
theorem sub_146_147 : s146 ⊆ s147 := by decide +kernel
theorem sub_146_150 : s146 ⊆ s150 := by decide +kernel
theorem sub_146_151 : s146 ⊆ s151 := by decide +kernel
theorem sub_146_154 : s146 ⊆ s154 := by decide +kernel
theorem sub_146_155 : s146 ⊆ s155 := by decide +kernel
theorem sub_147_151 : s147 ⊆ s151 := by decide +kernel
theorem sub_147_155 : s147 ⊆ s155 := by decide +kernel
theorem sub_149_151 : s149 ⊆ s151 := by decide +kernel
theorem sub_150_151 : s150 ⊆ s151 := by decide +kernel
theorem sub_153_155 : s153 ⊆ s155 := by decide +kernel
theorem sub_154_155 : s154 ⊆ s155 := by decide +kernel

section Acc

variable {α : Type*} [LinearOrder α]

/-! ### Acceptance propositions

`accP_B v`: an agent with valuation `v` accepts block `b` of partition `p`. -/

abbrev acc0_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s32 ≤ v s155 ∨ v s4 ≤ v s155) ∧ (v s0 ≤ v s155)
abbrev acc0_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s154 ≤ v s36 ∨ v s153 ≤ v s36 ∨ v s147 ≤ v s36 ∨ v s27 ≤ v s36) ∧ (v s0 ≤ v s36)
abbrev acc0_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s154 ≤ v s64 ∨ v s153 ≤ v s64 ∨ v s147 ≤ v s64 ∨ v s27 ≤ v s64) ∧ (v s32 ≤ v s64 ∨ v s4 ≤ v s64)
abbrev acc1_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s64 ≤ v s151 ∨ v s8 ≤ v s151) ∧ (v s0 ≤ v s151)
abbrev acc1_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s150 ≤ v s72 ∨ v s149 ≤ v s72 ∨ v s147 ≤ v s72 ∨ v s23 ≤ v s72) ∧ (v s0 ≤ v s72)
abbrev acc1_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s150 ≤ v s32 ∨ v s149 ≤ v s32 ∨ v s147 ≤ v s32 ∨ v s23 ≤ v s32) ∧ (v s64 ≤ v s32 ∨ v s8 ≤ v s32)
abbrev acc2_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s32 ≤ v s147 ∨ v s4 ≤ v s147) ∧ (v s64 ≤ v s147 ∨ v s8 ≤ v s147)
abbrev acc2_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s146 ≤ v s36 ∨ v s145 ≤ v s36 ∨ v s19 ≤ v s36) ∧ (v s64 ≤ v s36 ∨ v s8 ≤ v s36)
abbrev acc2_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s146 ≤ v s72 ∨ v s145 ≤ v s72 ∨ v s19 ≤ v s72) ∧ (v s32 ≤ v s72 ∨ v s4 ≤ v s72)
abbrev acc3_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s32 ≤ v s91 ∨ v s4 ≤ v s91) ∧ (v s0 ≤ v s91)
abbrev acc3_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s90 ≤ v s36 ∨ v s89 ≤ v s36 ∨ v s75 ≤ v s36 ∨ v s27 ≤ v s36) ∧ (v s0 ≤ v s36)
abbrev acc3_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s90 ≤ v s128 ∨ v s89 ≤ v s128 ∨ v s75 ≤ v s128 ∨ v s27 ≤ v s128) ∧ (v s32 ≤ v s128 ∨ v s4 ≤ v s128)
abbrev acc4_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s36 ≤ v s89 ∨ v s6 ≤ v s89) ∧ (v s0 ≤ v s89)
abbrev acc4_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s73 ≤ v s38 ∨ v s25 ≤ v s38) ∧ (v s0 ≤ v s38)
abbrev acc4_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s73 ≤ v s128 ∨ v s25 ≤ v s128) ∧ (v s36 ≤ v s128 ∨ v s6 ≤ v s128)
abbrev acc5_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s128 ≤ v s79 ∨ v s16 ≤ v s79) ∧ (v s0 ≤ v s79)
abbrev acc5_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s78 ≤ v s144 ∨ v s77 ≤ v s144 ∨ v s75 ≤ v s144 ∨ v s15 ≤ v s144) ∧ (v s0 ≤ v s144)
abbrev acc5_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s78 ≤ v s32 ∨ v s77 ≤ v s32 ∨ v s75 ≤ v s32 ∨ v s15 ≤ v s32) ∧ (v s128 ≤ v s32 ∨ v s16 ≤ v s32)
abbrev acc6_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s144 ≤ v s77 ∨ v s18 ≤ v s77) ∧ (v s0 ≤ v s77)
abbrev acc6_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s73 ≤ v s146 ∨ v s13 ≤ v s146) ∧ (v s0 ≤ v s146)
abbrev acc6_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s73 ≤ v s32 ∨ v s13 ≤ v s32) ∧ (v s144 ≤ v s32 ∨ v s18 ≤ v s32)
abbrev acc7_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s32 ≤ v s75 ∨ v s4 ≤ v s75) ∧ (v s128 ≤ v s75 ∨ v s16 ≤ v s75)
abbrev acc7_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s74 ≤ v s36 ∨ v s73 ≤ v s36 ∨ v s11 ≤ v s36) ∧ (v s128 ≤ v s36 ∨ v s16 ≤ v s36)
abbrev acc7_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s74 ≤ v s144 ∨ v s73 ≤ v s144 ∨ v s11 ≤ v s144) ∧ (v s32 ≤ v s144 ∨ v s4 ≤ v s144)
abbrev acc8_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s146 ≤ v s73 ∨ v s22 ≤ v s73) ∧ (v s0 ≤ v s73)
abbrev acc8_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s72 ≤ v s150 ∨ v s9 ≤ v s150) ∧ (v s0 ≤ v s150)
abbrev acc8_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s72 ≤ v s32 ∨ v s9 ≤ v s32) ∧ (v s146 ≤ v s32 ∨ v s22 ≤ v s32)
abbrev acc9_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s144 ≤ v s73 ∨ v s18 ≤ v s73) ∧ (v s32 ≤ v s73 ∨ v s4 ≤ v s73)
abbrev acc9_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s72 ≤ v s146 ∨ v s9 ≤ v s146) ∧ (v s32 ≤ v s146 ∨ v s4 ≤ v s146)
abbrev acc9_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s72 ≤ v s36 ∨ v s9 ≤ v s36) ∧ (v s144 ≤ v s36 ∨ v s18 ≤ v s36)
abbrev acc10_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s38 ≤ v s73 ∨ v s22 ≤ v s73) ∧ (v s0 ≤ v s73)
abbrev acc10_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s72 ≤ v s54 ∨ v s9 ≤ v s54) ∧ (v s0 ≤ v s54)
abbrev acc10_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s72 ≤ v s128 ∨ v s9 ≤ v s128) ∧ (v s38 ≤ v s128 ∨ v s22 ≤ v s128)
abbrev acc11_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s36 ≤ v s73 ∨ v s6 ≤ v s73) ∧ (v s128 ≤ v s73 ∨ v s16 ≤ v s73)
abbrev acc11_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s72 ≤ v s38 ∨ v s9 ≤ v s38) ∧ (v s128 ≤ v s38 ∨ v s16 ≤ v s38)
abbrev acc11_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s72 ≤ v s144 ∨ v s9 ≤ v s144) ∧ (v s36 ≤ v s144 ∨ v s6 ≤ v s144)
abbrev acc12_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s64 ≤ v s55 ∨ v s8 ≤ v s55) ∧ (v s0 ≤ v s55)
abbrev acc12_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s54 ≤ v s72 ∨ v s53 ≤ v s72 ∨ v s39 ≤ v s72 ∨ v s23 ≤ v s72) ∧ (v s0 ≤ v s72)
abbrev acc12_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s54 ≤ v s128 ∨ v s53 ≤ v s128 ∨ v s39 ≤ v s128 ∨ v s23 ≤ v s128) ∧ (v s64 ≤ v s128 ∨ v s8 ≤ v s128)
abbrev acc13_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s128 ≤ v s47 ∨ v s16 ≤ v s47) ∧ (v s0 ≤ v s47)
abbrev acc13_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s46 ≤ v s144 ∨ v s45 ≤ v s144 ∨ v s39 ≤ v s144 ∨ v s15 ≤ v s144) ∧ (v s0 ≤ v s144)
abbrev acc13_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s46 ≤ v s64 ∨ v s45 ≤ v s64 ∨ v s39 ≤ v s64 ∨ v s15 ≤ v s64) ∧ (v s128 ≤ v s64 ∨ v s16 ≤ v s64)
abbrev acc14_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s144 ≤ v s45 ∨ v s18 ≤ v s45) ∧ (v s0 ≤ v s45)
abbrev acc14_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s37 ≤ v s146 ∨ v s13 ≤ v s146) ∧ (v s0 ≤ v s146)
abbrev acc14_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s37 ≤ v s64 ∨ v s13 ≤ v s64) ∧ (v s144 ≤ v s64 ∨ v s18 ≤ v s64)
abbrev acc15_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s64 ≤ v s39 ∨ v s8 ≤ v s39) ∧ (v s128 ≤ v s39 ∨ v s16 ≤ v s39)
abbrev acc15_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s38 ≤ v s72 ∨ v s37 ≤ v s72 ∨ v s7 ≤ v s72) ∧ (v s128 ≤ v s72 ∨ v s16 ≤ v s72)
abbrev acc15_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s38 ≤ v s144 ∨ v s37 ≤ v s144 ∨ v s7 ≤ v s144) ∧ (v s64 ≤ v s144 ∨ v s8 ≤ v s144)
abbrev acc16_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s146 ≤ v s37 ∨ v s26 ≤ v s37) ∧ (v s0 ≤ v s37)
abbrev acc16_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s36 ≤ v s154 ∨ v s5 ≤ v s154) ∧ (v s0 ≤ v s154)
abbrev acc16_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s36 ≤ v s64 ∨ v s5 ≤ v s64) ∧ (v s146 ≤ v s64 ∨ v s26 ≤ v s64)
abbrev acc17_0 (v : Finset (Fin 8) → α) : Prop :=
  (v s144 ≤ v s37 ∨ v s18 ≤ v s37) ∧ (v s64 ≤ v s37 ∨ v s8 ≤ v s37)
abbrev acc17_1 (v : Finset (Fin 8) → α) : Prop :=
  (v s36 ≤ v s146 ∨ v s5 ≤ v s146) ∧ (v s64 ≤ v s146 ∨ v s8 ≤ v s146)
abbrev acc17_2 (v : Finset (Fin 8) → α) : Prop :=
  (v s36 ≤ v s72 ∨ v s5 ≤ v s72) ∧ (v s144 ≤ v s72 ∨ v s18 ≤ v s72)

theorem accP0_0 (v : Finset (Fin 8) → α) (h : acc0_0 v) : AccP v P0 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨2, by decide, rc_36_2, (congrArg v sd_36_2).trans_le h⟩
    · exact ⟨5, by decide, rc_36_5, (congrArg v sd_36_5).trans_le h⟩
  · exact ⟨6, by decide, rc_64_6, (congrArg v sd_64_6).trans_le h1⟩
theorem accP0_1 (v : Finset (Fin 8) → α) (h : acc0_1 v) : AccP v P0 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h | h
    · exact ⟨0, by decide, rc_155_0, (congrArg v sd_155_0).trans_le h⟩
    · exact ⟨1, by decide, rc_155_1, (congrArg v sd_155_1).trans_le h⟩
    · exact ⟨3, by decide, rc_155_3, (congrArg v sd_155_3).trans_le h⟩
    · exact ⟨7, by decide, rc_155_7, (congrArg v sd_155_7).trans_le h⟩
  · exact absurd rfl hc
  · exact ⟨6, by decide, rc_64_6, (congrArg v sd_64_6).trans_le h1⟩
theorem accP0_2 (v : Finset (Fin 8) → α) (h : acc0_2 v) : AccP v P0 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h | h
    · exact ⟨0, by decide, rc_155_0, (congrArg v sd_155_0).trans_le h⟩
    · exact ⟨1, by decide, rc_155_1, (congrArg v sd_155_1).trans_le h⟩
    · exact ⟨3, by decide, rc_155_3, (congrArg v sd_155_3).trans_le h⟩
    · exact ⟨7, by decide, rc_155_7, (congrArg v sd_155_7).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨2, by decide, rc_36_2, (congrArg v sd_36_2).trans_le h⟩
    · exact ⟨5, by decide, rc_36_5, (congrArg v sd_36_5).trans_le h⟩
  · exact absurd rfl hc
theorem accP1_0 (v : Finset (Fin 8) → α) (h : acc1_0 v) : AccP v P1 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨3, by decide, rc_72_3, (congrArg v sd_72_3).trans_le h⟩
    · exact ⟨6, by decide, rc_72_6, (congrArg v sd_72_6).trans_le h⟩
  · exact ⟨5, by decide, rc_32_5, (congrArg v sd_32_5).trans_le h1⟩
theorem accP1_1 (v : Finset (Fin 8) → α) (h : acc1_1 v) : AccP v P1 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h | h
    · exact ⟨0, by decide, rc_151_0, (congrArg v sd_151_0).trans_le h⟩
    · exact ⟨1, by decide, rc_151_1, (congrArg v sd_151_1).trans_le h⟩
    · exact ⟨2, by decide, rc_151_2, (congrArg v sd_151_2).trans_le h⟩
    · exact ⟨7, by decide, rc_151_7, (congrArg v sd_151_7).trans_le h⟩
  · exact absurd rfl hc
  · exact ⟨5, by decide, rc_32_5, (congrArg v sd_32_5).trans_le h1⟩
theorem accP1_2 (v : Finset (Fin 8) → α) (h : acc1_2 v) : AccP v P1 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h | h
    · exact ⟨0, by decide, rc_151_0, (congrArg v sd_151_0).trans_le h⟩
    · exact ⟨1, by decide, rc_151_1, (congrArg v sd_151_1).trans_le h⟩
    · exact ⟨2, by decide, rc_151_2, (congrArg v sd_151_2).trans_le h⟩
    · exact ⟨7, by decide, rc_151_7, (congrArg v sd_151_7).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨3, by decide, rc_72_3, (congrArg v sd_72_3).trans_le h⟩
    · exact ⟨6, by decide, rc_72_6, (congrArg v sd_72_6).trans_le h⟩
  · exact absurd rfl hc
theorem accP2_0 (v : Finset (Fin 8) → α) (h : acc2_0 v) : AccP v P2 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨2, by decide, rc_36_2, (congrArg v sd_36_2).trans_le h⟩
    · exact ⟨5, by decide, rc_36_5, (congrArg v sd_36_5).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨3, by decide, rc_72_3, (congrArg v sd_72_3).trans_le h⟩
    · exact ⟨6, by decide, rc_72_6, (congrArg v sd_72_6).trans_le h⟩
theorem accP2_1 (v : Finset (Fin 8) → α) (h : acc2_1 v) : AccP v P2 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h
    · exact ⟨0, by decide, rc_147_0, (congrArg v sd_147_0).trans_le h⟩
    · exact ⟨1, by decide, rc_147_1, (congrArg v sd_147_1).trans_le h⟩
    · exact ⟨7, by decide, rc_147_7, (congrArg v sd_147_7).trans_le h⟩
  · exact absurd rfl hc
  · rcases h1 with h | h
    · exact ⟨3, by decide, rc_72_3, (congrArg v sd_72_3).trans_le h⟩
    · exact ⟨6, by decide, rc_72_6, (congrArg v sd_72_6).trans_le h⟩
theorem accP2_2 (v : Finset (Fin 8) → α) (h : acc2_2 v) : AccP v P2 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h
    · exact ⟨0, by decide, rc_147_0, (congrArg v sd_147_0).trans_le h⟩
    · exact ⟨1, by decide, rc_147_1, (congrArg v sd_147_1).trans_le h⟩
    · exact ⟨7, by decide, rc_147_7, (congrArg v sd_147_7).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨2, by decide, rc_36_2, (congrArg v sd_36_2).trans_le h⟩
    · exact ⟨5, by decide, rc_36_5, (congrArg v sd_36_5).trans_le h⟩
  · exact absurd rfl hc
theorem accP3_0 (v : Finset (Fin 8) → α) (h : acc3_0 v) : AccP v P3 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨2, by decide, rc_36_2, (congrArg v sd_36_2).trans_le h⟩
    · exact ⟨5, by decide, rc_36_5, (congrArg v sd_36_5).trans_le h⟩
  · exact ⟨7, by decide, rc_128_7, (congrArg v sd_128_7).trans_le h1⟩
theorem accP3_1 (v : Finset (Fin 8) → α) (h : acc3_1 v) : AccP v P3 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h | h
    · exact ⟨0, by decide, rc_91_0, (congrArg v sd_91_0).trans_le h⟩
    · exact ⟨1, by decide, rc_91_1, (congrArg v sd_91_1).trans_le h⟩
    · exact ⟨4, by decide, rc_91_4, (congrArg v sd_91_4).trans_le h⟩
    · exact ⟨6, by decide, rc_91_6, (congrArg v sd_91_6).trans_le h⟩
  · exact absurd rfl hc
  · exact ⟨7, by decide, rc_128_7, (congrArg v sd_128_7).trans_le h1⟩
theorem accP3_2 (v : Finset (Fin 8) → α) (h : acc3_2 v) : AccP v P3 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h | h
    · exact ⟨0, by decide, rc_91_0, (congrArg v sd_91_0).trans_le h⟩
    · exact ⟨1, by decide, rc_91_1, (congrArg v sd_91_1).trans_le h⟩
    · exact ⟨4, by decide, rc_91_4, (congrArg v sd_91_4).trans_le h⟩
    · exact ⟨6, by decide, rc_91_6, (congrArg v sd_91_6).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨2, by decide, rc_36_2, (congrArg v sd_36_2).trans_le h⟩
    · exact ⟨5, by decide, rc_36_5, (congrArg v sd_36_5).trans_le h⟩
  · exact absurd rfl hc
theorem accP4_0 (v : Finset (Fin 8) → α) (h : acc4_0 v) : AccP v P4 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨1, by decide, rc_38_1, (congrArg v sd_38_1).trans_le h⟩
    · exact ⟨5, by decide, rc_38_5, (congrArg v sd_38_5).trans_le h⟩
  · exact ⟨7, by decide, rc_128_7, (congrArg v sd_128_7).trans_le h1⟩
theorem accP4_1 (v : Finset (Fin 8) → α) (h : acc4_1 v) : AccP v P4 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨4, by decide, rc_89_4, (congrArg v sd_89_4).trans_le h⟩
    · exact ⟨6, by decide, rc_89_6, (congrArg v sd_89_6).trans_le h⟩
  · exact absurd rfl hc
  · exact ⟨7, by decide, rc_128_7, (congrArg v sd_128_7).trans_le h1⟩
theorem accP4_2 (v : Finset (Fin 8) → α) (h : acc4_2 v) : AccP v P4 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨4, by decide, rc_89_4, (congrArg v sd_89_4).trans_le h⟩
    · exact ⟨6, by decide, rc_89_6, (congrArg v sd_89_6).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨1, by decide, rc_38_1, (congrArg v sd_38_1).trans_le h⟩
    · exact ⟨5, by decide, rc_38_5, (congrArg v sd_38_5).trans_le h⟩
  · exact absurd rfl hc
theorem accP5_0 (v : Finset (Fin 8) → α) (h : acc5_0 v) : AccP v P5 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨4, by decide, rc_144_4, (congrArg v sd_144_4).trans_le h⟩
    · exact ⟨7, by decide, rc_144_7, (congrArg v sd_144_7).trans_le h⟩
  · exact ⟨5, by decide, rc_32_5, (congrArg v sd_32_5).trans_le h1⟩
theorem accP5_1 (v : Finset (Fin 8) → α) (h : acc5_1 v) : AccP v P5 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h | h
    · exact ⟨0, by decide, rc_79_0, (congrArg v sd_79_0).trans_le h⟩
    · exact ⟨1, by decide, rc_79_1, (congrArg v sd_79_1).trans_le h⟩
    · exact ⟨2, by decide, rc_79_2, (congrArg v sd_79_2).trans_le h⟩
    · exact ⟨6, by decide, rc_79_6, (congrArg v sd_79_6).trans_le h⟩
  · exact absurd rfl hc
  · exact ⟨5, by decide, rc_32_5, (congrArg v sd_32_5).trans_le h1⟩
theorem accP5_2 (v : Finset (Fin 8) → α) (h : acc5_2 v) : AccP v P5 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h | h
    · exact ⟨0, by decide, rc_79_0, (congrArg v sd_79_0).trans_le h⟩
    · exact ⟨1, by decide, rc_79_1, (congrArg v sd_79_1).trans_le h⟩
    · exact ⟨2, by decide, rc_79_2, (congrArg v sd_79_2).trans_le h⟩
    · exact ⟨6, by decide, rc_79_6, (congrArg v sd_79_6).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨4, by decide, rc_144_4, (congrArg v sd_144_4).trans_le h⟩
    · exact ⟨7, by decide, rc_144_7, (congrArg v sd_144_7).trans_le h⟩
  · exact absurd rfl hc
theorem accP6_0 (v : Finset (Fin 8) → α) (h : acc6_0 v) : AccP v P6 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨1, by decide, rc_146_1, (congrArg v sd_146_1).trans_le h⟩
    · exact ⟨7, by decide, rc_146_7, (congrArg v sd_146_7).trans_le h⟩
  · exact ⟨5, by decide, rc_32_5, (congrArg v sd_32_5).trans_le h1⟩
theorem accP6_1 (v : Finset (Fin 8) → α) (h : acc6_1 v) : AccP v P6 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨2, by decide, rc_77_2, (congrArg v sd_77_2).trans_le h⟩
    · exact ⟨6, by decide, rc_77_6, (congrArg v sd_77_6).trans_le h⟩
  · exact absurd rfl hc
  · exact ⟨5, by decide, rc_32_5, (congrArg v sd_32_5).trans_le h1⟩
theorem accP6_2 (v : Finset (Fin 8) → α) (h : acc6_2 v) : AccP v P6 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨2, by decide, rc_77_2, (congrArg v sd_77_2).trans_le h⟩
    · exact ⟨6, by decide, rc_77_6, (congrArg v sd_77_6).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨1, by decide, rc_146_1, (congrArg v sd_146_1).trans_le h⟩
    · exact ⟨7, by decide, rc_146_7, (congrArg v sd_146_7).trans_le h⟩
  · exact absurd rfl hc
theorem accP7_0 (v : Finset (Fin 8) → α) (h : acc7_0 v) : AccP v P7 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨2, by decide, rc_36_2, (congrArg v sd_36_2).trans_le h⟩
    · exact ⟨5, by decide, rc_36_5, (congrArg v sd_36_5).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨4, by decide, rc_144_4, (congrArg v sd_144_4).trans_le h⟩
    · exact ⟨7, by decide, rc_144_7, (congrArg v sd_144_7).trans_le h⟩
theorem accP7_1 (v : Finset (Fin 8) → α) (h : acc7_1 v) : AccP v P7 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h
    · exact ⟨0, by decide, rc_75_0, (congrArg v sd_75_0).trans_le h⟩
    · exact ⟨1, by decide, rc_75_1, (congrArg v sd_75_1).trans_le h⟩
    · exact ⟨6, by decide, rc_75_6, (congrArg v sd_75_6).trans_le h⟩
  · exact absurd rfl hc
  · rcases h1 with h | h
    · exact ⟨4, by decide, rc_144_4, (congrArg v sd_144_4).trans_le h⟩
    · exact ⟨7, by decide, rc_144_7, (congrArg v sd_144_7).trans_le h⟩
theorem accP7_2 (v : Finset (Fin 8) → α) (h : acc7_2 v) : AccP v P7 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h
    · exact ⟨0, by decide, rc_75_0, (congrArg v sd_75_0).trans_le h⟩
    · exact ⟨1, by decide, rc_75_1, (congrArg v sd_75_1).trans_le h⟩
    · exact ⟨6, by decide, rc_75_6, (congrArg v sd_75_6).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨2, by decide, rc_36_2, (congrArg v sd_36_2).trans_le h⟩
    · exact ⟨5, by decide, rc_36_5, (congrArg v sd_36_5).trans_le h⟩
  · exact absurd rfl hc
theorem accP8_0 (v : Finset (Fin 8) → α) (h : acc8_0 v) : AccP v P8 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨2, by decide, rc_150_2, (congrArg v sd_150_2).trans_le h⟩
    · exact ⟨7, by decide, rc_150_7, (congrArg v sd_150_7).trans_le h⟩
  · exact ⟨5, by decide, rc_32_5, (congrArg v sd_32_5).trans_le h1⟩
theorem accP8_1 (v : Finset (Fin 8) → α) (h : acc8_1 v) : AccP v P8 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨0, by decide, rc_73_0, (congrArg v sd_73_0).trans_le h⟩
    · exact ⟨6, by decide, rc_73_6, (congrArg v sd_73_6).trans_le h⟩
  · exact absurd rfl hc
  · exact ⟨5, by decide, rc_32_5, (congrArg v sd_32_5).trans_le h1⟩
theorem accP8_2 (v : Finset (Fin 8) → α) (h : acc8_2 v) : AccP v P8 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨0, by decide, rc_73_0, (congrArg v sd_73_0).trans_le h⟩
    · exact ⟨6, by decide, rc_73_6, (congrArg v sd_73_6).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨2, by decide, rc_150_2, (congrArg v sd_150_2).trans_le h⟩
    · exact ⟨7, by decide, rc_150_7, (congrArg v sd_150_7).trans_le h⟩
  · exact absurd rfl hc
theorem accP9_0 (v : Finset (Fin 8) → α) (h : acc9_0 v) : AccP v P9 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨1, by decide, rc_146_1, (congrArg v sd_146_1).trans_le h⟩
    · exact ⟨7, by decide, rc_146_7, (congrArg v sd_146_7).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨2, by decide, rc_36_2, (congrArg v sd_36_2).trans_le h⟩
    · exact ⟨5, by decide, rc_36_5, (congrArg v sd_36_5).trans_le h⟩
theorem accP9_1 (v : Finset (Fin 8) → α) (h : acc9_1 v) : AccP v P9 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨0, by decide, rc_73_0, (congrArg v sd_73_0).trans_le h⟩
    · exact ⟨6, by decide, rc_73_6, (congrArg v sd_73_6).trans_le h⟩
  · exact absurd rfl hc
  · rcases h1 with h | h
    · exact ⟨2, by decide, rc_36_2, (congrArg v sd_36_2).trans_le h⟩
    · exact ⟨5, by decide, rc_36_5, (congrArg v sd_36_5).trans_le h⟩
theorem accP9_2 (v : Finset (Fin 8) → α) (h : acc9_2 v) : AccP v P9 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨0, by decide, rc_73_0, (congrArg v sd_73_0).trans_le h⟩
    · exact ⟨6, by decide, rc_73_6, (congrArg v sd_73_6).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨1, by decide, rc_146_1, (congrArg v sd_146_1).trans_le h⟩
    · exact ⟨7, by decide, rc_146_7, (congrArg v sd_146_7).trans_le h⟩
  · exact absurd rfl hc
theorem accP10_0 (v : Finset (Fin 8) → α) (h : acc10_0 v) : AccP v P10 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨4, by decide, rc_54_4, (congrArg v sd_54_4).trans_le h⟩
    · exact ⟨5, by decide, rc_54_5, (congrArg v sd_54_5).trans_le h⟩
  · exact ⟨7, by decide, rc_128_7, (congrArg v sd_128_7).trans_le h1⟩
theorem accP10_1 (v : Finset (Fin 8) → α) (h : acc10_1 v) : AccP v P10 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨0, by decide, rc_73_0, (congrArg v sd_73_0).trans_le h⟩
    · exact ⟨6, by decide, rc_73_6, (congrArg v sd_73_6).trans_le h⟩
  · exact absurd rfl hc
  · exact ⟨7, by decide, rc_128_7, (congrArg v sd_128_7).trans_le h1⟩
theorem accP10_2 (v : Finset (Fin 8) → α) (h : acc10_2 v) : AccP v P10 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨0, by decide, rc_73_0, (congrArg v sd_73_0).trans_le h⟩
    · exact ⟨6, by decide, rc_73_6, (congrArg v sd_73_6).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨4, by decide, rc_54_4, (congrArg v sd_54_4).trans_le h⟩
    · exact ⟨5, by decide, rc_54_5, (congrArg v sd_54_5).trans_le h⟩
  · exact absurd rfl hc
theorem accP11_0 (v : Finset (Fin 8) → α) (h : acc11_0 v) : AccP v P11 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨1, by decide, rc_38_1, (congrArg v sd_38_1).trans_le h⟩
    · exact ⟨5, by decide, rc_38_5, (congrArg v sd_38_5).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨4, by decide, rc_144_4, (congrArg v sd_144_4).trans_le h⟩
    · exact ⟨7, by decide, rc_144_7, (congrArg v sd_144_7).trans_le h⟩
theorem accP11_1 (v : Finset (Fin 8) → α) (h : acc11_1 v) : AccP v P11 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨0, by decide, rc_73_0, (congrArg v sd_73_0).trans_le h⟩
    · exact ⟨6, by decide, rc_73_6, (congrArg v sd_73_6).trans_le h⟩
  · exact absurd rfl hc
  · rcases h1 with h | h
    · exact ⟨4, by decide, rc_144_4, (congrArg v sd_144_4).trans_le h⟩
    · exact ⟨7, by decide, rc_144_7, (congrArg v sd_144_7).trans_le h⟩
theorem accP11_2 (v : Finset (Fin 8) → α) (h : acc11_2 v) : AccP v P11 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨0, by decide, rc_73_0, (congrArg v sd_73_0).trans_le h⟩
    · exact ⟨6, by decide, rc_73_6, (congrArg v sd_73_6).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨1, by decide, rc_38_1, (congrArg v sd_38_1).trans_le h⟩
    · exact ⟨5, by decide, rc_38_5, (congrArg v sd_38_5).trans_le h⟩
  · exact absurd rfl hc
theorem accP12_0 (v : Finset (Fin 8) → α) (h : acc12_0 v) : AccP v P12 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨3, by decide, rc_72_3, (congrArg v sd_72_3).trans_le h⟩
    · exact ⟨6, by decide, rc_72_6, (congrArg v sd_72_6).trans_le h⟩
  · exact ⟨7, by decide, rc_128_7, (congrArg v sd_128_7).trans_le h1⟩
theorem accP12_1 (v : Finset (Fin 8) → α) (h : acc12_1 v) : AccP v P12 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h | h
    · exact ⟨0, by decide, rc_55_0, (congrArg v sd_55_0).trans_le h⟩
    · exact ⟨1, by decide, rc_55_1, (congrArg v sd_55_1).trans_le h⟩
    · exact ⟨4, by decide, rc_55_4, (congrArg v sd_55_4).trans_le h⟩
    · exact ⟨5, by decide, rc_55_5, (congrArg v sd_55_5).trans_le h⟩
  · exact absurd rfl hc
  · exact ⟨7, by decide, rc_128_7, (congrArg v sd_128_7).trans_le h1⟩
theorem accP12_2 (v : Finset (Fin 8) → α) (h : acc12_2 v) : AccP v P12 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h | h
    · exact ⟨0, by decide, rc_55_0, (congrArg v sd_55_0).trans_le h⟩
    · exact ⟨1, by decide, rc_55_1, (congrArg v sd_55_1).trans_le h⟩
    · exact ⟨4, by decide, rc_55_4, (congrArg v sd_55_4).trans_le h⟩
    · exact ⟨5, by decide, rc_55_5, (congrArg v sd_55_5).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨3, by decide, rc_72_3, (congrArg v sd_72_3).trans_le h⟩
    · exact ⟨6, by decide, rc_72_6, (congrArg v sd_72_6).trans_le h⟩
  · exact absurd rfl hc
theorem accP13_0 (v : Finset (Fin 8) → α) (h : acc13_0 v) : AccP v P13 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨4, by decide, rc_144_4, (congrArg v sd_144_4).trans_le h⟩
    · exact ⟨7, by decide, rc_144_7, (congrArg v sd_144_7).trans_le h⟩
  · exact ⟨6, by decide, rc_64_6, (congrArg v sd_64_6).trans_le h1⟩
theorem accP13_1 (v : Finset (Fin 8) → α) (h : acc13_1 v) : AccP v P13 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h | h
    · exact ⟨0, by decide, rc_47_0, (congrArg v sd_47_0).trans_le h⟩
    · exact ⟨1, by decide, rc_47_1, (congrArg v sd_47_1).trans_le h⟩
    · exact ⟨3, by decide, rc_47_3, (congrArg v sd_47_3).trans_le h⟩
    · exact ⟨5, by decide, rc_47_5, (congrArg v sd_47_5).trans_le h⟩
  · exact absurd rfl hc
  · exact ⟨6, by decide, rc_64_6, (congrArg v sd_64_6).trans_le h1⟩
theorem accP13_2 (v : Finset (Fin 8) → α) (h : acc13_2 v) : AccP v P13 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h | h
    · exact ⟨0, by decide, rc_47_0, (congrArg v sd_47_0).trans_le h⟩
    · exact ⟨1, by decide, rc_47_1, (congrArg v sd_47_1).trans_le h⟩
    · exact ⟨3, by decide, rc_47_3, (congrArg v sd_47_3).trans_le h⟩
    · exact ⟨5, by decide, rc_47_5, (congrArg v sd_47_5).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨4, by decide, rc_144_4, (congrArg v sd_144_4).trans_le h⟩
    · exact ⟨7, by decide, rc_144_7, (congrArg v sd_144_7).trans_le h⟩
  · exact absurd rfl hc
theorem accP14_0 (v : Finset (Fin 8) → α) (h : acc14_0 v) : AccP v P14 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨1, by decide, rc_146_1, (congrArg v sd_146_1).trans_le h⟩
    · exact ⟨7, by decide, rc_146_7, (congrArg v sd_146_7).trans_le h⟩
  · exact ⟨6, by decide, rc_64_6, (congrArg v sd_64_6).trans_le h1⟩
theorem accP14_1 (v : Finset (Fin 8) → α) (h : acc14_1 v) : AccP v P14 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨3, by decide, rc_45_3, (congrArg v sd_45_3).trans_le h⟩
    · exact ⟨5, by decide, rc_45_5, (congrArg v sd_45_5).trans_le h⟩
  · exact absurd rfl hc
  · exact ⟨6, by decide, rc_64_6, (congrArg v sd_64_6).trans_le h1⟩
theorem accP14_2 (v : Finset (Fin 8) → α) (h : acc14_2 v) : AccP v P14 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨3, by decide, rc_45_3, (congrArg v sd_45_3).trans_le h⟩
    · exact ⟨5, by decide, rc_45_5, (congrArg v sd_45_5).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨1, by decide, rc_146_1, (congrArg v sd_146_1).trans_le h⟩
    · exact ⟨7, by decide, rc_146_7, (congrArg v sd_146_7).trans_le h⟩
  · exact absurd rfl hc
theorem accP15_0 (v : Finset (Fin 8) → α) (h : acc15_0 v) : AccP v P15 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨3, by decide, rc_72_3, (congrArg v sd_72_3).trans_le h⟩
    · exact ⟨6, by decide, rc_72_6, (congrArg v sd_72_6).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨4, by decide, rc_144_4, (congrArg v sd_144_4).trans_le h⟩
    · exact ⟨7, by decide, rc_144_7, (congrArg v sd_144_7).trans_le h⟩
theorem accP15_1 (v : Finset (Fin 8) → α) (h : acc15_1 v) : AccP v P15 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h
    · exact ⟨0, by decide, rc_39_0, (congrArg v sd_39_0).trans_le h⟩
    · exact ⟨1, by decide, rc_39_1, (congrArg v sd_39_1).trans_le h⟩
    · exact ⟨5, by decide, rc_39_5, (congrArg v sd_39_5).trans_le h⟩
  · exact absurd rfl hc
  · rcases h1 with h | h
    · exact ⟨4, by decide, rc_144_4, (congrArg v sd_144_4).trans_le h⟩
    · exact ⟨7, by decide, rc_144_7, (congrArg v sd_144_7).trans_le h⟩
theorem accP15_2 (v : Finset (Fin 8) → α) (h : acc15_2 v) : AccP v P15 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h | h
    · exact ⟨0, by decide, rc_39_0, (congrArg v sd_39_0).trans_le h⟩
    · exact ⟨1, by decide, rc_39_1, (congrArg v sd_39_1).trans_le h⟩
    · exact ⟨5, by decide, rc_39_5, (congrArg v sd_39_5).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨3, by decide, rc_72_3, (congrArg v sd_72_3).trans_le h⟩
    · exact ⟨6, by decide, rc_72_6, (congrArg v sd_72_6).trans_le h⟩
  · exact absurd rfl hc
theorem accP16_0 (v : Finset (Fin 8) → α) (h : acc16_0 v) : AccP v P16 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨3, by decide, rc_154_3, (congrArg v sd_154_3).trans_le h⟩
    · exact ⟨7, by decide, rc_154_7, (congrArg v sd_154_7).trans_le h⟩
  · exact ⟨6, by decide, rc_64_6, (congrArg v sd_64_6).trans_le h1⟩
theorem accP16_1 (v : Finset (Fin 8) → α) (h : acc16_1 v) : AccP v P16 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨0, by decide, rc_37_0, (congrArg v sd_37_0).trans_le h⟩
    · exact ⟨5, by decide, rc_37_5, (congrArg v sd_37_5).trans_le h⟩
  · exact absurd rfl hc
  · exact ⟨6, by decide, rc_64_6, (congrArg v sd_64_6).trans_le h1⟩
theorem accP16_2 (v : Finset (Fin 8) → α) (h : acc16_2 v) : AccP v P16 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨0, by decide, rc_37_0, (congrArg v sd_37_0).trans_le h⟩
    · exact ⟨5, by decide, rc_37_5, (congrArg v sd_37_5).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨3, by decide, rc_154_3, (congrArg v sd_154_3).trans_le h⟩
    · exact ⟨7, by decide, rc_154_7, (congrArg v sd_154_7).trans_le h⟩
  · exact absurd rfl hc
theorem accP17_0 (v : Finset (Fin 8) → α) (h : acc17_0 v) : AccP v P17 0 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · exact absurd rfl hc
  · rcases h0 with h | h
    · exact ⟨1, by decide, rc_146_1, (congrArg v sd_146_1).trans_le h⟩
    · exact ⟨7, by decide, rc_146_7, (congrArg v sd_146_7).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨3, by decide, rc_72_3, (congrArg v sd_72_3).trans_le h⟩
    · exact ⟨6, by decide, rc_72_6, (congrArg v sd_72_6).trans_le h⟩
theorem accP17_1 (v : Finset (Fin 8) → α) (h : acc17_1 v) : AccP v P17 1 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨0, by decide, rc_37_0, (congrArg v sd_37_0).trans_le h⟩
    · exact ⟨5, by decide, rc_37_5, (congrArg v sd_37_5).trans_le h⟩
  · exact absurd rfl hc
  · rcases h1 with h | h
    · exact ⟨3, by decide, rc_72_3, (congrArg v sd_72_3).trans_le h⟩
    · exact ⟨6, by decide, rc_72_6, (congrArg v sd_72_6).trans_le h⟩
theorem accP17_2 (v : Finset (Fin 8) → α) (h : acc17_2 v) : AccP v P17 2 := by
  obtain ⟨h0, h1⟩ := h
  intro c hc
  fin_cases c
  · rcases h0 with h | h
    · exact ⟨0, by decide, rc_37_0, (congrArg v sd_37_0).trans_le h⟩
    · exact ⟨5, by decide, rc_37_5, (congrArg v sd_37_5).trans_le h⟩
  · rcases h1 with h | h
    · exact ⟨1, by decide, rc_146_1, (congrArg v sd_146_1).trans_le h⟩
    · exact ⟨7, by decide, rc_146_7, (congrArg v sd_146_7).trans_le h⟩
  · exact absurd rfl hc

/-! ### Single-agent clauses over acceptance propositions -/

theorem cl0 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc0_1 v) : False := by
  rcases le_or_gt (v s32) (v s155) with g1 | g1
  · exact h0 ⟨Or.inl (g1), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_154_155) (g1)) (hv _ _ sub_32_36))), hv _ _ sub_0_36⟩
theorem cl1 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc1_0 v) : False := by
  rcases le_or_gt (v s4) (v s155) with g2 | g2
  · exact h0 ⟨Or.inr (g2), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_8_155) (g2)) (hv _ _ sub_4_151))), hv _ _ sub_0_151⟩
theorem cl2 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc1_2 v) : False := by
  rcases le_or_gt (v s32) (v s155) with g3 | g3
  · exact h0 ⟨Or.inl (g3), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_147_155) (g3))))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_8_155) (g3)))⟩
theorem cl4 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc2_1 v) : False := by
  rcases le_or_gt (v s32) (v s155) with g4 | g4
  · exact h0 ⟨Or.inl (g4), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_146_155) (g4)) (hv _ _ sub_32_36))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_8_155) (g4)) (hv _ _ sub_32_36)))⟩
theorem cl5 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc3_1 v) : False := by
  rcases le_or_gt (v s32) (v s155) with g5 | g5
  · exact h0 ⟨Or.inl (g5), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inr (Or.inr (Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_27_155) (g5)) (hv _ _ sub_32_36))))), hv _ _ sub_0_36⟩
theorem cl9 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc5_0 v) : False := by
  rcases le_or_gt (v s4) (v s155) with g6 | g6
  · exact h0 ⟨Or.inr (g6), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_155) (g6)) (hv _ _ sub_4_79))), hv _ _ sub_0_79⟩
theorem cl10 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc6_0 v) : False := by
  rcases le_or_gt (v s4) (v s155) with g7 | g7
  · exact h0 ⟨Or.inr (g7), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_144_155) (g7)) (hv _ _ sub_4_77))), hv _ _ sub_0_77⟩
theorem cl11 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc7_1 v) : False := by
  rcases le_or_gt (v s32) (v s155) with g8 | g8
  · exact h0 ⟨Or.inl (g8), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inr (Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_11_155) (g8)) (hv _ _ sub_32_36)))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_155) (g8)) (hv _ _ sub_32_36)))⟩
theorem cl12 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : acc7_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g9 | g9
  · exact h0 ⟨Or.inl (le_trans (g9) (hv _ _ sub_144_155)), hv _ _ sub_0_155⟩
  · exact h0 ⟨Or.inr (le_trans (g9) (hv _ _ sub_144_155)), hv _ _ sub_0_155⟩
theorem cl13 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc8_1 v) : False := by
  rcases le_or_gt (v s4) (v s155) with g10 | g10
  · exact h0 ⟨Or.inr (g10), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_9_155) (g10)) (hv _ _ sub_4_150))), hv _ _ sub_0_150⟩
theorem cl14 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc8_2 v) : False := by
  rcases le_or_gt (v s32) (v s155) with g11 | g11
  · exact h0 ⟨Or.inl (g11), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_9_155) (g11))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_146_155) (g11)))⟩
theorem cl15 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : acc9_1 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g12 | g12
  · exact h0 ⟨Or.inl (le_trans (g12) (hv _ _ sub_146_155)), hv _ _ sub_0_155⟩
  · exact h0 ⟨Or.inr (le_trans (g12) (hv _ _ sub_146_155)), hv _ _ sub_0_155⟩
theorem cl16 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc9_2 v) : False := by
  rcases le_or_gt (v s32) (v s155) with g13 | g13
  · exact h0 ⟨Or.inl (g13), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_9_155) (g13)) (hv _ _ sub_32_36))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_144_155) (g13)) (hv _ _ sub_32_36)))⟩
theorem cl19 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc11_1 v) : False := by
  rcases le_or_gt (v s32) (v s155) with g14 | g14
  · exact h0 ⟨Or.inl (g14), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_9_155) (g14)) (hv _ _ sub_32_38))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_155) (g14)) (hv _ _ sub_32_38)))⟩
theorem cl27 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc15_0 v) : False := by
  rcases le_or_gt (v s32) (v s155) with g15 | g15
  · exact h0 ⟨Or.inl (g15), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_8_155) (g15)) (hv _ _ sub_32_39))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_155) (g15)) (hv _ _ sub_32_39)))⟩
theorem cl29 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc16_0 v) : False := by
  rcases le_or_gt (v s32) (v s155) with g16 | g16
  · exact h0 ⟨Or.inl (g16), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_146_155) (g16)) (hv _ _ sub_32_37))), hv _ _ sub_0_37⟩
theorem cl31 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_0 v) (h1 : ¬acc17_0 v) : False := by
  rcases le_or_gt (v s32) (v s155) with g17 | g17
  · exact h0 ⟨Or.inl (g17), hv _ _ sub_0_155⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_144_155) (g17)) (hv _ _ sub_32_37))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_8_155) (g17)) (hv _ _ sub_32_37)))⟩
theorem cl34 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc0_1 v) (h1 : ¬acc14_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g18 | g18 | g18 | g18
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_154) (g18)) (hv _ _ sub_36_45)), hv _ _ sub_0_45⟩
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_153) (g18)) (hv _ _ sub_36_45)), hv _ _ sub_0_45⟩
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_147) (g18)) (hv _ _ sub_36_45)), hv _ _ sub_0_45⟩
  · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_27) (g18)) (hv _ _ sub_36_45)), hv _ _ sub_0_45⟩
theorem cl35 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_1 v) (h1 : ¬acc3_0 v) : False := by
  rcases le_or_gt (v s27) (v s36) with g19 | g19
  · exact h0 ⟨Or.inr (Or.inr (Or.inr (g19))), hv _ _ sub_0_36⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_36) (g19)) (hv _ _ sub_27_91))), hv _ _ sub_0_91⟩
theorem cl36 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_1 v) (h1 : ¬acc16_1 v) : False := by
  rcases le_or_gt (v s154) (v s36) with g20 | g20
  · exact h0 ⟨Or.inl (g20), hv _ _ sub_0_36⟩
  · exact h1 ⟨Or.inl (le_of_lt (g20)), hv _ _ sub_0_154⟩
theorem cl42 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc0_2 v) (h1 : ¬acc9_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g21 | g21
  · rcases h0a with g22 | g22 | g22 | g22
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_154) (g22)) (hv _ _ sub_64_73)), Or.inl (le_trans (g21) (hv _ _ sub_64_73))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_153) (g22)) (hv _ _ sub_64_73)), Or.inl (le_trans (g21) (hv _ _ sub_64_73))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_147) (g22)) (hv _ _ sub_64_73)), Or.inl (le_trans (g21) (hv _ _ sub_64_73))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_27) (g22)) (hv _ _ sub_64_73)), Or.inl (le_trans (g21) (hv _ _ sub_64_73))⟩
  · rcases h0a with g23 | g23 | g23 | g23
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_154) (g23)) (hv _ _ sub_64_73)), Or.inr (le_trans (g21) (hv _ _ sub_64_73))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_153) (g23)) (hv _ _ sub_64_73)), Or.inr (le_trans (g21) (hv _ _ sub_64_73))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_147) (g23)) (hv _ _ sub_64_73)), Or.inr (le_trans (g21) (hv _ _ sub_64_73))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_27) (g23)) (hv _ _ sub_64_73)), Or.inr (le_trans (g21) (hv _ _ sub_64_73))⟩
theorem cl43 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_2 v) (h1 : ¬acc1_0 v) : False := by
  rcases le_or_gt (v s64) (v s151) with g24 | g24
  · exact h1 ⟨Or.inl (g24), hv _ _ sub_0_151⟩
  · exact h0 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_147_151) (g24))))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_4_151) (g24)))⟩
theorem cl44 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : ¬acc1_1 v) : False := by
  rcases le_or_gt (v s64) (v s151) with g25 | g25
  · exact h0 ⟨Or.inl (g25), hv _ _ sub_0_151⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_150_151) (g25)) (hv _ _ sub_64_72))), hv _ _ sub_0_72⟩
theorem cl46 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : ¬acc2_2 v) : False := by
  rcases le_or_gt (v s64) (v s151) with g26 | g26
  · exact h0 ⟨Or.inl (g26), hv _ _ sub_0_151⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_146_151) (g26)) (hv _ _ sub_64_72))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_4_151) (g26)) (hv _ _ sub_64_72)))⟩
theorem cl47 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : ¬acc3_0 v) : False := by
  rcases le_or_gt (v s64) (v s151) with g27 | g27
  · exact h0 ⟨Or.inl (g27), hv _ _ sub_0_151⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_4_151) (g27)) (hv _ _ sub_64_91))), hv _ _ sub_0_91⟩
theorem cl61 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : ¬acc10_0 v) : False := by
  rcases le_or_gt (v s64) (v s151) with g28 | g28
  · exact h0 ⟨Or.inl (g28), hv _ _ sub_0_151⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_22_151) (g28)) (hv _ _ sub_64_73))), hv _ _ sub_0_73⟩
theorem cl64 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : acc11_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g29 | g29
  · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g29)) (hv _ _ sub_144_151)), hv _ _ sub_0_151⟩
  · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g29)) (hv _ _ sub_144_151)), hv _ _ sub_0_151⟩
theorem cl65 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : ¬acc12_1 v) : False := by
  rcases le_or_gt (v s64) (v s151) with g30 | g30
  · exact h0 ⟨Or.inl (g30), hv _ _ sub_0_151⟩
  · exact h1 ⟨Or.inr (Or.inr (Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_23_151) (g30)) (hv _ _ sub_64_72))))), hv _ _ sub_0_72⟩
theorem cl67 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : ¬acc13_0 v) : False := by
  rcases le_or_gt (v s8) (v s151) with g31 | g31
  · exact h0 ⟨Or.inr (g31), hv _ _ sub_0_151⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_151) (g31)) (hv _ _ sub_8_47))), hv _ _ sub_0_47⟩
theorem cl68 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : ¬acc14_0 v) : False := by
  rcases le_or_gt (v s8) (v s151) with g32 | g32
  · exact h0 ⟨Or.inr (g32), hv _ _ sub_0_151⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_144_151) (g32)) (hv _ _ sub_8_45))), hv _ _ sub_0_45⟩
theorem cl69 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : ¬acc15_1 v) : False := by
  rcases le_or_gt (v s64) (v s151) with g33 | g33
  · exact h0 ⟨Or.inl (g33), hv _ _ sub_0_151⟩
  · exact h1 ⟨Or.inr (Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_7_151) (g33)) (hv _ _ sub_64_72)))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_151) (g33)) (hv _ _ sub_64_72)))⟩
theorem cl70 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : acc15_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g34 | g34
  · exact h0 ⟨Or.inl (le_trans (g34) (hv _ _ sub_144_151)), hv _ _ sub_0_151⟩
  · exact h0 ⟨Or.inr (le_trans (g34) (hv _ _ sub_144_151)), hv _ _ sub_0_151⟩
theorem cl71 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : ¬acc16_1 v) : False := by
  rcases le_or_gt (v s8) (v s151) with g35 | g35
  · exact h0 ⟨Or.inr (g35), hv _ _ sub_0_151⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_5_151) (g35)) (hv _ _ sub_8_154))), hv _ _ sub_0_154⟩
theorem cl72 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : ¬acc16_2 v) : False := by
  rcases le_or_gt (v s64) (v s151) with g36 | g36
  · exact h0 ⟨Or.inl (g36), hv _ _ sub_0_151⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_5_151) (g36))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_146_151) (g36)))⟩
theorem cl74 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_0 v) (h1 : ¬acc17_2 v) : False := by
  rcases le_or_gt (v s64) (v s151) with g37 | g37
  · exact h0 ⟨Or.inl (g37), hv _ _ sub_0_151⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_5_151) (g37)) (hv _ _ sub_64_72))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_144_151) (g37)) (hv _ _ sub_64_72)))⟩
theorem cl77 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_1 v) (h1 : ¬acc8_1 v) : False := by
  rcases le_or_gt (v s150) (v s72) with g38 | g38
  · exact h0 ⟨Or.inl (g38), hv _ _ sub_0_72⟩
  · exact h1 ⟨Or.inl (le_of_lt (g38)), hv _ _ sub_0_150⟩
theorem cl78 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_1 v) (h1 : ¬acc12_0 v) : False := by
  rcases le_or_gt (v s23) (v s72) with g39 | g39
  · exact h0 ⟨Or.inr (Or.inr (Or.inr (g39))), hv _ _ sub_0_72⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g39)) (hv _ _ sub_23_55))), hv _ _ sub_0_55⟩
theorem cl79 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc1_2 v) (h1 : ¬acc2_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g40 | g40
  · rcases h0a with g41 | g41 | g41 | g41
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_146_150) (g41)) (hv _ _ sub_32_36)), Or.inl (le_trans (g40) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inr (Or.inl (le_trans (le_trans (hv _ _ sub_145_149) (g41)) (hv _ _ sub_32_36))), Or.inl (le_trans (g40) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_146_147) (g41)) (hv _ _ sub_32_36)), Or.inl (le_trans (g40) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inr (Or.inr (le_trans (le_trans (hv _ _ sub_19_23) (g41)) (hv _ _ sub_32_36))), Or.inl (le_trans (g40) (hv _ _ sub_32_36))⟩
  · rcases h0a with g42 | g42 | g42 | g42
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_146_150) (g42)) (hv _ _ sub_32_36)), Or.inr (le_trans (g40) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inr (Or.inl (le_trans (le_trans (hv _ _ sub_145_149) (g42)) (hv _ _ sub_32_36))), Or.inr (le_trans (g40) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_146_147) (g42)) (hv _ _ sub_32_36)), Or.inr (le_trans (g40) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inr (Or.inr (le_trans (le_trans (hv _ _ sub_19_23) (g42)) (hv _ _ sub_32_36))), Or.inr (le_trans (g40) (hv _ _ sub_32_36))⟩
theorem cl80 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc1_2 v) (h1 : ¬acc12_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g43 | g43
  · exact h1 ⟨Or.inl (le_trans (g43) (hv _ _ sub_32_55)), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inr (le_trans (g43) (hv _ _ sub_32_55)), hv _ _ sub_0_55⟩
theorem cl83 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc1_2 v) (h1 : ¬acc15_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g44 | g44
  · rcases h0a with g45 | g45 | g45 | g45
    · exact h1 ⟨Or.inl (le_trans (g44) (hv _ _ sub_32_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_150) (g45)) (hv _ _ sub_32_39))⟩
    · exact h1 ⟨Or.inl (le_trans (g44) (hv _ _ sub_32_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_149) (g45)) (hv _ _ sub_32_39))⟩
    · exact h1 ⟨Or.inl (le_trans (g44) (hv _ _ sub_32_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_147) (g45)) (hv _ _ sub_32_39))⟩
    · exact h1 ⟨Or.inl (le_trans (g44) (hv _ _ sub_32_39)), Or.inr (le_trans (le_trans (hv _ _ sub_16_23) (g45)) (hv _ _ sub_32_39))⟩
  · rcases h0a with g46 | g46 | g46 | g46
    · exact h1 ⟨Or.inr (le_trans (g44) (hv _ _ sub_32_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_150) (g46)) (hv _ _ sub_32_39))⟩
    · exact h1 ⟨Or.inr (le_trans (g44) (hv _ _ sub_32_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_149) (g46)) (hv _ _ sub_32_39))⟩
    · exact h1 ⟨Or.inr (le_trans (g44) (hv _ _ sub_32_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_147) (g46)) (hv _ _ sub_32_39))⟩
    · exact h1 ⟨Or.inr (le_trans (g44) (hv _ _ sub_32_39)), Or.inr (le_trans (le_trans (hv _ _ sub_16_23) (g46)) (hv _ _ sub_32_39))⟩
theorem cl84 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc1_2 v) (h1 : ¬acc17_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g47 | g47
  · rcases h0a with g48 | g48 | g48 | g48
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_150) (g48)) (hv _ _ sub_32_37)), Or.inl (le_trans (g47) (hv _ _ sub_32_37))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_149) (g48)) (hv _ _ sub_32_37)), Or.inl (le_trans (g47) (hv _ _ sub_32_37))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_147) (g48)) (hv _ _ sub_32_37)), Or.inl (le_trans (g47) (hv _ _ sub_32_37))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_23) (g48)) (hv _ _ sub_32_37)), Or.inl (le_trans (g47) (hv _ _ sub_32_37))⟩
  · rcases h0a with g49 | g49 | g49 | g49
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_150) (g49)) (hv _ _ sub_32_37)), Or.inr (le_trans (g47) (hv _ _ sub_32_37))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_149) (g49)) (hv _ _ sub_32_37)), Or.inr (le_trans (g47) (hv _ _ sub_32_37))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_147) (g49)) (hv _ _ sub_32_37)), Or.inr (le_trans (g47) (hv _ _ sub_32_37))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_23) (g49)) (hv _ _ sub_32_37)), Or.inr (le_trans (g47) (hv _ _ sub_32_37))⟩
theorem cl85 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : acc3_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g50 | g50
  · rcases h1a with g51 | g51 | g51 | g51
    · exact h0 ⟨Or.inl (le_trans (g50) (hv _ _ sub_128_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_90) (g51)) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inl (le_trans (g50) (hv _ _ sub_128_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_89) (g51)) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inl (le_trans (g50) (hv _ _ sub_128_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_75) (g51)) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inl (le_trans (g50) (hv _ _ sub_128_147)), Or.inr (le_trans (le_trans (hv _ _ sub_8_27) (g51)) (hv _ _ sub_128_147))⟩
  · rcases h1a with g52 | g52 | g52 | g52
    · exact h0 ⟨Or.inr (le_trans (g50) (hv _ _ sub_128_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_90) (g52)) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inr (le_trans (g50) (hv _ _ sub_128_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_89) (g52)) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inr (le_trans (g50) (hv _ _ sub_128_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_75) (g52)) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inr (le_trans (g50) (hv _ _ sub_128_147)), Or.inr (le_trans (le_trans (hv _ _ sub_8_27) (g52)) (hv _ _ sub_128_147))⟩
theorem cl86 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : acc4_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g53 | g53
  · rcases h1b with g54 | g54
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g54)) (hv _ _ sub_128_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_73) (g53)) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_4_6) (g54)) (hv _ _ sub_128_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_73) (g53)) (hv _ _ sub_128_147))⟩
  · rcases h1b with g55 | g55
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g55)) (hv _ _ sub_128_147)), Or.inr (le_trans (le_trans (hv _ _ sub_8_25) (g53)) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_4_6) (g55)) (hv _ _ sub_128_147)), Or.inr (le_trans (le_trans (hv _ _ sub_8_25) (g53)) (hv _ _ sub_128_147))⟩
theorem cl87 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : ¬acc5_0 v) : False := by
  rcases le_or_gt (v s128) (v s79) with g56 | g56
  · exact h1 ⟨Or.inl (g56), hv _ _ sub_0_79⟩
  · exact h0 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_4_79) (g56)) (hv _ _ sub_128_147))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_79) (g56)) (hv _ _ sub_128_147)))⟩
theorem cl88 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : ¬acc6_0 v) : False := by
  rcases le_or_gt (v s144) (v s77) with g57 | g57
  · exact h1 ⟨Or.inl (g57), hv _ _ sub_0_77⟩
  · exact h0 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_4_77) (g57)) (hv _ _ sub_144_147))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_77) (g57)) (hv _ _ sub_144_147)))⟩
theorem cl89 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : acc7_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g58 | g58
  · rcases h1a with g59 | g59 | g59
    · exact h0 ⟨Or.inl (le_trans (g58) (hv _ _ sub_144_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_74) (g59)) (hv _ _ sub_144_147))⟩
    · exact h0 ⟨Or.inl (le_trans (g58) (hv _ _ sub_144_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_73) (g59)) (hv _ _ sub_144_147))⟩
    · exact h0 ⟨Or.inl (le_trans (g58) (hv _ _ sub_144_147)), Or.inr (le_trans (le_trans (hv _ _ sub_8_11) (g59)) (hv _ _ sub_144_147))⟩
  · rcases h1a with g60 | g60 | g60
    · exact h0 ⟨Or.inr (le_trans (g58) (hv _ _ sub_144_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_74) (g60)) (hv _ _ sub_144_147))⟩
    · exact h0 ⟨Or.inr (le_trans (g58) (hv _ _ sub_144_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_73) (g60)) (hv _ _ sub_144_147))⟩
    · exact h0 ⟨Or.inr (le_trans (g58) (hv _ _ sub_144_147)), Or.inr (le_trans (le_trans (hv _ _ sub_8_11) (g60)) (hv _ _ sub_144_147))⟩
theorem cl90 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : acc9_1 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g61 | g61
  · rcases h1b with g62 | g62
    · exact h0 ⟨Or.inl (le_trans (g62) (hv _ _ sub_146_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g61)) (hv _ _ sub_146_147))⟩
    · exact h0 ⟨Or.inr (le_trans (g62) (hv _ _ sub_146_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g61)) (hv _ _ sub_146_147))⟩
  · rcases h1b with g63 | g63
    · exact h0 ⟨Or.inl (le_trans (g63) (hv _ _ sub_146_147)), Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g61)) (hv _ _ sub_146_147))⟩
    · exact h0 ⟨Or.inr (le_trans (g63) (hv _ _ sub_146_147)), Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g61)) (hv _ _ sub_146_147))⟩
theorem cl92 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : acc11_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g64 | g64
  · rcases h1b with g65 | g65
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g65)) (hv _ _ sub_144_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g64)) (hv _ _ sub_144_147))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_4_6) (g65)) (hv _ _ sub_144_147)), Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g64)) (hv _ _ sub_144_147))⟩
  · rcases h1b with g66 | g66
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g66)) (hv _ _ sub_144_147)), Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g64)) (hv _ _ sub_144_147))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_4_6) (g66)) (hv _ _ sub_144_147)), Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g64)) (hv _ _ sub_144_147))⟩
theorem cl93 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : acc12_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g67 | g67
  · rcases h1a with g68 | g68 | g68 | g68
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_54) (g68)) (hv _ _ sub_128_147)), Or.inl (le_trans (g67) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_53) (g68)) (hv _ _ sub_128_147)), Or.inl (le_trans (g67) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_39) (g68)) (hv _ _ sub_128_147)), Or.inl (le_trans (g67) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_4_23) (g68)) (hv _ _ sub_128_147)), Or.inl (le_trans (g67) (hv _ _ sub_128_147))⟩
  · rcases h1a with g69 | g69 | g69 | g69
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_54) (g69)) (hv _ _ sub_128_147)), Or.inr (le_trans (g67) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_53) (g69)) (hv _ _ sub_128_147)), Or.inr (le_trans (g67) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_39) (g69)) (hv _ _ sub_128_147)), Or.inr (le_trans (g67) (hv _ _ sub_128_147))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_4_23) (g69)) (hv _ _ sub_128_147)), Or.inr (le_trans (g67) (hv _ _ sub_128_147))⟩
theorem cl94 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : ¬acc13_0 v) : False := by
  rcases le_or_gt (v s128) (v s47) with g70 | g70
  · exact h1 ⟨Or.inl (g70), hv _ _ sub_0_47⟩
  · exact h0 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_47) (g70)) (hv _ _ sub_128_147))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_8_47) (g70)) (hv _ _ sub_128_147)))⟩
theorem cl95 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : ¬acc14_0 v) : False := by
  rcases le_or_gt (v s144) (v s45) with g71 | g71
  · exact h1 ⟨Or.inl (g71), hv _ _ sub_0_45⟩
  · exact h0 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_45) (g71)) (hv _ _ sub_144_147))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_8_45) (g71)) (hv _ _ sub_144_147)))⟩
theorem cl96 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : acc15_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g72 | g72
  · rcases h1a with g73 | g73 | g73
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_38) (g73)) (hv _ _ sub_144_147)), Or.inl (le_trans (g72) (hv _ _ sub_144_147))⟩
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_37) (g73)) (hv _ _ sub_144_147)), Or.inl (le_trans (g72) (hv _ _ sub_144_147))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_4_7) (g73)) (hv _ _ sub_144_147)), Or.inl (le_trans (g72) (hv _ _ sub_144_147))⟩
  · rcases h1a with g74 | g74 | g74
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_38) (g74)) (hv _ _ sub_144_147)), Or.inr (le_trans (g72) (hv _ _ sub_144_147))⟩
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_37) (g74)) (hv _ _ sub_144_147)), Or.inr (le_trans (g72) (hv _ _ sub_144_147))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_4_7) (g74)) (hv _ _ sub_144_147)), Or.inr (le_trans (g72) (hv _ _ sub_144_147))⟩
theorem cl97 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : acc17_1 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g75 | g75
  · rcases h1b with g76 | g76
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g75)) (hv _ _ sub_146_147)), Or.inl (le_trans (g76) (hv _ _ sub_146_147))⟩
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g75)) (hv _ _ sub_146_147)), Or.inr (le_trans (g76) (hv _ _ sub_146_147))⟩
  · rcases h1b with g77 | g77
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_4_5) (g75)) (hv _ _ sub_146_147)), Or.inl (le_trans (g77) (hv _ _ sub_146_147))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_4_5) (g75)) (hv _ _ sub_146_147)), Or.inr (le_trans (g77) (hv _ _ sub_146_147))⟩
theorem cl98 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc2_1 v) (h1 : ¬acc12_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g78 | g78
  · exact h1 ⟨Or.inl (le_trans (g78) (hv _ _ sub_36_55)), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inr (le_trans (g78) (hv _ _ sub_36_55)), hv _ _ sub_0_55⟩
theorem cl101 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc2_1 v) (h1 : ¬acc15_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g79 | g79
  · rcases h0a with g80 | g80 | g80
    · exact h1 ⟨Or.inl (le_trans (g79) (hv _ _ sub_36_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_146) (g80)) (hv _ _ sub_36_39))⟩
    · exact h1 ⟨Or.inl (le_trans (g79) (hv _ _ sub_36_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_145) (g80)) (hv _ _ sub_36_39))⟩
    · exact h1 ⟨Or.inl (le_trans (g79) (hv _ _ sub_36_39)), Or.inr (le_trans (le_trans (hv _ _ sub_16_19) (g80)) (hv _ _ sub_36_39))⟩
  · rcases h0a with g81 | g81 | g81
    · exact h1 ⟨Or.inr (le_trans (g79) (hv _ _ sub_36_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_146) (g81)) (hv _ _ sub_36_39))⟩
    · exact h1 ⟨Or.inr (le_trans (g79) (hv _ _ sub_36_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_145) (g81)) (hv _ _ sub_36_39))⟩
    · exact h1 ⟨Or.inr (le_trans (g79) (hv _ _ sub_36_39)), Or.inr (le_trans (le_trans (hv _ _ sub_16_19) (g81)) (hv _ _ sub_36_39))⟩
theorem cl102 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc2_1 v) (h1 : ¬acc17_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g82 | g82
  · rcases h0a with g83 | g83 | g83
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g83)) (hv _ _ sub_36_37)), Or.inl (le_trans (g82) (hv _ _ sub_36_37))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_145) (g83)) (hv _ _ sub_36_37)), Or.inl (le_trans (g82) (hv _ _ sub_36_37))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_19) (g83)) (hv _ _ sub_36_37)), Or.inl (le_trans (g82) (hv _ _ sub_36_37))⟩
  · rcases h0a with g84 | g84 | g84
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g84)) (hv _ _ sub_36_37)), Or.inr (le_trans (g82) (hv _ _ sub_36_37))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_145) (g84)) (hv _ _ sub_36_37)), Or.inr (le_trans (g82) (hv _ _ sub_36_37))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_19) (g84)) (hv _ _ sub_36_37)), Or.inr (le_trans (g82) (hv _ _ sub_36_37))⟩
theorem cl103 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_1 v) (h1 : ¬acc3_0 v) : False := by
  rcases le_or_gt (v s32) (v s91) with g85 | g85
  · exact h1 ⟨Or.inl (g85), hv _ _ sub_0_91⟩
  · exact h0 ⟨Or.inr (Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_19_91) (g85)) (hv _ _ sub_32_36)))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_91) (g85)) (hv _ _ sub_32_36)))⟩
theorem cl104 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_1 v) (h1 : ¬acc16_1 v) : False := by
  rcases le_or_gt (v s36) (v s154) with g86 | g86
  · exact h1 ⟨Or.inl (g86), hv _ _ sub_0_154⟩
  · exact h0 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_146_154) (g86))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_8_154) (g86)))⟩
theorem cl109 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc2_2 v) (h1 : ¬acc9_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g87 | g87
  · rcases h0a with g88 | g88 | g88
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g88)) (hv _ _ sub_72_73)), Or.inl (le_trans (g87) (hv _ _ sub_72_73))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_145) (g88)) (hv _ _ sub_72_73)), Or.inl (le_trans (g87) (hv _ _ sub_72_73))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_19) (g88)) (hv _ _ sub_72_73)), Or.inl (le_trans (g87) (hv _ _ sub_72_73))⟩
  · rcases h0a with g89 | g89 | g89
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g89)) (hv _ _ sub_72_73)), Or.inr (le_trans (g87) (hv _ _ sub_72_73))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_145) (g89)) (hv _ _ sub_72_73)), Or.inr (le_trans (g87) (hv _ _ sub_72_73))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_19) (g89)) (hv _ _ sub_72_73)), Or.inr (le_trans (g87) (hv _ _ sub_72_73))⟩
theorem cl110 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_2 v) (h1 : ¬acc8_1 v) : False := by
  rcases le_or_gt (v s72) (v s150) with g90 | g90
  · exact h1 ⟨Or.inl (g90), hv _ _ sub_0_150⟩
  · exact h0 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_146_150) (g90))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_4_150) (g90)))⟩
theorem cl111 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_2 v) (h1 : ¬acc12_0 v) : False := by
  rcases le_or_gt (v s64) (v s55) with g91 | g91
  · exact h1 ⟨Or.inl (g91), hv _ _ sub_0_55⟩
  · exact h0 ⟨Or.inr (Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_19_55) (g91)) (hv _ _ sub_64_72)))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_55) (g91)) (hv _ _ sub_64_72)))⟩
theorem cl112 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_0 v) (h1 : ¬acc3_1 v) : False := by
  rcases le_or_gt (v s32) (v s91) with g92 | g92
  · exact h0 ⟨Or.inl (g92), hv _ _ sub_0_91⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_90_91) (g92)) (hv _ _ sub_32_36))), hv _ _ sub_0_36⟩
theorem cl114 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_0 v) (h1 : ¬acc4_1 v) : False := by
  rcases le_or_gt (v s32) (v s91) with g93 | g93
  · exact h0 ⟨Or.inl (g93), hv _ _ sub_0_91⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_73_91) (g93)) (hv _ _ sub_32_38))), hv _ _ sub_0_38⟩
theorem cl115 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_0 v) (h1 : ¬acc5_0 v) : False := by
  rcases le_or_gt (v s4) (v s91) with g94 | g94
  · exact h0 ⟨Or.inr (g94), hv _ _ sub_0_91⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_91) (g94)) (hv _ _ sub_4_79))), hv _ _ sub_0_79⟩
theorem cl116 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_0 v) (h1 : ¬acc5_2 v) : False := by
  rcases le_or_gt (v s32) (v s91) with g95 | g95
  · exact h0 ⟨Or.inl (g95), hv _ _ sub_0_91⟩
  · exact h1 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_75_91) (g95))))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_16_91) (g95)))⟩
theorem cl117 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_0 v) (h1 : ¬acc6_0 v) : False := by
  rcases le_or_gt (v s4) (v s91) with g96 | g96
  · exact h0 ⟨Or.inr (g96), hv _ _ sub_0_91⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_18_91) (g96)) (hv _ _ sub_4_77))), hv _ _ sub_0_77⟩
theorem cl118 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_0 v) (h1 : ¬acc6_2 v) : False := by
  rcases le_or_gt (v s32) (v s91) with g97 | g97
  · exact h0 ⟨Or.inl (g97), hv _ _ sub_0_91⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_73_91) (g97))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_18_91) (g97)))⟩
theorem cl120 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_0 v) (h1 : ¬acc7_1 v) : False := by
  rcases le_or_gt (v s32) (v s91) with g98 | g98
  · exact h0 ⟨Or.inl (g98), hv _ _ sub_0_91⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_74_91) (g98)) (hv _ _ sub_32_36))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_91) (g98)) (hv _ _ sub_32_36)))⟩
theorem cl121 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_0 v) (h1 : ¬acc8_1 v) : False := by
  rcases le_or_gt (v s4) (v s91) with g99 | g99
  · exact h0 ⟨Or.inr (g99), hv _ _ sub_0_91⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_91) (g99)) (hv _ _ sub_4_150))), hv _ _ sub_0_150⟩
theorem cl123 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_0 v) (h1 : ¬acc9_2 v) : False := by
  rcases le_or_gt (v s32) (v s91) with g100 | g100
  · exact h0 ⟨Or.inl (g100), hv _ _ sub_0_91⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_91) (g100)) (hv _ _ sub_32_36))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_18_91) (g100)) (hv _ _ sub_32_36)))⟩
theorem cl127 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_0 v) (h1 : ¬acc11_1 v) : False := by
  rcases le_or_gt (v s32) (v s91) with g101 | g101
  · exact h0 ⟨Or.inl (g101), hv _ _ sub_0_91⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_91) (g101)) (hv _ _ sub_32_38))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_91) (g101)) (hv _ _ sub_32_38)))⟩
theorem cl130 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_0 v) (h1 : ¬acc13_0 v) : False := by
  rcases le_or_gt (v s32) (v s91) with g102 | g102
  · exact h0 ⟨Or.inl (g102), hv _ _ sub_0_91⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_91) (g102)) (hv _ _ sub_32_47))), hv _ _ sub_0_47⟩
theorem cl140 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc3_1 v) (h1 : ¬acc10_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g103 | g103 | g103 | g103
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_90) (g103)) (hv _ _ sub_36_54)), hv _ _ sub_0_54⟩
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_89) (g103)) (hv _ _ sub_36_54)), hv _ _ sub_0_54⟩
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_75) (g103)) (hv _ _ sub_36_54)), hv _ _ sub_0_54⟩
  · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_27) (g103)) (hv _ _ sub_36_54)), hv _ _ sub_0_54⟩
theorem cl141 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc3_1 v) (h1 : ¬acc12_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g104 | g104 | g104 | g104
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_90) (g104)) (hv _ _ sub_36_55)), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_89) (g104)) (hv _ _ sub_36_55)), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_75) (g104)) (hv _ _ sub_36_55)), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_8_27) (g104)) (hv _ _ sub_36_55)), hv _ _ sub_0_55⟩
theorem cl142 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_1 v) (h1 : ¬acc4_0 v) : False := by
  rcases le_or_gt (v s89) (v s36) with g105 | g105
  · exact h0 ⟨Or.inr (Or.inl (g105)), hv _ _ sub_0_36⟩
  · exact h1 ⟨Or.inl (le_of_lt (g105)), hv _ _ sub_0_89⟩
theorem cl143 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc3_2 v) (h1 : ¬acc7_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g106 | g106
  · rcases h0a with g107 | g107 | g107 | g107
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_74_90) (g107)) (hv _ _ sub_128_144)), Or.inl (le_trans (g106) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inr (Or.inl (le_trans (le_trans (hv _ _ sub_73_89) (g107)) (hv _ _ sub_128_144))), Or.inl (le_trans (g106) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_74_75) (g107)) (hv _ _ sub_128_144)), Or.inl (le_trans (g106) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inr (Or.inr (le_trans (le_trans (hv _ _ sub_11_27) (g107)) (hv _ _ sub_128_144))), Or.inl (le_trans (g106) (hv _ _ sub_128_144))⟩
  · rcases h0a with g108 | g108 | g108 | g108
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_74_90) (g108)) (hv _ _ sub_128_144)), Or.inr (le_trans (g106) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inr (Or.inl (le_trans (le_trans (hv _ _ sub_73_89) (g108)) (hv _ _ sub_128_144))), Or.inr (le_trans (g106) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_74_75) (g108)) (hv _ _ sub_128_144)), Or.inr (le_trans (g106) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inr (Or.inr (le_trans (le_trans (hv _ _ sub_11_27) (g108)) (hv _ _ sub_128_144))), Or.inr (le_trans (g106) (hv _ _ sub_128_144))⟩
theorem cl145 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc3_2 v) (h1 : ¬acc9_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g109 | g109
  · rcases h0a with g110 | g110 | g110 | g110
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_90) (g110)) (hv _ _ sub_128_146)), Or.inl (le_trans (g109) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_89) (g110)) (hv _ _ sub_128_146)), Or.inl (le_trans (g109) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_75) (g110)) (hv _ _ sub_128_146)), Or.inl (le_trans (g109) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_27) (g110)) (hv _ _ sub_128_146)), Or.inl (le_trans (g109) (hv _ _ sub_128_146))⟩
  · rcases h0a with g111 | g111 | g111 | g111
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_90) (g111)) (hv _ _ sub_128_146)), Or.inr (le_trans (g109) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_89) (g111)) (hv _ _ sub_128_146)), Or.inr (le_trans (g109) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_75) (g111)) (hv _ _ sub_128_146)), Or.inr (le_trans (g109) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_27) (g111)) (hv _ _ sub_128_146)), Or.inr (le_trans (g109) (hv _ _ sub_128_146))⟩
theorem cl146 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_2 v) (h1 : ¬acc5_0 v) : False := by
  rcases le_or_gt (v s128) (v s79) with g112 | g112
  · exact h1 ⟨Or.inl (g112), hv _ _ sub_0_79⟩
  · exact h0 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_75_79) (g112))))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_4_79) (g112)))⟩
theorem cl147 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc4_0 v) (h1 : ¬acc4_1 v) : False := by
  rcases le_or_gt (v s36) (v s89) with g113 | g113
  · exact h0 ⟨Or.inl (g113), hv _ _ sub_0_89⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_73_89) (g113)) (hv _ _ sub_36_38))), hv _ _ sub_0_38⟩
theorem cl148 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc4_0 v) (h1 : ¬acc5_0 v) : False := by
  rcases le_or_gt (v s6) (v s89) with g114 | g114
  · exact h0 ⟨Or.inr (g114), hv _ _ sub_0_89⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_89) (g114)) (hv _ _ sub_6_79))), hv _ _ sub_0_79⟩
theorem cl149 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc4_0 v) (h1 : ¬acc7_1 v) : False := by
  rcases le_or_gt (v s36) (v s89) with g115 | g115
  · exact h0 ⟨Or.inl (g115), hv _ _ sub_0_89⟩
  · exact h1 ⟨Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_73_89) (g115)))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_16_89) (g115)))⟩
theorem cl154 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc4_0 v) (h1 : ¬acc11_1 v) : False := by
  rcases le_or_gt (v s36) (v s89) with g116 | g116
  · exact h0 ⟨Or.inl (g116), hv _ _ sub_0_89⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_89) (g116)) (hv _ _ sub_36_38))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_89) (g116)) (hv _ _ sub_36_38)))⟩
theorem cl157 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc4_0 v) (h1 : ¬acc13_0 v) : False := by
  rcases le_or_gt (v s36) (v s89) with g117 | g117
  · exact h0 ⟨Or.inl (g117), hv _ _ sub_0_89⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_89) (g117)) (hv _ _ sub_36_47))), hv _ _ sub_0_47⟩
theorem cl160 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc4_0 v) (h1 : acc15_1 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g118 | g118 | g118
  · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_38) (g118)) (hv _ _ sub_72_89)), hv _ _ sub_0_89⟩
  · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_37) (g118)) (hv _ _ sub_72_89)), hv _ _ sub_0_89⟩
  · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_6_7) (g118)) (hv _ _ sub_72_89)), hv _ _ sub_0_89⟩
theorem cl163 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc4_1 v) (h1 : ¬acc10_0 v) : False := by
  rcases le_or_gt (v s73) (v s38) with g119 | g119
  · exact h0 ⟨Or.inl (g119), hv _ _ sub_0_38⟩
  · exact h1 ⟨Or.inl (le_of_lt (g119)), hv _ _ sub_0_73⟩
theorem cl164 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc4_2 v) (h1 : ¬acc8_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g120 | g120
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_73) (g120)) (hv _ _ sub_128_150)), hv _ _ sub_0_150⟩
  · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_25) (g120)) (hv _ _ sub_128_150)), hv _ _ sub_0_150⟩
theorem cl165 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc4_2 v) (h1 : ¬acc9_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g121 | g121
  · rcases h0b with g122 | g122
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_73) (g121)) (hv _ _ sub_128_146)), Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g122)) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_73) (g121)) (hv _ _ sub_128_146)), Or.inr (le_trans (le_trans (hv _ _ sub_4_6) (g122)) (hv _ _ sub_128_146))⟩
  · rcases h0b with g123 | g123
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_25) (g121)) (hv _ _ sub_128_146)), Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g123)) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_25) (g121)) (hv _ _ sub_128_146)), Or.inr (le_trans (le_trans (hv _ _ sub_4_6) (g123)) (hv _ _ sub_128_146))⟩
theorem cl166 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc4_2 v) (h1 : ¬acc11_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g124 | g124
  · rcases h0b with g125 | g125
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_73) (g124)) (hv _ _ sub_128_144)), Or.inl (le_trans (g125) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_73) (g124)) (hv _ _ sub_128_144)), Or.inr (le_trans (g125) (hv _ _ sub_128_144))⟩
  · rcases h0b with g126 | g126
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_25) (g124)) (hv _ _ sub_128_144)), Or.inl (le_trans (g126) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_25) (g124)) (hv _ _ sub_128_144)), Or.inr (le_trans (g126) (hv _ _ sub_128_144))⟩
theorem cl167 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc4_2 v) (h1 : ¬acc5_0 v) : False := by
  rcases le_or_gt (v s128) (v s79) with g127 | g127
  · exact h1 ⟨Or.inl (g127), hv _ _ sub_0_79⟩
  · exact h0 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_73_79) (g127))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_6_79) (g127)))⟩
theorem cl168 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_0 v) (h1 : ¬acc5_1 v) : False := by
  rcases le_or_gt (v s128) (v s79) with g128 | g128
  · exact h0 ⟨Or.inl (g128), hv _ _ sub_0_79⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_78_79) (g128)) (hv _ _ sub_128_144))), hv _ _ sub_0_144⟩
theorem cl172 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_0 v) (h1 : ¬acc7_2 v) : False := by
  rcases le_or_gt (v s128) (v s79) with g129 | g129
  · exact h0 ⟨Or.inl (g129), hv _ _ sub_0_79⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_74_79) (g129)) (hv _ _ sub_128_144))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_4_79) (g129)) (hv _ _ sub_128_144)))⟩
theorem cl176 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_0 v) (h1 : ¬acc9_1 v) : False := by
  rcases le_or_gt (v s128) (v s79) with g130 | g130
  · exact h0 ⟨Or.inl (g130), hv _ _ sub_0_79⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_79) (g130)) (hv _ _ sub_128_146))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_4_79) (g130)) (hv _ _ sub_128_146)))⟩
theorem cl177 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_0 v) (h1 : ¬acc10_1 v) : False := by
  rcases le_or_gt (v s16) (v s79) with g131 | g131
  · exact h0 ⟨Or.inr (g131), hv _ _ sub_0_79⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_79) (g131)) (hv _ _ sub_16_54))), hv _ _ sub_0_54⟩
theorem cl178 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_0 v) (h1 : acc11_0 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g132 | g132
  · exact h0 ⟨Or.inl (le_trans (g132) (hv _ _ sub_73_79)), hv _ _ sub_0_79⟩
  · exact h0 ⟨Or.inr (le_trans (g132) (hv _ _ sub_73_79)), hv _ _ sub_0_79⟩
theorem cl179 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_0 v) (h1 : ¬acc11_2 v) : False := by
  rcases le_or_gt (v s128) (v s79) with g133 | g133
  · exact h0 ⟨Or.inl (g133), hv _ _ sub_0_79⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_79) (g133)) (hv _ _ sub_128_144))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_6_79) (g133)) (hv _ _ sub_128_144)))⟩
theorem cl180 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_0 v) (h1 : ¬acc12_0 v) : False := by
  rcases le_or_gt (v s16) (v s79) with g134 | g134
  · exact h0 ⟨Or.inr (g134), hv _ _ sub_0_79⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_79) (g134)) (hv _ _ sub_16_55))), hv _ _ sub_0_55⟩
theorem cl181 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_0 v) (h1 : ¬acc13_1 v) : False := by
  rcases le_or_gt (v s128) (v s79) with g135 | g135
  · exact h0 ⟨Or.inl (g135), hv _ _ sub_0_79⟩
  · exact h1 ⟨Or.inr (Or.inr (Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_15_79) (g135)) (hv _ _ sub_128_144))))), hv _ _ sub_0_144⟩
theorem cl183 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_0 v) (h1 : ¬acc14_1 v) : False := by
  rcases le_or_gt (v s128) (v s79) with g136 | g136
  · exact h0 ⟨Or.inl (g136), hv _ _ sub_0_79⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_13_79) (g136)) (hv _ _ sub_128_146))), hv _ _ sub_0_146⟩
theorem cl185 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_0 v) (h1 : acc15_1 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g137 | g137
  · exact h0 ⟨Or.inl (le_trans (g137) (hv _ _ sub_72_79)), hv _ _ sub_0_79⟩
  · exact h0 ⟨Or.inr (le_trans (g137) (hv _ _ sub_72_79)), hv _ _ sub_0_79⟩
theorem cl186 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_0 v) (h1 : ¬acc15_2 v) : False := by
  rcases le_or_gt (v s128) (v s79) with g138 | g138
  · exact h0 ⟨Or.inl (g138), hv _ _ sub_0_79⟩
  · exact h1 ⟨Or.inr (Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_7_79) (g138)) (hv _ _ sub_128_144)))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_79) (g138)) (hv _ _ sub_128_144)))⟩
theorem cl192 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_1 v) (h1 : ¬acc6_0 v) : False := by
  rcases le_or_gt (v s77) (v s144) with g139 | g139
  · exact h0 ⟨Or.inr (Or.inl (g139)), hv _ _ sub_0_144⟩
  · exact h1 ⟨Or.inl (le_of_lt (g139)), hv _ _ sub_0_77⟩
theorem cl193 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_1 v) (h1 : ¬acc13_0 v) : False := by
  rcases le_or_gt (v s15) (v s144) with g140 | g140
  · exact h0 ⟨Or.inr (Or.inr (Or.inr (g140))), hv _ _ sub_0_144⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_144) (g140)) (hv _ _ sub_15_47))), hv _ _ sub_0_47⟩
theorem cl194 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc5_2 v) (h1 : ¬acc7_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g141 | g141
  · rcases h0a with g142 | g142 | g142 | g142
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_74_78) (g142)) (hv _ _ sub_32_36)), Or.inl (le_trans (g141) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inr (Or.inl (le_trans (le_trans (hv _ _ sub_73_77) (g142)) (hv _ _ sub_32_36))), Or.inl (le_trans (g141) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_74_75) (g142)) (hv _ _ sub_32_36)), Or.inl (le_trans (g141) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inr (Or.inr (le_trans (le_trans (hv _ _ sub_11_15) (g142)) (hv _ _ sub_32_36))), Or.inl (le_trans (g141) (hv _ _ sub_32_36))⟩
  · rcases h0a with g143 | g143 | g143 | g143
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_74_78) (g143)) (hv _ _ sub_32_36)), Or.inr (le_trans (g141) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inr (Or.inl (le_trans (le_trans (hv _ _ sub_73_77) (g143)) (hv _ _ sub_32_36))), Or.inr (le_trans (g141) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_74_75) (g143)) (hv _ _ sub_32_36)), Or.inr (le_trans (g141) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inr (Or.inr (le_trans (le_trans (hv _ _ sub_11_15) (g143)) (hv _ _ sub_32_36))), Or.inr (le_trans (g141) (hv _ _ sub_32_36))⟩
theorem cl200 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_0 v) (h1 : ¬acc6_1 v) : False := by
  rcases le_or_gt (v s144) (v s77) with g144 | g144
  · exact h0 ⟨Or.inl (g144), hv _ _ sub_0_77⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_73_77) (g144)) (hv _ _ sub_144_146))), hv _ _ sub_0_146⟩
theorem cl201 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_0 v) (h1 : ¬acc7_2 v) : False := by
  rcases le_or_gt (v s144) (v s77) with g145 | g145
  · exact h0 ⟨Or.inl (g145), hv _ _ sub_0_77⟩
  · exact h1 ⟨Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_73_77) (g145)))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_4_77) (g145)))⟩
theorem cl205 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_0 v) (h1 : ¬acc9_1 v) : False := by
  rcases le_or_gt (v s144) (v s77) with g146 | g146
  · exact h0 ⟨Or.inl (g146), hv _ _ sub_0_77⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_77) (g146)) (hv _ _ sub_144_146))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_4_77) (g146)) (hv _ _ sub_144_146)))⟩
theorem cl206 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_0 v) (h1 : ¬acc10_1 v) : False := by
  rcases le_or_gt (v s18) (v s77) with g147 | g147
  · exact h0 ⟨Or.inr (g147), hv _ _ sub_0_77⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_77) (g147)) (hv _ _ sub_18_54))), hv _ _ sub_0_54⟩
theorem cl208 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_0 v) (h1 : ¬acc14_1 v) : False := by
  rcases le_or_gt (v s144) (v s77) with g148 | g148
  · exact h0 ⟨Or.inl (g148), hv _ _ sub_0_77⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_13_77) (g148)) (hv _ _ sub_144_146))), hv _ _ sub_0_146⟩
theorem cl210 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_0 v) (h1 : ¬acc16_1 v) : False := by
  rcases le_or_gt (v s144) (v s77) with g149 | g149
  · exact h0 ⟨Or.inl (g149), hv _ _ sub_0_77⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_5_77) (g149)) (hv _ _ sub_144_154))), hv _ _ sub_0_154⟩
theorem cl212 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_0 v) (h1 : ¬acc17_1 v) : False := by
  rcases le_or_gt (v s144) (v s77) with g150 | g150
  · exact h0 ⟨Or.inl (g150), hv _ _ sub_0_77⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_5_77) (g150)) (hv _ _ sub_144_146))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_77) (g150)) (hv _ _ sub_144_146)))⟩
theorem cl213 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_0 v) (h1 : acc17_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g151 | g151
  · exact h0 ⟨Or.inl (le_trans (g151) (hv _ _ sub_72_77)), hv _ _ sub_0_77⟩
  · exact h0 ⟨Or.inr (le_trans (g151) (hv _ _ sub_72_77)), hv _ _ sub_0_77⟩
theorem cl215 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_1 v) (h1 : ¬acc8_0 v) : False := by
  rcases le_or_gt (v s73) (v s146) with g152 | g152
  · exact h0 ⟨Or.inl (g152), hv _ _ sub_0_146⟩
  · exact h1 ⟨Or.inl (le_of_lt (g152)), hv _ _ sub_0_73⟩
theorem cl216 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_1 v) (h1 : ¬acc13_0 v) : False := by
  rcases le_or_gt (v s13) (v s146) with g153 | g153
  · exact h0 ⟨Or.inr (g153), hv _ _ sub_0_146⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_146) (g153)) (hv _ _ sub_13_47))), hv _ _ sub_0_47⟩
theorem cl218 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc6_2 v) (h1 : ¬acc9_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g154 | g154
  · rcases h0b with g155 | g155
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_73) (g154)) (hv _ _ sub_32_36)), Or.inl (le_trans (g155) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_73) (g154)) (hv _ _ sub_32_36)), Or.inr (le_trans (g155) (hv _ _ sub_32_36))⟩
  · rcases h0b with g156 | g156
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_13) (g154)) (hv _ _ sub_32_36)), Or.inl (le_trans (g156) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_13) (g154)) (hv _ _ sub_32_36)), Or.inr (le_trans (g156) (hv _ _ sub_32_36))⟩
theorem cl226 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc7_0 v) (h1 : ¬acc8_1 v) : False := by
  rcases le_or_gt (v s72) (v s150) with g157 | g157
  · exact h1 ⟨Or.inl (g157), hv _ _ sub_0_150⟩
  · exact h0 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_4_150) (g157)) (hv _ _ sub_72_75))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_150) (g157)) (hv _ _ sub_72_75)))⟩
theorem cl227 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc7_0 v) (h1 : acc9_0 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g158 | g158
  · rcases h1b with g159 | g159
    · exact h0 ⟨Or.inl (le_trans (g159) (hv _ _ sub_73_75)), Or.inl (le_trans (le_trans (hv _ _ sub_128_144) (g158)) (hv _ _ sub_73_75))⟩
    · exact h0 ⟨Or.inr (le_trans (g159) (hv _ _ sub_73_75)), Or.inl (le_trans (le_trans (hv _ _ sub_128_144) (g158)) (hv _ _ sub_73_75))⟩
  · rcases h1b with g160 | g160
    · exact h0 ⟨Or.inl (le_trans (g160) (hv _ _ sub_73_75)), Or.inr (le_trans (le_trans (hv _ _ sub_16_18) (g158)) (hv _ _ sub_73_75))⟩
    · exact h0 ⟨Or.inr (le_trans (g160) (hv _ _ sub_73_75)), Or.inr (le_trans (le_trans (hv _ _ sub_16_18) (g158)) (hv _ _ sub_73_75))⟩
theorem cl228 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc7_0 v) (h1 : ¬acc10_1 v) : False := by
  rcases le_or_gt (v s72) (v s54) with g161 | g161
  · exact h1 ⟨Or.inl (g161), hv _ _ sub_0_54⟩
  · exact h0 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_54) (g161)) (hv _ _ sub_72_75))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_54) (g161)) (hv _ _ sub_72_75)))⟩
theorem cl229 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc7_0 v) (h1 : acc11_0 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g162 | g162
  · rcases h1b with g163 | g163
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g162)) (hv _ _ sub_73_75)), Or.inl (le_trans (g163) (hv _ _ sub_73_75))⟩
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g162)) (hv _ _ sub_73_75)), Or.inr (le_trans (g163) (hv _ _ sub_73_75))⟩
  · rcases h1b with g164 | g164
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_4_6) (g162)) (hv _ _ sub_73_75)), Or.inl (le_trans (g164) (hv _ _ sub_73_75))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_4_6) (g162)) (hv _ _ sub_73_75)), Or.inr (le_trans (g164) (hv _ _ sub_73_75))⟩
theorem cl230 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc7_0 v) (h1 : ¬acc12_0 v) : False := by
  rcases le_or_gt (v s64) (v s55) with g165 | g165
  · exact h1 ⟨Or.inl (g165), hv _ _ sub_0_55⟩
  · exact h0 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_55) (g165)) (hv _ _ sub_64_75))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_55) (g165)) (hv _ _ sub_64_75)))⟩
theorem cl237 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc7_1 v) (h1 : ¬acc11_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g166 | g166
  · rcases h0a with g167 | g167 | g167
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_74) (g167)) (hv _ _ sub_36_38)), Or.inl (le_trans (g166) (hv _ _ sub_36_38))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_73) (g167)) (hv _ _ sub_36_38)), Or.inl (le_trans (g166) (hv _ _ sub_36_38))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_11) (g167)) (hv _ _ sub_36_38)), Or.inl (le_trans (g166) (hv _ _ sub_36_38))⟩
  · rcases h0a with g168 | g168 | g168
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_74) (g168)) (hv _ _ sub_36_38)), Or.inr (le_trans (g166) (hv _ _ sub_36_38))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_73) (g168)) (hv _ _ sub_36_38)), Or.inr (le_trans (g166) (hv _ _ sub_36_38))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_11) (g168)) (hv _ _ sub_36_38)), Or.inr (le_trans (g166) (hv _ _ sub_36_38))⟩
theorem cl240 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc7_1 v) (h1 : ¬acc15_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g169 | g169
  · rcases h0a with g170 | g170 | g170
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_74) (g170)) (hv _ _ sub_36_39)), Or.inl (le_trans (g169) (hv _ _ sub_36_39))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_73) (g170)) (hv _ _ sub_36_39)), Or.inl (le_trans (g169) (hv _ _ sub_36_39))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_8_11) (g170)) (hv _ _ sub_36_39)), Or.inl (le_trans (g169) (hv _ _ sub_36_39))⟩
  · rcases h0a with g171 | g171 | g171
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_74) (g171)) (hv _ _ sub_36_39)), Or.inr (le_trans (g169) (hv _ _ sub_36_39))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_73) (g171)) (hv _ _ sub_36_39)), Or.inr (le_trans (g169) (hv _ _ sub_36_39))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_8_11) (g171)) (hv _ _ sub_36_39)), Or.inr (le_trans (g169) (hv _ _ sub_36_39))⟩
theorem cl241 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc7_2 v) (h1 : ¬acc8_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g172 | g172 | g172
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_74) (g172)) (hv _ _ sub_144_150)), hv _ _ sub_0_150⟩
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_73) (g172)) (hv _ _ sub_144_150)), hv _ _ sub_0_150⟩
  · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_11) (g172)) (hv _ _ sub_144_150)), hv _ _ sub_0_150⟩
theorem cl242 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc7_2 v) (h1 : ¬acc9_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g173 | g173
  · rcases h0a with g174 | g174 | g174
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_74) (g174)) (hv _ _ sub_144_146)), Or.inl (le_trans (g173) (hv _ _ sub_144_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_73) (g174)) (hv _ _ sub_144_146)), Or.inl (le_trans (g173) (hv _ _ sub_144_146))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_11) (g174)) (hv _ _ sub_144_146)), Or.inl (le_trans (g173) (hv _ _ sub_144_146))⟩
  · rcases h0a with g175 | g175 | g175
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_74) (g175)) (hv _ _ sub_144_146)), Or.inr (le_trans (g173) (hv _ _ sub_144_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_72_73) (g175)) (hv _ _ sub_144_146)), Or.inr (le_trans (g173) (hv _ _ sub_144_146))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_9_11) (g175)) (hv _ _ sub_144_146)), Or.inr (le_trans (g173) (hv _ _ sub_144_146))⟩
theorem cl243 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc7_2 v) (h1 : ¬acc13_0 v) : False := by
  rcases le_or_gt (v s128) (v s47) with g176 | g176
  · exact h1 ⟨Or.inl (g176), hv _ _ sub_0_47⟩
  · exact h0 ⟨Or.inr (Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_11_47) (g176)) (hv _ _ sub_128_144)))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_47) (g176)) (hv _ _ sub_128_144)))⟩
theorem cl244 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_0 v) (h1 : ¬acc8_1 v) : False := by
  rcases le_or_gt (v s146) (v s73) with g177 | g177
  · exact h0 ⟨Or.inl (g177), hv _ _ sub_0_73⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_73) (g177)) (hv _ _ sub_146_150))), hv _ _ sub_0_150⟩
theorem cl247 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_1 v) (h1 : ¬acc9_0 v) : False := by
  rcases le_or_gt (v s72) (v s150) with g178 | g178
  · exact h0 ⟨Or.inl (g178), hv _ _ sub_0_150⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_144_150) (g178)) (hv _ _ sub_72_73))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_4_150) (g178)) (hv _ _ sub_72_73)))⟩
theorem cl248 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_1 v) (h1 : acc9_1 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g179 | g179
  · exact h0 ⟨Or.inl (le_trans (g179) (hv _ _ sub_146_150)), hv _ _ sub_0_150⟩
  · exact h0 ⟨Or.inr (le_trans (g179) (hv _ _ sub_146_150)), hv _ _ sub_0_150⟩
theorem cl249 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_1 v) (h1 : ¬acc10_0 v) : False := by
  rcases le_or_gt (v s72) (v s150) with g180 | g180
  · exact h0 ⟨Or.inl (g180), hv _ _ sub_0_150⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_22_150) (g180)) (hv _ _ sub_72_73))), hv _ _ sub_0_73⟩
theorem cl250 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_1 v) (h1 : acc10_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g181 | g181
  · exact h0 ⟨Or.inl (le_trans (g181) (hv _ _ sub_128_150)), hv _ _ sub_0_150⟩
  · exact h0 ⟨Or.inr (le_trans (g181) (hv _ _ sub_128_150)), hv _ _ sub_0_150⟩
theorem cl251 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_1 v) (h1 : ¬acc11_0 v) : False := by
  rcases le_or_gt (v s72) (v s150) with g182 | g182
  · exact h0 ⟨Or.inl (g182), hv _ _ sub_0_150⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_6_150) (g182)) (hv _ _ sub_72_73))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_150) (g182)) (hv _ _ sub_72_73)))⟩
theorem cl252 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_1 v) (h1 : acc11_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g183 | g183
  · exact h0 ⟨Or.inl (le_trans (g183) (hv _ _ sub_144_150)), hv _ _ sub_0_150⟩
  · exact h0 ⟨Or.inr (le_trans (g183) (hv _ _ sub_144_150)), hv _ _ sub_0_150⟩
theorem cl253 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_1 v) (h1 : ¬acc13_0 v) : False := by
  rcases le_or_gt (v s9) (v s150) with g184 | g184
  · exact h0 ⟨Or.inr (g184), hv _ _ sub_0_150⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_150) (g184)) (hv _ _ sub_9_47))), hv _ _ sub_0_47⟩
theorem cl254 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_1 v) (h1 : ¬acc14_0 v) : False := by
  rcases le_or_gt (v s9) (v s150) with g185 | g185
  · exact h0 ⟨Or.inr (g185), hv _ _ sub_0_150⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_144_150) (g185)) (hv _ _ sub_9_45))), hv _ _ sub_0_45⟩
theorem cl255 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc8_2 v) (h1 : ¬acc9_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g186 | g186
  · rcases h0b with g187 | g187
    · exact h1 ⟨Or.inl (le_trans (g186) (hv _ _ sub_32_36)), Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g187)) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inl (le_trans (g186) (hv _ _ sub_32_36)), Or.inr (le_trans (le_trans (hv _ _ sub_18_22) (g187)) (hv _ _ sub_32_36))⟩
  · rcases h0b with g188 | g188
    · exact h1 ⟨Or.inr (le_trans (g186) (hv _ _ sub_32_36)), Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g188)) (hv _ _ sub_32_36))⟩
    · exact h1 ⟨Or.inr (le_trans (g186) (hv _ _ sub_32_36)), Or.inr (le_trans (le_trans (hv _ _ sub_18_22) (g188)) (hv _ _ sub_32_36))⟩
theorem cl256 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc8_2 v) (h1 : ¬acc10_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g189 | g189
  · exact h1 ⟨Or.inl (le_trans (g189) (hv _ _ sub_32_54)), hv _ _ sub_0_54⟩
  · exact h1 ⟨Or.inr (le_trans (g189) (hv _ _ sub_32_54)), hv _ _ sub_0_54⟩
theorem cl257 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc8_2 v) (h1 : ¬acc11_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g190 | g190
  · rcases h0b with g191 | g191
    · exact h1 ⟨Or.inl (le_trans (g190) (hv _ _ sub_32_38)), Or.inl (le_trans (le_trans (hv _ _ sub_128_146) (g191)) (hv _ _ sub_32_38))⟩
    · exact h1 ⟨Or.inl (le_trans (g190) (hv _ _ sub_32_38)), Or.inr (le_trans (le_trans (hv _ _ sub_16_22) (g191)) (hv _ _ sub_32_38))⟩
  · rcases h0b with g192 | g192
    · exact h1 ⟨Or.inr (le_trans (g190) (hv _ _ sub_32_38)), Or.inl (le_trans (le_trans (hv _ _ sub_128_146) (g192)) (hv _ _ sub_32_38))⟩
    · exact h1 ⟨Or.inr (le_trans (g190) (hv _ _ sub_32_38)), Or.inr (le_trans (le_trans (hv _ _ sub_16_22) (g192)) (hv _ _ sub_32_38))⟩
theorem cl260 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc8_2 v) (h1 : ¬acc14_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g193 | g193
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g193)) (hv _ _ sub_32_45)), hv _ _ sub_0_45⟩
  · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_22) (g193)) (hv _ _ sub_32_45)), hv _ _ sub_0_45⟩
theorem cl261 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc8_2 v) (h1 : ¬acc15_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g194 | g194
  · rcases h0b with g195 | g195
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g194)) (hv _ _ sub_32_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_146) (g195)) (hv _ _ sub_32_39))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g194)) (hv _ _ sub_32_39)), Or.inr (le_trans (le_trans (hv _ _ sub_16_22) (g195)) (hv _ _ sub_32_39))⟩
  · rcases h0b with g196 | g196
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g194)) (hv _ _ sub_32_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_146) (g196)) (hv _ _ sub_32_39))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g194)) (hv _ _ sub_32_39)), Or.inr (le_trans (le_trans (hv _ _ sub_16_22) (g196)) (hv _ _ sub_32_39))⟩
theorem cl262 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc8_2 v) (h1 : ¬acc17_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g197 | g197
  · rcases h0b with g198 | g198
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g198)) (hv _ _ sub_32_37)), Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g197)) (hv _ _ sub_32_37))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_22) (g198)) (hv _ _ sub_32_37)), Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g197)) (hv _ _ sub_32_37))⟩
  · rcases h0b with g199 | g199
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g199)) (hv _ _ sub_32_37)), Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g197)) (hv _ _ sub_32_37))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_22) (g199)) (hv _ _ sub_32_37)), Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g197)) (hv _ _ sub_32_37))⟩
theorem cl263 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_0 v) (h1 : ¬acc10_1 v) : False := by
  rcases le_or_gt (v s72) (v s54) with g200 | g200
  · exact h1 ⟨Or.inl (g200), hv _ _ sub_0_54⟩
  · exact h0 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_18_54) (g200)) (hv _ _ sub_72_73))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_54) (g200)) (hv _ _ sub_72_73)))⟩
theorem cl264 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_0 v) (h1 : ¬acc12_0 v) : False := by
  rcases le_or_gt (v s64) (v s55) with g201 | g201
  · exact h1 ⟨Or.inl (g201), hv _ _ sub_0_55⟩
  · exact h0 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_18_55) (g201)) (hv _ _ sub_64_73))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_55) (g201)) (hv _ _ sub_64_73)))⟩
theorem cl265 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_0 v) (h1 : acc14_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g202 | g202
  · rcases h1b with g203 | g203
    · exact h0 ⟨Or.inl (le_trans (g203) (hv _ _ sub_64_73)), Or.inl (le_trans (le_trans (hv _ _ sub_32_37) (g202)) (hv _ _ sub_64_73))⟩
    · exact h0 ⟨Or.inr (le_trans (g203) (hv _ _ sub_64_73)), Or.inl (le_trans (le_trans (hv _ _ sub_32_37) (g202)) (hv _ _ sub_64_73))⟩
  · rcases h1b with g204 | g204
    · exact h0 ⟨Or.inl (le_trans (g204) (hv _ _ sub_64_73)), Or.inr (le_trans (le_trans (hv _ _ sub_4_13) (g202)) (hv _ _ sub_64_73))⟩
    · exact h0 ⟨Or.inr (le_trans (g204) (hv _ _ sub_64_73)), Or.inr (le_trans (le_trans (hv _ _ sub_4_13) (g202)) (hv _ _ sub_64_73))⟩
theorem cl266 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_0 v) (h1 : acc16_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g205 | g205
  · rcases h1b with g206 | g206
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g206)) (hv _ _ sub_64_73)), Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g205)) (hv _ _ sub_64_73))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_26) (g206)) (hv _ _ sub_64_73)), Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g205)) (hv _ _ sub_64_73))⟩
  · rcases h1b with g207 | g207
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g207)) (hv _ _ sub_64_73)), Or.inr (le_trans (le_trans (hv _ _ sub_4_5) (g205)) (hv _ _ sub_64_73))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_18_26) (g207)) (hv _ _ sub_64_73)), Or.inr (le_trans (le_trans (hv _ _ sub_4_5) (g205)) (hv _ _ sub_64_73))⟩
theorem cl267 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_0 v) (h1 : acc17_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g208 | g208
  · rcases h1b with g209 | g209
    · exact h0 ⟨Or.inl (le_trans (g209) (hv _ _ sub_72_73)), Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g208)) (hv _ _ sub_72_73))⟩
    · exact h0 ⟨Or.inr (le_trans (g209) (hv _ _ sub_72_73)), Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g208)) (hv _ _ sub_72_73))⟩
  · rcases h1b with g210 | g210
    · exact h0 ⟨Or.inl (le_trans (g210) (hv _ _ sub_72_73)), Or.inr (le_trans (le_trans (hv _ _ sub_4_5) (g208)) (hv _ _ sub_72_73))⟩
    · exact h0 ⟨Or.inr (le_trans (g210) (hv _ _ sub_72_73)), Or.inr (le_trans (le_trans (hv _ _ sub_4_5) (g208)) (hv _ _ sub_72_73))⟩
theorem cl268 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_1 v) (h1 : acc10_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g211 | g211
  · rcases h1b with g212 | g212
    · exact h0 ⟨Or.inl (le_trans (g211) (hv _ _ sub_128_146)), Or.inl (le_trans (le_trans (hv _ _ sub_32_38) (g212)) (hv _ _ sub_128_146))⟩
    · exact h0 ⟨Or.inl (le_trans (g211) (hv _ _ sub_128_146)), Or.inr (le_trans (le_trans (hv _ _ sub_4_22) (g212)) (hv _ _ sub_128_146))⟩
  · rcases h1b with g213 | g213
    · exact h0 ⟨Or.inr (le_trans (g211) (hv _ _ sub_128_146)), Or.inl (le_trans (le_trans (hv _ _ sub_32_38) (g213)) (hv _ _ sub_128_146))⟩
    · exact h0 ⟨Or.inr (le_trans (g211) (hv _ _ sub_128_146)), Or.inr (le_trans (le_trans (hv _ _ sub_4_22) (g213)) (hv _ _ sub_128_146))⟩
theorem cl269 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_1 v) (h1 : acc11_2 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g214 | g214
  · rcases h1b with g215 | g215
    · exact h0 ⟨Or.inl (le_trans (g214) (hv _ _ sub_144_146)), Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g215)) (hv _ _ sub_144_146))⟩
    · exact h0 ⟨Or.inl (le_trans (g214) (hv _ _ sub_144_146)), Or.inr (le_trans (le_trans (hv _ _ sub_4_6) (g215)) (hv _ _ sub_144_146))⟩
  · rcases h1b with g216 | g216
    · exact h0 ⟨Or.inr (le_trans (g214) (hv _ _ sub_144_146)), Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g216)) (hv _ _ sub_144_146))⟩
    · exact h0 ⟨Or.inr (le_trans (g214) (hv _ _ sub_144_146)), Or.inr (le_trans (le_trans (hv _ _ sub_4_6) (g216)) (hv _ _ sub_144_146))⟩
theorem cl271 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_1 v) (h1 : ¬acc14_0 v) : False := by
  rcases le_or_gt (v s144) (v s45) with g217 | g217
  · exact h1 ⟨Or.inl (g217), hv _ _ sub_0_45⟩
  · exact h0 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_9_45) (g217)) (hv _ _ sub_144_146))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_45) (g217)) (hv _ _ sub_144_146)))⟩
theorem cl272 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc9_2 v) (h1 : ¬acc10_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g218 | g218
  · exact h1 ⟨Or.inl (le_trans (g218) (hv _ _ sub_36_54)), hv _ _ sub_0_54⟩
  · exact h1 ⟨Or.inr (le_trans (g218) (hv _ _ sub_36_54)), hv _ _ sub_0_54⟩
theorem cl273 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc9_2 v) (h1 : ¬acc11_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g219 | g219
  · rcases h0b with g220 | g220
    · exact h1 ⟨Or.inl (le_trans (g219) (hv _ _ sub_36_38)), Or.inl (le_trans (le_trans (hv _ _ sub_128_144) (g220)) (hv _ _ sub_36_38))⟩
    · exact h1 ⟨Or.inl (le_trans (g219) (hv _ _ sub_36_38)), Or.inr (le_trans (le_trans (hv _ _ sub_16_18) (g220)) (hv _ _ sub_36_38))⟩
  · rcases h0b with g221 | g221
    · exact h1 ⟨Or.inr (le_trans (g219) (hv _ _ sub_36_38)), Or.inl (le_trans (le_trans (hv _ _ sub_128_144) (g221)) (hv _ _ sub_36_38))⟩
    · exact h1 ⟨Or.inr (le_trans (g219) (hv _ _ sub_36_38)), Or.inr (le_trans (le_trans (hv _ _ sub_16_18) (g221)) (hv _ _ sub_36_38))⟩
theorem cl276 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc9_2 v) (h1 : ¬acc14_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g222 | g222
  · exact h1 ⟨Or.inl (le_trans (g222) (hv _ _ sub_36_45)), hv _ _ sub_0_45⟩
  · exact h1 ⟨Or.inr (le_trans (g222) (hv _ _ sub_36_45)), hv _ _ sub_0_45⟩
theorem cl277 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc9_2 v) (h1 : ¬acc15_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g223 | g223
  · rcases h0b with g224 | g224
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g223)) (hv _ _ sub_36_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_144) (g224)) (hv _ _ sub_36_39))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g223)) (hv _ _ sub_36_39)), Or.inr (le_trans (le_trans (hv _ _ sub_16_18) (g224)) (hv _ _ sub_36_39))⟩
  · rcases h0b with g225 | g225
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g223)) (hv _ _ sub_36_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_144) (g225)) (hv _ _ sub_36_39))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g223)) (hv _ _ sub_36_39)), Or.inr (le_trans (le_trans (hv _ _ sub_16_18) (g225)) (hv _ _ sub_36_39))⟩
theorem cl278 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc9_2 v) (h1 : ¬acc17_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g226 | g226
  · rcases h0b with g227 | g227
    · exact h1 ⟨Or.inl (le_trans (g227) (hv _ _ sub_36_37)), Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g226)) (hv _ _ sub_36_37))⟩
    · exact h1 ⟨Or.inr (le_trans (g227) (hv _ _ sub_36_37)), Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g226)) (hv _ _ sub_36_37))⟩
  · rcases h0b with g228 | g228
    · exact h1 ⟨Or.inl (le_trans (g228) (hv _ _ sub_36_37)), Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g226)) (hv _ _ sub_36_37))⟩
    · exact h1 ⟨Or.inr (le_trans (g228) (hv _ _ sub_36_37)), Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g226)) (hv _ _ sub_36_37))⟩
theorem cl279 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_0 v) (h1 : ¬acc10_1 v) : False := by
  rcases le_or_gt (v s38) (v s73) with g229 | g229
  · exact h0 ⟨Or.inl (g229), hv _ _ sub_0_73⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_73) (g229)) (hv _ _ sub_38_54))), hv _ _ sub_0_54⟩
theorem cl281 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc10_1 v) (h1 : ¬acc12_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g230 | g230
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g230)) (hv _ _ sub_54_55)), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g230)) (hv _ _ sub_54_55)), hv _ _ sub_0_55⟩
theorem cl282 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_1 v) (h1 : ¬acc11_0 v) : False := by
  rcases le_or_gt (v s72) (v s54) with g231 | g231
  · exact h0 ⟨Or.inl (g231), hv _ _ sub_0_54⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_36_54) (g231)) (hv _ _ sub_72_73))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_54) (g231)) (hv _ _ sub_72_73)))⟩
theorem cl283 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_1 v) (h1 : acc11_1 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g232 | g232
  · exact h0 ⟨Or.inl (le_trans (g232) (hv _ _ sub_38_54)), hv _ _ sub_0_54⟩
  · exact h0 ⟨Or.inr (le_trans (g232) (hv _ _ sub_38_54)), hv _ _ sub_0_54⟩
theorem cl284 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_1 v) (h1 : ¬acc12_1 v) : False := by
  rcases le_or_gt (v s72) (v s54) with g233 | g233
  · exact h0 ⟨Or.inl (g233), hv _ _ sub_0_54⟩
  · exact h1 ⟨Or.inl (le_of_lt (g233)), hv _ _ sub_0_72⟩
theorem cl285 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_1 v) (h1 : ¬acc13_0 v) : False := by
  rcases le_or_gt (v s9) (v s54) with g234 | g234
  · exact h0 ⟨Or.inr (g234), hv _ _ sub_0_54⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_54) (g234)) (hv _ _ sub_9_47))), hv _ _ sub_0_47⟩
theorem cl286 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_1 v) (h1 : ¬acc14_0 v) : False := by
  rcases le_or_gt (v s9) (v s54) with g235 | g235
  · exact h0 ⟨Or.inr (g235), hv _ _ sub_0_54⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_18_54) (g235)) (hv _ _ sub_9_45))), hv _ _ sub_0_45⟩
theorem cl287 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_1 v) (h1 : ¬acc15_1 v) : False := by
  rcases le_or_gt (v s72) (v s54) with g236 | g236
  · exact h0 ⟨Or.inl (g236), hv _ _ sub_0_54⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_38_54) (g236))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_16_54) (g236)))⟩
theorem cl288 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_1 v) (h1 : ¬acc17_2 v) : False := by
  rcases le_or_gt (v s72) (v s54) with g237 | g237
  · exact h0 ⟨Or.inl (g237), hv _ _ sub_0_54⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_36_54) (g237))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_18_54) (g237)))⟩
theorem cl289 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc10_2 v) (h1 : ¬acc11_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g238 | g238
  · rcases h0b with g239 | g239
    · exact h1 ⟨Or.inl (le_trans (g238) (hv _ _ sub_128_144)), Or.inl (le_trans (le_trans (hv _ _ sub_36_38) (g239)) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inl (le_trans (g238) (hv _ _ sub_128_144)), Or.inr (le_trans (le_trans (hv _ _ sub_6_22) (g239)) (hv _ _ sub_128_144))⟩
  · rcases h0b with g240 | g240
    · exact h1 ⟨Or.inr (le_trans (g238) (hv _ _ sub_128_144)), Or.inl (le_trans (le_trans (hv _ _ sub_36_38) (g240)) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inr (le_trans (g238) (hv _ _ sub_128_144)), Or.inr (le_trans (le_trans (hv _ _ sub_6_22) (g240)) (hv _ _ sub_128_144))⟩
theorem cl290 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_2 v) (h1 : ¬acc13_0 v) : False := by
  rcases le_or_gt (v s128) (v s47) with g241 | g241
  · exact h1 ⟨Or.inl (g241), hv _ _ sub_0_47⟩
  · exact h0 ⟨Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_9_47) (g241))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_38_47) (g241)))⟩
theorem cl291 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc11_0 v) (h1 : ¬acc12_0 v) : False := by
  rcases le_or_gt (v s64) (v s55) with g242 | g242
  · exact h1 ⟨Or.inl (g242), hv _ _ sub_0_55⟩
  · exact h0 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_36_55) (g242)) (hv _ _ sub_64_73))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_55) (g242)) (hv _ _ sub_64_73)))⟩
theorem cl293 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc11_0 v) (h1 : acc15_1 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g243 | g243
  · rcases h1a with g244 | g244 | g244
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_38) (g244)) (hv _ _ sub_72_73)), Or.inl (le_trans (g243) (hv _ _ sub_72_73))⟩
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_37) (g244)) (hv _ _ sub_72_73)), Or.inl (le_trans (g243) (hv _ _ sub_72_73))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_6_7) (g244)) (hv _ _ sub_72_73)), Or.inl (le_trans (g243) (hv _ _ sub_72_73))⟩
  · rcases h1a with g245 | g245 | g245
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_38) (g245)) (hv _ _ sub_72_73)), Or.inr (le_trans (g243) (hv _ _ sub_72_73))⟩
    · exact h0 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_37) (g245)) (hv _ _ sub_72_73)), Or.inr (le_trans (g243) (hv _ _ sub_72_73))⟩
    · exact h0 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_6_7) (g245)) (hv _ _ sub_72_73)), Or.inr (le_trans (g243) (hv _ _ sub_72_73))⟩
theorem cl296 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc11_1 v) (h1 : ¬acc15_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g246 | g246
  · rcases h0b with g247 | g247
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g246)) (hv _ _ sub_38_39)), Or.inl (le_trans (g247) (hv _ _ sub_38_39))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_64_72) (g246)) (hv _ _ sub_38_39)), Or.inr (le_trans (g247) (hv _ _ sub_38_39))⟩
  · rcases h0b with g248 | g248
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g246)) (hv _ _ sub_38_39)), Or.inl (le_trans (g248) (hv _ _ sub_38_39))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_8_9) (g246)) (hv _ _ sub_38_39)), Or.inr (le_trans (g248) (hv _ _ sub_38_39))⟩
theorem cl297 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc11_2 v) (h1 : ¬acc13_0 v) : False := by
  rcases le_or_gt (v s128) (v s47) with g249 | g249
  · exact h1 ⟨Or.inl (g249), hv _ _ sub_0_47⟩
  · exact h0 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_9_47) (g249)) (hv _ _ sub_128_144))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_36_47) (g249)) (hv _ _ sub_128_144)))⟩
theorem cl298 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc11_2 v) (h1 : ¬acc14_0 v) : False := by
  rcases le_or_gt (v s144) (v s45) with g250 | g250
  · exact h1 ⟨Or.inl (g250), hv _ _ sub_0_45⟩
  · exact h0 ⟨Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_9_45) (g250))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_36_45) (g250)))⟩
theorem cl299 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc12_0 v) (h1 : ¬acc12_1 v) : False := by
  rcases le_or_gt (v s64) (v s55) with g251 | g251
  · exact h0 ⟨Or.inl (g251), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_54_55) (g251)) (hv _ _ sub_64_72))), hv _ _ sub_0_72⟩
theorem cl301 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc12_0 v) (h1 : ¬acc13_2 v) : False := by
  rcases le_or_gt (v s64) (v s55) with g252 | g252
  · exact h0 ⟨Or.inl (g252), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_39_55) (g252))))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_16_55) (g252)))⟩
theorem cl302 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc12_0 v) (h1 : ¬acc14_0 v) : False := by
  rcases le_or_gt (v s8) (v s55) with g253 | g253
  · exact h0 ⟨Or.inr (g253), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_18_55) (g253)) (hv _ _ sub_8_45))), hv _ _ sub_0_45⟩
theorem cl303 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc12_0 v) (h1 : ¬acc14_2 v) : False := by
  rcases le_or_gt (v s64) (v s55) with g254 | g254
  · exact h0 ⟨Or.inl (g254), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_37_55) (g254))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_18_55) (g254)))⟩
theorem cl305 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc12_0 v) (h1 : ¬acc15_1 v) : False := by
  rcases le_or_gt (v s64) (v s55) with g255 | g255
  · exact h0 ⟨Or.inl (g255), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_38_55) (g255)) (hv _ _ sub_64_72))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_16_55) (g255)) (hv _ _ sub_64_72)))⟩
theorem cl306 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc12_0 v) (h1 : ¬acc16_1 v) : False := by
  rcases le_or_gt (v s8) (v s55) with g256 | g256
  · exact h0 ⟨Or.inr (g256), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_36_55) (g256)) (hv _ _ sub_8_154))), hv _ _ sub_0_154⟩
theorem cl307 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc12_0 v) (h1 : acc17_0 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g257 | g257
  · exact h0 ⟨Or.inl (le_trans (g257) (hv _ _ sub_37_55)), hv _ _ sub_0_55⟩
  · exact h0 ⟨Or.inr (le_trans (g257) (hv _ _ sub_37_55)), hv _ _ sub_0_55⟩
theorem cl308 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc12_0 v) (h1 : ¬acc17_2 v) : False := by
  rcases le_or_gt (v s64) (v s55) with g258 | g258
  · exact h0 ⟨Or.inl (g258), hv _ _ sub_0_55⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_36_55) (g258)) (hv _ _ sub_64_72))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_18_55) (g258)) (hv _ _ sub_64_72)))⟩
theorem cl309 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc12_2 v) (h1 : ¬acc15_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g259 | g259
  · rcases h0a with g260 | g260 | g260 | g260
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_38_54) (g260)) (hv _ _ sub_128_144)), Or.inl (le_trans (g259) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inr (Or.inl (le_trans (le_trans (hv _ _ sub_37_53) (g260)) (hv _ _ sub_128_144))), Or.inl (le_trans (g259) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_38_39) (g260)) (hv _ _ sub_128_144)), Or.inl (le_trans (g259) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inr (Or.inr (le_trans (le_trans (hv _ _ sub_7_23) (g260)) (hv _ _ sub_128_144))), Or.inl (le_trans (g259) (hv _ _ sub_128_144))⟩
  · rcases h0a with g261 | g261 | g261 | g261
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_38_54) (g261)) (hv _ _ sub_128_144)), Or.inr (le_trans (g259) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inr (Or.inl (le_trans (le_trans (hv _ _ sub_37_53) (g261)) (hv _ _ sub_128_144))), Or.inr (le_trans (g259) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_38_39) (g261)) (hv _ _ sub_128_144)), Or.inr (le_trans (g259) (hv _ _ sub_128_144))⟩
    · exact h1 ⟨Or.inr (Or.inr (le_trans (le_trans (hv _ _ sub_7_23) (g261)) (hv _ _ sub_128_144))), Or.inr (le_trans (g259) (hv _ _ sub_128_144))⟩
theorem cl311 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc12_2 v) (h1 : ¬acc17_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g262 | g262
  · rcases h0a with g263 | g263 | g263 | g263
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_54) (g263)) (hv _ _ sub_128_146)), Or.inl (le_trans (g262) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_53) (g263)) (hv _ _ sub_128_146)), Or.inl (le_trans (g262) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_39) (g263)) (hv _ _ sub_128_146)), Or.inl (le_trans (g262) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_5_23) (g263)) (hv _ _ sub_128_146)), Or.inl (le_trans (g262) (hv _ _ sub_128_146))⟩
  · rcases h0a with g264 | g264 | g264 | g264
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_54) (g264)) (hv _ _ sub_128_146)), Or.inr (le_trans (g262) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_53) (g264)) (hv _ _ sub_128_146)), Or.inr (le_trans (g262) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_39) (g264)) (hv _ _ sub_128_146)), Or.inr (le_trans (g262) (hv _ _ sub_128_146))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_5_23) (g264)) (hv _ _ sub_128_146)), Or.inr (le_trans (g262) (hv _ _ sub_128_146))⟩
theorem cl312 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc12_2 v) (h1 : ¬acc13_0 v) : False := by
  rcases le_or_gt (v s128) (v s47) with g265 | g265
  · exact h1 ⟨Or.inl (g265), hv _ _ sub_0_47⟩
  · exact h0 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_39_47) (g265))))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_8_47) (g265)))⟩
theorem cl315 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc13_0 v) (h1 : ¬acc14_1 v) : False := by
  rcases le_or_gt (v s128) (v s47) with g266 | g266
  · exact h0 ⟨Or.inl (g266), hv _ _ sub_0_47⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_37_47) (g266)) (hv _ _ sub_128_146))), hv _ _ sub_0_146⟩
theorem cl316 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc13_0 v) (h1 : acc15_0 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1b with g267 | g267
  · exact h0 ⟨Or.inl (le_trans (g267) (hv _ _ sub_39_47)), hv _ _ sub_0_47⟩
  · exact h0 ⟨Or.inr (le_trans (g267) (hv _ _ sub_39_47)), hv _ _ sub_0_47⟩
theorem cl317 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc13_0 v) (h1 : ¬acc15_2 v) : False := by
  rcases le_or_gt (v s128) (v s47) with g268 | g268
  · exact h0 ⟨Or.inl (g268), hv _ _ sub_0_47⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_38_47) (g268)) (hv _ _ sub_128_144))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_8_47) (g268)) (hv _ _ sub_128_144)))⟩
theorem cl321 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc13_0 v) (h1 : ¬acc17_1 v) : False := by
  rcases le_or_gt (v s128) (v s47) with g269 | g269
  · exact h0 ⟨Or.inl (g269), hv _ _ sub_0_47⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_36_47) (g269)) (hv _ _ sub_128_146))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_8_47) (g269)) (hv _ _ sub_128_146)))⟩
theorem cl323 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc13_1 v) (h1 : ¬acc14_0 v) : False := by
  rcases le_or_gt (v s45) (v s144) with g270 | g270
  · exact h0 ⟨Or.inr (Or.inl (g270)), hv _ _ sub_0_144⟩
  · exact h1 ⟨Or.inl (le_of_lt (g270)), hv _ _ sub_0_45⟩
theorem cl325 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc14_0 v) (h1 : ¬acc14_1 v) : False := by
  rcases le_or_gt (v s144) (v s45) with g271 | g271
  · exact h0 ⟨Or.inl (g271), hv _ _ sub_0_45⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_37_45) (g271)) (hv _ _ sub_144_146))), hv _ _ sub_0_146⟩
theorem cl326 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc14_0 v) (h1 : ¬acc15_2 v) : False := by
  rcases le_or_gt (v s144) (v s45) with g272 | g272
  · exact h0 ⟨Or.inl (g272), hv _ _ sub_0_45⟩
  · exact h1 ⟨Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_37_45) (g272)))), Or.inr (le_of_lt (lt_of_le_of_lt (hv _ _ sub_8_45) (g272)))⟩
theorem cl329 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc14_0 v) (h1 : acc17_0 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g273 | g273
  · exact h0 ⟨Or.inl (le_trans (g273) (hv _ _ sub_37_45)), hv _ _ sub_0_45⟩
  · exact h0 ⟨Or.inr (le_trans (g273) (hv _ _ sub_37_45)), hv _ _ sub_0_45⟩
theorem cl330 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc14_0 v) (h1 : ¬acc17_1 v) : False := by
  rcases le_or_gt (v s144) (v s45) with g274 | g274
  · exact h0 ⟨Or.inl (g274), hv _ _ sub_0_45⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_36_45) (g274)) (hv _ _ sub_144_146))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_8_45) (g274)) (hv _ _ sub_144_146)))⟩
theorem cl332 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc14_1 v) (h1 : ¬acc16_0 v) : False := by
  rcases le_or_gt (v s37) (v s146) with g275 | g275
  · exact h0 ⟨Or.inl (g275), hv _ _ sub_0_146⟩
  · exact h1 ⟨Or.inl (le_of_lt (g275)), hv _ _ sub_0_37⟩
theorem cl333 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc14_2 v) (h1 : ¬acc17_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g276 | g276
  · rcases h0b with g277 | g277
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_37) (g276)) (hv _ _ sub_64_72)), Or.inl (le_trans (g277) (hv _ _ sub_64_72))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_37) (g276)) (hv _ _ sub_64_72)), Or.inr (le_trans (g277) (hv _ _ sub_64_72))⟩
  · rcases h0b with g278 | g278
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_5_13) (g276)) (hv _ _ sub_64_72)), Or.inl (le_trans (g278) (hv _ _ sub_64_72))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_5_13) (g276)) (hv _ _ sub_64_72)), Or.inr (le_trans (g278) (hv _ _ sub_64_72))⟩
theorem cl334 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_0 v) (h1 : ¬acc16_1 v) : False := by
  rcases le_or_gt (v s36) (v s154) with g279 | g279
  · exact h1 ⟨Or.inl (g279), hv _ _ sub_0_154⟩
  · exact h0 ⟨Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_8_154) (g279)) (hv _ _ sub_36_39))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_154) (g279)) (hv _ _ sub_36_39)))⟩
theorem cl335 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_0 v) (h1 : acc17_0 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g280 | g280
  · rcases h1b with g281 | g281
    · exact h0 ⟨Or.inl (le_trans (g281) (hv _ _ sub_37_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_144) (g280)) (hv _ _ sub_37_39))⟩
    · exact h0 ⟨Or.inr (le_trans (g281) (hv _ _ sub_37_39)), Or.inl (le_trans (le_trans (hv _ _ sub_128_144) (g280)) (hv _ _ sub_37_39))⟩
  · rcases h1b with g282 | g282
    · exact h0 ⟨Or.inl (le_trans (g282) (hv _ _ sub_37_39)), Or.inr (le_trans (le_trans (hv _ _ sub_16_18) (g280)) (hv _ _ sub_37_39))⟩
    · exact h0 ⟨Or.inr (le_trans (g282) (hv _ _ sub_37_39)), Or.inr (le_trans (le_trans (hv _ _ sub_16_18) (g280)) (hv _ _ sub_37_39))⟩
theorem cl336 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc15_2 v) (h1 : ¬acc16_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g283 | g283 | g283
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_38) (g283)) (hv _ _ sub_144_154)), hv _ _ sub_0_154⟩
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_37) (g283)) (hv _ _ sub_144_154)), hv _ _ sub_0_154⟩
  · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_5_7) (g283)) (hv _ _ sub_144_154)), hv _ _ sub_0_154⟩
theorem cl337 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc15_2 v) (h1 : ¬acc17_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g284 | g284
  · rcases h0a with g285 | g285 | g285
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_38) (g285)) (hv _ _ sub_144_146)), Or.inl (le_trans (g284) (hv _ _ sub_144_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_37) (g285)) (hv _ _ sub_144_146)), Or.inl (le_trans (g284) (hv _ _ sub_144_146))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_5_7) (g285)) (hv _ _ sub_144_146)), Or.inl (le_trans (g284) (hv _ _ sub_144_146))⟩
  · rcases h0a with g286 | g286 | g286
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_38) (g286)) (hv _ _ sub_144_146)), Or.inr (le_trans (g284) (hv _ _ sub_144_146))⟩
    · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_36_37) (g286)) (hv _ _ sub_144_146)), Or.inr (le_trans (g284) (hv _ _ sub_144_146))⟩
    · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_5_7) (g286)) (hv _ _ sub_144_146)), Or.inr (le_trans (g284) (hv _ _ sub_144_146))⟩
theorem cl338 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc16_0 v) (h1 : ¬acc16_1 v) : False := by
  rcases le_or_gt (v s146) (v s37) with g287 | g287
  · exact h0 ⟨Or.inl (g287), hv _ _ sub_0_37⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_36_37) (g287)) (hv _ _ sub_146_154))), hv _ _ sub_0_154⟩
theorem cl339 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc16_1 v) (h1 : ¬acc17_0 v) : False := by
  rcases le_or_gt (v s36) (v s154) with g288 | g288
  · exact h0 ⟨Or.inl (g288), hv _ _ sub_0_154⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_144_154) (g288)) (hv _ _ sub_36_37))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_8_154) (g288)) (hv _ _ sub_36_37)))⟩
theorem cl340 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc16_1 v) (h1 : acc17_1 v) : False := by
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g289 | g289
  · exact h0 ⟨Or.inl (le_trans (g289) (hv _ _ sub_146_154)), hv _ _ sub_0_154⟩
  · exact h0 ⟨Or.inr (le_trans (g289) (hv _ _ sub_146_154)), hv _ _ sub_0_154⟩
theorem cl341 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc16_2 v) (h1 : ¬acc17_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g290 | g290
  · rcases h0b with g291 | g291
    · exact h1 ⟨Or.inl (le_trans (g290) (hv _ _ sub_64_72)), Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g291)) (hv _ _ sub_64_72))⟩
    · exact h1 ⟨Or.inl (le_trans (g290) (hv _ _ sub_64_72)), Or.inr (le_trans (le_trans (hv _ _ sub_18_26) (g291)) (hv _ _ sub_64_72))⟩
  · rcases h0b with g292 | g292
    · exact h1 ⟨Or.inr (le_trans (g290) (hv _ _ sub_64_72)), Or.inl (le_trans (le_trans (hv _ _ sub_144_146) (g292)) (hv _ _ sub_64_72))⟩
    · exact h1 ⟨Or.inr (le_trans (g290) (hv _ _ sub_64_72)), Or.inr (le_trans (le_trans (hv _ _ sub_18_26) (g292)) (hv _ _ sub_64_72))⟩
theorem cl342 (v : Finset (Fin 8) → α) (_hv : IsMonotoneVal v) (h0 : ¬acc9_2 v) (h1 : ¬acc11_2 v) (h2 : ¬acc17_2 v) : False := by
  rcases le_or_gt (v s72) (v s36) with g293 | g293
  · rcases le_or_gt (v s144) (v s36) with g294 | g294
    · exact h0 ⟨Or.inl (g293), Or.inl (g294)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (g293) (g294))), Or.inl (le_of_lt (g294))⟩
  · rcases le_or_gt (v s72) (v s144) with g295 | g295
    · exact h1 ⟨Or.inl (g295), Or.inl (le_of_lt (lt_of_lt_of_le (g293) (g295)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g293)), Or.inl (le_of_lt (g295))⟩
theorem cl344 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_0 v) (h1 : ¬acc8_2 v) (h2 : ¬acc6_1 v) : False := by
  rcases le_or_gt (v s32) (v s91) with g296 | g296
  · exact h0 ⟨Or.inl (g296), hv _ _ sub_0_91⟩
  · rcases le_or_gt (v s146) (v s32) with g297 | g297
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_72_91) (g296))), Or.inl (g297)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_trans (lt_of_le_of_lt (hv _ _ sub_73_91) (g296)) (g297))), hv _ _ sub_0_146⟩
theorem cl345 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_2 v) (h1 : ¬acc2_0 v) (h2 : ¬acc1_1 v) : False := by
  rcases le_or_gt (v s64) (v s147) with g298 | g298
  · rcases le_or_gt (v s147) (v s32) with g299 | g299
    · exact h0 ⟨Or.inr (Or.inr (Or.inl (g299))), Or.inl (le_trans (g298) (g299))⟩
    · exact h1 ⟨Or.inl (le_of_lt (g299)), Or.inl (g298)⟩
  · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (g298) (hv _ _ sub_64_72))))), hv _ _ sub_0_72⟩
theorem cl347 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_1 v) (h1 : ¬acc8_0 v) (h2 : ¬acc2_1 v) : False := by
  rcases le_or_gt (v s72) (v s146) with g300 | g300
  · rcases le_or_gt (v s32) (v s146) with g301 | g301
    · exact h0 ⟨Or.inl (g300), Or.inl (g301)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g301) (hv _ _ sub_32_36))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_64_72) (g300)) (g301)) (hv _ _ sub_32_36)))⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g300) (hv _ _ sub_72_73))), hv _ _ sub_0_73⟩
theorem cl348 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_1 v) (h1 : ¬acc8_0 v) (h2 : ¬acc16_0 v) : False := by
  rcases le_or_gt (v s72) (v s146) with g302 | g302
  · rcases le_or_gt (v s32) (v s146) with g303 | g303
    · exact h0 ⟨Or.inl (g302), Or.inl (g303)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g303) (hv _ _ sub_32_37))), hv _ _ sub_0_37⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g302) (hv _ _ sub_72_73))), hv _ _ sub_0_73⟩
theorem cl349 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc7_0 v) (h1 : ¬acc7_2 v) (h2 : ¬acc3_1 v) : False := by
  rcases le_or_gt (v s32) (v s75) with g304 | g304
  · rcases le_or_gt (v s128) (v s75) with g305 | g305
    · exact h0 ⟨Or.inl (g304), Or.inl (g305)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_74_75) (g305)) (hv _ _ sub_128_144))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (g304) (g305)) (hv _ _ sub_128_144)))⟩
  · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (g304) (hv _ _ sub_32_36))))), hv _ _ sub_0_36⟩
theorem cl351 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc9_2 v) (h1 : ¬acc7_0 v) (h2 : ¬acc4_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases le_or_gt (v s32) (v s75) with g306 | g306
  · rcases le_or_gt (v s4) (v s75) with g307 | g307
    · rcases le_or_gt (v s128) (v s75) with g308 | g308
      · exact h1 ⟨Or.inl (g306), Or.inl (g308)⟩
      · rcases h0b with g309 | g309
        · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_73_75) (g308)) (hv _ _ sub_128_144)) (g309)) (hv _ _ sub_36_38))), hv _ _ sub_0_38⟩
        · rcases le_or_gt (v s16) (v s75) with g310 | g310
          · exact h1 ⟨Or.inl (g306), Or.inr (g310)⟩
          · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_73_75) (g310)) (hv _ _ sub_16_18)) (g309)) (hv _ _ sub_36_38))), hv _ _ sub_0_38⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_73_75) (g307)) (hv _ _ sub_4_38))), hv _ _ sub_0_38⟩
  · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_73_75) (g306)) (hv _ _ sub_32_38))), hv _ _ sub_0_38⟩
theorem cl353 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_1 v) (h1 : ¬acc11_1 v) (h2 : ¬acc2_0 v) : False := by
  rcases le_or_gt (v s150) (v s72) with g311 | g311
  · exact h0 ⟨Or.inl (g311), hv _ _ sub_0_72⟩
  · rcases le_or_gt (v s149) (v s72) with g312 | g312
    · exact h0 ⟨Or.inr (Or.inl (g312)), hv _ _ sub_0_72⟩
    · rcases le_or_gt (v s147) (v s72) with g313 | g313
      · exact h0 ⟨Or.inr (Or.inr (Or.inl (g313))), hv _ _ sub_0_72⟩
      · rcases le_or_gt (v s32) (v s147) with g314 | g314
        · exact h2 ⟨Or.inl (g314), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g313)))⟩
        · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (g313) (g314)) (hv _ _ sub_32_38))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_147) (g314)) (hv _ _ sub_32_38)))⟩
theorem cl354 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_2 v) (h1 : ¬acc1_1 v) (h2 : ¬acc2_0 v) : False := by
  rcases le_or_gt (v s150) (v s72) with g315 | g315
  · exact h1 ⟨Or.inl (g315), hv _ _ sub_0_72⟩
  · rcases le_or_gt (v s149) (v s72) with g316 | g316
    · exact h1 ⟨Or.inr (Or.inl (g316)), hv _ _ sub_0_72⟩
    · rcases le_or_gt (v s147) (v s72) with g317 | g317
      · exact h1 ⟨Or.inr (Or.inr (Or.inl (g317))), hv _ _ sub_0_72⟩
      · rcases le_or_gt (v s32) (v s147) with g318 | g318
        · exact h2 ⟨Or.inl (g318), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g317)))⟩
        · exact h0 ⟨Or.inl (le_of_lt (lt_trans (g317) (g318))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_146_147) (g318)))⟩
theorem cl355 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_2 v) (h1 : ¬acc9_1 v) (h2 : ¬acc8_0 v) : False := by
  rcases le_or_gt (v s72) (v s146) with g319 | g319
  · rcases le_or_gt (v s146) (v s32) with g320 | g320
    · exact h0 ⟨Or.inl (le_trans (g319) (g320)), Or.inl (g320)⟩
    · exact h1 ⟨Or.inl (g319), Or.inl (le_of_lt (g320))⟩
  · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g319) (hv _ _ sub_72_73))), hv _ _ sub_0_73⟩
theorem cl356 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_2 v) (h1 : ¬acc9_0 v) (h2 : ¬acc6_1 v) : False := by
  rcases le_or_gt (v s144) (v s73) with g321 | g321
  · rcases le_or_gt (v s72) (v s32) with g322 | g322
    · rcases le_or_gt (v s9) (v s32) with g323 | g323
      · rcases le_or_gt (v s146) (v s32) with g324 | g324
        · exact h0 ⟨Or.inl (g322), Or.inl (g324)⟩
        · rcases le_or_gt (v s32) (v s73) with g325 | g325
          · exact h1 ⟨Or.inl (g321), Or.inl (g325)⟩
          · exact h2 ⟨Or.inl (le_of_lt (lt_trans (g325) (g324))), hv _ _ sub_0_146⟩
      · exact h1 ⟨Or.inl (g321), Or.inl (le_of_lt (lt_of_lt_of_le (g323) (hv _ _ sub_9_73)))⟩
    · exact h1 ⟨Or.inl (g321), Or.inl (le_of_lt (lt_of_lt_of_le (g322) (hv _ _ sub_72_73)))⟩
  · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g321) (hv _ _ sub_144_146))), hv _ _ sub_0_146⟩
theorem cl360 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc7_0 v) (h1 : ¬acc7_1 v) (h2 : ¬acc4_2 v) : False := by
  rcases le_or_gt (v s32) (v s75) with g326 | g326
  · rcases le_or_gt (v s128) (v s75) with g327 | g327
    · exact h0 ⟨Or.inl (g326), Or.inl (g327)⟩
    · rcases le_or_gt (v s128) (v s36) with g328 | g328
      · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_74_75) (g327)) (g328))), Or.inl (g328)⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_73_75) (g327))), Or.inl (le_of_lt (g328))⟩
  · rcases le_or_gt (v s128) (v s36) with g329 | g329
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_74_75) (g326)) (hv _ _ sub_32_36))), Or.inl (g329)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_trans (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_73_75) (g326)) (hv _ _ sub_32_36)) (g329))), Or.inl (le_of_lt (g329))⟩
theorem cl362 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc7_2 v) (h1 : ¬acc9_0 v) (h2 : ¬acc4_1 v) : False := by
  rcases le_or_gt (v s32) (v s73) with g330 | g330
  · rcases le_or_gt (v s73) (v s144) with g331 | g331
    · exact h0 ⟨Or.inr (Or.inl (g331)), Or.inl (le_trans (g330) (g331))⟩
    · exact h1 ⟨Or.inl (le_of_lt (g331)), Or.inl (g330)⟩
  · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g330) (hv _ _ sub_32_38))), hv _ _ sub_0_38⟩
theorem cl364 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_2 v) (h1 : ¬acc11_0 v) (h2 : ¬acc11_1 v) : False := by
  rcases le_or_gt (v s72) (v s128) with g332 | g332
  · rcases le_or_gt (v s38) (v s128) with g333 | g333
    · exact h0 ⟨Or.inl (g332), Or.inl (g333)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (g332) (g333))), Or.inl (le_of_lt (g333))⟩
  · rcases le_or_gt (v s36) (v s73) with g334 | g334
    · exact h1 ⟨Or.inl (g334), Or.inl (le_of_lt (lt_of_lt_of_le (g332) (hv _ _ sub_72_73)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_73) (g334)) (hv _ _ sub_36_38))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (g332) (hv _ _ sub_72_73)) (g334)) (hv _ _ sub_36_38)))⟩
theorem cl365 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_2 v) (h1 : ¬acc11_0 v) (h2 : ¬acc4_1 v) : False := by
  rcases le_or_gt (v s36) (v s73) with g335 | g335
  · rcases le_or_gt (v s72) (v s128) with g336 | g336
    · rcases le_or_gt (v s9) (v s128) with g337 | g337
      · rcases le_or_gt (v s38) (v s128) with g338 | g338
        · exact h0 ⟨Or.inl (g336), Or.inl (g338)⟩
        · rcases le_or_gt (v s128) (v s73) with g339 | g339
          · exact h1 ⟨Or.inl (g335), Or.inl (g339)⟩
          · exact h2 ⟨Or.inl (le_of_lt (lt_trans (g339) (g338))), hv _ _ sub_0_38⟩
      · exact h1 ⟨Or.inl (g335), Or.inl (le_of_lt (lt_of_lt_of_le (g337) (hv _ _ sub_9_73)))⟩
    · exact h1 ⟨Or.inl (g335), Or.inl (le_of_lt (lt_of_lt_of_le (g336) (hv _ _ sub_72_73)))⟩
  · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g335) (hv _ _ sub_36_38))), hv _ _ sub_0_38⟩
theorem cl367 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc15_2 v) (h1 : ¬acc17_2 v) (h2 : ¬acc11_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g340 | g340
  · rcases le_or_gt (v s36) (v s72) with g341 | g341
    · rcases le_or_gt (v s144) (v s72) with g342 | g342
      · exact h1 ⟨Or.inl (g341), Or.inl (g342)⟩
      · exact h2 ⟨Or.inl (le_of_lt (g342)), Or.inl (le_of_lt (lt_of_le_of_lt (g341) (g342)))⟩
    · rcases h0a with g343 | g343 | g343
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (g341) (hv _ _ sub_36_38)) (g343))), Or.inl (le_trans (hv _ _ sub_36_38) (g343))⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (g341) (hv _ _ sub_36_37)) (g343))), Or.inl (le_trans (hv _ _ sub_36_37) (g343))⟩
      · rcases le_or_gt (v s144) (v s72) with g344 | g344
        · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_5_7) (g343)) (g344)), Or.inl (g344)⟩
        · exact h2 ⟨Or.inl (le_of_lt (g344)), Or.inr (le_trans (hv _ _ sub_6_7) (g343))⟩
  · rcases le_or_gt (v s36) (v s72) with g345 | g345
    · rcases le_or_gt (v s144) (v s72) with g346 | g346
      · exact h1 ⟨Or.inl (g345), Or.inl (g346)⟩
      · exact h2 ⟨Or.inl (le_of_lt (g346)), Or.inl (le_of_lt (lt_of_le_of_lt (g345) (g346)))⟩
    · rcases h0a with g347 | g347 | g347
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (g345) (hv _ _ sub_36_38)) (g347))), Or.inl (le_trans (hv _ _ sub_36_38) (g347))⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (g345) (hv _ _ sub_36_37)) (g347))), Or.inl (le_trans (hv _ _ sub_36_37) (g347))⟩
      · rcases le_or_gt (v s144) (v s72) with g348 | g348
        · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_5_7) (g347)) (g348)), Or.inl (g348)⟩
        · exact h2 ⟨Or.inl (le_of_lt (g348)), Or.inr (le_trans (hv _ _ sub_6_7) (g347))⟩
theorem cl368 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc3_1 v) (h1 : ¬acc4_1 v) (h2 : ¬acc9_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g349 | g349 | g349 | g349
  · exact h2 ⟨Or.inl (le_trans (hv _ _ sub_72_90) (g349)), Or.inr (le_trans (hv _ _ sub_18_90) (g349))⟩
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_73_89) (g349)) (hv _ _ sub_36_38)), hv _ _ sub_0_38⟩
  · exact h1 ⟨Or.inl (le_trans (le_trans (hv _ _ sub_73_75) (g349)) (hv _ _ sub_36_38)), hv _ _ sub_0_38⟩
  · exact h1 ⟨Or.inr (le_trans (le_trans (hv _ _ sub_25_27) (g349)) (hv _ _ sub_36_38)), hv _ _ sub_0_38⟩
theorem cl371 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_2 v) (h1 : ¬acc15_1 v) (h2 : ¬acc15_0 v) : False := by
  rcases le_or_gt (v s72) (v s128) with g350 | g350
  · rcases le_or_gt (v s38) (v s128) with g351 | g351
    · exact h0 ⟨Or.inl (g350), Or.inl (g351)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_64_72) (g350)) (g351)) (hv _ _ sub_38_39))), Or.inl (le_of_lt (lt_of_lt_of_le (g351) (hv _ _ sub_38_39)))⟩
  · rcases le_or_gt (v s38) (v s72) with g352 | g352
    · exact h1 ⟨Or.inl (g352), Or.inl (le_of_lt (g350))⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g352)) (hv _ _ sub_38_39))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (g350) (g352)) (hv _ _ sub_38_39)))⟩
theorem cl372 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc12_1 v) (h1 : ¬acc17_2 v) (h2 : ¬acc15_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g353 | g353 | g353 | g353
  · exact h1 ⟨Or.inl (le_trans (hv _ _ sub_36_54) (g353)), Or.inr (le_trans (hv _ _ sub_18_54) (g353))⟩
  · rcases le_or_gt (v s144) (v s72) with g354 | g354
    · exact h1 ⟨Or.inl (le_trans (hv _ _ sub_36_53) (g353)), Or.inl (g354)⟩
    · exact h2 ⟨Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (le_trans (hv _ _ sub_37_53) (g353)) (g354)))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g354)))⟩
  · rcases le_or_gt (v s144) (v s72) with g355 | g355
    · exact h1 ⟨Or.inl (le_trans (hv _ _ sub_36_39) (g353)), Or.inl (g355)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (le_trans (hv _ _ sub_38_39) (g353)) (g355))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g355)))⟩
  · exact h1 ⟨Or.inr (le_trans (hv _ _ sub_5_23) (g353)), Or.inr (le_trans (hv _ _ sub_18_23) (g353))⟩
theorem cl373 (v : Finset (Fin 8) → α) (_hv : IsMonotoneVal v) (h0 : ¬acc14_2 v) (h1 : ¬acc15_2 v) (h2 : ¬acc17_0 v) : False := by
  rcases le_or_gt (v s37) (v s64) with g356 | g356
  · rcases le_or_gt (v s144) (v s64) with g357 | g357
    · exact h0 ⟨Or.inl (g356), Or.inl (g357)⟩
    · exact h1 ⟨Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (g356) (g357)))), Or.inl (le_of_lt (g357))⟩
  · rcases le_or_gt (v s37) (v s144) with g358 | g358
    · exact h1 ⟨Or.inr (Or.inl (g358)), Or.inl (le_of_lt (lt_of_lt_of_le (g356) (g358)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g358)), Or.inl (le_of_lt (g356))⟩
theorem cl375 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_2 v) (h1 : ¬acc2_1 v) (h2 : ¬acc9_1 v) : False := by
  rcases le_or_gt (v s146) (v s72) with g359 | g359
  · rcases le_or_gt (v s32) (v s72) with g360 | g360
    · exact h0 ⟨Or.inl (g359), Or.inl (g360)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (g359) (g360)) (hv _ _ sub_32_36))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g360)) (hv _ _ sub_32_36)))⟩
  · rcases le_or_gt (v s146) (v s36) with g361 | g361
    · exact h1 ⟨Or.inl (g361), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g359)) (g361)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g359)), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_32_36) (g361)))⟩
theorem cl376 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_2 v) (h1 : ¬acc9_2 v) (h2 : ¬acc17_1 v) : False := by
  rcases le_or_gt (v s146) (v s72) with g362 | g362
  · rcases le_or_gt (v s32) (v s72) with g363 | g363
    · exact h0 ⟨Or.inl (g362), Or.inl (g363)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g363) (hv _ _ sub_32_36))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_144_146) (g362)) (g363)) (hv _ _ sub_32_36)))⟩
  · rcases le_or_gt (v s36) (v s146) with g364 | g364
    · exact h2 ⟨Or.inl (g364), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g362)))⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_trans (g362) (g364))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_144_146) (g364)))⟩
theorem cl377 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_1 v) (h1 : ¬acc0_1 v) (h2 : ¬acc2_0 v) : False := by
  rcases le_or_gt (v s150) (v s72) with g365 | g365
  · exact h0 ⟨Or.inl (g365), hv _ _ sub_0_72⟩
  · rcases le_or_gt (v s149) (v s72) with g366 | g366
    · exact h0 ⟨Or.inr (Or.inl (g366)), hv _ _ sub_0_72⟩
    · rcases le_or_gt (v s147) (v s72) with g367 | g367
      · exact h0 ⟨Or.inr (Or.inr (Or.inl (g367))), hv _ _ sub_0_72⟩
      · rcases le_or_gt (v s147) (v s36) with g368 | g368
        · exact h1 ⟨Or.inr (Or.inr (Or.inl (g368))), hv _ _ sub_0_36⟩
        · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_32_36) (g368))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g367)))⟩
theorem cl379 (v : Finset (Fin 8) → α) (_hv : IsMonotoneVal v) (h0 : ¬acc16_2 v) (h1 : ¬acc2_1 v) (h2 : ¬acc17_1 v) : False := by
  rcases le_or_gt (v s36) (v s64) with g369 | g369
  · rcases le_or_gt (v s146) (v s64) with g370 | g370
    · exact h0 ⟨Or.inl (g369), Or.inl (g370)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (g369) (g370))), Or.inl (le_of_lt (g370))⟩
  · rcases le_or_gt (v s146) (v s36) with g371 | g371
    · exact h1 ⟨Or.inl (g371), Or.inl (le_of_lt (g369))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g371)), Or.inl (le_of_lt (lt_trans (g369) (g371)))⟩
theorem cl382 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc15_1 v) (h1 : ¬acc9_1 v) (h2 : ¬acc2_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g372 | g372
  · rcases le_or_gt (v s72) (v s146) with g373 | g373
    · rcases h0a with g374 | g374 | g374
      · exact h1 ⟨Or.inl (g373), Or.inl (le_trans (le_trans (hv _ _ sub_32_38) (g374)) (g373))⟩
      · exact h1 ⟨Or.inl (g373), Or.inl (le_trans (le_trans (hv _ _ sub_32_37) (g374)) (g373))⟩
      · exact h1 ⟨Or.inl (g373), Or.inr (le_trans (le_trans (hv _ _ sub_4_7) (g374)) (g373))⟩
    · rcases h0a with g375 | g375 | g375
      · exact h2 ⟨Or.inl (le_of_lt (g373)), Or.inl (le_trans (hv _ _ sub_32_38) (g375))⟩
      · exact h2 ⟨Or.inl (le_of_lt (g373)), Or.inl (le_trans (hv _ _ sub_32_37) (g375))⟩
      · exact h2 ⟨Or.inl (le_of_lt (g373)), Or.inr (le_trans (hv _ _ sub_4_7) (g375))⟩
  · rcases le_or_gt (v s72) (v s146) with g376 | g376
    · rcases h0a with g377 | g377 | g377
      · exact h1 ⟨Or.inl (g376), Or.inl (le_trans (le_trans (hv _ _ sub_32_38) (g377)) (g376))⟩
      · exact h1 ⟨Or.inl (g376), Or.inl (le_trans (le_trans (hv _ _ sub_32_37) (g377)) (g376))⟩
      · exact h1 ⟨Or.inl (g376), Or.inr (le_trans (le_trans (hv _ _ sub_4_7) (g377)) (g376))⟩
    · rcases h0a with g378 | g378 | g378
      · exact h2 ⟨Or.inl (le_of_lt (g376)), Or.inl (le_trans (hv _ _ sub_32_38) (g378))⟩
      · exact h2 ⟨Or.inl (le_of_lt (g376)), Or.inl (le_trans (hv _ _ sub_32_37) (g378))⟩
      · exact h2 ⟨Or.inl (le_of_lt (g376)), Or.inr (le_trans (hv _ _ sub_4_7) (g378))⟩
theorem cl384 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc16_2 v) (h1 : ¬acc17_1 v) (h2 : ¬acc16_0 v) : False := by
  rcases le_or_gt (v s36) (v s146) with g379 | g379
  · rcases le_or_gt (v s146) (v s64) with g380 | g380
    · exact h0 ⟨Or.inl (le_trans (g379) (g380)), Or.inl (g380)⟩
    · exact h1 ⟨Or.inl (g379), Or.inl (le_of_lt (g380))⟩
  · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g379) (hv _ _ sub_36_37))), hv _ _ sub_0_37⟩
theorem cl385 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc14_2 v) (h1 : ¬acc17_1 v) (h2 : ¬acc16_0 v) : False := by
  rcases le_or_gt (v s36) (v s146) with g381 | g381
  · rcases le_or_gt (v s144) (v s64) with g382 | g382
    · rcases le_or_gt (v s37) (v s64) with g383 | g383
      · exact h0 ⟨Or.inl (g383), Or.inl (g382)⟩
      · rcases le_or_gt (v s64) (v s146) with g384 | g384
        · exact h1 ⟨Or.inl (g381), Or.inl (g384)⟩
        · exact h2 ⟨Or.inl (le_of_lt (lt_trans (g384) (g383))), hv _ _ sub_0_37⟩
    · exact h1 ⟨Or.inl (g381), Or.inl (le_of_lt (lt_of_lt_of_le (g382) (hv _ _ sub_144_146)))⟩
  · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g381) (hv _ _ sub_36_37))), hv _ _ sub_0_37⟩
theorem cl387 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc16_2 v) (h1 : ¬acc14_2 v) (h2 : ¬acc17_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g385 | g385
  · rcases h0b with g386 | g386
    · rcases le_or_gt (v s37) (v s64) with g387 | g387
      · exact h1 ⟨Or.inl (g387), Or.inl (le_trans (hv _ _ sub_144_146) (g386))⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (le_trans (hv _ _ sub_144_146) (g386)) (g387))), Or.inl (le_of_lt (g387))⟩
    · rcases le_or_gt (v s37) (v s64) with g388 | g388
      · exact h1 ⟨Or.inl (g388), Or.inr (le_trans (hv _ _ sub_18_26) (g386))⟩
      · exact h2 ⟨Or.inr (le_of_lt (lt_of_le_of_lt (le_trans (hv _ _ sub_18_26) (g386)) (g388))), Or.inl (le_of_lt (g388))⟩
  · rcases h0b with g389 | g389
    · rcases le_or_gt (v s37) (v s64) with g390 | g390
      · exact h1 ⟨Or.inl (g390), Or.inl (le_trans (hv _ _ sub_144_146) (g389))⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (le_trans (hv _ _ sub_144_146) (g389)) (g390))), Or.inl (le_of_lt (g390))⟩
    · rcases le_or_gt (v s37) (v s64) with g391 | g391
      · exact h1 ⟨Or.inl (g391), Or.inr (le_trans (hv _ _ sub_18_26) (g389))⟩
      · exact h2 ⟨Or.inr (le_of_lt (lt_of_le_of_lt (le_trans (hv _ _ sub_18_26) (g389)) (g391))), Or.inl (le_of_lt (g391))⟩
theorem cl388 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_2 v) (h1 : ¬acc17_1 v) (h2 : ¬acc17_2 v) : False := by
  rcases le_or_gt (v s72) (v s36) with g392 | g392
  · rcases le_or_gt (v s144) (v s36) with g393 | g393
    · exact h0 ⟨Or.inl (g392), Or.inl (g393)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g393) (hv _ _ sub_144_146))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_64_72) (g392)) (g393)) (hv _ _ sub_144_146)))⟩
  · rcases le_or_gt (v s144) (v s72) with g394 | g394
    · exact h2 ⟨Or.inl (le_of_lt (g392)), Or.inl (g394)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (g392) (g394)) (hv _ _ sub_144_146))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g394)) (hv _ _ sub_144_146)))⟩
theorem cl389 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_0 v) (h1 : ¬acc17_2 v) (h2 : ¬acc2_1 v) : False := by
  rcases le_or_gt (v s32) (v s147) with g395 | g395
  · rcases le_or_gt (v s64) (v s147) with g396 | g396
    · exact h0 ⟨Or.inl (g395), Or.inl (g396)⟩
    · rcases le_or_gt (v s36) (v s72) with g397 | g397
      · exact h1 ⟨Or.inl (g397), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_144_147) (g396)) (hv _ _ sub_64_72)))⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_trans (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_146_147) (g396)) (hv _ _ sub_64_72)) (g397))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g397)))⟩
  · rcases le_or_gt (v s36) (v s72) with g398 | g398
    · exact h1 ⟨Or.inl (g398), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_144_147) (g395)) (hv _ _ sub_32_36)) (g398)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_146_147) (g395)) (hv _ _ sub_32_36))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g398)))⟩
theorem cl390 (v : Finset (Fin 8) → α) (_hv : IsMonotoneVal v) (h0 : ¬acc0_2 v) (h1 : ¬acc1_2 v) (h2 : ¬acc2_0 v) : False := by
  rcases le_or_gt (v s154) (v s64) with g399 | g399
  · rcases le_or_gt (v s32) (v s64) with g400 | g400
    · exact h0 ⟨Or.inl (g399), Or.inl (g400)⟩
    · rcases le_or_gt (v s147) (v s32) with g401 | g401
      · exact h1 ⟨Or.inr (Or.inr (Or.inl (g401))), Or.inl (le_of_lt (g400))⟩
      · exact h2 ⟨Or.inl (le_of_lt (g401)), Or.inl (le_of_lt (lt_trans (g400) (g401)))⟩
  · rcases le_or_gt (v s153) (v s64) with g402 | g402
    · rcases le_or_gt (v s32) (v s64) with g403 | g403
      · exact h0 ⟨Or.inr (Or.inl (g402)), Or.inl (g403)⟩
      · rcases le_or_gt (v s147) (v s32) with g404 | g404
        · exact h1 ⟨Or.inr (Or.inr (Or.inl (g404))), Or.inl (le_of_lt (g403))⟩
        · exact h2 ⟨Or.inl (le_of_lt (g404)), Or.inl (le_of_lt (lt_trans (g403) (g404)))⟩
    · rcases le_or_gt (v s147) (v s64) with g405 | g405
      · rcases le_or_gt (v s32) (v s64) with g406 | g406
        · exact h0 ⟨Or.inr (Or.inr (Or.inl (g405))), Or.inl (g406)⟩
        · exact h1 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (g405) (g406))))), Or.inl (le_of_lt (g406))⟩
      · rcases le_or_gt (v s147) (v s32) with g407 | g407
        · exact h1 ⟨Or.inr (Or.inr (Or.inl (g407))), Or.inl (le_of_lt (lt_of_lt_of_le (g405) (g407)))⟩
        · exact h2 ⟨Or.inl (le_of_lt (g407)), Or.inl (le_of_lt (g405))⟩
theorem cl392 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc14_1 v) (h1 : ¬acc17_1 v) (h2 : ¬acc17_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g408 | g408
  · rcases le_or_gt (v s64) (v s146) with g409 | g409
    · exact h1 ⟨Or.inl (le_trans (hv _ _ sub_36_37) (g408)), Or.inl (g409)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_36_37) (g408)) (g409)) (hv _ _ sub_64_72))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_144_146) (g409)) (hv _ _ sub_64_72)))⟩
  · exact h1 ⟨Or.inr (le_trans (hv _ _ sub_5_13) (g408)), Or.inr (le_trans (hv _ _ sub_8_13) (g408))⟩
theorem cl393 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc9_1 v) (h1 : acc14_1 v) (h2 : ¬acc17_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  obtain ⟨h1a, h1b⟩ := h1
  rcases h1a with g410 | g410
  · rcases h0a with g411 | g411
    · exact h2 ⟨Or.inl (le_trans (hv _ _ sub_36_37) (g410)), Or.inl (le_trans (hv _ _ sub_64_72) (g411))⟩
    · exact h2 ⟨Or.inl (le_trans (hv _ _ sub_36_37) (g410)), Or.inr (le_trans (hv _ _ sub_8_9) (g411))⟩
  · exact h2 ⟨Or.inr (le_trans (hv _ _ sub_5_13) (g410)), Or.inr (le_trans (hv _ _ sub_8_13) (g410))⟩
theorem cl394 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_2 v) (h1 : ¬acc17_1 v) (h2 : ¬acc2_1 v) : False := by
  rcases le_or_gt (v s146) (v s72) with g412 | g412
  · rcases le_or_gt (v s32) (v s72) with g413 | g413
    · exact h0 ⟨Or.inl (g412), Or.inl (g413)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (g412) (g413)) (hv _ _ sub_32_36))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g413)) (hv _ _ sub_32_36)))⟩
  · rcases le_or_gt (v s36) (v s146) with g414 | g414
    · exact h1 ⟨Or.inl (g414), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g412)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g414)), Or.inl (le_of_lt (lt_trans (lt_of_le_of_lt (hv _ _ sub_64_72) (g412)) (g414)))⟩
theorem cl397 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc16_2 v) (h1 : ¬acc2_2 v) (h2 : ¬acc17_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g415 | g415
  · rcases le_or_gt (v s146) (v s72) with g416 | g416
    · exact h1 ⟨Or.inl (g416), Or.inl (le_trans (le_trans (hv _ _ sub_32_36) (g415)) (hv _ _ sub_64_72))⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (le_trans (g415) (hv _ _ sub_64_72)) (g416))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g416)))⟩
  · rcases le_or_gt (v s146) (v s72) with g417 | g417
    · exact h1 ⟨Or.inl (g417), Or.inr (le_trans (le_trans (hv _ _ sub_4_5) (g415)) (hv _ _ sub_64_72))⟩
    · exact h2 ⟨Or.inr (le_of_lt (lt_of_le_of_lt (le_trans (g415) (hv _ _ sub_64_72)) (g417))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g417)))⟩
theorem cl401 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_2 v) (h1 : ¬acc7_0 v) (h2 : ¬acc9_1 v) : False := by
  rcases le_or_gt (v s73) (v s32) with g418 | g418
  · rcases le_or_gt (v s144) (v s32) with g419 | g419
    · exact h0 ⟨Or.inl (g418), Or.inl (g419)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_72_73) (g418)) (g419)) (hv _ _ sub_144_146))), Or.inl (le_of_lt (lt_of_lt_of_le (g419) (hv _ _ sub_144_146)))⟩
  · rcases le_or_gt (v s128) (v s75) with g420 | g420
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g418) (hv _ _ sub_73_75))), Or.inl (g420)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_75) (g420)) (hv _ _ sub_128_146))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (g418) (hv _ _ sub_73_75)) (g420)) (hv _ _ sub_128_146)))⟩
theorem cl403 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_2 v) (h1 : ¬acc8_0 v) (h2 : ¬acc9_1 v) : False := by
  rcases le_or_gt (v s146) (v s73) with g421 | g421
  · exact h1 ⟨Or.inl (g421), hv _ _ sub_0_73⟩
  · rcases le_or_gt (v s32) (v s146) with g422 | g422
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_72_73) (g421))), Or.inl (g422)⟩
    · exact h0 ⟨Or.inl (le_of_lt (lt_trans (g421) (g422))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_144_146) (g422)))⟩
theorem cl404 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_2 v) (h1 : ¬acc8_0 v) (h2 : ¬acc2_0 v) : False := by
  rcases le_or_gt (v s146) (v s73) with g423 | g423
  · exact h1 ⟨Or.inl (g423), hv _ _ sub_0_73⟩
  · rcases le_or_gt (v s32) (v s147) with g424 | g424
    · exact h2 ⟨Or.inl (g424), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_73) (g423)) (hv _ _ sub_146_147)))⟩
    · exact h0 ⟨Or.inl (le_of_lt (lt_trans (lt_of_lt_of_le (g423) (hv _ _ sub_146_147)) (g424))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_144_147) (g424)))⟩
theorem cl405 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc11_2 v) (h1 : ¬acc6_0 v) (h2 : ¬acc7_1 v) : False := by
  rcases le_or_gt (v s72) (v s144) with g425 | g425
  · rcases le_or_gt (v s9) (v s144) with g426 | g426
    · rcases le_or_gt (v s36) (v s144) with g427 | g427
      · exact h0 ⟨Or.inl (g425), Or.inl (g427)⟩
      · rcases le_or_gt (v s144) (v s77) with g428 | g428
        · exact h1 ⟨Or.inl (g428), hv _ _ sub_0_77⟩
        · exact h2 ⟨Or.inr (Or.inl (le_of_lt (lt_trans (lt_of_le_of_lt (hv _ _ sub_73_77) (g428)) (g427)))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_128_144) (g427)))⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g426) (hv _ _ sub_9_77))), hv _ _ sub_0_77⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g425) (hv _ _ sub_72_77))), hv _ _ sub_0_77⟩
theorem cl406 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_0 v) (h1 : ¬acc7_1 v) (h2 : ¬acc7_2 v) : False := by
  rcases le_or_gt (v s144) (v s73) with g429 | g429
  · rcases le_or_gt (v s32) (v s73) with g430 | g430
    · exact h0 ⟨Or.inl (g429), Or.inl (g430)⟩
    · exact h1 ⟨Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (g430) (hv _ _ sub_32_36)))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_128_144) (g429)) (g430)) (hv _ _ sub_32_36)))⟩
  · rcases le_or_gt (v s32) (v s144) with g431 | g431
    · exact h2 ⟨Or.inr (Or.inl (le_of_lt (g429))), Or.inl (g431)⟩
    · exact h1 ⟨Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (g429) (g431)) (hv _ _ sub_32_36)))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_144) (g431)) (hv _ _ sub_32_36)))⟩
theorem cl407 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_1 v) (h1 : ¬acc5_2 v) (h2 : ¬acc7_0 v) : False := by
  rcases le_or_gt (v s78) (v s144) with g432 | g432
  · exact h0 ⟨Or.inl (g432), hv _ _ sub_0_144⟩
  · rcases le_or_gt (v s77) (v s144) with g433 | g433
    · exact h0 ⟨Or.inr (Or.inl (g433)), hv _ _ sub_0_144⟩
    · rcases le_or_gt (v s75) (v s144) with g434 | g434
      · exact h0 ⟨Or.inr (Or.inr (Or.inl (g434))), hv _ _ sub_0_144⟩
      · rcases le_or_gt (v s75) (v s32) with g435 | g435
        · exact h1 ⟨Or.inr (Or.inr (Or.inl (g435))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_144) (g434)) (g435)))⟩
        · exact h2 ⟨Or.inl (le_of_lt (g435)), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_128_144) (g434)))⟩
theorem cl408 (v : Finset (Fin 8) → α) (_hv : IsMonotoneVal v) (h0 : ¬acc6_2 v) (h1 : ¬acc9_0 v) (h2 : ¬acc7_2 v) : False := by
  rcases le_or_gt (v s73) (v s32) with g436 | g436
  · rcases le_or_gt (v s144) (v s32) with g437 | g437
    · exact h0 ⟨Or.inl (g436), Or.inl (g437)⟩
    · exact h2 ⟨Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (g436) (g437)))), Or.inl (le_of_lt (g437))⟩
  · rcases le_or_gt (v s144) (v s73) with g438 | g438
    · exact h1 ⟨Or.inl (g438), Or.inl (le_of_lt (g436))⟩
    · exact h2 ⟨Or.inr (Or.inl (le_of_lt (g438))), Or.inl (le_of_lt (lt_trans (g436) (g438)))⟩
theorem cl410 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc11_2 v) (h1 : ¬acc7_1 v) (h2 : ¬acc11_0 v) : False := by
  rcases le_or_gt (v s72) (v s144) with g439 | g439
  · rcases le_or_gt (v s36) (v s144) with g440 | g440
    · exact h0 ⟨Or.inl (g439), Or.inl (g440)⟩
    · rcases le_or_gt (v s73) (v s36) with g441 | g441
      · exact h1 ⟨Or.inr (Or.inl (g441)), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_128_144) (g440)))⟩
      · exact h2 ⟨Or.inl (le_of_lt (g441)), Or.inl (le_of_lt (lt_trans (lt_of_le_of_lt (hv _ _ sub_128_144) (g440)) (g441)))⟩
  · rcases le_or_gt (v s73) (v s36) with g442 | g442
    · exact h1 ⟨Or.inr (Or.inl (g442)), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_144) (g439)) (hv _ _ sub_72_73)) (g442)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g442)), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_144) (g439)) (hv _ _ sub_72_73)))⟩
theorem cl411 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_0 v) (h1 : ¬acc11_2 v) (h2 : ¬acc7_1 v) : False := by
  rcases le_or_gt (v s144) (v s73) with g443 | g443
  · rcases le_or_gt (v s32) (v s73) with g444 | g444
    · exact h0 ⟨Or.inl (g443), Or.inl (g444)⟩
    · exact h2 ⟨Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (g444) (hv _ _ sub_32_36)))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_128_144) (g443)) (g444)) (hv _ _ sub_32_36)))⟩
  · rcases le_or_gt (v s36) (v s144) with g445 | g445
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_72_73) (g443))), Or.inl (g445)⟩
    · exact h2 ⟨Or.inr (Or.inl (le_of_lt (lt_trans (g443) (g445)))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_128_144) (g445)))⟩
theorem cl412 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_0 v) (h1 : ¬acc15_2 v) (h2 : ¬acc11_1 v) : False := by
  rcases le_or_gt (v s38) (v s73) with g446 | g446
  · exact h0 ⟨Or.inl (g446), hv _ _ sub_0_73⟩
  · rcases le_or_gt (v s38) (v s144) with g447 | g447
    · exact h1 ⟨Or.inl (g447), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_73) (g446)) (g447)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_72_73) (g446))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_128_144) (g447)))⟩
theorem cl413 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_0 v) (h1 : ¬acc17_0 v) (h2 : ¬acc14_1 v) : False := by
  rcases le_or_gt (v s144) (v s37) with g448 | g448
  · rcases le_or_gt (v s64) (v s37) with g449 | g449
    · exact h1 ⟨Or.inl (g448), Or.inl (g449)⟩
    · exact h0 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (g448) (g449)) (hv _ _ sub_64_73))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_37) (g449)) (hv _ _ sub_64_73)))⟩
  · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g448) (hv _ _ sub_144_146))), hv _ _ sub_0_146⟩
theorem cl414 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc4_2 v) (h1 : ¬acc10_0 v) (h2 : ¬acc11_1 v) : False := by
  rcases le_or_gt (v s38) (v s73) with g450 | g450
  · exact h1 ⟨Or.inl (g450), hv _ _ sub_0_73⟩
  · rcases le_or_gt (v s128) (v s38) with g451 | g451
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_72_73) (g450))), Or.inl (g451)⟩
    · exact h0 ⟨Or.inl (le_of_lt (lt_trans (g450) (g451))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_36_38) (g451)))⟩
theorem cl415 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_0 v) (h1 : ¬acc4_1 v) (h2 : ¬acc15_2 v) : False := by
  rcases le_or_gt (v s32) (v s73) with g452 | g452
  · rcases le_or_gt (v s144) (v s73) with g453 | g453
    · exact h0 ⟨Or.inl (g453), Or.inl (g452)⟩
    · rcases le_or_gt (v s73) (v s38) with g454 | g454
      · exact h1 ⟨Or.inl (g454), hv _ _ sub_0_38⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_trans (g454) (g453))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_73) (g453)))⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g452) (hv _ _ sub_32_38))), hv _ _ sub_0_38⟩
theorem cl416 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc4_2 v) (h1 : ¬acc11_0 v) (h2 : ¬acc4_1 v) : False := by
  rcases le_or_gt (v s36) (v s73) with g455 | g455
  · rcases le_or_gt (v s73) (v s128) with g456 | g456
    · exact h0 ⟨Or.inl (g456), Or.inl (le_trans (g455) (g456))⟩
    · exact h1 ⟨Or.inl (g455), Or.inl (le_of_lt (g456))⟩
  · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g455) (hv _ _ sub_36_38))), hv _ _ sub_0_38⟩
theorem cl417 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc11_2 v) (h1 : ¬acc15_2 v) (h2 : ¬acc17_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g457 | g457
  · rcases le_or_gt (v s37) (v s144) with g458 | g458
    · exact h1 ⟨Or.inr (Or.inl (g458)), Or.inl (le_trans (hv _ _ sub_64_72) (g457))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g458)), Or.inl (le_of_lt (lt_of_le_of_lt (le_trans (hv _ _ sub_64_72) (g457)) (g458)))⟩
  · rcases le_or_gt (v s37) (v s144) with g459 | g459
    · exact h1 ⟨Or.inr (Or.inl (g459)), Or.inr (le_trans (hv _ _ sub_8_9) (g457))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g459)), Or.inr (le_of_lt (lt_of_le_of_lt (le_trans (hv _ _ sub_8_9) (g457)) (g459)))⟩
theorem cl418 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_1 v) (h1 : ¬acc12_2 v) (h2 : ¬acc15_0 v) : False := by
  rcases le_or_gt (v s38) (v s72) with g460 | g460
  · rcases le_or_gt (v s128) (v s72) with g461 | g461
    · exact h0 ⟨Or.inl (g460), Or.inl (g461)⟩
    · rcases le_or_gt (v s39) (v s128) with g462 | g462
      · exact h1 ⟨Or.inr (Or.inr (Or.inl (g462))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g461)))⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_trans (lt_of_le_of_lt (hv _ _ sub_64_72) (g461)) (g462))), Or.inl (le_of_lt (g462))⟩
  · rcases le_or_gt (v s39) (v s128) with g463 | g463
    · exact h1 ⟨Or.inr (Or.inr (Or.inl (g463))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g460)) (hv _ _ sub_38_39)) (g463)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g460)) (hv _ _ sub_38_39))), Or.inl (le_of_lt (g463))⟩
theorem cl421 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_2 v) (h1 : ¬acc11_0 v) (h2 : ¬acc17_1 v) : False := by
  rcases le_or_gt (v s72) (v s36) with g464 | g464
  · rcases le_or_gt (v s144) (v s36) with g465 | g465
    · exact h0 ⟨Or.inl (g464), Or.inl (g465)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g465) (hv _ _ sub_144_146))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_64_72) (g464)) (g465)) (hv _ _ sub_144_146)))⟩
  · rcases le_or_gt (v s128) (v s73) with g466 | g466
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g464) (hv _ _ sub_72_73))), Or.inl (g466)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (g464) (hv _ _ sub_72_73)) (g466)) (hv _ _ sub_128_146))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_73) (g466)) (hv _ _ sub_128_146)))⟩
theorem cl422 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc5_1 v) (h1 : ¬acc3_1 v) (h2 : ¬acc7_0 v) : False := by
  rcases le_or_gt (v s78) (v s144) with g467 | g467
  · exact h0 ⟨Or.inl (g467), hv _ _ sub_0_144⟩
  · rcases le_or_gt (v s77) (v s144) with g468 | g468
    · exact h0 ⟨Or.inr (Or.inl (g468)), hv _ _ sub_0_144⟩
    · rcases le_or_gt (v s75) (v s144) with g469 | g469
      · exact h0 ⟨Or.inr (Or.inr (Or.inl (g469))), hv _ _ sub_0_144⟩
      · rcases le_or_gt (v s75) (v s36) with g470 | g470
        · exact h1 ⟨Or.inr (Or.inr (Or.inl (g470))), hv _ _ sub_0_36⟩
        · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_32_36) (g470))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_128_144) (g469)))⟩
theorem cl423 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc8_0 v) (h1 : ¬acc11_0 v) (h2 : ¬acc4_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g471 | g471
  · rcases le_or_gt (v s36) (v s73) with g472 | g472
    · exact h1 ⟨Or.inl (g472), Or.inl (le_trans (hv _ _ sub_128_146) (g471))⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g472) (hv _ _ sub_36_38))), hv _ _ sub_0_38⟩
  · exact h1 ⟨Or.inr (le_trans (hv _ _ sub_6_22) (g471)), Or.inr (le_trans (hv _ _ sub_16_22) (g471))⟩
theorem cl424 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc7_2 v) (h1 : ¬acc17_0 v) (h2 : ¬acc15_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g473 | g473
  · rcases le_or_gt (v s144) (v s37) with g474 | g474
    · rcases h0a with g475 | g475 | g475
      · exact h1 ⟨Or.inl (g474), Or.inl (le_trans (le_trans (hv _ _ sub_64_74) (g475)) (g474))⟩
      · exact h1 ⟨Or.inl (g474), Or.inl (le_trans (le_trans (hv _ _ sub_64_73) (g475)) (g474))⟩
      · exact h1 ⟨Or.inl (g474), Or.inr (le_trans (le_trans (hv _ _ sub_8_11) (g475)) (g474))⟩
    · rcases h0a with g476 | g476 | g476
      · exact h2 ⟨Or.inr (Or.inl (le_of_lt (g474))), Or.inl (le_trans (hv _ _ sub_64_74) (g476))⟩
      · exact h2 ⟨Or.inr (Or.inl (le_of_lt (g474))), Or.inl (le_trans (hv _ _ sub_64_73) (g476))⟩
      · exact h2 ⟨Or.inr (Or.inl (le_of_lt (g474))), Or.inr (le_trans (hv _ _ sub_8_11) (g476))⟩
  · rcases le_or_gt (v s144) (v s37) with g477 | g477
    · rcases h0a with g478 | g478 | g478
      · exact h1 ⟨Or.inl (g477), Or.inl (le_trans (le_trans (hv _ _ sub_64_74) (g478)) (g477))⟩
      · exact h1 ⟨Or.inl (g477), Or.inl (le_trans (le_trans (hv _ _ sub_64_73) (g478)) (g477))⟩
      · exact h1 ⟨Or.inl (g477), Or.inr (le_trans (le_trans (hv _ _ sub_8_11) (g478)) (g477))⟩
    · rcases h0a with g479 | g479 | g479
      · exact h2 ⟨Or.inr (Or.inl (le_of_lt (g477))), Or.inl (le_trans (hv _ _ sub_64_74) (g479))⟩
      · exact h2 ⟨Or.inr (Or.inl (le_of_lt (g477))), Or.inl (le_trans (hv _ _ sub_64_73) (g479))⟩
      · exact h2 ⟨Or.inr (Or.inl (le_of_lt (g477))), Or.inr (le_trans (hv _ _ sub_8_11) (g479))⟩
theorem cl425 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc11_0 v) (h1 : ¬acc4_1 v) (h2 : ¬acc11_2 v) : False := by
  rcases le_or_gt (v s36) (v s73) with g480 | g480
  · rcases le_or_gt (v s128) (v s73) with g481 | g481
    · exact h0 ⟨Or.inl (g480), Or.inl (g481)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_72_73) (g481)) (hv _ _ sub_128_144))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (g480) (g481)) (hv _ _ sub_128_144)))⟩
  · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g480) (hv _ _ sub_36_38))), hv _ _ sub_0_38⟩
theorem cl426 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc7_1 v) (h1 : ¬acc11_0 v) (h2 : ¬acc7_2 v) : False := by
  rcases le_or_gt (v s74) (v s36) with g482 | g482
  · rcases le_or_gt (v s128) (v s36) with g483 | g483
    · exact h0 ⟨Or.inl (g482), Or.inl (g483)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (g482) (g483)) (hv _ _ sub_128_144))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_36) (g483)) (hv _ _ sub_128_144)))⟩
  · rcases le_or_gt (v s74) (v s144) with g484 | g484
    · exact h2 ⟨Or.inl (g484), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_36) (g482)) (g484)))⟩
    · rcases le_or_gt (v s73) (v s36) with g485 | g485
      · rcases le_or_gt (v s128) (v s36) with g486 | g486
        · exact h0 ⟨Or.inr (Or.inl (g485)), Or.inl (g486)⟩
        · exact h2 ⟨Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (g485) (g486)) (hv _ _ sub_128_144)))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_36) (g486)) (hv _ _ sub_128_144)))⟩
      · rcases le_or_gt (v s128) (v s73) with g487 | g487
        · exact h1 ⟨Or.inl (le_of_lt (g485)), Or.inl (g487)⟩
        · exact h2 ⟨Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (g487) (hv _ _ sub_128_144)))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (lt_of_le_of_lt (hv _ _ sub_32_36) (g485)) (g487)) (hv _ _ sub_128_144)))⟩
theorem cl427 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc4_1 v) (h1 : ¬acc11_0 v) (h2 : ¬acc7_2 v) : False := by
  rcases le_or_gt (v s73) (v s38) with g488 | g488
  · exact h0 ⟨Or.inl (g488), hv _ _ sub_0_38⟩
  · rcases le_or_gt (v s128) (v s73) with g489 | g489
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_36_38) (g488))), Or.inl (g489)⟩
    · exact h2 ⟨Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (g489) (hv _ _ sub_128_144)))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (lt_of_le_of_lt (hv _ _ sub_32_38) (g488)) (g489)) (hv _ _ sub_128_144)))⟩
theorem cl428 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc9_0 v) (h1 : ¬acc7_1 v) (h2 : ¬acc11_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g490 | g490
  · rcases le_or_gt (v s73) (v s36) with g491 | g491
    · exact h1 ⟨Or.inr (Or.inl (g491)), Or.inl (le_trans (le_trans (hv _ _ sub_128_144) (g490)) (g491))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g491)), Or.inl (le_trans (hv _ _ sub_128_144) (g490))⟩
  · rcases le_or_gt (v s73) (v s36) with g492 | g492
    · exact h1 ⟨Or.inr (Or.inl (g492)), Or.inr (le_trans (le_trans (hv _ _ sub_16_18) (g490)) (g492))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g492)), Or.inr (le_trans (hv _ _ sub_16_18) (g490))⟩
theorem cl429 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc9_0 v) (h1 : ¬acc4_1 v) (h2 : ¬acc11_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases le_or_gt (v s73) (v s38) with g493 | g493
  · exact h1 ⟨Or.inl (g493), hv _ _ sub_0_38⟩
  · rcases h0a with g494 | g494
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_36_38) (g493))), Or.inl (le_trans (hv _ _ sub_128_144) (g494))⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_36_38) (g493))), Or.inr (le_trans (hv _ _ sub_16_18) (g494))⟩
theorem cl430 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_0 v) (h1 : ¬acc12_1 v) (h2 : ¬acc12_2 v) : False := by
  rcases le_or_gt (v s64) (v s39) with g495 | g495
  · rcases le_or_gt (v s128) (v s39) with g496 | g496
    · exact h0 ⟨Or.inl (g495), Or.inl (g496)⟩
    · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (g496)))), Or.inl (le_of_lt (lt_of_le_of_lt (g495) (g496)))⟩
  · exact h1 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (g495) (hv _ _ sub_64_72))))), hv _ _ sub_0_72⟩
theorem cl432 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_0 v) (h1 : ¬acc17_2 v) (h2 : ¬acc13_1 v) : False := by
  rcases le_or_gt (v s128) (v s39) with g497 | g497
  · rcases le_or_gt (v s64) (v s39) with g498 | g498
    · exact h0 ⟨Or.inl (g498), Or.inl (g497)⟩
    · rcases le_or_gt (v s144) (v s72) with g499 | g499
      · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_36_39) (g498)) (hv _ _ sub_64_72))), Or.inl (g499)⟩
      · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_trans (lt_of_lt_of_le (g498) (hv _ _ sub_64_72)) (g499))))), hv _ _ sub_0_144⟩
  · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (g497) (hv _ _ sub_128_144))))), hv _ _ sub_0_144⟩
theorem cl433 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_0 v) (h1 : ¬acc14_2 v) (h2 : ¬acc13_1 v) : False := by
  rcases le_or_gt (v s128) (v s39) with g500 | g500
  · rcases le_or_gt (v s64) (v s39) with g501 | g501
    · exact h0 ⟨Or.inl (g501), Or.inl (g500)⟩
    · rcases le_or_gt (v s144) (v s64) with g502 | g502
      · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_37_39) (g501))), Or.inl (g502)⟩
      · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_trans (g501) (g502))))), hv _ _ sub_0_144⟩
  · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (g500) (hv _ _ sub_128_144))))), hv _ _ sub_0_144⟩
theorem cl435 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc3_2 v) (h1 : ¬acc15_0 v) (h2 : ¬acc7_0 v) : False := by
  rcases le_or_gt (v s90) (v s128) with g503 | g503
  · rcases le_or_gt (v s32) (v s128) with g504 | g504
    · exact h0 ⟨Or.inl (g503), Or.inl (g504)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_64_90) (g503)) (g504)) (hv _ _ sub_32_39))), Or.inl (le_of_lt (lt_of_lt_of_le (g504) (hv _ _ sub_32_39)))⟩
  · rcases le_or_gt (v s89) (v s128) with g505 | g505
    · rcases le_or_gt (v s32) (v s128) with g506 | g506
      · exact h0 ⟨Or.inr (Or.inl (g505)), Or.inl (g506)⟩
      · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_64_89) (g505)) (g506)) (hv _ _ sub_32_39))), Or.inl (le_of_lt (lt_of_lt_of_le (g506) (hv _ _ sub_32_39)))⟩
    · rcases le_or_gt (v s75) (v s128) with g507 | g507
      · rcases le_or_gt (v s32) (v s128) with g508 | g508
        · exact h0 ⟨Or.inr (Or.inr (Or.inl (g507))), Or.inl (g508)⟩
        · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_64_75) (g507)) (g508)) (hv _ _ sub_32_39))), Or.inl (le_of_lt (lt_of_lt_of_le (g508) (hv _ _ sub_32_39)))⟩
      · rcases le_or_gt (v s32) (v s75) with g509 | g509
        · exact h2 ⟨Or.inl (g509), Or.inl (le_of_lt (g507))⟩
        · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_75) (g509)) (hv _ _ sub_32_39))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (g507) (g509)) (hv _ _ sub_32_39)))⟩
theorem cl436 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_0 v) (h1 : ¬acc13_1 v) (h2 : ¬acc13_2 v) : False := by
  rcases le_or_gt (v s128) (v s39) with g510 | g510
  · rcases le_or_gt (v s64) (v s39) with g511 | g511
    · exact h0 ⟨Or.inl (g511), Or.inl (g510)⟩
    · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (g511)))), Or.inl (le_of_lt (lt_of_le_of_lt (g510) (g511)))⟩
  · exact h1 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (g510) (hv _ _ sub_128_144))))), hv _ _ sub_0_144⟩
theorem cl438 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_0 v) (h1 : ¬acc15_2 v) (h2 : ¬acc13_2 v) : False := by
  rcases le_or_gt (v s64) (v s39) with g512 | g512
  · rcases le_or_gt (v s128) (v s39) with g513 | g513
    · exact h0 ⟨Or.inl (g512), Or.inl (g513)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_38_39) (g513)) (hv _ _ sub_128_144))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (g512) (g513)) (hv _ _ sub_128_144)))⟩
  · rcases le_or_gt (v s64) (v s144) with g514 | g514
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_38_39) (g512)) (g514))), Or.inl (g514)⟩
    · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (g512)))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_128_144) (g514)))⟩
theorem cl439 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc6_1 v) (h1 : acc15_2 v) (h2 : ¬acc9_1 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  obtain ⟨h1a, h1b⟩ := h1
  rcases h0a with g515 | g515
  · rcases h1a with g516 | g516 | g516
    · exact h2 ⟨Or.inl (le_trans (hv _ _ sub_72_73) (g515)), Or.inl (le_trans (le_trans (hv _ _ sub_32_38) (g516)) (hv _ _ sub_144_146))⟩
    · exact h2 ⟨Or.inl (le_trans (hv _ _ sub_72_73) (g515)), Or.inl (le_trans (le_trans (hv _ _ sub_32_37) (g516)) (hv _ _ sub_144_146))⟩
    · exact h2 ⟨Or.inl (le_trans (hv _ _ sub_72_73) (g515)), Or.inr (le_trans (le_trans (hv _ _ sub_4_7) (g516)) (hv _ _ sub_144_146))⟩
  · exact h2 ⟨Or.inr (le_trans (hv _ _ sub_9_13) (g515)), Or.inr (le_trans (hv _ _ sub_4_13) (g515))⟩
theorem cl441 (v : Finset (Fin 8) → α) (_hv : IsMonotoneVal v) (h0 : ¬acc15_0 v) (h1 : ¬acc13_2 v) (h2 : ¬acc12_2 v) : False := by
  rcases le_or_gt (v s64) (v s39) with g517 | g517
  · rcases le_or_gt (v s128) (v s39) with g518 | g518
    · exact h0 ⟨Or.inl (g517), Or.inl (g518)⟩
    · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (g518)))), Or.inl (le_of_lt (lt_of_le_of_lt (g517) (g518)))⟩
  · rcases le_or_gt (v s128) (v s64) with g519 | g519
    · exact h1 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (g517)))), Or.inl (g519)⟩
    · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_trans (g517) (g519))))), Or.inl (le_of_lt (g519))⟩
theorem cl443 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_0 v) (h1 : ¬acc16_2 v) (h2 : ¬acc14_1 v) : False := by
  rcases le_or_gt (v s128) (v s39) with g520 | g520
  · rcases le_or_gt (v s64) (v s39) with g521 | g521
    · exact h0 ⟨Or.inl (g521), Or.inl (g520)⟩
    · rcases le_or_gt (v s146) (v s64) with g522 | g522
      · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_36_39) (g521))), Or.inl (g522)⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_trans (lt_of_le_of_lt (hv _ _ sub_37_39) (g521)) (g522))), hv _ _ sub_0_146⟩
  · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_37_39) (g520)) (hv _ _ sub_128_146))), hv _ _ sub_0_146⟩
theorem cl446 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc1_1 v) (h1 : ¬acc0_1 v) (h2 : ¬acc2_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g523 | g523 | g523 | g523
  · exact h2 ⟨Or.inl (le_trans (hv _ _ sub_146_150) (g523)), Or.inr (le_trans (hv _ _ sub_4_150) (g523))⟩
  · exact h2 ⟨Or.inr (Or.inl (le_trans (hv _ _ sub_145_149) (g523))), Or.inr (le_trans (hv _ _ sub_4_149) (g523))⟩
  · rcases le_or_gt (v s147) (v s36) with g524 | g524
    · exact h1 ⟨Or.inr (Or.inr (Or.inl (g524))), hv _ _ sub_0_36⟩
    · exact h2 ⟨Or.inl (le_trans (hv _ _ sub_146_147) (g523)), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_36) (g524)) (g523)))⟩
  · exact h2 ⟨Or.inr (Or.inr (le_trans (hv _ _ sub_19_23) (g523))), Or.inr (le_trans (hv _ _ sub_4_23) (g523))⟩
theorem cl448 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc3_1 v) (h1 : ¬acc9_2 v) (h2 : ¬acc11_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g525 | g525 | g525 | g525
  · exact h1 ⟨Or.inl (le_trans (hv _ _ sub_72_90) (g525)), Or.inr (le_trans (hv _ _ sub_18_90) (g525))⟩
  · rcases le_or_gt (v s144) (v s36) with g526 | g526
    · exact h1 ⟨Or.inl (le_trans (hv _ _ sub_72_89) (g525)), Or.inl (g526)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (le_trans (hv _ _ sub_72_89) (g525)) (g526))), Or.inl (le_of_lt (g526))⟩
  · rcases le_or_gt (v s144) (v s36) with g527 | g527
    · exact h1 ⟨Or.inl (le_trans (hv _ _ sub_72_75) (g525)), Or.inl (g527)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (le_trans (hv _ _ sub_72_75) (g525)) (g527))), Or.inl (le_of_lt (g527))⟩
  · exact h1 ⟨Or.inr (le_trans (hv _ _ sub_9_27) (g525)), Or.inr (le_trans (hv _ _ sub_18_27) (g525))⟩
theorem cl452 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc17_0 v) (h1 : ¬acc16_2 v) (h2 : ¬acc14_1 v) : False := by
  rcases le_or_gt (v s144) (v s37) with g528 | g528
  · rcases le_or_gt (v s18) (v s37) with g529 | g529
    · rcases le_or_gt (v s64) (v s37) with g530 | g530
      · exact h0 ⟨Or.inl (g528), Or.inl (g530)⟩
      · rcases le_or_gt (v s146) (v s64) with g531 | g531
        · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_36_37) (g530))), Or.inl (g531)⟩
        · exact h2 ⟨Or.inl (le_of_lt (lt_trans (g530) (g531))), hv _ _ sub_0_146⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g529) (hv _ _ sub_18_146))), hv _ _ sub_0_146⟩
  · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g528) (hv _ _ sub_144_146))), hv _ _ sub_0_146⟩
theorem cl453 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_1 v) (h1 : ¬acc15_2 v) (h2 : ¬acc11_1 v) : False := by
  rcases le_or_gt (v s38) (v s72) with g532 | g532
  · rcases le_or_gt (v s128) (v s72) with g533 | g533
    · exact h0 ⟨Or.inl (g532), Or.inl (g533)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (g532) (g533)) (hv _ _ sub_128_144))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g533)) (hv _ _ sub_128_144)))⟩
  · rcases le_or_gt (v s38) (v s144) with g534 | g534
    · exact h1 ⟨Or.inl (g534), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g532)) (g534)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g532)), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_128_144) (g534)))⟩
theorem cl454 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc3_1 v) (h1 : ¬acc9_2 v) (h2 : ¬acc7_2 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g535 | g535 | g535 | g535
  · exact h1 ⟨Or.inl (le_trans (hv _ _ sub_72_90) (g535)), Or.inr (le_trans (hv _ _ sub_18_90) (g535))⟩
  · rcases le_or_gt (v s144) (v s36) with g536 | g536
    · exact h1 ⟨Or.inl (le_trans (hv _ _ sub_72_89) (g535)), Or.inl (g536)⟩
    · exact h2 ⟨Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (le_trans (hv _ _ sub_73_89) (g535)) (g536)))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_32_36) (g536)))⟩
  · rcases le_or_gt (v s144) (v s36) with g537 | g537
    · exact h1 ⟨Or.inl (le_trans (hv _ _ sub_72_75) (g535)), Or.inl (g537)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (le_trans (hv _ _ sub_74_75) (g535)) (g537))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_32_36) (g537)))⟩
  · exact h1 ⟨Or.inr (le_trans (hv _ _ sub_9_27) (g535)), Or.inr (le_trans (hv _ _ sub_18_27) (g535))⟩
theorem cl455 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc2_1 v) (h1 : ¬acc9_2 v) (h2 : ¬acc11_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0b with g538 | g538
  · rcases le_or_gt (v s72) (v s36) with g539 | g539
    · rcases h0a with g540 | g540 | g540
      · exact h1 ⟨Or.inl (g539), Or.inl (le_trans (hv _ _ sub_144_146) (g540))⟩
      · exact h1 ⟨Or.inl (g539), Or.inl (le_trans (hv _ _ sub_144_145) (g540))⟩
      · exact h1 ⟨Or.inl (g539), Or.inr (le_trans (hv _ _ sub_18_19) (g540))⟩
    · rcases h0a with g541 | g541 | g541
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g539) (hv _ _ sub_72_73))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_128_146) (g541)) (g539)) (hv _ _ sub_72_73)))⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g539) (hv _ _ sub_72_73))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_128_145) (g541)) (g539)) (hv _ _ sub_72_73)))⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g539) (hv _ _ sub_72_73))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_16_19) (g541)) (g539)) (hv _ _ sub_72_73)))⟩
  · rcases le_or_gt (v s72) (v s36) with g542 | g542
    · rcases h0a with g543 | g543 | g543
      · exact h1 ⟨Or.inl (g542), Or.inl (le_trans (hv _ _ sub_144_146) (g543))⟩
      · exact h1 ⟨Or.inl (g542), Or.inl (le_trans (hv _ _ sub_144_145) (g543))⟩
      · exact h1 ⟨Or.inl (g542), Or.inr (le_trans (hv _ _ sub_18_19) (g543))⟩
    · rcases h0a with g544 | g544 | g544
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g542) (hv _ _ sub_72_73))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_128_146) (g544)) (g542)) (hv _ _ sub_72_73)))⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g542) (hv _ _ sub_72_73))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_128_145) (g544)) (g542)) (hv _ _ sub_72_73)))⟩
      · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g542) (hv _ _ sub_72_73))), Or.inr (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_16_19) (g544)) (g542)) (hv _ _ sub_72_73)))⟩
theorem cl456 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc6_2 v) (h1 : ¬acc5_1 v) (h2 : ¬acc7_0 v) : False := by
  rcases le_or_gt (v s78) (v s144) with g545 | g545
  · exact h1 ⟨Or.inl (g545), hv _ _ sub_0_144⟩
  · rcases le_or_gt (v s77) (v s144) with g546 | g546
    · exact h1 ⟨Or.inr (Or.inl (g546)), hv _ _ sub_0_144⟩
    · rcases le_or_gt (v s75) (v s144) with g547 | g547
      · exact h1 ⟨Or.inr (Or.inr (Or.inl (g547))), hv _ _ sub_0_144⟩
      · rcases le_or_gt (v s32) (v s75) with g548 | g548
        · exact h2 ⟨Or.inl (g548), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_128_144) (g547)))⟩
        · exact h0 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_73_75) (g548))), Or.inl (le_of_lt (lt_trans (g547) (g548)))⟩
theorem cl457 (v : Finset (Fin 8) → α) (_hv : IsMonotoneVal v) (h0 : ¬acc3_2 v) (h1 : ¬acc7_0 v) (h2 : ¬acc5_2 v) : False := by
  rcases le_or_gt (v s90) (v s128) with g549 | g549
  · rcases le_or_gt (v s32) (v s128) with g550 | g550
    · exact h0 ⟨Or.inl (g549), Or.inl (g550)⟩
    · rcases le_or_gt (v s32) (v s75) with g551 | g551
      · exact h1 ⟨Or.inl (g551), Or.inl (le_of_lt (lt_of_lt_of_le (g550) (g551)))⟩
      · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (g551)))), Or.inl (le_of_lt (g550))⟩
  · rcases le_or_gt (v s89) (v s128) with g552 | g552
    · rcases le_or_gt (v s32) (v s128) with g553 | g553
      · exact h0 ⟨Or.inr (Or.inl (g552)), Or.inl (g553)⟩
      · rcases le_or_gt (v s32) (v s75) with g554 | g554
        · exact h1 ⟨Or.inl (g554), Or.inl (le_of_lt (lt_of_lt_of_le (g553) (g554)))⟩
        · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (g554)))), Or.inl (le_of_lt (g553))⟩
    · rcases le_or_gt (v s75) (v s128) with g555 | g555
      · rcases le_or_gt (v s32) (v s128) with g556 | g556
        · exact h0 ⟨Or.inr (Or.inr (Or.inl (g555))), Or.inl (g556)⟩
        · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (g555) (g556))))), Or.inl (le_of_lt (g556))⟩
      · rcases le_or_gt (v s32) (v s75) with g557 | g557
        · exact h1 ⟨Or.inl (g557), Or.inl (le_of_lt (g555))⟩
        · exact h2 ⟨Or.inr (Or.inr (Or.inl (le_of_lt (g557)))), Or.inl (le_of_lt (lt_trans (g555) (g557)))⟩
theorem cl459 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_1 v) (h1 : ¬acc11_2 v) (h2 : ¬acc11_1 v) : False := by
  rcases le_or_gt (v s38) (v s72) with g558 | g558
  · rcases le_or_gt (v s128) (v s72) with g559 | g559
    · exact h0 ⟨Or.inl (g558), Or.inl (g559)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g559) (hv _ _ sub_128_144))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_36_38) (g558)) (g559)) (hv _ _ sub_128_144)))⟩
  · rcases le_or_gt (v s128) (v s38) with g560 | g560
    · exact h2 ⟨Or.inl (le_of_lt (g558)), Or.inl (g560)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (g558) (g560)) (hv _ _ sub_128_144))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_36_38) (g560)) (hv _ _ sub_128_144)))⟩
theorem cl460 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_1 v) (h1 : ¬acc2_0 v) (h2 : ¬acc11_1 v) : False := by
  rcases le_or_gt (v s38) (v s72) with g561 | g561
  · rcases le_or_gt (v s128) (v s72) with g562 | g562
    · exact h0 ⟨Or.inl (g561), Or.inl (g562)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_32_38) (g561)) (g562)) (hv _ _ sub_128_147))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g562)) (hv _ _ sub_128_147)))⟩
  · rcases le_or_gt (v s128) (v s38) with g563 | g563
    · exact h2 ⟨Or.inl (le_of_lt (g561)), Or.inl (g563)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_38) (g563)) (hv _ _ sub_128_147))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (lt_of_le_of_lt (hv _ _ sub_64_72) (g561)) (g563)) (hv _ _ sub_128_147)))⟩
theorem cl461 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc4_2 v) (h1 : ¬acc3_1 v) (h2 : ¬acc7_0 v) : False := by
  rcases le_or_gt (v s90) (v s36) with g564 | g564
  · exact h1 ⟨Or.inl (g564), hv _ _ sub_0_36⟩
  · rcases le_or_gt (v s89) (v s36) with g565 | g565
    · exact h1 ⟨Or.inr (Or.inl (g565)), hv _ _ sub_0_36⟩
    · rcases le_or_gt (v s75) (v s36) with g566 | g566
      · exact h1 ⟨Or.inr (Or.inr (Or.inl (g566))), hv _ _ sub_0_36⟩
      · rcases le_or_gt (v s128) (v s75) with g567 | g567
        · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_32_36) (g566))), Or.inl (g567)⟩
        · exact h0 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_73_75) (g567))), Or.inl (le_of_lt (lt_trans (g566) (g567)))⟩
theorem cl462 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc2_1 v) (h1 : ¬acc11_0 v) (h2 : ¬acc6_1 v) : False := by
  rcases le_or_gt (v s128) (v s73) with g568 | g568
  · rcases le_or_gt (v s64) (v s36) with g569 | g569
    · rcases le_or_gt (v s146) (v s36) with g570 | g570
      · exact h0 ⟨Or.inl (g570), Or.inl (g569)⟩
      · rcases le_or_gt (v s36) (v s73) with g571 | g571
        · exact h1 ⟨Or.inl (g571), Or.inl (g568)⟩
        · exact h2 ⟨Or.inl (le_of_lt (lt_trans (g571) (g570))), hv _ _ sub_0_146⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g569) (hv _ _ sub_64_73))), Or.inl (g568)⟩
  · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g568) (hv _ _ sub_128_146))), hv _ _ sub_0_146⟩
theorem cl463 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc15_1 v) (h1 : ¬acc14_1 v) (h2 : ¬acc17_0 v) : False := by
  rcases le_or_gt (v s37) (v s146) with g572 | g572
  · exact h1 ⟨Or.inl (g572), hv _ _ sub_0_146⟩
  · rcases le_or_gt (v s37) (v s72) with g573 | g573
    · exact h0 ⟨Or.inr (Or.inl (g573)), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_146) (g572)) (g573)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_144_146) (g572))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g573)))⟩
theorem cl464 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc10_2 v) (h1 : ¬acc12_1 v) (h2 : ¬acc15_0 v) : False := by
  rcases le_or_gt (v s54) (v s72) with g574 | g574
  · exact h1 ⟨Or.inl (g574), hv _ _ sub_0_72⟩
  · rcases le_or_gt (v s53) (v s72) with g575 | g575
    · exact h1 ⟨Or.inr (Or.inl (g575)), hv _ _ sub_0_72⟩
    · rcases le_or_gt (v s39) (v s72) with g576 | g576
      · exact h1 ⟨Or.inr (Or.inr (Or.inl (g576))), hv _ _ sub_0_72⟩
      · rcases le_or_gt (v s128) (v s39) with g577 | g577
        · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g576))), Or.inl (g577)⟩
        · exact h0 ⟨Or.inl (le_of_lt (lt_trans (g576) (g577))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_38_39) (g577)))⟩
theorem cl465 (v : Finset (Fin 8) → α) (_hv : IsMonotoneVal v) (h0 : ¬acc10_2 v) (h1 : ¬acc11_1 v) (h2 : ¬acc15_1 v) : False := by
  rcases le_or_gt (v s72) (v s128) with g578 | g578
  · rcases le_or_gt (v s38) (v s128) with g579 | g579
    · exact h0 ⟨Or.inl (g578), Or.inl (g579)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (g578) (g579))), Or.inl (le_of_lt (g579))⟩
  · rcases le_or_gt (v s72) (v s38) with g580 | g580
    · exact h1 ⟨Or.inl (g580), Or.inl (le_of_lt (lt_of_lt_of_le (g578) (g580)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g580)), Or.inl (le_of_lt (g578))⟩
theorem cl466 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc7_2 v) (h1 : ¬acc9_2 v) (h2 : ¬acc11_0 v) : False := by
  rcases le_or_gt (v s74) (v s144) with g581 | g581
  · rcases le_or_gt (v s32) (v s144) with g582 | g582
    · exact h0 ⟨Or.inl (g581), Or.inl (g582)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_72_74) (g581)) (g582)) (hv _ _ sub_32_36))), Or.inl (le_of_lt (lt_of_lt_of_le (g582) (hv _ _ sub_32_36)))⟩
  · rcases le_or_gt (v s73) (v s144) with g583 | g583
    · rcases le_or_gt (v s32) (v s144) with g584 | g584
      · exact h0 ⟨Or.inr (Or.inl (g583)), Or.inl (g584)⟩
      · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_72_73) (g583)) (g584)) (hv _ _ sub_32_36))), Or.inl (le_of_lt (lt_of_lt_of_le (g584) (hv _ _ sub_32_36)))⟩
    · rcases le_or_gt (v s36) (v s73) with g585 | g585
      · exact h2 ⟨Or.inl (g585), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_128_144) (g583)))⟩
      · exact h1 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_72_73) (g585))), Or.inl (le_of_lt (lt_trans (g583) (g585)))⟩
theorem cl467 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : acc10_0 v) (h1 : ¬acc4_2 v) (h2 : ¬acc11_0 v) : False := by
  obtain ⟨h0a, h0b⟩ := h0
  rcases h0a with g586 | g586
  · rcases le_or_gt (v s73) (v s128) with g587 | g587
    · exact h1 ⟨Or.inl (g587), Or.inl (le_trans (le_trans (hv _ _ sub_36_38) (g586)) (g587))⟩
    · exact h2 ⟨Or.inl (le_trans (hv _ _ sub_36_38) (g586)), Or.inl (le_of_lt (g587))⟩
  · exact h2 ⟨Or.inr (le_trans (hv _ _ sub_6_22) (g586)), Or.inr (le_trans (hv _ _ sub_16_22) (g586))⟩
theorem cl468 (v : Finset (Fin 8) → α) (_hv : IsMonotoneVal v) (h0 : ¬acc4_2 v) (h1 : ¬acc7_1 v) (h2 : ¬acc11_0 v) : False := by
  rcases le_or_gt (v s73) (v s128) with g588 | g588
  · rcases le_or_gt (v s36) (v s128) with g589 | g589
    · exact h0 ⟨Or.inl (g588), Or.inl (g589)⟩
    · exact h1 ⟨Or.inr (Or.inl (le_of_lt (lt_of_le_of_lt (g588) (g589)))), Or.inl (le_of_lt (g589))⟩
  · rcases le_or_gt (v s73) (v s36) with g590 | g590
    · exact h1 ⟨Or.inr (Or.inl (g590)), Or.inl (le_of_lt (lt_of_lt_of_le (g588) (g590)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g590)), Or.inl (le_of_lt (g588))⟩
theorem cl470 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc0_1 v) (h1 : ¬acc16_2 v) (h2 : ¬acc2_0 v) : False := by
  rcases le_or_gt (v s154) (v s36) with g591 | g591
  · exact h0 ⟨Or.inl (g591), hv _ _ sub_0_36⟩
  · rcases le_or_gt (v s153) (v s36) with g592 | g592
    · exact h0 ⟨Or.inr (Or.inl (g592)), hv _ _ sub_0_36⟩
    · rcases le_or_gt (v s147) (v s36) with g593 | g593
      · exact h0 ⟨Or.inr (Or.inr (Or.inl (g593))), hv _ _ sub_0_36⟩
      · rcases le_or_gt (v s64) (v s147) with g594 | g594
        · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_32_36) (g593))), Or.inl (g594)⟩
        · exact h1 ⟨Or.inl (le_of_lt (lt_trans (g593) (g594))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_146_147) (g594)))⟩
theorem cl471 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc17_2 v) (h1 : ¬acc11_1 v) (h2 : ¬acc9_1 v) : False := by
  rcases le_or_gt (v s36) (v s72) with g595 | g595
  · rcases le_or_gt (v s144) (v s72) with g596 | g596
    · exact h0 ⟨Or.inl (g595), Or.inl (g596)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g596) (hv _ _ sub_144_146))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_32_36) (g595)) (g596)) (hv _ _ sub_144_146)))⟩
  · rcases le_or_gt (v s128) (v s38) with g597 | g597
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g595) (hv _ _ sub_36_38))), Or.inl (g597)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (g595) (hv _ _ sub_36_38)) (g597)) (hv _ _ sub_128_146))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_32_38) (g597)) (hv _ _ sub_128_146)))⟩
theorem cl472 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc17_2 v) (h1 : ¬acc11_1 v) (h2 : ¬acc15_2 v) : False := by
  rcases le_or_gt (v s36) (v s72) with g598 | g598
  · rcases le_or_gt (v s144) (v s72) with g599 | g599
    · exact h0 ⟨Or.inl (g598), Or.inl (g599)⟩
    · rcases le_or_gt (v s38) (v s144) with g600 | g600
      · exact h2 ⟨Or.inl (g600), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g599)))⟩
      · exact h1 ⟨Or.inl (le_of_lt (lt_trans (g599) (g600))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_128_144) (g600)))⟩
  · rcases le_or_gt (v s128) (v s38) with g601 | g601
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g598) (hv _ _ sub_36_38))), Or.inl (g601)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g601) (hv _ _ sub_128_144))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g598)) (hv _ _ sub_36_38)) (g601)) (hv _ _ sub_128_144)))⟩
theorem cl473 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc1_2 v) (h1 : ¬acc2_0 v) (h2 : ¬acc2_2 v) : False := by
  rcases le_or_gt (v s150) (v s32) with g602 | g602
  · rcases le_or_gt (v s64) (v s32) with g603 | g603
    · exact h0 ⟨Or.inl (g602), Or.inl (g603)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_146_150) (g602)) (g603)) (hv _ _ sub_64_72))), Or.inl (le_of_lt (lt_of_lt_of_le (g603) (hv _ _ sub_64_72)))⟩
  · rcases le_or_gt (v s149) (v s32) with g604 | g604
    · rcases le_or_gt (v s64) (v s32) with g605 | g605
      · exact h0 ⟨Or.inr (Or.inl (g604)), Or.inl (g605)⟩
      · exact h2 ⟨Or.inr (Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_145_149) (g604)) (g605)) (hv _ _ sub_64_72)))), Or.inl (le_of_lt (lt_of_lt_of_le (g605) (hv _ _ sub_64_72)))⟩
    · rcases le_or_gt (v s147) (v s32) with g606 | g606
      · rcases le_or_gt (v s64) (v s32) with g607 | g607
        · exact h0 ⟨Or.inr (Or.inr (Or.inl (g606))), Or.inl (g607)⟩
        · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_146_147) (g606)) (g607)) (hv _ _ sub_64_72))), Or.inl (le_of_lt (lt_of_lt_of_le (g607) (hv _ _ sub_64_72)))⟩
      · rcases le_or_gt (v s64) (v s147) with g608 | g608
        · exact h1 ⟨Or.inl (le_of_lt (g606)), Or.inl (g608)⟩
        · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_146_147) (g608)) (hv _ _ sub_64_72))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (g606) (g608)) (hv _ _ sub_64_72)))⟩
theorem cl474 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc8_2 v) (h1 : ¬acc2_0 v) (h2 : ¬acc2_2 v) : False := by
  rcases le_or_gt (v s72) (v s32) with g609 | g609
  · rcases le_or_gt (v s146) (v s32) with g610 | g610
    · exact h0 ⟨Or.inl (g609), Or.inl (g610)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g610) (hv _ _ sub_146_147))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_64_72) (g609)) (g610)) (hv _ _ sub_146_147)))⟩
  · rcases le_or_gt (v s146) (v s72) with g611 | g611
    · exact h2 ⟨Or.inl (g611), Or.inl (le_of_lt (g609))⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (lt_trans (g609) (g611)) (hv _ _ sub_146_147))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_64_72) (g611)) (hv _ _ sub_146_147)))⟩
theorem cl475 (v : Finset (Fin 8) → α) (_hv : IsMonotoneVal v) (h0 : ¬acc8_2 v) (h1 : ¬acc2_2 v) (h2 : ¬acc9_1 v) : False := by
  rcases le_or_gt (v s72) (v s32) with g612 | g612
  · rcases le_or_gt (v s146) (v s32) with g613 | g613
    · exact h0 ⟨Or.inl (g612), Or.inl (g613)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_le_of_lt (g612) (g613))), Or.inl (le_of_lt (g613))⟩
  · rcases le_or_gt (v s146) (v s72) with g614 | g614
    · exact h1 ⟨Or.inl (g614), Or.inl (le_of_lt (g612))⟩
    · exact h2 ⟨Or.inl (le_of_lt (g614)), Or.inl (le_of_lt (lt_trans (g612) (g614)))⟩
theorem cl477 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc11_2 v) (h1 : ¬acc15_1 v) (h2 : ¬acc17_0 v) : False := by
  rcases le_or_gt (v s72) (v s144) with g615 | g615
  · rcases le_or_gt (v s36) (v s144) with g616 | g616
    · exact h0 ⟨Or.inl (g615), Or.inl (g616)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g616) (hv _ _ sub_36_37))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_64_72) (g615)) (g616)) (hv _ _ sub_36_37)))⟩
  · rcases le_or_gt (v s37) (v s72) with g617 | g617
    · exact h1 ⟨Or.inr (Or.inl (g617)), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_128_144) (g615)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_trans (g615) (g617))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g617)))⟩
theorem cl478 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_1 v) (h1 : ¬acc11_0 v) (h2 : ¬acc2_1 v) : False := by
  rcases le_or_gt (v s72) (v s146) with g618 | g618
  · rcases le_or_gt (v s32) (v s146) with g619 | g619
    · exact h0 ⟨Or.inl (g618), Or.inl (g619)⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g619) (hv _ _ sub_32_36))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_64_72) (g618)) (g619)) (hv _ _ sub_32_36)))⟩
  · rcases le_or_gt (v s36) (v s73) with g620 | g620
    · exact h1 ⟨Or.inl (g620), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (hv _ _ sub_128_146) (g618)) (hv _ _ sub_72_73)))⟩
    · exact h2 ⟨Or.inl (le_of_lt (lt_trans (lt_of_lt_of_le (g618) (hv _ _ sub_72_73)) (g620))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_73) (g620)))⟩
theorem cl479 (v : Finset (Fin 8) → α) (hv : IsMonotoneVal v) (h0 : ¬acc9_1 v) (h1 : ¬acc2_1 v) (h2 : ¬acc17_2 v) : False := by
  rcases le_or_gt (v s72) (v s146) with g621 | g621
  · rcases le_or_gt (v s32) (v s146) with g622 | g622
    · exact h0 ⟨Or.inl (g621), Or.inl (g622)⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_of_lt_of_le (g622) (hv _ _ sub_32_36))), Or.inl (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_trans (hv _ _ sub_64_72) (g621)) (g622)) (hv _ _ sub_32_36)))⟩
  · rcases le_or_gt (v s36) (v s72) with g623 | g623
    · exact h2 ⟨Or.inl (g623), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_144_146) (g621)))⟩
    · exact h1 ⟨Or.inl (le_of_lt (lt_trans (g621) (g623))), Or.inl (le_of_lt (lt_of_le_of_lt (hv _ _ sub_64_72) (g623)))⟩

end Acc

/-! ### Allocations in which every agent accepts its block -/


theorem succ0_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc0_0 (v 0)) (h1 : acc0_1 (v 1))
    (h2 : acc0_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P0 alloc0 out0 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP0_0 _ h0, accP0_1 _ h1, accP0_2 _ h2])⟩

theorem succ0_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc0_0 (v 0)) (h1 : acc0_2 (v 1))
    (h2 : acc0_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P0 alloc0 out0 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP0_0 _ h0, accP0_2 _ h1, accP0_1 _ h2])⟩

theorem succ0_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc0_1 (v 0)) (h1 : acc0_0 (v 1))
    (h2 : acc0_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P0 alloc0 out0 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP0_1 _ h0, accP0_0 _ h1, accP0_2 _ h2])⟩

theorem succ0_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc0_1 (v 0)) (h1 : acc0_2 (v 1))
    (h2 : acc0_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P0 alloc0 out0 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP0_1 _ h0, accP0_2 _ h1, accP0_0 _ h2])⟩

theorem succ0_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc0_2 (v 0)) (h1 : acc0_0 (v 1))
    (h2 : acc0_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P0 alloc0 out0 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP0_2 _ h0, accP0_0 _ h1, accP0_1 _ h2])⟩

theorem succ0_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc0_2 (v 0)) (h1 : acc0_1 (v 1))
    (h2 : acc0_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P0 alloc0 out0 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP0_2 _ h0, accP0_1 _ h1, accP0_0 _ h2])⟩

theorem succ1_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc1_0 (v 0)) (h1 : acc1_1 (v 1))
    (h2 : acc1_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P1 alloc1 out1 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP1_0 _ h0, accP1_1 _ h1, accP1_2 _ h2])⟩

theorem succ1_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc1_0 (v 0)) (h1 : acc1_2 (v 1))
    (h2 : acc1_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P1 alloc1 out1 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP1_0 _ h0, accP1_2 _ h1, accP1_1 _ h2])⟩

theorem succ1_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc1_1 (v 0)) (h1 : acc1_0 (v 1))
    (h2 : acc1_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P1 alloc1 out1 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP1_1 _ h0, accP1_0 _ h1, accP1_2 _ h2])⟩

theorem succ1_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc1_1 (v 0)) (h1 : acc1_2 (v 1))
    (h2 : acc1_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P1 alloc1 out1 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP1_1 _ h0, accP1_2 _ h1, accP1_0 _ h2])⟩

theorem succ1_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc1_2 (v 0)) (h1 : acc1_0 (v 1))
    (h2 : acc1_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P1 alloc1 out1 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP1_2 _ h0, accP1_0 _ h1, accP1_1 _ h2])⟩

theorem succ1_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc1_2 (v 0)) (h1 : acc1_1 (v 1))
    (h2 : acc1_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P1 alloc1 out1 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP1_2 _ h0, accP1_1 _ h1, accP1_0 _ h2])⟩

theorem succ2_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc2_0 (v 0)) (h1 : acc2_1 (v 1))
    (h2 : acc2_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P2 alloc2 out2 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP2_0 _ h0, accP2_1 _ h1, accP2_2 _ h2])⟩

theorem succ2_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc2_0 (v 0)) (h1 : acc2_2 (v 1))
    (h2 : acc2_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P2 alloc2 out2 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP2_0 _ h0, accP2_2 _ h1, accP2_1 _ h2])⟩

theorem succ2_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc2_1 (v 0)) (h1 : acc2_0 (v 1))
    (h2 : acc2_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P2 alloc2 out2 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP2_1 _ h0, accP2_0 _ h1, accP2_2 _ h2])⟩

theorem succ2_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc2_1 (v 0)) (h1 : acc2_2 (v 1))
    (h2 : acc2_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P2 alloc2 out2 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP2_1 _ h0, accP2_2 _ h1, accP2_0 _ h2])⟩

theorem succ2_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc2_2 (v 0)) (h1 : acc2_0 (v 1))
    (h2 : acc2_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P2 alloc2 out2 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP2_2 _ h0, accP2_0 _ h1, accP2_1 _ h2])⟩

theorem succ2_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc2_2 (v 0)) (h1 : acc2_1 (v 1))
    (h2 : acc2_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P2 alloc2 out2 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP2_2 _ h0, accP2_1 _ h1, accP2_0 _ h2])⟩

theorem succ3_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc3_0 (v 0)) (h1 : acc3_1 (v 1))
    (h2 : acc3_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P3 alloc3 out3 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP3_0 _ h0, accP3_1 _ h1, accP3_2 _ h2])⟩

theorem succ3_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc3_0 (v 0)) (h1 : acc3_2 (v 1))
    (h2 : acc3_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P3 alloc3 out3 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP3_0 _ h0, accP3_2 _ h1, accP3_1 _ h2])⟩

theorem succ3_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc3_1 (v 0)) (h1 : acc3_0 (v 1))
    (h2 : acc3_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P3 alloc3 out3 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP3_1 _ h0, accP3_0 _ h1, accP3_2 _ h2])⟩

theorem succ3_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc3_1 (v 0)) (h1 : acc3_2 (v 1))
    (h2 : acc3_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P3 alloc3 out3 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP3_1 _ h0, accP3_2 _ h1, accP3_0 _ h2])⟩

theorem succ3_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc3_2 (v 0)) (h1 : acc3_0 (v 1))
    (h2 : acc3_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P3 alloc3 out3 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP3_2 _ h0, accP3_0 _ h1, accP3_1 _ h2])⟩

theorem succ3_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc3_2 (v 0)) (h1 : acc3_1 (v 1))
    (h2 : acc3_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P3 alloc3 out3 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP3_2 _ h0, accP3_1 _ h1, accP3_0 _ h2])⟩

theorem succ4_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc4_0 (v 0)) (h1 : acc4_1 (v 1))
    (h2 : acc4_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P4 alloc4 out4 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP4_0 _ h0, accP4_1 _ h1, accP4_2 _ h2])⟩

theorem succ4_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc4_0 (v 0)) (h1 : acc4_2 (v 1))
    (h2 : acc4_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P4 alloc4 out4 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP4_0 _ h0, accP4_2 _ h1, accP4_1 _ h2])⟩

theorem succ4_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc4_1 (v 0)) (h1 : acc4_0 (v 1))
    (h2 : acc4_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P4 alloc4 out4 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP4_1 _ h0, accP4_0 _ h1, accP4_2 _ h2])⟩

theorem succ4_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc4_1 (v 0)) (h1 : acc4_2 (v 1))
    (h2 : acc4_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P4 alloc4 out4 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP4_1 _ h0, accP4_2 _ h1, accP4_0 _ h2])⟩

theorem succ4_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc4_2 (v 0)) (h1 : acc4_0 (v 1))
    (h2 : acc4_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P4 alloc4 out4 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP4_2 _ h0, accP4_0 _ h1, accP4_1 _ h2])⟩

theorem succ4_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc4_2 (v 0)) (h1 : acc4_1 (v 1))
    (h2 : acc4_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P4 alloc4 out4 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP4_2 _ h0, accP4_1 _ h1, accP4_0 _ h2])⟩

theorem succ5_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc5_0 (v 0)) (h1 : acc5_1 (v 1))
    (h2 : acc5_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P5 alloc5 out5 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP5_0 _ h0, accP5_1 _ h1, accP5_2 _ h2])⟩

theorem succ5_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc5_0 (v 0)) (h1 : acc5_2 (v 1))
    (h2 : acc5_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P5 alloc5 out5 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP5_0 _ h0, accP5_2 _ h1, accP5_1 _ h2])⟩

theorem succ5_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc5_1 (v 0)) (h1 : acc5_0 (v 1))
    (h2 : acc5_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P5 alloc5 out5 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP5_1 _ h0, accP5_0 _ h1, accP5_2 _ h2])⟩

theorem succ5_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc5_1 (v 0)) (h1 : acc5_2 (v 1))
    (h2 : acc5_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P5 alloc5 out5 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP5_1 _ h0, accP5_2 _ h1, accP5_0 _ h2])⟩

theorem succ5_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc5_2 (v 0)) (h1 : acc5_0 (v 1))
    (h2 : acc5_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P5 alloc5 out5 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP5_2 _ h0, accP5_0 _ h1, accP5_1 _ h2])⟩

theorem succ5_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc5_2 (v 0)) (h1 : acc5_1 (v 1))
    (h2 : acc5_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P5 alloc5 out5 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP5_2 _ h0, accP5_1 _ h1, accP5_0 _ h2])⟩

theorem succ6_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc6_0 (v 0)) (h1 : acc6_1 (v 1))
    (h2 : acc6_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P6 alloc6 out6 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP6_0 _ h0, accP6_1 _ h1, accP6_2 _ h2])⟩

theorem succ6_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc6_0 (v 0)) (h1 : acc6_2 (v 1))
    (h2 : acc6_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P6 alloc6 out6 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP6_0 _ h0, accP6_2 _ h1, accP6_1 _ h2])⟩

theorem succ6_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc6_1 (v 0)) (h1 : acc6_0 (v 1))
    (h2 : acc6_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P6 alloc6 out6 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP6_1 _ h0, accP6_0 _ h1, accP6_2 _ h2])⟩

theorem succ6_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc6_1 (v 0)) (h1 : acc6_2 (v 1))
    (h2 : acc6_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P6 alloc6 out6 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP6_1 _ h0, accP6_2 _ h1, accP6_0 _ h2])⟩

theorem succ6_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc6_2 (v 0)) (h1 : acc6_0 (v 1))
    (h2 : acc6_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P6 alloc6 out6 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP6_2 _ h0, accP6_0 _ h1, accP6_1 _ h2])⟩

theorem succ6_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc6_2 (v 0)) (h1 : acc6_1 (v 1))
    (h2 : acc6_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P6 alloc6 out6 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP6_2 _ h0, accP6_1 _ h1, accP6_0 _ h2])⟩

theorem succ7_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc7_0 (v 0)) (h1 : acc7_1 (v 1))
    (h2 : acc7_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P7 alloc7 out7 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP7_0 _ h0, accP7_1 _ h1, accP7_2 _ h2])⟩

theorem succ7_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc7_0 (v 0)) (h1 : acc7_2 (v 1))
    (h2 : acc7_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P7 alloc7 out7 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP7_0 _ h0, accP7_2 _ h1, accP7_1 _ h2])⟩

theorem succ7_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc7_1 (v 0)) (h1 : acc7_0 (v 1))
    (h2 : acc7_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P7 alloc7 out7 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP7_1 _ h0, accP7_0 _ h1, accP7_2 _ h2])⟩

theorem succ7_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc7_1 (v 0)) (h1 : acc7_2 (v 1))
    (h2 : acc7_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P7 alloc7 out7 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP7_1 _ h0, accP7_2 _ h1, accP7_0 _ h2])⟩

theorem succ7_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc7_2 (v 0)) (h1 : acc7_0 (v 1))
    (h2 : acc7_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P7 alloc7 out7 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP7_2 _ h0, accP7_0 _ h1, accP7_1 _ h2])⟩

theorem succ7_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc7_2 (v 0)) (h1 : acc7_1 (v 1))
    (h2 : acc7_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P7 alloc7 out7 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP7_2 _ h0, accP7_1 _ h1, accP7_0 _ h2])⟩

theorem succ8_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc8_0 (v 0)) (h1 : acc8_1 (v 1))
    (h2 : acc8_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P8 alloc8 out8 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP8_0 _ h0, accP8_1 _ h1, accP8_2 _ h2])⟩

theorem succ8_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc8_0 (v 0)) (h1 : acc8_2 (v 1))
    (h2 : acc8_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P8 alloc8 out8 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP8_0 _ h0, accP8_2 _ h1, accP8_1 _ h2])⟩

theorem succ8_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc8_1 (v 0)) (h1 : acc8_0 (v 1))
    (h2 : acc8_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P8 alloc8 out8 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP8_1 _ h0, accP8_0 _ h1, accP8_2 _ h2])⟩

theorem succ8_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc8_1 (v 0)) (h1 : acc8_2 (v 1))
    (h2 : acc8_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P8 alloc8 out8 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP8_1 _ h0, accP8_2 _ h1, accP8_0 _ h2])⟩

theorem succ8_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc8_2 (v 0)) (h1 : acc8_0 (v 1))
    (h2 : acc8_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P8 alloc8 out8 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP8_2 _ h0, accP8_0 _ h1, accP8_1 _ h2])⟩

theorem succ8_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc8_2 (v 0)) (h1 : acc8_1 (v 1))
    (h2 : acc8_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P8 alloc8 out8 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP8_2 _ h0, accP8_1 _ h1, accP8_0 _ h2])⟩

theorem succ9_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc9_0 (v 0)) (h1 : acc9_1 (v 1))
    (h2 : acc9_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P9 alloc9 out9 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP9_0 _ h0, accP9_1 _ h1, accP9_2 _ h2])⟩

theorem succ9_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc9_0 (v 0)) (h1 : acc9_2 (v 1))
    (h2 : acc9_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P9 alloc9 out9 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP9_0 _ h0, accP9_2 _ h1, accP9_1 _ h2])⟩

theorem succ9_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc9_1 (v 0)) (h1 : acc9_0 (v 1))
    (h2 : acc9_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P9 alloc9 out9 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP9_1 _ h0, accP9_0 _ h1, accP9_2 _ h2])⟩

theorem succ9_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc9_1 (v 0)) (h1 : acc9_2 (v 1))
    (h2 : acc9_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P9 alloc9 out9 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP9_1 _ h0, accP9_2 _ h1, accP9_0 _ h2])⟩

theorem succ9_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc9_2 (v 0)) (h1 : acc9_0 (v 1))
    (h2 : acc9_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P9 alloc9 out9 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP9_2 _ h0, accP9_0 _ h1, accP9_1 _ h2])⟩

theorem succ9_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc9_2 (v 0)) (h1 : acc9_1 (v 1))
    (h2 : acc9_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P9 alloc9 out9 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP9_2 _ h0, accP9_1 _ h1, accP9_0 _ h2])⟩

theorem succ10_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc10_0 (v 0)) (h1 : acc10_1 (v 1))
    (h2 : acc10_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P10 alloc10 out10 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP10_0 _ h0, accP10_1 _ h1, accP10_2 _ h2])⟩

theorem succ10_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc10_0 (v 0)) (h1 : acc10_2 (v 1))
    (h2 : acc10_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P10 alloc10 out10 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP10_0 _ h0, accP10_2 _ h1, accP10_1 _ h2])⟩

theorem succ10_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc10_1 (v 0)) (h1 : acc10_0 (v 1))
    (h2 : acc10_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P10 alloc10 out10 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP10_1 _ h0, accP10_0 _ h1, accP10_2 _ h2])⟩

theorem succ10_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc10_1 (v 0)) (h1 : acc10_2 (v 1))
    (h2 : acc10_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P10 alloc10 out10 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP10_1 _ h0, accP10_2 _ h1, accP10_0 _ h2])⟩

theorem succ10_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc10_2 (v 0)) (h1 : acc10_0 (v 1))
    (h2 : acc10_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P10 alloc10 out10 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP10_2 _ h0, accP10_0 _ h1, accP10_1 _ h2])⟩

theorem succ10_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc10_2 (v 0)) (h1 : acc10_1 (v 1))
    (h2 : acc10_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P10 alloc10 out10 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP10_2 _ h0, accP10_1 _ h1, accP10_0 _ h2])⟩

theorem succ11_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc11_0 (v 0)) (h1 : acc11_1 (v 1))
    (h2 : acc11_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P11 alloc11 out11 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP11_0 _ h0, accP11_1 _ h1, accP11_2 _ h2])⟩

theorem succ11_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc11_0 (v 0)) (h1 : acc11_2 (v 1))
    (h2 : acc11_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P11 alloc11 out11 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP11_0 _ h0, accP11_2 _ h1, accP11_1 _ h2])⟩

theorem succ11_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc11_1 (v 0)) (h1 : acc11_0 (v 1))
    (h2 : acc11_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P11 alloc11 out11 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP11_1 _ h0, accP11_0 _ h1, accP11_2 _ h2])⟩

theorem succ11_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc11_1 (v 0)) (h1 : acc11_2 (v 1))
    (h2 : acc11_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P11 alloc11 out11 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP11_1 _ h0, accP11_2 _ h1, accP11_0 _ h2])⟩

theorem succ11_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc11_2 (v 0)) (h1 : acc11_0 (v 1))
    (h2 : acc11_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P11 alloc11 out11 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP11_2 _ h0, accP11_0 _ h1, accP11_1 _ h2])⟩

theorem succ11_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc11_2 (v 0)) (h1 : acc11_1 (v 1))
    (h2 : acc11_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P11 alloc11 out11 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP11_2 _ h0, accP11_1 _ h1, accP11_0 _ h2])⟩

theorem succ12_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc12_0 (v 0)) (h1 : acc12_1 (v 1))
    (h2 : acc12_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P12 alloc12 out12 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP12_0 _ h0, accP12_1 _ h1, accP12_2 _ h2])⟩

theorem succ12_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc12_0 (v 0)) (h1 : acc12_2 (v 1))
    (h2 : acc12_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P12 alloc12 out12 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP12_0 _ h0, accP12_2 _ h1, accP12_1 _ h2])⟩

theorem succ12_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc12_1 (v 0)) (h1 : acc12_0 (v 1))
    (h2 : acc12_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P12 alloc12 out12 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP12_1 _ h0, accP12_0 _ h1, accP12_2 _ h2])⟩

theorem succ12_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc12_1 (v 0)) (h1 : acc12_2 (v 1))
    (h2 : acc12_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P12 alloc12 out12 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP12_1 _ h0, accP12_2 _ h1, accP12_0 _ h2])⟩

theorem succ12_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc12_2 (v 0)) (h1 : acc12_0 (v 1))
    (h2 : acc12_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P12 alloc12 out12 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP12_2 _ h0, accP12_0 _ h1, accP12_1 _ h2])⟩

theorem succ12_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc12_2 (v 0)) (h1 : acc12_1 (v 1))
    (h2 : acc12_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P12 alloc12 out12 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP12_2 _ h0, accP12_1 _ h1, accP12_0 _ h2])⟩

theorem succ13_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc13_0 (v 0)) (h1 : acc13_1 (v 1))
    (h2 : acc13_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P13 alloc13 out13 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP13_0 _ h0, accP13_1 _ h1, accP13_2 _ h2])⟩

theorem succ13_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc13_0 (v 0)) (h1 : acc13_2 (v 1))
    (h2 : acc13_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P13 alloc13 out13 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP13_0 _ h0, accP13_2 _ h1, accP13_1 _ h2])⟩

theorem succ13_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc13_1 (v 0)) (h1 : acc13_0 (v 1))
    (h2 : acc13_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P13 alloc13 out13 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP13_1 _ h0, accP13_0 _ h1, accP13_2 _ h2])⟩

theorem succ13_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc13_1 (v 0)) (h1 : acc13_2 (v 1))
    (h2 : acc13_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P13 alloc13 out13 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP13_1 _ h0, accP13_2 _ h1, accP13_0 _ h2])⟩

theorem succ13_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc13_2 (v 0)) (h1 : acc13_0 (v 1))
    (h2 : acc13_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P13 alloc13 out13 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP13_2 _ h0, accP13_0 _ h1, accP13_1 _ h2])⟩

theorem succ13_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc13_2 (v 0)) (h1 : acc13_1 (v 1))
    (h2 : acc13_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P13 alloc13 out13 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP13_2 _ h0, accP13_1 _ h1, accP13_0 _ h2])⟩

theorem succ14_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc14_0 (v 0)) (h1 : acc14_1 (v 1))
    (h2 : acc14_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P14 alloc14 out14 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP14_0 _ h0, accP14_1 _ h1, accP14_2 _ h2])⟩

theorem succ14_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc14_0 (v 0)) (h1 : acc14_2 (v 1))
    (h2 : acc14_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P14 alloc14 out14 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP14_0 _ h0, accP14_2 _ h1, accP14_1 _ h2])⟩

theorem succ14_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc14_1 (v 0)) (h1 : acc14_0 (v 1))
    (h2 : acc14_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P14 alloc14 out14 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP14_1 _ h0, accP14_0 _ h1, accP14_2 _ h2])⟩

theorem succ14_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc14_1 (v 0)) (h1 : acc14_2 (v 1))
    (h2 : acc14_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P14 alloc14 out14 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP14_1 _ h0, accP14_2 _ h1, accP14_0 _ h2])⟩

theorem succ14_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc14_2 (v 0)) (h1 : acc14_0 (v 1))
    (h2 : acc14_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P14 alloc14 out14 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP14_2 _ h0, accP14_0 _ h1, accP14_1 _ h2])⟩

theorem succ14_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc14_2 (v 0)) (h1 : acc14_1 (v 1))
    (h2 : acc14_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P14 alloc14 out14 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP14_2 _ h0, accP14_1 _ h1, accP14_0 _ h2])⟩

theorem succ15_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc15_0 (v 0)) (h1 : acc15_1 (v 1))
    (h2 : acc15_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P15 alloc15 out15 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP15_0 _ h0, accP15_1 _ h1, accP15_2 _ h2])⟩

theorem succ15_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc15_0 (v 0)) (h1 : acc15_2 (v 1))
    (h2 : acc15_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P15 alloc15 out15 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP15_0 _ h0, accP15_2 _ h1, accP15_1 _ h2])⟩

theorem succ15_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc15_1 (v 0)) (h1 : acc15_0 (v 1))
    (h2 : acc15_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P15 alloc15 out15 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP15_1 _ h0, accP15_0 _ h1, accP15_2 _ h2])⟩

theorem succ15_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc15_1 (v 0)) (h1 : acc15_2 (v 1))
    (h2 : acc15_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P15 alloc15 out15 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP15_1 _ h0, accP15_2 _ h1, accP15_0 _ h2])⟩

theorem succ15_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc15_2 (v 0)) (h1 : acc15_0 (v 1))
    (h2 : acc15_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P15 alloc15 out15 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP15_2 _ h0, accP15_0 _ h1, accP15_1 _ h2])⟩

theorem succ15_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc15_2 (v 0)) (h1 : acc15_1 (v 1))
    (h2 : acc15_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P15 alloc15 out15 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP15_2 _ h0, accP15_1 _ h1, accP15_0 _ h2])⟩

theorem succ16_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc16_0 (v 0)) (h1 : acc16_1 (v 1))
    (h2 : acc16_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P16 alloc16 out16 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP16_0 _ h0, accP16_1 _ h1, accP16_2 _ h2])⟩

theorem succ16_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc16_0 (v 0)) (h1 : acc16_2 (v 1))
    (h2 : acc16_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P16 alloc16 out16 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP16_0 _ h0, accP16_2 _ h1, accP16_1 _ h2])⟩

theorem succ16_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc16_1 (v 0)) (h1 : acc16_0 (v 1))
    (h2 : acc16_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P16 alloc16 out16 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP16_1 _ h0, accP16_0 _ h1, accP16_2 _ h2])⟩

theorem succ16_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc16_1 (v 0)) (h1 : acc16_2 (v 1))
    (h2 : acc16_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P16 alloc16 out16 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP16_1 _ h0, accP16_2 _ h1, accP16_0 _ h2])⟩

theorem succ16_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc16_2 (v 0)) (h1 : acc16_0 (v 1))
    (h2 : acc16_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P16 alloc16 out16 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP16_2 _ h0, accP16_0 _ h1, accP16_1 _ h2])⟩

theorem succ16_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc16_2 (v 0)) (h1 : acc16_1 (v 1))
    (h2 : acc16_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P16 alloc16 out16 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP16_2 _ h0, accP16_1 _ h1, accP16_0 _ h2])⟩

theorem succ17_012 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc17_0 (v 0)) (h1 : acc17_1 (v 1))
    (h2 : acc17_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P17 alloc17 out17 ![0, 1, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP17_0 _ h0, accP17_1 _ h1, accP17_2 _ h2])⟩

theorem succ17_021 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc17_0 (v 0)) (h1 : acc17_2 (v 1))
    (h2 : acc17_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P17 alloc17 out17 ![0, 2, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP17_0 _ h0, accP17_2 _ h1, accP17_1 _ h2])⟩

theorem succ17_102 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc17_1 (v 0)) (h1 : acc17_0 (v 1))
    (h2 : acc17_2 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P17 alloc17 out17 ![1, 0, 2] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP17_1 _ h0, accP17_0 _ h1, accP17_2 _ h2])⟩

theorem succ17_120 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc17_1 (v 0)) (h1 : acc17_2 (v 1))
    (h2 : acc17_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P17 alloc17 out17 ![1, 2, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP17_1 _ h0, accP17_2 _ h1, accP17_0 _ h2])⟩

theorem succ17_201 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc17_2 (v 0)) (h1 : acc17_0 (v 1))
    (h2 : acc17_1 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P17 alloc17 out17 ![2, 0, 1] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP17_2 _ h0, accP17_0 _ h1, accP17_1 _ h2])⟩

theorem succ17_210 {α : Type*} [LinearOrder α] (v : Fin 3 → Finset (Fin 8) → α)
    (hv : ∀ i, IsMonotoneVal (v i)) (h0 : acc17_2 (v 0)) (h1 : acc17_1 (v 1))
    (h2 : acc17_0 (v 2)) : ∃ A, IsEF1Outer H 3 v A :=
  ⟨_, ef1_of_acc P17 alloc17 out17 ![2, 1, 0] (by decide) v hv (fun i => by
    fin_cases i
    exacts [accP17_2 _ h0, accP17_1 _ h1, accP17_0 _ h2])⟩

-- The case split below is a single declaration of about 4000 tactic steps.
set_option maxHeartbeats 1000000 in
/-- Every profile of three monotone valuations on `H` has an EF1_outer allocation. -/
theorem H_yes_k3_hetero_monotone {α : Type*} [LinearOrder α]
    (v : Fin 3 → Finset (Fin 8) → α) (hv : ∀ i, IsMonotoneVal (v i)) :
    ∃ A, IsEF1Outer H 3 v A := by
  by_cases a64 : acc11_2 (v 0)
  · have a7 : acc1_0 (v 0) := Classical.byContradiction fun hc => cl64 (v 0) (hv 0) hc a64
    have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl92 (v 0) (hv 0) hc a64
    have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl252 (v 0) (hv 0) hc a64
    have a49 : acc9_1 (v 0) := Classical.byContradiction fun hc => cl269 (v 0) (hv 0) hc a64
    by_cases a3 : acc0_0 (v 1)
    · by_cases a5 : acc0_0 (v 2)
      · by_cases a8 : acc1_0 (v 1)
        · by_cases a9 : acc1_0 (v 2)
          · by_cases a116 : acc9_0 (v 1)
            · have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl227 (v 1) (hv 1) hc a116
              refine (Classical.em (acc9_2 (v 2))).elim (fun a54 => succ9_102 v hv a49 a116 a54) fun a54 => ?_
              have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl123 (v 2) (hv 2) hc a54
              have a48 : ¬acc8_2 (v 2) := fun hc => cl255 (v 2) (hv 2) hc a54
              by_cases a31 : acc5_0 (v 0)
              · by_cases a33 : acc5_0 (v 2)
                · by_cases a38 : acc7_1 (v 1)
                  · have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl237 (v 1) (hv 1) a38 hc
                    have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl240 (v 1) (hv 1) a38 hc
                    refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_210 v hv a64 a62 a138) fun a138 => ?_
                    have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl466 (v 2) (hv 2) hc a54 a138
                    refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_012 v hv a112 a38 a42) fun a112 => ?_
                    refine (Classical.em (acc7_1 (v 0))).elim (fun a37 => succ7_102 v hv a37 a113 a42) fun a37 => ?_
                    have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl149 (v 0) (hv 0) hc a37
                    have a151 : ¬acc5_2 (v 0) := fun hc => cl194 (v 0) (hv 0) hc a37
                    have a28 : acc4_2 (v 0) := Classical.byContradiction fun hc => cl360 (v 0) (hv 0) a112 a37 hc
                    have a22 : acc3_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) hc a112 a151
                    refine (Classical.em (acc3_1 (v 1))).elim (fun a20 => succ3_210 v hv a22 a20 a105) fun a20 => ?_
                    have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl142 (v 1) (hv 1) a20 hc
                    refine (Classical.em (acc4_1 (v 2))).elim (fun a27 => succ4_201 v hv a28 a122 a27) fun a27 => ?_
                    have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl365 (v 2) (hv 2) hc a138 a27
                    have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl416 (v 2) (hv 2) hc a138 a27
                    have a117 : ¬acc9_0 (v 2) := fun hc => cl429 (v 2) (hv 2) hc a27 a138
                    have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl415 (v 2) (hv 2) a117 a27 hc
                    refine (Classical.em (acc15_1 (v 0))).elim (fun a142 => succ15_102 v hv a142 a86 a90) fun a142 => ?_
                    have a55 : acc10_1 (v 0) := Classical.byContradiction fun hc => cl287 (v 0) (hv 0) hc a142
                    refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_102 v hv a55 a134 a60) fun a134 => ?_
                    have a26 : acc4_1 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) hc a134
                    exact succ4_012 v hv a121 a26 a30
                  · have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl149 (v 1) (hv 1) hc a38
                    have a137 : acc11_0 (v 1) := Classical.byContradiction fun hc => cl428 (v 1) (hv 1) a116 a38 hc
                    refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_201 v hv a64 a137 a63) fun a63 => ?_
                    have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl154 (v 2) (hv 2) hc a63
                    have a39 : ¬acc7_1 (v 2) := fun hc => cl237 (v 2) (hv 2) hc a63
                    by_cases a11 : acc1_2 (v 1)
                    · have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl79 (v 1) (hv 1) a11 hc
                      have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl83 (v 1) (hv 1) a11 hc
                      have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl84 (v 1) (hv 1) a11 hc
                      refine (Classical.em (acc1_1 (v 2))).elim (fun a120 => succ1_021 v hv a7 a11 a120) fun a120 => ?_
                      have a15 : acc2_0 (v 2) := Classical.byContradiction fun hc => cl353 (v 2) (hv 2) a120 a63 hc
                      refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_210 v hv a107 a17 a15) fun a107 => ?_
                      refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_012 v hv a13 a17 a111) fun a111 => ?_
                      have a51 : acc9_1 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) a48 a111 hc
                      refine (Classical.em (acc9_2 (v 0))).elim (fun a52 => succ9_201 v hv a52 a116 a51) fun a52 => ?_
                      have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl376 (v 0) (hv 0) a107 a52 hc
                      refine (Classical.em (acc17_2 (v 2))).elim (fun a150 => succ17_102 v hv a100 a98 a150) fun a150 => ?_
                      have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl288 (v 2) (hv 2) hc a150
                      have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 hc a150
                      have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl472 (v 2) (hv 2) a150 a63 hc
                      refine (Classical.em (acc15_1 (v 0))).elim (fun a142 => succ15_102 v hv a142 a86 a90) fun a142 => ?_
                      refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_102 v hv a61 a137 a66) fun a61 => ?_
                      have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl154 (v 0) (hv 0) hc a61
                      have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl465 (v 0) (hv 0) hc a61 a142
                      refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_201 v hv a58 a134 a57) fun a134 => ?_
                      have a26 : acc4_1 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) hc a134
                      have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl279 (v 1) (hv 1) a134 hc
                      refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_210 v hv a58 a56 a135) fun a135 => ?_
                      have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) hc a135 a63
                      exact succ4_012 v hv a121 a26 a30
                    · by_cases a17 : acc2_1 (v 1)
                      · have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl101 (v 1) (hv 1) a17 hc
                        have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl102 (v 1) (hv 1) a17 hc
                        refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_012 v hv a13 a17 a111) fun a111 => ?_
                        have a15 : acc2_0 (v 2) := Classical.byContradiction fun hc => cl474 (v 2) (hv 2) a48 hc a111
                        have a51 : acc9_1 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) a48 a111 hc
                        refine (Classical.em (acc9_2 (v 0))).elim (fun a52 => succ9_201 v hv a52 a116 a51) fun a52 => ?_
                        refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_210 v hv a107 a17 a15) fun a107 => ?_
                        have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl376 (v 0) (hv 0) a107 a52 hc
                        refine (Classical.em (acc17_2 (v 2))).elim (fun a150 => succ17_102 v hv a100 a98 a150) fun a150 => ?_
                        have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl288 (v 2) (hv 2) hc a150
                        have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 hc a150
                        have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl472 (v 2) (hv 2) a150 a63 hc
                        refine (Classical.em (acc15_1 (v 0))).elim (fun a142 => succ15_102 v hv a142 a86 a90) fun a142 => ?_
                        refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_102 v hv a61 a137 a66) fun a61 => ?_
                        have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl154 (v 0) (hv 0) hc a61
                        have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl465 (v 0) (hv 0) hc a61 a142
                        refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_201 v hv a58 a134 a57) fun a134 => ?_
                        have a26 : acc4_1 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) hc a134
                        have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl279 (v 1) (hv 1) a134 hc
                        refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_210 v hv a58 a56 a135) fun a135 => ?_
                        have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) hc a135 a63
                        exact succ4_012 v hv a121 a26 a30
                      · have a95 : acc16_1 (v 1) := Classical.byContradiction fun hc => cl104 (v 1) (hv 1) a17 hc
                        by_cases a10 : acc1_2 (v 0)
                        · have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl79 (v 0) (hv 0) a10 hc
                          have a67 : acc12_0 (v 0) := Classical.byContradiction fun hc => cl80 (v 0) (hv 0) a10 hc
                          have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl83 (v 0) (hv 0) a10 hc
                          have a97 : acc17_0 (v 0) := Classical.byContradiction fun hc => cl84 (v 0) (hv 0) a10 hc
                          refine (Classical.em (acc1_1 (v 1))).elim (fun a119 => succ1_210 v hv a10 a119 a9) fun a119 => ?_
                          have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl345 (v 1) (hv 1) a11 hc a119
                          refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_102 v hv a16 a14 a111) fun a111 => ?_
                          have a15 : acc2_0 (v 2) := Classical.byContradiction fun hc => cl474 (v 2) (hv 2) a48 hc a111
                          have a51 : acc9_1 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) a48 a111 hc
                          refine (Classical.em (acc9_2 (v 0))).elim (fun a52 => succ9_201 v hv a52 a116 a51) fun a52 => ?_
                          have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl455 (v 0) (hv 0) a16 a52 hc
                          refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_120 v hv a16 a109 a15) fun a109 => ?_
                          have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl394 (v 1) (hv 1) a109 hc a17
                          refine (Classical.em (acc17_2 (v 2))).elim (fun a150 => succ17_012 v hv a97 a101 a150) fun a150 => ?_
                          have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl288 (v 2) (hv 2) hc a150
                          have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 hc a150
                          have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl472 (v 2) (hv 2) a150 a63 hc
                          refine (Classical.em (acc15_1 (v 1))).elim (fun a143 => succ15_012 v hv a85 a143 a90) fun a143 => ?_
                          refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                          refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_102 v hv a61 a137 a66) fun a61 => ?_
                          have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl453 (v 1) (hv 1) a143 hc a62
                          have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) hc a62 a143
                          refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_021 v hv a133 a59 a57) fun a133 => ?_
                          have a55 : acc10_1 (v 0) := Classical.byContradiction fun hc => cl279 (v 0) (hv 0) a133 hc
                          have a28 : acc4_2 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) hc a133 a61
                          refine (Classical.em (acc4_1 (v 1))).elim (fun a26 => succ4_210 v hv a28 a26 a123) fun a26 => ?_
                          have a134 : acc10_0 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) a26 hc
                          refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_102 v hv a55 a134 a60) fun a60 => ?_
                          refine (Classical.em (acc10_2 (v 0))).elim (fun a58 => succ10_201 v hv a58 a134 a57) fun a58 => ?_
                          have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl465 (v 0) (hv 0) a58 a61 hc
                          refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                          refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                          have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                          refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_021 v hv a67 a71 a141) fun a71 => ?_
                          exact (cl418 (v 1) (hv 1) a143 a71 a86).elim
                        · by_cases a46 : acc8_2 (v 0)
                          · have a52 : acc9_2 (v 0) := Classical.byContradiction fun hc => cl255 (v 0) (hv 0) a46 hc
                            have a61 : acc11_1 (v 0) := Classical.byContradiction fun hc => cl257 (v 0) (hv 0) a46 hc
                            have a79 : acc14_0 (v 0) := Classical.byContradiction fun hc => cl260 (v 0) (hv 0) a46 hc
                            have a97 : acc17_0 (v 0) := Classical.byContradiction fun hc => cl262 (v 0) (hv 0) a46 hc
                            refine (Classical.em (acc11_2 (v 2))).elim (fun a66 => succ11_102 v hv a61 a137 a66) fun a66 => ?_
                            have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl298 (v 2) (hv 2) a66 hc
                            have a117 : acc9_0 (v 2) := Classical.byContradiction fun hc => cl411 (v 2) (hv 2) hc a66 a39
                            refine (Classical.em (acc9_1 (v 1))).elim (fun a50 => succ9_210 v hv a52 a50 a117) fun a50 => ?_
                            have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl375 (v 1) (hv 1) hc a17 a50
                            have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl479 (v 1) (hv 1) a50 a17 hc
                            refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_021 v hv a97 a149 a102) fun a102 => ?_
                            have a90 : ¬acc15_2 (v 2) := fun hc => cl337 (v 2) (hv 2) hc a102
                            refine (Classical.em (acc2_1 (v 2))).elim (fun a18 => succ2_021 v hv a13 a109 a18) fun a18 => ?_
                            have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) hc a18 a102
                            refine (Classical.em (acc16_0 (v 0))).elim (fun a91 => succ16_012 v hv a91 a95 a147) fun a91 => ?_
                            have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl338 (v 0) (hv 0) a91 hc
                            refine (Classical.em (acc16_0 (v 1))).elim (fun a92 => succ16_102 v hv a94 a92 a147) fun a92 => ?_
                            have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) hc a92
                            refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                            refine (Classical.em (acc14_2 (v 0))).elim (fun a160 => succ14_210 v hv a160 a83 a81) fun a160 => ?_
                            have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl385 (v 0) (hv 0) a160 hc a91
                            refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_120 v hv a100 a149 a99) fun a99 => ?_
                            exact (cl373 (v 2) (hv 2) a162 a90 a99).elim
                          · by_cases a47 : acc8_2 (v 1)
                            · have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl255 (v 1) (hv 1) a47 hc
                              have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl256 (v 1) (hv 1) a47 hc
                              have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl261 (v 1) (hv 1) a47 hc
                              have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl262 (v 1) (hv 1) a47 hc
                              refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                              have a51 : acc9_1 (v 2) := Classical.byContradiction fun hc => cl355 (v 2) (hv 2) a48 hc a132
                              refine (Classical.em (acc9_0 (v 0))).elim (fun a115 => succ9_021 v hv a115 a53 a51) fun a115 => ?_
                              refine (Classical.em (acc9_2 (v 0))).elim (fun a52 => succ9_201 v hv a52 a116 a51) fun a52 => ?_
                              have a55 : acc10_1 (v 0) := Classical.byContradiction fun hc => cl263 (v 0) (hv 0) a115 hc
                              have a148 : ¬acc17_2 (v 0) := fun hc => cl267 (v 0) (hv 0) a115 hc
                              have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl388 (v 0) (hv 0) a52 hc a148
                              refine (Classical.em (acc17_2 (v 2))).elim (fun a150 => succ17_102 v hv a100 a98 a150) fun a150 => ?_
                              have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 hc a150
                              have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl472 (v 2) (hv 2) a150 a63 hc
                              refine (Classical.em (acc15_1 (v 0))).elim (fun a142 => succ15_102 v hv a142 a86 a90) fun a142 => ?_
                              refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_102 v hv a61 a137 a66) fun a61 => ?_
                              have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl453 (v 0) (hv 0) a142 hc a61
                              refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_201 v hv a88 a86 a144) fun a144 => ?_
                              have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl465 (v 2) (hv 2) hc a63 a144
                              refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_012 v hv a133 a56 a60) fun a133 => ?_
                              refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_102 v hv a55 a134 a60) fun a134 => ?_
                              have a26 : acc4_1 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) hc a134
                              refine (Classical.em (acc4_2 (v 0))).elim (fun a28 => succ4_210 v hv a28 a26 a123) fun a28 => ?_
                              exact (cl414 (v 0) (hv 0) a28 a133 a61).elim
                            · by_cases a52 : acc9_2 (v 0)
                              · have a79 : acc14_0 (v 0) := Classical.byContradiction fun hc => cl276 (v 0) (hv 0) a52 hc
                                have a97 : acc17_0 (v 0) := Classical.byContradiction fun hc => cl278 (v 0) (hv 0) a52 hc
                                refine (Classical.em (acc9_1 (v 2))).elim (fun a51 => succ9_201 v hv a52 a116 a51) fun a51 => ?_
                                have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl271 (v 2) (hv 2) a51 hc
                                have a111 : acc2_2 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) a48 hc a51
                                have a117 : acc9_0 (v 2) := Classical.byContradiction fun hc => cl109 (v 2) (hv 2) a111 hc
                                refine (Classical.em (acc9_1 (v 1))).elim (fun a50 => succ9_210 v hv a52 a50 a117) fun a50 => ?_
                                have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl375 (v 1) (hv 1) hc a17 a50
                                have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl479 (v 1) (hv 1) a50 a17 hc
                                refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_021 v hv a97 a149 a102) fun a102 => ?_
                                have a90 : ¬acc15_2 (v 2) := fun hc => cl337 (v 2) (hv 2) hc a102
                                refine (Classical.em (acc2_1 (v 2))).elim (fun a18 => succ2_021 v hv a13 a109 a18) fun a18 => ?_
                                have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) hc a18 a102
                                refine (Classical.em (acc16_0 (v 0))).elim (fun a91 => succ16_012 v hv a91 a95 a147) fun a91 => ?_
                                have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl338 (v 0) (hv 0) a91 hc
                                refine (Classical.em (acc16_0 (v 1))).elim (fun a92 => succ16_102 v hv a94 a92 a147) fun a92 => ?_
                                have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) hc a92
                                refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                                refine (Classical.em (acc14_2 (v 0))).elim (fun a160 => succ14_210 v hv a160 a83 a81) fun a160 => ?_
                                have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl385 (v 0) (hv 0) a160 hc a91
                                refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_120 v hv a100 a149 a99) fun a99 => ?_
                                exact (cl373 (v 2) (hv 2) a162 a90 a99).elim
                              · by_cases a12 : acc1_2 (v 2)
                                · have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl79 (v 2) (hv 2) a12 hc
                                  have a87 : acc15_0 (v 2) := Classical.byContradiction fun hc => cl83 (v 2) (hv 2) a12 hc
                                  have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl84 (v 2) (hv 2) a12 hc
                                  refine (Classical.em (acc1_1 (v 1))).elim (fun a119 => succ1_012 v hv a7 a119 a12) fun a119 => ?_
                                  have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl345 (v 1) (hv 1) a11 hc a119
                                  refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_201 v hv a107 a14 a18) fun a107 => ?_
                                  have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl376 (v 0) (hv 0) a107 a52 hc
                                  refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_120 v hv a100 a149 a99) fun a149 => ?_
                                  have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl288 (v 1) (hv 1) hc a149
                                  have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl455 (v 2) (hv 2) a18 a54 hc
                                  refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_210 v hv a64 a62 a138) fun a62 => ?_
                                  have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl472 (v 1) (hv 1) a149 a62 hc
                                  have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl367 (v 1) (hv 1) a89 a149 hc
                                  refine (Classical.em (acc15_1 (v 0))).elim (fun a142 => succ15_120 v hv a142 a89 a87) fun a142 => ?_
                                  refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_120 v hv a61 a65 a138) fun a61 => ?_
                                  have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl453 (v 0) (hv 0) a142 hc a61
                                  have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl465 (v 0) (hv 0) hc a61 a142
                                  refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_210 v hv a58 a56 a135) fun a135 => ?_
                                  have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl279 (v 2) (hv 2) a135 hc
                                  have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) hc a135 a63
                                  refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                                  have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                  refine (Classical.em (acc10_2 (v 1))).elim (fun a59 => succ10_021 v hv a133 a59 a57) fun a59 => ?_
                                  have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) a59 a62 hc
                                  exact succ15_210 v hv a88 a143 a87
                                · by_cases a18 : acc2_1 (v 2)
                                  · have a87 : acc15_0 (v 2) := Classical.byContradiction fun hc => cl101 (v 2) (hv 2) a18 hc
                                    have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl102 (v 2) (hv 2) a18 hc
                                    have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl455 (v 2) (hv 2) a18 a54 hc
                                    refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_021 v hv a13 a109 a18) fun a109 => ?_
                                    have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl473 (v 1) (hv 1) a11 hc a109
                                    refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_201 v hv a107 a14 a18) fun a107 => ?_
                                    have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl376 (v 0) (hv 0) a107 a52 hc
                                    refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_120 v hv a100 a149 a99) fun a149 => ?_
                                    have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl288 (v 1) (hv 1) hc a149
                                    refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_210 v hv a64 a62 a138) fun a62 => ?_
                                    have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl472 (v 1) (hv 1) a149 a62 hc
                                    have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl367 (v 1) (hv 1) a89 a149 hc
                                    refine (Classical.em (acc15_1 (v 0))).elim (fun a142 => succ15_120 v hv a142 a89 a87) fun a142 => ?_
                                    refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_120 v hv a61 a65 a138) fun a61 => ?_
                                    have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl453 (v 0) (hv 0) a142 hc a61
                                    have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl465 (v 0) (hv 0) hc a61 a142
                                    refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_210 v hv a58 a56 a135) fun a135 => ?_
                                    have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl279 (v 2) (hv 2) a135 hc
                                    have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) hc a135 a63
                                    refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                                    have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                    refine (Classical.em (acc10_2 (v 1))).elim (fun a59 => succ10_021 v hv a133 a59 a57) fun a59 => ?_
                                    have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) a59 a62 hc
                                    exact succ15_210 v hv a88 a143 a87
                                  · have a96 : acc16_1 (v 2) := Classical.byContradiction fun hc => cl104 (v 2) (hv 2) a18 hc
                                    by_cases a15 : acc2_0 (v 2)
                                    · by_cases a16 : acc2_1 (v 0)
                                      · have a67 : acc12_0 (v 0) := Classical.byContradiction fun hc => cl98 (v 0) (hv 0) a16 hc
                                        have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl101 (v 0) (hv 0) a16 hc
                                        have a97 : acc17_0 (v 0) := Classical.byContradiction fun hc => cl102 (v 0) (hv 0) a16 hc
                                        have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl455 (v 0) (hv 0) a16 a52 hc
                                        refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_120 v hv a16 a109 a15) fun a109 => ?_
                                        have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl394 (v 1) (hv 1) a109 hc a17
                                        refine (Classical.em (acc17_2 (v 2))).elim (fun a150 => succ17_012 v hv a97 a101 a150) fun a150 => ?_
                                        have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl288 (v 2) (hv 2) hc a150
                                        have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 hc a150
                                        have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl472 (v 2) (hv 2) a150 a63 hc
                                        refine (Classical.em (acc15_1 (v 1))).elim (fun a143 => succ15_012 v hv a85 a143 a90) fun a143 => ?_
                                        refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                                        refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_102 v hv a61 a137 a66) fun a61 => ?_
                                        have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl453 (v 1) (hv 1) a143 hc a62
                                        have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) hc a62 a143
                                        refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_021 v hv a133 a59 a57) fun a133 => ?_
                                        have a55 : acc10_1 (v 0) := Classical.byContradiction fun hc => cl279 (v 0) (hv 0) a133 hc
                                        have a28 : acc4_2 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) hc a133 a61
                                        refine (Classical.em (acc4_1 (v 1))).elim (fun a26 => succ4_210 v hv a28 a26 a123) fun a26 => ?_
                                        have a134 : acc10_0 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) a26 hc
                                        refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_102 v hv a55 a134 a60) fun a60 => ?_
                                        refine (Classical.em (acc10_2 (v 0))).elim (fun a58 => succ10_201 v hv a58 a134 a57) fun a58 => ?_
                                        have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl465 (v 0) (hv 0) a58 a61 hc
                                        refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                        refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                        have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                        refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_021 v hv a67 a71 a141) fun a71 => ?_
                                        exact (cl418 (v 1) (hv 1) a143 a71 a86).elim
                                      · have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl104 (v 0) (hv 0) a16 hc
                                        by_cases a53 : acc9_2 (v 1)
                                        · have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl272 (v 1) (hv 1) a53 hc
                                          have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl273 (v 1) (hv 1) a53 hc
                                          have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl277 (v 1) (hv 1) a53 hc
                                          refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_120 v hv a49 a53 a117) fun a117 => ?_
                                          have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl411 (v 2) (hv 2) a117 hc a39
                                          refine (Classical.em (acc11_0 (v 0))).elim (fun a136 => succ11_012 v hv a136 a62 a66) fun a136 => ?_
                                          refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_102 v hv a61 a137 a66) fun a61 => ?_
                                          have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl364 (v 0) (hv 0) hc a136 a61
                                          refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_210 v hv a58 a56 a135) fun a135 => ?_
                                          have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) hc a135 a63
                                          refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                                          have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                          have a115 : ¬acc9_0 (v 0) := fun hc => cl429 (v 0) (hv 0) hc a25 a136
                                          have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl415 (v 0) (hv 0) a115 a25 hc
                                          refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_201 v hv a88 a86 a144) fun a144 => ?_
                                          have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl465 (v 2) (hv 2) hc a63 a144
                                          exact succ10_012 v hv a133 a56 a60
                                        · by_cases a62 : acc11_1 (v 1)
                                          · have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl283 (v 1) (hv 1) hc a62
                                            refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_210 v hv a64 a62 a138) fun a138 => ?_
                                            have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl364 (v 2) (hv 2) hc a138 a63
                                            have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl468 (v 2) (hv 2) hc a39 a138
                                            refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                                            have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                            exact succ10_012 v hv a133 a56 a60
                                          · by_cases a14 : acc2_0 (v 1)
                                            · by_cases a100 : acc17_1 (v 0)
                                              · by_cases a37 : acc7_1 (v 0)
                                                · have a61 : acc11_1 (v 0) := Classical.byContradiction fun hc => cl237 (v 0) (hv 0) a37 hc
                                                  have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl240 (v 0) (hv 0) a37 hc
                                                  refine (Classical.em (acc7_2 (v 2))).elim (fun a42 => succ7_102 v hv a37 a113 a42) fun a42 => ?_
                                                  have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl426 (v 2) (hv 2) a39 hc a42
                                                  refine (Classical.em (acc11_2 (v 1))).elim (fun a65 => succ11_120 v hv a61 a65 a138) fun a65 => ?_
                                                  have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl342 (v 1) (hv 1) a53 a65 hc
                                                  have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl459 (v 1) (hv 1) hc a65 a62
                                                  refine (Classical.em (acc15_2 (v 2))).elim (fun a90 => succ15_012 v hv a85 a143 a90) fun a90 => ?_
                                                  have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl326 (v 2) (hv 2) hc a90
                                                  have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl453 (v 2) (hv 2) hc a90 a63
                                                  have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl472 (v 2) (hv 2) hc a63 a90
                                                  refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_102 v hv a100 a98 a150) fun a98 => ?_
                                                  refine (Classical.em (acc15_2 (v 1))).elim (fun a89 => succ15_021 v hv a85 a89 a144) fun a89 => ?_
                                                  have a161 : acc14_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) hc a89 a98
                                                  refine (Classical.em (acc14_1 (v 0))).elim (fun a82 => succ14_120 v hv a82 a161 a81) fun a82 => ?_
                                                  have a79 : acc14_0 (v 0) := Classical.byContradiction fun hc => cl325 (v 0) (hv 0) hc a82
                                                  have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) a82 hc
                                                  refine (Classical.em (acc16_2 (v 1))).elim (fun a146 => succ16_021 v hv a91 a146 a96) fun a146 => ?_
                                                  have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) a98 a146 hc
                                                  refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                                                  have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) a162 a90 hc
                                                  exact succ17_120 v hv a100 a149 a99
                                                · have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl149 (v 0) (hv 0) hc a37
                                                  by_cases a61 : acc11_1 (v 0)
                                                  · have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl296 (v 0) (hv 0) a61 hc
                                                    refine (Classical.em (acc11_2 (v 2))).elim (fun a66 => succ11_102 v hv a61 a137 a66) fun a66 => ?_
                                                    have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 a66 hc
                                                    have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl459 (v 2) (hv 2) hc a66 a63
                                                    refine (Classical.em (acc15_2 (v 1))).elim (fun a89 => succ15_021 v hv a85 a89 a144) fun a89 => ?_
                                                    have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl326 (v 1) (hv 1) hc a89
                                                    have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl453 (v 1) (hv 1) hc a89 a62
                                                    have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl472 (v 1) (hv 1) hc a62 a89
                                                    refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_120 v hv a100 a149 a99) fun a99 => ?_
                                                    refine (Classical.em (acc15_2 (v 2))).elim (fun a90 => succ15_012 v hv a85 a143 a90) fun a90 => ?_
                                                    have a162 : acc14_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) hc a90 a99
                                                    refine (Classical.em (acc14_1 (v 0))).elim (fun a82 => succ14_102 v hv a82 a80 a162) fun a82 => ?_
                                                    have a79 : acc14_0 (v 0) := Classical.byContradiction fun hc => cl325 (v 0) (hv 0) hc a82
                                                    have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) a82 hc
                                                    refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_012 v hv a91 a95 a147) fun a147 => ?_
                                                    refine (Classical.em (acc16_2 (v 1))).elim (fun a146 => succ16_021 v hv a91 a146 a96) fun a146 => ?_
                                                    have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) a146 a17 hc
                                                    refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_012 v hv a97 a101 a150) fun a97 => ?_
                                                    have a145 : acc16_2 (v 0) := Classical.byContradiction fun hc => cl452 (v 0) (hv 0) a97 hc a82
                                                    have a148 : acc17_2 (v 0) := Classical.byContradiction fun hc => cl341 (v 0) (hv 0) a145 hc
                                                    refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_210 v hv a145 a95 a93) fun a93 => ?_
                                                    have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl384 (v 2) (hv 2) a147 hc a93
                                                    refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_201 v hv a148 a98 a102) fun a98 => ?_
                                                    have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) a98 a146 hc
                                                    exact succ14_012 v hv a79 a83 a162
                                                  · by_cases a98 : acc17_0 (v 1)
                                                    · have a68 : acc12_0 (v 1) := Classical.byContradiction fun hc => cl307 (v 1) (hv 1) hc a98
                                                      have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl335 (v 1) (hv 1) hc a98
                                                      refine (Classical.em (acc17_2 (v 2))).elim (fun a150 => succ17_102 v hv a100 a98 a150) fun a150 => ?_
                                                      have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl288 (v 2) (hv 2) hc a150
                                                      have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl472 (v 2) (hv 2) a150 a63 hc
                                                      refine (Classical.em (acc15_1 (v 0))).elim (fun a142 => succ15_102 v hv a142 a86 a90) fun a142 => ?_
                                                      have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl453 (v 0) (hv 0) a142 hc a61
                                                      have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl465 (v 0) (hv 0) hc a61 a142
                                                      refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_201 v hv a58 a134 a57) fun a134 => ?_
                                                      have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl279 (v 1) (hv 1) a134 hc
                                                      have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl414 (v 1) (hv 1) hc a134 a62
                                                      refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_120 v hv a25 a29 a123) fun a25 => ?_
                                                      have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                      refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_012 v hv a133 a56 a60) fun a60 => ?_
                                                      refine (Classical.em (acc10_2 (v 1))).elim (fun a59 => succ10_021 v hv a133 a59 a57) fun a59 => ?_
                                                      have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) a59 a62 hc
                                                      refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
                                                      refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                      have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                      refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_201 v hv a70 a68 a141) fun a70 => ?_
                                                      exact (cl418 (v 0) (hv 0) a142 a70 a85).elim
                                                    · by_cases a20 : acc3_1 (v 1)
                                                      · have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl140 (v 1) (hv 1) a20 hc
                                                        have a68 : acc12_0 (v 1) := Classical.byContradiction fun hc => cl141 (v 1) (hv 1) a20 hc
                                                        have a26 : acc4_1 (v 1) := Classical.byContradiction fun hc => cl368 (v 1) (hv 1) a20 hc a53
                                                        have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl454 (v 1) (hv 1) a20 a53 hc
                                                        have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl424 (v 1) (hv 1) a41 a98 hc
                                                        refine (Classical.em (acc4_2 (v 2))).elim (fun a30 => succ4_012 v hv a121 a26 a30) fun a30 => ?_
                                                        refine (Classical.em (acc4_2 (v 0))).elim (fun a28 => succ4_210 v hv a28 a26 a123) fun a28 => ?_
                                                        have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 hc a61
                                                        refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_012 v hv a133 a56 a60) fun a60 => ?_
                                                        have a75 : acc13_0 (v 2) := Classical.byContradiction fun hc => cl290 (v 2) (hv 2) a60 hc
                                                        have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl465 (v 2) (hv 2) a60 a63 hc
                                                        refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_021 v hv a85 a89 a144) fun a85 => ?_
                                                        have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                                        have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                                        refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                                        have a135 : acc10_0 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) a30 hc a63
                                                        refine (Classical.em (acc10_2 (v 0))).elim (fun a58 => succ10_210 v hv a58 a56 a135) fun a58 => ?_
                                                        have a73 : acc13_0 (v 0) := Classical.byContradiction fun hc => cl290 (v 0) (hv 0) a58 hc
                                                        have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl371 (v 0) (hv 0) a58 hc a85
                                                        have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 hc a85
                                                        refine (Classical.em (acc12_2 (v 2))).elim (fun a72 => succ12_102 v hv a139 a68 a72) fun a72 => ?_
                                                        refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                        have a99 : ¬acc17_0 (v 2) := fun hc => cl335 (v 2) (hv 2) a87 hc
                                                        have a159 : acc13_2 (v 2) := Classical.byContradiction fun hc => cl441 (v 2) (hv 2) a87 hc a72
                                                        refine (Classical.em (acc13_1 (v 1))).elim (fun a77 => succ13_012 v hv a73 a77 a159) fun a77 => ?_
                                                        have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl323 (v 1) (hv 1) a77 hc
                                                        have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl436 (v 1) (hv 1) a86 a77 hc
                                                        refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_120 v hv a76 a158 a75) fun a76 => ?_
                                                        have a79 : acc14_0 (v 0) := Classical.byContradiction fun hc => cl323 (v 0) (hv 0) a76 hc
                                                        have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) a85 hc a76
                                                        refine (Classical.em (acc14_1 (v 2))).elim (fun a84 => succ14_201 v hv a160 a80 a84) fun a84 => ?_
                                                        have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl443 (v 2) (hv 2) a87 hc a84
                                                        have a162 : acc14_2 (v 2) := Classical.byContradiction fun hc => cl387 (v 2) (hv 2) a147 hc a99
                                                        refine (Classical.em (acc16_0 (v 1))).elim (fun a92 => succ16_102 v hv a94 a92 a147) fun a92 => ?_
                                                        have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) hc a92
                                                        exact succ14_012 v hv a79 a83 a162
                                                      · by_cases a83 : acc14_1 (v 1)
                                                        · by_cases a67 : acc12_0 (v 0)
                                                          · by_cases a68 : acc12_0 (v 1)
                                                            · by_cases a69 : acc12_0 (v 2)
                                                              · by_cases a73 : acc13_0 (v 0)
                                                                · by_cases a74 : acc13_0 (v 1)
                                                                  · by_cases a75 : acc13_0 (v 2)
                                                                    · by_cases a99 : acc17_0 (v 2)
                                                                      · have a87 : acc15_0 (v 2) := Classical.byContradiction fun hc => cl335 (v 2) (hv 2) hc a99
                                                                        refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_120 v hv a100 a149 a99) fun a149 => ?_
                                                                        have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl288 (v 1) (hv 1) hc a149
                                                                        have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl472 (v 1) (hv 1) a149 a62 hc
                                                                        refine (Classical.em (acc15_1 (v 0))).elim (fun a142 => succ15_120 v hv a142 a89 a87) fun a142 => ?_
                                                                        have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl453 (v 0) (hv 0) a142 hc a61
                                                                        have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl465 (v 0) (hv 0) hc a61 a142
                                                                        refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_210 v hv a58 a56 a135) fun a135 => ?_
                                                                        have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl279 (v 2) (hv 2) a135 hc
                                                                        have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) hc a135 a63
                                                                        refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                                                                        have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                                        refine (Classical.em (acc10_2 (v 1))).elim (fun a59 => succ10_021 v hv a133 a59 a57) fun a59 => ?_
                                                                        have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) a59 a62 hc
                                                                        exact succ15_210 v hv a88 a143 a87
                                                                      · by_cases a21 : acc3_1 (v 2)
                                                                        · have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl140 (v 2) (hv 2) a21 hc
                                                                          have a27 : acc4_1 (v 2) := Classical.byContradiction fun hc => cl368 (v 2) (hv 2) a21 hc a54
                                                                          have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl454 (v 2) (hv 2) a21 a54 hc
                                                                          have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl424 (v 2) (hv 2) a42 a99 hc
                                                                          refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_021 v hv a121 a29 a27) fun a29 => ?_
                                                                          refine (Classical.em (acc4_2 (v 0))).elim (fun a28 => succ4_201 v hv a28 a122 a27) fun a28 => ?_
                                                                          have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 hc a61
                                                                          refine (Classical.em (acc10_2 (v 1))).elim (fun a59 => succ10_021 v hv a133 a59 a57) fun a59 => ?_
                                                                          have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) a59 a62 hc
                                                                          refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
                                                                          have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                                                          have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                                                          refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                          have a134 : acc10_0 (v 1) := Classical.byContradiction fun hc => cl414 (v 1) (hv 1) a29 hc a62
                                                                          refine (Classical.em (acc10_2 (v 0))).elim (fun a58 => succ10_201 v hv a58 a134 a57) fun a58 => ?_
                                                                          have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 hc a85
                                                                          refine (Classical.em (acc12_2 (v 2))).elim (fun a72 => succ12_102 v hv a139 a68 a72) fun a72 => ?_
                                                                          have a159 : acc13_2 (v 2) := Classical.byContradiction fun hc => cl441 (v 2) (hv 2) a87 hc a72
                                                                          refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_102 v hv a76 a74 a159) fun a76 => ?_
                                                                          have a79 : acc14_0 (v 0) := Classical.byContradiction fun hc => cl323 (v 0) (hv 0) a76 hc
                                                                          have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl436 (v 0) (hv 0) a85 a76 hc
                                                                          refine (Classical.em (acc13_1 (v 2))).elim (fun a78 => succ13_201 v hv a157 a74 a78) fun a78 => ?_
                                                                          have a162 : acc14_2 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 hc a78
                                                                          exact succ14_012 v hv a79 a83 a162
                                                                        · by_cases a55 : acc10_1 (v 0)
                                                                          · by_cases a59 : acc10_2 (v 1)
                                                                            · refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_120 v hv a55 a59 a135) fun a135 => ?_
                                                                              have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl279 (v 2) (hv 2) a135 hc
                                                                              have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) hc a135 a63
                                                                              refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                                                                              have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                                              exact succ10_021 v hv a133 a59 a57
                                                                            · have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) a59 a62 hc
                                                                              by_cases a2 : acc0_1 (v 0)
                                                                              · have a79 : acc14_0 (v 0) := Classical.byContradiction fun hc => cl34 (v 0) (hv 0) a2 hc
                                                                                refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                                                                                have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) a162 hc a99
                                                                                refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
                                                                                have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                                                                have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                                                                refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                                have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                                refine (Classical.em (acc13_2 (v 0))).elim (fun a157 => succ13_201 v hv a157 a74 a78) fun a157 => ?_
                                                                                have a70 : acc12_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 a157 hc
                                                                                refine (Classical.em (acc12_1 (v 1))).elim (fun a140 => succ12_210 v hv a70 a140 a69) fun a140 => ?_
                                                                                have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl284 (v 1) (hv 1) hc a140
                                                                                have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl464 (v 1) (hv 1) a59 a140 hc
                                                                                refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_201 v hv a88 a86 a144) fun a144 => ?_
                                                                                have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl371 (v 2) (hv 2) hc a144 a87
                                                                                have a72 : acc12_2 (v 2) := Classical.byContradiction fun hc => cl418 (v 2) (hv 2) a144 hc a87
                                                                                refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_102 v hv a139 a68 a72) fun a139 => ?_
                                                                                have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) hc a139 a85
                                                                                refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_210 v hv a58 a56 a135) fun a135 => ?_
                                                                                have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) hc a135 a63
                                                                                refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                                                                                have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                                                exact succ10_012 v hv a133 a56 a60
                                                                              · by_cases a30 : acc4_2 (v 2)
                                                                                · have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl166 (v 2) (hv 2) a30 hc
                                                                                  refine (Classical.em (acc4_1 (v 1))).elim (fun a26 => succ4_012 v hv a121 a26 a30) fun a26 => ?_
                                                                                  have a134 : acc10_0 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) a26 hc
                                                                                  refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_102 v hv a55 a134 a60) fun a60 => ?_
                                                                                  have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl465 (v 2) (hv 2) a60 a63 hc
                                                                                  have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl417 (v 2) (hv 2) a66 hc a99
                                                                                  refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
                                                                                  have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                                                                  have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                                                                  refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                                                                  refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                                  have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                  refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_201 v hv a70 a68 a141) fun a70 => ?_
                                                                                  have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 hc a70
                                                                                  refine (Classical.em (acc13_1 (v 2))).elim (fun a78 => succ13_201 v hv a157 a74 a78) fun a78 => ?_
                                                                                  refine (Classical.em (acc13_1 (v 1))).elim (fun a77 => succ13_210 v hv a157 a77 a75) fun a77 => ?_
                                                                                  have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl436 (v 1) (hv 1) a86 a77 hc
                                                                                  refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_120 v hv a76 a158 a75) fun a76 => ?_
                                                                                  have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) a85 hc a76
                                                                                  refine (Classical.em (acc14_0 (v 2))).elim (fun a81 => succ14_210 v hv a160 a83 a81) fun a81 => ?_
                                                                                  exact (cl323 (v 2) (hv 2) a78 a81).elim
                                                                                · have a135 : acc10_0 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) a30 hc a63
                                                                                  by_cases a36 : acc6_0 (v 2)
                                                                                  · by_cases a60 : acc10_2 (v 2)
                                                                                    · refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_102 v hv a55 a134 a60) fun a134 => ?_
                                                                                      have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl279 (v 1) (hv 1) a134 hc
                                                                                      have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl414 (v 1) (hv 1) hc a134 a62
                                                                                      refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_120 v hv a25 a29 a123) fun a25 => ?_
                                                                                      have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                                                      exact succ10_012 v hv a133 a56 a60
                                                                                    · have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl465 (v 2) (hv 2) a60 a63 hc
                                                                                      by_cases a23 : acc3_2 (v 1)
                                                                                      · have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl143 (v 1) (hv 1) a23 hc
                                                                                        have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl424 (v 1) (hv 1) a41 a98 hc
                                                                                        refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_021 v hv a85 a89 a144) fun a85 => ?_
                                                                                        have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                                                                        have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                                                                        refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                                                                        refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                                        have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                        refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_201 v hv a70 a68 a141) fun a70 => ?_
                                                                                        have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 hc a70
                                                                                        refine (Classical.em (acc13_1 (v 2))).elim (fun a78 => succ13_201 v hv a157 a74 a78) fun a78 => ?_
                                                                                        refine (Classical.em (acc13_1 (v 1))).elim (fun a77 => succ13_210 v hv a157 a77 a75) fun a77 => ?_
                                                                                        have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl436 (v 1) (hv 1) a86 a77 hc
                                                                                        refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_120 v hv a76 a158 a75) fun a76 => ?_
                                                                                        have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) a85 hc a76
                                                                                        refine (Classical.em (acc14_0 (v 2))).elim (fun a81 => succ14_210 v hv a160 a83 a81) fun a81 => ?_
                                                                                        exact (cl323 (v 2) (hv 2) a78 a81).elim
                                                                                      · by_cases a24 : acc3_2 (v 2)
                                                                                        · have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl143 (v 2) (hv 2) a24 hc
                                                                                          have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl424 (v 2) (hv 2) a42 a99 hc
                                                                                          refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
                                                                                          have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                                                                          have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                                                                          refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                                                                          refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                                          have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                          refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_201 v hv a70 a68 a141) fun a70 => ?_
                                                                                          have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 hc a70
                                                                                          refine (Classical.em (acc13_1 (v 2))).elim (fun a78 => succ13_201 v hv a157 a74 a78) fun a78 => ?_
                                                                                          refine (Classical.em (acc13_1 (v 1))).elim (fun a77 => succ13_210 v hv a157 a77 a75) fun a77 => ?_
                                                                                          have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl436 (v 1) (hv 1) a86 a77 hc
                                                                                          refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_120 v hv a76 a158 a75) fun a76 => ?_
                                                                                          have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) a85 hc a76
                                                                                          refine (Classical.em (acc14_0 (v 2))).elim (fun a81 => succ14_210 v hv a160 a83 a81) fun a81 => ?_
                                                                                          exact (cl323 (v 2) (hv 2) a78 a81).elim
                                                                                        · by_cases a29 : acc4_2 (v 1)
                                                                                          · have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl166 (v 1) (hv 1) a29 hc
                                                                                            have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl417 (v 1) (hv 1) a65 hc a98
                                                                                            refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_021 v hv a85 a89 a144) fun a85 => ?_
                                                                                            have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                                                                            have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                                                                            refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                                                                            refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                                            have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                            refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_201 v hv a70 a68 a141) fun a70 => ?_
                                                                                            have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 hc a70
                                                                                            refine (Classical.em (acc13_1 (v 2))).elim (fun a78 => succ13_201 v hv a157 a74 a78) fun a78 => ?_
                                                                                            refine (Classical.em (acc13_1 (v 1))).elim (fun a77 => succ13_210 v hv a157 a77 a75) fun a77 => ?_
                                                                                            have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl436 (v 1) (hv 1) a86 a77 hc
                                                                                            refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_120 v hv a76 a158 a75) fun a76 => ?_
                                                                                            have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) a85 hc a76
                                                                                            refine (Classical.em (acc14_0 (v 2))).elim (fun a81 => succ14_210 v hv a160 a83 a81) fun a81 => ?_
                                                                                            exact (cl323 (v 2) (hv 2) a78 a81).elim
                                                                                          · by_cases a34 : acc6_0 (v 0)
                                                                                            · by_cases a41 : acc7_2 (v 1)
                                                                                              · have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl424 (v 1) (hv 1) a41 a98 hc
                                                                                                refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_021 v hv a85 a89 a144) fun a85 => ?_
                                                                                                have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                                                                                have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                                                                                refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                                                                                refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                                                have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                                refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_201 v hv a70 a68 a141) fun a70 => ?_
                                                                                                have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 hc a70
                                                                                                refine (Classical.em (acc13_1 (v 2))).elim (fun a78 => succ13_201 v hv a157 a74 a78) fun a78 => ?_
                                                                                                refine (Classical.em (acc13_1 (v 1))).elim (fun a77 => succ13_210 v hv a157 a77 a75) fun a77 => ?_
                                                                                                have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl436 (v 1) (hv 1) a86 a77 hc
                                                                                                refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_120 v hv a76 a158 a75) fun a76 => ?_
                                                                                                have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) a85 hc a76
                                                                                                refine (Classical.em (acc14_0 (v 2))).elim (fun a81 => succ14_210 v hv a160 a83 a81) fun a81 => ?_
                                                                                                exact (cl323 (v 2) (hv 2) a78 a81).elim
                                                                                              · by_cases a42 : acc7_2 (v 2)
                                                                                                · have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl424 (v 2) (hv 2) a42 a99 hc
                                                                                                  refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
                                                                                                  have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                                                                                  have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                                                                                  refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                                                                                  refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                                                  have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                                  refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_201 v hv a70 a68 a141) fun a70 => ?_
                                                                                                  have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 hc a70
                                                                                                  refine (Classical.em (acc13_1 (v 2))).elim (fun a78 => succ13_201 v hv a157 a74 a78) fun a78 => ?_
                                                                                                  refine (Classical.em (acc13_1 (v 1))).elim (fun a77 => succ13_210 v hv a157 a77 a75) fun a77 => ?_
                                                                                                  have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl436 (v 1) (hv 1) a86 a77 hc
                                                                                                  refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_120 v hv a76 a158 a75) fun a76 => ?_
                                                                                                  have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) a85 hc a76
                                                                                                  refine (Classical.em (acc14_0 (v 2))).elim (fun a81 => succ14_210 v hv a160 a83 a81) fun a81 => ?_
                                                                                                  exact (cl323 (v 2) (hv 2) a78 a81).elim
                                                                                                · by_cases a65 : acc11_2 (v 1)
                                                                                                  · have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl417 (v 1) (hv 1) a65 hc a98
                                                                                                    refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_021 v hv a85 a89 a144) fun a85 => ?_
                                                                                                    have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                                                                                    have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                                                                                    refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                                                                                    refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                                                    have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                                    refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_201 v hv a70 a68 a141) fun a70 => ?_
                                                                                                    have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 hc a70
                                                                                                    refine (Classical.em (acc13_1 (v 2))).elim (fun a78 => succ13_201 v hv a157 a74 a78) fun a78 => ?_
                                                                                                    refine (Classical.em (acc13_1 (v 1))).elim (fun a77 => succ13_210 v hv a157 a77 a75) fun a77 => ?_
                                                                                                    have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl436 (v 1) (hv 1) a86 a77 hc
                                                                                                    refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_120 v hv a76 a158 a75) fun a76 => ?_
                                                                                                    have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) a85 hc a76
                                                                                                    refine (Classical.em (acc14_0 (v 2))).elim (fun a81 => succ14_210 v hv a160 a83 a81) fun a81 => ?_
                                                                                                    exact (cl323 (v 2) (hv 2) a78 a81).elim
                                                                                                  · have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl298 (v 1) (hv 1) a65 hc
                                                                                                    by_cases a66 : acc11_2 (v 2)
                                                                                                    · have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl417 (v 2) (hv 2) a66 hc a99
                                                                                                      refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
                                                                                                      have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                                                                                      have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                                                                                      refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                                                                                      refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                                                      have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                                      refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_201 v hv a70 a68 a141) fun a70 => ?_
                                                                                                      have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 hc a70
                                                                                                      refine (Classical.em (acc13_1 (v 2))).elim (fun a78 => succ13_201 v hv a157 a74 a78) fun a78 => ?_
                                                                                                      refine (Classical.em (acc13_1 (v 1))).elim (fun a77 => succ13_210 v hv a157 a77 a75) fun a77 => ?_
                                                                                                      have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl436 (v 1) (hv 1) a86 a77 hc
                                                                                                      refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_120 v hv a76 a158 a75) fun a76 => ?_
                                                                                                      have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) a85 hc a76
                                                                                                      refine (Classical.em (acc14_0 (v 2))).elim (fun a81 => succ14_210 v hv a160 a83 a81) fun a81 => ?_
                                                                                                      exact (cl323 (v 2) (hv 2) a78 a81).elim
                                                                                                    · have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl298 (v 2) (hv 2) a66 hc
                                                                                                      have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 a66 hc
                                                                                                      refine (Classical.em (acc14_2 (v 0))).elim (fun a160 => succ14_210 v hv a160 a83 a81) fun a160 => ?_
                                                                                                      by_cases a50 : acc9_1 (v 1)
                                                                                                      · have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl393 (v 1) (hv 1) a50 a83 hc
                                                                                                        refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_012 v hv a97 a101 a150) fun a97 => ?_
                                                                                                        have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl373 (v 0) (hv 0) a160 hc a97
                                                                                                        have a145 : ¬acc16_2 (v 0) := fun hc => cl387 (v 0) (hv 0) hc a160 a97
                                                                                                        have a82 : acc14_1 (v 0) := Classical.byContradiction fun hc => cl452 (v 0) (hv 0) a97 a145 hc
                                                                                                        refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_102 v hv a82 a80 a162) fun a162 => ?_
                                                                                                        refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_120 v hv a82 a161 a81) fun a161 => ?_
                                                                                                        have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) a161 hc a98
                                                                                                        refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_021 v hv a85 a89 a144) fun a85 => ?_
                                                                                                        refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                                                        have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                                                        have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                                        refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_201 v hv a70 a68 a141) fun a70 => ?_
                                                                                                        have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 hc a70
                                                                                                        exact succ13_201 v hv a157 a74 a78
                                                                                                      · by_cases a70 : acc12_2 (v 0)
                                                                                                        · have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl309 (v 0) (hv 0) a70 hc
                                                                                                          refine (Classical.em (acc12_1 (v 1))).elim (fun a140 => succ12_210 v hv a70 a140 a69) fun a140 => ?_
                                                                                                          have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl464 (v 1) (hv 1) a59 a140 hc
                                                                                                          exact succ15_201 v hv a88 a86 a144
                                                                                                        · by_cases a71 : acc12_2 (v 1)
                                                                                                          · have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl309 (v 1) (hv 1) a71 hc
                                                                                                            refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_120 v hv a139 a71 a69) fun a139 => ?_
                                                                                                            have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl430 (v 0) (hv 0) hc a139 a70
                                                                                                            exact succ15_021 v hv a85 a89 a144
                                                                                                          · by_cases a72 : acc12_2 (v 2)
                                                                                                            · have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl309 (v 2) (hv 2) a72 hc
                                                                                                              refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_102 v hv a139 a68 a72) fun a139 => ?_
                                                                                                              have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl430 (v 0) (hv 0) hc a139 a70
                                                                                                              exact succ15_012 v hv a85 a143 a90
                                                                                                            · by_cases a76 : acc13_1 (v 0)
                                                                                                              · refine (Classical.em (acc13_2 (v 2))).elim (fun a159 => succ13_102 v hv a76 a74 a159) fun a159 => ?_
                                                                                                                refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_120 v hv a76 a158 a75) fun a158 => ?_
                                                                                                                have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) hc a158 a71
                                                                                                                refine (Classical.em (acc15_2 (v 0))).elim (fun a88 => succ15_201 v hv a88 a86 a144) fun a88 => ?_
                                                                                                                have a97 : acc17_0 (v 0) := Classical.byContradiction fun hc => cl373 (v 0) (hv 0) a160 a88 hc
                                                                                                                have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl453 (v 0) (hv 0) hc a88 a61
                                                                                                                refine (Classical.em (acc15_2 (v 2))).elim (fun a90 => succ15_102 v hv a142 a86 a90) fun a90 => ?_
                                                                                                                have a87 : acc15_0 (v 2) := Classical.byContradiction fun hc => cl438 (v 2) (hv 2) hc a90 a159
                                                                                                                refine (Classical.em (acc15_2 (v 1))).elim (fun a89 => succ15_120 v hv a142 a89 a87) fun a89 => ?_
                                                                                                                have a161 : acc14_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) hc a89 a98
                                                                                                                refine (Classical.em (acc14_1 (v 0))).elim (fun a82 => succ14_120 v hv a82 a161 a81) fun a82 => ?_
                                                                                                                have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) a82 hc
                                                                                                                refine (Classical.em (acc16_2 (v 1))).elim (fun a146 => succ16_021 v hv a91 a146 a96) fun a146 => ?_
                                                                                                                have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) a146 a17 hc
                                                                                                                exact succ17_012 v hv a97 a101 a150
                                                                                                              · have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) hc a160 a76
                                                                                                                refine (Classical.em (acc15_2 (v 1))).elim (fun a89 => succ15_021 v hv a85 a89 a144) fun a89 => ?_
                                                                                                                have a161 : acc14_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) hc a89 a98
                                                                                                                refine (Classical.em (acc14_1 (v 0))).elim (fun a82 => succ14_120 v hv a82 a161 a81) fun a82 => ?_
                                                                                                                have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) a82 hc
                                                                                                                refine (Classical.em (acc16_2 (v 1))).elim (fun a146 => succ16_021 v hv a91 a146 a96) fun a146 => ?_
                                                                                                                have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) a146 a17 hc
                                                                                                                refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_012 v hv a97 a101 a150) fun a97 => ?_
                                                                                                                have a145 : ¬acc16_2 (v 0) := fun hc => cl387 (v 0) (hv 0) hc a160 a97
                                                                                                                exact (cl452 (v 0) (hv 0) a97 a145 a82).elim
                                                                                            · have a82 : acc14_1 (v 0) := Classical.byContradiction fun hc => cl208 (v 0) (hv 0) a34 hc
                                                                                              have a148 : ¬acc17_2 (v 0) := fun hc => cl213 (v 0) (hv 0) a34 hc
                                                                                              have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl472 (v 0) (hv 0) a148 a61 hc
                                                                                              refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                                                                              refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                                              have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                              refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_021 v hv a67 a71 a141) fun a71 => ?_
                                                                                              have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 hc a71
                                                                                              refine (Classical.em (acc13_1 (v 2))).elim (fun a78 => succ13_021 v hv a73 a158 a78) fun a78 => ?_
                                                                                              refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_120 v hv a76 a158 a75) fun a76 => ?_
                                                                                              have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl432 (v 0) (hv 0) hc a148 a76
                                                                                              refine (Classical.em (acc15_2 (v 1))).elim (fun a89 => succ15_021 v hv a85 a89 a144) fun a89 => ?_
                                                                                              have a161 : acc14_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) hc a89 a98
                                                                                              refine (Classical.em (acc14_0 (v 2))).elim (fun a81 => succ14_120 v hv a82 a161 a81) fun a81 => ?_
                                                                                              exact (cl323 (v 2) (hv 2) a78 a81).elim
                                                                                  · have a150 : ¬acc17_2 (v 2) := fun hc => cl213 (v 2) (hv 2) a36 hc
                                                                                    have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl405 (v 2) (hv 2) hc a36 a39
                                                                                    have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl417 (v 2) (hv 2) a66 hc a99
                                                                                    refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
                                                                                    have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                                                                    have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                                                                    refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                                    have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl432 (v 2) (hv 2) a87 a150 hc
                                                                                    refine (Classical.em (acc13_2 (v 0))).elim (fun a157 => succ13_201 v hv a157 a74 a78) fun a157 => ?_
                                                                                    have a70 : acc12_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 a157 hc
                                                                                    refine (Classical.em (acc12_1 (v 1))).elim (fun a140 => succ12_210 v hv a70 a140 a69) fun a140 => ?_
                                                                                    have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl284 (v 1) (hv 1) hc a140
                                                                                    have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl464 (v 1) (hv 1) a59 a140 hc
                                                                                    refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_201 v hv a88 a86 a144) fun a144 => ?_
                                                                                    have a72 : acc12_2 (v 2) := Classical.byContradiction fun hc => cl418 (v 2) (hv 2) a144 hc a87
                                                                                    refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_102 v hv a139 a68 a72) fun a139 => ?_
                                                                                    have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) hc a139 a85
                                                                                    exact succ10_210 v hv a58 a56 a135
                                                                          · have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl284 (v 0) (hv 0) a55 hc
                                                                            have a79 : acc14_0 (v 0) := Classical.byContradiction fun hc => cl286 (v 0) (hv 0) a55 hc
                                                                            have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl287 (v 0) (hv 0) a55 hc
                                                                            refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                                                                            have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) a162 hc a99
                                                                            have a147 : ¬acc16_2 (v 2) := fun hc => cl387 (v 2) (hv 2) hc a162 a99
                                                                            have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl452 (v 2) (hv 2) a99 a147 hc
                                                                            refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_021 v hv a79 a161 a84) fun a161 => ?_
                                                                            have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) a161 hc a98
                                                                            refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                                            have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                            refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_021 v hv a73 a158 a78) fun a158 => ?_
                                                                            refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                                            have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 a158 hc
                                                                            exact succ12_120 v hv a139 a71 a69
                                                                    · have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl290 (v 2) (hv 2) hc a75
                                                                      have a72 : acc12_2 (v 2) := Classical.byContradiction fun hc => cl312 (v 2) (hv 2) hc a75
                                                                      refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_102 v hv a139 a68 a72) fun a139 => ?_
                                                                      have a55 : acc10_1 (v 0) := Classical.byContradiction fun hc => cl284 (v 0) (hv 0) hc a139
                                                                      refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_102 v hv a55 a134 a60) fun a134 => ?_
                                                                      have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl279 (v 1) (hv 1) a134 hc
                                                                      have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl414 (v 1) (hv 1) hc a134 a62
                                                                      refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_120 v hv a25 a29 a123) fun a25 => ?_
                                                                      have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                                      exact succ10_012 v hv a133 a56 a60
                                                                  · have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl290 (v 1) (hv 1) hc a74
                                                                    have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl312 (v 1) (hv 1) hc a74
                                                                    refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_120 v hv a139 a71 a69) fun a139 => ?_
                                                                    have a55 : acc10_1 (v 0) := Classical.byContradiction fun hc => cl284 (v 0) (hv 0) hc a139
                                                                    refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_120 v hv a55 a59 a135) fun a135 => ?_
                                                                    have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl279 (v 2) (hv 2) a135 hc
                                                                    have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) hc a135 a63
                                                                    refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                                                                    have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                                    exact succ10_021 v hv a133 a59 a57
                                                                · have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl290 (v 0) (hv 0) hc a73
                                                                  have a70 : acc12_2 (v 0) := Classical.byContradiction fun hc => cl312 (v 0) (hv 0) hc a73
                                                                  have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl317 (v 0) (hv 0) a73 hc
                                                                  refine (Classical.em (acc12_1 (v 2))).elim (fun a141 => succ12_201 v hv a70 a68 a141) fun a141 => ?_
                                                                  refine (Classical.em (acc12_1 (v 1))).elim (fun a140 => succ12_210 v hv a70 a140 a69) fun a140 => ?_
                                                                  have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl284 (v 1) (hv 1) hc a140
                                                                  refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_210 v hv a58 a56 a135) fun a135 => ?_
                                                                  have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl279 (v 2) (hv 2) a135 hc
                                                                  have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) hc a135 a63
                                                                  refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                                                                  have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                                  refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_012 v hv a133 a56 a60) fun a60 => ?_
                                                                  refine (Classical.em (acc10_2 (v 1))).elim (fun a59 => succ10_021 v hv a133 a59 a57) fun a59 => ?_
                                                                  have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) a59 a62 hc
                                                                  refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                                  exact (cl464 (v 2) (hv 2) a60 a141 a87).elim
                                                              · have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl299 (v 2) (hv 2) a69 hc
                                                                have a159 : acc13_2 (v 2) := Classical.byContradiction fun hc => cl301 (v 2) (hv 2) a69 hc
                                                                have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl302 (v 2) (hv 2) a69 hc
                                                                have a162 : acc14_2 (v 2) := Classical.byContradiction fun hc => cl303 (v 2) (hv 2) a69 hc
                                                                have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl305 (v 2) (hv 2) a69 hc
                                                                refine (Classical.em (acc14_0 (v 0))).elim (fun a79 => succ14_012 v hv a79 a83 a162) fun a79 => ?_
                                                                have a82 : acc14_1 (v 0) := Classical.byContradiction fun hc => cl325 (v 0) (hv 0) a79 hc
                                                                have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl326 (v 0) (hv 0) a79 hc
                                                                refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                                                refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_120 v hv a82 a161 a81) fun a161 => ?_
                                                                have a77 : acc13_1 (v 1) := Classical.byContradiction fun hc => cl433 (v 1) (hv 1) a86 a161 hc
                                                                refine (Classical.em (acc13_0 (v 0))).elim (fun a73 => succ13_012 v hv a73 a77 a159) fun a73 => ?_
                                                                have a70 : acc12_2 (v 0) := Classical.byContradiction fun hc => cl312 (v 0) (hv 0) hc a73
                                                                exact succ12_201 v hv a70 a68 a141
                                                            · have a140 : acc12_1 (v 1) := Classical.byContradiction fun hc => cl299 (v 1) (hv 1) a68 hc
                                                              have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl301 (v 1) (hv 1) a68 hc
                                                              have a161 : acc14_2 (v 1) := Classical.byContradiction fun hc => cl303 (v 1) (hv 1) a68 hc
                                                              have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl308 (v 1) (hv 1) a68 hc
                                                              refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_120 v hv a100 a149 a99) fun a99 => ?_
                                                              refine (Classical.em (acc12_2 (v 2))).elim (fun a72 => succ12_012 v hv a67 a140 a72) fun a72 => ?_
                                                              have a75 : acc13_0 (v 2) := Classical.byContradiction fun hc => cl312 (v 2) (hv 2) a72 hc
                                                              refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_120 v hv a76 a158 a75) fun a76 => ?_
                                                              have a79 : acc14_0 (v 0) := Classical.byContradiction fun hc => cl323 (v 0) (hv 0) a76 hc
                                                              refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                                                              refine (Classical.em (acc14_1 (v 2))).elim (fun a84 => succ14_021 v hv a79 a161 a84) fun a84 => ?_
                                                              have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl452 (v 2) (hv 2) a99 hc a84
                                                              exact (cl387 (v 2) (hv 2) a147 a162 a99).elim
                                                          · have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl299 (v 0) (hv 0) a67 hc
                                                            have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl301 (v 0) (hv 0) a67 hc
                                                            have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl303 (v 0) (hv 0) a67 hc
                                                            refine (Classical.em (acc14_0 (v 2))).elim (fun a81 => succ14_210 v hv a160 a83 a81) fun a81 => ?_
                                                            have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl325 (v 2) (hv 2) a81 hc
                                                            refine (Classical.em (acc14_0 (v 1))).elim (fun a80 => succ14_201 v hv a160 a80 a84) fun a80 => ?_
                                                            have a68 : acc12_0 (v 1) := Classical.byContradiction fun hc => cl302 (v 1) (hv 1) hc a80
                                                            have a77 : acc13_1 (v 1) := Classical.byContradiction fun hc => cl323 (v 1) (hv 1) hc a80
                                                            refine (Classical.em (acc13_0 (v 2))).elim (fun a75 => succ13_210 v hv a157 a77 a75) fun a75 => ?_
                                                            have a72 : acc12_2 (v 2) := Classical.byContradiction fun hc => cl312 (v 2) (hv 2) hc a75
                                                            exact succ12_102 v hv a139 a68 a72
                                                        · have a74 : acc13_0 (v 1) := Classical.byContradiction fun hc => cl315 (v 1) (hv 1) hc a83
                                                          have a146 : acc16_2 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) a98 hc a83
                                                          have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl463 (v 1) (hv 1) hc a83 a98
                                                          have a161 : acc14_2 (v 1) := Classical.byContradiction fun hc => cl387 (v 1) (hv 1) a146 hc a98
                                                          refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_120 v hv a94 a146 a93) fun a93 => ?_
                                                          have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl332 (v 2) (hv 2) hc a93
                                                          refine (Classical.em (acc14_0 (v 0))).elim (fun a79 => succ14_021 v hv a79 a161 a84) fun a79 => ?_
                                                          have a55 : acc10_1 (v 0) := Classical.byContradiction fun hc => cl286 (v 0) (hv 0) hc a79
                                                          have a82 : acc14_1 (v 0) := Classical.byContradiction fun hc => cl325 (v 0) (hv 0) a79 hc
                                                          have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl326 (v 0) (hv 0) a79 hc
                                                          refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                                          refine (Classical.em (acc14_0 (v 2))).elim (fun a81 => succ14_120 v hv a82 a161 a81) fun a81 => ?_
                                                          have a69 : acc12_0 (v 2) := Classical.byContradiction fun hc => cl302 (v 2) (hv 2) hc a81
                                                          have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl323 (v 2) (hv 2) hc a81
                                                          have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl326 (v 2) (hv 2) a81 hc
                                                          refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
                                                          refine (Classical.em (acc13_2 (v 0))).elim (fun a157 => succ13_201 v hv a157 a74 a78) fun a157 => ?_
                                                          have a70 : acc12_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 a157 hc
                                                          refine (Classical.em (acc12_1 (v 1))).elim (fun a140 => succ12_210 v hv a70 a140 a69) fun a140 => ?_
                                                          have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl284 (v 1) (hv 1) hc a140
                                                          have a68 : acc12_0 (v 1) := Classical.byContradiction fun hc => cl299 (v 1) (hv 1) hc a140
                                                          refine (Classical.em (acc12_1 (v 2))).elim (fun a141 => succ12_201 v hv a70 a68 a141) fun a141 => ?_
                                                          have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) hc a141 a87
                                                          refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_012 v hv a133 a56 a60) fun a133 => ?_
                                                          refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_102 v hv a55 a134 a60) fun a134 => ?_
                                                          have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl414 (v 1) (hv 1) hc a134 a62
                                                          refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_120 v hv a25 a29 a123) fun a25 => ?_
                                                          exact (cl163 (v 0) (hv 0) a25 a133).elim
                                              · have a73 : acc13_0 (v 0) := Classical.byContradiction fun hc => cl321 (v 0) (hv 0) hc a100
                                                have a79 : acc14_0 (v 0) := Classical.byContradiction fun hc => cl330 (v 0) (hv 0) hc a100
                                                have a88 : ¬acc15_2 (v 0) := fun hc => cl337 (v 0) (hv 0) hc a100
                                                have a148 : acc17_2 (v 0) := Classical.byContradiction fun hc => cl388 (v 0) (hv 0) a52 a100 hc
                                                have a82 : ¬acc14_1 (v 0) := fun hc => cl393 (v 0) (hv 0) a49 hc a100
                                                have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) a82 hc
                                                refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_012 v hv a91 a95 a147) fun a147 => ?_
                                                refine (Classical.em (acc16_2 (v 1))).elim (fun a146 => succ16_021 v hv a91 a146 a96) fun a146 => ?_
                                                have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) a146 a17 hc
                                                refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_210 v hv a148 a101 a99) fun a99 => ?_
                                                have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl452 (v 2) (hv 2) a99 a147 hc
                                                refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_021 v hv a79 a161 a84) fun a161 => ?_
                                                have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) a147 a18 hc
                                                refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_201 v hv a148 a98 a102) fun a98 => ?_
                                                have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) a161 hc a98
                                                have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) a98 a146 hc
                                                refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                                                have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) a162 hc a99
                                                have a97 : acc17_0 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 a88 hc
                                                have a67 : acc12_0 (v 0) := Classical.byContradiction fun hc => cl307 (v 0) (hv 0) hc a97
                                                refine (Classical.em (acc17_2 (v 2))).elim (fun a150 => succ17_012 v hv a97 a101 a150) fun a150 => ?_
                                                refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_021 v hv a97 a149 a102) fun a149 => ?_
                                                have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl288 (v 1) (hv 1) hc a149
                                                have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 hc a150
                                                refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_102 v hv a61 a137 a66) fun a61 => ?_
                                                have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl412 (v 0) (hv 0) hc a88 a61
                                                have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl453 (v 0) (hv 0) hc a88 a61
                                                refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl432 (v 2) (hv 2) a87 a150 hc
                                                refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_021 v hv a73 a158 a78) fun a158 => ?_
                                                have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 a158 hc
                                                refine (Classical.em (acc12_1 (v 2))).elim (fun a141 => succ12_021 v hv a67 a71 a141) fun a141 => ?_
                                                have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) hc a141 a87
                                                exact succ10_012 v hv a133 a56 a60
                                            · have a71 : ¬acc12_2 (v 1) := fun hc => cl93 (v 1) (hv 1) a14 hc
                                              have a74 : acc13_0 (v 1) := Classical.byContradiction fun hc => cl94 (v 1) (hv 1) a14 hc
                                              have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl95 (v 1) (hv 1) a14 hc
                                              have a101 : ¬acc17_1 (v 1) := fun hc => cl97 (v 1) (hv 1) a14 hc
                                              have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl389 (v 1) (hv 1) a14 hc a17
                                              have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl460 (v 1) (hv 1) hc a14 a62
                                              have a146 : acc16_2 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) hc a17 a101
                                              refine (Classical.em (acc16_0 (v 0))).elim (fun a91 => succ16_021 v hv a91 a146 a96) fun a91 => ?_
                                              refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_120 v hv a94 a146 a93) fun a93 => ?_
                                              have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl332 (v 2) (hv 2) hc a93
                                              refine (Classical.em (acc14_2 (v 0))).elim (fun a160 => succ14_201 v hv a160 a80 a84) fun a160 => ?_
                                              have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl385 (v 0) (hv 0) a160 hc a91
                                              refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_120 v hv a100 a149 a99) fun a99 => ?_
                                              have a82 : acc14_1 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) hc a91
                                              refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_102 v hv a82 a80 a162) fun a162 => ?_
                                              have a69 : acc12_0 (v 2) := Classical.byContradiction fun hc => cl303 (v 2) (hv 2) hc a162
                                              have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) a162 hc a99
                                              have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl385 (v 2) (hv 2) a162 hc a93
                                              refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_021 v hv a97 a149 a102) fun a97 => ?_
                                              have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl373 (v 0) (hv 0) a160 hc a97
                                              refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
                                              have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                              refine (Classical.em (acc13_2 (v 0))).elim (fun a157 => succ13_201 v hv a157 a74 a78) fun a157 => ?_
                                              refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
                                              have a70 : acc12_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 a157 hc
                                              refine (Classical.em (acc12_1 (v 1))).elim (fun a140 => succ12_210 v hv a70 a140 a69) fun a140 => ?_
                                              have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl284 (v 1) (hv 1) hc a140
                                              have a68 : acc12_0 (v 1) := Classical.byContradiction fun hc => cl299 (v 1) (hv 1) hc a140
                                              have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl430 (v 1) (hv 1) hc a140 a71
                                              refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_201 v hv a88 a86 a144) fun a144 => ?_
                                              have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl371 (v 2) (hv 2) hc a144 a87
                                              have a72 : acc12_2 (v 2) := Classical.byContradiction fun hc => cl418 (v 2) (hv 2) a144 hc a87
                                              refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_102 v hv a139 a68 a72) fun a139 => ?_
                                              have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) hc a139 a85
                                              refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_210 v hv a58 a56 a135) fun a135 => ?_
                                              have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) hc a135 a63
                                              refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                                              have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                              exact succ10_012 v hv a133 a56 a60
                                    · have a72 : ¬acc12_2 (v 2) := fun hc => cl93 (v 2) (hv 2) a15 hc
                                      have a75 : acc13_0 (v 2) := Classical.byContradiction fun hc => cl94 (v 2) (hv 2) a15 hc
                                      have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl95 (v 2) (hv 2) a15 hc
                                      have a90 : ¬acc15_2 (v 2) := fun hc => cl96 (v 2) (hv 2) a15 hc
                                      have a102 : ¬acc17_1 (v 2) := fun hc => cl97 (v 2) (hv 2) a15 hc
                                      have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl389 (v 2) (hv 2) a15 hc a18
                                      have a110 : acc0_2 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) hc a12 a15
                                      have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl460 (v 2) (hv 2) hc a15 a63
                                      refine (Classical.em (acc0_1 (v 0))).elim (fun a2 => succ0_102 v hv a2 a3 a110) fun a2 => ?_
                                      have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl36 (v 0) (hv 0) a2 hc
                                      have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) hc a18 a102
                                      refine (Classical.em (acc16_0 (v 0))).elim (fun a91 => succ16_012 v hv a91 a95 a147) fun a91 => ?_
                                      refine (Classical.em (acc16_0 (v 1))).elim (fun a92 => succ16_102 v hv a94 a92 a147) fun a92 => ?_
                                      have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) hc a92
                                      refine (Classical.em (acc14_2 (v 0))).elim (fun a160 => succ14_210 v hv a160 a83 a81) fun a160 => ?_
                                      have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl385 (v 0) (hv 0) a160 hc a91
                                      refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_102 v hv a100 a98 a150) fun a98 => ?_
                                      have a82 : acc14_1 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) hc a91
                                      refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_120 v hv a82 a161 a81) fun a161 => ?_
                                      have a68 : acc12_0 (v 1) := Classical.byContradiction fun hc => cl303 (v 1) (hv 1) hc a161
                                      have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) a161 hc a98
                                      have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl385 (v 1) (hv 1) a161 hc a92
                                      refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_012 v hv a97 a101 a150) fun a97 => ?_
                                      have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl373 (v 0) (hv 0) a160 hc a97
                                      refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                      have a77 : acc13_1 (v 1) := Classical.byContradiction fun hc => cl433 (v 1) (hv 1) a86 a161 hc
                                      refine (Classical.em (acc13_2 (v 0))).elim (fun a157 => succ13_210 v hv a157 a77 a75) fun a157 => ?_
                                      refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_021 v hv a85 a89 a144) fun a85 => ?_
                                      have a70 : acc12_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 a157 hc
                                      refine (Classical.em (acc12_1 (v 2))).elim (fun a141 => succ12_201 v hv a70 a68 a141) fun a141 => ?_
                                      have a69 : acc12_0 (v 2) := Classical.byContradiction fun hc => cl299 (v 2) (hv 2) hc a141
                                      have a87 : acc15_0 (v 2) := Classical.byContradiction fun hc => cl430 (v 2) (hv 2) hc a141 a72
                                      refine (Classical.em (acc15_1 (v 1))).elim (fun a143 => succ15_210 v hv a88 a143 a87) fun a143 => ?_
                                      have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl287 (v 1) (hv 1) hc a143
                                      have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl418 (v 1) (hv 1) a143 hc a86
                                      refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_120 v hv a139 a71 a69) fun a139 => ?_
                                      have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) hc a139 a85
                                      refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_210 v hv a58 a56 a135) fun a135 => ?_
                                      exact (cl412 (v 2) (hv 2) a135 a90 a63).elim
                · have a24 : acc3_2 (v 2) := Classical.byContradiction fun hc => cl146 (v 2) (hv 2) hc a33
                  have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl167 (v 2) (hv 2) hc a33
                  have a51 : acc9_1 (v 2) := Classical.byContradiction fun hc => cl176 (v 2) (hv 2) a33 hc
                  have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl177 (v 2) (hv 2) a33 hc
                  have a138 : ¬acc11_0 (v 2) := fun hc => cl178 (v 2) (hv 2) a33 hc
                  have a69 : acc12_0 (v 2) := Classical.byContradiction fun hc => cl180 (v 2) (hv 2) a33 hc
                  have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl181 (v 2) (hv 2) a33 hc
                  have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl186 (v 2) (hv 2) a33 hc
                  refine (Classical.em (acc9_2 (v 0))).elim (fun a52 => succ9_201 v hv a52 a116 a51) fun a52 => ?_
                  have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl123 (v 0) (hv 0) hc a52
                  refine (Classical.em (acc3_1 (v 1))).elim (fun a20 => succ3_012 v hv a103 a20 a24) fun a20 => ?_
                  have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl142 (v 1) (hv 1) a20 hc
                  refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                  have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl147 (v 0) (hv 0) hc a25
                  have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                  refine (Classical.em (acc10_2 (v 1))).elim (fun a59 => succ10_021 v hv a133 a59 a57) fun a59 => ?_
                  have a74 : acc13_0 (v 1) := Classical.byContradiction fun hc => cl290 (v 1) (hv 1) a59 hc
                  refine (Classical.em (acc13_2 (v 0))).elim (fun a157 => succ13_201 v hv a157 a74 a78) fun a157 => ?_
                  refine (Classical.em (acc4_1 (v 1))).elim (fun a26 => succ4_012 v hv a121 a26 a30) fun a26 => ?_
                  have a134 : acc10_0 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) a26 hc
                  have a137 : acc11_0 (v 1) := Classical.byContradiction fun hc => cl365 (v 1) (hv 1) a59 hc a26
                  refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_201 v hv a64 a137 a63) fun a63 => ?_
                  have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl364 (v 2) (hv 2) hc a138 a63
                  refine (Classical.em (acc10_1 (v 0))).elim (fun a55 => succ10_102 v hv a55 a134 a60) fun a55 => ?_
                  have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl287 (v 0) (hv 0) a55 hc
                  refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                  have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl371 (v 1) (hv 1) a59 hc a86
                  have a140 : acc12_1 (v 1) := Classical.byContradiction fun hc => cl464 (v 1) (hv 1) a59 hc a86
                  refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_210 v hv a70 a140 a69) fun a70 => ?_
                  have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) hc a157 a70
                  exact succ15_012 v hv a85 a143 a90
              · have a28 : acc4_2 (v 0) := Classical.byContradiction fun hc => cl167 (v 0) (hv 0) hc a31
                have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl172 (v 0) (hv 0) a31 hc
                have a55 : acc10_1 (v 0) := Classical.byContradiction fun hc => cl177 (v 0) (hv 0) a31 hc
                have a136 : ¬acc11_0 (v 0) := fun hc => cl178 (v 0) (hv 0) a31 hc
                have a67 : acc12_0 (v 0) := Classical.byContradiction fun hc => cl180 (v 0) (hv 0) a31 hc
                have a76 : acc13_1 (v 0) := Classical.byContradiction fun hc => cl181 (v 0) (hv 0) a31 hc
                have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl186 (v 0) (hv 0) a31 hc
                refine (Classical.em (acc7_1 (v 2))).elim (fun a39 => succ7_201 v hv a40 a113 a39) fun a39 => ?_
                have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl149 (v 2) (hv 2) hc a39
                refine (Classical.em (acc4_1 (v 1))).elim (fun a26 => succ4_210 v hv a28 a26 a123) fun a26 => ?_
                have a134 : acc10_0 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) a26 hc
                have a137 : acc11_0 (v 1) := Classical.byContradiction fun hc => cl429 (v 1) (hv 1) a116 a26 hc
                refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_201 v hv a64 a137 a63) fun a63 => ?_
                refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_102 v hv a55 a134 a60) fun a60 => ?_
                have a75 : acc13_0 (v 2) := Classical.byContradiction fun hc => cl290 (v 2) (hv 2) a60 hc
                have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl364 (v 2) (hv 2) a60 hc a63
                have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl465 (v 2) (hv 2) a60 a63 hc
                refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                have a62 : ¬acc11_1 (v 1) := fun hc => cl296 (v 1) (hv 1) hc a86
                refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_120 v hv a76 a158 a75) fun a158 => ?_
                have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 a158 hc
                refine (Classical.em (acc12_1 (v 2))).elim (fun a141 => succ12_021 v hv a67 a71 a141) fun a141 => ?_
                have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl284 (v 2) (hv 2) hc a141
                have a87 : acc15_0 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 a141 hc
                refine (Classical.em (acc15_1 (v 1))).elim (fun a143 => succ15_210 v hv a88 a143 a87) fun a143 => ?_
                have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl459 (v 1) (hv 1) a143 hc a62
                refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_120 v hv a61 a65 a138) fun a61 => ?_
                have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl364 (v 0) (hv 0) hc a136 a61
                exact succ10_201 v hv a58 a134 a57
            · have a109 : ¬acc2_2 (v 1) := fun hc => cl109 (v 1) (hv 1) hc a116
              have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl247 (v 1) (hv 1) hc a116
              have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl263 (v 1) (hv 1) a116 hc
              have a68 : acc12_0 (v 1) := Classical.byContradiction fun hc => cl264 (v 1) (hv 1) a116 hc
              have a146 : ¬acc16_2 (v 1) := fun hc => cl266 (v 1) (hv 1) a116 hc
              have a149 : ¬acc17_2 (v 1) := fun hc => cl267 (v 1) (hv 1) a116 hc
              by_cases a14 : acc2_0 (v 1)
              · by_cases a45 : acc8_1 (v 2)
                · by_cases a50 : acc9_1 (v 1)
                  · by_cases a57 : acc10_1 (v 2)
                    · have a69 : acc12_0 (v 2) := Classical.byContradiction fun hc => cl281 (v 2) (hv 2) a57 hc
                      by_cases a67 : acc12_0 (v 0)
                      · by_cases a73 : acc13_0 (v 0)
                        · by_cases a74 : acc13_0 (v 1)
                          · by_cases a75 : acc13_0 (v 2)
                            · by_cases a144 : acc15_1 (v 2)
                              · have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl160 (v 2) (hv 2) hc a144
                                have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl293 (v 2) (hv 2) hc a144
                                refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_210 v hv a64 a62 a138) fun a62 => ?_
                                have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl472 (v 1) (hv 1) a149 a62 hc
                                refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_021 v hv a85 a89 a144) fun a85 => ?_
                                have a61 : ¬acc11_1 (v 0) := fun hc => cl296 (v 0) (hv 0) hc a85
                                have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                                have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                                refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
                                have a77 : acc13_1 (v 1) := Classical.byContradiction fun hc => cl432 (v 1) (hv 1) a86 a149 hc
                                refine (Classical.em (acc13_2 (v 0))).elim (fun a157 => succ13_210 v hv a157 a77 a75) fun a157 => ?_
                                have a70 : acc12_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 a157 hc
                                refine (Classical.em (acc12_1 (v 1))).elim (fun a140 => succ12_210 v hv a70 a140 a69) fun a140 => ?_
                                have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl430 (v 1) (hv 1) a86 a140 hc
                                have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl464 (v 1) (hv 1) hc a140 a86
                                refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_021 v hv a133 a59 a57) fun a133 => ?_
                                have a28 : acc4_2 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) hc a133 a61
                                refine (Classical.em (acc4_1 (v 1))).elim (fun a26 => succ4_210 v hv a28 a26 a123) fun a26 => ?_
                                have a134 : acc10_0 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) a26 hc
                                refine (Classical.em (acc10_2 (v 0))).elim (fun a58 => succ10_201 v hv a58 a134 a57) fun a58 => ?_
                                have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 hc a85
                                exact succ12_120 v hv a139 a71 a69
                              · by_cases a55 : acc10_1 (v 0)
                                · by_cases a26 : acc4_1 (v 1)
                                  · by_cases a31 : acc5_0 (v 0)
                                    · by_cases a32 : acc5_0 (v 1)
                                      · by_cases a33 : acc5_0 (v 2)
                                        · by_cases a63 : acc11_1 (v 2)
                                          · refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_201 v hv a64 a137 a63) fun a137 => ?_
                                            by_cases a27 : acc4_1 (v 2)
                                            · by_cases a38 : acc7_1 (v 1)
                                              · have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl237 (v 1) (hv 1) a38 hc
                                                refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_210 v hv a64 a62 a138) fun a138 => ?_
                                                by_cases a34 : acc6_0 (v 0)
                                                · by_cases a36 : acc6_0 (v 2)
                                                  · by_cases a39 : acc7_1 (v 2)
                                                    · by_cases a35 : acc6_0 (v 1)
                                                      · by_cases a18 : acc2_1 (v 2)
                                                        · have a54 : acc9_2 (v 2) := Classical.byContradiction fun hc => cl455 (v 2) (hv 2) a18 hc a138
                                                          refine (Classical.em (acc9_0 (v 0))).elim (fun a115 => succ9_012 v hv a115 a50 a54) fun a115 => ?_
                                                          by_cases a17 : acc2_1 (v 1)
                                                          · have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl455 (v 1) (hv 1) a17 hc a137
                                                            refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_012 v hv a13 a17 a111) fun a111 => ?_
                                                            refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_120 v hv a49 a53 a117) fun a117 => ?_
                                                            by_cases a15 : acc2_0 (v 2)
                                                            · by_cases a25 : acc4_1 (v 0)
                                                              · by_cases a37 : acc7_1 (v 0)
                                                                · by_cases a40 : acc7_2 (v 0)
                                                                  · refine (Classical.em (acc7_0 (v 1))).elim (fun a113 => succ7_201 v hv a40 a113 a39) fun a113 => ?_
                                                                    refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_210 v hv a40 a38 a114) fun a114 => ?_
                                                                    by_cases a19 : acc3_1 (v 0)
                                                                    · by_cases a4 : acc0_1 (v 1)
                                                                      · by_cases a6 : acc0_1 (v 2)
                                                                        · by_cases a20 : acc3_1 (v 1)
                                                                          · by_cases a2 : acc0_1 (v 0)
                                                                            · by_cases a16 : acc2_1 (v 0)
                                                                              · by_cases a21 : acc3_1 (v 2)
                                                                                · by_cases a22 : acc3_2 (v 0)
                                                                                  · refine (Classical.em (acc3_0 (v 2))).elim (fun a105 => succ3_210 v hv a22 a20 a105) fun a105 => ?_
                                                                                    have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl118 (v 2) (hv 2) a105 hc
                                                                                    refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                                                                    have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl356 (v 0) (hv 0) hc a115 a127
                                                                                    refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                                    have a129 : acc6_1 (v 2) := Classical.byContradiction fun hc => cl215 (v 2) (hv 2) hc a132
                                                                                    refine (Classical.em (acc6_2 (v 1))).elim (fun a155 => succ6_021 v hv a34 a155 a129) fun a155 => ?_
                                                                                    refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_201 v hv a154 a35 a129) fun a154 => ?_
                                                                                    have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl118 (v 0) (hv 0) hc a154
                                                                                    refine (Classical.em (acc3_2 (v 1))).elim (fun a23 => succ3_021 v hv a103 a23 a21) fun a23 => ?_
                                                                                    have a152 : acc5_2 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) a23 a113 hc
                                                                                    refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_120 v hv a124 a152 a33) fun a124 => ?_
                                                                                    have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) a154 a124 hc
                                                                                    refine (Classical.em (acc7_2 (v 1))).elim (fun a41 => succ7_021 v hv a112 a41 a39) fun a41 => ?_
                                                                                    exact (cl408 (v 1) (hv 1) a155 a116 a41).elim
                                                                                  · by_cases a23 : acc3_2 (v 1)
                                                                                    · refine (Classical.em (acc3_0 (v 0))).elim (fun a103 => succ3_021 v hv a103 a23 a21) fun a103 => ?_
                                                                                      refine (Classical.em (acc3_0 (v 2))).elim (fun a105 => succ3_120 v hv a19 a23 a105) fun a105 => ?_
                                                                                      have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl118 (v 2) (hv 2) a105 hc
                                                                                      refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                                                                      have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl344 (v 0) (hv 0) a103 hc a127
                                                                                      refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                                      have a129 : acc6_1 (v 2) := Classical.byContradiction fun hc => cl215 (v 2) (hv 2) hc a132
                                                                                      refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_201 v hv a154 a35 a129) fun a154 => ?_
                                                                                      exact (cl118 (v 0) (hv 0) a103 a154).elim
                                                                                    · have a152 : acc5_2 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) a23 a113 hc
                                                                                      refine (Classical.em (acc5_1 (v 2))).elim (fun a126 => succ5_021 v hv a31 a152 a126) fun a126 => ?_
                                                                                      refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_120 v hv a124 a152 a33) fun a124 => ?_
                                                                                      have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl456 (v 2) (hv 2) hc a126 a114
                                                                                      refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                                                                      have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl356 (v 0) (hv 0) hc a115 a127
                                                                                      refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                                      have a129 : acc6_1 (v 2) := Classical.byContradiction fun hc => cl215 (v 2) (hv 2) hc a132
                                                                                      refine (Classical.em (acc6_2 (v 1))).elim (fun a155 => succ6_021 v hv a34 a155 a129) fun a155 => ?_
                                                                                      refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_201 v hv a154 a35 a129) fun a154 => ?_
                                                                                      have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) a154 a124 hc
                                                                                      refine (Classical.em (acc7_2 (v 1))).elim (fun a41 => succ7_021 v hv a112 a41 a39) fun a41 => ?_
                                                                                      exact (cl408 (v 1) (hv 1) a155 a116 a41).elim
                                                                                · have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl349 (v 2) (hv 2) a114 hc a21
                                                                                  have a126 : acc5_1 (v 2) := Classical.byContradiction fun hc => cl422 (v 2) (hv 2) hc a21 a114
                                                                                  refine (Classical.em (acc5_2 (v 0))).elim (fun a151 => succ5_201 v hv a151 a32 a126) fun a151 => ?_
                                                                                  have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl116 (v 0) (hv 0) hc a151
                                                                                  refine (Classical.em (acc3_2 (v 2))).elim (fun a24 => succ3_012 v hv a103 a20 a24) fun a24 => ?_
                                                                                  have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                                                                  refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_102 v hv a124 a32 a153) fun a124 => ?_
                                                                                  have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl407 (v 0) (hv 0) a124 a151 hc
                                                                                  exact succ7_012 v hv a112 a38 a42
                                                                              · have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl103 (v 0) (hv 0) a16 hc
                                                                                refine (Classical.em (acc3_2 (v 2))).elim (fun a24 => succ3_012 v hv a103 a20 a24) fun a24 => ?_
                                                                                have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                                                                refine (Classical.em (acc5_1 (v 1))).elim (fun a125 => succ5_012 v hv a31 a125 a153) fun a125 => ?_
                                                                                have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl456 (v 1) (hv 1) hc a125 a113
                                                                                refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                                                have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                                                have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl462 (v 0) (hv 0) a16 hc a127
                                                                                have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl229 (v 0) (hv 0) hc a136
                                                                                refine (Classical.em (acc7_2 (v 2))).elim (fun a42 => succ7_012 v hv a112 a38 a42) fun a42 => ?_
                                                                                have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) hc a117 a42
                                                                                refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_012 v hv a34 a128 a156) fun a128 => ?_
                                                                                have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl356 (v 1) (hv 1) hc a116 a128
                                                                                exact succ8_021 v hv a130 a47 a45
                                                                            · have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl35 (v 0) (hv 0) a2 hc
                                                                              refine (Classical.em (acc3_2 (v 2))).elim (fun a24 => succ3_012 v hv a103 a20 a24) fun a24 => ?_
                                                                              have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                                                              refine (Classical.em (acc5_1 (v 1))).elim (fun a125 => succ5_012 v hv a31 a125 a153) fun a125 => ?_
                                                                              have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl456 (v 1) (hv 1) hc a125 a113
                                                                              refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_021 v hv a34 a155 a129) fun a129 => ?_
                                                                              refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                                              have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl356 (v 0) (hv 0) hc a115 a127
                                                                              refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                              exact (cl215 (v 2) (hv 2) a129 a132).elim
                                                                          · have a104 : acc3_0 (v 1) := Classical.byContradiction fun hc => cl112 (v 1) (hv 1) hc a20
                                                                            have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl349 (v 1) (hv 1) a113 hc a20
                                                                            have a125 : acc5_1 (v 1) := Classical.byContradiction fun hc => cl422 (v 1) (hv 1) hc a20 a113
                                                                            have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl461 (v 1) (hv 1) hc a20 a113
                                                                            refine (Classical.em (acc4_0 (v 2))).elim (fun a123 => succ4_120 v hv a25 a29 a123) fun a123 => ?_
                                                                            have a21 : acc3_1 (v 2) := Classical.byContradiction fun hc => cl142 (v 2) (hv 2) hc a123
                                                                            refine (Classical.em (acc3_2 (v 0))).elim (fun a22 => succ3_201 v hv a22 a104 a21) fun a22 => ?_
                                                                            refine (Classical.em (acc5_2 (v 0))).elim (fun a151 => succ5_210 v hv a151 a125 a33) fun a151 => ?_
                                                                            have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) a22 hc a151
                                                                            exact succ7_021 v hv a112 a41 a39
                                                                        · have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl35 (v 2) (hv 2) a6 hc
                                                                          refine (Classical.em (acc3_2 (v 1))).elim (fun a23 => succ3_120 v hv a19 a23 a105) fun a23 => ?_
                                                                          have a152 : acc5_2 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) a23 a113 hc
                                                                          refine (Classical.em (acc5_1 (v 2))).elim (fun a126 => succ5_021 v hv a31 a152 a126) fun a126 => ?_
                                                                          refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_120 v hv a124 a152 a33) fun a124 => ?_
                                                                          have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl456 (v 2) (hv 2) hc a126 a114
                                                                          refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                                                          have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl356 (v 0) (hv 0) hc a115 a127
                                                                          refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                          have a129 : acc6_1 (v 2) := Classical.byContradiction fun hc => cl215 (v 2) (hv 2) hc a132
                                                                          refine (Classical.em (acc6_2 (v 1))).elim (fun a155 => succ6_021 v hv a34 a155 a129) fun a155 => ?_
                                                                          refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_201 v hv a154 a35 a129) fun a154 => ?_
                                                                          have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) a154 a124 hc
                                                                          refine (Classical.em (acc7_2 (v 1))).elim (fun a41 => succ7_021 v hv a112 a41 a39) fun a41 => ?_
                                                                          exact (cl408 (v 1) (hv 1) a155 a116 a41).elim
                                                                      · have a104 : acc3_0 (v 1) := Classical.byContradiction fun hc => cl35 (v 1) (hv 1) a4 hc
                                                                        refine (Classical.em (acc3_2 (v 2))).elim (fun a24 => succ3_102 v hv a19 a104 a24) fun a24 => ?_
                                                                        have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                                                        refine (Classical.em (acc5_1 (v 1))).elim (fun a125 => succ5_012 v hv a31 a125 a153) fun a125 => ?_
                                                                        have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl456 (v 1) (hv 1) hc a125 a113
                                                                        refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_021 v hv a34 a155 a129) fun a129 => ?_
                                                                        refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                                        have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl356 (v 0) (hv 0) hc a115 a127
                                                                        refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                        exact (cl215 (v 2) (hv 2) a129 a132).elim
                                                                    · have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl112 (v 0) (hv 0) hc a19
                                                                      have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl142 (v 0) (hv 0) a19 hc
                                                                      refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_021 v hv a121 a29 a27) fun a29 => ?_
                                                                      have a20 : acc3_1 (v 1) := Classical.byContradiction fun hc => cl461 (v 1) (hv 1) a29 hc a113
                                                                      refine (Classical.em (acc3_2 (v 2))).elim (fun a24 => succ3_012 v hv a103 a20 a24) fun a24 => ?_
                                                                      have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                                                      refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_102 v hv a124 a32 a153) fun a124 => ?_
                                                                      have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl422 (v 0) (hv 0) a124 a19 hc
                                                                      refine (Classical.em (acc7_2 (v 1))).elim (fun a41 => succ7_021 v hv a112 a41 a39) fun a41 => ?_
                                                                      have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl408 (v 1) (hv 1) hc a116 a41
                                                                      refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_021 v hv a34 a155 a129) fun a129 => ?_
                                                                      refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                                      have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl356 (v 0) (hv 0) hc a115 a127
                                                                      refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                      exact (cl215 (v 2) (hv 2) a129 a132).elim
                                                                  · have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl408 (v 0) (hv 0) hc a115 a40
                                                                    refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_201 v hv a154 a35 a129) fun a129 => ?_
                                                                    refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_210 v hv a154 a128 a36) fun a128 => ?_
                                                                    have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl356 (v 1) (hv 1) hc a116 a128
                                                                    refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                                                    exact (cl215 (v 2) (hv 2) a129 a132).elim
                                                                · have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl120 (v 0) (hv 0) hc a37
                                                                  have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl149 (v 0) (hv 0) hc a37
                                                                  have a151 : ¬acc5_2 (v 0) := fun hc => cl194 (v 0) (hv 0) hc a37
                                                                  have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl406 (v 0) (hv 0) a115 a37 hc
                                                                  refine (Classical.em (acc7_0 (v 1))).elim (fun a113 => succ7_201 v hv a40 a113 a39) fun a113 => ?_
                                                                  refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_210 v hv a40 a38 a114) fun a114 => ?_
                                                                  refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_021 v hv a121 a29 a27) fun a29 => ?_
                                                                  have a20 : acc3_1 (v 1) := Classical.byContradiction fun hc => cl461 (v 1) (hv 1) a29 hc a113
                                                                  refine (Classical.em (acc3_2 (v 2))).elim (fun a24 => succ3_012 v hv a103 a20 a24) fun a24 => ?_
                                                                  have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                                                  refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_102 v hv a124 a32 a153) fun a124 => ?_
                                                                  have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl407 (v 0) (hv 0) a124 a151 hc
                                                                  refine (Classical.em (acc7_2 (v 1))).elim (fun a41 => succ7_021 v hv a112 a41 a39) fun a41 => ?_
                                                                  have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl408 (v 1) (hv 1) hc a116 a41
                                                                  refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_021 v hv a34 a155 a129) fun a129 => ?_
                                                                  refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                                  have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl356 (v 0) (hv 0) hc a115 a127
                                                                  refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                  exact (cl215 (v 2) (hv 2) a129 a132).elim
                                                              · have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl114 (v 0) (hv 0) hc a25
                                                                have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl147 (v 0) (hv 0) hc a25
                                                                have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl362 (v 0) (hv 0) hc a115 a25
                                                                refine (Classical.em (acc7_0 (v 1))).elim (fun a113 => succ7_201 v hv a40 a113 a39) fun a113 => ?_
                                                                refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_210 v hv a40 a38 a114) fun a114 => ?_
                                                                refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_021 v hv a121 a29 a27) fun a29 => ?_
                                                                have a20 : acc3_1 (v 1) := Classical.byContradiction fun hc => cl461 (v 1) (hv 1) a29 hc a113
                                                                refine (Classical.em (acc3_2 (v 2))).elim (fun a24 => succ3_012 v hv a103 a20 a24) fun a24 => ?_
                                                                have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                                                refine (Classical.em (acc5_1 (v 1))).elim (fun a125 => succ5_012 v hv a31 a125 a153) fun a125 => ?_
                                                                have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl456 (v 1) (hv 1) hc a125 a113
                                                                refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_021 v hv a34 a155 a129) fun a129 => ?_
                                                                refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                                have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl356 (v 0) (hv 0) hc a115 a127
                                                                refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                exact (cl215 (v 2) (hv 2) a129 a132).elim
                                                            · have a51 : ¬acc9_1 (v 2) := fun hc => cl90 (v 2) (hv 2) a15 hc
                                                              have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl474 (v 2) (hv 2) hc a15 a111
                                                              refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_102 v hv a43 a131 a48) fun a131 => ?_
                                                              have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) hc a131
                                                              refine (Classical.em (acc6_2 (v 2))).elim (fun a156 => succ6_012 v hv a34 a128 a156) fun a156 => ?_
                                                              refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_210 v hv a154 a128 a36) fun a154 => ?_
                                                              have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl408 (v 0) (hv 0) a154 a115 hc
                                                              refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_210 v hv a40 a38 a114) fun a114 => ?_
                                                              exact (cl401 (v 2) (hv 2) a156 a114 a51).elim
                                                          · have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl462 (v 1) (hv 1) a17 a137 hc
                                                            refine (Classical.em (acc6_2 (v 2))).elim (fun a156 => succ6_012 v hv a34 a128 a156) fun a156 => ?_
                                                            refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_210 v hv a154 a128 a36) fun a154 => ?_
                                                            have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl118 (v 0) (hv 0) hc a154
                                                            have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl408 (v 0) (hv 0) a154 a115 hc
                                                            refine (Classical.em (acc7_0 (v 1))).elim (fun a113 => succ7_201 v hv a40 a113 a39) fun a113 => ?_
                                                            refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_210 v hv a40 a38 a114) fun a114 => ?_
                                                            have a126 : acc5_1 (v 2) := Classical.byContradiction fun hc => cl456 (v 2) (hv 2) a156 hc a114
                                                            refine (Classical.em (acc5_2 (v 1))).elim (fun a152 => succ5_021 v hv a31 a152 a126) fun a152 => ?_
                                                            refine (Classical.em (acc5_2 (v 0))).elim (fun a151 => succ5_201 v hv a151 a32 a126) fun a151 => ?_
                                                            have a23 : acc3_2 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) hc a113 a152
                                                            refine (Classical.em (acc3_1 (v 2))).elim (fun a21 => succ3_021 v hv a103 a23 a21) fun a21 => ?_
                                                            have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl112 (v 2) (hv 2) hc a21
                                                            have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl142 (v 2) (hv 2) a21 hc
                                                            have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl349 (v 2) (hv 2) a114 hc a21
                                                            have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl461 (v 2) (hv 2) hc a21 a114
                                                            refine (Classical.em (acc4_0 (v 0))).elim (fun a121 => succ4_012 v hv a121 a26 a30) fun a121 => ?_
                                                            have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl147 (v 0) (hv 0) a121 hc
                                                            refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_120 v hv a25 a29 a123) fun a29 => ?_
                                                            have a20 : acc3_1 (v 1) := Classical.byContradiction fun hc => cl461 (v 1) (hv 1) a29 hc a113
                                                            refine (Classical.em (acc3_2 (v 0))).elim (fun a22 => succ3_210 v hv a22 a20 a105) fun a22 => ?_
                                                            have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) a22 hc a151
                                                            exact succ7_012 v hv a112 a38 a42
                                                        · have a129 : acc6_1 (v 2) := Classical.byContradiction fun hc => cl462 (v 2) (hv 2) a18 a138 hc
                                                          refine (Classical.em (acc6_2 (v 1))).elim (fun a155 => succ6_021 v hv a34 a155 a129) fun a155 => ?_
                                                          refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_201 v hv a154 a35 a129) fun a154 => ?_
                                                          have a104 : acc3_0 (v 1) := Classical.byContradiction fun hc => cl118 (v 1) (hv 1) hc a155
                                                          have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl408 (v 1) (hv 1) a155 a116 hc
                                                          refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_021 v hv a112 a41 a39) fun a112 => ?_
                                                          have a115 : ¬acc9_0 (v 0) := fun hc => cl227 (v 0) (hv 0) a112 hc
                                                          have a124 : acc5_1 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) a154 hc a112
                                                          refine (Classical.em (acc5_2 (v 2))).elim (fun a153 => succ5_102 v hv a124 a32 a153) fun a153 => ?_
                                                          have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl408 (v 0) (hv 0) a154 a115 hc
                                                          refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_210 v hv a40 a38 a114) fun a114 => ?_
                                                          have a126 : acc5_1 (v 2) := Classical.byContradiction fun hc => cl407 (v 2) (hv 2) hc a153 a114
                                                          have a24 : acc3_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) hc a114 a153
                                                          refine (Classical.em (acc3_1 (v 0))).elim (fun a19 => succ3_102 v hv a19 a104 a24) fun a19 => ?_
                                                          have a28 : acc4_2 (v 0) := Classical.byContradiction fun hc => cl461 (v 0) (hv 0) hc a19 a112
                                                          refine (Classical.em (acc4_0 (v 2))).elim (fun a123 => succ4_210 v hv a28 a26 a123) fun a123 => ?_
                                                          have a21 : acc3_1 (v 2) := Classical.byContradiction fun hc => cl142 (v 2) (hv 2) hc a123
                                                          refine (Classical.em (acc3_2 (v 0))).elim (fun a22 => succ3_201 v hv a22 a104 a21) fun a22 => ?_
                                                          have a151 : acc5_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) a22 a112 hc
                                                          exact succ5_201 v hv a151 a32 a126
                                                      · have a104 : acc3_0 (v 1) := Classical.byContradiction fun hc => cl117 (v 1) (hv 1) hc a35
                                                        have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl200 (v 1) (hv 1) a35 hc
                                                        have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl201 (v 1) (hv 1) a35 hc
                                                        refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_021 v hv a112 a41 a39) fun a112 => ?_
                                                        have a115 : ¬acc9_0 (v 0) := fun hc => cl227 (v 0) (hv 0) a112 hc
                                                        refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_210 v hv a154 a128 a36) fun a154 => ?_
                                                        have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl408 (v 0) (hv 0) a154 a115 hc
                                                        have a124 : acc5_1 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) a154 hc a112
                                                        refine (Classical.em (acc5_2 (v 2))).elim (fun a153 => succ5_102 v hv a124 a32 a153) fun a153 => ?_
                                                        refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_210 v hv a40 a38 a114) fun a114 => ?_
                                                        have a126 : acc5_1 (v 2) := Classical.byContradiction fun hc => cl407 (v 2) (hv 2) hc a153 a114
                                                        have a24 : acc3_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) hc a114 a153
                                                        refine (Classical.em (acc3_1 (v 0))).elim (fun a19 => succ3_102 v hv a19 a104 a24) fun a19 => ?_
                                                        have a28 : acc4_2 (v 0) := Classical.byContradiction fun hc => cl461 (v 0) (hv 0) hc a19 a112
                                                        refine (Classical.em (acc4_0 (v 2))).elim (fun a123 => succ4_210 v hv a28 a26 a123) fun a123 => ?_
                                                        have a21 : acc3_1 (v 2) := Classical.byContradiction fun hc => cl142 (v 2) (hv 2) hc a123
                                                        refine (Classical.em (acc3_2 (v 0))).elim (fun a22 => succ3_201 v hv a22 a104 a21) fun a22 => ?_
                                                        have a151 : acc5_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) a22 a112 hc
                                                        exact succ5_201 v hv a151 a32 a126
                                                    · have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl120 (v 2) (hv 2) hc a39
                                                      have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl149 (v 2) (hv 2) hc a39
                                                      have a153 : ¬acc5_2 (v 2) := fun hc => cl194 (v 2) (hv 2) hc a39
                                                      have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl426 (v 2) (hv 2) a39 a138 hc
                                                      have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl468 (v 2) (hv 2) hc a39 a138
                                                      have a51 : acc9_1 (v 2) := Classical.byContradiction fun hc => cl165 (v 2) (hv 2) a30 hc
                                                      refine (Classical.em (acc4_0 (v 0))).elim (fun a121 => succ4_012 v hv a121 a26 a30) fun a121 => ?_
                                                      have a19 : acc3_1 (v 0) := Classical.byContradiction fun hc => cl142 (v 0) (hv 0) hc a121
                                                      have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl147 (v 0) (hv 0) a121 hc
                                                      have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl149 (v 0) (hv 0) a121 hc
                                                      refine (Classical.em (acc7_0 (v 1))).elim (fun a113 => succ7_102 v hv a37 a113 a42) fun a113 => ?_
                                                      refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_120 v hv a25 a29 a123) fun a29 => ?_
                                                      have a20 : acc3_1 (v 1) := Classical.byContradiction fun hc => cl461 (v 1) (hv 1) a29 hc a113
                                                      refine (Classical.em (acc3_2 (v 1))).elim (fun a23 => succ3_120 v hv a19 a23 a105) fun a23 => ?_
                                                      have a152 : acc5_2 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) a23 a113 hc
                                                      refine (Classical.em (acc5_1 (v 2))).elim (fun a126 => succ5_021 v hv a31 a152 a126) fun a126 => ?_
                                                      have a114 : acc7_0 (v 2) := Classical.byContradiction fun hc => cl407 (v 2) (hv 2) a126 a153 hc
                                                      refine (Classical.em (acc7_2 (v 1))).elim (fun a41 => succ7_120 v hv a37 a41 a114) fun a41 => ?_
                                                      refine (Classical.em (acc7_2 (v 0))).elim (fun a40 => succ7_210 v hv a40 a38 a114) fun a40 => ?_
                                                      have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl201 (v 1) (hv 1) hc a41
                                                      have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl454 (v 1) (hv 1) a20 hc a41
                                                      refine (Classical.em (acc9_0 (v 0))).elim (fun a115 => succ9_021 v hv a115 a53 a51) fun a115 => ?_
                                                      have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl408 (v 0) (hv 0) hc a115 a40
                                                      refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_201 v hv a154 a35 a129) fun a129 => ?_
                                                      refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_210 v hv a154 a128 a36) fun a128 => ?_
                                                      have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl356 (v 1) (hv 1) hc a116 a128
                                                      refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                                      exact (cl215 (v 2) (hv 2) a129 a132).elim
                                                  · have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl117 (v 2) (hv 2) hc a36
                                                    have a126 : acc5_1 (v 2) := Classical.byContradiction fun hc => cl192 (v 2) (hv 2) hc a36
                                                    have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl201 (v 2) (hv 2) a36 hc
                                                    refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_012 v hv a112 a38 a42) fun a112 => ?_
                                                    refine (Classical.em (acc5_2 (v 1))).elim (fun a152 => succ5_021 v hv a31 a152 a126) fun a152 => ?_
                                                    refine (Classical.em (acc5_2 (v 0))).elim (fun a151 => succ5_201 v hv a151 a32 a126) fun a151 => ?_
                                                    have a22 : acc3_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) hc a112 a151
                                                    refine (Classical.em (acc3_1 (v 1))).elim (fun a20 => succ3_210 v hv a22 a20 a105) fun a20 => ?_
                                                    have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl142 (v 1) (hv 1) a20 hc
                                                    refine (Classical.em (acc4_2 (v 0))).elim (fun a28 => succ4_201 v hv a28 a122 a27) fun a28 => ?_
                                                    have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl360 (v 0) (hv 0) a112 hc a28
                                                    have a19 : acc3_1 (v 0) := Classical.byContradiction fun hc => cl461 (v 0) (hv 0) a28 hc a112
                                                    refine (Classical.em (acc3_2 (v 1))).elim (fun a23 => succ3_120 v hv a19 a23 a105) fun a23 => ?_
                                                    have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) a23 hc a152
                                                    exact succ7_102 v hv a37 a113 a42
                                                · have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl117 (v 0) (hv 0) hc a34
                                                  have a124 : acc5_1 (v 0) := Classical.byContradiction fun hc => cl192 (v 0) (hv 0) hc a34
                                                  have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl201 (v 0) (hv 0) a34 hc
                                                  refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_210 v hv a40 a38 a114) fun a114 => ?_
                                                  refine (Classical.em (acc5_2 (v 2))).elim (fun a153 => succ5_102 v hv a124 a32 a153) fun a153 => ?_
                                                  refine (Classical.em (acc5_2 (v 1))).elim (fun a152 => succ5_120 v hv a124 a152 a33) fun a152 => ?_
                                                  have a104 : acc3_0 (v 1) := Classical.byContradiction fun hc => cl116 (v 1) (hv 1) hc a152
                                                  have a24 : acc3_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) hc a114 a153
                                                  refine (Classical.em (acc3_1 (v 1))).elim (fun a20 => succ3_012 v hv a103 a20 a24) fun a20 => ?_
                                                  refine (Classical.em (acc3_1 (v 0))).elim (fun a19 => succ3_102 v hv a19 a104 a24) fun a19 => ?_
                                                  have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl142 (v 0) (hv 0) a19 hc
                                                  refine (Classical.em (acc4_2 (v 2))).elim (fun a30 => succ4_012 v hv a121 a26 a30) fun a30 => ?_
                                                  refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_021 v hv a121 a29 a27) fun a29 => ?_
                                                  have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl461 (v 1) (hv 1) a29 a20 hc
                                                  refine (Classical.em (acc7_1 (v 2))).elim (fun a39 => succ7_201 v hv a40 a113 a39) fun a39 => ?_
                                                  exact (cl360 (v 2) (hv 2) a114 a39 a30).elim
                                              · have a104 : acc3_0 (v 1) := Classical.byContradiction fun hc => cl120 (v 1) (hv 1) hc a38
                                                have a152 : ¬acc5_2 (v 1) := fun hc => cl194 (v 1) (hv 1) hc a38
                                                have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl406 (v 1) (hv 1) a116 a38 hc
                                                have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl468 (v 1) (hv 1) hc a38 a137
                                                refine (Classical.em (acc4_0 (v 0))).elim (fun a121 => succ4_021 v hv a121 a29 a27) fun a121 => ?_
                                                have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl147 (v 0) (hv 0) a121 hc
                                                have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl149 (v 0) (hv 0) a121 hc
                                                refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_120 v hv a37 a41 a114) fun a114 => ?_
                                                have a117 : ¬acc9_0 (v 2) := fun hc => cl227 (v 2) (hv 2) a114 hc
                                                refine (Classical.em (acc4_0 (v 2))).elim (fun a123 => succ4_120 v hv a25 a29 a123) fun a123 => ?_
                                                have a21 : acc3_1 (v 2) := Classical.byContradiction fun hc => cl142 (v 2) (hv 2) hc a123
                                                have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl149 (v 2) (hv 2) a123 hc
                                                refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_021 v hv a112 a41 a39) fun a112 => ?_
                                                have a115 : ¬acc9_0 (v 0) := fun hc => cl227 (v 0) (hv 0) a112 hc
                                                refine (Classical.em (acc3_2 (v 0))).elim (fun a22 => succ3_201 v hv a22 a104 a21) fun a22 => ?_
                                                have a151 : acc5_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) a22 a112 hc
                                                refine (Classical.em (acc5_1 (v 1))).elim (fun a125 => succ5_210 v hv a151 a125 a33) fun a125 => ?_
                                                have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl192 (v 1) (hv 1) a125 hc
                                                have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl407 (v 1) (hv 1) a125 a152 hc
                                                refine (Classical.em (acc7_2 (v 0))).elim (fun a40 => succ7_201 v hv a40 a113 a39) fun a40 => ?_
                                                have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl408 (v 0) (hv 0) hc a115 a40
                                                refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_201 v hv a154 a35 a129) fun a129 => ?_
                                                have a36 : acc6_0 (v 2) := Classical.byContradiction fun hc => cl200 (v 2) (hv 2) hc a129
                                                have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl356 (v 2) (hv 2) hc a117 a129
                                                refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_102 v hv a43 a131 a48) fun a131 => ?_
                                                have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) hc a131
                                                exact succ6_210 v hv a154 a128 a36
                                            · have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl114 (v 2) (hv 2) hc a27
                                              have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl147 (v 2) (hv 2) hc a27
                                              have a135 : acc10_0 (v 2) := Classical.byContradiction fun hc => cl163 (v 2) (hv 2) a27 hc
                                              refine (Classical.em (acc10_2 (v 1))).elim (fun a59 => succ10_120 v hv a55 a59 a135) fun a59 => ?_
                                              refine (Classical.em (acc10_2 (v 0))).elim (fun a58 => succ10_210 v hv a58 a56 a135) fun a58 => ?_
                                              have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl364 (v 1) (hv 1) a59 a137 hc
                                              refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_210 v hv a64 a62 a138) fun a138 => ?_
                                              have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl416 (v 2) (hv 2) hc a138 a27
                                              have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl425 (v 2) (hv 2) a138 a27 hc
                                              have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl427 (v 2) (hv 2) a27 a138 hc
                                              refine (Classical.em (acc11_0 (v 0))).elim (fun a136 => succ11_012 v hv a136 a62 a66) fun a136 => ?_
                                              have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl365 (v 0) (hv 0) a58 a136 hc
                                              refine (Classical.em (acc4_0 (v 1))).elim (fun a122 => succ4_102 v hv a25 a122 a30) fun a122 => ?_
                                              refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_120 v hv a25 a29 a123) fun a29 => ?_
                                              have a38 : acc7_1 (v 1) := Classical.byContradiction fun hc => cl468 (v 1) (hv 1) a29 hc a137
                                              refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_012 v hv a112 a38 a42) fun a112 => ?_
                                              have a115 : ¬acc9_0 (v 0) := fun hc => cl227 (v 0) (hv 0) a112 hc
                                              have a20 : acc3_1 (v 1) := Classical.byContradiction fun hc => cl142 (v 1) (hv 1) hc a122
                                              refine (Classical.em (acc3_2 (v 0))).elim (fun a22 => succ3_210 v hv a22 a20 a105) fun a22 => ?_
                                              have a151 : acc5_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) a22 a112 hc
                                              have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl194 (v 0) (hv 0) a151 hc
                                              refine (Classical.em (acc5_1 (v 2))).elim (fun a126 => succ5_201 v hv a151 a32 a126) fun a126 => ?_
                                              refine (Classical.em (acc5_1 (v 1))).elim (fun a125 => succ5_210 v hv a151 a125 a33) fun a125 => ?_
                                              have a36 : acc6_0 (v 2) := Classical.byContradiction fun hc => cl192 (v 2) (hv 2) a126 hc
                                              refine (Classical.em (acc7_0 (v 1))).elim (fun a113 => succ7_102 v hv a37 a113 a42) fun a113 => ?_
                                              have a152 : acc5_2 (v 1) := Classical.byContradiction fun hc => cl407 (v 1) (hv 1) a125 hc a113
                                              have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl456 (v 1) (hv 1) hc a125 a113
                                              refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                              have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl356 (v 0) (hv 0) hc a115 a127
                                              refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_201 v hv a46 a131 a45) fun a131 => ?_
                                              have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) hc a131
                                              refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_210 v hv a154 a128 a36) fun a154 => ?_
                                              have a124 : acc5_1 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) a154 hc a112
                                              exact succ5_120 v hv a124 a152 a33
                                          · have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl127 (v 2) (hv 2) hc a63
                                            have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl154 (v 2) (hv 2) hc a63
                                            have a39 : ¬acc7_1 (v 2) := fun hc => cl237 (v 2) (hv 2) hc a63
                                            have a54 : ¬acc9_2 (v 2) := fun hc => cl273 (v 2) (hv 2) hc a63
                                            have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl465 (v 2) (hv 2) hc a63 a144
                                            refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_012 v hv a133 a56 a60) fun a133 => ?_
                                            refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_102 v hv a55 a134 a60) fun a134 => ?_
                                            have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) hc a133
                                            refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_120 v hv a25 a29 a123) fun a29 => ?_
                                            have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl414 (v 1) (hv 1) a29 a134 hc
                                            refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_210 v hv a64 a62 a138) fun a138 => ?_
                                            have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl426 (v 2) (hv 2) a39 a138 hc
                                            have a18 : ¬acc2_1 (v 2) := fun hc => cl455 (v 2) (hv 2) hc a54 a138
                                            have a129 : acc6_1 (v 2) := Classical.byContradiction fun hc => cl462 (v 2) (hv 2) a18 a138 hc
                                            have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl468 (v 2) (hv 2) hc a39 a138
                                            refine (Classical.em (acc4_0 (v 1))).elim (fun a122 => succ4_102 v hv a25 a122 a30) fun a122 => ?_
                                            have a20 : acc3_1 (v 1) := Classical.byContradiction fun hc => cl142 (v 1) (hv 1) hc a122
                                            have a38 : acc7_1 (v 1) := Classical.byContradiction fun hc => cl149 (v 1) (hv 1) a122 hc
                                            refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_012 v hv a112 a38 a42) fun a112 => ?_
                                            refine (Classical.em (acc3_2 (v 0))).elim (fun a22 => succ3_210 v hv a22 a20 a105) fun a22 => ?_
                                            have a151 : acc5_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) a22 a112 hc
                                            have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl194 (v 0) (hv 0) a151 hc
                                            refine (Classical.em (acc5_1 (v 1))).elim (fun a125 => succ5_210 v hv a151 a125 a33) fun a125 => ?_
                                            have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl192 (v 1) (hv 1) a125 hc
                                            refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_201 v hv a154 a35 a129) fun a154 => ?_
                                            have a124 : acc5_1 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) a154 hc a112
                                            refine (Classical.em (acc5_2 (v 1))).elim (fun a152 => succ5_120 v hv a124 a152 a33) fun a152 => ?_
                                            have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl407 (v 1) (hv 1) a125 a152 hc
                                            exact succ7_102 v hv a37 a113 a42
                                        · have a24 : acc3_2 (v 2) := Classical.byContradiction fun hc => cl146 (v 2) (hv 2) hc a33
                                          have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl167 (v 2) (hv 2) hc a33
                                          have a126 : acc5_1 (v 2) := Classical.byContradiction fun hc => cl168 (v 2) (hv 2) a33 hc
                                          have a138 : ¬acc11_0 (v 2) := fun hc => cl178 (v 2) (hv 2) a33 hc
                                          have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl179 (v 2) (hv 2) a33 hc
                                          have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl181 (v 2) (hv 2) a33 hc
                                          have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl186 (v 2) (hv 2) a33 hc
                                          refine (Classical.em (acc13_2 (v 0))).elim (fun a157 => succ13_201 v hv a157 a74 a78) fun a157 => ?_
                                          refine (Classical.em (acc5_2 (v 0))).elim (fun a151 => succ5_201 v hv a151 a32 a126) fun a151 => ?_
                                          have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl116 (v 0) (hv 0) hc a151
                                          refine (Classical.em (acc3_1 (v 1))).elim (fun a20 => succ3_012 v hv a103 a20 a24) fun a20 => ?_
                                          have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl142 (v 1) (hv 1) a20 hc
                                          refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                                          have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                          refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_012 v hv a133 a56 a60) fun a60 => ?_
                                          have a63 : acc11_1 (v 2) := Classical.byContradiction fun hc => cl364 (v 2) (hv 2) a60 a138 hc
                                          have a27 : acc4_1 (v 2) := Classical.byContradiction fun hc => cl365 (v 2) (hv 2) a60 a138 hc
                                          have a87 : acc15_0 (v 2) := Classical.byContradiction fun hc => cl371 (v 2) (hv 2) a60 a144 hc
                                          refine (Classical.em (acc4_2 (v 0))).elim (fun a28 => succ4_201 v hv a28 a122 a27) fun a28 => ?_
                                          have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl416 (v 0) (hv 0) a28 hc a25
                                          refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                                          refine (Classical.em (acc11_2 (v 1))).elim (fun a65 => succ11_021 v hv a136 a65 a63) fun a65 => ?_
                                          have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl459 (v 1) (hv 1) hc a65 a62
                                          refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
                                          refine (Classical.em (acc15_2 (v 0))).elim (fun a88 => succ15_210 v hv a88 a143 a87) fun a88 => ?_
                                          exact (cl438 (v 0) (hv 0) a85 a88 a157).elim
                                      · have a23 : acc3_2 (v 1) := Classical.byContradiction fun hc => cl146 (v 1) (hv 1) hc a32
                                        have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl167 (v 1) (hv 1) hc a32
                                        have a125 : acc5_1 (v 1) := Classical.byContradiction fun hc => cl168 (v 1) (hv 1) a32 hc
                                        have a137 : ¬acc11_0 (v 1) := fun hc => cl178 (v 1) (hv 1) a32 hc
                                        refine (Classical.em (acc5_2 (v 2))).elim (fun a153 => succ5_012 v hv a31 a125 a153) fun a153 => ?_
                                        have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl116 (v 2) (hv 2) hc a153
                                        refine (Classical.em (acc3_1 (v 0))).elim (fun a19 => succ3_120 v hv a19 a23 a105) fun a19 => ?_
                                        have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl142 (v 0) (hv 0) a19 hc
                                        refine (Classical.em (acc4_2 (v 2))).elim (fun a30 => succ4_012 v hv a121 a26 a30) fun a30 => ?_
                                        refine (Classical.em (acc4_1 (v 2))).elim (fun a27 => succ4_021 v hv a121 a29 a27) fun a27 => ?_
                                        have a135 : acc10_0 (v 2) := Classical.byContradiction fun hc => cl163 (v 2) (hv 2) a27 hc
                                        have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl416 (v 2) (hv 2) a30 hc a27
                                        refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_210 v hv a64 a62 a138) fun a62 => ?_
                                        have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl364 (v 1) (hv 1) hc a137 a62
                                        exact succ10_120 v hv a55 a59 a135
                                    · have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl115 (v 0) (hv 0) hc a31
                                      have a28 : acc4_2 (v 0) := Classical.byContradiction fun hc => cl167 (v 0) (hv 0) hc a31
                                      have a124 : acc5_1 (v 0) := Classical.byContradiction fun hc => cl168 (v 0) (hv 0) a31 hc
                                      have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl172 (v 0) (hv 0) a31 hc
                                      refine (Classical.em (acc4_0 (v 2))).elim (fun a123 => succ4_210 v hv a28 a26 a123) fun a123 => ?_
                                      have a21 : acc3_1 (v 2) := Classical.byContradiction fun hc => cl142 (v 2) (hv 2) hc a123
                                      have a33 : acc5_0 (v 2) := Classical.byContradiction fun hc => cl148 (v 2) (hv 2) a123 hc
                                      have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl149 (v 2) (hv 2) a123 hc
                                      refine (Classical.em (acc7_0 (v 1))).elim (fun a113 => succ7_201 v hv a40 a113 a39) fun a113 => ?_
                                      refine (Classical.em (acc5_2 (v 1))).elim (fun a152 => succ5_120 v hv a124 a152 a33) fun a152 => ?_
                                      have a23 : acc3_2 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) hc a113 a152
                                      exact succ3_021 v hv a103 a23 a21
                                  · have a104 : acc3_0 (v 1) := Classical.byContradiction fun hc => cl114 (v 1) (hv 1) hc a26
                                    have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl147 (v 1) (hv 1) hc a26
                                    have a134 : acc10_0 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) a26 hc
                                    have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl362 (v 1) (hv 1) hc a116 a26
                                    have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl415 (v 1) (hv 1) a116 a26 hc
                                    have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl367 (v 1) (hv 1) a89 a149 hc
                                    refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_102 v hv a55 a134 a60) fun a60 => ?_
                                    have a63 : acc11_1 (v 2) := Classical.byContradiction fun hc => cl465 (v 2) (hv 2) a60 hc a144
                                    refine (Classical.em (acc11_0 (v 0))).elim (fun a136 => succ11_021 v hv a136 a65 a63) fun a136 => ?_
                                    refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_201 v hv a64 a137 a63) fun a137 => ?_
                                    have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl365 (v 1) (hv 1) hc a137 a26
                                    have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl416 (v 1) (hv 1) hc a137 a26
                                    have a131 : ¬acc8_0 (v 1) := fun hc => cl423 (v 1) (hv 1) hc a137 a26
                                    have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) hc a131
                                    refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_120 v hv a55 a59 a135) fun a135 => ?_
                                    have a27 : acc4_1 (v 2) := Classical.byContradiction fun hc => cl163 (v 2) (hv 2) hc a135
                                    refine (Classical.em (acc4_2 (v 0))).elim (fun a28 => succ4_201 v hv a28 a122 a27) fun a28 => ?_
                                    have a31 : acc5_0 (v 0) := Classical.byContradiction fun hc => cl167 (v 0) (hv 0) a28 hc
                                    have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl416 (v 0) (hv 0) a28 a136 hc
                                    have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl468 (v 0) (hv 0) a28 hc a136
                                    refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_120 v hv a37 a41 a114) fun a114 => ?_
                                    refine (Classical.em (acc4_0 (v 2))).elim (fun a123 => succ4_120 v hv a25 a29 a123) fun a123 => ?_
                                    have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl149 (v 2) (hv 2) a123 hc
                                    refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_021 v hv a112 a41 a39) fun a112 => ?_
                                    have a19 : acc3_1 (v 0) := Classical.byContradiction fun hc => cl461 (v 0) (hv 0) a28 hc a112
                                    refine (Classical.em (acc3_2 (v 2))).elim (fun a24 => succ3_102 v hv a19 a104 a24) fun a24 => ?_
                                    have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                    refine (Classical.em (acc5_1 (v 1))).elim (fun a125 => succ5_012 v hv a31 a125 a153) fun a125 => ?_
                                    have a32 : acc5_0 (v 1) := Classical.byContradiction fun hc => cl168 (v 1) (hv 1) hc a125
                                    have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl192 (v 1) (hv 1) a125 hc
                                    refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_102 v hv a124 a32 a153) fun a124 => ?_
                                    have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) hc a124 a112
                                    refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_201 v hv a154 a35 a129) fun a129 => ?_
                                    refine (Classical.em (acc6_0 (v 2))).elim (fun a36 => succ6_210 v hv a154 a128 a36) fun a36 => ?_
                                    exact (cl200 (v 2) (hv 2) a36 a129).elim
                                · have a34 : acc6_0 (v 0) := Classical.byContradiction fun hc => cl206 (v 0) (hv 0) hc a55
                                  have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl228 (v 0) (hv 0) hc a55
                                  have a115 : acc9_0 (v 0) := Classical.byContradiction fun hc => cl263 (v 0) (hv 0) hc a55
                                  have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl282 (v 0) (hv 0) a55 hc
                                  have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl284 (v 0) (hv 0) a55 hc
                                  have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl287 (v 0) (hv 0) a55 hc
                                  refine (Classical.em (acc12_2 (v 2))).elim (fun a72 => succ12_102 v hv a139 a68 a72) fun a72 => ?_
                                  have a87 : acc15_0 (v 2) := Classical.byContradiction fun hc => cl418 (v 2) (hv 2) a144 a72 hc
                                  refine (Classical.em (acc15_2 (v 1))).elim (fun a89 => succ15_120 v hv a142 a89 a87) fun a89 => ?_
                                  have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl472 (v 1) (hv 1) a149 hc a89
                                  refine (Classical.em (acc11_2 (v 2))).elim (fun a66 => succ11_012 v hv a136 a62 a66) fun a66 => ?_
                                  refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_210 v hv a64 a62 a138) fun a138 => ?_
                                  have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl410 (v 2) (hv 2) a66 hc a138
                                  refine (Classical.em (acc7_2 (v 1))).elim (fun a41 => succ7_021 v hv a112 a41 a39) fun a41 => ?_
                                  have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl408 (v 1) (hv 1) hc a116 a41
                                  refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_021 v hv a34 a155 a129) fun a129 => ?_
                                  have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl462 (v 2) (hv 2) hc a138 a129
                                  have a54 : acc9_2 (v 2) := Classical.byContradiction fun hc => cl455 (v 2) (hv 2) a18 hc a138
                                  exact succ9_012 v hv a115 a50 a54
                            · have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl130 (v 2) (hv 2) hc a75
                              have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl157 (v 2) (hv 2) hc a75
                              have a126 : acc5_1 (v 2) := Classical.byContradiction fun hc => cl193 (v 2) (hv 2) hc a75
                              have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl243 (v 2) (hv 2) hc a75
                              have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl290 (v 2) (hv 2) hc a75
                              have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl297 (v 2) (hv 2) hc a75
                              have a72 : acc12_2 (v 2) := Classical.byContradiction fun hc => cl312 (v 2) (hv 2) hc a75
                              refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_102 v hv a139 a68 a72) fun a139 => ?_
                              have a55 : acc10_1 (v 0) := Classical.byContradiction fun hc => cl284 (v 0) (hv 0) hc a139
                              refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_102 v hv a55 a134 a60) fun a134 => ?_
                              have a26 : acc4_1 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) hc a134
                              refine (Classical.em (acc4_2 (v 0))).elim (fun a28 => succ4_210 v hv a28 a26 a123) fun a28 => ?_
                              have a31 : acc5_0 (v 0) := Classical.byContradiction fun hc => cl167 (v 0) (hv 0) a28 hc
                              refine (Classical.em (acc5_2 (v 1))).elim (fun a152 => succ5_021 v hv a31 a152 a126) fun a152 => ?_
                              refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_012 v hv a133 a56 a60) fun a133 => ?_
                              have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) hc a133
                              have a61 : acc11_1 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 a133 hc
                              refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_102 v hv a61 a137 a66) fun a137 => ?_
                              refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_120 v hv a25 a29 a123) fun a29 => ?_
                              have a38 : acc7_1 (v 1) := Classical.byContradiction fun hc => cl468 (v 1) (hv 1) a29 hc a137
                              refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_012 v hv a112 a38 a42) fun a112 => ?_
                              have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl360 (v 0) (hv 0) a112 hc a28
                              have a19 : acc3_1 (v 0) := Classical.byContradiction fun hc => cl461 (v 0) (hv 0) a28 hc a112
                              refine (Classical.em (acc3_2 (v 1))).elim (fun a23 => succ3_120 v hv a19 a23 a105) fun a23 => ?_
                              have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) a23 hc a152
                              exact succ7_102 v hv a37 a113 a42
                          · have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl157 (v 1) (hv 1) hc a74
                            have a125 : acc5_1 (v 1) := Classical.byContradiction fun hc => cl193 (v 1) (hv 1) hc a74
                            have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl216 (v 1) (hv 1) hc a74
                            have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl243 (v 1) (hv 1) hc a74
                            have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl290 (v 1) (hv 1) hc a74
                            have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl297 (v 1) (hv 1) hc a74
                            have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl312 (v 1) (hv 1) hc a74
                            have a86 : ¬acc15_0 (v 1) := fun hc => cl316 (v 1) (hv 1) a74 hc
                            refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_120 v hv a139 a71 a69) fun a139 => ?_
                            have a55 : acc10_1 (v 0) := Classical.byContradiction fun hc => cl284 (v 0) (hv 0) hc a139
                            refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_120 v hv a55 a59 a135) fun a135 => ?_
                            have a27 : acc4_1 (v 2) := Classical.byContradiction fun hc => cl163 (v 2) (hv 2) hc a135
                            refine (Classical.em (acc4_2 (v 0))).elim (fun a28 => succ4_201 v hv a28 a122 a27) fun a28 => ?_
                            have a31 : acc5_0 (v 0) := Classical.byContradiction fun hc => cl167 (v 0) (hv 0) a28 hc
                            refine (Classical.em (acc5_2 (v 2))).elim (fun a153 => succ5_012 v hv a31 a125 a153) fun a153 => ?_
                            have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl116 (v 2) (hv 2) hc a153
                            refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_021 v hv a133 a59 a57) fun a133 => ?_
                            have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) hc a133
                            have a61 : acc11_1 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 a133 hc
                            refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_120 v hv a61 a65 a138) fun a138 => ?_
                            refine (Classical.em (acc4_2 (v 2))).elim (fun a30 => succ4_102 v hv a25 a122 a30) fun a30 => ?_
                            have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl468 (v 2) (hv 2) a30 hc a138
                            refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_021 v hv a112 a41 a39) fun a112 => ?_
                            have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl360 (v 0) (hv 0) a112 hc a28
                            have a19 : acc3_1 (v 0) := Classical.byContradiction fun hc => cl461 (v 0) (hv 0) a28 hc a112
                            refine (Classical.em (acc3_2 (v 1))).elim (fun a23 => succ3_120 v hv a19 a23 a105) fun a23 => ?_
                            have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl435 (v 1) (hv 1) a23 a86 hc
                            refine (Classical.em (acc7_2 (v 2))).elim (fun a42 => succ7_102 v hv a37 a113 a42) fun a42 => ?_
                            refine (Classical.em (acc7_2 (v 0))).elim (fun a40 => succ7_201 v hv a40 a113 a39) fun a40 => ?_
                            have a34 : acc6_0 (v 0) := Classical.byContradiction fun hc => cl201 (v 0) (hv 0) hc a40
                            have a52 : acc9_2 (v 0) := Classical.byContradiction fun hc => cl454 (v 0) (hv 0) a19 hc a40
                            refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_210 v hv a52 a50 a117) fun a117 => ?_
                            have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) hc a117 a42
                            exact succ6_012 v hv a34 a128 a156
                        · have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl157 (v 0) (hv 0) hc a73
                          have a124 : acc5_1 (v 0) := Classical.byContradiction fun hc => cl193 (v 0) (hv 0) hc a73
                          have a127 : acc6_1 (v 0) := Classical.byContradiction fun hc => cl216 (v 0) (hv 0) hc a73
                          have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl243 (v 0) (hv 0) hc a73
                          have a58 : acc10_2 (v 0) := Classical.byContradiction fun hc => cl290 (v 0) (hv 0) hc a73
                          have a85 : ¬acc15_0 (v 0) := fun hc => cl316 (v 0) (hv 0) a73 hc
                          refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_201 v hv a58 a134 a57) fun a134 => ?_
                          refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_210 v hv a58 a56 a135) fun a135 => ?_
                          have a27 : acc4_1 (v 2) := Classical.byContradiction fun hc => cl163 (v 2) (hv 2) hc a135
                          refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_021 v hv a121 a29 a27) fun a29 => ?_
                          have a32 : acc5_0 (v 1) := Classical.byContradiction fun hc => cl167 (v 1) (hv 1) a29 hc
                          have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl414 (v 1) (hv 1) a29 a134 hc
                          refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_210 v hv a64 a62 a138) fun a138 => ?_
                          refine (Classical.em (acc5_2 (v 2))).elim (fun a153 => succ5_102 v hv a124 a32 a153) fun a153 => ?_
                          have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl116 (v 2) (hv 2) hc a153
                          have a26 : acc4_1 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) hc a134
                          refine (Classical.em (acc4_2 (v 2))).elim (fun a30 => succ4_012 v hv a121 a26 a30) fun a30 => ?_
                          have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl468 (v 2) (hv 2) a30 hc a138
                          refine (Classical.em (acc7_0 (v 1))).elim (fun a113 => succ7_201 v hv a40 a113 a39) fun a113 => ?_
                          have a38 : acc7_1 (v 1) := Classical.byContradiction fun hc => cl360 (v 1) (hv 1) a113 hc a29
                          have a20 : acc3_1 (v 1) := Classical.byContradiction fun hc => cl461 (v 1) (hv 1) a29 hc a113
                          refine (Classical.em (acc3_2 (v 0))).elim (fun a22 => succ3_210 v hv a22 a20 a105) fun a22 => ?_
                          have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl435 (v 0) (hv 0) a22 a85 hc
                          refine (Classical.em (acc7_2 (v 2))).elim (fun a42 => succ7_012 v hv a112 a38 a42) fun a42 => ?_
                          refine (Classical.em (acc7_2 (v 1))).elim (fun a41 => succ7_021 v hv a112 a41 a39) fun a41 => ?_
                          have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl201 (v 1) (hv 1) hc a41
                          have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl454 (v 1) (hv 1) a20 hc a41
                          refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_120 v hv a49 a53 a117) fun a117 => ?_
                          have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) hc a117 a42
                          exact succ6_102 v hv a127 a35 a156
                      · have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl230 (v 0) (hv 0) hc a67
                        have a115 : acc9_0 (v 0) := Classical.byContradiction fun hc => cl264 (v 0) (hv 0) hc a67
                        have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl291 (v 0) (hv 0) hc a67
                        have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl299 (v 0) (hv 0) a67 hc
                        have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl301 (v 0) (hv 0) a67 hc
                        have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl303 (v 0) (hv 0) a67 hc
                        have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl305 (v 0) (hv 0) a67 hc
                        have a97 : ¬acc17_0 (v 0) := fun hc => cl307 (v 0) (hv 0) a67 hc
                        have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl417 (v 0) (hv 0) a64 hc a97
                        refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_120 v hv a139 a71 a69) fun a71 => ?_
                        have a74 : acc13_0 (v 1) := Classical.byContradiction fun hc => cl312 (v 1) (hv 1) a71 hc
                        refine (Classical.em (acc13_1 (v 2))).elim (fun a78 => succ13_201 v hv a157 a74 a78) fun a78 => ?_
                        have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl323 (v 2) (hv 2) a78 hc
                        refine (Classical.em (acc14_1 (v 1))).elim (fun a83 => succ14_210 v hv a160 a83 a81) fun a83 => ?_
                        have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl443 (v 1) (hv 1) hc a146 a83
                        refine (Classical.em (acc15_2 (v 2))).elim (fun a90 => succ15_102 v hv a142 a86 a90) fun a90 => ?_
                        refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_201 v hv a88 a86 a144) fun a144 => ?_
                        have a63 : acc11_1 (v 2) := Classical.byContradiction fun hc => cl453 (v 2) (hv 2) a144 a90 hc
                        refine (Classical.em (acc11_2 (v 1))).elim (fun a65 => succ11_021 v hv a136 a65 a63) fun a65 => ?_
                        refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_201 v hv a64 a137 a63) fun a137 => ?_
                        have a38 : acc7_1 (v 1) := Classical.byContradiction fun hc => cl410 (v 1) (hv 1) a65 hc a137
                        have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl237 (v 1) (hv 1) a38 hc
                        refine (Classical.em (acc7_2 (v 2))).elim (fun a42 => succ7_012 v hv a112 a38 a42) fun a42 => ?_
                        refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_210 v hv a64 a62 a138) fun a138 => ?_
                        have a54 : acc9_2 (v 2) := Classical.byContradiction fun hc => cl466 (v 2) (hv 2) a42 hc a138
                        exact succ9_012 v hv a115 a50 a54
                    · have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl282 (v 2) (hv 2) a57 hc
                      have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl284 (v 2) (hv 2) a57 hc
                      have a75 : acc13_0 (v 2) := Classical.byContradiction fun hc => cl285 (v 2) (hv 2) a57 hc
                      have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl287 (v 2) (hv 2) a57 hc
                      refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_201 v hv a70 a68 a141) fun a70 => ?_
                      refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_210 v hv a64 a62 a138) fun a62 => ?_
                      have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl472 (v 1) (hv 1) a149 a62 hc
                      refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_021 v hv a85 a89 a144) fun a85 => ?_
                      have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                      have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 hc a70
                      refine (Classical.em (acc13_1 (v 1))).elim (fun a77 => succ13_210 v hv a157 a77 a75) fun a77 => ?_
                      have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl432 (v 1) (hv 1) hc a149 a77
                      refine (Classical.em (acc15_2 (v 0))).elim (fun a88 => succ15_201 v hv a88 a86 a144) fun a88 => ?_
                      exact (cl417 (v 0) (hv 0) a64 a88 a97).elim
                  · have a32 : acc5_0 (v 1) := Classical.byContradiction fun hc => cl176 (v 1) (hv 1) hc a50
                    have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl205 (v 1) (hv 1) hc a50
                    have a41 : ¬acc7_2 (v 1) := fun hc => cl242 (v 1) (hv 1) hc a50
                    have a65 : ¬acc11_2 (v 1) := fun hc => cl269 (v 1) (hv 1) a50 hc
                    have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl471 (v 1) (hv 1) a149 hc a50
                    have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) hc a109 a50
                    have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl255 (v 1) (hv 1) a47 hc
                    refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_021 v hv a130 a47 a45) fun a130 => ?_
                    refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                    have a129 : acc6_1 (v 2) := Classical.byContradiction fun hc => cl215 (v 2) (hv 2) hc a132
                    refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_201 v hv a154 a35 a129) fun a154 => ?_
                    have a127 : acc6_1 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) hc a130
                    refine (Classical.em (acc6_2 (v 2))).elim (fun a156 => succ6_102 v hv a127 a35 a156) fun a156 => ?_
                    have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl118 (v 2) (hv 2) hc a156
                    have a51 : acc9_1 (v 2) := Classical.byContradiction fun hc => cl403 (v 2) (hv 2) a156 a132 hc
                    refine (Classical.em (acc9_0 (v 0))).elim (fun a115 => succ9_021 v hv a115 a53 a51) fun a115 => ?_
                    have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl408 (v 0) (hv 0) a154 a115 hc
                    refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_120 v hv a49 a53 a117) fun a117 => ?_
                    have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) a156 a117 hc
                    refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_210 v hv a64 a62 a138) fun a138 => ?_
                    have a38 : acc7_1 (v 1) := Classical.byContradiction fun hc => cl411 (v 1) (hv 1) a116 a65 hc
                    refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_012 v hv a112 a38 a42) fun a112 => ?_
                    refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_210 v hv a40 a38 a114) fun a114 => ?_
                    have a126 : acc5_1 (v 2) := Classical.byContradiction fun hc => cl456 (v 2) (hv 2) a156 hc a114
                    refine (Classical.em (acc5_2 (v 0))).elim (fun a151 => succ5_201 v hv a151 a32 a126) fun a151 => ?_
                    have a22 : acc3_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) hc a112 a151
                    refine (Classical.em (acc3_1 (v 1))).elim (fun a20 => succ3_210 v hv a22 a20 a105) fun a20 => ?_
                    have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl349 (v 1) (hv 1) hc a41 a20
                    refine (Classical.em (acc7_1 (v 0))).elim (fun a37 => succ7_102 v hv a37 a113 a42) fun a37 => ?_
                    refine (Classical.em (acc7_1 (v 2))).elim (fun a39 => succ7_201 v hv a40 a113 a39) fun a39 => ?_
                    have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl149 (v 2) (hv 2) hc a39
                    have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl410 (v 2) (hv 2) hc a39 a138
                    refine (Classical.em (acc11_0 (v 0))).elim (fun a136 => succ11_012 v hv a136 a62 a66) fun a136 => ?_
                    have a28 : acc4_2 (v 0) := Classical.byContradiction fun hc => cl468 (v 0) (hv 0) hc a37 a136
                    refine (Classical.em (acc4_1 (v 1))).elim (fun a26 => succ4_210 v hv a28 a26 a123) fun a26 => ?_
                    exact (cl362 (v 1) (hv 1) a41 a116 a26).elim
                · have a135 : acc10_0 (v 2) := Classical.byContradiction fun hc => cl249 (v 2) (hv 2) a45 hc
                  have a60 : ¬acc10_2 (v 2) := fun hc => cl250 (v 2) (hv 2) a45 hc
                  have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl251 (v 2) (hv 2) a45 hc
                  have a75 : acc13_0 (v 2) := Classical.byContradiction fun hc => cl253 (v 2) (hv 2) a45 hc
                  refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_210 v hv a64 a62 a138) fun a62 => ?_
                  have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl472 (v 1) (hv 1) a149 a62 hc
                  have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl367 (v 1) (hv 1) a89 a149 hc
                  refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_120 v hv a61 a65 a138) fun a61 => ?_
                  refine (Classical.em (acc10_2 (v 0))).elim (fun a58 => succ10_210 v hv a58 a56 a135) fun a58 => ?_
                  have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl465 (v 0) (hv 0) a58 a61 hc
                  refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                  have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl371 (v 2) (hv 2) a60 hc a87
                  have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                  refine (Classical.em (acc12_2 (v 0))).elim (fun a70 => succ12_201 v hv a70 a68 a141) fun a70 => ?_
                  refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_021 v hv a85 a89 a144) fun a85 => ?_
                  have a97 : ¬acc17_0 (v 0) := fun hc => cl335 (v 0) (hv 0) a85 hc
                  have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl441 (v 0) (hv 0) a85 hc a70
                  refine (Classical.em (acc13_1 (v 1))).elim (fun a77 => succ13_210 v hv a157 a77 a75) fun a77 => ?_
                  have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl432 (v 1) (hv 1) hc a149 a77
                  refine (Classical.em (acc15_2 (v 0))).elim (fun a88 => succ15_201 v hv a88 a86 a144) fun a88 => ?_
                  exact (cl417 (v 0) (hv 0) a64 a88 a97).elim
              · have a32 : acc5_0 (v 1) := Classical.byContradiction fun hc => cl87 (v 1) (hv 1) a14 hc
                have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl88 (v 1) (hv 1) a14 hc
                have a41 : ¬acc7_2 (v 1) := fun hc => cl89 (v 1) (hv 1) a14 hc
                have a65 : ¬acc11_2 (v 1) := fun hc => cl92 (v 1) (hv 1) a14 hc
                have a89 : ¬acc15_2 (v 1) := fun hc => cl96 (v 1) (hv 1) a14 hc
                have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl474 (v 1) (hv 1) hc a14 a109
                have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl255 (v 1) (hv 1) a47 hc
                have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl257 (v 1) (hv 1) a47 hc
                refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                have a129 : acc6_1 (v 2) := Classical.byContradiction fun hc => cl215 (v 2) (hv 2) hc a132
                have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl244 (v 2) (hv 2) a132 hc
                refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_021 v hv a130 a47 a45) fun a130 => ?_
                have a127 : acc6_1 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) hc a130
                refine (Classical.em (acc6_2 (v 2))).elim (fun a156 => succ6_102 v hv a127 a35 a156) fun a156 => ?_
                have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl118 (v 2) (hv 2) hc a156
                have a51 : acc9_1 (v 2) := Classical.byContradiction fun hc => cl403 (v 2) (hv 2) a156 a132 hc
                refine (Classical.em (acc9_0 (v 0))).elim (fun a115 => succ9_021 v hv a115 a53 a51) fun a115 => ?_
                refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_201 v hv a154 a35 a129) fun a154 => ?_
                have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl408 (v 0) (hv 0) a154 a115 hc
                refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_210 v hv a64 a62 a138) fun a138 => ?_
                refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_120 v hv a49 a53 a117) fun a117 => ?_
                have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) a156 a117 hc
                have a26 : acc4_1 (v 1) := Classical.byContradiction fun hc => cl415 (v 1) (hv 1) a116 hc a89
                have a38 : acc7_1 (v 1) := Classical.byContradiction fun hc => cl411 (v 1) (hv 1) a116 a65 hc
                refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_012 v hv a112 a38 a42) fun a112 => ?_
                refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_210 v hv a40 a38 a114) fun a114 => ?_
                have a126 : acc5_1 (v 2) := Classical.byContradiction fun hc => cl456 (v 2) (hv 2) a156 hc a114
                refine (Classical.em (acc5_2 (v 0))).elim (fun a151 => succ5_201 v hv a151 a32 a126) fun a151 => ?_
                have a22 : acc3_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) hc a112 a151
                refine (Classical.em (acc3_1 (v 1))).elim (fun a20 => succ3_210 v hv a22 a20 a105) fun a20 => ?_
                have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl349 (v 1) (hv 1) hc a41 a20
                refine (Classical.em (acc7_1 (v 0))).elim (fun a37 => succ7_102 v hv a37 a113 a42) fun a37 => ?_
                refine (Classical.em (acc7_1 (v 2))).elim (fun a39 => succ7_201 v hv a40 a113 a39) fun a39 => ?_
                have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl149 (v 2) (hv 2) hc a39
                have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl410 (v 2) (hv 2) hc a39 a138
                refine (Classical.em (acc11_0 (v 0))).elim (fun a136 => succ11_012 v hv a136 a62 a66) fun a136 => ?_
                have a28 : acc4_2 (v 0) := Classical.byContradiction fun hc => cl468 (v 0) (hv 0) hc a37 a136
                exact succ4_210 v hv a28 a26 a123
          · have a111 : acc2_2 (v 2) := Classical.byContradiction fun hc => cl46 (v 2) (hv 2) a9 hc
            have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl65 (v 2) (hv 2) a9 hc
            have a75 : acc13_0 (v 2) := Classical.byContradiction fun hc => cl67 (v 2) (hv 2) a9 hc
            have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl68 (v 2) (hv 2) a9 hc
            have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl69 (v 2) (hv 2) a9 hc
            have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl72 (v 2) (hv 2) a9 hc
            have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl74 (v 2) (hv 2) a9 hc
            refine (Classical.em (acc2_1 (v 1))).elim (fun a17 => succ2_012 v hv a13 a17 a111) fun a17 => ?_
            have a95 : acc16_1 (v 1) := Classical.byContradiction fun hc => cl104 (v 1) (hv 1) a17 hc
            refine (Classical.em (acc16_0 (v 0))).elim (fun a91 => succ16_012 v hv a91 a95 a147) fun a91 => ?_
            have a82 : acc14_1 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) hc a91
            have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl338 (v 0) (hv 0) a91 hc
            refine (Classical.em (acc16_0 (v 1))).elim (fun a92 => succ16_102 v hv a94 a92 a147) fun a92 => ?_
            have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) hc a92
            refine (Classical.em (acc14_2 (v 0))).elim (fun a160 => succ14_210 v hv a160 a83 a81) fun a160 => ?_
            have a67 : acc12_0 (v 0) := Classical.byContradiction fun hc => cl303 (v 0) (hv 0) hc a160
            have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl385 (v 0) (hv 0) a160 hc a91
            refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_102 v hv a100 a98 a150) fun a98 => ?_
            refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_021 v hv a67 a71 a141) fun a71 => ?_
            refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_120 v hv a82 a161 a81) fun a161 => ?_
            have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) a161 hc a98
            have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl385 (v 1) (hv 1) a161 hc a92
            refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_012 v hv a97 a101 a150) fun a97 => ?_
            have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl373 (v 0) (hv 0) a160 hc a97
            refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_201 v hv a88 a86 a144) fun a86 => ?_
            have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 hc a71
            refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_120 v hv a76 a158 a75) fun a76 => ?_
            have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) hc a160 a76
            exact succ15_021 v hv a85 a89 a144
        · have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl46 (v 1) (hv 1) a8 hc
          have a140 : acc12_1 (v 1) := Classical.byContradiction fun hc => cl65 (v 1) (hv 1) a8 hc
          have a74 : acc13_0 (v 1) := Classical.byContradiction fun hc => cl67 (v 1) (hv 1) a8 hc
          have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl68 (v 1) (hv 1) a8 hc
          have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl69 (v 1) (hv 1) a8 hc
          have a146 : acc16_2 (v 1) := Classical.byContradiction fun hc => cl72 (v 1) (hv 1) a8 hc
          have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl74 (v 1) (hv 1) a8 hc
          refine (Classical.em (acc2_1 (v 2))).elim (fun a18 => succ2_021 v hv a13 a109 a18) fun a18 => ?_
          have a96 : acc16_1 (v 2) := Classical.byContradiction fun hc => cl104 (v 2) (hv 2) a18 hc
          refine (Classical.em (acc16_0 (v 0))).elim (fun a91 => succ16_021 v hv a91 a146 a96) fun a91 => ?_
          have a82 : acc14_1 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) hc a91
          have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl338 (v 0) (hv 0) a91 hc
          refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_120 v hv a94 a146 a93) fun a93 => ?_
          have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl332 (v 2) (hv 2) hc a93
          refine (Classical.em (acc14_2 (v 0))).elim (fun a160 => succ14_201 v hv a160 a80 a84) fun a160 => ?_
          have a67 : acc12_0 (v 0) := Classical.byContradiction fun hc => cl303 (v 0) (hv 0) hc a160
          have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl385 (v 0) (hv 0) a160 hc a91
          refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_120 v hv a100 a149 a99) fun a99 => ?_
          refine (Classical.em (acc12_2 (v 2))).elim (fun a72 => succ12_012 v hv a67 a140 a72) fun a72 => ?_
          refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_102 v hv a82 a80 a162) fun a162 => ?_
          have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) a162 hc a99
          have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl385 (v 2) (hv 2) a162 hc a93
          refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_021 v hv a97 a149 a102) fun a97 => ?_
          have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl373 (v 0) (hv 0) a160 hc a97
          refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_210 v hv a88 a143 a87) fun a87 => ?_
          have a159 : acc13_2 (v 2) := Classical.byContradiction fun hc => cl441 (v 2) (hv 2) a87 hc a72
          refine (Classical.em (acc13_1 (v 0))).elim (fun a76 => succ13_102 v hv a76 a74 a159) fun a76 => ?_
          have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) hc a160 a76
          exact succ15_012 v hv a85 a143 a90
      · have a21 : acc3_1 (v 2) := Classical.byContradiction fun hc => cl5 (v 2) (hv 2) a5 hc
        have a33 : acc5_0 (v 2) := Classical.byContradiction fun hc => cl9 (v 2) (hv 2) a5 hc
        have a36 : acc6_0 (v 2) := Classical.byContradiction fun hc => cl10 (v 2) (hv 2) a5 hc
        have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl11 (v 2) (hv 2) a5 hc
        have a42 : ¬acc7_2 (v 2) := fun hc => cl12 (v 2) (hv 2) a5 hc
        have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl14 (v 2) (hv 2) a5 hc
        have a54 : acc9_2 (v 2) := Classical.byContradiction fun hc => cl16 (v 2) (hv 2) a5 hc
        have a63 : acc11_1 (v 2) := Classical.byContradiction fun hc => cl19 (v 2) (hv 2) a5 hc
        refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_201 v hv a64 a137 a63) fun a137 => ?_
        have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl251 (v 1) (hv 1) hc a137
        refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_012 v hv a130 a44 a48) fun a130 => ?_
        have a127 : acc6_1 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) hc a130
        refine (Classical.em (acc6_2 (v 1))).elim (fun a155 => succ6_120 v hv a127 a155 a36) fun a155 => ?_
        have a104 : acc3_0 (v 1) := Classical.byContradiction fun hc => cl118 (v 1) (hv 1) hc a155
        refine (Classical.em (acc3_2 (v 0))).elim (fun a22 => succ3_201 v hv a22 a104 a21) fun a22 => ?_
        refine (Classical.em (acc9_0 (v 1))).elim (fun a116 => succ9_102 v hv a49 a116 a54) fun a116 => ?_
        have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl408 (v 1) (hv 1) a155 a116 hc
        have a50 : acc9_1 (v 1) := Classical.byContradiction fun hc => cl242 (v 1) (hv 1) a41 hc
        refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_021 v hv a112 a41 a39) fun a112 => ?_
        have a151 : acc5_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) a22 a112 hc
        refine (Classical.em (acc5_1 (v 1))).elim (fun a125 => succ5_210 v hv a151 a125 a33) fun a125 => ?_
        have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl192 (v 1) (hv 1) a125 hc
        have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl456 (v 1) (hv 1) a155 a125 hc
        refine (Classical.em (acc7_2 (v 0))).elim (fun a40 => succ7_201 v hv a40 a113 a39) fun a40 => ?_
        have a19 : acc3_1 (v 0) := Classical.byContradiction fun hc => cl349 (v 0) (hv 0) a112 a40 hc
        have a52 : acc9_2 (v 0) := Classical.byContradiction fun hc => cl454 (v 0) (hv 0) a19 hc a40
        refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_210 v hv a52 a50 a117) fun a117 => ?_
        have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) hc a117 a42
        exact succ6_102 v hv a127 a35 a156
    · have a20 : acc3_1 (v 1) := Classical.byContradiction fun hc => cl5 (v 1) (hv 1) a3 hc
      have a32 : acc5_0 (v 1) := Classical.byContradiction fun hc => cl9 (v 1) (hv 1) a3 hc
      have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl10 (v 1) (hv 1) a3 hc
      have a38 : acc7_1 (v 1) := Classical.byContradiction fun hc => cl11 (v 1) (hv 1) a3 hc
      have a41 : ¬acc7_2 (v 1) := fun hc => cl12 (v 1) (hv 1) a3 hc
      have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl14 (v 1) (hv 1) a3 hc
      have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl16 (v 1) (hv 1) a3 hc
      have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl19 (v 1) (hv 1) a3 hc
      refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_210 v hv a64 a62 a138) fun a138 => ?_
      have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl251 (v 2) (hv 2) hc a138
      refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_021 v hv a130 a47 a45) fun a130 => ?_
      have a127 : acc6_1 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) hc a130
      refine (Classical.em (acc6_2 (v 2))).elim (fun a156 => succ6_102 v hv a127 a35 a156) fun a156 => ?_
      have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl118 (v 2) (hv 2) hc a156
      refine (Classical.em (acc3_2 (v 0))).elim (fun a22 => succ3_210 v hv a22 a20 a105) fun a22 => ?_
      refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_120 v hv a49 a53 a117) fun a117 => ?_
      have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) a156 a117 hc
      have a51 : acc9_1 (v 2) := Classical.byContradiction fun hc => cl242 (v 2) (hv 2) a42 hc
      refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_012 v hv a112 a38 a42) fun a112 => ?_
      have a151 : acc5_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) a22 a112 hc
      refine (Classical.em (acc5_1 (v 2))).elim (fun a126 => succ5_201 v hv a151 a32 a126) fun a126 => ?_
      have a36 : acc6_0 (v 2) := Classical.byContradiction fun hc => cl192 (v 2) (hv 2) a126 hc
      have a114 : acc7_0 (v 2) := Classical.byContradiction fun hc => cl456 (v 2) (hv 2) a156 a126 hc
      refine (Classical.em (acc7_2 (v 0))).elim (fun a40 => succ7_210 v hv a40 a38 a114) fun a40 => ?_
      have a19 : acc3_1 (v 0) := Classical.byContradiction fun hc => cl349 (v 0) (hv 0) a112 a40 hc
      have a52 : acc9_2 (v 0) := Classical.byContradiction fun hc => cl454 (v 0) (hv 0) a19 hc a40
      refine (Classical.em (acc9_0 (v 1))).elim (fun a116 => succ9_201 v hv a52 a116 a51) fun a116 => ?_
      have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl408 (v 1) (hv 1) hc a116 a41
      exact succ6_120 v hv a127 a155 a36
  · have a28 : ¬acc4_2 (v 0) := fun hc => cl166 (v 0) (hv 0) hc a64
    have a31 : acc5_0 (v 0) := Classical.byContradiction fun hc => cl179 (v 0) (hv 0) hc a64
    have a58 : ¬acc10_2 (v 0) := fun hc => cl289 (v 0) (hv 0) hc a64
    have a73 : acc13_0 (v 0) := Classical.byContradiction fun hc => cl297 (v 0) (hv 0) a64 hc
    have a79 : acc14_0 (v 0) := Classical.byContradiction fun hc => cl298 (v 0) (hv 0) a64 hc
    by_cases a32 : acc5_0 (v 1)
    · by_cases a33 : acc5_0 (v 2)
      · by_cases a68 : acc12_0 (v 1)
        · by_cases a67 : acc12_0 (v 0)
          · by_cases a69 : acc12_0 (v 2)
            · by_cases a74 : acc13_0 (v 1)
              · by_cases a75 : acc13_0 (v 2)
                · by_cases a103 : acc3_0 (v 0)
                  · by_cases a104 : acc3_0 (v 1)
                    · by_cases a105 : acc3_0 (v 2)
                      · by_cases a52 : acc9_2 (v 0)
                        · have a55 : acc10_1 (v 0) := Classical.byContradiction fun hc => cl272 (v 0) (hv 0) a52 hc
                          have a61 : acc11_1 (v 0) := Classical.byContradiction fun hc => cl273 (v 0) (hv 0) a52 hc
                          have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl277 (v 0) (hv 0) a52 hc
                          have a97 : acc17_0 (v 0) := Classical.byContradiction fun hc => cl278 (v 0) (hv 0) a52 hc
                          by_cases a23 : acc3_2 (v 1)
                          · have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl143 (v 1) (hv 1) a23 hc
                            have a50 : acc9_1 (v 1) := Classical.byContradiction fun hc => cl145 (v 1) (hv 1) a23 hc
                            refine (Classical.em (acc3_1 (v 0))).elim (fun a19 => succ3_120 v hv a19 a23 a105) fun a19 => ?_
                            have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl461 (v 0) (hv 0) a28 a19 hc
                            refine (Classical.em (acc7_1 (v 2))).elim (fun a39 => succ7_021 v hv a112 a41 a39) fun a39 => ?_
                            have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl149 (v 2) (hv 2) hc a39
                            refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_210 v hv a52 a50 a117) fun a117 => ?_
                            have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl406 (v 2) (hv 2) a117 a39 hc
                            have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl411 (v 2) (hv 2) a117 hc a39
                            refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_102 v hv a61 a137 a66) fun a137 => ?_
                            have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl282 (v 1) (hv 1) hc a137
                            have a143 : ¬acc15_1 (v 1) := fun hc => cl293 (v 1) (hv 1) a137 hc
                            refine (Classical.em (acc7_1 (v 1))).elim (fun a38 => succ7_012 v hv a112 a38 a42) fun a38 => ?_
                            have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl410 (v 1) (hv 1) hc a38 a137
                            have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl468 (v 1) (hv 1) hc a38 a137
                            refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_120 v hv a25 a29 a123) fun a25 => ?_
                            have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                            have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl365 (v 0) (hv 0) a58 hc a25
                            refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                            refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_021 v hv a136 a65 a63) fun a63 => ?_
                            have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl453 (v 1) (hv 1) a143 hc a62
                            refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                            have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl465 (v 2) (hv 2) hc a63 a144
                            exact succ10_012 v hv a133 a56 a60
                          · by_cases a24 : acc3_2 (v 2)
                            · have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl143 (v 2) (hv 2) a24 hc
                              have a51 : acc9_1 (v 2) := Classical.byContradiction fun hc => cl145 (v 2) (hv 2) a24 hc
                              refine (Classical.em (acc3_1 (v 0))).elim (fun a19 => succ3_102 v hv a19 a104 a24) fun a19 => ?_
                              have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl142 (v 0) (hv 0) a19 hc
                              have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl461 (v 0) (hv 0) a28 a19 hc
                              refine (Classical.em (acc7_1 (v 1))).elim (fun a38 => succ7_012 v hv a112 a38 a42) fun a38 => ?_
                              have a152 : ¬acc5_2 (v 1) := fun hc => cl194 (v 1) (hv 1) hc a38
                              have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) a23 hc a152
                              refine (Classical.em (acc7_1 (v 0))).elim (fun a37 => succ7_102 v hv a37 a113 a42) fun a37 => ?_
                              have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl410 (v 0) (hv 0) a64 a37 hc
                              refine (Classical.em (acc9_0 (v 1))).elim (fun a116 => succ9_201 v hv a52 a116 a51) fun a116 => ?_
                              have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl411 (v 1) (hv 1) a116 hc a38
                              refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_021 v hv a136 a65 a63) fun a63 => ?_
                              refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_120 v hv a61 a65 a138) fun a138 => ?_
                              have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl364 (v 2) (hv 2) hc a138 a63
                              refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_102 v hv a55 a134 a60) fun a134 => ?_
                              have a26 : acc4_1 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) hc a134
                              refine (Classical.em (acc4_2 (v 2))).elim (fun a30 => succ4_012 v hv a121 a26 a30) fun a30 => ?_
                              have a135 : acc10_0 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) a30 hc a63
                              exact (cl467 (v 2) (hv 2) a135 a30 a138).elim
                            · by_cases a34 : acc6_0 (v 0)
                              · by_cases a35 : acc6_0 (v 1)
                                · by_cases a36 : acc6_0 (v 2)
                                  · by_cases a116 : acc9_0 (v 1)
                                    · have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl227 (v 1) (hv 1) hc a116
                                      refine (Classical.em (acc9_1 (v 2))).elim (fun a51 => succ9_201 v hv a52 a116 a51) fun a51 => ?_
                                      have a42 : ¬acc7_2 (v 2) := fun hc => cl242 (v 2) (hv 2) hc a51
                                      have a60 : ¬acc10_2 (v 2) := fun hc => cl268 (v 2) (hv 2) a51 hc
                                      have a66 : ¬acc11_2 (v 2) := fun hc => cl269 (v 2) (hv 2) a51 hc
                                      have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl271 (v 2) (hv 2) a51 hc
                                      by_cases a22 : acc3_2 (v 0)
                                      · have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl85 (v 0) (hv 0) hc a22
                                        have a49 : acc9_1 (v 0) := Classical.byContradiction fun hc => cl145 (v 0) (hv 0) a22 hc
                                        refine (Classical.em (acc9_2 (v 2))).elim (fun a54 => succ9_102 v hv a49 a116 a54) fun a54 => ?_
                                        have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 a66 hc
                                        have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl466 (v 2) (hv 2) a42 a54 hc
                                        refine (Classical.em (acc11_2 (v 1))).elim (fun a65 => succ11_120 v hv a61 a65 a138) fun a65 => ?_
                                        have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl298 (v 1) (hv 1) a65 hc
                                        have a117 : acc9_0 (v 2) := Classical.byContradiction fun hc => cl267 (v 2) (hv 2) hc a150
                                        refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_012 v hv a97 a101 a150) fun a101 => ?_
                                        have a89 : ¬acc15_2 (v 1) := fun hc => cl337 (v 1) (hv 1) hc a101
                                        refine (Classical.em (acc9_2 (v 1))).elim (fun a53 => succ9_120 v hv a49 a53 a117) fun a53 => ?_
                                        have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl376 (v 1) (hv 1) hc a53 a101
                                        refine (Classical.em (acc2_1 (v 2))).elim (fun a18 => succ2_021 v hv a13 a109 a18) fun a18 => ?_
                                        have a96 : acc16_1 (v 2) := Classical.byContradiction fun hc => cl104 (v 2) (hv 2) a18 hc
                                        have a111 : acc2_2 (v 2) := Classical.byContradiction fun hc => cl375 (v 2) (hv 2) hc a18 a51
                                        refine (Classical.em (acc2_1 (v 1))).elim (fun a17 => succ2_012 v hv a13 a17 a111) fun a17 => ?_
                                        have a146 : acc16_2 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) hc a17 a101
                                        refine (Classical.em (acc16_0 (v 0))).elim (fun a91 => succ16_021 v hv a91 a146 a96) fun a91 => ?_
                                        have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl338 (v 0) (hv 0) a91 hc
                                        refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_120 v hv a94 a146 a93) fun a93 => ?_
                                        have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl332 (v 2) (hv 2) hc a93
                                        refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_021 v hv a79 a161 a84) fun a161 => ?_
                                        refine (Classical.em (acc14_2 (v 0))).elim (fun a160 => succ14_201 v hv a160 a80 a84) fun a160 => ?_
                                        have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl385 (v 0) (hv 0) a160 hc a91
                                        refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_102 v hv a100 a98 a150) fun a98 => ?_
                                        exact (cl373 (v 1) (hv 1) a161 a89 a98).elim
                                      · by_cases a29 : acc4_2 (v 1)
                                        · have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl86 (v 1) (hv 1) hc a29
                                          have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl164 (v 1) (hv 1) a29 hc
                                          have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl166 (v 1) (hv 1) a29 hc
                                          refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_120 v hv a61 a65 a138) fun a138 => ?_
                                          have a54 : acc9_2 (v 2) := Classical.byContradiction fun hc => cl466 (v 2) (hv 2) a42 hc a138
                                          have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl478 (v 2) (hv 2) a51 a138 hc
                                          refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_201 v hv a107 a14 a18) fun a107 => ?_
                                          refine (Classical.em (acc9_1 (v 0))).elim (fun a49 => succ9_102 v hv a49 a116 a54) fun a49 => ?_
                                          have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl475 (v 0) (hv 0) hc a107 a49
                                          refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                          have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl355 (v 2) (hv 2) hc a51 a132
                                          have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl403 (v 2) (hv 2) hc a132 a51
                                          refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                          have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                          exact succ8_012 v hv a130 a44 a48
                                        · by_cases a40 : acc7_2 (v 0)
                                          · have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl89 (v 0) (hv 0) hc a40
                                            have a49 : acc9_1 (v 0) := Classical.byContradiction fun hc => cl242 (v 0) (hv 0) a40 hc
                                            refine (Classical.em (acc7_1 (v 2))).elim (fun a39 => succ7_201 v hv a40 a113 a39) fun a39 => ?_
                                            have a117 : acc9_0 (v 2) := Classical.byContradiction fun hc => cl406 (v 2) (hv 2) hc a39 a42
                                            have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl410 (v 2) (hv 2) a66 a39 hc
                                            refine (Classical.em (acc11_2 (v 1))).elim (fun a65 => succ11_120 v hv a61 a65 a138) fun a65 => ?_
                                            have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl298 (v 1) (hv 1) a65 hc
                                            refine (Classical.em (acc9_2 (v 1))).elim (fun a53 => succ9_120 v hv a49 a53 a117) fun a53 => ?_
                                            refine (Classical.em (acc9_1 (v 1))).elim (fun a50 => succ9_210 v hv a52 a50 a117) fun a50 => ?_
                                            have a47 : ¬acc8_2 (v 1) := fun hc => cl255 (v 1) (hv 1) hc a53
                                            have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl342 (v 1) (hv 1) a53 a65 hc
                                            refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_021 v hv a97 a149 a102) fun a102 => ?_
                                            have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) a47 hc a50
                                            refine (Classical.em (acc2_1 (v 2))).elim (fun a18 => succ2_021 v hv a13 a109 a18) fun a18 => ?_
                                            have a96 : acc16_1 (v 2) := Classical.byContradiction fun hc => cl104 (v 2) (hv 2) a18 hc
                                            have a111 : acc2_2 (v 2) := Classical.byContradiction fun hc => cl375 (v 2) (hv 2) hc a18 a51
                                            have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl479 (v 2) (hv 2) a51 a18 hc
                                            refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_012 v hv a97 a101 a150) fun a101 => ?_
                                            refine (Classical.em (acc2_1 (v 1))).elim (fun a17 => succ2_012 v hv a13 a17 a111) fun a17 => ?_
                                            have a146 : acc16_2 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) hc a17 a101
                                            refine (Classical.em (acc16_0 (v 0))).elim (fun a91 => succ16_021 v hv a91 a146 a96) fun a91 => ?_
                                            have a82 : acc14_1 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) hc a91
                                            have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl338 (v 0) (hv 0) a91 hc
                                            refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_120 v hv a94 a146 a93) fun a93 => ?_
                                            have a162 : acc14_2 (v 2) := Classical.byContradiction fun hc => cl385 (v 2) (hv 2) hc a102 a93
                                            exact succ14_102 v hv a82 a80 a162
                                          · by_cases a41 : acc7_2 (v 1)
                                            · have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl241 (v 1) (hv 1) a41 hc
                                              have a50 : acc9_1 (v 1) := Classical.byContradiction fun hc => cl242 (v 1) (hv 1) a41 hc
                                              refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_210 v hv a52 a50 a117) fun a117 => ?_
                                              have a111 : ¬acc2_2 (v 2) := fun hc => cl109 (v 2) (hv 2) hc a117
                                              have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) hc a117 a42
                                              refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                              have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                              refine (Classical.em (acc8_2 (v 2))).elim (fun a48 => succ8_012 v hv a130 a44 a48) fun a48 => ?_
                                              exact (cl475 (v 2) (hv 2) a48 a111 a51).elim
                                            · by_cases a49 : acc9_1 (v 0)
                                              · have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl90 (v 0) (hv 0) hc a49
                                                refine (Classical.em (acc9_2 (v 2))).elim (fun a54 => succ9_102 v hv a49 a116 a54) fun a54 => ?_
                                                have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 a66 hc
                                                have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl466 (v 2) (hv 2) a42 a54 hc
                                                refine (Classical.em (acc11_2 (v 1))).elim (fun a65 => succ11_120 v hv a61 a65 a138) fun a65 => ?_
                                                have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl298 (v 1) (hv 1) a65 hc
                                                have a117 : acc9_0 (v 2) := Classical.byContradiction fun hc => cl267 (v 2) (hv 2) hc a150
                                                refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_012 v hv a97 a101 a150) fun a101 => ?_
                                                have a89 : ¬acc15_2 (v 1) := fun hc => cl337 (v 1) (hv 1) hc a101
                                                refine (Classical.em (acc9_2 (v 1))).elim (fun a53 => succ9_120 v hv a49 a53 a117) fun a53 => ?_
                                                have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl376 (v 1) (hv 1) hc a53 a101
                                                refine (Classical.em (acc2_1 (v 2))).elim (fun a18 => succ2_021 v hv a13 a109 a18) fun a18 => ?_
                                                have a96 : acc16_1 (v 2) := Classical.byContradiction fun hc => cl104 (v 2) (hv 2) a18 hc
                                                have a111 : acc2_2 (v 2) := Classical.byContradiction fun hc => cl375 (v 2) (hv 2) hc a18 a51
                                                refine (Classical.em (acc2_1 (v 1))).elim (fun a17 => succ2_012 v hv a13 a17 a111) fun a17 => ?_
                                                have a146 : acc16_2 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) hc a17 a101
                                                refine (Classical.em (acc16_0 (v 0))).elim (fun a91 => succ16_021 v hv a91 a146 a96) fun a91 => ?_
                                                have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl338 (v 0) (hv 0) a91 hc
                                                refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_120 v hv a94 a146 a93) fun a93 => ?_
                                                have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl332 (v 2) (hv 2) hc a93
                                                refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_021 v hv a79 a161 a84) fun a161 => ?_
                                                refine (Classical.em (acc14_2 (v 0))).elim (fun a160 => succ14_201 v hv a160 a80 a84) fun a160 => ?_
                                                have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl385 (v 0) (hv 0) a160 hc a91
                                                refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_102 v hv a100 a98 a150) fun a98 => ?_
                                                exact (cl373 (v 1) (hv 1) a161 a89 a98).elim
                                              · by_cases a50 : acc9_1 (v 1)
                                                · have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl248 (v 1) (hv 1) hc a50
                                                  refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_210 v hv a52 a50 a117) fun a117 => ?_
                                                  have a111 : ¬acc2_2 (v 2) := fun hc => cl109 (v 2) (hv 2) hc a117
                                                  have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) hc a117 a42
                                                  refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                                  have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                  refine (Classical.em (acc8_2 (v 2))).elim (fun a48 => succ8_012 v hv a130 a44 a48) fun a48 => ?_
                                                  exact (cl475 (v 2) (hv 2) a48 a111 a51).elim
                                                · have a59 : ¬acc10_2 (v 1) := fun hc => cl268 (v 1) (hv 1) a50 hc
                                                  have a65 : ¬acc11_2 (v 1) := fun hc => cl269 (v 1) (hv 1) a50 hc
                                                  have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl271 (v 1) (hv 1) a50 hc
                                                  by_cases a70 : acc12_2 (v 0)
                                                  · have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl93 (v 0) (hv 0) hc a70
                                                    have a88 : acc15_2 (v 0) := Classical.byContradiction fun hc => cl309 (v 0) (hv 0) a70 hc
                                                    have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl311 (v 0) (hv 0) a70 hc
                                                    refine (Classical.em (acc12_1 (v 1))).elim (fun a140 => succ12_210 v hv a70 a140 a69) fun a140 => ?_
                                                    have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl464 (v 1) (hv 1) a59 a140 hc
                                                    refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_201 v hv a88 a86 a144) fun a144 => ?_
                                                    have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl477 (v 2) (hv 2) a66 a144 hc
                                                    refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_120 v hv a100 a149 a99) fun a149 => ?_
                                                    have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl479 (v 1) (hv 1) a50 hc a149
                                                    refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_012 v hv a13 a17 a111) fun a111 => ?_
                                                    have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl110 (v 2) (hv 2) a111 hc
                                                    have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl375 (v 2) (hv 2) a111 hc a51
                                                    have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) hc a111 a51
                                                    refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_021 v hv a13 a109 a18) fun a109 => ?_
                                                    have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) hc a109 a50
                                                    refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_021 v hv a130 a47 a45) fun a130 => ?_
                                                    have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl244 (v 0) (hv 0) a130 hc
                                                    have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl403 (v 0) (hv 0) hc a130 a49
                                                    refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_210 v hv a154 a128 a36) fun a128 => ?_
                                                    have a131 : acc8_0 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) a128 hc
                                                    exact succ8_102 v hv a43 a131 a48
                                                  · by_cases a71 : acc12_2 (v 1)
                                                    · have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl93 (v 1) (hv 1) hc a71
                                                      have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl311 (v 1) (hv 1) a71 hc
                                                      refine (Classical.em (acc17_2 (v 2))).elim (fun a150 => succ17_012 v hv a97 a101 a150) fun a150 => ?_
                                                      have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl479 (v 2) (hv 2) a51 hc a150
                                                      refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_201 v hv a107 a14 a18) fun a107 => ?_
                                                      have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl110 (v 0) (hv 0) a107 hc
                                                      have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl375 (v 0) (hv 0) a107 hc a49
                                                      refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_102 v hv a16 a14 a111) fun a111 => ?_
                                                      have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) hc a111 a51
                                                      refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_102 v hv a43 a131 a48) fun a131 => ?_
                                                      have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl244 (v 1) (hv 1) a131 hc
                                                      have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl403 (v 1) (hv 1) hc a131 a50
                                                      refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                      have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                      exact succ8_012 v hv a130 a44 a48
                                                    · by_cases a72 : acc12_2 (v 2)
                                                      · have a15 : acc2_0 (v 2) := Classical.byContradiction fun hc => cl93 (v 2) (hv 2) hc a72
                                                        have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl311 (v 2) (hv 2) a72 hc
                                                        refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_021 v hv a97 a149 a102) fun a149 => ?_
                                                        have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl479 (v 1) (hv 1) a50 hc a149
                                                        refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_210 v hv a107 a17 a15) fun a107 => ?_
                                                        have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl110 (v 0) (hv 0) a107 hc
                                                        have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl375 (v 0) (hv 0) a107 hc a49
                                                        refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_120 v hv a16 a109 a15) fun a109 => ?_
                                                        have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl110 (v 1) (hv 1) a109 hc
                                                        have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) hc a109 a50
                                                        refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                                        have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl355 (v 2) (hv 2) hc a51 a132
                                                        have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl403 (v 2) (hv 2) hc a132 a51
                                                        refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                                        have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                        exact succ8_012 v hv a130 a44 a48
                                                      · by_cases a89 : acc15_2 (v 1)
                                                        · have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl96 (v 1) (hv 1) hc a89
                                                          have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl337 (v 1) (hv 1) a89 hc
                                                          have a128 : ¬acc6_1 (v 1) := fun hc => cl439 (v 1) (hv 1) hc a89 a50
                                                          refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                                                          have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl477 (v 2) (hv 2) a66 a144 hc
                                                          refine (Classical.em (acc17_2 (v 0))).elim (fun a148 => succ17_210 v hv a148 a101 a99) fun a148 => ?_
                                                          have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl479 (v 0) (hv 0) a49 hc a148
                                                          refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_102 v hv a16 a14 a111) fun a111 => ?_
                                                          have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl110 (v 2) (hv 2) a111 hc
                                                          have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl375 (v 2) (hv 2) a111 hc a51
                                                          refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_201 v hv a107 a14 a18) fun a107 => ?_
                                                          have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl475 (v 0) (hv 0) hc a107 a49
                                                          refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_201 v hv a46 a131 a45) fun a131 => ?_
                                                          exact (cl215 (v 1) (hv 1) a128 a131).elim
                                                        · by_cases a86 : acc15_0 (v 1)
                                                          · by_cases a88 : acc15_2 (v 0)
                                                            · have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl96 (v 0) (hv 0) hc a88
                                                              have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl336 (v 0) (hv 0) a88 hc
                                                              have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl337 (v 0) (hv 0) a88 hc
                                                              have a148 : acc17_2 (v 0) := Classical.byContradiction fun hc => cl367 (v 0) (hv 0) a88 hc a64
                                                              have a127 : ¬acc6_1 (v 0) := fun hc => cl439 (v 0) (hv 0) hc a88 a49
                                                              refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_201 v hv a88 a86 a144) fun a144 => ?_
                                                              have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl477 (v 2) (hv 2) a66 a144 hc
                                                              refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_120 v hv a100 a149 a99) fun a149 => ?_
                                                              refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_210 v hv a148 a101 a99) fun a101 => ?_
                                                              have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl388 (v 1) (hv 1) hc a101 a149
                                                              have a83 : ¬acc14_1 (v 1) := fun hc => cl392 (v 1) (hv 1) hc a101 a149
                                                              have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) a83 hc
                                                              refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_102 v hv a94 a92 a147) fun a147 => ?_
                                                              have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl278 (v 1) (hv 1) a53 hc
                                                              refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_201 v hv a148 a98 a102) fun a102 => ?_
                                                              have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) a147 hc a102
                                                              have a93 : acc16_0 (v 2) := Classical.byContradiction fun hc => cl384 (v 2) (hv 2) a147 a102 hc
                                                              refine (Classical.em (acc16_2 (v 1))).elim (fun a146 => succ16_120 v hv a94 a146 a93) fun a146 => ?_
                                                              have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) a146 hc a101
                                                              refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_012 v hv a13 a17 a111) fun a111 => ?_
                                                              have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl110 (v 2) (hv 2) a111 hc
                                                              refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_021 v hv a13 a109 a18) fun a109 => ?_
                                                              have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) hc a109 a50
                                                              refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_021 v hv a130 a47 a45) fun a130 => ?_
                                                              exact (cl215 (v 0) (hv 0) a127 a130).elim
                                                            · by_cases a90 : acc15_2 (v 2)
                                                              · have a15 : acc2_0 (v 2) := Classical.byContradiction fun hc => cl96 (v 2) (hv 2) hc a90
                                                                have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl337 (v 2) (hv 2) a90 hc
                                                                have a129 : ¬acc6_1 (v 2) := fun hc => cl439 (v 2) (hv 2) hc a90 a51
                                                                refine (Classical.em (acc15_1 (v 1))).elim (fun a143 => succ15_012 v hv a85 a143 a90) fun a143 => ?_
                                                                have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl477 (v 1) (hv 1) a65 a143 hc
                                                                refine (Classical.em (acc17_2 (v 0))).elim (fun a148 => succ17_201 v hv a148 a98 a102) fun a148 => ?_
                                                                have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl479 (v 0) (hv 0) a49 hc a148
                                                                refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_120 v hv a16 a109 a15) fun a109 => ?_
                                                                have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl110 (v 1) (hv 1) a109 hc
                                                                have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl375 (v 1) (hv 1) a109 hc a50
                                                                refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_210 v hv a107 a17 a15) fun a107 => ?_
                                                                have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl475 (v 0) (hv 0) hc a107 a49
                                                                refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                exact (cl215 (v 2) (hv 2) a129 a132).elim
                                                              · by_cases a87 : acc15_0 (v 2)
                                                                · by_cases a98 : acc17_0 (v 1)
                                                                  · by_cases a99 : acc17_0 (v 2)
                                                                    · by_cases a100 : acc17_1 (v 0)
                                                                      · have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl97 (v 0) (hv 0) hc a100
                                                                        refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_120 v hv a100 a149 a99) fun a149 => ?_
                                                                        have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl479 (v 1) (hv 1) a50 hc a149
                                                                        refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_012 v hv a13 a17 a111) fun a111 => ?_
                                                                        have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl110 (v 2) (hv 2) a111 hc
                                                                        have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl375 (v 2) (hv 2) a111 hc a51
                                                                        have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) hc a111 a51
                                                                        refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_021 v hv a13 a109 a18) fun a109 => ?_
                                                                        have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) hc a109 a50
                                                                        refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_021 v hv a130 a47 a45) fun a130 => ?_
                                                                        have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl244 (v 0) (hv 0) a130 hc
                                                                        have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl403 (v 0) (hv 0) hc a130 a49
                                                                        refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_210 v hv a154 a128 a36) fun a128 => ?_
                                                                        have a131 : acc8_0 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) a128 hc
                                                                        exact succ8_102 v hv a43 a131 a48
                                                                      · by_cases a91 : acc16_0 (v 0)
                                                                        · by_cases a8 : acc1_0 (v 1)
                                                                          · by_cases a1 : acc0_0 (v 0)
                                                                            · by_cases a3 : acc0_0 (v 1)
                                                                              · by_cases a5 : acc0_0 (v 2)
                                                                                · by_cases a7 : acc1_0 (v 0)
                                                                                  · by_cases a9 : acc1_0 (v 2)
                                                                                    · by_cases a17 : acc2_1 (v 1)
                                                                                      · by_cases a13 : acc2_0 (v 0)
                                                                                        · refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_012 v hv a13 a17 a111) fun a111 => ?_
                                                                                          have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl110 (v 2) (hv 2) a111 hc
                                                                                          have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl375 (v 2) (hv 2) a111 hc a51
                                                                                          have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) hc a111 a51
                                                                                          refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_021 v hv a13 a109 a18) fun a109 => ?_
                                                                                          have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) hc a109 a50
                                                                                          refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_021 v hv a130 a47 a45) fun a130 => ?_
                                                                                          have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl244 (v 0) (hv 0) a130 hc
                                                                                          have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl403 (v 0) (hv 0) hc a130 a49
                                                                                          refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_210 v hv a154 a128 a36) fun a128 => ?_
                                                                                          have a131 : acc8_0 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) a128 hc
                                                                                          exact succ8_102 v hv a43 a131 a48
                                                                                        · by_cases a2 : acc0_1 (v 0)
                                                                                          · refine (Classical.em (acc0_2 (v 2))).elim (fun a110 => succ0_102 v hv a2 a3 a110) fun a110 => ?_
                                                                                            by_cases a10 : acc1_2 (v 0)
                                                                                            · have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl79 (v 0) (hv 0) a10 hc
                                                                                              refine (Classical.em (acc1_1 (v 2))).elim (fun a120 => succ1_201 v hv a10 a8 a120) fun a120 => ?_
                                                                                              refine (Classical.em (acc1_1 (v 1))).elim (fun a119 => succ1_210 v hv a10 a119 a9) fun a119 => ?_
                                                                                              have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl77 (v 1) (hv 1) a119 hc
                                                                                              by_cases a4 : acc0_1 (v 1)
                                                                                              · by_cases a6 : acc0_1 (v 2)
                                                                                                · by_cases a11 : acc1_2 (v 1)
                                                                                                  · refine (Classical.em (acc1_1 (v 0))).elim (fun a118 => succ1_120 v hv a118 a11 a9) fun a118 => ?_
                                                                                                    have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl354 (v 0) (hv 0) hc a118 a13
                                                                                                    refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                                                    have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl355 (v 2) (hv 2) hc a51 a132
                                                                                                    have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl403 (v 2) (hv 2) hc a132 a51
                                                                                                    refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                                                                                    have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                                                                    exact succ8_012 v hv a130 a44 a48
                                                                                                  · have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl345 (v 1) (hv 1) a11 hc a119
                                                                                                    refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_102 v hv a16 a14 a111) fun a111 => ?_
                                                                                                    have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) hc a111 a51
                                                                                                    refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_012 v hv a130 a44 a48) fun a130 => ?_
                                                                                                    have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl244 (v 0) (hv 0) a130 hc
                                                                                                    have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl403 (v 0) (hv 0) hc a130 a49
                                                                                                    refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_210 v hv a154 a128 a36) fun a128 => ?_
                                                                                                    have a131 : acc8_0 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) a128 hc
                                                                                                    exact succ8_102 v hv a43 a131 a48
                                                                                                · have a15 : acc2_0 (v 2) := Classical.byContradiction fun hc => cl377 (v 2) (hv 2) a120 a6 hc
                                                                                                  refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_210 v hv a107 a17 a15) fun a107 => ?_
                                                                                                  have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl474 (v 0) (hv 0) hc a13 a107
                                                                                                  refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                                                  have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl355 (v 2) (hv 2) hc a51 a132
                                                                                                  have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl403 (v 2) (hv 2) hc a132 a51
                                                                                                  refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                                                                                  have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                                                                  exact succ8_012 v hv a130 a44 a48
                                                                                              · have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl377 (v 1) (hv 1) a119 a4 hc
                                                                                                refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_102 v hv a16 a14 a111) fun a111 => ?_
                                                                                                have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) hc a111 a51
                                                                                                refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_012 v hv a130 a44 a48) fun a130 => ?_
                                                                                                have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl244 (v 0) (hv 0) a130 hc
                                                                                                have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl403 (v 0) (hv 0) hc a130 a49
                                                                                                refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_210 v hv a154 a128 a36) fun a128 => ?_
                                                                                                have a131 : acc8_0 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) a128 hc
                                                                                                exact succ8_102 v hv a43 a131 a48
                                                                                            · have a118 : acc1_1 (v 0) := Classical.byContradiction fun hc => cl345 (v 0) (hv 0) a10 a13 hc
                                                                                              have a107 : acc2_2 (v 0) := Classical.byContradiction fun hc => cl473 (v 0) (hv 0) a10 a13 hc
                                                                                              refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_210 v hv a107 a17 a15) fun a15 => ?_
                                                                                              have a12 : acc1_2 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) a110 hc a15
                                                                                              exact succ1_102 v hv a118 a8 a12
                                                                                          · have a118 : acc1_1 (v 0) := Classical.byContradiction fun hc => cl377 (v 0) (hv 0) hc a2 a13
                                                                                            have a107 : acc2_2 (v 0) := Classical.byContradiction fun hc => cl446 (v 0) (hv 0) a118 a2 hc
                                                                                            have a145 : acc16_2 (v 0) := Classical.byContradiction fun hc => cl470 (v 0) (hv 0) a2 hc a13
                                                                                            have a148 : acc17_2 (v 0) := Classical.byContradiction fun hc => cl341 (v 0) (hv 0) a145 hc
                                                                                            refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_201 v hv a148 a98 a102) fun a102 => ?_
                                                                                            refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_210 v hv a107 a17 a15) fun a15 => ?_
                                                                                            refine (Classical.em (acc1_2 (v 2))).elim (fun a12 => succ1_102 v hv a118 a8 a12) fun a12 => ?_
                                                                                            have a110 : acc0_2 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) hc a12 a15
                                                                                            refine (Classical.em (acc0_1 (v 1))).elim (fun a4 => succ0_012 v hv a1 a4 a110) fun a4 => ?_
                                                                                            have a95 : acc16_1 (v 1) := Classical.byContradiction fun hc => cl36 (v 1) (hv 1) a4 hc
                                                                                            refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_012 v hv a91 a95 a147) fun a147 => ?_
                                                                                            refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_210 v hv a145 a95 a93) fun a93 => ?_
                                                                                            exact (cl384 (v 2) (hv 2) a147 a102 a93).elim
                                                                                      · have a11 : ¬acc1_2 (v 1) := fun hc => cl79 (v 1) (hv 1) hc a17
                                                                                        have a95 : acc16_1 (v 1) := Classical.byContradiction fun hc => cl104 (v 1) (hv 1) a17 hc
                                                                                        have a131 : acc8_0 (v 1) := Classical.byContradiction fun hc => cl347 (v 1) (hv 1) a50 hc a17
                                                                                        have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl375 (v 1) (hv 1) hc a17 a50
                                                                                        have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl479 (v 1) (hv 1) a50 a17 hc
                                                                                        refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_021 v hv a97 a149 a102) fun a102 => ?_
                                                                                        refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_012 v hv a91 a95 a147) fun a147 => ?_
                                                                                        have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) a147 hc a102
                                                                                        have a93 : acc16_0 (v 2) := Classical.byContradiction fun hc => cl384 (v 2) (hv 2) a147 a102 hc
                                                                                        refine (Classical.em (acc16_2 (v 0))).elim (fun a145 => succ16_210 v hv a145 a95 a93) fun a145 => ?_
                                                                                        have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl379 (v 0) (hv 0) a145 hc a100
                                                                                        refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_120 v hv a16 a109 a15) fun a15 => ?_
                                                                                        have a6 : acc0_1 (v 2) := Classical.byContradiction fun hc => cl470 (v 2) (hv 2) hc a147 a15
                                                                                        refine (Classical.em (acc0_2 (v 1))).elim (fun a108 => succ0_021 v hv a1 a108 a6) fun a108 => ?_
                                                                                        have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl390 (v 1) (hv 1) a108 a11 hc
                                                                                        refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_102 v hv a16 a14 a111) fun a111 => ?_
                                                                                        refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_201 v hv a107 a14 a18) fun a107 => ?_
                                                                                        have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl475 (v 0) (hv 0) hc a107 a49
                                                                                        refine (Classical.em (acc8_1 (v 2))).elim (fun a45 => succ8_201 v hv a46 a131 a45) fun a45 => ?_
                                                                                        exact (cl110 (v 2) (hv 2) a111 a45).elim
                                                                                    · have a110 : acc0_2 (v 2) := Classical.byContradiction fun hc => cl43 (v 2) (hv 2) hc a9
                                                                                      have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl72 (v 2) (hv 2) a9 hc
                                                                                      refine (Classical.em (acc16_1 (v 1))).elim (fun a95 => succ16_012 v hv a91 a95 a147) fun a95 => ?_
                                                                                      have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl338 (v 1) (hv 1) hc a95
                                                                                      refine (Classical.em (acc16_1 (v 0))).elim (fun a94 => succ16_102 v hv a94 a92 a147) fun a94 => ?_
                                                                                      have a2 : acc0_1 (v 0) := Classical.byContradiction fun hc => cl36 (v 0) (hv 0) hc a94
                                                                                      exact succ0_102 v hv a2 a3 a110
                                                                                  · have a106 : acc0_2 (v 0) := Classical.byContradiction fun hc => cl43 (v 0) (hv 0) hc a7
                                                                                    have a145 : acc16_2 (v 0) := Classical.byContradiction fun hc => cl72 (v 0) (hv 0) a7 hc
                                                                                    have a148 : acc17_2 (v 0) := Classical.byContradiction fun hc => cl74 (v 0) (hv 0) a7 hc
                                                                                    refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_201 v hv a148 a98 a102) fun a102 => ?_
                                                                                    refine (Classical.em (acc0_1 (v 1))).elim (fun a4 => succ0_210 v hv a106 a4 a5) fun a4 => ?_
                                                                                    have a95 : acc16_1 (v 1) := Classical.byContradiction fun hc => cl36 (v 1) (hv 1) a4 hc
                                                                                    refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_012 v hv a91 a95 a147) fun a147 => ?_
                                                                                    refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_210 v hv a145 a95 a93) fun a93 => ?_
                                                                                    exact (cl384 (v 2) (hv 2) a147 a102 a93).elim
                                                                                · have a12 : acc1_2 (v 2) := Classical.byContradiction fun hc => cl2 (v 2) (hv 2) a5 hc
                                                                                  have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl14 (v 2) (hv 2) a5 hc
                                                                                  refine (Classical.em (acc1_1 (v 0))).elim (fun a118 => succ1_102 v hv a118 a8 a12) fun a118 => ?_
                                                                                  have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl77 (v 0) (hv 0) a118 hc
                                                                                  refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_102 v hv a43 a131 a48) fun a131 => ?_
                                                                                  have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl244 (v 1) (hv 1) a131 hc
                                                                                  have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl403 (v 1) (hv 1) hc a131 a50
                                                                                  refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                                                  have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                                                  exact succ8_012 v hv a130 a44 a48
                                                                              · have a4 : acc0_1 (v 1) := Classical.byContradiction fun hc => cl0 (v 1) (hv 1) a3 hc
                                                                                have a11 : acc1_2 (v 1) := Classical.byContradiction fun hc => cl2 (v 1) (hv 1) a3 hc
                                                                                have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl13 (v 1) (hv 1) a3 hc
                                                                                have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl14 (v 1) (hv 1) a3 hc
                                                                                refine (Classical.em (acc0_2 (v 2))).elim (fun a110 => succ0_012 v hv a1 a4 a110) fun a110 => ?_
                                                                                have a9 : acc1_0 (v 2) := Classical.byContradiction fun hc => cl43 (v 2) (hv 2) a110 hc
                                                                                refine (Classical.em (acc1_1 (v 0))).elim (fun a118 => succ1_120 v hv a118 a11 a9) fun a118 => ?_
                                                                                have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl77 (v 0) (hv 0) a118 hc
                                                                                refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                                                                have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl355 (v 2) (hv 2) hc a51 a132
                                                                                have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl403 (v 2) (hv 2) hc a132 a51
                                                                                refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                                                                have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                                                exact succ8_012 v hv a130 a44 a48
                                                                            · have a10 : acc1_2 (v 0) := Classical.byContradiction fun hc => cl2 (v 0) (hv 0) a1 hc
                                                                              have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl14 (v 0) (hv 0) a1 hc
                                                                              refine (Classical.em (acc1_1 (v 2))).elim (fun a120 => succ1_201 v hv a10 a8 a120) fun a120 => ?_
                                                                              have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl77 (v 2) (hv 2) a120 hc
                                                                              refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_201 v hv a46 a131 a45) fun a131 => ?_
                                                                              have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl355 (v 1) (hv 1) hc a50 a131
                                                                              have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl403 (v 1) (hv 1) hc a131 a50
                                                                              refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                                              have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                                              exact succ8_021 v hv a130 a47 a45
                                                                          · have a3 : acc0_0 (v 1) := Classical.byContradiction fun hc => cl1 (v 1) (hv 1) hc a8
                                                                            have a119 : acc1_1 (v 1) := Classical.byContradiction fun hc => cl44 (v 1) (hv 1) a8 hc
                                                                            have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl46 (v 1) (hv 1) a8 hc
                                                                            have a95 : acc16_1 (v 1) := Classical.byContradiction fun hc => cl71 (v 1) (hv 1) a8 hc
                                                                            have a146 : acc16_2 (v 1) := Classical.byContradiction fun hc => cl72 (v 1) (hv 1) a8 hc
                                                                            refine (Classical.em (acc16_1 (v 2))).elim (fun a96 => succ16_021 v hv a91 a146 a96) fun a96 => ?_
                                                                            have a93 : acc16_0 (v 2) := Classical.byContradiction fun hc => cl338 (v 2) (hv 2) hc a96
                                                                            refine (Classical.em (acc16_1 (v 0))).elim (fun a94 => succ16_120 v hv a94 a146 a93) fun a94 => ?_
                                                                            refine (Classical.em (acc16_2 (v 0))).elim (fun a145 => succ16_210 v hv a145 a95 a93) fun a145 => ?_
                                                                            have a7 : acc1_0 (v 0) := Classical.byContradiction fun hc => cl72 (v 0) (hv 0) hc a145
                                                                            have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl379 (v 0) (hv 0) a145 hc a100
                                                                            refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_120 v hv a16 a109 a15) fun a15 => ?_
                                                                            refine (Classical.em (acc1_2 (v 2))).elim (fun a12 => succ1_012 v hv a7 a119 a12) fun a12 => ?_
                                                                            have a110 : acc0_2 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) hc a12 a15
                                                                            refine (Classical.em (acc0_1 (v 0))).elim (fun a2 => succ0_102 v hv a2 a3 a110) fun a2 => ?_
                                                                            exact (cl36 (v 0) (hv 0) a2 a94).elim
                                                                        · have a1 : acc0_0 (v 0) := Classical.byContradiction fun hc => cl29 (v 0) (hv 0) hc a91
                                                                          have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl348 (v 0) (hv 0) a49 hc a91
                                                                          have a145 : acc16_2 (v 0) := Classical.byContradiction fun hc => cl384 (v 0) (hv 0) hc a100 a91
                                                                          have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl385 (v 0) (hv 0) hc a100 a91
                                                                          refine (Classical.em (acc14_1 (v 1))).elim (fun a83 => succ14_210 v hv a160 a83 a81) fun a83 => ?_
                                                                          have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) a83 hc
                                                                          refine (Classical.em (acc16_1 (v 2))).elim (fun a96 => succ16_201 v hv a145 a92 a96) fun a96 => ?_
                                                                          have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl104 (v 2) (hv 2) hc a96
                                                                          have a93 : acc16_0 (v 2) := Classical.byContradiction fun hc => cl338 (v 2) (hv 2) hc a96
                                                                          refine (Classical.em (acc16_1 (v 1))).elim (fun a95 => succ16_210 v hv a145 a95 a93) fun a95 => ?_
                                                                          have a4 : acc0_1 (v 1) := Classical.byContradiction fun hc => cl36 (v 1) (hv 1) hc a95
                                                                          have a8 : acc1_0 (v 1) := Classical.byContradiction fun hc => cl71 (v 1) (hv 1) hc a95
                                                                          have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl104 (v 1) (hv 1) hc a95
                                                                          refine (Classical.em (acc0_2 (v 2))).elim (fun a110 => succ0_012 v hv a1 a4 a110) fun a110 => ?_
                                                                          have a107 : acc2_2 (v 0) := Classical.byContradiction fun hc => cl397 (v 0) (hv 0) a145 hc a100
                                                                          refine (Classical.em (acc2_0 (v 1))).elim (fun a14 => succ2_201 v hv a107 a14 a18) fun a14 => ?_
                                                                          refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_210 v hv a107 a17 a15) fun a15 => ?_
                                                                          have a12 : acc1_2 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) a110 hc a15
                                                                          refine (Classical.em (acc1_1 (v 0))).elim (fun a118 => succ1_102 v hv a118 a8 a12) fun a118 => ?_
                                                                          have a7 : acc1_0 (v 0) := Classical.byContradiction fun hc => cl44 (v 0) (hv 0) hc a118
                                                                          have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl77 (v 0) (hv 0) a118 hc
                                                                          refine (Classical.em (acc1_1 (v 1))).elim (fun a119 => succ1_012 v hv a7 a119 a12) fun a119 => ?_
                                                                          have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl354 (v 1) (hv 1) hc a119 a14
                                                                          refine (Classical.em (acc8_1 (v 2))).elim (fun a45 => succ8_021 v hv a130 a47 a45) fun a45 => ?_
                                                                          refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                                                          exact (cl244 (v 2) (hv 2) a132 a45).elim
                                                                    · have a5 : acc0_0 (v 2) := Classical.byContradiction fun hc => cl31 (v 2) (hv 2) hc a99
                                                                      have a12 : ¬acc1_2 (v 2) := fun hc => cl84 (v 2) (hv 2) hc a99
                                                                      have a96 : acc16_1 (v 2) := Classical.byContradiction fun hc => cl339 (v 2) (hv 2) hc a99
                                                                      have a162 : acc14_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) hc a90 a99
                                                                      have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl477 (v 2) (hv 2) a66 hc a99
                                                                      have a111 : acc2_2 (v 2) := Classical.byContradiction fun hc => cl382 (v 2) (hv 2) a144 a51 hc
                                                                      have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl333 (v 2) (hv 2) a162 hc
                                                                      refine (Classical.em (acc14_1 (v 1))).elim (fun a83 => succ14_012 v hv a79 a83 a162) fun a83 => ?_
                                                                      refine (Classical.em (acc14_1 (v 0))).elim (fun a82 => succ14_102 v hv a82 a80 a162) fun a82 => ?_
                                                                      have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) a82 hc
                                                                      refine (Classical.em (acc16_2 (v 1))).elim (fun a146 => succ16_021 v hv a91 a146 a96) fun a146 => ?_
                                                                      have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) a83 hc
                                                                      refine (Classical.em (acc16_2 (v 0))).elim (fun a145 => succ16_201 v hv a145 a92 a96) fun a145 => ?_
                                                                      have a7 : acc1_0 (v 0) := Classical.byContradiction fun hc => cl72 (v 0) (hv 0) hc a145
                                                                      refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_012 v hv a97 a101 a150) fun a101 => ?_
                                                                      refine (Classical.em (acc17_1 (v 0))).elim (fun a100 => succ17_102 v hv a100 a98 a150) fun a100 => ?_
                                                                      have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl379 (v 0) (hv 0) a145 hc a100
                                                                      refine (Classical.em (acc2_0 (v 1))).elim (fun a14 => succ2_102 v hv a16 a14 a111) fun a14 => ?_
                                                                      have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) a146 hc a101
                                                                      refine (Classical.em (acc2_0 (v 0))).elim (fun a13 => succ2_012 v hv a13 a17 a111) fun a13 => ?_
                                                                      have a2 : acc0_1 (v 0) := Classical.byContradiction fun hc => cl470 (v 0) (hv 0) hc a145 a13
                                                                      refine (Classical.em (acc0_2 (v 1))).elim (fun a108 => succ0_120 v hv a2 a108 a5) fun a108 => ?_
                                                                      have a11 : acc1_2 (v 1) := Classical.byContradiction fun hc => cl390 (v 1) (hv 1) a108 hc a14
                                                                      refine (Classical.em (acc1_1 (v 2))).elim (fun a120 => succ1_021 v hv a7 a11 a120) fun a120 => ?_
                                                                      have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl77 (v 2) (hv 2) a120 hc
                                                                      have a15 : acc2_0 (v 2) := Classical.byContradiction fun hc => cl345 (v 2) (hv 2) a12 hc a120
                                                                      refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_210 v hv a107 a17 a15) fun a107 => ?_
                                                                      have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl474 (v 0) (hv 0) hc a13 a107
                                                                      refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_201 v hv a46 a131 a45) fun a131 => ?_
                                                                      have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl355 (v 1) (hv 1) hc a50 a131
                                                                      have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl403 (v 1) (hv 1) hc a131 a50
                                                                      refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                                      have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                                      exact succ8_021 v hv a130 a47 a45
                                                                  · have a3 : acc0_0 (v 1) := Classical.byContradiction fun hc => cl31 (v 1) (hv 1) hc a98
                                                                    have a11 : ¬acc1_2 (v 1) := fun hc => cl84 (v 1) (hv 1) hc a98
                                                                    have a95 : acc16_1 (v 1) := Classical.byContradiction fun hc => cl339 (v 1) (hv 1) hc a98
                                                                    have a161 : acc14_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) hc a89 a98
                                                                    have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl477 (v 1) (hv 1) a65 hc a98
                                                                    have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl382 (v 1) (hv 1) a143 a50 hc
                                                                    have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl333 (v 1) (hv 1) a161 hc
                                                                    refine (Classical.em (acc14_1 (v 2))).elim (fun a84 => succ14_021 v hv a79 a161 a84) fun a84 => ?_
                                                                    refine (Classical.em (acc14_1 (v 0))).elim (fun a82 => succ14_120 v hv a82 a161 a81) fun a82 => ?_
                                                                    have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) a82 hc
                                                                    refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_012 v hv a91 a95 a147) fun a147 => ?_
                                                                    have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl452 (v 2) (hv 2) hc a147 a84
                                                                    refine (Classical.em (acc17_1 (v 0))).elim (fun a100 => succ17_120 v hv a100 a149 a99) fun a100 => ?_
                                                                    have a93 : acc16_0 (v 2) := Classical.byContradiction fun hc => cl332 (v 2) (hv 2) a84 hc
                                                                    refine (Classical.em (acc16_2 (v 0))).elim (fun a145 => succ16_210 v hv a145 a95 a93) fun a145 => ?_
                                                                    have a7 : acc1_0 (v 0) := Classical.byContradiction fun hc => cl72 (v 0) (hv 0) hc a145
                                                                    have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl379 (v 0) (hv 0) a145 hc a100
                                                                    refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_120 v hv a16 a109 a15) fun a15 => ?_
                                                                    have a102 : ¬acc17_1 (v 2) := fun hc => cl97 (v 2) (hv 2) a15 hc
                                                                    have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) a147 hc a102
                                                                    refine (Classical.em (acc2_0 (v 0))).elim (fun a13 => succ2_021 v hv a13 a109 a18) fun a13 => ?_
                                                                    have a2 : acc0_1 (v 0) := Classical.byContradiction fun hc => cl470 (v 0) (hv 0) hc a145 a13
                                                                    refine (Classical.em (acc0_2 (v 2))).elim (fun a110 => succ0_102 v hv a2 a3 a110) fun a110 => ?_
                                                                    have a12 : acc1_2 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) a110 hc a15
                                                                    refine (Classical.em (acc1_1 (v 1))).elim (fun a119 => succ1_012 v hv a7 a119 a12) fun a119 => ?_
                                                                    have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl77 (v 1) (hv 1) a119 hc
                                                                    have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl345 (v 1) (hv 1) a11 hc a119
                                                                    refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_201 v hv a107 a14 a18) fun a107 => ?_
                                                                    have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl474 (v 0) (hv 0) hc a13 a107
                                                                    refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                                    have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl355 (v 2) (hv 2) hc a51 a132
                                                                    have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl403 (v 2) (hv 2) hc a132 a51
                                                                    refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                                                    have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                                    exact succ8_012 v hv a130 a44 a48
                                                                · have a5 : acc0_0 (v 2) := Classical.byContradiction fun hc => cl27 (v 2) (hv 2) hc a87
                                                                  have a12 : ¬acc1_2 (v 2) := fun hc => cl83 (v 2) (hv 2) hc a87
                                                                  have a96 : acc16_1 (v 2) := Classical.byContradiction fun hc => cl334 (v 2) (hv 2) a87 hc
                                                                  have a99 : ¬acc17_0 (v 2) := fun hc => cl335 (v 2) (hv 2) a87 hc
                                                                  have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl371 (v 2) (hv 2) a60 hc a87
                                                                  have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl430 (v 2) (hv 2) a87 hc a72
                                                                  have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl372 (v 2) (hv 2) a141 hc a90
                                                                  refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_012 v hv a97 a101 a150) fun a101 => ?_
                                                                  have a111 : acc2_2 (v 2) := Classical.byContradiction fun hc => cl382 (v 2) (hv 2) a144 a51 hc
                                                                  have a162 : acc14_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) hc a90 a99
                                                                  refine (Classical.em (acc14_1 (v 1))).elim (fun a83 => succ14_012 v hv a79 a83 a162) fun a83 => ?_
                                                                  refine (Classical.em (acc14_1 (v 0))).elim (fun a82 => succ14_102 v hv a82 a80 a162) fun a82 => ?_
                                                                  have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) a82 hc
                                                                  refine (Classical.em (acc16_2 (v 1))).elim (fun a146 => succ16_021 v hv a91 a146 a96) fun a146 => ?_
                                                                  have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) a146 hc a101
                                                                  have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl384 (v 1) (hv 1) a146 a101 hc
                                                                  have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) hc a146 a83
                                                                  refine (Classical.em (acc17_1 (v 0))).elim (fun a100 => succ17_102 v hv a100 a98 a150) fun a100 => ?_
                                                                  refine (Classical.em (acc16_2 (v 0))).elim (fun a145 => succ16_201 v hv a145 a92 a96) fun a145 => ?_
                                                                  have a7 : acc1_0 (v 0) := Classical.byContradiction fun hc => cl72 (v 0) (hv 0) hc a145
                                                                  have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl379 (v 0) (hv 0) a145 hc a100
                                                                  refine (Classical.em (acc2_0 (v 1))).elim (fun a14 => succ2_102 v hv a16 a14 a111) fun a14 => ?_
                                                                  refine (Classical.em (acc2_0 (v 0))).elim (fun a13 => succ2_012 v hv a13 a17 a111) fun a13 => ?_
                                                                  have a2 : acc0_1 (v 0) := Classical.byContradiction fun hc => cl470 (v 0) (hv 0) hc a145 a13
                                                                  refine (Classical.em (acc0_2 (v 1))).elim (fun a108 => succ0_120 v hv a2 a108 a5) fun a108 => ?_
                                                                  have a11 : acc1_2 (v 1) := Classical.byContradiction fun hc => cl390 (v 1) (hv 1) a108 hc a14
                                                                  refine (Classical.em (acc1_1 (v 2))).elim (fun a120 => succ1_021 v hv a7 a11 a120) fun a120 => ?_
                                                                  have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl77 (v 2) (hv 2) a120 hc
                                                                  have a15 : acc2_0 (v 2) := Classical.byContradiction fun hc => cl345 (v 2) (hv 2) a12 hc a120
                                                                  refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_210 v hv a107 a17 a15) fun a107 => ?_
                                                                  have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl474 (v 0) (hv 0) hc a13 a107
                                                                  refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_201 v hv a46 a131 a45) fun a131 => ?_
                                                                  have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl355 (v 1) (hv 1) hc a50 a131
                                                                  have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl403 (v 1) (hv 1) hc a131 a50
                                                                  refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                                  have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                                  exact succ8_021 v hv a130 a47 a45
                                                          · have a3 : acc0_0 (v 1) := Classical.byContradiction fun hc => cl27 (v 1) (hv 1) hc a86
                                                            have a11 : ¬acc1_2 (v 1) := fun hc => cl83 (v 1) (hv 1) hc a86
                                                            have a95 : acc16_1 (v 1) := Classical.byContradiction fun hc => cl334 (v 1) (hv 1) a86 hc
                                                            have a98 : ¬acc17_0 (v 1) := fun hc => cl335 (v 1) (hv 1) a86 hc
                                                            have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl371 (v 1) (hv 1) a59 hc a86
                                                            have a140 : acc12_1 (v 1) := Classical.byContradiction fun hc => cl430 (v 1) (hv 1) a86 hc a71
                                                            have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl372 (v 1) (hv 1) a140 hc a89
                                                            refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_021 v hv a97 a149 a102) fun a102 => ?_
                                                            have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl382 (v 1) (hv 1) a143 a50 hc
                                                            have a161 : acc14_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) hc a89 a98
                                                            refine (Classical.em (acc14_1 (v 2))).elim (fun a84 => succ14_021 v hv a79 a161 a84) fun a84 => ?_
                                                            refine (Classical.em (acc14_1 (v 0))).elim (fun a82 => succ14_120 v hv a82 a161 a81) fun a82 => ?_
                                                            have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) a82 hc
                                                            refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_012 v hv a91 a95 a147) fun a147 => ?_
                                                            have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) a147 hc a102
                                                            have a93 : acc16_0 (v 2) := Classical.byContradiction fun hc => cl384 (v 2) (hv 2) a147 a102 hc
                                                            have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl452 (v 2) (hv 2) hc a147 a84
                                                            refine (Classical.em (acc17_1 (v 0))).elim (fun a100 => succ17_120 v hv a100 a149 a99) fun a100 => ?_
                                                            refine (Classical.em (acc16_2 (v 0))).elim (fun a145 => succ16_210 v hv a145 a95 a93) fun a145 => ?_
                                                            have a7 : acc1_0 (v 0) := Classical.byContradiction fun hc => cl72 (v 0) (hv 0) hc a145
                                                            have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl379 (v 0) (hv 0) a145 hc a100
                                                            refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_120 v hv a16 a109 a15) fun a15 => ?_
                                                            refine (Classical.em (acc2_0 (v 0))).elim (fun a13 => succ2_021 v hv a13 a109 a18) fun a13 => ?_
                                                            have a2 : acc0_1 (v 0) := Classical.byContradiction fun hc => cl470 (v 0) (hv 0) hc a145 a13
                                                            refine (Classical.em (acc0_2 (v 2))).elim (fun a110 => succ0_102 v hv a2 a3 a110) fun a110 => ?_
                                                            have a12 : acc1_2 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) a110 hc a15
                                                            refine (Classical.em (acc1_1 (v 1))).elim (fun a119 => succ1_012 v hv a7 a119 a12) fun a119 => ?_
                                                            have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl77 (v 1) (hv 1) a119 hc
                                                            have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl345 (v 1) (hv 1) a11 hc a119
                                                            refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_201 v hv a107 a14 a18) fun a107 => ?_
                                                            have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl474 (v 0) (hv 0) hc a13 a107
                                                            refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                                            have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl355 (v 2) (hv 2) hc a51 a132
                                                            have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl403 (v 2) (hv 2) hc a132 a51
                                                            refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                                            have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                            exact succ8_012 v hv a130 a44 a48
                                    · have a108 : ¬acc0_2 (v 1) := fun hc => cl42 (v 1) (hv 1) hc a116
                                      have a109 : ¬acc2_2 (v 1) := fun hc => cl109 (v 1) (hv 1) hc a116
                                      have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl247 (v 1) (hv 1) hc a116
                                      have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl263 (v 1) (hv 1) a116 hc
                                      have a161 : ¬acc14_2 (v 1) := fun hc => cl265 (v 1) (hv 1) a116 hc
                                      have a146 : ¬acc16_2 (v 1) := fun hc => cl266 (v 1) (hv 1) a116 hc
                                      have a149 : ¬acc17_2 (v 1) := fun hc => cl267 (v 1) (hv 1) a116 hc
                                      by_cases a1 : acc0_0 (v 0)
                                      · by_cases a3 : acc0_0 (v 1)
                                        · by_cases a5 : acc0_0 (v 2)
                                          · by_cases a7 : acc1_0 (v 0)
                                            · by_cases a9 : acc1_0 (v 2)
                                              · by_cases a14 : acc2_0 (v 1)
                                                · by_cases a26 : acc4_1 (v 1)
                                                  · by_cases a41 : acc7_2 (v 1)
                                                    · have a50 : acc9_1 (v 1) := Classical.byContradiction fun hc => cl242 (v 1) (hv 1) a41 hc
                                                      refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_210 v hv a52 a50 a117) fun a117 => ?_
                                                      have a111 : ¬acc2_2 (v 2) := fun hc => cl109 (v 2) (hv 2) hc a117
                                                      have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl247 (v 2) (hv 2) hc a117
                                                      have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl263 (v 2) (hv 2) a117 hc
                                                      have a150 : ¬acc17_2 (v 2) := fun hc => cl267 (v 2) (hv 2) a117 hc
                                                      by_cases a15 : acc2_0 (v 2)
                                                      · by_cases a19 : acc3_1 (v 0)
                                                        · by_cases a25 : acc4_1 (v 0)
                                                          · by_cases a22 : acc3_2 (v 0)
                                                            · have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl143 (v 0) (hv 0) a22 hc
                                                              refine (Classical.em (acc3_1 (v 2))).elim (fun a21 => succ3_201 v hv a22 a104 a21) fun a21 => ?_
                                                              refine (Classical.em (acc3_1 (v 1))).elim (fun a20 => succ3_210 v hv a22 a20 a105) fun a20 => ?_
                                                              have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl142 (v 1) (hv 1) a20 hc
                                                              refine (Classical.em (acc4_2 (v 2))).elim (fun a30 => succ4_102 v hv a25 a122 a30) fun a30 => ?_
                                                              have a114 : acc7_0 (v 2) := Classical.byContradiction fun hc => cl461 (v 2) (hv 2) a30 a21 hc
                                                              refine (Classical.em (acc7_1 (v 1))).elim (fun a38 => succ7_210 v hv a40 a38 a114) fun a38 => ?_
                                                              have a152 : ¬acc5_2 (v 1) := fun hc => cl194 (v 1) (hv 1) hc a38
                                                              have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl411 (v 1) (hv 1) a116 hc a38
                                                              refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_120 v hv a61 a65 a138) fun a138 => ?_
                                                              have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl468 (v 2) (hv 2) a30 hc a138
                                                              refine (Classical.em (acc7_0 (v 1))).elim (fun a113 => succ7_201 v hv a40 a113 a39) fun a113 => ?_
                                                              exact (cl457 (v 1) (hv 1) a23 a113 a152).elim
                                                            · by_cases a27 : acc4_1 (v 2)
                                                              · by_cases a29 : acc4_2 (v 1)
                                                                · have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl166 (v 1) (hv 1) a29 hc
                                                                  refine (Classical.em (acc4_0 (v 2))).elim (fun a123 => succ4_120 v hv a25 a29 a123) fun a123 => ?_
                                                                  have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl149 (v 2) (hv 2) a123 hc
                                                                  have a63 : acc11_1 (v 2) := Classical.byContradiction fun hc => cl154 (v 2) (hv 2) a123 hc
                                                                  refine (Classical.em (acc11_0 (v 0))).elim (fun a136 => succ11_021 v hv a136 a65 a63) fun a136 => ?_
                                                                  have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl251 (v 0) (hv 0) hc a136
                                                                  have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl410 (v 0) (hv 0) a64 hc a136
                                                                  refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_120 v hv a37 a41 a114) fun a114 => ?_
                                                                  have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                                                  refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_102 v hv a124 a32 a153) fun a124 => ?_
                                                                  refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_021 v hv a112 a41 a39) fun a112 => ?_
                                                                  have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) hc a124 a112
                                                                  refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_201 v hv a154 a35 a129) fun a129 => ?_
                                                                  refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_210 v hv a154 a128 a36) fun a128 => ?_
                                                                  have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl356 (v 1) (hv 1) hc a116 a128
                                                                  refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                                                  exact (cl215 (v 2) (hv 2) a129 a132).elim
                                                                · by_cases a30 : acc4_2 (v 2)
                                                                  · have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl166 (v 2) (hv 2) a30 hc
                                                                    refine (Classical.em (acc4_0 (v 1))).elim (fun a122 => succ4_102 v hv a25 a122 a30) fun a122 => ?_
                                                                    have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl154 (v 1) (hv 1) a122 hc
                                                                    refine (Classical.em (acc11_0 (v 0))).elim (fun a136 => succ11_012 v hv a136 a62 a66) fun a136 => ?_
                                                                    have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl251 (v 0) (hv 0) hc a136
                                                                    have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl410 (v 0) (hv 0) a64 hc a136
                                                                    refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_120 v hv a37 a41 a114) fun a114 => ?_
                                                                    have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                                                    have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl194 (v 2) (hv 2) a153 hc
                                                                    refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_102 v hv a124 a32 a153) fun a124 => ?_
                                                                    refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_021 v hv a112 a41 a39) fun a112 => ?_
                                                                    have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) hc a124 a112
                                                                    refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_201 v hv a154 a35 a129) fun a129 => ?_
                                                                    refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_210 v hv a154 a128 a36) fun a128 => ?_
                                                                    have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl356 (v 1) (hv 1) hc a116 a128
                                                                    refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                                                    exact (cl215 (v 2) (hv 2) a129 a132).elim
                                                                  · by_cases a21 : acc3_1 (v 2)
                                                                    · by_cases a37 : acc7_1 (v 0)
                                                                      · refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_120 v hv a37 a41 a114) fun a114 => ?_
                                                                        have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl360 (v 2) (hv 2) a114 hc a30
                                                                        have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                                                        refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_102 v hv a124 a32 a153) fun a124 => ?_
                                                                        refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_021 v hv a112 a41 a39) fun a112 => ?_
                                                                        have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl226 (v 0) (hv 0) a112 hc
                                                                        have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) hc a124 a112
                                                                        refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_201 v hv a154 a35 a129) fun a129 => ?_
                                                                        refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_210 v hv a154 a128 a36) fun a128 => ?_
                                                                        have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl356 (v 1) (hv 1) hc a116 a128
                                                                        refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                                                        exact (cl215 (v 2) (hv 2) a129 a132).elim
                                                                      · have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl360 (v 0) (hv 0) hc a37 a28
                                                                        have a115 : acc9_0 (v 0) := Classical.byContradiction fun hc => cl411 (v 0) (hv 0) hc a64 a37
                                                                        refine (Classical.em (acc9_2 (v 2))).elim (fun a54 => succ9_012 v hv a115 a50 a54) fun a54 => ?_
                                                                        have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 hc a150
                                                                        have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl454 (v 2) (hv 2) a21 a54 hc
                                                                        refine (Classical.em (acc7_1 (v 1))).elim (fun a38 => succ7_012 v hv a112 a38 a42) fun a38 => ?_
                                                                        have a137 : acc11_0 (v 1) := Classical.byContradiction fun hc => cl468 (v 1) (hv 1) a29 a38 hc
                                                                        exact succ11_102 v hv a61 a137 a66
                                                                    · have a114 : acc7_0 (v 2) := Classical.byContradiction fun hc => cl461 (v 2) (hv 2) a30 a21 hc
                                                                      refine (Classical.em (acc7_1 (v 0))).elim (fun a37 => succ7_120 v hv a37 a41 a114) fun a37 => ?_
                                                                      have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl410 (v 0) (hv 0) a64 a37 hc
                                                                      have a115 : acc9_0 (v 0) := Classical.byContradiction fun hc => cl411 (v 0) (hv 0) hc a64 a37
                                                                      refine (Classical.em (acc9_2 (v 2))).elim (fun a54 => succ9_012 v hv a115 a50 a54) fun a54 => ?_
                                                                      have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 hc a150
                                                                      refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                                                                      refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_102 v hv a61 a137 a66) fun a137 => ?_
                                                                      have a38 : acc7_1 (v 1) := Classical.byContradiction fun hc => cl468 (v 1) (hv 1) a29 hc a137
                                                                      exact (cl237 (v 1) (hv 1) a38 a62).elim
                                                              · have a135 : acc10_0 (v 2) := Classical.byContradiction fun hc => cl163 (v 2) (hv 2) a27 hc
                                                                have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl362 (v 2) (hv 2) hc a117 a27
                                                                have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl415 (v 2) (hv 2) a117 a27 hc
                                                                have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl367 (v 2) (hv 2) a90 a150 hc
                                                                refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_102 v hv a61 a137 a66) fun a137 => ?_
                                                                refine (Classical.em (acc10_2 (v 1))).elim (fun a59 => succ10_120 v hv a55 a59 a135) fun a59 => ?_
                                                                have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl364 (v 1) (hv 1) a59 a137 hc
                                                                refine (Classical.em (acc11_0 (v 0))).elim (fun a136 => succ11_012 v hv a136 a62 a66) fun a136 => ?_
                                                                have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl410 (v 0) (hv 0) a64 hc a136
                                                                refine (Classical.em (acc7_0 (v 1))).elim (fun a113 => succ7_102 v hv a37 a113 a42) fun a113 => ?_
                                                                refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_120 v hv a37 a41 a114) fun a114 => ?_
                                                                have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                                                have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl194 (v 2) (hv 2) a153 hc
                                                                refine (Classical.em (acc5_1 (v 1))).elim (fun a125 => succ5_012 v hv a31 a125 a153) fun a125 => ?_
                                                                refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_102 v hv a124 a32 a153) fun a124 => ?_
                                                                have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl456 (v 1) (hv 1) hc a125 a113
                                                                refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                                have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                                refine (Classical.em (acc8_2 (v 1))).elim (fun a47 => succ8_021 v hv a130 a47 a45) fun a47 => ?_
                                                                have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl356 (v 1) (hv 1) a47 a116 hc
                                                                refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_210 v hv a154 a128 a36) fun a154 => ?_
                                                                have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) a154 a124 hc
                                                                exact succ7_021 v hv a112 a41 a39
                                                          · have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                            have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl351 (v 0) (hv 0) a52 hc a25
                                                            have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl365 (v 0) (hv 0) a58 hc a25
                                                            refine (Classical.em (acc7_1 (v 2))).elim (fun a39 => succ7_021 v hv a112 a41 a39) fun a39 => ?_
                                                            have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl411 (v 2) (hv 2) a117 hc a39
                                                            refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                                                            refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_102 v hv a61 a137 a66) fun a137 => ?_
                                                            have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl364 (v 1) (hv 1) hc a137 a62
                                                            exact succ10_021 v hv a133 a59 a57
                                                        · have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl461 (v 0) (hv 0) a28 a19 hc
                                                          refine (Classical.em (acc7_1 (v 2))).elim (fun a39 => succ7_021 v hv a112 a41 a39) fun a39 => ?_
                                                          have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl149 (v 2) (hv 2) hc a39
                                                          have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl406 (v 2) (hv 2) a117 a39 hc
                                                          have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl411 (v 2) (hv 2) a117 hc a39
                                                          refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_102 v hv a61 a137 a66) fun a137 => ?_
                                                          have a143 : ¬acc15_1 (v 1) := fun hc => cl293 (v 1) (hv 1) a137 hc
                                                          refine (Classical.em (acc7_1 (v 1))).elim (fun a38 => succ7_012 v hv a112 a38 a42) fun a38 => ?_
                                                          have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl410 (v 1) (hv 1) hc a38 a137
                                                          have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl468 (v 1) (hv 1) hc a38 a137
                                                          refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_120 v hv a25 a29 a123) fun a25 => ?_
                                                          have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                          have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl365 (v 0) (hv 0) a58 hc a25
                                                          refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                                                          refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_021 v hv a136 a65 a63) fun a63 => ?_
                                                          have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl453 (v 1) (hv 1) a143 hc a62
                                                          refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                                                          have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl465 (v 2) (hv 2) hc a63 a144
                                                          exact succ10_012 v hv a133 a56 a60
                                                      · have a42 : ¬acc7_2 (v 2) := fun hc => cl89 (v 2) (hv 2) a15 hc
                                                        have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl474 (v 2) (hv 2) hc a15 a111
                                                        refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_012 v hv a130 a44 a48) fun a130 => ?_
                                                        have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl244 (v 0) (hv 0) a130 hc
                                                        refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_102 v hv a43 a131 a48) fun a131 => ?_
                                                        have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) hc a131
                                                        refine (Classical.em (acc6_2 (v 2))).elim (fun a156 => succ6_012 v hv a34 a128 a156) fun a156 => ?_
                                                        exact (cl408 (v 2) (hv 2) a156 a117 a42).elim
                                                    · have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl408 (v 1) (hv 1) hc a116 a41
                                                      have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl218 (v 1) (hv 1) a155 hc
                                                      refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_021 v hv a34 a155 a129) fun a129 => ?_
                                                      refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                                      have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                                      refine (Classical.em (acc8_2 (v 2))).elim (fun a48 => succ8_012 v hv a130 a44 a48) fun a48 => ?_
                                                      have a117 : acc9_0 (v 2) := Classical.byContradiction fun hc => cl356 (v 2) (hv 2) a48 hc a129
                                                      refine (Classical.em (acc9_1 (v 0))).elim (fun a49 => succ9_120 v hv a49 a53 a117) fun a49 => ?_
                                                      refine (Classical.em (acc9_1 (v 1))).elim (fun a50 => succ9_210 v hv a52 a50 a117) fun a50 => ?_
                                                      have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl375 (v 1) (hv 1) a109 hc a50
                                                      have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) hc a109 a50
                                                      refine (Classical.em (acc8_1 (v 2))).elim (fun a45 => succ8_021 v hv a130 a47 a45) fun a45 => ?_
                                                      have a132 : acc8_0 (v 2) := Classical.byContradiction fun hc => cl244 (v 2) (hv 2) hc a45
                                                      refine (Classical.em (acc8_2 (v 0))).elim (fun a46 => succ8_210 v hv a46 a44 a132) fun a46 => ?_
                                                      have a107 : acc2_2 (v 0) := Classical.byContradiction fun hc => cl475 (v 0) (hv 0) a46 hc a49
                                                      refine (Classical.em (acc2_1 (v 2))).elim (fun a18 => succ2_201 v hv a107 a14 a18) fun a18 => ?_
                                                      refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_210 v hv a107 a17 a15) fun a15 => ?_
                                                      have a102 : ¬acc17_1 (v 2) := fun hc => cl97 (v 2) (hv 2) a15 hc
                                                      have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl389 (v 2) (hv 2) a15 hc a18
                                                      refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_012 v hv a97 a101 a150) fun a101 => ?_
                                                      have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl384 (v 1) (hv 1) a146 a101 hc
                                                      have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) hc a18 a102
                                                      refine (Classical.em (acc16_1 (v 0))).elim (fun a94 => succ16_102 v hv a94 a92 a147) fun a94 => ?_
                                                      have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl338 (v 0) (hv 0) hc a94
                                                      refine (Classical.em (acc16_1 (v 1))).elim (fun a95 => succ16_012 v hv a91 a95 a147) fun a95 => ?_
                                                      have a4 : acc0_1 (v 1) := Classical.byContradiction fun hc => cl36 (v 1) (hv 1) hc a95
                                                      refine (Classical.em (acc0_2 (v 2))).elim (fun a110 => succ0_012 v hv a1 a4 a110) fun a110 => ?_
                                                      have a12 : acc1_2 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) a110 hc a15
                                                      exact (cl79 (v 2) (hv 2) a12 a18).elim
                                                  · have a134 : acc10_0 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) a26 hc
                                                    have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl362 (v 1) (hv 1) hc a116 a26
                                                    have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl415 (v 1) (hv 1) a116 a26 hc
                                                    have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl367 (v 1) (hv 1) a89 a149 hc
                                                    refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_120 v hv a61 a65 a138) fun a138 => ?_
                                                    refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_102 v hv a55 a134 a60) fun a60 => ?_
                                                    have a63 : acc11_1 (v 2) := Classical.byContradiction fun hc => cl364 (v 2) (hv 2) a60 a138 hc
                                                    refine (Classical.em (acc11_0 (v 0))).elim (fun a136 => succ11_021 v hv a136 a65 a63) fun a136 => ?_
                                                    have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl251 (v 0) (hv 0) hc a136
                                                    have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl410 (v 0) (hv 0) a64 hc a136
                                                    refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_120 v hv a37 a41 a114) fun a114 => ?_
                                                    have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 a114 hc
                                                    have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl194 (v 2) (hv 2) a153 hc
                                                    refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_102 v hv a124 a32 a153) fun a124 => ?_
                                                    refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_021 v hv a112 a41 a39) fun a112 => ?_
                                                    have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl456 (v 0) (hv 0) hc a124 a112
                                                    refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_201 v hv a154 a35 a129) fun a129 => ?_
                                                    refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_210 v hv a154 a128 a36) fun a128 => ?_
                                                    have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl356 (v 1) (hv 1) hc a116 a128
                                                    refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                                    exact (cl215 (v 2) (hv 2) a129 a132).elim
                                                · have a41 : ¬acc7_2 (v 1) := fun hc => cl89 (v 1) (hv 1) a14 hc
                                                  have a11 : acc1_2 (v 1) := Classical.byContradiction fun hc => cl390 (v 1) (hv 1) a108 hc a14
                                                  have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl474 (v 1) (hv 1) hc a14 a109
                                                  refine (Classical.em (acc1_1 (v 0))).elim (fun a118 => succ1_120 v hv a118 a11 a9) fun a118 => ?_
                                                  have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl77 (v 0) (hv 0) a118 hc
                                                  refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                                  have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl244 (v 2) (hv 2) a132 hc
                                                  refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_021 v hv a130 a47 a45) fun a130 => ?_
                                                  have a127 : acc6_1 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) hc a130
                                                  refine (Classical.em (acc6_2 (v 1))).elim (fun a155 => succ6_120 v hv a127 a155 a36) fun a155 => ?_
                                                  exact (cl408 (v 1) (hv 1) a155 a116 a41).elim
                                              · have a110 : acc0_2 (v 2) := Classical.byContradiction fun hc => cl43 (v 2) (hv 2) hc a9
                                                have a96 : acc16_1 (v 2) := Classical.byContradiction fun hc => cl71 (v 2) (hv 2) a9 hc
                                                have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl72 (v 2) (hv 2) a9 hc
                                                have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl74 (v 2) (hv 2) a9 hc
                                                refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_012 v hv a97 a101 a150) fun a101 => ?_
                                                have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl384 (v 1) (hv 1) a146 a101 hc
                                                have a83 : ¬acc14_1 (v 1) := fun hc => cl392 (v 1) (hv 1) hc a101 a149
                                                have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl413 (v 1) (hv 1) a116 hc a83
                                                refine (Classical.em (acc17_1 (v 0))).elim (fun a100 => succ17_102 v hv a100 a98 a150) fun a100 => ?_
                                                refine (Classical.em (acc16_2 (v 0))).elim (fun a145 => succ16_201 v hv a145 a92 a96) fun a145 => ?_
                                                have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl384 (v 0) (hv 0) a145 a100 hc
                                                refine (Classical.em (acc16_1 (v 1))).elim (fun a95 => succ16_012 v hv a91 a95 a147) fun a95 => ?_
                                                have a4 : acc0_1 (v 1) := Classical.byContradiction fun hc => cl36 (v 1) (hv 1) hc a95
                                                exact succ0_012 v hv a1 a4 a110
                                            · have a106 : acc0_2 (v 0) := Classical.byContradiction fun hc => cl43 (v 0) (hv 0) hc a7
                                              have a107 : acc2_2 (v 0) := Classical.byContradiction fun hc => cl46 (v 0) (hv 0) a7 hc
                                              have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl61 (v 0) (hv 0) a7 hc
                                              have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl69 (v 0) (hv 0) a7 hc
                                              have a145 : acc16_2 (v 0) := Classical.byContradiction fun hc => cl72 (v 0) (hv 0) a7 hc
                                              have a148 : acc17_2 (v 0) := Classical.byContradiction fun hc => cl74 (v 0) (hv 0) a7 hc
                                              refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_012 v hv a133 a56 a60) fun a60 => ?_
                                              refine (Classical.em (acc0_1 (v 1))).elim (fun a4 => succ0_210 v hv a106 a4 a5) fun a4 => ?_
                                              have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl470 (v 1) (hv 1) a4 a146 hc
                                              refine (Classical.em (acc2_1 (v 2))).elim (fun a18 => succ2_201 v hv a107 a14 a18) fun a18 => ?_
                                              have a96 : acc16_1 (v 2) := Classical.byContradiction fun hc => cl104 (v 2) (hv 2) a18 hc
                                              refine (Classical.em (acc16_0 (v 1))).elim (fun a92 => succ16_201 v hv a145 a92 a96) fun a92 => ?_
                                              have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl384 (v 1) (hv 1) a146 hc a92
                                              refine (Classical.em (acc17_2 (v 2))).elim (fun a150 => succ17_012 v hv a97 a101 a150) fun a150 => ?_
                                              refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_210 v hv a148 a101 a99) fun a99 => ?_
                                              have a54 : ¬acc9_2 (v 2) := fun hc => cl278 (v 2) (hv 2) hc a99
                                              have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl388 (v 2) (hv 2) a54 hc a150
                                              refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_201 v hv a148 a98 a102) fun a98 => ?_
                                              have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) a161 hc a98
                                              refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                                              refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                              exact (cl371 (v 2) (hv 2) a60 a144 a87).elim
                                          · have a42 : ¬acc7_2 (v 2) := fun hc => cl12 (v 2) (hv 2) a5 hc
                                            have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl14 (v 2) (hv 2) a5 hc
                                            refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_012 v hv a130 a44 a48) fun a130 => ?_
                                            have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl244 (v 0) (hv 0) a130 hc
                                            refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_102 v hv a43 a131 a48) fun a131 => ?_
                                            have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) hc a131
                                            refine (Classical.em (acc6_2 (v 2))).elim (fun a156 => succ6_012 v hv a34 a128 a156) fun a156 => ?_
                                            refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_210 v hv a154 a128 a36) fun a154 => ?_
                                            have a49 : acc9_1 (v 0) := Classical.byContradiction fun hc => cl403 (v 0) (hv 0) a154 a130 hc
                                            have a117 : acc9_0 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) a156 hc a42
                                            refine (Classical.em (acc9_2 (v 1))).elim (fun a53 => succ9_120 v hv a49 a53 a117) fun a53 => ?_
                                            refine (Classical.em (acc9_1 (v 1))).elim (fun a50 => succ9_210 v hv a52 a50 a117) fun a50 => ?_
                                            have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl403 (v 1) (hv 1) hc a131 a50
                                            exact (cl218 (v 1) (hv 1) a155 a53).elim
                                        · have a11 : acc1_2 (v 1) := Classical.byContradiction fun hc => cl2 (v 1) (hv 1) a3 hc
                                          have a41 : ¬acc7_2 (v 1) := fun hc => cl12 (v 1) (hv 1) a3 hc
                                          have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl14 (v 1) (hv 1) a3 hc
                                          have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl29 (v 1) (hv 1) a3 hc
                                          have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl408 (v 1) (hv 1) hc a116 a41
                                          refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                                          have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                                          refine (Classical.em (acc8_1 (v 2))).elim (fun a45 => succ8_021 v hv a130 a47 a45) fun a45 => ?_
                                          have a120 : acc1_1 (v 2) := Classical.byContradiction fun hc => cl77 (v 2) (hv 2) hc a45
                                          have a132 : acc8_0 (v 2) := Classical.byContradiction fun hc => cl244 (v 2) (hv 2) hc a45
                                          refine (Classical.em (acc8_1 (v 0))).elim (fun a43 => succ8_120 v hv a43 a47 a132) fun a43 => ?_
                                          have a118 : acc1_1 (v 0) := Classical.byContradiction fun hc => cl77 (v 0) (hv 0) hc a43
                                          refine (Classical.em (acc1_0 (v 2))).elim (fun a9 => succ1_120 v hv a118 a11 a9) fun a9 => ?_
                                          have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl72 (v 2) (hv 2) a9 hc
                                          refine (Classical.em (acc16_1 (v 0))).elim (fun a94 => succ16_102 v hv a94 a92 a147) fun a94 => ?_
                                          have a7 : acc1_0 (v 0) := Classical.byContradiction fun hc => cl71 (v 0) (hv 0) hc a94
                                          exact succ1_021 v hv a7 a11 a120
                                      · have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl11 (v 0) (hv 0) a1 hc
                                        have a46 : acc8_2 (v 0) := Classical.byContradiction fun hc => cl14 (v 0) (hv 0) a1 hc
                                        have a49 : ¬acc9_1 (v 0) := fun hc => cl15 (v 0) (hv 0) a1 hc
                                        refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_210 v hv a46 a44 a132) fun a132 => ?_
                                        have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl244 (v 2) (hv 2) a132 hc
                                        refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_201 v hv a46 a131 a45) fun a131 => ?_
                                        have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) hc a131
                                        refine (Classical.em (acc6_2 (v 2))).elim (fun a156 => succ6_012 v hv a34 a128 a156) fun a156 => ?_
                                        refine (Classical.em (acc6_2 (v 0))).elim (fun a154 => succ6_210 v hv a154 a128 a36) fun a154 => ?_
                                        have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl401 (v 0) (hv 0) a154 hc a49
                                        have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl403 (v 0) (hv 0) a154 hc a49
                                        refine (Classical.em (acc8_2 (v 1))).elim (fun a47 => succ8_021 v hv a130 a47 a45) fun a47 => ?_
                                        have a50 : acc9_1 (v 1) := Classical.byContradiction fun hc => cl355 (v 1) (hv 1) a47 hc a131
                                        refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_210 v hv a52 a50 a117) fun a117 => ?_
                                        have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) a156 a117 hc
                                        refine (Classical.em (acc7_1 (v 1))).elim (fun a38 => succ7_012 v hv a112 a38 a42) fun a38 => ?_
                                        refine (Classical.em (acc7_0 (v 1))).elim (fun a113 => succ7_102 v hv a37 a113 a42) fun a113 => ?_
                                        have a152 : acc5_2 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) a23 a113 hc
                                        exact (cl194 (v 1) (hv 1) a152 a38).elim
                                  · have a126 : acc5_1 (v 2) := Classical.byContradiction fun hc => cl192 (v 2) (hv 2) hc a36
                                    have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl201 (v 2) (hv 2) a36 hc
                                    have a51 : acc9_1 (v 2) := Classical.byContradiction fun hc => cl205 (v 2) (hv 2) a36 hc
                                    have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl212 (v 2) (hv 2) a36 hc
                                    refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_021 v hv a97 a149 a102) fun a149 => ?_
                                    refine (Classical.em (acc5_2 (v 1))).elim (fun a152 => succ5_021 v hv a31 a152 a126) fun a152 => ?_
                                    have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) a23 hc a152
                                    refine (Classical.em (acc7_1 (v 0))).elim (fun a37 => succ7_102 v hv a37 a113 a42) fun a37 => ?_
                                    have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl149 (v 0) (hv 0) hc a37
                                    have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl410 (v 0) (hv 0) a64 a37 hc
                                    have a115 : acc9_0 (v 0) := Classical.byContradiction fun hc => cl411 (v 0) (hv 0) hc a64 a37
                                    refine (Classical.em (acc9_2 (v 1))).elim (fun a53 => succ9_021 v hv a115 a53 a51) fun a53 => ?_
                                    have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl342 (v 1) (hv 1) a53 hc a149
                                    refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_021 v hv a136 a65 a63) fun a63 => ?_
                                    refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_120 v hv a61 a65 a138) fun a138 => ?_
                                    have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl364 (v 2) (hv 2) hc a138 a63
                                    refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_102 v hv a55 a134 a60) fun a134 => ?_
                                    have a26 : acc4_1 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) hc a134
                                    refine (Classical.em (acc4_2 (v 2))).elim (fun a30 => succ4_012 v hv a121 a26 a30) fun a30 => ?_
                                    have a135 : acc10_0 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) a30 hc a63
                                    exact (cl467 (v 2) (hv 2) a135 a30 a138).elim
                                · have a125 : acc5_1 (v 1) := Classical.byContradiction fun hc => cl192 (v 1) (hv 1) hc a35
                                  have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl200 (v 1) (hv 1) a35 hc
                                  have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl201 (v 1) (hv 1) a35 hc
                                  have a50 : acc9_1 (v 1) := Classical.byContradiction fun hc => cl205 (v 1) (hv 1) a35 hc
                                  have a149 : ¬acc17_2 (v 1) := fun hc => cl213 (v 1) (hv 1) a35 hc
                                  refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_210 v hv a52 a50 a117) fun a117 => ?_
                                  refine (Classical.em (acc6_2 (v 2))).elim (fun a156 => succ6_012 v hv a34 a128 a156) fun a156 => ?_
                                  have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) a156 a117 hc
                                  have a51 : acc9_1 (v 2) := Classical.byContradiction fun hc => cl242 (v 2) (hv 2) a42 hc
                                  refine (Classical.em (acc5_2 (v 2))).elim (fun a153 => succ5_012 v hv a31 a125 a153) fun a153 => ?_
                                  have a114 : acc7_0 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 hc a153
                                  refine (Classical.em (acc7_1 (v 0))).elim (fun a37 => succ7_120 v hv a37 a41 a114) fun a37 => ?_
                                  have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl149 (v 0) (hv 0) hc a37
                                  have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl410 (v 0) (hv 0) a64 a37 hc
                                  have a115 : acc9_0 (v 0) := Classical.byContradiction fun hc => cl411 (v 0) (hv 0) hc a64 a37
                                  refine (Classical.em (acc9_2 (v 1))).elim (fun a53 => succ9_021 v hv a115 a53 a51) fun a53 => ?_
                                  have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl342 (v 1) (hv 1) a53 hc a149
                                  refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_021 v hv a136 a65 a63) fun a63 => ?_
                                  refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_120 v hv a61 a65 a138) fun a138 => ?_
                                  have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl364 (v 2) (hv 2) hc a138 a63
                                  refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_102 v hv a55 a134 a60) fun a134 => ?_
                                  have a26 : acc4_1 (v 1) := Classical.byContradiction fun hc => cl163 (v 1) (hv 1) hc a134
                                  refine (Classical.em (acc4_2 (v 2))).elim (fun a30 => succ4_012 v hv a121 a26 a30) fun a30 => ?_
                                  have a135 : acc10_0 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) a30 hc a63
                                  exact (cl467 (v 2) (hv 2) a135 a30 a138).elim
                              · have a124 : acc5_1 (v 0) := Classical.byContradiction fun hc => cl192 (v 0) (hv 0) hc a34
                                have a40 : acc7_2 (v 0) := Classical.byContradiction fun hc => cl201 (v 0) (hv 0) a34 hc
                                have a49 : acc9_1 (v 0) := Classical.byContradiction fun hc => cl205 (v 0) (hv 0) a34 hc
                                have a82 : acc14_1 (v 0) := Classical.byContradiction fun hc => cl208 (v 0) (hv 0) a34 hc
                                have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl212 (v 0) (hv 0) a34 hc
                                have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl405 (v 0) (hv 0) a64 a34 hc
                                refine (Classical.em (acc5_2 (v 1))).elim (fun a152 => succ5_120 v hv a124 a152 a33) fun a152 => ?_
                                have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) a23 hc a152
                                refine (Classical.em (acc7_2 (v 2))).elim (fun a42 => succ7_102 v hv a37 a113 a42) fun a42 => ?_
                                refine (Classical.em (acc7_1 (v 2))).elim (fun a39 => succ7_201 v hv a40 a113 a39) fun a39 => ?_
                                have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl426 (v 2) (hv 2) a39 hc a42
                                have a114 : acc7_0 (v 2) := Classical.byContradiction fun hc => cl229 (v 2) (hv 2) hc a138
                                refine (Classical.em (acc11_2 (v 1))).elim (fun a65 => succ11_120 v hv a61 a65 a138) fun a65 => ?_
                                have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl298 (v 1) (hv 1) a65 hc
                                refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_102 v hv a82 a80 a162) fun a162 => ?_
                                refine (Classical.em (acc7_2 (v 1))).elim (fun a41 => succ7_120 v hv a37 a41 a114) fun a41 => ?_
                                refine (Classical.em (acc7_1 (v 1))).elim (fun a38 => succ7_210 v hv a40 a38 a114) fun a38 => ?_
                                have a116 : acc9_0 (v 1) := Classical.byContradiction fun hc => cl406 (v 1) (hv 1) hc a38 a41
                                have a137 : acc11_0 (v 1) := Classical.byContradiction fun hc => cl410 (v 1) (hv 1) a65 a38 hc
                                refine (Classical.em (acc11_2 (v 2))).elim (fun a66 => succ11_102 v hv a61 a137 a66) fun a66 => ?_
                                refine (Classical.em (acc9_2 (v 2))).elim (fun a54 => succ9_102 v hv a49 a116 a54) fun a54 => ?_
                                have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 a66 hc
                                refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_102 v hv a100 a98 a150) fun a98 => ?_
                                have a53 : ¬acc9_2 (v 1) := fun hc => cl278 (v 1) (hv 1) hc a98
                                have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl477 (v 1) (hv 1) a65 hc a98
                                refine (Classical.em (acc15_2 (v 2))).elim (fun a90 => succ15_012 v hv a85 a143 a90) fun a90 => ?_
                                have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) a162 a90 hc
                                refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_120 v hv a100 a149 a99) fun a149 => ?_
                                exact (cl342 (v 1) (hv 1) a53 a65 a149).elim
                        · have a1 : acc0_0 (v 0) := Classical.byContradiction fun hc => cl16 (v 0) (hv 0) hc a52
                          have a154 : ¬acc6_2 (v 0) := fun hc => cl218 (v 0) (hv 0) hc a52
                          have a46 : ¬acc8_2 (v 0) := fun hc => cl255 (v 0) (hv 0) hc a52
                          have a148 : acc17_2 (v 0) := Classical.byContradiction fun hc => cl342 (v 0) (hv 0) a52 a64 hc
                          have a19 : ¬acc3_1 (v 0) := fun hc => cl448 (v 0) (hv 0) hc a52 a64
                          have a121 : acc4_0 (v 0) := Classical.byContradiction fun hc => cl142 (v 0) (hv 0) a19 hc
                          have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl461 (v 0) (hv 0) a28 a19 hc
                          have a34 : acc6_0 (v 0) := Classical.byContradiction fun hc => cl213 (v 0) (hv 0) hc a148
                          have a115 : acc9_0 (v 0) := Classical.byContradiction fun hc => cl267 (v 0) (hv 0) hc a148
                          by_cases a3 : acc0_0 (v 1)
                          · by_cases a5 : acc0_0 (v 2)
                            · by_cases a7 : acc1_0 (v 0)
                              · by_cases a8 : acc1_0 (v 1)
                                · by_cases a9 : acc1_0 (v 2)
                                  · by_cases a11 : acc1_2 (v 1)
                                    · have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl79 (v 1) (hv 1) a11 hc
                                      have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl84 (v 1) (hv 1) a11 hc
                                      refine (Classical.em (acc1_1 (v 0))).elim (fun a118 => succ1_120 v hv a118 a11 a9) fun a118 => ?_
                                      have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl77 (v 0) (hv 0) a118 hc
                                      have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl354 (v 0) (hv 0) a46 a118 hc
                                      refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_012 v hv a13 a17 a111) fun a111 => ?_
                                      refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_201 v hv a148 a98 a102) fun a102 => ?_
                                      have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl394 (v 2) (hv 2) a111 a102 hc
                                      have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl102 (v 2) (hv 2) a18 hc
                                      refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_021 v hv a13 a109 a18) fun a109 => ?_
                                      have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl110 (v 1) (hv 1) a109 hc
                                      refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_210 v hv a148 a101 a99) fun a101 => ?_
                                      have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl376 (v 1) (hv 1) a109 hc a101
                                      refine (Classical.em (acc9_1 (v 2))).elim (fun a51 => succ9_021 v hv a115 a53 a51) fun a51 => ?_
                                      have a42 : ¬acc7_2 (v 2) := fun hc => cl242 (v 2) (hv 2) hc a51
                                      have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) hc a111 a51
                                      refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_012 v hv a130 a44 a48) fun a130 => ?_
                                      refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_102 v hv a43 a131 a48) fun a131 => ?_
                                      have a128 : acc6_1 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) hc a131
                                      refine (Classical.em (acc6_2 (v 2))).elim (fun a156 => succ6_012 v hv a34 a128 a156) fun a156 => ?_
                                      have a117 : acc9_0 (v 2) := Classical.byContradiction fun hc => cl408 (v 2) (hv 2) a156 hc a42
                                      refine (Classical.em (acc9_1 (v 0))).elim (fun a49 => succ9_120 v hv a49 a53 a117) fun a49 => ?_
                                      exact (cl355 (v 0) (hv 0) a46 a49 a130).elim
                                    · by_cases a12 : acc1_2 (v 2)
                                      · have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl79 (v 2) (hv 2) a12 hc
                                        have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl84 (v 2) (hv 2) a12 hc
                                        refine (Classical.em (acc1_1 (v 0))).elim (fun a118 => succ1_102 v hv a118 a8 a12) fun a118 => ?_
                                        have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl77 (v 0) (hv 0) a118 hc
                                        have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl354 (v 0) (hv 0) a46 a118 hc
                                        refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_021 v hv a13 a109 a18) fun a109 => ?_
                                        have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl473 (v 1) (hv 1) a11 hc a109
                                        refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_201 v hv a107 a14 a18) fun a107 => ?_
                                        have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl376 (v 0) (hv 0) a107 a52 hc
                                        have a49 : acc9_1 (v 0) := Classical.byContradiction fun hc => cl475 (v 0) (hv 0) a46 a107 hc
                                        refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_120 v hv a100 a149 a99) fun a149 => ?_
                                        have a146 : ¬acc16_2 (v 1) := fun hc => cl341 (v 1) (hv 1) hc a149
                                        refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_210 v hv a148 a101 a99) fun a101 => ?_
                                        have a83 : ¬acc14_1 (v 1) := fun hc => cl392 (v 1) (hv 1) hc a101 a149
                                        have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) hc a146 a83
                                        refine (Classical.em (acc17_2 (v 2))).elim (fun a150 => succ17_102 v hv a100 a98 a150) fun a150 => ?_
                                        refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_201 v hv a148 a98 a102) fun a102 => ?_
                                        have a36 : acc6_0 (v 2) := Classical.byContradiction fun hc => cl212 (v 2) (hv 2) hc a102
                                        have a54 : acc9_2 (v 2) := Classical.byContradiction fun hc => cl388 (v 2) (hv 2) hc a102 a150
                                        refine (Classical.em (acc9_1 (v 1))).elim (fun a50 => succ9_012 v hv a115 a50 a54) fun a50 => ?_
                                        refine (Classical.em (acc9_0 (v 1))).elim (fun a116 => succ9_102 v hv a49 a116 a54) fun a116 => ?_
                                        have a41 : ¬acc7_2 (v 1) := fun hc => cl242 (v 1) (hv 1) hc a50
                                        have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) hc a109 a50
                                        refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                        have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl244 (v 2) (hv 2) a132 hc
                                        refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_021 v hv a130 a47 a45) fun a130 => ?_
                                        have a127 : acc6_1 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) hc a130
                                        refine (Classical.em (acc6_2 (v 1))).elim (fun a155 => succ6_120 v hv a127 a155 a36) fun a155 => ?_
                                        exact (cl408 (v 1) (hv 1) a155 a116 a41).elim
                                      · by_cases a94 : acc16_1 (v 0)
                                        · by_cases a95 : acc16_1 (v 1)
                                          · by_cases a96 : acc16_1 (v 2)
                                            · by_cases a146 : acc16_2 (v 1)
                                              · refine (Classical.em (acc16_0 (v 0))).elim (fun a91 => succ16_021 v hv a91 a146 a96) fun a91 => ?_
                                                refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_120 v hv a94 a146 a93) fun a93 => ?_
                                                have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl332 (v 2) (hv 2) hc a93
                                                refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_021 v hv a79 a161 a84) fun a161 => ?_
                                                have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl387 (v 1) (hv 1) a146 a161 hc
                                                have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl329 (v 1) (hv 1) hc a98
                                                refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_201 v hv a148 a98 a102) fun a102 => ?_
                                                have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl392 (v 2) (hv 2) a84 a102 hc
                                                refine (Classical.em (acc17_1 (v 0))).elim (fun a100 => succ17_102 v hv a100 a98 a150) fun a100 => ?_
                                                have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl385 (v 0) (hv 0) hc a100 a91
                                                exact succ14_201 v hv a160 a80 a84
                                              · by_cases a14 : acc2_0 (v 1)
                                                · by_cases a18 : acc2_1 (v 2)
                                                  · have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl102 (v 2) (hv 2) a18 hc
                                                    refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_201 v hv a107 a14 a18) fun a107 => ?_
                                                    have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl110 (v 0) (hv 0) a107 hc
                                                    have a100 : acc17_1 (v 0) := Classical.byContradiction fun hc => cl376 (v 0) (hv 0) a107 a52 hc
                                                    have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl474 (v 0) (hv 0) a46 hc a107
                                                    have a49 : acc9_1 (v 0) := Classical.byContradiction fun hc => cl475 (v 0) (hv 0) a46 a107 hc
                                                    refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_021 v hv a13 a109 a18) fun a109 => ?_
                                                    refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_120 v hv a100 a149 a99) fun a149 => ?_
                                                    refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_210 v hv a148 a101 a99) fun a101 => ?_
                                                    have a83 : ¬acc14_1 (v 1) := fun hc => cl392 (v 1) (hv 1) hc a101 a149
                                                    have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) hc a146 a83
                                                    refine (Classical.em (acc17_2 (v 2))).elim (fun a150 => succ17_102 v hv a100 a98 a150) fun a150 => ?_
                                                    refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_201 v hv a148 a98 a102) fun a102 => ?_
                                                    have a36 : acc6_0 (v 2) := Classical.byContradiction fun hc => cl212 (v 2) (hv 2) hc a102
                                                    have a54 : acc9_2 (v 2) := Classical.byContradiction fun hc => cl388 (v 2) (hv 2) hc a102 a150
                                                    refine (Classical.em (acc9_1 (v 1))).elim (fun a50 => succ9_012 v hv a115 a50 a54) fun a50 => ?_
                                                    refine (Classical.em (acc9_0 (v 1))).elim (fun a116 => succ9_102 v hv a49 a116 a54) fun a116 => ?_
                                                    have a41 : ¬acc7_2 (v 1) := fun hc => cl242 (v 1) (hv 1) hc a50
                                                    have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) hc a109 a50
                                                    refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                                    have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl244 (v 2) (hv 2) a132 hc
                                                    refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_021 v hv a130 a47 a45) fun a130 => ?_
                                                    have a127 : acc6_1 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) hc a130
                                                    refine (Classical.em (acc6_2 (v 1))).elim (fun a155 => succ6_120 v hv a127 a155 a36) fun a155 => ?_
                                                    exact (cl408 (v 1) (hv 1) a155 a116 a41).elim
                                                  · by_cases a10 : acc1_2 (v 0)
                                                    · have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl79 (v 0) (hv 0) a10 hc
                                                      have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl83 (v 0) (hv 0) a10 hc
                                                      have a97 : acc17_0 (v 0) := Classical.byContradiction fun hc => cl84 (v 0) (hv 0) a10 hc
                                                      have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl455 (v 0) (hv 0) a16 a52 hc
                                                      refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_102 v hv a16 a14 a111) fun a111 => ?_
                                                      have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl394 (v 2) (hv 2) a111 hc a18
                                                      refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_021 v hv a97 a149 a102) fun a149 => ?_
                                                      refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_201 v hv a148 a98 a102) fun a98 => ?_
                                                      have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) a98 a146 hc
                                                      have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl392 (v 1) (hv 1) a83 hc a149
                                                      refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                                                      refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_210 v hv a148 a101 a99) fun a99 => ?_
                                                      have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) a162 hc a99
                                                      have a147 : ¬acc16_2 (v 2) := fun hc => cl387 (v 2) (hv 2) hc a162 a99
                                                      have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl452 (v 2) (hv 2) a99 a147 hc
                                                      refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_021 v hv a79 a161 a84) fun a161 => ?_
                                                      have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) a161 hc a98
                                                      have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl367 (v 1) (hv 1) a89 a149 hc
                                                      refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                                                      have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl287 (v 2) (hv 2) hc a144
                                                      have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl477 (v 2) (hv 2) hc a144 a99
                                                      refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                                                      have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl154 (v 1) (hv 1) hc a62
                                                      refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_021 v hv a136 a65 a63) fun a63 => ?_
                                                      have a39 : ¬acc7_1 (v 2) := fun hc => cl237 (v 2) (hv 2) hc a63
                                                      refine (Classical.em (acc15_1 (v 1))).elim (fun a143 => succ15_012 v hv a85 a143 a90) fun a143 => ?_
                                                      have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) hc a62 a143
                                                      refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_021 v hv a133 a59 a57) fun a133 => ?_
                                                      have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) hc a133
                                                      have a61 : acc11_1 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 a133 hc
                                                      refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_120 v hv a61 a65 a138) fun a138 => ?_
                                                      have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl468 (v 2) (hv 2) hc a39 a138
                                                      exact succ4_102 v hv a25 a122 a30
                                                    · by_cases a15 : acc2_0 (v 2)
                                                      · by_cases a16 : acc2_1 (v 0)
                                                        · have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl101 (v 0) (hv 0) a16 hc
                                                          have a97 : acc17_0 (v 0) := Classical.byContradiction fun hc => cl102 (v 0) (hv 0) a16 hc
                                                          have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl455 (v 0) (hv 0) a16 a52 hc
                                                          refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_102 v hv a16 a14 a111) fun a111 => ?_
                                                          have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl394 (v 2) (hv 2) a111 hc a18
                                                          refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_021 v hv a97 a149 a102) fun a149 => ?_
                                                          refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_201 v hv a148 a98 a102) fun a98 => ?_
                                                          have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) a98 a146 hc
                                                          have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl392 (v 1) (hv 1) a83 hc a149
                                                          refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                                                          refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_210 v hv a148 a101 a99) fun a99 => ?_
                                                          have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) a162 hc a99
                                                          have a147 : ¬acc16_2 (v 2) := fun hc => cl387 (v 2) (hv 2) hc a162 a99
                                                          have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl452 (v 2) (hv 2) a99 a147 hc
                                                          refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_021 v hv a79 a161 a84) fun a161 => ?_
                                                          have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) a161 hc a98
                                                          have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl367 (v 1) (hv 1) a89 a149 hc
                                                          refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                                                          have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl287 (v 2) (hv 2) hc a144
                                                          have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl477 (v 2) (hv 2) hc a144 a99
                                                          refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                                                          have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl154 (v 1) (hv 1) hc a62
                                                          refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_021 v hv a136 a65 a63) fun a63 => ?_
                                                          have a39 : ¬acc7_1 (v 2) := fun hc => cl237 (v 2) (hv 2) hc a63
                                                          refine (Classical.em (acc15_1 (v 1))).elim (fun a143 => succ15_012 v hv a85 a143 a90) fun a143 => ?_
                                                          have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) hc a62 a143
                                                          refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_021 v hv a133 a59 a57) fun a133 => ?_
                                                          have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) hc a133
                                                          have a61 : acc11_1 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 a133 hc
                                                          refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_120 v hv a61 a65 a138) fun a138 => ?_
                                                          have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl468 (v 2) (hv 2) hc a39 a138
                                                          exact succ4_102 v hv a25 a122 a30
                                                        · by_cases a17 : acc2_1 (v 1)
                                                          · have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl102 (v 1) (hv 1) a17 hc
                                                            refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_210 v hv a107 a17 a15) fun a107 => ?_
                                                            have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl473 (v 0) (hv 0) a10 hc a107
                                                            refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_012 v hv a13 a17 a111) fun a111 => ?_
                                                            have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl394 (v 2) (hv 2) a111 hc a18
                                                            exact succ17_201 v hv a148 a98 a102
                                                          · have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) a146 a17 hc
                                                            refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_210 v hv a148 a101 a99) fun a99 => ?_
                                                            have a54 : ¬acc9_2 (v 2) := fun hc => cl278 (v 2) (hv 2) hc a99
                                                            by_cases a21 : acc3_1 (v 2)
                                                            · have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl140 (v 2) (hv 2) a21 hc
                                                              have a27 : acc4_1 (v 2) := Classical.byContradiction fun hc => cl368 (v 2) (hv 2) a21 hc a54
                                                              have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl448 (v 2) (hv 2) a21 a54 hc
                                                              have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl454 (v 2) (hv 2) a21 a54 hc
                                                              refine (Classical.em (acc3_2 (v 1))).elim (fun a23 => succ3_021 v hv a103 a23 a21) fun a23 => ?_
                                                              have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl424 (v 2) (hv 2) a42 a99 hc
                                                              refine (Classical.em (acc7_1 (v 1))).elim (fun a38 => succ7_012 v hv a112 a38 a42) fun a38 => ?_
                                                              have a152 : ¬acc5_2 (v 1) := fun hc => cl194 (v 1) (hv 1) hc a38
                                                              have a113 : acc7_0 (v 1) := Classical.byContradiction fun hc => cl457 (v 1) (hv 1) a23 hc a152
                                                              refine (Classical.em (acc7_1 (v 0))).elim (fun a37 => succ7_102 v hv a37 a113 a42) fun a37 => ?_
                                                              have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl410 (v 0) (hv 0) a64 a37 hc
                                                              refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                                                              have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl337 (v 2) (hv 2) a90 hc
                                                              refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_201 v hv a148 a98 a102) fun a98 => ?_
                                                              have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) a98 a146 hc
                                                              refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                                                              have a147 : ¬acc16_2 (v 2) := fun hc => cl387 (v 2) (hv 2) hc a162 a99
                                                              have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl452 (v 2) (hv 2) a99 a147 hc
                                                              refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_021 v hv a79 a161 a84) fun a161 => ?_
                                                              have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) a161 hc a98
                                                              refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_021 v hv a121 a29 a27) fun a29 => ?_
                                                              have a134 : acc10_0 (v 1) := Classical.byContradiction fun hc => cl414 (v 1) (hv 1) a29 hc a62
                                                              have a137 : acc11_0 (v 1) := Classical.byContradiction fun hc => cl467 (v 1) (hv 1) a134 a29 hc
                                                              refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_102 v hv a61 a137 a66) fun a61 => ?_
                                                              have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 hc a61
                                                              have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl459 (v 0) (hv 0) hc a64 a61
                                                              refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                              refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                              have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                              refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_021 v hv a73 a158 a78) fun a158 => ?_
                                                              have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 a158 hc
                                                              refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_120 v hv a139 a71 a69) fun a139 => ?_
                                                              have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 a139 hc
                                                              refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                                                              have a72 : acc12_2 (v 2) := Classical.byContradiction fun hc => cl418 (v 2) (hv 2) a144 hc a87
                                                              refine (Classical.em (acc12_1 (v 1))).elim (fun a140 => succ12_012 v hv a67 a140 a72) fun a140 => ?_
                                                              have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl464 (v 1) (hv 1) hc a140 a86
                                                              exact succ10_021 v hv a133 a59 a57
                                                            · have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl142 (v 2) (hv 2) a21 hc
                                                              by_cases a38 : acc7_1 (v 1)
                                                              · have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl237 (v 1) (hv 1) a38 hc
                                                                have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl240 (v 1) (hv 1) a38 hc
                                                                refine (Classical.em (acc7_2 (v 2))).elim (fun a42 => succ7_012 v hv a112 a38 a42) fun a42 => ?_
                                                                have a114 : acc7_0 (v 2) := Classical.byContradiction fun hc => cl349 (v 2) (hv 2) hc a42 a21
                                                                refine (Classical.em (acc7_2 (v 0))).elim (fun a40 => succ7_210 v hv a40 a38 a114) fun a40 => ?_
                                                                have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl466 (v 0) (hv 0) a40 a52 hc
                                                                refine (Classical.em (acc11_2 (v 2))).elim (fun a66 => succ11_012 v hv a136 a62 a66) fun a66 => ?_
                                                                have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl342 (v 2) (hv 2) a54 a66 hc
                                                                refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_012 v hv a97 a101 a150) fun a97 => ?_
                                                                have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl477 (v 0) (hv 0) a64 hc a97
                                                                refine (Classical.em (acc15_2 (v 2))).elim (fun a90 => succ15_102 v hv a142 a86 a90) fun a90 => ?_
                                                                have a162 : acc14_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) hc a90 a99
                                                                refine (Classical.em (acc14_1 (v 1))).elim (fun a83 => succ14_012 v hv a79 a83 a162) fun a83 => ?_
                                                                have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) a83 hc
                                                                have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) hc a146 a83
                                                                refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_201 v hv a148 a98 a102) fun a102 => ?_
                                                                have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) hc a18 a102
                                                                exact succ16_102 v hv a94 a92 a147
                                                              · have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl149 (v 1) (hv 1) hc a38
                                                                by_cases a47 : acc8_2 (v 1)
                                                                · have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl260 (v 1) (hv 1) a47 hc
                                                                  have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl262 (v 1) (hv 1) a47 hc
                                                                  refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_201 v hv a148 a98 a102) fun a102 => ?_
                                                                  have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) hc a18 a102
                                                                  have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl388 (v 2) (hv 2) a54 a102 hc
                                                                  refine (Classical.em (acc17_1 (v 0))).elim (fun a100 => succ17_102 v hv a100 a98 a150) fun a100 => ?_
                                                                  have a145 : acc16_2 (v 0) := Classical.byContradiction fun hc => cl379 (v 0) (hv 0) hc a16 a100
                                                                  refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_210 v hv a145 a95 a93) fun a93 => ?_
                                                                  have a162 : acc14_2 (v 2) := Classical.byContradiction fun hc => cl385 (v 2) (hv 2) hc a102 a93
                                                                  refine (Classical.em (acc14_1 (v 0))).elim (fun a82 => succ14_102 v hv a82 a80 a162) fun a82 => ?_
                                                                  have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) a82 hc
                                                                  exact succ16_012 v hv a91 a95 a147
                                                                · by_cases a53 : acc9_2 (v 1)
                                                                  · have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl276 (v 1) (hv 1) a53 hc
                                                                    have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl278 (v 1) (hv 1) a53 hc
                                                                    refine (Classical.em (acc9_1 (v 2))).elim (fun a51 => succ9_021 v hv a115 a53 a51) fun a51 => ?_
                                                                    have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl479 (v 2) (hv 2) a51 a18 hc
                                                                    refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_012 v hv a97 a101 a150) fun a97 => ?_
                                                                    refine (Classical.em (acc17_1 (v 0))).elim (fun a100 => succ17_102 v hv a100 a98 a150) fun a100 => ?_
                                                                    have a145 : acc16_2 (v 0) := Classical.byContradiction fun hc => cl379 (v 0) (hv 0) hc a16 a100
                                                                    have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl387 (v 0) (hv 0) a145 hc a97
                                                                    refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_210 v hv a145 a95 a93) fun a93 => ?_
                                                                    have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl332 (v 2) (hv 2) hc a93
                                                                    exact succ14_201 v hv a160 a80 a84
                                                                  · by_cases a83 : acc14_1 (v 1)
                                                                    · refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                                                                      have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) a162 hc a99
                                                                      have a147 : ¬acc16_2 (v 2) := fun hc => cl387 (v 2) (hv 2) hc a162 a99
                                                                      have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) a147 a18 hc
                                                                      have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl452 (v 2) (hv 2) a99 a147 hc
                                                                      refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_021 v hv a79 a161 a84) fun a161 => ?_
                                                                      refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_201 v hv a148 a98 a102) fun a98 => ?_
                                                                      have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) a161 hc a98
                                                                      by_cases a20 : acc3_1 (v 1)
                                                                      · have a26 : acc4_1 (v 1) := Classical.byContradiction fun hc => cl368 (v 1) (hv 1) a20 hc a53
                                                                        have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl448 (v 1) (hv 1) a20 a53 hc
                                                                        have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl454 (v 1) (hv 1) a20 a53 hc
                                                                        refine (Classical.em (acc3_2 (v 2))).elim (fun a24 => succ3_012 v hv a103 a20 a24) fun a24 => ?_
                                                                        refine (Classical.em (acc7_1 (v 2))).elim (fun a39 => succ7_021 v hv a112 a41 a39) fun a39 => ?_
                                                                        have a153 : ¬acc5_2 (v 2) := fun hc => cl194 (v 2) (hv 2) hc a39
                                                                        have a114 : acc7_0 (v 2) := Classical.byContradiction fun hc => cl457 (v 2) (hv 2) a24 hc a153
                                                                        refine (Classical.em (acc7_1 (v 0))).elim (fun a37 => succ7_120 v hv a37 a41 a114) fun a37 => ?_
                                                                        have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl410 (v 0) (hv 0) a64 a37 hc
                                                                        refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_021 v hv a136 a65 a63) fun a63 => ?_
                                                                        refine (Classical.em (acc4_2 (v 2))).elim (fun a30 => succ4_012 v hv a121 a26 a30) fun a30 => ?_
                                                                        have a135 : acc10_0 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) a30 hc a63
                                                                        have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl467 (v 2) (hv 2) a135 a30 hc
                                                                        refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_120 v hv a61 a65 a138) fun a61 => ?_
                                                                        have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 hc a61
                                                                        have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl459 (v 0) (hv 0) hc a64 a61
                                                                        refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                                        refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                                        have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                        refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_021 v hv a73 a158 a78) fun a158 => ?_
                                                                        have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 a158 hc
                                                                        refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_120 v hv a139 a71 a69) fun a139 => ?_
                                                                        have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 a139 hc
                                                                        refine (Classical.em (acc15_1 (v 1))).elim (fun a143 => succ15_012 v hv a85 a143 a90) fun a143 => ?_
                                                                        refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                                                                        have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl287 (v 2) (hv 2) hc a144
                                                                        have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl459 (v 2) (hv 2) a144 hc a63
                                                                        refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                                                                        have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) hc a62 a143
                                                                        exact succ10_021 v hv a133 a59 a57
                                                                      · by_cases a37 : acc7_1 (v 0)
                                                                        · have a61 : acc11_1 (v 0) := Classical.byContradiction fun hc => cl237 (v 0) (hv 0) a37 hc
                                                                          have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl240 (v 0) (hv 0) a37 hc
                                                                          refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                                                                          have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl477 (v 2) (hv 2) hc a144 a99
                                                                          refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_102 v hv a61 a137 a66) fun a137 => ?_
                                                                          have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl282 (v 1) (hv 1) hc a137
                                                                          have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl410 (v 1) (hv 1) hc a38 a137
                                                                          have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl468 (v 1) (hv 1) hc a38 a137
                                                                          refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_120 v hv a25 a29 a123) fun a25 => ?_
                                                                          have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                                          have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl365 (v 0) (hv 0) a58 hc a25
                                                                          refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_021 v hv a136 a65 a63) fun a63 => ?_
                                                                          have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl465 (v 2) (hv 2) hc a63 a144
                                                                          exact succ10_012 v hv a133 a56 a60
                                                                        · have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl410 (v 0) (hv 0) a64 a37 hc
                                                                          by_cases a39 : acc7_1 (v 2)
                                                                          · have a63 : acc11_1 (v 2) := Classical.byContradiction fun hc => cl237 (v 2) (hv 2) a39 hc
                                                                            have a87 : acc15_0 (v 2) := Classical.byContradiction fun hc => cl240 (v 2) (hv 2) a39 hc
                                                                            refine (Classical.em (acc15_1 (v 0))).elim (fun a142 => succ15_120 v hv a142 a89 a87) fun a142 => ?_
                                                                            have a97 : acc17_0 (v 0) := Classical.byContradiction fun hc => cl477 (v 0) (hv 0) a64 a142 hc
                                                                            refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_021 v hv a97 a149 a102) fun a149 => ?_
                                                                            have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl342 (v 1) (hv 1) a53 hc a149
                                                                            exact succ11_021 v hv a136 a65 a63
                                                                          · by_cases a44 : acc8_1 (v 1)
                                                                            · by_cases a45 : acc8_1 (v 2)
                                                                              · by_cases a50 : acc9_1 (v 1)
                                                                                · by_cases a51 : acc9_1 (v 2)
                                                                                  · by_cases a55 : acc10_1 (v 0)
                                                                                    · by_cases a56 : acc10_1 (v 1)
                                                                                      · by_cases a29 : acc4_2 (v 1)
                                                                                        · have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl166 (v 1) (hv 1) a29 hc
                                                                                          refine (Classical.em (acc4_1 (v 2))).elim (fun a27 => succ4_021 v hv a121 a29 a27) fun a27 => ?_
                                                                                          refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_120 v hv a25 a29 a123) fun a25 => ?_
                                                                                          have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                                                          refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_012 v hv a133 a56 a60) fun a60 => ?_
                                                                                          have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl365 (v 2) (hv 2) a60 hc a27
                                                                                          refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_120 v hv a61 a65 a138) fun a61 => ?_
                                                                                          have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl459 (v 0) (hv 0) hc a64 a61
                                                                                          refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                                                          refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                                                          have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                                          have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                          refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_021 v hv a67 a71 a141) fun a71 => ?_
                                                                                          have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 hc a71
                                                                                          exact succ13_021 v hv a73 a158 a78
                                                                                        · have a137 : acc11_0 (v 1) := Classical.byContradiction fun hc => cl468 (v 1) (hv 1) a29 a38 hc
                                                                                          by_cases a30 : acc4_2 (v 2)
                                                                                          · have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl166 (v 2) (hv 2) a30 hc
                                                                                            refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
                                                                                            have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
                                                                                            refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_012 v hv a133 a56 a60) fun a60 => ?_
                                                                                            refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_102 v hv a61 a137 a66) fun a61 => ?_
                                                                                            have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl459 (v 0) (hv 0) hc a64 a61
                                                                                            refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                                                            refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                                                            have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                                            have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                            refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_021 v hv a67 a71 a141) fun a71 => ?_
                                                                                            have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 hc a71
                                                                                            exact succ13_021 v hv a73 a158 a78
                                                                                          · have a138 : acc11_0 (v 2) := Classical.byContradiction fun hc => cl468 (v 2) (hv 2) a30 a39 hc
                                                                                            by_cases a35 : acc6_0 (v 1)
                                                                                            · by_cases a36 : acc6_0 (v 2)
                                                                                              · by_cases a57 : acc10_1 (v 2)
                                                                                                · by_cases a59 : acc10_2 (v 1)
                                                                                                  · have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl289 (v 1) (hv 1) a59 hc
                                                                                                    refine (Classical.em (acc10_0 (v 2))).elim (fun a135 => succ10_120 v hv a55 a59 a135) fun a135 => ?_
                                                                                                    have a63 : acc11_1 (v 2) := Classical.byContradiction fun hc => cl414 (v 2) (hv 2) a30 a135 hc
                                                                                                    exact succ11_021 v hv a136 a65 a63
                                                                                                  · by_cases a60 : acc10_2 (v 2)
                                                                                                    · have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl289 (v 2) (hv 2) a60 hc
                                                                                                      refine (Classical.em (acc10_0 (v 1))).elim (fun a134 => succ10_102 v hv a55 a134 a60) fun a134 => ?_
                                                                                                      have a62 : acc11_1 (v 1) := Classical.byContradiction fun hc => cl414 (v 1) (hv 1) a29 a134 hc
                                                                                                      exact succ11_012 v hv a136 a62 a66
                                                                                                    · by_cases a61 : acc11_1 (v 0)
                                                                                                      · have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl296 (v 0) (hv 0) a61 hc
                                                                                                        refine (Classical.em (acc11_2 (v 1))).elim (fun a65 => succ11_120 v hv a61 a65 a138) fun a65 => ?_
                                                                                                        have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl477 (v 1) (hv 1) a65 hc a98
                                                                                                        exact succ15_012 v hv a85 a143 a90
                                                                                                      · have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl459 (v 0) (hv 0) hc a64 a61
                                                                                                        refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                                                                        refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                                                                        have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                                                        have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                                        refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_021 v hv a67 a71 a141) fun a71 => ?_
                                                                                                        have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 hc a71
                                                                                                        exact succ13_021 v hv a73 a158 a78
                                                                                                · have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl284 (v 2) (hv 2) a57 hc
                                                                                                  have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl288 (v 2) (hv 2) a57 hc
                                                                                                  refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_012 v hv a97 a101 a150) fun a97 => ?_
                                                                                                  have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl477 (v 0) (hv 0) a64 hc a97
                                                                                                  refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                                                                  refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                                                                  have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                                                  refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_021 v hv a73 a158 a78) fun a158 => ?_
                                                                                                  have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 a158 hc
                                                                                                  exact succ12_021 v hv a67 a71 a141
                                                                                              · have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl206 (v 2) (hv 2) a36 hc
                                                                                                have a150 : ¬acc17_2 (v 2) := fun hc => cl213 (v 2) (hv 2) a36 hc
                                                                                                have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl405 (v 2) (hv 2) hc a36 a39
                                                                                                refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_102 v hv a61 a137 a66) fun a61 => ?_
                                                                                                have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 hc a61
                                                                                                have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl459 (v 0) (hv 0) hc a64 a61
                                                                                                refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                                                                refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                                                                have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl432 (v 2) (hv 2) a87 a150 hc
                                                                                                refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_021 v hv a73 a158 a78) fun a158 => ?_
                                                                                                have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 a158 hc
                                                                                                refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_120 v hv a139 a71 a69) fun a139 => ?_
                                                                                                have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 a139 hc
                                                                                                refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                                                                                                have a72 : acc12_2 (v 2) := Classical.byContradiction fun hc => cl418 (v 2) (hv 2) a144 hc a87
                                                                                                refine (Classical.em (acc12_1 (v 1))).elim (fun a140 => succ12_012 v hv a67 a140 a72) fun a140 => ?_
                                                                                                have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl464 (v 1) (hv 1) hc a140 a86
                                                                                                exact succ10_021 v hv a133 a59 a57
                                                                                            · have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl405 (v 1) (hv 1) hc a35 a38
                                                                                              refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_021 v hv a136 a65 a63) fun a63 => ?_
                                                                                              refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_120 v hv a61 a65 a138) fun a61 => ?_
                                                                                              have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 hc a61
                                                                                              have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl459 (v 0) (hv 0) hc a64 a61
                                                                                              refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                                                              refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                                                              have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                                              refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_021 v hv a73 a158 a78) fun a158 => ?_
                                                                                              have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 a158 hc
                                                                                              refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_120 v hv a139 a71 a69) fun a139 => ?_
                                                                                              have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 a139 hc
                                                                                              refine (Classical.em (acc15_1 (v 1))).elim (fun a143 => succ15_012 v hv a85 a143 a90) fun a143 => ?_
                                                                                              refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                                                                                              have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl287 (v 2) (hv 2) hc a144
                                                                                              have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl459 (v 2) (hv 2) a144 hc a63
                                                                                              refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                                                                                              have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) hc a62 a143
                                                                                              exact succ10_021 v hv a133 a59 a57
                                                                                      · have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl287 (v 1) (hv 1) a56 hc
                                                                                        have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl288 (v 1) (hv 1) a56 hc
                                                                                        refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_021 v hv a97 a149 a102) fun a97 => ?_
                                                                                        have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl477 (v 0) (hv 0) a64 hc a97
                                                                                        refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                                                        refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                                                        have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                                        refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_021 v hv a73 a158 a78) fun a158 => ?_
                                                                                        have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 a158 hc
                                                                                        refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_120 v hv a139 a71 a69) fun a139 => ?_
                                                                                        have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 a139 hc
                                                                                        exact succ15_012 v hv a85 a143 a90
                                                                                    · have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl284 (v 0) (hv 0) a55 hc
                                                                                      have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl287 (v 0) (hv 0) a55 hc
                                                                                      refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                                                      refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                                                      have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                                      refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_021 v hv a73 a158 a78) fun a158 => ?_
                                                                                      have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 a158 hc
                                                                                      exact succ12_120 v hv a139 a71 a69
                                                                                  · have a60 : ¬acc10_2 (v 2) := fun hc => cl268 (v 2) (hv 2) a51 hc
                                                                                    have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl479 (v 2) (hv 2) a51 a18 hc
                                                                                    refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_012 v hv a97 a101 a150) fun a97 => ?_
                                                                                    have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl477 (v 0) (hv 0) a64 hc a97
                                                                                    refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                                                    refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                                                    have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                                    have a141 : acc12_1 (v 2) := Classical.byContradiction fun hc => cl464 (v 2) (hv 2) a60 hc a87
                                                                                    refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_021 v hv a67 a71 a141) fun a71 => ?_
                                                                                    have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 hc a71
                                                                                    exact succ13_021 v hv a73 a158 a78
                                                                                · have a137 : acc11_0 (v 1) := Classical.byContradiction fun hc => cl478 (v 1) (hv 1) a50 hc a17
                                                                                  have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl479 (v 1) (hv 1) a50 a17 hc
                                                                                  refine (Classical.em (acc17_0 (v 0))).elim (fun a97 => succ17_021 v hv a97 a149 a102) fun a97 => ?_
                                                                                  have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl477 (v 0) (hv 0) a64 hc a97
                                                                                  refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                                                                  refine (Classical.em (acc15_0 (v 2))).elim (fun a87 => succ15_120 v hv a142 a89 a87) fun a87 => ?_
                                                                                  have a63 : ¬acc11_1 (v 2) := fun hc => cl296 (v 2) (hv 2) hc a87
                                                                                  have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) a87 a162 hc
                                                                                  refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_021 v hv a73 a158 a78) fun a158 => ?_
                                                                                  have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 a158 hc
                                                                                  refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_120 v hv a139 a71 a69) fun a139 => ?_
                                                                                  have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 a139 hc
                                                                                  refine (Classical.em (acc15_1 (v 1))).elim (fun a143 => succ15_012 v hv a85 a143 a90) fun a143 => ?_
                                                                                  refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                                                                                  have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl371 (v 2) (hv 2) hc a144 a87
                                                                                  have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl459 (v 2) (hv 2) a144 hc a63
                                                                                  refine (Classical.em (acc11_1 (v 0))).elim (fun a61 => succ11_102 v hv a61 a137 a66) fun a61 => ?_
                                                                                  have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 hc a61
                                                                                  refine (Classical.em (acc10_1 (v 1))).elim (fun a56 => succ10_012 v hv a133 a56 a60) fun a56 => ?_
                                                                                  exact (cl287 (v 1) (hv 1) a56 a143).elim
                                                                              · have a66 : ¬acc11_2 (v 2) := fun hc => cl252 (v 2) (hv 2) a45 hc
                                                                                have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl254 (v 2) (hv 2) a45 hc
                                                                                refine (Classical.em (acc14_2 (v 0))).elim (fun a160 => succ14_210 v hv a160 a83 a81) fun a160 => ?_
                                                                                have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl477 (v 2) (hv 2) a66 hc a99
                                                                                refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_021 v hv a85 a89 a144) fun a85 => ?_
                                                                                have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl371 (v 0) (hv 0) a58 hc a85
                                                                                have a76 : acc13_1 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) a85 a160 hc
                                                                                have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 hc a85
                                                                                refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_120 v hv a139 a71 a69) fun a71 => ?_
                                                                                refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_120 v hv a76 a158 a75) fun a158 => ?_
                                                                                have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) hc a158 a71
                                                                                exact succ15_102 v hv a142 a86 a90
                                                                            · have a65 : ¬acc11_2 (v 1) := fun hc => cl252 (v 1) (hv 1) a44 hc
                                                                              have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl254 (v 1) (hv 1) a44 hc
                                                                              refine (Classical.em (acc14_2 (v 0))).elim (fun a160 => succ14_201 v hv a160 a80 a84) fun a160 => ?_
                                                                              have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl477 (v 1) (hv 1) a65 hc a98
                                                                              refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
                                                                              have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl371 (v 0) (hv 0) a58 hc a85
                                                                              have a76 : acc13_1 (v 0) := Classical.byContradiction fun hc => cl433 (v 0) (hv 0) a85 a160 hc
                                                                              have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 hc a85
                                                                              refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_120 v hv a139 a71 a69) fun a71 => ?_
                                                                              refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_120 v hv a76 a158 a75) fun a158 => ?_
                                                                              have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) hc a158 a71
                                                                              exact succ15_102 v hv a142 a86 a90
                                                                    · have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) a83 hc
                                                                      have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) hc a146 a83
                                                                      refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_201 v hv a148 a98 a102) fun a102 => ?_
                                                                      have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl388 (v 2) (hv 2) a54 a102 hc
                                                                      refine (Classical.em (acc17_1 (v 0))).elim (fun a100 => succ17_102 v hv a100 a98 a150) fun a100 => ?_
                                                                      have a145 : acc16_2 (v 0) := Classical.byContradiction fun hc => cl379 (v 0) (hv 0) hc a16 a100
                                                                      exact succ16_201 v hv a145 a92 a96
                                                      · have a90 : ¬acc15_2 (v 2) := fun hc => cl96 (v 2) (hv 2) a15 hc
                                                        have a102 : ¬acc17_1 (v 2) := fun hc => cl97 (v 2) (hv 2) a15 hc
                                                        have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) hc a18 a102
                                                        refine (Classical.em (acc16_0 (v 1))).elim (fun a92 => succ16_102 v hv a94 a92 a147) fun a92 => ?_
                                                        have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) hc a92
                                                        have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl384 (v 1) (hv 1) a146 hc a92
                                                        refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_210 v hv a148 a101 a99) fun a99 => ?_
                                                        have a162 : acc14_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) hc a90 a99
                                                        exact succ14_012 v hv a79 a83 a162
                                                · have a101 : ¬acc17_1 (v 1) := fun hc => cl97 (v 1) (hv 1) a14 hc
                                                  have a4 : acc0_1 (v 1) := Classical.byContradiction fun hc => cl470 (v 1) (hv 1) hc a146 a14
                                                  have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl473 (v 1) (hv 1) a11 a14 hc
                                                  refine (Classical.em (acc0_2 (v 2))).elim (fun a110 => succ0_012 v hv a1 a4 a110) fun a110 => ?_
                                                  refine (Classical.em (acc0_2 (v 0))).elim (fun a106 => succ0_210 v hv a106 a4 a5) fun a106 => ?_
                                                  have a15 : acc2_0 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) a110 a12 hc
                                                  refine (Classical.em (acc2_1 (v 0))).elim (fun a16 => succ2_120 v hv a16 a109 a15) fun a16 => ?_
                                                  have a10 : ¬acc1_2 (v 0) := fun hc => cl79 (v 0) (hv 0) hc a16
                                                  have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl390 (v 0) (hv 0) a106 a10 hc
                                                  refine (Classical.em (acc2_1 (v 2))).elim (fun a18 => succ2_021 v hv a13 a109 a18) fun a18 => ?_
                                                  have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) a146 hc a101
                                                  have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl384 (v 1) (hv 1) a146 a101 hc
                                                  refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_102 v hv a94 a92 a147) fun a147 => ?_
                                                  have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) a147 a18 hc
                                                  refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_201 v hv a148 a98 a102) fun a98 => ?_
                                                  exact (cl102 (v 1) (hv 1) a17 a98).elim
                                            · have a6 : acc0_1 (v 2) := Classical.byContradiction fun hc => cl36 (v 2) (hv 2) hc a96
                                              have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl104 (v 2) (hv 2) hc a96
                                              have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl339 (v 2) (hv 2) a96 hc
                                              have a102 : ¬acc17_1 (v 2) := fun hc => cl340 (v 2) (hv 2) a96 hc
                                              refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_210 v hv a148 a101 a99) fun a101 => ?_
                                              have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl212 (v 1) (hv 1) hc a101
                                              refine (Classical.em (acc0_2 (v 1))).elim (fun a108 => succ0_021 v hv a1 a108 a6) fun a108 => ?_
                                              have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl390 (v 1) (hv 1) a108 a11 hc
                                              refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_201 v hv a107 a14 a18) fun a107 => ?_
                                              have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl110 (v 0) (hv 0) a107 hc
                                              have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl474 (v 0) (hv 0) a46 hc a107
                                              have a49 : acc9_1 (v 0) := Classical.byContradiction fun hc => cl475 (v 0) (hv 0) a46 a107 hc
                                              refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_021 v hv a13 a109 a18) fun a109 => ?_
                                              have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl376 (v 1) (hv 1) a109 hc a101
                                              refine (Classical.em (acc9_1 (v 2))).elim (fun a51 => succ9_021 v hv a115 a53 a51) fun a51 => ?_
                                              refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_120 v hv a49 a53 a117) fun a117 => ?_
                                              have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl247 (v 2) (hv 2) hc a117
                                              have a150 : ¬acc17_2 (v 2) := fun hc => cl267 (v 2) (hv 2) a117 hc
                                              have a54 : acc9_2 (v 2) := Classical.byContradiction fun hc => cl388 (v 2) (hv 2) hc a102 a150
                                              refine (Classical.em (acc9_1 (v 1))).elim (fun a50 => succ9_012 v hv a115 a50 a54) fun a50 => ?_
                                              have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) hc a109 a50
                                              refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_021 v hv a130 a47 a45) fun a130 => ?_
                                              refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                              have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl403 (v 2) (hv 2) hc a132 a51
                                              refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                              exact (cl215 (v 0) (hv 0) a127 a130).elim
                                          · have a4 : acc0_1 (v 1) := Classical.byContradiction fun hc => cl36 (v 1) (hv 1) hc a95
                                            have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl104 (v 1) (hv 1) hc a95
                                            have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl210 (v 1) (hv 1) hc a95
                                            have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl338 (v 1) (hv 1) hc a95
                                            have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl339 (v 1) (hv 1) a95 hc
                                            have a101 : ¬acc17_1 (v 1) := fun hc => cl340 (v 1) (hv 1) a95 hc
                                            refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_201 v hv a148 a98 a102) fun a102 => ?_
                                            refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_102 v hv a94 a92 a147) fun a147 => ?_
                                            have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl379 (v 2) (hv 2) a147 hc a102
                                            refine (Classical.em (acc0_2 (v 2))).elim (fun a110 => succ0_012 v hv a1 a4 a110) fun a110 => ?_
                                            have a15 : acc2_0 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) a110 a12 hc
                                            refine (Classical.em (acc2_2 (v 0))).elim (fun a107 => succ2_210 v hv a107 a17 a15) fun a107 => ?_
                                            have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl110 (v 0) (hv 0) a107 hc
                                            have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl474 (v 0) (hv 0) a46 hc a107
                                            have a49 : acc9_1 (v 0) := Classical.byContradiction fun hc => cl475 (v 0) (hv 0) a46 a107 hc
                                            refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_021 v hv a13 a109 a18) fun a109 => ?_
                                            have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl376 (v 1) (hv 1) a109 hc a101
                                            refine (Classical.em (acc9_1 (v 2))).elim (fun a51 => succ9_021 v hv a115 a53 a51) fun a51 => ?_
                                            refine (Classical.em (acc9_0 (v 2))).elim (fun a117 => succ9_120 v hv a49 a53 a117) fun a117 => ?_
                                            have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl247 (v 2) (hv 2) hc a117
                                            have a150 : ¬acc17_2 (v 2) := fun hc => cl267 (v 2) (hv 2) a117 hc
                                            have a54 : acc9_2 (v 2) := Classical.byContradiction fun hc => cl388 (v 2) (hv 2) hc a102 a150
                                            refine (Classical.em (acc9_1 (v 1))).elim (fun a50 => succ9_012 v hv a115 a50 a54) fun a50 => ?_
                                            have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) hc a109 a50
                                            refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_021 v hv a130 a47 a45) fun a130 => ?_
                                            refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                                            have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl403 (v 2) (hv 2) hc a132 a51
                                            refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                                            exact (cl215 (v 0) (hv 0) a127 a130).elim
                                        · have a2 : acc0_1 (v 0) := Classical.byContradiction fun hc => cl36 (v 0) (hv 0) hc a94
                                          have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl104 (v 0) (hv 0) hc a94
                                          have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl334 (v 0) (hv 0) hc a94
                                          have a88 : ¬acc15_2 (v 0) := fun hc => cl336 (v 0) (hv 0) hc a94
                                          have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl338 (v 0) (hv 0) hc a94
                                          have a97 : acc17_0 (v 0) := Classical.byContradiction fun hc => cl339 (v 0) (hv 0) a94 hc
                                          have a100 : ¬acc17_1 (v 0) := fun hc => cl340 (v 0) (hv 0) a94 hc
                                          have a107 : acc2_2 (v 0) := Classical.byContradiction fun hc => cl376 (v 0) (hv 0) hc a52 a100
                                          have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl421 (v 0) (hv 0) a52 hc a100
                                          refine (Classical.em (acc0_2 (v 1))).elim (fun a108 => succ0_120 v hv a2 a108 a5) fun a108 => ?_
                                          have a14 : acc2_0 (v 1) := Classical.byContradiction fun hc => cl390 (v 1) (hv 1) a108 a11 hc
                                          refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_102 v hv a16 a14 a111) fun a111 => ?_
                                          refine (Classical.em (acc2_1 (v 2))).elim (fun a18 => succ2_201 v hv a107 a14 a18) fun a18 => ?_
                                          have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl394 (v 2) (hv 2) a111 hc a18
                                          refine (Classical.em (acc17_2 (v 1))).elim (fun a149 => succ17_021 v hv a97 a149 a102) fun a149 => ?_
                                          refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_201 v hv a148 a98 a102) fun a98 => ?_
                                          have a53 : ¬acc9_2 (v 1) := fun hc => cl278 (v 1) (hv 1) hc a98
                                          have a95 : acc16_1 (v 1) := Classical.byContradiction fun hc => cl339 (v 1) (hv 1) hc a98
                                          refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_012 v hv a91 a95 a147) fun a147 => ?_
                                          have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl388 (v 1) (hv 1) a53 hc a149
                                          refine (Classical.em (acc17_2 (v 2))).elim (fun a150 => succ17_012 v hv a97 a101 a150) fun a150 => ?_
                                          refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_210 v hv a148 a101 a99) fun a99 => ?_
                                          have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl452 (v 2) (hv 2) a99 a147 hc
                                          refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_021 v hv a79 a161 a84) fun a161 => ?_
                                          have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) a161 hc a98
                                          have a146 : ¬acc16_2 (v 1) := fun hc => cl387 (v 1) (hv 1) hc a161 a98
                                          have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) a98 a146 hc
                                          refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                                          have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) a162 hc a99
                                          have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl367 (v 2) (hv 2) a90 a150 hc
                                          refine (Classical.em (acc15_1 (v 1))).elim (fun a143 => succ15_012 v hv a85 a143 a90) fun a143 => ?_
                                          refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
                                          have a38 : ¬acc7_1 (v 1) := fun hc => cl237 (v 1) (hv 1) hc a62
                                          have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) hc a62 a143
                                          refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                                          have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl287 (v 2) (hv 2) hc a144
                                          refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_021 v hv a133 a59 a57) fun a133 => ?_
                                          have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) hc a133
                                          have a61 : acc11_1 (v 0) := Classical.byContradiction fun hc => cl412 (v 0) (hv 0) a133 a88 hc
                                          refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_102 v hv a61 a137 a66) fun a137 => ?_
                                          have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl468 (v 1) (hv 1) hc a38 a137
                                          refine (Classical.em (acc4_1 (v 2))).elim (fun a27 => succ4_021 v hv a121 a29 a27) fun a27 => ?_
                                          refine (Classical.em (acc4_0 (v 2))).elim (fun a123 => succ4_120 v hv a25 a29 a123) fun a123 => ?_
                                          exact (cl147 (v 2) (hv 2) a123 a27).elim
                                  · have a110 : acc0_2 (v 2) := Classical.byContradiction fun hc => cl43 (v 2) (hv 2) hc a9
                                    have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl68 (v 2) (hv 2) a9 hc
                                    have a90 : ¬acc15_2 (v 2) := fun hc => cl70 (v 2) (hv 2) a9 hc
                                    have a147 : acc16_2 (v 2) := Classical.byContradiction fun hc => cl72 (v 2) (hv 2) a9 hc
                                    refine (Classical.em (acc0_1 (v 0))).elim (fun a2 => succ0_102 v hv a2 a3 a110) fun a2 => ?_
                                    have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl36 (v 0) (hv 0) a2 hc
                                    refine (Classical.em (acc16_0 (v 1))).elim (fun a92 => succ16_102 v hv a94 a92 a147) fun a92 => ?_
                                    have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) hc a92
                                    have a95 : acc16_1 (v 1) := Classical.byContradiction fun hc => cl338 (v 1) (hv 1) a92 hc
                                    refine (Classical.em (acc16_0 (v 0))).elim (fun a91 => succ16_012 v hv a91 a95 a147) fun a91 => ?_
                                    have a82 : acc14_1 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) hc a91
                                    refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_120 v hv a82 a161 a81) fun a161 => ?_
                                    have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl385 (v 1) (hv 1) a161 hc a92
                                    refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_210 v hv a148 a101 a99) fun a99 => ?_
                                    have a162 : acc14_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) hc a90 a99
                                    exact succ14_012 v hv a79 a83 a162
                                · have a108 : acc0_2 (v 1) := Classical.byContradiction fun hc => cl43 (v 1) (hv 1) hc a8
                                  have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl68 (v 1) (hv 1) a8 hc
                                  have a89 : ¬acc15_2 (v 1) := fun hc => cl70 (v 1) (hv 1) a8 hc
                                  have a146 : acc16_2 (v 1) := Classical.byContradiction fun hc => cl72 (v 1) (hv 1) a8 hc
                                  refine (Classical.em (acc0_1 (v 0))).elim (fun a2 => succ0_120 v hv a2 a108 a5) fun a2 => ?_
                                  have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl36 (v 0) (hv 0) a2 hc
                                  refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_120 v hv a94 a146 a93) fun a93 => ?_
                                  have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl332 (v 2) (hv 2) hc a93
                                  have a96 : acc16_1 (v 2) := Classical.byContradiction fun hc => cl338 (v 2) (hv 2) a93 hc
                                  refine (Classical.em (acc16_0 (v 0))).elim (fun a91 => succ16_021 v hv a91 a146 a96) fun a91 => ?_
                                  have a82 : acc14_1 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) hc a91
                                  refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_102 v hv a82 a80 a162) fun a162 => ?_
                                  have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl385 (v 2) (hv 2) a162 hc a93
                                  refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_201 v hv a148 a98 a102) fun a98 => ?_
                                  have a161 : acc14_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) hc a89 a98
                                  exact succ14_021 v hv a79 a161 a84
                              · have a106 : acc0_2 (v 0) := Classical.byContradiction fun hc => cl43 (v 0) (hv 0) hc a7
                                have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl65 (v 0) (hv 0) a7 hc
                                have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl69 (v 0) (hv 0) a7 hc
                                have a145 : acc16_2 (v 0) := Classical.byContradiction fun hc => cl72 (v 0) (hv 0) a7 hc
                                refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_120 v hv a139 a71 a69) fun a71 => ?_
                                refine (Classical.em (acc0_1 (v 1))).elim (fun a4 => succ0_210 v hv a106 a4 a5) fun a4 => ?_
                                have a95 : acc16_1 (v 1) := Classical.byContradiction fun hc => cl36 (v 1) (hv 1) a4 hc
                                refine (Classical.em (acc16_0 (v 2))).elim (fun a93 => succ16_210 v hv a145 a95 a93) fun a93 => ?_
                                have a84 : acc14_1 (v 2) := Classical.byContradiction fun hc => cl332 (v 2) (hv 2) hc a93
                                have a96 : acc16_1 (v 2) := Classical.byContradiction fun hc => cl338 (v 2) (hv 2) a93 hc
                                refine (Classical.em (acc16_0 (v 1))).elim (fun a92 => succ16_201 v hv a145 a92 a96) fun a92 => ?_
                                have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) hc a92
                                refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
                                have a102 : acc17_1 (v 2) := Classical.byContradiction fun hc => cl385 (v 2) (hv 2) a162 hc a93
                                refine (Classical.em (acc17_0 (v 1))).elim (fun a98 => succ17_201 v hv a148 a98 a102) fun a98 => ?_
                                refine (Classical.em (acc14_2 (v 1))).elim (fun a161 => succ14_021 v hv a79 a161 a84) fun a161 => ?_
                                have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl373 (v 1) (hv 1) a161 hc a98
                                have a101 : acc17_1 (v 1) := Classical.byContradiction fun hc => cl385 (v 1) (hv 1) a161 hc a92
                                refine (Classical.em (acc17_0 (v 2))).elim (fun a99 => succ17_210 v hv a148 a101 a99) fun a99 => ?_
                                have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl373 (v 2) (hv 2) a162 hc a99
                                refine (Classical.em (acc15_0 (v 1))).elim (fun a86 => succ15_102 v hv a142 a86 a90) fun a86 => ?_
                                have a158 : acc13_2 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) a86 hc a71
                                refine (Classical.em (acc13_1 (v 2))).elim (fun a78 => succ13_021 v hv a73 a158 a78) fun a78 => ?_
                                have a87 : acc15_0 (v 2) := Classical.byContradiction fun hc => cl433 (v 2) (hv 2) hc a162 a78
                                exact succ15_120 v hv a142 a89 a87
                            · have a6 : acc0_1 (v 2) := Classical.byContradiction fun hc => cl0 (v 2) (hv 2) a5 hc
                              have a12 : acc1_2 (v 2) := Classical.byContradiction fun hc => cl2 (v 2) (hv 2) a5 hc
                              have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl4 (v 2) (hv 2) a5 hc
                              have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl14 (v 2) (hv 2) a5 hc
                              have a51 : ¬acc9_1 (v 2) := fun hc => cl15 (v 2) (hv 2) a5 hc
                              have a54 : acc9_2 (v 2) := Classical.byContradiction fun hc => cl16 (v 2) (hv 2) a5 hc
                              have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl31 (v 2) (hv 2) a5 hc
                              refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_210 v hv a148 a101 a99) fun a101 => ?_
                              have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl212 (v 1) (hv 1) hc a101
                              refine (Classical.em (acc9_1 (v 1))).elim (fun a50 => succ9_012 v hv a115 a50 a54) fun a50 => ?_
                              refine (Classical.em (acc0_2 (v 0))).elim (fun a106 => succ0_201 v hv a106 a3 a6) fun a106 => ?_
                              have a7 : acc1_0 (v 0) := Classical.byContradiction fun hc => cl43 (v 0) (hv 0) a106 hc
                              refine (Classical.em (acc1_1 (v 1))).elim (fun a119 => succ1_012 v hv a7 a119 a12) fun a119 => ?_
                              have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl77 (v 1) (hv 1) a119 hc
                              refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_012 v hv a130 a44 a48) fun a130 => ?_
                              have a127 : acc6_1 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) hc a130
                              have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl244 (v 0) (hv 0) a130 hc
                              have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl404 (v 0) (hv 0) a154 a130 hc
                              refine (Classical.em (acc2_2 (v 1))).elim (fun a109 => succ2_021 v hv a13 a109 a18) fun a109 => ?_
                              have a47 : acc8_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) hc a109 a50
                              refine (Classical.em (acc8_0 (v 2))).elim (fun a132 => succ8_120 v hv a43 a47 a132) fun a132 => ?_
                              have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl403 (v 2) (hv 2) hc a132 a51
                              exact succ6_102 v hv a127 a35 a156
                          · have a4 : acc0_1 (v 1) := Classical.byContradiction fun hc => cl0 (v 1) (hv 1) a3 hc
                            have a11 : acc1_2 (v 1) := Classical.byContradiction fun hc => cl2 (v 1) (hv 1) a3 hc
                            have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl4 (v 1) (hv 1) a3 hc
                            have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl13 (v 1) (hv 1) a3 hc
                            have a50 : ¬acc9_1 (v 1) := fun hc => cl15 (v 1) (hv 1) a3 hc
                            have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl16 (v 1) (hv 1) a3 hc
                            have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl31 (v 1) (hv 1) a3 hc
                            refine (Classical.em (acc17_1 (v 2))).elim (fun a102 => succ17_201 v hv a148 a98 a102) fun a102 => ?_
                            have a36 : acc6_0 (v 2) := Classical.byContradiction fun hc => cl212 (v 2) (hv 2) hc a102
                            refine (Classical.em (acc9_1 (v 2))).elim (fun a51 => succ9_021 v hv a115 a53 a51) fun a51 => ?_
                            refine (Classical.em (acc0_2 (v 2))).elim (fun a110 => succ0_012 v hv a1 a4 a110) fun a110 => ?_
                            have a9 : acc1_0 (v 2) := Classical.byContradiction fun hc => cl43 (v 2) (hv 2) a110 hc
                            refine (Classical.em (acc1_1 (v 0))).elim (fun a118 => succ1_120 v hv a118 a11 a9) fun a118 => ?_
                            have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl77 (v 0) (hv 0) a118 hc
                            have a13 : acc2_0 (v 0) := Classical.byContradiction fun hc => cl354 (v 0) (hv 0) a46 a118 hc
                            refine (Classical.em (acc2_2 (v 2))).elim (fun a111 => succ2_012 v hv a13 a17 a111) fun a111 => ?_
                            have a48 : acc8_2 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) hc a111 a51
                            refine (Classical.em (acc8_0 (v 0))).elim (fun a130 => succ8_012 v hv a130 a44 a48) fun a130 => ?_
                            refine (Classical.em (acc8_0 (v 1))).elim (fun a131 => succ8_102 v hv a43 a131 a48) fun a131 => ?_
                            have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl403 (v 1) (hv 1) hc a131 a50
                            refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                            exact (cl215 (v 0) (hv 0) a127 a130).elim
                      · have a6 : acc0_1 (v 2) := Classical.byContradiction fun hc => cl35 (v 2) (hv 2) hc a105
                        have a9 : acc1_0 (v 2) := Classical.byContradiction fun hc => cl47 (v 2) (hv 2) hc a105
                        have a18 : acc2_1 (v 2) := Classical.byContradiction fun hc => cl103 (v 2) (hv 2) hc a105
                        have a153 : acc5_2 (v 2) := Classical.byContradiction fun hc => cl116 (v 2) (hv 2) a105 hc
                        have a156 : acc6_2 (v 2) := Classical.byContradiction fun hc => cl118 (v 2) (hv 2) a105 hc
                        have a45 : acc8_1 (v 2) := Classical.byContradiction fun hc => cl121 (v 2) (hv 2) a105 hc
                        have a54 : acc9_2 (v 2) := Classical.byContradiction fun hc => cl123 (v 2) (hv 2) a105 hc
                        refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_102 v hv a124 a32 a153) fun a124 => ?_
                        have a34 : acc6_0 (v 0) := Classical.byContradiction fun hc => cl192 (v 0) (hv 0) a124 hc
                        refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_012 v hv a34 a128 a156) fun a128 => ?_
                        have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl200 (v 1) (hv 1) hc a128
                        have a131 : acc8_0 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) a128 hc
                        refine (Classical.em (acc8_2 (v 0))).elim (fun a46 => succ8_201 v hv a46 a131 a45) fun a46 => ?_
                        have a1 : acc0_0 (v 0) := Classical.byContradiction fun hc => cl14 (v 0) (hv 0) hc a46
                        refine (Classical.em (acc0_2 (v 1))).elim (fun a108 => succ0_021 v hv a1 a108 a6) fun a108 => ?_
                        refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_102 v hv a127 a35 a156) fun a127 => ?_
                        have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                        have a115 : acc9_0 (v 0) := Classical.byContradiction fun hc => cl356 (v 0) (hv 0) a46 hc a127
                        refine (Classical.em (acc9_1 (v 1))).elim (fun a50 => succ9_012 v hv a115 a50 a54) fun a50 => ?_
                        refine (Classical.em (acc8_2 (v 1))).elim (fun a47 => succ8_021 v hv a130 a47 a45) fun a47 => ?_
                        have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl475 (v 1) (hv 1) a47 hc a50
                        refine (Classical.em (acc2_0 (v 0))).elim (fun a13 => succ2_021 v hv a13 a109 a18) fun a13 => ?_
                        have a118 : acc1_1 (v 0) := Classical.byContradiction fun hc => cl354 (v 0) (hv 0) a46 hc a13
                        have a107 : acc2_2 (v 0) := Classical.byContradiction fun hc => cl474 (v 0) (hv 0) a46 a13 hc
                        refine (Classical.em (acc2_0 (v 1))).elim (fun a14 => succ2_201 v hv a107 a14 a18) fun a14 => ?_
                        have a11 : acc1_2 (v 1) := Classical.byContradiction fun hc => cl390 (v 1) (hv 1) a108 hc a14
                        exact succ1_120 v hv a118 a11 a9
                    · have a4 : acc0_1 (v 1) := Classical.byContradiction fun hc => cl35 (v 1) (hv 1) hc a104
                      have a8 : acc1_0 (v 1) := Classical.byContradiction fun hc => cl47 (v 1) (hv 1) hc a104
                      have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl103 (v 1) (hv 1) hc a104
                      have a152 : acc5_2 (v 1) := Classical.byContradiction fun hc => cl116 (v 1) (hv 1) a104 hc
                      have a155 : acc6_2 (v 1) := Classical.byContradiction fun hc => cl118 (v 1) (hv 1) a104 hc
                      have a44 : acc8_1 (v 1) := Classical.byContradiction fun hc => cl121 (v 1) (hv 1) a104 hc
                      have a53 : acc9_2 (v 1) := Classical.byContradiction fun hc => cl123 (v 1) (hv 1) a104 hc
                      refine (Classical.em (acc5_1 (v 0))).elim (fun a124 => succ5_120 v hv a124 a152 a33) fun a124 => ?_
                      have a34 : acc6_0 (v 0) := Classical.byContradiction fun hc => cl192 (v 0) (hv 0) a124 hc
                      refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_021 v hv a34 a155 a129) fun a129 => ?_
                      have a36 : acc6_0 (v 2) := Classical.byContradiction fun hc => cl200 (v 2) (hv 2) hc a129
                      have a132 : acc8_0 (v 2) := Classical.byContradiction fun hc => cl215 (v 2) (hv 2) a129 hc
                      refine (Classical.em (acc8_2 (v 0))).elim (fun a46 => succ8_210 v hv a46 a44 a132) fun a46 => ?_
                      have a1 : acc0_0 (v 0) := Classical.byContradiction fun hc => cl14 (v 0) (hv 0) hc a46
                      refine (Classical.em (acc0_2 (v 2))).elim (fun a110 => succ0_012 v hv a1 a4 a110) fun a110 => ?_
                      refine (Classical.em (acc6_1 (v 0))).elim (fun a127 => succ6_120 v hv a127 a155 a36) fun a127 => ?_
                      have a130 : acc8_0 (v 0) := Classical.byContradiction fun hc => cl215 (v 0) (hv 0) a127 hc
                      have a115 : acc9_0 (v 0) := Classical.byContradiction fun hc => cl356 (v 0) (hv 0) a46 hc a127
                      refine (Classical.em (acc9_1 (v 2))).elim (fun a51 => succ9_021 v hv a115 a53 a51) fun a51 => ?_
                      refine (Classical.em (acc8_2 (v 2))).elim (fun a48 => succ8_012 v hv a130 a44 a48) fun a48 => ?_
                      have a111 : acc2_2 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) a48 hc a51
                      refine (Classical.em (acc2_0 (v 0))).elim (fun a13 => succ2_012 v hv a13 a17 a111) fun a13 => ?_
                      have a118 : acc1_1 (v 0) := Classical.byContradiction fun hc => cl354 (v 0) (hv 0) a46 hc a13
                      have a107 : acc2_2 (v 0) := Classical.byContradiction fun hc => cl474 (v 0) (hv 0) a46 a13 hc
                      refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_210 v hv a107 a17 a15) fun a15 => ?_
                      have a12 : acc1_2 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) a110 hc a15
                      exact succ1_102 v hv a118 a8 a12
                  · have a2 : acc0_1 (v 0) := Classical.byContradiction fun hc => cl35 (v 0) (hv 0) hc a103
                    have a7 : acc1_0 (v 0) := Classical.byContradiction fun hc => cl47 (v 0) (hv 0) hc a103
                    have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl103 (v 0) (hv 0) hc a103
                    have a151 : acc5_2 (v 0) := Classical.byContradiction fun hc => cl116 (v 0) (hv 0) a103 hc
                    have a154 : acc6_2 (v 0) := Classical.byContradiction fun hc => cl118 (v 0) (hv 0) a103 hc
                    have a43 : acc8_1 (v 0) := Classical.byContradiction fun hc => cl121 (v 0) (hv 0) a103 hc
                    have a52 : acc9_2 (v 0) := Classical.byContradiction fun hc => cl123 (v 0) (hv 0) a103 hc
                    refine (Classical.em (acc5_1 (v 1))).elim (fun a125 => succ5_210 v hv a151 a125 a33) fun a125 => ?_
                    have a35 : acc6_0 (v 1) := Classical.byContradiction fun hc => cl192 (v 1) (hv 1) a125 hc
                    refine (Classical.em (acc6_1 (v 2))).elim (fun a129 => succ6_201 v hv a154 a35 a129) fun a129 => ?_
                    have a36 : acc6_0 (v 2) := Classical.byContradiction fun hc => cl200 (v 2) (hv 2) hc a129
                    have a132 : acc8_0 (v 2) := Classical.byContradiction fun hc => cl215 (v 2) (hv 2) a129 hc
                    refine (Classical.em (acc8_2 (v 1))).elim (fun a47 => succ8_120 v hv a43 a47 a132) fun a47 => ?_
                    have a3 : acc0_0 (v 1) := Classical.byContradiction fun hc => cl14 (v 1) (hv 1) hc a47
                    refine (Classical.em (acc0_2 (v 2))).elim (fun a110 => succ0_102 v hv a2 a3 a110) fun a110 => ?_
                    refine (Classical.em (acc6_1 (v 1))).elim (fun a128 => succ6_210 v hv a154 a128 a36) fun a128 => ?_
                    have a131 : acc8_0 (v 1) := Classical.byContradiction fun hc => cl215 (v 1) (hv 1) a128 hc
                    have a116 : acc9_0 (v 1) := Classical.byContradiction fun hc => cl356 (v 1) (hv 1) a47 hc a128
                    refine (Classical.em (acc9_1 (v 2))).elim (fun a51 => succ9_201 v hv a52 a116 a51) fun a51 => ?_
                    refine (Classical.em (acc8_2 (v 2))).elim (fun a48 => succ8_102 v hv a43 a131 a48) fun a48 => ?_
                    have a111 : acc2_2 (v 2) := Classical.byContradiction fun hc => cl475 (v 2) (hv 2) a48 hc a51
                    refine (Classical.em (acc2_0 (v 1))).elim (fun a14 => succ2_102 v hv a16 a14 a111) fun a14 => ?_
                    have a119 : acc1_1 (v 1) := Classical.byContradiction fun hc => cl354 (v 1) (hv 1) a47 hc a14
                    have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl474 (v 1) (hv 1) a47 a14 hc
                    refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_120 v hv a16 a109 a15) fun a15 => ?_
                    have a12 : acc1_2 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) a110 hc a15
                    exact succ1_012 v hv a7 a119 a12
                · have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl130 (v 2) (hv 2) hc a75
                  have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl157 (v 2) (hv 2) hc a75
                  have a126 : acc5_1 (v 2) := Classical.byContradiction fun hc => cl193 (v 2) (hv 2) hc a75
                  have a42 : acc7_2 (v 2) := Classical.byContradiction fun hc => cl243 (v 2) (hv 2) hc a75
                  have a60 : acc10_2 (v 2) := Classical.byContradiction fun hc => cl290 (v 2) (hv 2) hc a75
                  have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl297 (v 2) (hv 2) hc a75
                  have a72 : acc12_2 (v 2) := Classical.byContradiction fun hc => cl312 (v 2) (hv 2) hc a75
                  have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl317 (v 2) (hv 2) a75 hc
                  refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_102 v hv a139 a68 a72) fun a139 => ?_
                  have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 a139 hc
                  refine (Classical.em (acc15_1 (v 1))).elim (fun a143 => succ15_012 v hv a85 a143 a90) fun a143 => ?_
                  have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl287 (v 1) (hv 1) hc a143
                  refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_012 v hv a133 a56 a60) fun a133 => ?_
                  have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) hc a133
                  have a61 : acc11_1 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 a133 hc
                  refine (Classical.em (acc11_0 (v 1))).elim (fun a137 => succ11_102 v hv a61 a137 a66) fun a137 => ?_
                  refine (Classical.em (acc4_2 (v 1))).elim (fun a29 => succ4_120 v hv a25 a29 a123) fun a29 => ?_
                  have a38 : acc7_1 (v 1) := Classical.byContradiction fun hc => cl468 (v 1) (hv 1) a29 hc a137
                  refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_012 v hv a112 a38 a42) fun a112 => ?_
                  have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl360 (v 0) (hv 0) a112 hc a28
                  refine (Classical.em (acc7_0 (v 1))).elim (fun a113 => succ7_102 v hv a37 a113 a42) fun a113 => ?_
                  have a20 : acc3_1 (v 1) := Classical.byContradiction fun hc => cl461 (v 1) (hv 1) a29 hc a113
                  refine (Classical.em (acc3_2 (v 0))).elim (fun a22 => succ3_210 v hv a22 a20 a105) fun a22 => ?_
                  have a151 : acc5_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) a22 a112 hc
                  exact succ5_201 v hv a151 a32 a126
              · have a104 : acc3_0 (v 1) := Classical.byContradiction fun hc => cl130 (v 1) (hv 1) hc a74
                have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl157 (v 1) (hv 1) hc a74
                have a125 : acc5_1 (v 1) := Classical.byContradiction fun hc => cl193 (v 1) (hv 1) hc a74
                have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl243 (v 1) (hv 1) hc a74
                have a59 : acc10_2 (v 1) := Classical.byContradiction fun hc => cl290 (v 1) (hv 1) hc a74
                have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl297 (v 1) (hv 1) hc a74
                have a71 : acc12_2 (v 1) := Classical.byContradiction fun hc => cl312 (v 1) (hv 1) hc a74
                have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl317 (v 1) (hv 1) a74 hc
                refine (Classical.em (acc12_1 (v 0))).elim (fun a139 => succ12_120 v hv a139 a71 a69) fun a139 => ?_
                have a85 : acc15_0 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 a139 hc
                refine (Classical.em (acc15_1 (v 2))).elim (fun a144 => succ15_021 v hv a85 a89 a144) fun a144 => ?_
                have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl287 (v 2) (hv 2) hc a144
                refine (Classical.em (acc10_0 (v 0))).elim (fun a133 => succ10_021 v hv a133 a59 a57) fun a133 => ?_
                have a25 : acc4_1 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) hc a133
                have a61 : acc11_1 (v 0) := Classical.byContradiction fun hc => cl414 (v 0) (hv 0) a28 a133 hc
                refine (Classical.em (acc11_0 (v 2))).elim (fun a138 => succ11_120 v hv a61 a65 a138) fun a138 => ?_
                refine (Classical.em (acc4_2 (v 2))).elim (fun a30 => succ4_102 v hv a25 a122 a30) fun a30 => ?_
                have a39 : acc7_1 (v 2) := Classical.byContradiction fun hc => cl468 (v 2) (hv 2) a30 hc a138
                refine (Classical.em (acc7_0 (v 0))).elim (fun a112 => succ7_021 v hv a112 a41 a39) fun a112 => ?_
                have a37 : acc7_1 (v 0) := Classical.byContradiction fun hc => cl360 (v 0) (hv 0) a112 hc a28
                refine (Classical.em (acc7_0 (v 2))).elim (fun a114 => succ7_120 v hv a37 a41 a114) fun a114 => ?_
                have a21 : acc3_1 (v 2) := Classical.byContradiction fun hc => cl461 (v 2) (hv 2) a30 hc a114
                refine (Classical.em (acc3_2 (v 0))).elim (fun a22 => succ3_201 v hv a22 a104 a21) fun a22 => ?_
                have a151 : acc5_2 (v 0) := Classical.byContradiction fun hc => cl457 (v 0) (hv 0) a22 a112 hc
                exact succ5_210 v hv a151 a125 a33
            · have a120 : acc1_1 (v 2) := Classical.byContradiction fun hc => cl78 (v 2) (hv 2) hc a69
              have a12 : ¬acc1_2 (v 2) := fun hc => cl80 (v 2) (hv 2) hc a69
              have a111 : acc2_2 (v 2) := Classical.byContradiction fun hc => cl111 (v 2) (hv 2) hc a69
              have a162 : acc14_2 (v 2) := Classical.byContradiction fun hc => cl303 (v 2) (hv 2) a69 hc
              have a96 : acc16_1 (v 2) := Classical.byContradiction fun hc => cl306 (v 2) (hv 2) a69 hc
              have a150 : acc17_2 (v 2) := Classical.byContradiction fun hc => cl308 (v 2) (hv 2) a69 hc
              refine (Classical.em (acc14_1 (v 1))).elim (fun a83 => succ14_012 v hv a79 a83 a162) fun a83 => ?_
              have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl325 (v 1) (hv 1) hc a83
              have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) a83 hc
              refine (Classical.em (acc16_2 (v 0))).elim (fun a145 => succ16_201 v hv a145 a92 a96) fun a145 => ?_
              have a7 : acc1_0 (v 0) := Classical.byContradiction fun hc => cl72 (v 0) (hv 0) hc a145
              refine (Classical.em (acc1_2 (v 1))).elim (fun a11 => succ1_021 v hv a7 a11 a120) fun a11 => ?_
              have a3 : acc0_0 (v 1) := Classical.byContradiction fun hc => cl2 (v 1) (hv 1) hc a11
              refine (Classical.em (acc14_1 (v 0))).elim (fun a82 => succ14_102 v hv a82 a80 a162) fun a82 => ?_
              have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) a82 hc
              refine (Classical.em (acc16_2 (v 1))).elim (fun a146 => succ16_021 v hv a91 a146 a96) fun a146 => ?_
              have a98 : acc17_0 (v 1) := Classical.byContradiction fun hc => cl452 (v 1) (hv 1) hc a146 a83
              refine (Classical.em (acc17_1 (v 0))).elim (fun a100 => succ17_102 v hv a100 a98 a150) fun a100 => ?_
              have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl379 (v 0) (hv 0) a145 hc a100
              refine (Classical.em (acc2_0 (v 1))).elim (fun a14 => succ2_102 v hv a16 a14 a111) fun a14 => ?_
              have a4 : acc0_1 (v 1) := Classical.byContradiction fun hc => cl470 (v 1) (hv 1) hc a146 a14
              have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl473 (v 1) (hv 1) a11 a14 hc
              refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_120 v hv a16 a109 a15) fun a15 => ?_
              have a110 : acc0_2 (v 2) := Classical.byContradiction fun hc => cl390 (v 2) (hv 2) hc a12 a15
              refine (Classical.em (acc0_0 (v 0))).elim (fun a1 => succ0_012 v hv a1 a4 a110) fun a1 => ?_
              refine (Classical.em (acc0_1 (v 0))).elim (fun a2 => succ0_102 v hv a2 a3 a110) fun a2 => ?_
              exact (cl0 (v 0) (hv 0) a1 a2).elim
          · have a118 : acc1_1 (v 0) := Classical.byContradiction fun hc => cl78 (v 0) (hv 0) hc a67
            have a10 : ¬acc1_2 (v 0) := fun hc => cl80 (v 0) (hv 0) hc a67
            have a107 : acc2_2 (v 0) := Classical.byContradiction fun hc => cl111 (v 0) (hv 0) hc a67
            have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl299 (v 0) (hv 0) a67 hc
            have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl301 (v 0) (hv 0) a67 hc
            have a160 : acc14_2 (v 0) := Classical.byContradiction fun hc => cl303 (v 0) (hv 0) a67 hc
            have a94 : acc16_1 (v 0) := Classical.byContradiction fun hc => cl306 (v 0) (hv 0) a67 hc
            have a148 : acc17_2 (v 0) := Classical.byContradiction fun hc => cl308 (v 0) (hv 0) a67 hc
            refine (Classical.em (acc12_2 (v 2))).elim (fun a72 => succ12_102 v hv a139 a68 a72) fun a72 => ?_
            have a75 : acc13_0 (v 2) := Classical.byContradiction fun hc => cl312 (v 2) (hv 2) a72 hc
            refine (Classical.em (acc13_1 (v 1))).elim (fun a77 => succ13_210 v hv a157 a77 a75) fun a77 => ?_
            have a80 : acc14_0 (v 1) := Classical.byContradiction fun hc => cl323 (v 1) (hv 1) a77 hc
            refine (Classical.em (acc14_1 (v 2))).elim (fun a84 => succ14_201 v hv a160 a80 a84) fun a84 => ?_
            have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl325 (v 2) (hv 2) hc a84
            have a93 : acc16_0 (v 2) := Classical.byContradiction fun hc => cl332 (v 2) (hv 2) a84 hc
            refine (Classical.em (acc16_2 (v 1))).elim (fun a146 => succ16_120 v hv a94 a146 a93) fun a146 => ?_
            have a8 : acc1_0 (v 1) := Classical.byContradiction fun hc => cl72 (v 1) (hv 1) hc a146
            refine (Classical.em (acc1_2 (v 2))).elim (fun a12 => succ1_102 v hv a118 a8 a12) fun a12 => ?_
            have a5 : acc0_0 (v 2) := Classical.byContradiction fun hc => cl2 (v 2) (hv 2) hc a12
            refine (Classical.em (acc14_1 (v 1))).elim (fun a83 => succ14_210 v hv a160 a83 a81) fun a83 => ?_
            have a92 : acc16_0 (v 1) := Classical.byContradiction fun hc => cl332 (v 1) (hv 1) a83 hc
            refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_102 v hv a94 a92 a147) fun a147 => ?_
            have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl452 (v 2) (hv 2) hc a147 a84
            refine (Classical.em (acc17_1 (v 1))).elim (fun a101 => succ17_210 v hv a148 a101 a99) fun a101 => ?_
            have a17 : acc2_1 (v 1) := Classical.byContradiction fun hc => cl379 (v 1) (hv 1) a146 hc a101
            refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_210 v hv a107 a17 a15) fun a15 => ?_
            have a6 : acc0_1 (v 2) := Classical.byContradiction fun hc => cl470 (v 2) (hv 2) hc a147 a15
            have a111 : acc2_2 (v 2) := Classical.byContradiction fun hc => cl473 (v 2) (hv 2) a12 a15 hc
            refine (Classical.em (acc2_0 (v 0))).elim (fun a13 => succ2_012 v hv a13 a17 a111) fun a13 => ?_
            have a106 : acc0_2 (v 0) := Classical.byContradiction fun hc => cl390 (v 0) (hv 0) hc a10 a13
            refine (Classical.em (acc0_0 (v 1))).elim (fun a3 => succ0_201 v hv a106 a3 a6) fun a3 => ?_
            refine (Classical.em (acc0_1 (v 1))).elim (fun a4 => succ0_210 v hv a106 a4 a5) fun a4 => ?_
            exact (cl0 (v 1) (hv 1) a3 a4).elim
        · have a119 : acc1_1 (v 1) := Classical.byContradiction fun hc => cl78 (v 1) (hv 1) hc a68
          have a11 : ¬acc1_2 (v 1) := fun hc => cl80 (v 1) (hv 1) hc a68
          have a109 : acc2_2 (v 1) := Classical.byContradiction fun hc => cl111 (v 1) (hv 1) hc a68
          have a161 : acc14_2 (v 1) := Classical.byContradiction fun hc => cl303 (v 1) (hv 1) a68 hc
          have a95 : acc16_1 (v 1) := Classical.byContradiction fun hc => cl306 (v 1) (hv 1) a68 hc
          have a149 : acc17_2 (v 1) := Classical.byContradiction fun hc => cl308 (v 1) (hv 1) a68 hc
          refine (Classical.em (acc14_1 (v 2))).elim (fun a84 => succ14_021 v hv a79 a161 a84) fun a84 => ?_
          have a81 : acc14_0 (v 2) := Classical.byContradiction fun hc => cl325 (v 2) (hv 2) hc a84
          have a93 : acc16_0 (v 2) := Classical.byContradiction fun hc => cl332 (v 2) (hv 2) a84 hc
          refine (Classical.em (acc16_2 (v 0))).elim (fun a145 => succ16_210 v hv a145 a95 a93) fun a145 => ?_
          have a7 : acc1_0 (v 0) := Classical.byContradiction fun hc => cl72 (v 0) (hv 0) hc a145
          refine (Classical.em (acc1_2 (v 2))).elim (fun a12 => succ1_012 v hv a7 a119 a12) fun a12 => ?_
          have a5 : acc0_0 (v 2) := Classical.byContradiction fun hc => cl2 (v 2) (hv 2) hc a12
          refine (Classical.em (acc14_1 (v 0))).elim (fun a82 => succ14_120 v hv a82 a161 a81) fun a82 => ?_
          have a91 : acc16_0 (v 0) := Classical.byContradiction fun hc => cl332 (v 0) (hv 0) a82 hc
          refine (Classical.em (acc16_2 (v 2))).elim (fun a147 => succ16_012 v hv a91 a95 a147) fun a147 => ?_
          have a99 : acc17_0 (v 2) := Classical.byContradiction fun hc => cl452 (v 2) (hv 2) hc a147 a84
          refine (Classical.em (acc17_1 (v 0))).elim (fun a100 => succ17_120 v hv a100 a149 a99) fun a100 => ?_
          have a16 : acc2_1 (v 0) := Classical.byContradiction fun hc => cl379 (v 0) (hv 0) a145 hc a100
          refine (Classical.em (acc2_0 (v 2))).elim (fun a15 => succ2_120 v hv a16 a109 a15) fun a15 => ?_
          have a6 : acc0_1 (v 2) := Classical.byContradiction fun hc => cl470 (v 2) (hv 2) hc a147 a15
          have a111 : acc2_2 (v 2) := Classical.byContradiction fun hc => cl473 (v 2) (hv 2) a12 a15 hc
          refine (Classical.em (acc2_0 (v 1))).elim (fun a14 => succ2_102 v hv a16 a14 a111) fun a14 => ?_
          have a108 : acc0_2 (v 1) := Classical.byContradiction fun hc => cl390 (v 1) (hv 1) hc a11 a14
          refine (Classical.em (acc0_0 (v 0))).elim (fun a1 => succ0_021 v hv a1 a108 a6) fun a1 => ?_
          refine (Classical.em (acc0_1 (v 0))).elim (fun a2 => succ0_120 v hv a2 a108 a5) fun a2 => ?_
          exact (cl0 (v 0) (hv 0) a1 a2).elim
      · have a24 : acc3_2 (v 2) := Classical.byContradiction fun hc => cl146 (v 2) (hv 2) hc a33
        have a30 : acc4_2 (v 2) := Classical.byContradiction fun hc => cl167 (v 2) (hv 2) hc a33
        have a126 : acc5_1 (v 2) := Classical.byContradiction fun hc => cl168 (v 2) (hv 2) a33 hc
        have a57 : acc10_1 (v 2) := Classical.byContradiction fun hc => cl177 (v 2) (hv 2) a33 hc
        have a66 : acc11_2 (v 2) := Classical.byContradiction fun hc => cl179 (v 2) (hv 2) a33 hc
        have a69 : acc12_0 (v 2) := Classical.byContradiction fun hc => cl180 (v 2) (hv 2) a33 hc
        have a78 : acc13_1 (v 2) := Classical.byContradiction fun hc => cl181 (v 2) (hv 2) a33 hc
        have a90 : acc15_2 (v 2) := Classical.byContradiction fun hc => cl186 (v 2) (hv 2) a33 hc
        refine (Classical.em (acc13_2 (v 1))).elim (fun a158 => succ13_021 v hv a73 a158 a78) fun a158 => ?_
        refine (Classical.em (acc5_2 (v 0))).elim (fun a151 => succ5_201 v hv a151 a32 a126) fun a151 => ?_
        have a103 : acc3_0 (v 0) := Classical.byContradiction fun hc => cl116 (v 0) (hv 0) hc a151
        refine (Classical.em (acc3_1 (v 1))).elim (fun a20 => succ3_012 v hv a103 a20 a24) fun a20 => ?_
        have a122 : acc4_0 (v 1) := Classical.byContradiction fun hc => cl142 (v 1) (hv 1) a20 hc
        refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_102 v hv a25 a122 a30) fun a25 => ?_
        have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
        have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl365 (v 0) (hv 0) a58 hc a25
        refine (Classical.em (acc11_1 (v 1))).elim (fun a62 => succ11_012 v hv a136 a62 a66) fun a62 => ?_
        refine (Classical.em (acc10_2 (v 1))).elim (fun a59 => succ10_021 v hv a133 a59 a57) fun a59 => ?_
        have a143 : acc15_1 (v 1) := Classical.byContradiction fun hc => cl465 (v 1) (hv 1) a59 a62 hc
        refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_012 v hv a85 a143 a90) fun a85 => ?_
        have a142 : acc15_1 (v 0) := Classical.byContradiction fun hc => cl371 (v 0) (hv 0) a58 hc a85
        have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 hc a85
        refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_120 v hv a139 a71 a69) fun a71 => ?_
        have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl441 (v 1) (hv 1) hc a158 a71
        exact succ15_102 v hv a142 a86 a90
    · have a23 : acc3_2 (v 1) := Classical.byContradiction fun hc => cl146 (v 1) (hv 1) hc a32
      have a29 : acc4_2 (v 1) := Classical.byContradiction fun hc => cl167 (v 1) (hv 1) hc a32
      have a125 : acc5_1 (v 1) := Classical.byContradiction fun hc => cl168 (v 1) (hv 1) a32 hc
      have a41 : acc7_2 (v 1) := Classical.byContradiction fun hc => cl172 (v 1) (hv 1) a32 hc
      have a56 : acc10_1 (v 1) := Classical.byContradiction fun hc => cl177 (v 1) (hv 1) a32 hc
      have a65 : acc11_2 (v 1) := Classical.byContradiction fun hc => cl179 (v 1) (hv 1) a32 hc
      have a77 : acc13_1 (v 1) := Classical.byContradiction fun hc => cl181 (v 1) (hv 1) a32 hc
      have a83 : acc14_1 (v 1) := Classical.byContradiction fun hc => cl183 (v 1) (hv 1) a32 hc
      have a143 : ¬acc15_1 (v 1) := fun hc => cl185 (v 1) (hv 1) a32 hc
      have a89 : acc15_2 (v 1) := Classical.byContradiction fun hc => cl186 (v 1) (hv 1) a32 hc
      refine (Classical.em (acc14_2 (v 2))).elim (fun a162 => succ14_012 v hv a79 a83 a162) fun a162 => ?_
      have a69 : acc12_0 (v 2) := Classical.byContradiction fun hc => cl303 (v 2) (hv 2) hc a162
      refine (Classical.em (acc5_2 (v 2))).elim (fun a153 => succ5_012 v hv a31 a125 a153) fun a153 => ?_
      have a105 : acc3_0 (v 2) := Classical.byContradiction fun hc => cl116 (v 2) (hv 2) hc a153
      refine (Classical.em (acc3_1 (v 0))).elim (fun a19 => succ3_120 v hv a19 a23 a105) fun a19 => ?_
      have a112 : acc7_0 (v 0) := Classical.byContradiction fun hc => cl461 (v 0) (hv 0) a28 a19 hc
      refine (Classical.em (acc7_1 (v 2))).elim (fun a39 => succ7_021 v hv a112 a41 a39) fun a39 => ?_
      have a123 : acc4_0 (v 2) := Classical.byContradiction fun hc => cl149 (v 2) (hv 2) hc a39
      refine (Classical.em (acc4_1 (v 0))).elim (fun a25 => succ4_120 v hv a25 a29 a123) fun a25 => ?_
      have a133 : acc10_0 (v 0) := Classical.byContradiction fun hc => cl163 (v 0) (hv 0) a25 hc
      have a136 : acc11_0 (v 0) := Classical.byContradiction fun hc => cl365 (v 0) (hv 0) a58 hc a25
      refine (Classical.em (acc11_1 (v 2))).elim (fun a63 => succ11_021 v hv a136 a65 a63) fun a63 => ?_
      refine (Classical.em (acc10_2 (v 2))).elim (fun a60 => succ10_012 v hv a133 a56 a60) fun a60 => ?_
      have a75 : acc13_0 (v 2) := Classical.byContradiction fun hc => cl290 (v 2) (hv 2) a60 hc
      have a144 : acc15_1 (v 2) := Classical.byContradiction fun hc => cl465 (v 2) (hv 2) a60 a63 hc
      refine (Classical.em (acc15_0 (v 0))).elim (fun a85 => succ15_021 v hv a85 a89 a144) fun a85 => ?_
      have a139 : acc12_1 (v 0) := Classical.byContradiction fun hc => cl464 (v 0) (hv 0) a58 hc a85
      refine (Classical.em (acc12_2 (v 1))).elim (fun a71 => succ12_120 v hv a139 a71 a69) fun a71 => ?_
      have a86 : acc15_0 (v 1) := Classical.byContradiction fun hc => cl418 (v 1) (hv 1) a143 a71 hc
      refine (Classical.em (acc15_2 (v 0))).elim (fun a88 => succ15_201 v hv a88 a86 a144) fun a88 => ?_
      have a157 : acc13_2 (v 0) := Classical.byContradiction fun hc => cl438 (v 0) (hv 0) a85 a88 hc
      exact succ13_210 v hv a157 a77 a75

/-- Every common binary additive valuation (all `2^8` weight vectors) admits an EF1_outer
3-allocation. -/
theorem H_yes_k3_common_binary (w : Fin 8 → Bool) :
    ∃ A, IsEF1Outer H 3 (fun _ => commonBinaryVal w) A :=
  H_yes_k3_hetero_monotone _ fun _ _ _ hST => card_le_card (filter_subset_filter _ hST)

/-! ## Spectra and Conjecture 1 -/

/-- Spectrum entry `k` of `H` is yes for the valuation class `Cls` if every profile of `k`
valuations in `Cls` admits an EF1_outer allocation. -/
def SpectrumYes (Cls : (k : ℕ) → (Fin k → Finset (Fin 8) → ℝ) → Prop) (k : ℕ) : Prop :=
  ∀ v, Cls k v → ∃ A, IsEF1Outer H k v A

/-- The shape required by Conjecture 1: yes on `[1, a)`, no on `[a, b)`, yes on `[b, ∞)`. -/
def ChenZwickerShape (Yes : ℕ → Prop) : Prop :=
  ∃ a b : ℕ, (∀ k, 1 ≤ k → k < a → Yes k) ∧ (∀ k, a ≤ k → k < b → ¬ Yes k) ∧
    ∀ k, 1 ≤ k → b ≤ k → Yes k

theorem not_shape (Yes : ℕ → Prop) (h2 : ¬ Yes 2) (h3 : Yes 3) (h4 : ¬ Yes 4) :
    ¬ ChenZwickerShape Yes := by
  rintro ⟨a, b, hy, hn, hy'⟩
  by_cases ha : 2 < a
  · exact h2 (hy 2 (by norm_num) ha)
  by_cases hb : b ≤ 4
  · exact h4 (hy' 4 (by norm_num) hb)
  exact hn 3 (by omega) (by omega) h3

/-- `beta` as a real-valued valuation. -/
def betaR (S : Finset (Fin 8)) : ℝ := (beta S : ℝ)

/-- Any class containing `beta` (for `k = 2, 4`) and contained in the monotone valuations
(for `k = 3`) has spectrum `no, yes, no` at `k = 2, 3, 4`, so it violates Conjecture 1. -/
theorem spectrum_gap (Cls : (k : ℕ) → (Fin k → Finset (Fin 8) → ℝ) → Prop)
    (h2 : Cls 2 (fun _ => betaR)) (h4 : Cls 4 (fun _ => betaR))
    (h3 : ∀ v, Cls 3 v → ∀ i, IsMonotoneVal (v i)) :
    (¬ SpectrumYes Cls 2 ∧ SpectrumYes Cls 3 ∧ ¬ SpectrumYes Cls 4) ∧
      ¬ ChenZwickerShape (SpectrumYes Cls) := by
  have n2 : ¬ SpectrumYes Cls 2 := fun h => by
    obtain ⟨A, hA⟩ := h _ h2
    exact H_no_k2 (fun n : ℕ => (n : ℝ)) Nat.strictMono_cast A hA
  have y3 : SpectrumYes Cls 3 := fun v hv => H_yes_k3_hetero_monotone v (h3 v hv)
  have n4 : ¬ SpectrumYes Cls 4 := fun h => by
    obtain ⟨A, hA⟩ := h _ h4
    exact H_no_k4 (fun n : ℕ => (n : ℝ)) Nat.strictMono_cast A hA
  exact ⟨⟨n2, y3, n4⟩, not_shape _ n2 y3 n4⟩

/-! ### Valuation classes (real-valued, as in arXiv:2608.29902) -/

def commonBinaryAdditive : (k : ℕ) → (Fin k → Finset (Fin 8) → ℝ) → Prop :=
  fun _ v => ∃ w : Fin 8 → Bool, ∀ i S, v i S = (commonBinaryVal w S : ℝ)

def commonAdditive : (k : ℕ) → (Fin k → Finset (Fin 8) → ℝ) → Prop :=
  fun _ v => ∃ w : Fin 8 → ℝ, (∀ x, 0 ≤ w x) ∧ ∀ i S, v i S = ∑ x ∈ S, w x

def commonMonotone : (k : ℕ) → (Fin k → Finset (Fin 8) → ℝ) → Prop :=
  fun _ v => (∀ i j, v i = v j) ∧ ∀ i, IsMonotoneVal (v i) ∧ v i ∅ = 0

def heteroAdditive : (k : ℕ) → (Fin k → Finset (Fin 8) → ℝ) → Prop :=
  fun k v => ∃ w : Fin k → Fin 8 → ℝ, (∀ i x, 0 ≤ w i x) ∧ ∀ i S, v i S = ∑ x ∈ S, w i x

def heteroMonotone : (k : ℕ) → (Fin k → Finset (Fin 8) → ℝ) → Prop :=
  fun _ v => ∀ i, IsMonotoneVal (v i) ∧ v i ∅ = 0

def hubWR (x : Fin 8) : ℝ := if hubW x = true then 1 else 0

theorem betaR_eq_sum (S : Finset (Fin 8)) : betaR S = ∑ x ∈ S, hubWR x := by
  simp [betaR, beta, commonBinaryVal, hubWR, Finset.sum_boole]

theorem betaR_mono : IsMonotoneVal betaR := fun _ _ h =>
  Nat.cast_le.2 (card_le_card (filter_subset_filter _ h))

theorem betaR_empty : betaR ∅ = 0 := by simp [betaR, beta, commonBinaryVal]

theorem hubWR_nonneg (x : Fin 8) : 0 ≤ hubWR x := by unfold hubWR; split_ifs <;> norm_num

theorem additive_mono (w : Fin 8 → ℝ) (hw : ∀ x, 0 ≤ w x) :
    IsMonotoneVal (fun S : Finset (Fin 8) => ∑ x ∈ S, w x) := fun _ _ h =>
  sum_le_sum_of_subset_of_nonneg h fun x _ _ => hw x

/-- Headline: `H` is connected, and for each of the five valuation classes the EF1_outer
spectrum of `H` is no at `k = 2`, yes at `k = 3`, no at `k = 4`, contradicting Conjecture 1. -/
theorem not_chen_zwicker_conjecture_1 :
    H.Connected ∧
    ((¬ SpectrumYes commonBinaryAdditive 2 ∧ SpectrumYes commonBinaryAdditive 3 ∧
        ¬ SpectrumYes commonBinaryAdditive 4) ∧ ¬ ChenZwickerShape (SpectrumYes commonBinaryAdditive)) ∧
    ((¬ SpectrumYes commonAdditive 2 ∧ SpectrumYes commonAdditive 3 ∧
        ¬ SpectrumYes commonAdditive 4) ∧ ¬ ChenZwickerShape (SpectrumYes commonAdditive)) ∧
    ((¬ SpectrumYes commonMonotone 2 ∧ SpectrumYes commonMonotone 3 ∧
        ¬ SpectrumYes commonMonotone 4) ∧ ¬ ChenZwickerShape (SpectrumYes commonMonotone)) ∧
    ((¬ SpectrumYes heteroAdditive 2 ∧ SpectrumYes heteroAdditive 3 ∧
        ¬ SpectrumYes heteroAdditive 4) ∧ ¬ ChenZwickerShape (SpectrumYes heteroAdditive)) ∧
    ((¬ SpectrumYes heteroMonotone 2 ∧ SpectrumYes heteroMonotone 3 ∧
        ¬ SpectrumYes heteroMonotone 4) ∧ ¬ ChenZwickerShape (SpectrumYes heteroMonotone)) := by
  refine ⟨H_connected, ?_, ?_, ?_, ?_, ?_⟩
  · refine spectrum_gap _ ⟨hubW, fun _ _ => rfl⟩ ⟨hubW, fun _ _ => rfl⟩ ?_
    rintro v ⟨w, hw⟩ i S T hST
    rw [hw, hw]
    exact Nat.cast_le.2 (card_le_card (filter_subset_filter _ hST))
  · refine spectrum_gap _ ⟨hubWR, hubWR_nonneg, fun _ S => betaR_eq_sum S⟩
      ⟨hubWR, hubWR_nonneg, fun _ S => betaR_eq_sum S⟩ ?_
    rintro v ⟨w, hw0, hw⟩ i S T hST
    rw [hw, hw]
    exact additive_mono w hw0 S T hST
  · exact spectrum_gap _ ⟨fun _ _ => rfl, fun _ => ⟨betaR_mono, betaR_empty⟩⟩
      ⟨fun _ _ => rfl, fun _ => ⟨betaR_mono, betaR_empty⟩⟩ fun v hv i => (hv.2 i).1
  · refine spectrum_gap _ ⟨fun _ => hubWR, fun _ => hubWR_nonneg, fun _ S => betaR_eq_sum S⟩
      ⟨fun _ => hubWR, fun _ => hubWR_nonneg, fun _ S => betaR_eq_sum S⟩ ?_
    rintro v ⟨w, hw0, hw⟩ i S T hST
    rw [hw, hw]
    exact additive_mono (w i) (hw0 i) S T hST
  · exact spectrum_gap _ (fun _ => ⟨betaR_mono, betaR_empty⟩) (fun _ => ⟨betaR_mono, betaR_empty⟩)
      fun v hv i => (hv i).1

end ChenZwickerEF1Outer

#print axioms ChenZwickerEF1Outer.H_connected
#print axioms ChenZwickerEF1Outer.isConnectedBundle_iff_connected
#print axioms ChenZwickerEF1Outer.H_no_k2
#print axioms ChenZwickerEF1Outer.H_no_k4
#print axioms ChenZwickerEF1Outer.H_yes_k3_common_binary
#print axioms ChenZwickerEF1Outer.H_yes_k3_hetero_monotone
#print axioms ChenZwickerEF1Outer.spectrum_gap
#print axioms ChenZwickerEF1Outer.not_chen_zwicker_conjecture_1
