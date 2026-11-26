import Mathlib

/-!
# Odd-`n` Extremal Heap-Type Permutation Generation (Russo, arXiv:2611.22780v1)

This file resolves the open question in Section 10, item 2 (and the Section 7 remark on odd `n`)
of Luís M. S. Russo, *Heap-type permutation generation with a prescribed final arrangement*,
arXiv:2611.22780v1 (17 Nov 2026):

> "We found no closed formula for the parking order at the top level and no variant for odd
> $n \ge 7$ with the cyclic variant below it; whether other lower levels make the largest
> attainable arrangement reachable for odd $n$ is open."

We prove from first principles (without assuming any unproved lemma from the paper) that for
**every odd `n ≥ 3`**, there exists a Heap-type swap schedule whose recursive enumeration:
1. starts at the identity arrangement `1 : Equiv.Perm (Fin n)`,
2. visits all `n!` arrangements of `Fin n` exactly once (`List.Nodup` and length `n!`),
3. advances by a single transposition (swap of two positions) at every step, and
4. ends at `a*_n`, the unique lexicographically largest odd permutation in `S_n`
   (`rev_n` when `n ≡ 3 (mod 4)` and `rev_n * swap (n-2) (n-1)` when `n ≡ 1 (mod 4)`).
-/

namespace RussoHeapOddExtremal

open Equiv

/-! ### 1. Heap-type schedules and recursive enumeration -/

/-- A Heap-type schedule gives, for each level `k` and each inter-block step `m : Fin (k - 1)`,
the partner position `sched k m : Fin (k - 1)` to swap with position `k - 1`. -/
abbrev HeapSchedule := (k : ℕ) → Fin (k - 1) → Fin (k - 1)

/-- Run `Heap(k)` on `Equiv.Perm (Fin n)` starting from state `g`, returning the list of all
visited states (in left-multiplication state convention, where array `a = g⁻¹`) together with
the final state. Swapping positions `i` and `j` of array `a` produces `a * swap i j`, whose
inverse state is `swap i j * a⁻¹ = swap i j * g`. -/
def heapRun {n : ℕ} (sched : HeapSchedule) :
    (k : ℕ) → k ≤ n → Perm (Fin n) → List (Perm (Fin n)) × Perm (Fin n)
  | 0, _, g => ([g], g)
  | 1, _, g => ([g], g)
  | k + 2, hk, g =>
      let init := heapRun sched (k + 1) (by omega) g
      (List.finRange (k + 1)).foldl
        (fun acc m =>
          let pos : Fin n := ⟨(sched (k + 2) m).val, by
            have := (sched (k + 2) m).isLt; omega⟩
          let top : Fin n := ⟨k + 1, by omega⟩
          let g' := Equiv.swap pos top * acc.2
          let res := heapRun sched (k + 1) (by omega) g'
          (acc.1 ++ res.1, res.2))
        init

/-- The sequence of states visited by `Heap(k)` starting from `1`. -/
def heapStates {n : ℕ} (sched : HeapSchedule) (k : ℕ) (hk : k ≤ n) : List (Perm (Fin n)) :=
  (heapRun sched k hk 1).1

/-- The net state transformation of `Heap(k)`. -/
def heapNet {n : ℕ} (sched : HeapSchedule) (k : ℕ) (hk : k ≤ n) : Perm (Fin n) :=
  (heapRun sched k hk 1).2

/-- The sequence of arrays (`a = g⁻¹`) visited by `Heap(n)` starting from `1`. -/
def heapArrays {n : ℕ} (sched : HeapSchedule) : List (Perm (Fin n)) :=
  (heapStates sched n le_rfl).map (·⁻¹)

/-- Adjacent-swap relation on states: `b = swap i j * a` for distinct `i, j`. -/
def AdjState {n : ℕ} (a b : Perm (Fin n)) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ b = Equiv.swap i j * a

/-- Adjacent-swap relation on arrays: `b = a * swap i j` for distinct `i, j`. -/
def AdjArray {n : ℕ} (a b : Perm (Fin n)) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ b = a * Equiv.swap i j

private lemma adjState_mul_right {n : ℕ} {a b : Perm (Fin n)} (g : Perm (Fin n))
    (h : AdjState a b) : AdjState (a * g) (b * g) := by
  rcases h with ⟨i, j, hij, rfl⟩
  exact ⟨i, j, hij, by simp [mul_assoc]⟩

private lemma adjArray_of_adjState {n : ℕ} {a b : Perm (Fin n)}
    (h : AdjState a b) : AdjArray a⁻¹ b⁻¹ := by
  rcases h with ⟨i, j, hij, rfl⟩
  exact ⟨i, j, hij, by simp [mul_inv_rev, Equiv.swap_inv]⟩

private lemma isChain_append_of_adj {α : Type*} {R : α → α → Prop} {l₁ l₂ : List α}
    (h₁ : l₁.IsChain R) (h₂ : l₂.IsChain R)
    (hjoin : ∀ a b, l₁.getLast? = some a → l₂.head? = some b → R a b) :
    (l₁ ++ l₂).IsChain R := by
  induction l₁ with
  | nil => simpa using h₂
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases l₂ with
          | nil => exact List.IsChain.singleton x
          | cons y ys =>
              exact List.IsChain.cons_cons (hjoin x y rfl rfl) h₂
      | cons y ys =>
          rcases List.isChain_cons_cons.mp h₁ with ⟨hxy, htail⟩
          have htail' := ih htail (by
            intro a b ha hb
            exact hjoin a b (by simpa using ha) hb)
          exact List.IsChain.cons_cons hxy htail'

/-- Right-equivariance of `heapRun`. -/
private lemma heapRun_mul_right {n : ℕ} (sched : HeapSchedule) :
    ∀ (k : ℕ) (hk : k ≤ n) (g : Perm (Fin n)),
      heapRun sched k hk g = ((heapRun sched k hk 1).1.map (· * g), (heapRun sched k hk 1).2 * g)
  | 0, _, g => by simp [heapRun]
  | 1, _, g => by simp [heapRun]
  | k + 2, hk, g => by
      have ih := heapRun_mul_right (n := n) sched (k + 1) (by omega)
      simp only [heapRun]
      have hfold :
          ∀ (ms : List (Fin (k + 1))) (acc : List (Perm (Fin n)) × Perm (Fin n)),
            ms.foldl
              (fun a m =>
                let pos : Fin n := ⟨(sched (k + 2) m).val, by
                  have := (sched (k + 2) m).isLt; omega⟩
                let top : Fin n := ⟨k + 1, by omega⟩
                let g' := Equiv.swap pos top * a.2
                let res := heapRun sched (k + 1) (by omega) g'
                (a.1 ++ res.1, res.2))
              (acc.1.map (· * g), acc.2 * g) =
            let r := ms.foldl
              (fun a m =>
                let pos : Fin n := ⟨(sched (k + 2) m).val, by
                  have := (sched (k + 2) m).isLt; omega⟩
                let top : Fin n := ⟨k + 1, by omega⟩
                let g' := Equiv.swap pos top * a.2
                let res := heapRun sched (k + 1) (by omega) g'
                (a.1 ++ res.1, res.2))
              acc
            (r.1.map (· * g), r.2 * g) := by
        intro ms
        induction ms with
        | nil => intro acc; rfl
        | cons m ms ihms =>
            intro acc
            simp only [List.foldl_cons]
            set pos : Fin n := ⟨(sched (k + 2) m).val, by
              have := (sched (k + 2) m).isLt; omega⟩
            set top : Fin n := ⟨k + 1, by omega⟩
            have h1 := ih (Equiv.swap pos top * acc.2 * g)
            have h2 := ih (Equiv.swap pos top * acc.2)
            have hmul : Equiv.swap pos top * (acc.2 * g) = (Equiv.swap pos top * acc.2) * g := by
              rw [mul_assoc]
            rw [hmul, h1, h2]
            have hmap :
                acc.1.map (· * g) ++ (heapRun sched (k + 1) (by omega) 1).1.map
                  (· * (Equiv.swap pos top * acc.2 * g)) =
                (acc.1 ++ (heapRun sched (k + 1) (by omega) 1).1.map
                  (· * (Equiv.swap pos top * acc.2))).map (· * g) := by
              simp [List.map_append, List.map_map, Function.comp_def, mul_assoc]
            have hfin :
                (heapRun sched (k + 1) (by omega) 1).2 * (Equiv.swap pos top * acc.2 * g) =
                ((heapRun sched (k + 1) (by omega) 1).2 * (Equiv.swap pos top * acc.2)) * g := by
              rw [← mul_assoc]
            rw [hmap, hfin]
            exact ihms (acc.1 ++ (heapRun sched (k + 1) (by omega) 1).1.map
              (· * (Equiv.swap pos top * acc.2)),
              (heapRun sched (k + 1) (by omega) 1).2 * (Equiv.swap pos top * acc.2))
      rw [ih g]
      exact hfold (List.finRange (k + 1)) (heapRun sched (k + 1) (by omega) 1)

/-- Basic structural invariants of `heapRun`: head, last, length, adjacency, and support. -/
private lemma heapRun_basic {n : ℕ} (sched : HeapSchedule) :
    ∀ (k : ℕ) (hk : k ≤ n) (_hk1 : 1 ≤ k),
      (heapStates sched k hk).head? = some 1 ∧
      (heapStates sched k hk).getLast? = some (heapNet sched k hk) ∧
      (heapStates sched k hk).length = Nat.factorial k ∧
      (heapStates sched k hk).IsChain AdjState ∧
      (∀ p ∈ heapStates sched k hk, ∀ x : Fin n, k ≤ x.val → p x = x)
  | 0, _, hk1 => by omega
  | 1, hk, _ => by
      refine ⟨rfl, rfl, rfl, List.IsChain.singleton 1, ?_⟩
      intro p hp x _
      simp only [heapStates, heapRun, List.mem_singleton] at hp
      subst hp; rfl
  | k + 2, hk, _ => by
      have ih := heapRun_basic (n := n) sched (k + 1) (by omega) (by omega)
      rcases ih with ⟨ih_head, ih_last, ih_len, ih_chain, ih_fix⟩
      let step : List (Perm (Fin n)) × Perm (Fin n) → Fin (k + 1) →
          List (Perm (Fin n)) × Perm (Fin n) := fun a m =>
        let pos : Fin n := ⟨(sched (k + 2) m).val, by
          have := (sched (k + 2) m).isLt; omega⟩
        let top : Fin n := ⟨k + 1, by omega⟩
        let g' := Equiv.swap pos top * a.2
        let r := heapRun sched (k + 1) (by omega) g'
        (a.1 ++ r.1, r.2)
      have hfold :
          ∀ (ms : List (Fin (k + 1))) (acc : List (Perm (Fin n)) × Perm (Fin n)),
            acc.1.head? = some 1 →
            acc.1.getLast? = some acc.2 →
            acc.1.IsChain AdjState →
            (∀ p ∈ acc.1, ∀ x : Fin n, k + 2 ≤ x.val → p x = x) →
            let res := ms.foldl step acc
            res.1.head? = some 1 ∧
            res.1.getLast? = some res.2 ∧
            res.1.length = acc.1.length + ms.length * Nat.factorial (k + 1) ∧
            res.1.IsChain AdjState ∧
            (∀ p ∈ res.1, ∀ x : Fin n, k + 2 ≤ x.val → p x = x) := by
        intro ms
        induction ms with
        | nil =>
            intro acc hhead hlast hchain hfix
            exact ⟨hhead, hlast, by simp, hchain, hfix⟩
        | cons m ms ihms =>
            intro acc hhead hlast hchain hfix
            simp only [List.foldl_cons]
            set pos : Fin n := ⟨(sched (k + 2) m).val, by
              have := (sched (k + 2) m).isLt; omega⟩
            set top : Fin n := ⟨k + 1, by omega⟩
            set g' := Equiv.swap pos top * acc.2
            have hr := heapRun_mul_right sched (k + 1) (by omega) g'
            have hne_acc : acc.1 ≠ [] := by
              intro h; rw [h] at hhead; simp at hhead
            have hr_head : (heapRun sched (k + 1) (by omega) g').1.head? = some g' := by
              rw [hr]
              show ((heapStates sched (k + 1) (by omega)).map (· * g')).head? = some g'
              rw [List.head?_map, ih_head]
              simp
            have hr_last : (heapRun sched (k + 1) (by omega) g').1.getLast? =
                some (heapRun sched (k + 1) (by omega) g').2 := by
              rw [hr]
              show ((heapStates sched (k + 1) (by omega)).map (· * g')).getLast? =
                some (heapNet sched (k + 1) (by omega) * g')
              rw [List.getLast?_map, ih_last]
              simp
            have hr_len : (heapRun sched (k + 1) (by omega) g').1.length = Nat.factorial (k + 1) := by
              rw [hr]; simpa [heapStates] using ih_len
            have hr_chain : (heapRun sched (k + 1) (by omega) g').1.IsChain AdjState := by
              rw [hr]
              exact (List.isChain_map (· * g')).mpr (ih_chain.imp fun _ _ h => adjState_mul_right g' h)
            have hpos_lt : pos.val < k + 1 := (sched (k + 2) m).isLt
            have htop_val : top.val = k + 1 := rfl
            have hpos_ne : pos ≠ top := fun h => by
              have : pos.val = top.val := congrArg Fin.val h
              omega
            have hacc2_fix : ∀ x : Fin n, k + 2 ≤ x.val → acc.2 x = x :=
              hfix acc.2 (List.mem_of_getLast? hlast)
            have hg'_fix : ∀ x : Fin n, k + 2 ≤ x.val → g' x = x := by
              intro x hx
              simp only [g', Equiv.Perm.mul_apply, hacc2_fix x hx]
              apply Equiv.swap_apply_of_ne_of_ne
              · intro h; have := congrArg Fin.val h; omega
              · intro h; have := congrArg Fin.val h; omega
            have hr_fix : ∀ p ∈ (heapRun sched (k + 1) (by omega) g').1,
                ∀ x : Fin n, k + 2 ≤ x.val → p x = x := by
              intro p hp x hx
              rw [hr] at hp
              rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
              simp only [Equiv.Perm.mul_apply, hg'_fix x hx]
              exact ih_fix q hq x (by omega)
            have hnext_head : (step acc m).1.head? = some 1 := by
              dsimp only [step]
              rw [List.head?_append_of_ne_nil _ hne_acc, hhead]
            have hnext_last : (step acc m).1.getLast? = some (step acc m).2 := by
              dsimp only [step]
              have hne_r : (heapRun sched (k + 1) (by omega) g').1 ≠ [] := by
                intro h; rw [h] at hr_head; simp at hr_head
              rw [List.getLast?_append_of_ne_nil _ hne_r, hr_last]
            have hnext_chain : (step acc m).1.IsChain AdjState := by
              dsimp only [step]
              apply isChain_append_of_adj hchain hr_chain
              intro a b ha hb
              rw [hlast] at ha; rw [hr_head] at hb
              cases ha; cases hb
              exact ⟨pos, top, hpos_ne, rfl⟩
            have hnext_fix : ∀ p ∈ (step acc m).1, ∀ x : Fin n, k + 2 ≤ x.val → p x = x := by
              dsimp only [step]
              intro p hp x hx
              rcases List.mem_append.mp hp with hp1 | hp2
              · exact hfix p hp1 x hx
              · exact hr_fix p hp2 x hx
            have hres := ihms (step acc m) hnext_head hnext_last hnext_chain hnext_fix
            refine ⟨hres.1, hres.2.1, ?_, hres.2.2.2.1, hres.2.2.2.2⟩
            have hstep_len : (step acc m).1.length = acc.1.length + Nat.factorial (k + 1) := by
              dsimp only [step]; rw [List.length_append, hr_len]
            rw [hres.2.2.1, hstep_len, List.length_cons]
            ring
      have hinit_fix : ∀ p ∈ heapStates sched (k + 1) (by omega),
          ∀ x : Fin n, k + 2 ≤ x.val → p x = x := fun p hp x hx => ih_fix p hp x (by omega)
      have hres := hfold (List.finRange (k + 1)) (heapRun sched (k + 1) (by omega) 1)
        ih_head ih_last ih_chain hinit_fix
      refine ⟨hres.1, hres.2.1, ?_, hres.2.2.2.1, hres.2.2.2.2⟩
      change ((List.finRange (k + 1)).foldl step (heapRun sched (k + 1) (by omega) 1)).1.length =
        Nat.factorial (k + 2)
      rw [hres.2.2.1, List.length_finRange]
      have hlen1 : (heapRun (n := n) sched (k + 1) (by omega) 1).1.length = Nat.factorial (k + 1) := ih_len
      rw [hlen1, show k + 2 = (k + 1) + 1 from rfl, Nat.factorial_succ (k + 1)]
      ring

/-- A schedule only matters at levels `≤ k` for `heapRun sched k`. -/
private lemma heapRun_congr_sched {n : ℕ} (s₁ s₂ : HeapSchedule) :
    ∀ (k : ℕ) (hk : k ≤ n) (g : Perm (Fin n)),
      (∀ j ≤ k, s₁ j = s₂ j) →
      heapRun s₁ k hk g = heapRun s₂ k hk g
  | 0, _, _, _ => rfl
  | 1, _, _, _ => rfl
  | k + 2, hk, g, hEq => by
      have hlow : ∀ j ≤ k + 1, s₁ j = s₂ j := fun j hj => hEq j (by omega)
      have htop : s₁ (k + 2) = s₂ (k + 2) := hEq (k + 2) le_rfl
      simp only [heapRun]
      rw [heapRun_congr_sched s₁ s₂ (k + 1) (by omega) g hlow]
      have hstep :
          (fun (acc : List (Perm (Fin n)) × Perm (Fin n)) (m : Fin (k + 1)) =>
            let pos : Fin n := ⟨(s₁ (k + 2) m).val, by
              have := (s₁ (k + 2) m).isLt; omega⟩
            let top : Fin n := ⟨k + 1, by omega⟩
            let g' := Equiv.swap pos top * acc.2
            let res := heapRun s₁ (k + 1) (by omega) g'
            (acc.1 ++ res.1, res.2)) =
          (fun (acc : List (Perm (Fin n)) × Perm (Fin n)) (m : Fin (k + 1)) =>
            let pos : Fin n := ⟨(s₂ (k + 2) m).val, by
              have := (s₂ (k + 2) m).isLt; omega⟩
            let top : Fin n := ⟨k + 1, by omega⟩
            let g' := Equiv.swap pos top * acc.2
            let res := heapRun s₂ (k + 1) (by omega) g'
            (acc.1 ++ res.1, res.2)) := by
        funext acc m
        dsimp only
        have hpos : (⟨(s₁ (k + 2) m).val, by have := (s₁ (k + 2) m).isLt; omega⟩ : Fin n) =
            ⟨(s₂ (k + 2) m).val, by have := (s₂ (k + 2) m).isLt; omega⟩ := by
          apply Fin.ext; simp [htop]
        rw [hpos, heapRun_congr_sched s₁ s₂ (k + 1) (by omega) _ hlow]
      exact congrArg (fun f => (List.finRange (k + 1)).foldl f _) hstep

/-! ### 2. Parking orders, cycle nets, and Russo's Theorem 18 (self-contained proof) -/

/-- Embed `Fin k` into `Fin n` when `k ≤ n`. -/
def emb {k n : ℕ} (hk : k ≤ n) (i : Fin k) : Fin n := ⟨i.val, by omega⟩

private lemma fin_mk_emb {k n : ℕ} (hk : k ≤ n) (a : Fin k) (h : (emb hk a).val < k) :
    (⟨(emb hk a).val, h⟩ : Fin k) = a := Fin.ext rfl

/-- Given a bijection `ord : Fin k ≃ Fin k` (where `k ≤ n`), the `k`-cycle on `Fin n`
sending `ord i ↦ ord ((i + 1) % k)` and fixing all `x ≥ k`. -/
def cyclePerm {n k : ℕ} (hk : k ≤ n) (hk0 : 0 < k) (ord : Fin k ≃ Fin k) : Perm (Fin n) where
  toFun x :=
    if hx : x.val < k then
      emb hk (ord ⟨((ord.symm ⟨x.val, hx⟩).val + 1) % k, Nat.mod_lt _ hk0⟩)
    else x
  invFun x :=
    if hx : x.val < k then
      emb hk (ord ⟨((ord.symm ⟨x.val, hx⟩).val + (k - 1)) % k, Nat.mod_lt _ hk0⟩)
    else x
  left_inv x := by
    by_cases hx : x.val < k
    · have hlt : (emb hk (ord ⟨((ord.symm ⟨x.val, hx⟩).val + 1) % k, Nat.mod_lt _ hk0⟩)).val < k :=
        (ord _).isLt
      simp only [hx, ↓reduceDIte, hlt, fin_mk_emb, Equiv.symm_apply_apply]
      have hmod : (((ord.symm ⟨x.val, hx⟩).val + 1) % k + (k - 1)) % k =
          (ord.symm ⟨x.val, hx⟩).val := by
        have hi := (ord.symm ⟨x.val, hx⟩).isLt
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have : (ord.symm ⟨x.val, hx⟩).val + 1 + (k - 1) = (ord.symm ⟨x.val, hx⟩).val + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      have h2 : (⟨(((ord.symm ⟨x.val, hx⟩).val + 1) % k + (k - 1)) % k, Nat.mod_lt _ hk0⟩ : Fin k) =
          ord.symm ⟨x.val, hx⟩ := Fin.ext hmod
      rw [h2, Equiv.apply_symm_apply]
      exact Fin.ext rfl
    · simp only [hx, ↓reduceDIte]
  right_inv x := by
    by_cases hx : x.val < k
    · have hlt : (emb hk (ord ⟨((ord.symm ⟨x.val, hx⟩).val + (k - 1)) % k, Nat.mod_lt _ hk0⟩)).val < k :=
        (ord _).isLt
      simp only [hx, ↓reduceDIte, hlt, fin_mk_emb, Equiv.symm_apply_apply]
      have hmod : (((ord.symm ⟨x.val, hx⟩).val + (k - 1)) % k + 1) % k =
          (ord.symm ⟨x.val, hx⟩).val := by
        have hi := (ord.symm ⟨x.val, hx⟩).isLt
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have : (ord.symm ⟨x.val, hx⟩).val + (k - 1) + 1 = (ord.symm ⟨x.val, hx⟩).val + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      have h2 : (⟨(((ord.symm ⟨x.val, hx⟩).val + (k - 1)) % k + 1) % k, Nat.mod_lt _ hk0⟩ : Fin k) =
          ord.symm ⟨x.val, hx⟩ := Fin.ext hmod
      rw [h2, Equiv.apply_symm_apply]
      exact Fin.ext rfl
    · simp only [hx, ↓reduceDIte]

private lemma cyclePerm_apply_ord {n k : ℕ} (hk : k ≤ n) (hk0 : 0 < k)
    (ord : Fin k ≃ Fin k) (i : Fin k) :
    cyclePerm hk hk0 ord (emb hk (ord i)) = emb hk (ord ⟨(i.val + 1) % k, Nat.mod_lt _ hk0⟩) := by
  have hlt : (emb hk (ord i)).val < k := (ord i).isLt
  simp only [cyclePerm, Equiv.coe_fn_mk, hlt, ↓reduceDIte, fin_mk_emb, Equiv.symm_apply_apply]

private lemma cyclePerm_apply_ge {n k : ℕ} (hk : k ≤ n) (hk0 : 0 < k)
    (ord : Fin k ≃ Fin k) (x : Fin n) (hx : k ≤ x.val) :
    cyclePerm hk hk0 ord x = x := by
  have hnot : ¬ x.val < k := by omega
  simp only [cyclePerm, Equiv.coe_fn_mk, hnot, ↓reduceDIte]

private lemma cyclePerm_pow_apply_ord {n k : ℕ} (hk : k ≤ n) (hk0 : 0 < k)
    (ord : Fin k ≃ Fin k) (r : ℕ) (i : Fin k) :
    (cyclePerm hk hk0 ord ^ r) (emb hk (ord i)) =
      emb hk (ord ⟨(i.val + r) % k, Nat.mod_lt _ hk0⟩) := by
  induction r with
  | zero =>
      simp only [pow_zero, Equiv.Perm.one_apply, Nat.add_zero]
      have h1 : (⟨i.val % k, Nat.mod_lt _ hk0⟩ : Fin k) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
      rw [h1]
  | succ r ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, cyclePerm_apply_ord]
      have h1 : (⟨((i.val + r) % k + 1) % k, Nat.mod_lt _ hk0⟩ : Fin k) =
          ⟨(i.val + (r + 1)) % k, Nat.mod_lt _ hk0⟩ := by
        apply Fin.ext; simp only; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]
      rw [h1]

private lemma cyclePerm_pow_self {n k : ℕ} (hk : k ≤ n) (hk0 : 0 < k)
    (ord : Fin k ≃ Fin k) :
    cyclePerm hk hk0 ord ^ k = 1 := by
  ext x
  by_cases hx : x.val < k
  · set i := ord.symm ⟨x.val, hx⟩
    have hx_eq : x = emb hk (ord i) := by
      apply Fin.ext; simp [emb, i]
    rw [hx_eq, cyclePerm_pow_apply_ord]
    have h1 : (⟨(i.val + k) % k, Nat.mod_lt _ hk0⟩ : Fin k) = i :=
      Fin.ext (by simp only; rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt])
    rw [h1]; rfl
  · have hfix : ∀ r, (cyclePerm hk hk0 ord ^ r) x = x := by
      intro r; induction r with
      | zero => rfl
      | succ r ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, cyclePerm_apply_ge hk hk0 ord x (by omega)]
    rw [hfix k]; rfl

/-- Left-to-right product of adjacent swaps `swap (ord 1) (ord 0) * ... * swap (ord m) (ord (m-1))`. -/
private def swapChain {n k : ℕ} (hk : k ≤ n) (ord : Fin k ≃ Fin k) :
    (m : ℕ) → m < k → Perm (Fin n)
  | 0, _ => 1
  | m + 1, hm =>
      swapChain hk ord m (by omega) *
        Equiv.swap (emb hk (ord ⟨m + 1, hm⟩)) (emb hk (ord ⟨m, by omega⟩))

private lemma swapChain_apply_top {n k : ℕ} (hk : k ≤ n) (ord : Fin k ≃ Fin k) :
    ∀ (m : ℕ) (hm : m < k),
      swapChain hk ord m hm (emb hk (ord ⟨m, hm⟩)) = emb hk (ord ⟨0, by omega⟩)
  | 0, _ => rfl
  | m + 1, hm => by
      simp only [swapChain, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      exact swapChain_apply_top hk ord m (by omega)

private lemma swapChain_apply_gt {n k : ℕ} (hk : k ≤ n) (ord : Fin k ≃ Fin k) :
    ∀ (m : ℕ) (hm : m < k) (j : Fin k), m < j.val →
      swapChain hk ord m hm (emb hk (ord j)) = emb hk (ord j)
  | 0, _, _, _ => rfl
  | m + 1, hm, j, hj => by
      simp only [swapChain, Equiv.Perm.mul_apply]
      have hne1 : emb hk (ord j) ≠ emb hk (ord ⟨m + 1, hm⟩) := by
        intro h
        have h1 : ord j = ord ⟨m + 1, hm⟩ := Fin.ext (by simpa [emb] using congrArg Fin.val h)
        have h2 : j = ⟨m + 1, hm⟩ := ord.injective h1
        have : j.val = m + 1 := congrArg Fin.val h2
        omega
      have hne2 : emb hk (ord j) ≠ emb hk (ord ⟨m, by omega⟩) := by
        intro h
        have h1 : ord j = ord ⟨m, by omega⟩ := Fin.ext (by simpa [emb] using congrArg Fin.val h)
        have h2 : j = ⟨m, by omega⟩ := ord.injective h1
        have : j.val = m := congrArg Fin.val h2
        omega
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      exact swapChain_apply_gt hk ord m (by omega) j (by omega)

private lemma swapChain_apply_lt {n k : ℕ} (hk : k ≤ n) (ord : Fin k ≃ Fin k) :
    ∀ (m : ℕ) (hm : m < k) (j : Fin k) (hj : j.val < m),
      swapChain hk ord m hm (emb hk (ord j)) = emb hk (ord ⟨j.val + 1, by omega⟩)
  | 0, _, j, hj => by omega
  | m + 1, hm, j, hj => by
      simp only [swapChain, Equiv.Perm.mul_apply]
      by_cases hjm : j.val = m
      · have hj_eq : j = ⟨m, by omega⟩ := Fin.ext hjm
        have hsw : (Equiv.swap (emb hk (ord ⟨m + 1, hm⟩)) (emb hk (ord ⟨m, by omega⟩))) (emb hk (ord j)) =
            emb hk (ord ⟨m + 1, hm⟩) := by
          have harg : emb hk (ord j) = emb hk (ord ⟨m, by omega⟩) :=
            congrArg (fun a => emb hk (ord a)) hj_eq
          rw [harg, Equiv.swap_apply_right]
        rw [hsw, swapChain_apply_gt hk ord m (by omega) ⟨m + 1, hm⟩ (by simp)]
        congr 2; exact Fin.ext (by simp [hjm])
      · have hjlt : j.val < m := by omega
        have hne1 : emb hk (ord j) ≠ emb hk (ord ⟨m + 1, hm⟩) := by
          intro h
          have : j.val = m + 1 := congrArg Fin.val (ord.injective (Fin.ext (by simpa [emb] using congrArg Fin.val h)))
          omega
        have hne2 : emb hk (ord j) ≠ emb hk (ord ⟨m, by omega⟩) := by
          intro h
          have : j.val = m := congrArg Fin.val (ord.injective (Fin.ext (by simpa [emb] using congrArg Fin.val h)))
          omega
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
        exact swapChain_apply_lt hk ord m (by omega) j hjlt

private lemma swapChain_apply_ge {n k : ℕ} (hk : k ≤ n) (ord : Fin k ≃ Fin k) :
    ∀ (m : ℕ) (hm : m < k) (x : Fin n), k ≤ x.val →
      swapChain hk ord m hm x = x
  | 0, _, _, _ => rfl
  | m + 1, hm, x, hx => by
      simp only [swapChain, Equiv.Perm.mul_apply]
      have hne1 : x ≠ emb hk (ord ⟨m + 1, hm⟩) := by
        intro h; have h1 := (ord ⟨m + 1, hm⟩).isLt; have := congrArg Fin.val h; simp [emb] at this; omega
      have hne2 : x ≠ emb hk (ord ⟨m, by omega⟩) := by
        intro h; have h1 := (ord ⟨m, by omega⟩).isLt; have := congrArg Fin.val h; simp [emb] at this; omega
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      exact swapChain_apply_ge hk ord m (by omega) x hx

/-- The full `swapChain` equals the `k`-cycle `cyclePerm hk hk0 ord`. -/
private lemma swapChain_eq_cyclePerm {n k : ℕ} (hk : k ≤ n) (hk0 : 0 < k) (ord : Fin k ≃ Fin k) :
    swapChain hk ord (k - 1) (by omega) = cyclePerm hk hk0 ord := by
  ext x
  by_cases hx : x.val < k
  · set j := ord.symm ⟨x.val, hx⟩
    have hx_eq : x = emb hk (ord j) := Fin.ext (by simp [emb, j])
    rw [hx_eq, cyclePerm_apply_ord]
    by_cases htop : j.val = k - 1
    · have hj_eq : j = ⟨k - 1, by omega⟩ := Fin.ext htop
      rw [hj_eq, swapChain_apply_top]
      have hmod : (⟨(k - 1 + 1) % k, Nat.mod_lt _ hk0⟩ : Fin k) = ⟨0, hk0⟩ := by
        apply Fin.ext; have : k - 1 + 1 = k := by omega
        simp [this]
      rw [hmod]
    · have hjlt : j.val < k - 1 := by omega
      rw [swapChain_apply_lt hk ord (k - 1) (by omega) j hjlt]
      have hmod : (⟨(j.val + 1) % k, Nat.mod_lt _ hk0⟩ : Fin k) = ⟨j.val + 1, by omega⟩ :=
        Fin.ext (Nat.mod_eq_of_lt (by omega))
      rw [hmod]
  · rw [swapChain_apply_ge hk ord (k - 1) (by omega) x (by omega),
        cyclePerm_apply_ge hk hk0 ord x (by omega)]

/-- **Self-contained proof of Russo's Theorem 18 (level lifting by parking order):**
Given any schedule `sched` whose level `k + 1` (`k + 2 ≤ n`) produces a `Nodup` state list
with net `C`, and any parking bijection `ord : Fin (k + 2) ≃ Fin (k + 2)` with
`ord 0 = ⟨k + 1, _⟩`, modifying `sched` ONLY at level `k + 2` yields a schedule whose level
`k + 2` state list is `Nodup` and has net `C ^ (k + 2) * cyclePerm _ _ ord`. -/
theorem heap_extend_level {n k : ℕ} (hk : k + 2 ≤ n)
    (sched : HeapSchedule)
    (hNodup : (heapStates (n := n) sched (k + 1) (by omega)).Nodup)
    (ord : Fin (k + 2) ≃ Fin (k + 2))
    (hord0 : ord 0 = ⟨k + 1, by omega⟩) :
    ∃ sched' : HeapSchedule,
      (∀ j ≤ k + 1, sched' j = sched j) ∧
      (heapStates (n := n) sched' (k + 2) hk).Nodup ∧
      heapNet (n := n) sched' (k + 2) hk =
        (heapNet (n := n) sched (k + 1) (by omega)) ^ (k + 2) * cyclePerm hk (by omega) ord := by
  set C := heapNet (n := n) sched (k + 1) (by omega)
  have hbasic := heapRun_basic (n := n) sched (k + 1) (by omega) (by omega)
  have hC_mem : C ∈ heapStates (n := n) sched (k + 1) (by omega) := List.mem_of_getLast? hbasic.2.1
  have hC_fix : ∀ x : Fin n, k + 1 ≤ x.val → C x = x := hbasic.2.2.2.2 C hC_mem
  have hCpow_fix : ∀ r (x : Fin n), k + 1 ≤ x.val → (C ^ r) x = x := by
    intro r x hx
    induction r with
    | zero => rfl
    | succ r ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hC_fix x hx]
  let G : (m : ℕ) → m < k + 2 → Perm (Fin n) := fun m hm =>
    C ^ m * swapChain hk ord m hm
  have hG_top : ∀ m (hm : m < k + 2), G m hm (emb hk (ord ⟨m, hm⟩)) = ⟨k + 1, by omega⟩ := by
    intro m hm
    simp only [G, Equiv.Perm.mul_apply, swapChain_apply_top]
    have h0 : emb hk (ord ⟨0, by omega⟩) = (⟨k + 1, by omega⟩ : Fin n) := by
      apply Fin.ext; simp [emb, hord0]
    rw [h0]
    exact hCpow_fix m ⟨k + 1, by omega⟩ le_rfl
  have hG_fix : ∀ m (hm : m < k + 2) (x : Fin n), k + 2 ≤ x.val → G m hm x = x := by
    intro m hm x hx
    simp only [G, Equiv.Perm.mul_apply]
    rw [swapChain_apply_ge hk ord m hm x hx]
    exact hCpow_fix m x (by omega)
  have hpos_lt : ∀ m : Fin (k + 1),
      ((C * G m.val (by have := m.isLt; omega))
        (emb hk (ord ⟨m.val + 1, by have := m.isLt; omega⟩))).val < k + 1 := by
    intro m
    have hm := m.isLt
    set y := (C * G m.val (by omega)) (emb hk (ord ⟨m.val + 1, by omega⟩))
    have hlt2 : y.val < k + 2 := by
      by_contra hge
      have hfix : (C * G m.val (by omega)) y = y := by
        simp only [Equiv.Perm.mul_apply]
        rw [hG_fix m.val (by omega) y (by omega), hC_fix y (by omega)]
      have hy_eq : emb hk (ord ⟨m.val + 1, by omega⟩) = y :=
        (C * G m.val (by omega)).injective hfix.symm
      have : y.val < k + 2 := by
        rw [← hy_eq]; exact (ord ⟨m.val + 1, by omega⟩).isLt
      omega
    have hne : y ≠ (⟨k + 1, by omega⟩ : Fin n) := by
      intro heq
      have htop_eq : (C * G m.val (by omega)) (emb hk (ord ⟨m.val, by omega⟩)) =
          ⟨k + 1, by omega⟩ := by
        simp only [Equiv.Perm.mul_apply, hG_top m.val (by omega)]
        exact hC_fix ⟨k + 1, by omega⟩ le_rfl
      have hinj := (C * G m.val (by omega)).injective (heq.trans htop_eq.symm)
      have hord_eq : ord ⟨m.val + 1, by omega⟩ = ord ⟨m.val, by omega⟩ :=
        Fin.ext (by simpa [emb] using congrArg Fin.val hinj)
      have hfin_eq := ord.injective hord_eq
      have : m.val + 1 = m.val := congrArg Fin.val hfin_eq
      omega
    have : y.val ≠ k + 1 := fun h => hne (Fin.ext h)
    omega
  let levelFn : Fin (k + 1) → Fin (k + 1) := fun m =>
    ⟨((C * G m.val (by have := m.isLt; omega))
      (emb hk (ord ⟨m.val + 1, by have := m.isLt; omega⟩))).val, hpos_lt m⟩
  let sched' : HeapSchedule := fun j =>
    if h : j = k + 2 then
      h ▸ levelFn
    else
      sched j
  have hsched_low : ∀ j ≤ k + 1, sched' j = sched j := by
    intro j hj
    have hne : j ≠ k + 2 := by omega
    simp [sched', hne]
  have hsched_top : sched' (k + 2) = levelFn := by
    simp [sched']
  let step : List (Perm (Fin n)) × Perm (Fin n) → Fin (k + 1) →
      List (Perm (Fin n)) × Perm (Fin n) := fun acc m =>
    let pos : Fin n := ⟨(sched' (k + 2) m).val, by
      have := (sched' (k + 2) m).isLt; omega⟩
    let top : Fin n := ⟨k + 1, by omega⟩
    let g' := Equiv.swap pos top * acc.2
    let sub := heapRun sched' (k + 1) (by omega) g'
    (acc.1 ++ sub.1, sub.2)
  have hprefix :
      ∀ (r : ℕ) (hr : r ≤ k + 1),
        let res := ((List.finRange (k + 1)).take r).foldl step
          (heapRun sched' (k + 1) (by omega) 1)
        res.2 = C * G r (by omega) ∧
        res.1.Nodup ∧
        (∀ p ∈ res.1, ∃ j : ℕ, j ≤ r ∧ ∃ hj : j < k + 2,
          p⁻¹ ⟨k + 1, by omega⟩ = emb hk (ord ⟨j, hj⟩)) := by
    intro r
    induction r with
    | zero =>
        intro hr
        simp only [List.take_zero, List.foldl_nil]
        have hcongr := heapRun_congr_sched (n := n) sched' sched (k + 1) (by omega) 1 hsched_low
        rw [hcongr]
        refine ⟨by simp [C, G, swapChain, heapNet], hNodup, ?_⟩
        intro p hp
        refine ⟨0, le_rfl, by omega, ?_⟩
        have hfix : p ⟨k + 1, by omega⟩ = ⟨k + 1, by omega⟩ := hbasic.2.2.2.2 p hp _ le_rfl
        have hinv : p⁻¹ ⟨k + 1, by omega⟩ = ⟨k + 1, by omega⟩ := by
          apply p.injective; simp [hfix]
        rw [hinv]
        apply Fin.ext; simp [emb, hord0]
    | succ r ihr =>
        intro hr
        have hih := ihr (by omega)
        have htake : (List.finRange (k + 1)).take (r + 1) =
            (List.finRange (k + 1)).take r ++ [⟨r, by omega⟩] := by
          rw [List.take_succ_eq_append_getElem (by simp; omega)]
          simp
        simp only [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
        set acc := ((List.finRange (k + 1)).take r).foldl step
          (heapRun sched' (k + 1) (by omega) 1)
        rcases hih with ⟨hacc_fin, hacc_nodup, hacc_tag⟩
        set m : Fin (k + 1) := ⟨r, by omega⟩
        set pos : Fin n := ⟨(sched' (k + 2) m).val, by
          have := (sched' (k + 2) m).isLt; omega⟩
        set top : Fin n := ⟨k + 1, by omega⟩
        have hpos_eq : pos = (C * G r (by omega)) (emb hk (ord ⟨r + 1, by omega⟩)) := by
          apply Fin.ext
          simp only [pos, hsched_top, levelFn, m]
        have htop_eq : top = (C * G r (by omega)) (emb hk (ord ⟨r, by omega⟩)) := by
          simp only [Equiv.Perm.mul_apply, hG_top r (by omega)]
          exact (hC_fix top le_rfl).symm
        have hg'_eq : Equiv.swap pos top * acc.2 = G (r + 1) (by omega) := by
          rw [hacc_fin, hpos_eq, htop_eq]
          ext x
          set h := C * G r (by omega)
          have hconj :
              (Equiv.swap (h (emb hk (ord ⟨r + 1, by omega⟩)))
                (h (emb hk (ord ⟨r, by omega⟩))) * h) x =
              (h * Equiv.swap (emb hk (ord ⟨r + 1, by omega⟩))
                (emb hk (ord ⟨r, by omega⟩))) x := by
            simp only [Equiv.Perm.mul_apply]
            by_cases h1 : x = emb hk (ord ⟨r + 1, by omega⟩)
            · rw [h1, Equiv.swap_apply_left, Equiv.swap_apply_left]
            · by_cases h2 : x = emb hk (ord ⟨r, by omega⟩)
              · rw [h2, Equiv.swap_apply_right, Equiv.swap_apply_right]
              · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
                  Equiv.swap_apply_of_ne_of_ne (fun hc => h1 (h.injective hc))
                    (fun hc => h2 (h.injective hc))]
          rw [hconj]
          simp only [h, G, swapChain, pow_succ', mul_assoc]
        have hsub_eq :
            heapRun sched' (k + 1) (by omega) (Equiv.swap pos top * acc.2) =
              ((heapStates sched (k + 1) (by omega)).map (· * G (r + 1) (by omega)),
                C * G (r + 1) (by omega)) := by
          rw [hg'_eq, heapRun_mul_right,
              heapRun_congr_sched sched' sched (k + 1) (by omega) 1 hsched_low]
          rfl
        have hstep_eq : step acc m =
            (acc.1 ++ (heapStates sched (k + 1) (by omega)).map (· * G (r + 1) (by omega)),
              C * G (r + 1) (by omega)) := by
          dsimp only [step]
          exact congrArg (fun p => (acc.1 ++ p.1, p.2)) hsub_eq
        rw [hstep_eq]
        refine ⟨rfl, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨hacc_nodup, hNodup.map (mul_left_injective _), ?_⟩
          intro p hp1 q hq2 hpq
          rw [hpq] at hp1
          rcases hacc_tag q hp1 with ⟨j, hjle, hjlt, htag1⟩
          rcases List.mem_map.mp hq2 with ⟨u, hu, rfl⟩
          have hu_fix : u top = top := hbasic.2.2.2.2 u hu top le_rfl
          have hu_inv : u⁻¹ top = top := by apply u.injective; simp [hu_fix]
          have htag2 : (u * G (r + 1) (by omega))⁻¹ top = emb hk (ord ⟨r + 1, by omega⟩) := by
            rw [mul_inv_rev, Equiv.Perm.mul_apply, hu_inv]
            apply (G (r + 1) (by omega)).injective
            rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
            exact (hG_top (r + 1) (by omega)).symm
          have hEq := htag1.symm.trans htag2
          have hord_eq : ord ⟨j, hjlt⟩ = ord ⟨r + 1, by omega⟩ :=
            Fin.ext (by simpa [emb] using congrArg Fin.val hEq)
          have : j = r + 1 := congrArg Fin.val (ord.injective hord_eq)
          omega
        · intro p hp
          rcases List.mem_append.mp hp with hp1 | hp2
          · rcases hacc_tag p hp1 with ⟨j, hjle, hjlt, htag⟩
            exact ⟨j, by omega, hjlt, htag⟩
          · rcases List.mem_map.mp hp2 with ⟨u, hu, rfl⟩
            have hu_fix : u top = top := hbasic.2.2.2.2 u hu top le_rfl
            have hu_inv : u⁻¹ top = top := by apply u.injective; simp [hu_fix]
            refine ⟨r + 1, le_rfl, by omega, ?_⟩
            rw [mul_inv_rev, Equiv.Perm.mul_apply, hu_inv]
            apply (G (r + 1) (by omega)).injective
            rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
            exact (hG_top (r + 1) (by omega)).symm
  have hfull := hprefix (k + 1) le_rfl
  have htake_full : (List.finRange (k + 1)).take (k + 1) = List.finRange (k + 1) := by
    rw [List.take_of_length_le (by simp)]
  simp only [htake_full] at hfull
  refine ⟨sched', hsched_low, hfull.2.1, ?_⟩
  change ((List.finRange (k + 1)).foldl step (heapRun sched' (k + 1) (by omega) 1)).2 = _
  rw [hfull.1]
  simp only [G, ← mul_assoc, ← pow_succ']
  congr 1
  exact swapChain_eq_cyclePerm hk (by omega) ord

/-! ### 3. Russo's cyclic lower levels `2, ..., k`: net `swap 0 (k - 1)` for every odd `k ≥ 3` -/

/-- The standard `k`-cycle bijection `0 ↦ k-1, 1 ↦ 0, ..., k-1 ↦ k-2` (for even levels). -/
private def evenOrd (k : ℕ) (hk : 2 ≤ k) : Fin k ≃ Fin k where
  toFun i := if hi : i.val = 0 then ⟨k - 1, by omega⟩ else ⟨i.val - 1, by have := i.isLt; omega⟩
  invFun j := if hj : j.val = k - 1 then ⟨0, by omega⟩ else ⟨j.val + 1, by have := j.isLt; omega⟩
  left_inv i := by
    have hi := i.isLt
    apply Fin.ext; dsimp only
    by_cases h0 : i.val = 0
    · simp [h0]
    · have hne : i.val - 1 ≠ k - 1 := by omega
      simp [h0, hne]; omega
  right_inv j := by
    have hj := j.isLt
    apply Fin.ext; dsimp only
    by_cases htop : j.val = k - 1
    · simp [htop]
    · simp [htop]

/-- The descending `k`-cycle bijection `i ↦ k - 1 - i` (for odd levels). -/
private def revOrd (k : ℕ) : Fin k ≃ Fin k where
  toFun i := ⟨k - 1 - i.val, by omega⟩
  invFun i := ⟨k - 1 - i.val, by omega⟩
  left_inv i := Fin.ext (by dsimp; omega)
  right_inv i := Fin.ext (by dsimp; omega)

/-- Product of `cyclePerm (evenOrd k)` and `cyclePerm (revOrd (k + 1))` is `swap 0 k`. -/
private lemma even_mul_rev_eq_swap {n k : ℕ} (hk : k + 1 ≤ n) (hk2 : 2 ≤ k) :
    cyclePerm (by omega : k ≤ n) (by omega) (evenOrd k hk2) *
      cyclePerm hk (by omega) (revOrd (k + 1)) =
    Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨k, by omega⟩ := by
  ext x
  simp only [Equiv.Perm.mul_apply]
  by_cases h0 : x.val = 0
  · have hx : x = emb hk (revOrd (k + 1) ⟨k, by omega⟩) := Fin.ext (by simp [emb, revOrd, h0])
    rw [hx, cyclePerm_apply_ord]
    have hstep : emb hk (revOrd (k + 1) ⟨(k + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩) =
        (⟨k, by omega⟩ : Fin n) := Fin.ext (by simp [emb, revOrd])
    rw [hstep, cyclePerm_apply_ge (k := k) (by omega) (by omega) (evenOrd k hk2) (⟨k, by omega⟩ : Fin n) le_rfl]
    have hx0 : emb hk (revOrd (k + 1) ⟨k, by omega⟩) = (⟨0, by omega⟩ : Fin n) :=
      Fin.ext (by simp [emb, revOrd])
    rw [hx0, Equiv.swap_apply_left]
  · by_cases hlt : x.val < k
    · have hx : x = emb hk (revOrd (k + 1) ⟨k - x.val, by omega⟩) :=
        Fin.ext (by simp [emb, revOrd]; omega)
      rw [hx, cyclePerm_apply_ord]
      have hmod : (k - x.val + 1) % (k + 1) = k - x.val + 1 := Nat.mod_eq_of_lt (by omega)
      have hmid : emb hk (revOrd (k + 1) ⟨(k - x.val + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩) =
          emb (by omega : k ≤ n) (evenOrd k hk2 ⟨x.val, hlt⟩) := by
        apply Fin.ext; simp only [emb, revOrd, evenOrd, Equiv.coe_fn_mk, hmod, h0, ↓reduceDIte]; omega
      rw [hmid, cyclePerm_apply_ord]
      have hres : emb (by omega : k ≤ n) (evenOrd k hk2 ⟨(x.val + 1) % k, Nat.mod_lt _ (by omega)⟩) = x := by
        apply Fin.ext
        by_cases hx1 : x.val + 1 = k
        · have hm : (x.val + 1) % k = 0 := by rw [hx1, Nat.mod_self]
          simp only [emb, evenOrd, Equiv.coe_fn_mk, hm, ↓reduceDIte]; omega
        · have hm : (x.val + 1) % k = x.val + 1 := Nat.mod_eq_of_lt (by omega)
          have hne0 : x.val + 1 ≠ 0 := by omega
          simp only [emb, evenOrd, Equiv.coe_fn_mk, hm, hne0, ↓reduceDIte]; omega
      rw [hres, ← hx]
      have hne1 : x ≠ ⟨0, by omega⟩ := fun h => h0 (congrArg Fin.val h)
      have hne2 : x ≠ ⟨k, by omega⟩ := fun h => by have : x.val = k := congrArg Fin.val h; omega
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    · by_cases hkeq : x.val = k
      · have hx : x = emb hk (revOrd (k + 1) ⟨0, by omega⟩) :=
          Fin.ext (by simp [emb, revOrd, hkeq])
        rw [hx, cyclePerm_apply_ord]
        have hmod : (0 + 1) % (k + 1) = 1 := Nat.mod_eq_of_lt (by omega)
        have hmid : emb hk (revOrd (k + 1) ⟨(0 + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩) =
            emb (by omega : k ≤ n) (evenOrd k hk2 ⟨0, by omega⟩) := by
          apply Fin.ext; simp [emb, revOrd, evenOrd, hmod]
        rw [hmid, cyclePerm_apply_ord]
        have hmod2 : (0 + 1) % k = 1 := Nat.mod_eq_of_lt (by omega)
        have hres : emb (by omega : k ≤ n) (evenOrd k hk2 ⟨(0 + 1) % k, Nat.mod_lt _ (by omega)⟩) =
            ⟨0, by omega⟩ := by
          apply Fin.ext; simp [emb, evenOrd, hmod2]
        rw [hres]
        have hxk : emb hk (revOrd (k + 1) ⟨0, by omega⟩) = (⟨k, by omega⟩ : Fin n) :=
          Fin.ext (by simp [emb, revOrd])
        rw [hxk, Equiv.swap_apply_right]
      · rw [cyclePerm_apply_ge hk (by omega) _ x (by omega),
            cyclePerm_apply_ge (by omega) (by omega) _ x (by omega)]
        have hne1 : x ≠ ⟨0, by omega⟩ := fun h => h0 (congrArg Fin.val h)
        have hne2 : x ≠ ⟨k, by omega⟩ := fun h => hkeq (congrArg Fin.val h)
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]

/-- Inductive construction of valid cyclic lower levels up to any `k` (`2 ≤ k ≤ n`):
- Even `k`: net is `cyclePerm (evenOrd k)`.
- Odd `k ≥ 3`: net is `swap 0 (k - 1)`. -/
private theorem exists_cyclic_lower {n : ℕ} :
    ∀ (k : ℕ) (hk2 : 2 ≤ k) (hk : k ≤ n),
      ∃ sched : HeapSchedule,
        (heapStates (n := n) sched k hk).Nodup ∧
        heapNet (n := n) sched k hk =
          if Even k then
            cyclePerm hk (by omega) (evenOrd k hk2)
          else
            Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨k - 1, by omega⟩
  | 0, hk2, _ => by omega
  | 1, hk2, _ => by omega
  | 2, hk2, hk => by
      let base : HeapSchedule := fun _ m => m
      have h1 : (heapStates (n := n) base 1 (by omega)).Nodup := by
        simp [heapStates, heapRun]
      have hord0 : evenOrd 2 (by omega) 0 = ⟨1, by omega⟩ := by
        apply Fin.ext; simp [evenOrd]
      rcases heap_extend_level hk base h1 (evenOrd 2 (by omega)) hord0 with
        ⟨sched', _, hnodup, hnet⟩
      refine ⟨sched', hnodup, ?_⟩
      have heven : Even 2 := ⟨1, rfl⟩
      simp only [heven, ↓reduceIte]
      have hnet1 : heapNet (n := n) base 1 (by omega) = 1 := rfl
      rw [hnet, hnet1, one_pow, one_mul]
  | k + 3, _, hk => by
      rcases exists_cyclic_lower (n := n) (k + 2) (by omega) (by omega) with ⟨sched, hnodup, hnet⟩
      by_cases hev : Even (k + 3)
      · have hodd_prev : ¬ Even (k + 2) := by
          rcases hev with ⟨m, hm⟩
          rintro ⟨r, hr⟩; omega
        simp only [hodd_prev, ↓reduceIte] at hnet
        have hord0 : evenOrd (k + 3) (by omega) 0 = ⟨k + 2, by omega⟩ := by
          apply Fin.ext; simp [evenOrd]
        rcases heap_extend_level hk sched hnodup (evenOrd (k + 3) (by omega)) hord0 with
          ⟨sched', _, hnodup', hnet'⟩
        refine ⟨sched', hnodup', ?_⟩
        simp only [hev, ↓reduceIte]
        rw [hnet', hnet]
        rcases hev with ⟨m, hm⟩
        have hpow : (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨k + 2 - 1, by omega⟩) ^ (k + 3) = 1 := by
          rw [hm, ← two_mul, pow_mul, sq, Equiv.swap_mul_self, one_pow]
        rw [hpow, one_mul]
      · have hev_prev : Even (k + 2) := by
          rcases Nat.even_or_odd (k + 2) with h | ⟨r, hr⟩
          · exact h
          · exfalso; apply hev; exact ⟨r + 1, by omega⟩
        simp only [hev_prev, ↓reduceIte] at hnet
        have hord0 : revOrd (k + 3) 0 = ⟨k + 2, by omega⟩ := by
          apply Fin.ext; simp [revOrd]
        rcases heap_extend_level hk sched hnodup (revOrd (k + 3)) hord0 with
          ⟨sched', _, hnodup', hnet'⟩
        refine ⟨sched', hnodup', ?_⟩
        simp only [hev, ↓reduceIte]
        rw [hnet', hnet]
        have hpow : cyclePerm (by omega : k + 2 ≤ n) (by omega) (evenOrd (k + 2) (by omega)) ^ (k + 3) =
            cyclePerm (by omega : k + 2 ≤ n) (by omega) (evenOrd (k + 2) (by omega)) := by
          rw [pow_succ, cyclePerm_pow_self, one_mul]
        rw [hpow]
        exact even_mul_rev_eq_swap hk (by omega)

/-! ### 4. Extremal odd permutation `a*_n` and target state `T = (a*_n)⁻¹` -/

/-- The lexicographically largest odd permutation `a*_n` on `Fin n` (for `n ≥ 2`):
- when `n % 4 = 3` (or `2`), the full reversal `i ↦ n - 1 - i`;
- when `n % 4 = 1` (or `0`), `rev_n * swap (n-2) (n-1)` (swaps the last two entries `0` and `1`). -/
def targetArray (n : ℕ) (hn : 2 ≤ n) : Perm (Fin n) :=
  if n % 4 = 2 ∨ n % 4 = 3 then
    revOrd n
  else
    revOrd n * Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩

/-- Target state `T = (a*_n)⁻¹`. -/
def targetState (n : ℕ) (hn : 2 ≤ n) : Perm (Fin n) :=
  (targetArray n hn)⁻¹

private def revPrefix (n : ℕ) : (m : ℕ) → m ≤ n / 2 → Perm (Fin n)
  | 0, _ => 1
  | m + 1, hm =>
      revPrefix n m (by omega) * Equiv.swap ⟨m, by omega⟩ ⟨n - 1 - m, by omega⟩

private lemma sign_revPrefix (n : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ n / 2), Equiv.Perm.sign (revPrefix n m hm) = (-1 : ℤˣ) ^ m
  | 0, _ => by simp [revPrefix]
  | m + 1, hm => by
      simp only [revPrefix, map_mul]
      have hne : (⟨m, by omega⟩ : Fin n) ≠ ⟨n - 1 - m, by omega⟩ := by
        intro h; have : m = n - 1 - m := congrArg Fin.val h; omega
      rw [sign_revPrefix n m (by omega), Equiv.Perm.sign_swap hne, pow_succ]

private lemma revPrefix_apply (n : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ n / 2) (x : Fin n),
      (revPrefix n m hm x).val =
        if x.val < m ∨ n - m ≤ x.val then n - 1 - x.val else x.val
  | 0, _, x => by simp [revPrefix]
  | m + 1, hm, x => by
      have hxlt := x.isLt
      simp only [revPrefix, Equiv.Perm.mul_apply]
      by_cases hxm : x.val = m
      · have hxe : x = ⟨m, by omega⟩ := Fin.ext hxm
        rw [hxe, Equiv.swap_apply_left, revPrefix_apply n m (by omega)]
        dsimp only
        split_ifs <;> omega
      · by_cases hxtop : x.val = n - 1 - m
        · have hxe : x = ⟨n - 1 - m, by omega⟩ := Fin.ext hxtop
          rw [hxe, Equiv.swap_apply_right, revPrefix_apply n m (by omega)]
          dsimp only
          split_ifs <;> omega
        · have hne1 : x ≠ ⟨m, by omega⟩ := fun h => hxm (congrArg Fin.val h)
          have hne2 : x ≠ ⟨n - 1 - m, by omega⟩ := fun h => hxtop (congrArg Fin.val h)
          rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, revPrefix_apply n m (by omega)]
          split_ifs <;> omega

private lemma sign_revOrd (n : ℕ) :
    Equiv.Perm.sign (revOrd n) = (-1 : ℤˣ) ^ (n / 2) := by
  have heq : revOrd n = revPrefix n (n / 2) le_rfl := by
    ext x
    have hxlt := x.isLt
    rw [revPrefix_apply n (n / 2) le_rfl x]
    simp only [revOrd, Equiv.coe_fn_mk]
    split_ifs <;> omega
  rw [heq, sign_revPrefix]

/-- `targetArray n hn` is always an odd permutation (`sign = -1`). -/
theorem sign_targetArray (n : ℕ) (hn : 2 ≤ n) :
    Equiv.Perm.sign (targetArray n hn) = -1 := by
  unfold targetArray
  split_ifs with h
  · rw [sign_revOrd]
    have hodd : Odd (n / 2) := by
      rcases h with h2 | h3 <;> exact ⟨n / 4, by omega⟩
    exact hodd.neg_one_pow
  · rw [map_mul, sign_revOrd, Equiv.Perm.sign_swap (by
      intro heq; have := congrArg Fin.val heq; simp at this; omega)]
    have hev : Even (n / 2) := ⟨n / 4, by omega⟩
    rw [hev.neg_one_pow, one_mul]

/-- Helper: strict lexicographic comparison on `List.ofFn` from first differing index. -/
private lemma ofFn_lt_of_first_diff {n : ℕ} :
    ∀ (m : ℕ) (f g : Fin m → Fin n) (i : Fin m),
      (∀ j : Fin m, j < i → f j = g j) → f i < g i →
      List.ofFn f < List.ofFn g
  | 0, _, _, i, _, _ => Fin.elim0 i
  | m + 1, f, g, i, hpr, hfi => by
      rw [List.ofFn_succ, List.ofFn_succ]
      cases i using Fin.cases with
      | zero => exact List.Lex.rel hfi
      | succ i' =>
          have h0 : f 0 = g 0 := hpr 0 (Fin.succ_pos i')
          rw [h0]
          exact List.Lex.cons (ofFn_lt_of_first_diff m (fun j => f j.succ) (fun j => g j.succ) i'
            (fun j hj => hpr j.succ (Fin.succ_lt_succ_iff.mpr hj)) hfi)

/-- Every odd permutation `p : Perm (Fin n)` is lexicographically `≤ targetArray n hn`. -/
theorem targetArray_lex_max (n : ℕ) (hn : 2 ≤ n) (p : Perm (Fin n))
    (hodd : Equiv.Perm.sign p = -1) :
    List.ofFn p ≤ List.ofFn (targetArray n hn) := by
  have hle_rev : ∀ q : Perm (Fin n), List.ofFn q ≤ List.ofFn (revOrd n) := by
    intro q
    by_contra hlt
    rw [not_le] at hlt
    have hex : ∃ i : Fin n, (∀ j : Fin n, j < i → q j = revOrd n j) ∧ revOrd n i < q i := by
      have hne : List.ofFn q ≠ List.ofFn (revOrd n) := ne_of_gt hlt
      have hex_ne : ∃ i : Fin n, q i ≠ revOrd n i := by
        by_contra hall
        push Not at hall
        exact hne (by congr 1; funext i; exact hall i)
      classical
      let S : Finset (Fin n) := Finset.univ.filter (fun i => q i ≠ revOrd n i)
      have hSne : S.Nonempty := by
        rcases hex_ne with ⟨i, hi⟩
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      let i := S.min' hSne
      have hi_mem : i ∈ S := Finset.min'_mem S hSne
      have hi_ne : q i ≠ revOrd n i := (Finset.mem_filter.mp hi_mem).2
      have hprev : ∀ j : Fin n, j < i → q j = revOrd n j := by
        intro j hj
        by_contra hne_j
        have hj_mem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne_j⟩
        have hle := Finset.min'_le S j hj_mem
        exact not_lt_of_ge hle hj
      refine ⟨i, hprev, ?_⟩
      by_contra hnotlt
      have hqlt : q i < revOrd n i := lt_of_le_of_ne (not_lt.mp hnotlt) hi_ne
      exact lt_asymm hlt (ofFn_lt_of_first_diff n q (revOrd n) i hprev hqlt)
    rcases hex with ⟨i, hprev, hgt⟩
    have hi_lt := i.isLt
    have hqi_lt := (q i).isLt
    have hgtv : n - 1 - i.val < (q i).val := hgt
    have hj_lt : n - 1 - (q i).val < i.val := by omega
    let j : Fin n := ⟨n - 1 - (q i).val, by omega⟩
    have hqj : q j = revOrd n j := hprev j hj_lt
    have hqj_eq : q j = q i := by
      rw [hqj]; apply Fin.ext; simp [revOrd, j]; omega
    have : j = i := q.injective hqj_eq
    have hjv : j.val = n - 1 - (q i).val := rfl
    have : j.val = i.val := congrArg Fin.val this
    omega
  unfold targetArray
  split_ifs with h
  · exact hle_rev p
  · have hrev_even : Equiv.Perm.sign (revOrd n) = 1 := by
      rw [sign_revOrd]
      have hev : Even (n / 2) := ⟨n / 4, by omega⟩
      exact hev.neg_one_pow
    have hp_ne_rev : p ≠ revOrd n := by
      intro heq; rw [heq, hrev_even] at hodd; exact absurd hodd (by decide)
    by_contra hlt
    rw [not_le] at hlt
    have hple : List.ofFn p ≤ List.ofFn (revOrd n) := hle_rev p
    have htarget_eq : ∀ j : Fin n, j.val < n - 2 →
        (revOrd n * Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) j = revOrd n j := by
      intro j hj
      simp only [Equiv.Perm.mul_apply]
      have hne1 : j ≠ ⟨n - 2, by omega⟩ := fun hc => by have : j.val = n - 2 := congrArg Fin.val hc; omega
      have hne2 : j ≠ ⟨n - 1, by omega⟩ := fun hc => by have : j.val = n - 1 := congrArg Fin.val hc; omega
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    have hp_prefix : ∀ j : Fin n, j.val < n - 2 → p j = revOrd n j := by
      intro j hj
      induction hjv : j.val using Nat.strongRecOn generalizing j with
      | ind m ih =>
        have hprev : ∀ u : Fin n, u.val < m → p u = revOrd n u := by
          intro u hu
          exact ih u.val hu u (by omega) rfl
        have hlt_imp : ∀ (a b : Fin n → Fin n), List.ofFn a ≤ List.ofFn b →
            (∀ u : Fin n, u < j → a u = b u) → a j ≤ b j := by
          intro a b hab hpr
          by_contra hba
          exact not_lt_of_ge hab (ofFn_lt_of_first_diff n b a j
            (fun u hu => (hpr u hu).symm) (not_le.mp hba))
        have h1 : p j ≤ revOrd n j := hlt_imp p (revOrd n) hple (fun u hu => hprev u (by
          have : u.val < j.val := hu; omega))
        have h2 : revOrd n j ≤ p j := by
          rw [← htarget_eq j hj]
          exact hlt_imp _ p (le_of_lt hlt) (fun u hu => by
            have hu_lt : u.val < m := by have : u.val < j.val := hu; omega
            rw [htarget_eq u (by omega), hprev u hu_lt])
        exact le_antisymm h1 h2
    have hp_small : ∀ j : Fin n, n - 2 ≤ j.val → (p j).val < 2 := by
      intro j hj
      have hpj_lt := (p j).isLt
      by_contra hge
      let u : Fin n := ⟨n - 1 - (p j).val, by omega⟩
      have hu_lt : u.val < n - 2 := by simp [u]; omega
      have hpu : p u = revOrd n u := hp_prefix u hu_lt
      have hpu_eq : p u = p j := by rw [hpu]; apply Fin.ext; simp [revOrd, u]; omega
      have : u = j := p.injective hpu_eq
      have : u.val = j.val := congrArg Fin.val this
      omega
    have hval1 : (p ⟨n - 2, by omega⟩).val < 2 := hp_small ⟨n - 2, by omega⟩ le_rfl
    have hval2 : (p ⟨n - 1, by omega⟩).val < 2 := hp_small ⟨n - 1, by omega⟩ (by dsimp; omega)
    have hne12 : p ⟨n - 2, by omega⟩ ≠ p ⟨n - 1, by omega⟩ := fun hc => by
      have := congrArg Fin.val (p.injective hc); simp at this; omega
    have hne12v : (p ⟨n - 2, by omega⟩).val ≠ (p ⟨n - 1, by omega⟩).val := fun hc =>
      hne12 (Fin.ext hc)
    have hp_eq_t_case : (p ⟨n - 2, by omega⟩).val = 0 → False := by
      intro hp0
      have hp1 : (p ⟨n - 1, by omega⟩).val = 1 := by omega
      have hp_eq_t : p = revOrd n * Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ := by
        ext x
        have hxlt := x.isLt
        by_cases hx : x.val < n - 2
        · rw [hp_prefix x hx, htarget_eq x hx]
        · by_cases hx2 : x.val = n - 2
          · have hxe : x = ⟨n - 2, by omega⟩ := Fin.ext hx2
            rw [hxe]; simp [revOrd, hp0]
          · have hxe : x = ⟨n - 1, by omega⟩ := Fin.ext (show x.val = n - 1 by omega)
            rw [hxe]; simp [revOrd, hp1]; omega
      rw [hp_eq_t] at hlt
      exact lt_irrefl _ hlt
    by_cases hp0 : (p ⟨n - 2, by omega⟩).val = 0
    · exact hp_eq_t_case hp0
    · have hp0' : (p ⟨n - 2, by omega⟩).val = 1 := by omega
      have hp1' : (p ⟨n - 1, by omega⟩).val = 0 := by omega
      have hp_eq_rev : p = revOrd n := by
        ext x
        have hxlt := x.isLt
        by_cases hx : x.val < n - 2
        · exact congrArg Fin.val (hp_prefix x hx)
        · by_cases hx2 : x.val = n - 2
          · have hxe : x = ⟨n - 2, by omega⟩ := Fin.ext hx2
            rw [hxe]; simp [revOrd, hp0']; omega
          · have hxe : x = ⟨n - 1, by omega⟩ := Fin.ext (show x.val = n - 1 by omega)
            rw [hxe]; simp [revOrd, hp1']
      exact hp_ne_rev hp_eq_rev

/-! ### 5. The odd-`n` zigzag level `n - 1` and three-phase top level `n` (`n ≥ 5` odd) -/

/-- Level `n - 1` zigzag parking order (0-based, `n ≥ 5` odd, `h = (n - 3) / 2`):
`0 ↦ n-2`, `2t+1 ↦ t`, `2t+2 ↦ n-3-t` for `0 ≤ t < h`, and `n-2 ↦ h`. -/
private def penultOrdFun (n : ℕ) (hn : 5 ≤ n) (i : Fin (n - 1)) : Fin (n - 1) :=
  let h := (n - 3) / 2
  if i.val = 0 then ⟨n - 2, by omega⟩
  else if i.val = n - 2 then ⟨h, by omega⟩
  else if i.val % 2 = 1 then ⟨(i.val - 1) / 2, by omega⟩
  else ⟨n - 2 - i.val / 2, by omega⟩

private lemma penultOrdFun_inj (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) :
    Function.Injective (penultOrdFun n hn) := by
  intro i j hij
  have hval : (penultOrdFun n hn i).val = (penultOrdFun n hn j).val :=
    congrArg Fin.val hij
  obtain ⟨q, hq⟩ := hodd
  have hi := i.isLt
  have hj := j.isLt
  dsimp only [penultOrdFun] at hval
  apply Fin.ext
  split_ifs at hval <;> simp only [] at hval <;> omega

/-- Level `n - 1` zigzag parking bijection on `Fin (n - 1)`. -/
private noncomputable def penultOrd (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) :
    Fin (n - 1) ≃ Fin (n - 1) :=
  Equiv.ofBijective (penultOrdFun n hn)
    (Finite.injective_iff_bijective.mp (penultOrdFun_inj n hn hodd))

private lemma penultOrd_zero (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) :
    penultOrd n hn hodd ⟨0, by omega⟩ = ⟨n - 2, by omega⟩ := by
  apply Fin.ext; simp [penultOrd, penultOrdFun]

/-- The penultimate net `Z' = cyclePerm (penultOrd n)`. -/
private noncomputable def Zp (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) : Perm (Fin n) :=
  cyclePerm (by omega : n - 1 ≤ n) (by omega) (penultOrd n hn hodd)

/-- Closed form of `Z'` on `Fin n`. -/
private lemma Zp_apply (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) (x : Fin n) :
    let h := (n - 3) / 2
    (Zp n hn hodd x).val =
      if x.val < h then n - 3 - x.val
      else if x.val = h then n - 2
      else if x.val < n - 1 then n - 2 - x.val
      else n - 1 := by
  have ⟨q, hq⟩ := hodd
  have hx := x.isLt
  dsimp only
  split_ifs with h1 h2 h3
  · have hx_eq : x = emb (by omega : n - 1 ≤ n)
        (penultOrd n hn hodd ⟨2 * x.val + 1, by omega⟩) := by
      apply Fin.ext; simp only [emb, penultOrd, Equiv.ofBijective_apply, penultOrdFun]
      split_ifs <;> first | contradiction | rfl | (try dsimp only; omega)
    conv_lhs => rw [hx_eq]
    unfold Zp; rw [cyclePerm_apply_ord]
    have hmod : (2 * x.val + 1 + 1) % (n - 1) = 2 * x.val + 2 := Nat.mod_eq_of_lt (by omega)
    simp only [emb, penultOrd, Equiv.ofBijective_apply, penultOrdFun, hmod]
    split_ifs <;> first | contradiction | rfl | (try dsimp only; omega)
  · have hx_eq : x = emb (by omega : n - 1 ≤ n)
        (penultOrd n hn hodd ⟨n - 2, by omega⟩) := by
      apply Fin.ext; simp only [emb, penultOrd, Equiv.ofBijective_apply, penultOrdFun]
      split_ifs <;> first | contradiction | rfl | (try dsimp only; omega)
    conv_lhs => rw [hx_eq]
    unfold Zp; rw [cyclePerm_apply_ord]
    have hmod : (n - 2 + 1) % (n - 1) = 0 := by
      have : n - 2 + 1 = n - 1 := by omega
      rw [this, Nat.mod_self]
    simp only [emb, penultOrd, Equiv.ofBijective_apply, penultOrdFun, hmod]
    split_ifs <;> first | contradiction | rfl
  · by_cases htop : x.val = n - 2
    · have hx_eq : x = emb (by omega : n - 1 ≤ n)
          (penultOrd n hn hodd ⟨0, by omega⟩) := by
        apply Fin.ext; simp only [emb, penultOrd, Equiv.ofBijective_apply, penultOrdFun, htop]
        split_ifs <;> first | contradiction | rfl
      conv_lhs => rw [hx_eq]
      unfold Zp; rw [cyclePerm_apply_ord]
      have hmod : (0 + 1) % (n - 1) = 1 := Nat.mod_eq_of_lt (by omega)
      simp only [emb, penultOrd, Equiv.ofBijective_apply, penultOrdFun, hmod]
      split_ifs <;> first | contradiction | rfl | (try dsimp only; omega)
    · have hx_eq : x = emb (by omega : n - 1 ≤ n)
          (penultOrd n hn hodd ⟨2 * (n - 2 - x.val), by omega⟩) := by
        apply Fin.ext; simp only [emb, penultOrd, Equiv.ofBijective_apply, penultOrdFun]
        split_ifs <;> first | contradiction | rfl | (try dsimp only; omega)
      conv_lhs => rw [hx_eq]
      unfold Zp; rw [cyclePerm_apply_ord]
      have hmod : (2 * (n - 2 - x.val) + 1) % (n - 1) = 2 * (n - 2 - x.val) + 1 :=
        Nat.mod_eq_of_lt (by omega)
      simp only [emb, penultOrd, Equiv.ofBijective_apply, penultOrdFun, hmod]
      split_ifs <;> first | contradiction | rfl | (try dsimp only; omega)
  · have hx_eq : x.val = n - 1 := by omega
    unfold Zp
    rw [cyclePerm_apply_ge (by omega) (by omega) _ x (by omega), hx_eq]

/-- Closed form of `Z = Zp⁻¹ * targetState` on `Fin n`. -/
private lemma Z_apply (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) (v : Fin n) :
    let h := (n - 3) / 2
    let Z := (Zp n hn hodd)⁻¹ * targetState n (by omega)
    (Z v).val =
      if v.val = 0 then (if n % 4 = 3 then n - 1 else h)
      else if v.val = 1 then (if n % 4 = 3 then h else n - 1)
      else if v.val ≤ h + 1 then v.val - 2
      else v.val - 1 := by
  have ⟨q, hq⟩ := hodd
  have hv := v.isLt
  let expVal : ℕ :=
    if v.val = 0 then (if n % 4 = 3 then n - 1 else (n - 3) / 2)
    else if v.val = 1 then (if n % 4 = 3 then (n - 3) / 2 else n - 1)
    else if v.val ≤ (n - 3) / 2 + 1 then v.val - 2
    else v.val - 1
  have hexp_lt : expVal < n := by dsimp [expVal]; split_ifs <;> omega
  let expFin : Fin n := ⟨expVal, hexp_lt⟩
  have hrev_inv : (revOrd n)⁻¹ = revOrd n := by
    ext u; simp [revOrd]
  have hT : (targetState n (by omega) v).val =
      if v.val = 0 then (if n % 4 = 3 then n - 1 else n - 2)
      else if v.val = 1 then (if n % 4 = 3 then n - 2 else n - 1)
      else n - 1 - v.val := by
    unfold targetState targetArray
    by_cases h3 : n % 4 = 3
    · have hcond : n % 4 = 2 ∨ n % 4 = 3 := Or.inr h3
      have hts : (if n % 4 = 2 ∨ n % 4 = 3 then revOrd n
          else revOrd n * Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩)⁻¹ = revOrd n := by
        rw [if_pos hcond, hrev_inv]
      rw [hts]
      simp only [revOrd, Equiv.coe_fn_mk, h3, ↓reduceIte]
      split_ifs <;> omega
    · have hcond : ¬ (n % 4 = 2 ∨ n % 4 = 3) := by omega
      have hts : (if n % 4 = 2 ∨ n % 4 = 3 then revOrd n
          else revOrd n * Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩)⁻¹ =
          Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ * revOrd n := by
        rw [if_neg hcond, mul_inv_rev, Equiv.swap_inv, hrev_inv]
      rw [hts, Equiv.Perm.mul_apply]
      by_cases hv0 : v.val = 0
      · have hrv : revOrd n v = ⟨n - 1, by omega⟩ := Fin.ext (by simp [revOrd, hv0])
        rw [hrv, Equiv.swap_apply_right]; simp [hv0, h3]
      · by_cases hv1 : v.val = 1
        · have hrv : revOrd n v = ⟨n - 2, by omega⟩ := Fin.ext (by simp [revOrd, hv1]; omega)
          rw [hrv, Equiv.swap_apply_left]; simp [hv1, h3]
        · have hne1 : revOrd n v ≠ ⟨n - 2, by omega⟩ := by
            intro hc; have := congrArg Fin.val hc; simp [revOrd] at this; omega
          have hne2 : revOrd n v ≠ ⟨n - 1, by omega⟩ := by
            intro hc; have := congrArg Fin.val hc; simp [revOrd] at this; omega
          rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
          simp [revOrd, hv0, hv1]
  have hkey : Zp n hn hodd expFin = targetState n (by omega) v := by
    apply Fin.ext
    rw [Zp_apply n hn hodd expFin, hT]
    dsimp only [expFin, expVal]
    split_ifs <;> omega
  have hres : ((Zp n hn hodd)⁻¹ * targetState n (by omega)) v = expFin := by
    simp only [Equiv.Perm.mul_apply]
    rw [← hkey, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  exact congrArg Fin.val hres

/-- Unified 3-phase top-level parking order on `Fin n` (for odd `n ≥ 5`):
- Phase 1 (`0 ≤ j ≤ h + 1`): `n - 1 - j` (descends by 1 from `n - 1` to `h + 1`),
- Phase 2 (`h + 1 < j ≤ h + 1 + (h + 1) / 2`): `(h + 1) - 2 * (j - (h + 1))` (descends by 2 to `r`),
- Phase 3 (`h + 2 + (h + 1) / 2 ≤ j < n`): `h - 2 * (j - (h + 2 + (h + 1) / 2))` (descends by 2 to `1 - r`). -/
private def topOrdFun (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) (j : Fin n) : Fin n :=
  let h := (n - 3) / 2
  let j1 := h + 1 + (h + 1) / 2
  if j.val ≤ h + 1 then ⟨n - 1 - j.val, by omega⟩
  else if j.val ≤ j1 then ⟨(h + 1) - 2 * (j.val - (h + 1)), by omega⟩
  else ⟨h - 2 * (j.val - (j1 + 1)), by
    obtain ⟨q, hq⟩ := hodd; have := j.isLt; omega⟩

private lemma topOrdFun_inj (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) :
    Function.Injective (topOrdFun n hn hodd) := by
  intro i j hij
  have hval : (topOrdFun n hn hodd i).val = (topOrdFun n hn hodd j).val :=
    congrArg Fin.val hij
  obtain ⟨q, hq⟩ := hodd
  have hi := i.isLt
  have hj := j.isLt
  dsimp only [topOrdFun] at hval
  apply Fin.ext
  split_ifs at hval <;> simp only [] at hval <;> omega

/-- Top-level parking bijection on `Fin n`. -/
private noncomputable def topOrd (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (topOrdFun n hn hodd)
    (Finite.injective_iff_bijective.mp (topOrdFun_inj n hn hodd))

private lemma topOrd_zero (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) :
    topOrd n hn hodd ⟨0, by omega⟩ = ⟨n - 1, by omega⟩ := by
  apply Fin.ext; simp [topOrd, topOrdFun]

/-- **Core Cycle Theorem:** `Z = Z'⁻¹ * T` equals the `n`-cycle `cyclePerm (topOrd n)`. -/
private lemma Z_eq_cyclePerm_topOrd (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) :
    (Zp n hn hodd)⁻¹ * targetState n (by omega) =
      cyclePerm le_rfl (by omega) (topOrd n hn hodd) := by
  have hstep : ∀ j : Fin n,
      ((Zp n hn hodd)⁻¹ * targetState n (by omega)) (topOrd n hn hodd j) =
        topOrd n hn hodd ⟨(j.val + 1) % n, Nat.mod_lt _ (by omega)⟩ := by
    intro j
    apply Fin.ext
    rw [Z_apply n hn hodd (topOrd n hn hodd j)]
    obtain ⟨q, hq⟩ := hodd
    have hj := j.isLt
    simp only [topOrd, Equiv.ofBijective_apply]
    by_cases hlast : j.val + 1 = n
    · have hmod : (j.val + 1) % n = 0 := by rw [hlast, Nat.mod_self]
      dsimp only [topOrdFun]
      simp only [hmod]
      split_ifs <;> simp only [] at * <;> omega
    · have hmod : (j.val + 1) % n = j.val + 1 := Nat.mod_eq_of_lt (by omega)
      dsimp only [topOrdFun]
      simp only [hmod]
      split_ifs <;> simp only [] at * <;> omega
  ext x
  set j := (topOrd n hn hodd).symm x
  have hx : x = emb le_rfl (topOrd n hn hodd j) := by
    apply Fin.ext; simp [emb, j]
  rw [hx, cyclePerm_apply_ord]
  exact congrArg Fin.val (hstep j)

/-! ### 6. Main Theorem: Resolution of Russo's Open Question (arXiv:2611.22780v1, §10 item 2) -/

/-- **Main Theorem (Positive resolution of Russo arXiv:2611.22780v1, §10 item 2):**
For every odd `n ≥ 3`, there exists a Heap-type swap schedule whose recursive array
enumeration `heapArrays sched`:
1. starts at the identity arrangement `1`,
2. has length `n!` with no repeated arrangements (hence visits every permutation of `Fin n` once),
3. advances by a single swap of two positions at every step, and
4. ends at `targetArray n`, the lexicographically largest odd permutation in `S_n`. -/
theorem russo_odd_extremal_heap (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    ∃ sched : HeapSchedule,
      (heapArrays (n := n) sched).head? = some 1 ∧
      (heapArrays (n := n) sched).getLast? = some (targetArray n (by omega)) ∧
      (heapArrays (n := n) sched).length = Nat.factorial n ∧
      (heapArrays (n := n) sched).Nodup ∧
      (heapArrays (n := n) sched).IsChain AdjArray := by
  by_cases hn3 : n = 3
  · subst hn3
    rcases exists_cyclic_lower (n := 3) 3 (by omega) le_rfl with ⟨sched, hnodup, hnet⟩
    have hbasic := heapRun_basic sched 3 le_rfl (by omega)
    have hnot_even : ¬ Even 3 := by rintro ⟨r, hr⟩; omega
    simp only [hnot_even, ↓reduceIte] at hnet
    have hnet_eq : (heapNet sched 3 le_rfl)⁻¹ = targetArray 3 (by omega) := by
      rw [hnet, Equiv.swap_inv]
      ext x; fin_cases x <;> simp [Equiv.swap_apply_def, targetArray, revOrd]
    refine ⟨sched, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [heapArrays, List.head?_map, hbasic.1]; simp
    · simp only [heapArrays, List.getLast?_map, hbasic.2.1]; simp [hnet_eq]
    · simp only [heapArrays, List.length_map, hbasic.2.2.1]
    · exact hnodup.map inv_injective
    · exact (List.isChain_map (·⁻¹)).mpr (hbasic.2.2.2.1.imp fun _ _ h => adjArray_of_adjState h)
  · have hn5 : 5 ≤ n := by obtain ⟨q, hq⟩ := hodd; omega
    have hodd_nm2 : ¬ Even (n - 2) := by
      obtain ⟨q, hq⟩ := hodd; rintro ⟨r, hr⟩; omega
    rcases exists_cyclic_lower (n := n) (n - 2) (by omega) (by omega) with
      ⟨sched0, hnodup0, hnet0⟩
    simp only [hodd_nm2, ↓reduceIte] at hnet0
    have hk1 : (n - 3) + 2 ≤ n := by omega
    have hnm2_eq : (n - 3) + 1 = n - 2 := by omega
    have hnm1_eq : (n - 3) + 2 = n - 1 := by omega
    have hnodup0' : (heapStates (n := n) sched0 ((n - 3) + 1) (by omega)).Nodup := by
      simpa [hnm2_eq] using hnodup0
    let penOrd' : Fin ((n - 3) + 2) ≃ Fin ((n - 3) + 2) :=
      (finCongr hnm1_eq).trans ((penultOrd n hn5 hodd).trans (finCongr hnm1_eq.symm))
    have hpenOrd0 : penOrd' 0 = ⟨(n - 3) + 1, by omega⟩ := by
      apply Fin.ext
      have h0 : finCongr hnm1_eq (0 : Fin ((n - 3) + 2)) = ⟨0, by omega⟩ := rfl
      simp [penOrd', h0, penultOrd_zero]; omega
    rcases heap_extend_level hk1 sched0 hnodup0' penOrd' hpenOrd0 with
      ⟨sched1, _, hnodup1, hnet1⟩
    have hnet1_eq : heapNet (n := n) sched1 (n - 1) (by omega) = Zp n hn5 hodd := by
      have h1 : heapNet (n := n) sched1 (n - 1) (by omega) =
          heapNet (n := n) sched1 ((n - 3) + 2) hk1 := by
        congr 1; omega
      rw [h1, hnet1]
      have hnet0' : heapNet (n := n) sched0 ((n - 3) + 1) (by omega) =
          Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨n - 2 - 1, by omega⟩ := by
        simpa [hnm2_eq] using hnet0
      rw [hnet0']
      have heven_nm1 : Even ((n - 3) + 2) := by
        obtain ⟨q, hq⟩ := hodd; exact ⟨q, by omega⟩
      rcases heven_nm1 with ⟨r, hr⟩
      have hpow1 : (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨n - 2 - 1, by omega⟩) ^ ((n - 3) + 2) = 1 := by
        rw [hr, ← two_mul, pow_mul, sq, Equiv.swap_mul_self, one_pow]
      rw [hpow1, one_mul]
      ext x
      by_cases hx : x.val < n - 1
      · set i := (penultOrd n hn5 hodd).symm ⟨x.val, hx⟩
        have hx1 : x = emb (by omega : n - 1 ≤ n) (penultOrd n hn5 hodd i) :=
          Fin.ext (by simp [emb, i])
        have hx2 : x = emb hk1 (penOrd' (finCongr hnm1_eq.symm i)) :=
          Fin.ext (by simp [emb, penOrd', i])
        rw [hx2, cyclePerm_apply_ord]
        rw [← hx2, hx1]; unfold Zp; rw [cyclePerm_apply_ord]
        simp only [emb, penOrd', Equiv.trans_apply, finCongr_apply, Fin.val_cast]
        congr 2; apply Fin.ext; simp [hnm1_eq]
      · rw [cyclePerm_apply_ge hk1 (by omega) _ x (by omega)]
        unfold Zp
        rw [cyclePerm_apply_ge (by omega) (by omega) _ x (by omega)]
    have hk2 : (n - 2) + 2 ≤ n := by omega
    have hnm1_eq2 : (n - 2) + 1 = n - 1 := by omega
    have hn_eq2 : (n - 2) + 2 = n := by omega
    have hnodup1' : (heapStates (n := n) sched1 ((n - 2) + 1) (by omega)).Nodup := by
      simpa [hnm1_eq, hnm1_eq2] using hnodup1
    let topOrd' : Fin ((n - 2) + 2) ≃ Fin ((n - 2) + 2) :=
      (finCongr hn_eq2).trans ((topOrd n hn5 hodd).trans (finCongr hn_eq2.symm))
    have htopOrd0 : topOrd' 0 = ⟨(n - 2) + 1, by omega⟩ := by
      apply Fin.ext
      have h0 : finCongr hn_eq2 (0 : Fin ((n - 2) + 2)) = ⟨0, by omega⟩ := rfl
      simp [topOrd', h0, topOrd_zero]; omega
    rcases heap_extend_level hk2 sched1 hnodup1' topOrd' htopOrd0 with
      ⟨sched2, _, hnodup2, hnet2⟩
    have hnodup_n : (heapStates (n := n) sched2 n le_rfl).Nodup := by
      simpa [hn_eq2] using hnodup2
    have hnet_n : heapNet (n := n) sched2 n le_rfl = targetState n (by omega) := by
      have h2 : heapNet (n := n) sched2 n le_rfl = heapNet (n := n) sched2 ((n - 2) + 2) hk2 := by
        congr 1; omega
      rw [h2, hnet2]
      have hnet1' : heapNet (n := n) sched1 ((n - 2) + 1) (by omega) = Zp n hn5 hodd := by
        simpa [hnm1_eq2] using hnet1_eq
      rw [hnet1']
      have hZp_pow : (Zp n hn5 hodd) ^ ((n - 2) + 2) = Zp n hn5 hodd := by
        have hexp : (n - 2) + 2 = (n - 1) + 1 := by omega
        rw [hexp, pow_succ]
        have h1 : (Zp n hn5 hodd) ^ (n - 1) = 1 := cyclePerm_pow_self (by omega) (by omega) _
        rw [h1, one_mul]
      rw [hZp_pow]
      have hcyc_eq : cyclePerm hk2 (by omega) topOrd' =
          cyclePerm le_rfl (by omega) (topOrd n hn5 hodd) := by
        ext x
        set i := (topOrd n hn5 hodd).symm x
        have hx1 : x = emb le_rfl (topOrd n hn5 hodd i) := Fin.ext (by simp [emb, i])
        have hx2 : x = emb hk2 (topOrd' (finCongr hn_eq2.symm i)) :=
          Fin.ext (by simp [emb, topOrd', i])
        rw [hx2, cyclePerm_apply_ord, ← hx2, hx1, cyclePerm_apply_ord]
        simp only [emb, topOrd', Equiv.trans_apply, finCongr_apply, Fin.val_cast]
        congr 2; apply Fin.ext; simp [hn_eq2]
      rw [hcyc_eq, ← Z_eq_cyclePerm_topOrd n hn5 hodd, ← mul_assoc, mul_inv_cancel, one_mul]
    have hbasic := heapRun_basic sched2 n le_rfl (by omega)
    refine ⟨sched2, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [heapArrays, List.head?_map, hbasic.1]; simp
    · simp only [heapArrays, List.getLast?_map, hbasic.2.1]
      simp [hnet_n, targetState]
    · simp only [heapArrays, List.length_map, hbasic.2.2.1]
    · exact hnodup_n.map inv_injective
    · exact (List.isChain_map (·⁻¹)).mpr (hbasic.2.2.2.1.imp fun _ _ h => adjArray_of_adjState h)

/-- Combined summary theorem: for every odd `n ≥ 3`, there exists a valid single-swap
Heap-type enumeration of all `n!` permutations of `Fin n` ending at `targetArray n`, which is
an odd permutation lexicographically maximal among all odd permutations in `S_n`. -/
theorem russo_open_question_item2 (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    Equiv.Perm.sign (targetArray n (by omega)) = -1 ∧
    (∀ p : Perm (Fin n), Equiv.Perm.sign p = -1 →
      List.ofFn p ≤ List.ofFn (targetArray n (by omega))) ∧
    ∃ sched : HeapSchedule,
      (heapArrays (n := n) sched).head? = some 1 ∧
      (heapArrays (n := n) sched).getLast? = some (targetArray n (by omega)) ∧
      (heapArrays (n := n) sched).length = Nat.factorial n ∧
      (heapArrays (n := n) sched).Nodup ∧
      (heapArrays (n := n) sched).IsChain AdjArray :=
  ⟨sign_targetArray n (by omega),
   fun p hp => targetArray_lex_max n (by omega) p hp,
   russo_odd_extremal_heap n hn hodd⟩

end RussoHeapOddExtremal
