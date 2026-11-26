import Mathlib

/-!
# Disproof of Manna–Mandal Problem 7.10, Question 2 (`arXiv:2611.27642v1`)

Reference: P. Manna and S. Mandal, "On the prime index elements graph of finite groups",
arXiv:2611.27642v1 [math.GR] (20 Nov 2026), §7.3, Theorem 7.6 and Problem 7.10.

We construct the finite non-abelian 3-group `PGrp` of order `243`,
`P = (ZMod 9 × ZMod 9) × Fin 3` with
`(v, i) * (w, j) = (v + s^i(w) + [i + j ≥ 3] u, (i + j) mod 3)`,
where `s(a, b) = (-b, a - b)` and `u = (6, 3)`, and set
`K = PGrp × Multiplicative (ZMod 5)` (order `1215`) and
`G = PGrp × Multiplicative (ZMod 10)` (order `2430`, isomorphic to `K × Z_2`).

We formally prove:
1. `PGrp` is a non-abelian group of order `243` with element-order profile `(1: 1, 3: 8, 9: 234)`.
2. `(H1)` holds for every prime dividing `|K|`:
   `N_3(P) = 4 ≤ 10 = 2 * 5` and `N_5(Z_5) = 1 ≤ 486 = 2 * 243`.
3. `(H2)` fails for `p = 3` at `C = ⟨u⟩` of order `3`:
   `c_P(⟨u⟩) = 30 > 19 = 2 * φ(3) * 5 - 1`.
4. Directly from the definition of the prime index elements graph `Γ(G)`, deleting the `20`-vertex
   cut set `S = {(y, t) | y ∈ {u, u^2}}` disconnects `Γ(G)` into at least `31` components, proving
   that `Γ(G)` has neither a Hamiltonian path nor a Hamiltonian cycle.
-/

namespace MannaMandalPrimeIndexGraph

open Finset
open scoped Classical

/-! ### Section 1: The non-abelian 3-group `PGrp` of order 243 -/

/-- Underlying set of the order-243 irregular 3-group `P = Z_9^2 × {0, 1, 2}`. -/
@[ext]
structure PGrp where
  a : ZMod 9
  b : ZMod 9
  i : Fin 3
  deriving DecidableEq

/-- Equivalence between `PGrp` and `ZMod 9 × ZMod 9 × Fin 3`. -/
def pGrpEquiv : PGrp ≃ ZMod 9 × ZMod 9 × Fin 3 where
  toFun x := (x.a, x.b, x.i)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype PGrp := Fintype.ofEquiv _ pGrpEquiv.symm

lemma card_PGrp : Fintype.card PGrp = 243 := by
  rw [Fintype.card_congr pGrpEquiv, Fintype.card_prod, Fintype.card_prod, ZMod.card, Fintype.card_fin]

/-- Order-3 automorphism `s(a, b) = (-b, a - b)` iterated `i` times on `ZMod 9 × ZMod 9`. -/
def sAct : Fin 3 → ZMod 9 × ZMod 9 → ZMod 9 × ZMod 9
  | ⟨0, _⟩, (a, b) => (a, b)
  | ⟨1, _⟩, (a, b) => (-b, a - b)
  | ⟨2, _⟩, (a, b) => (b - a, -a)

private lemma sAct_add (i : Fin 3) (v w : ZMod 9 × ZMod 9) :
    sAct i (v.1 + w.1, v.2 + w.2) = ((sAct i v).1 + (sAct i w).1, (sAct i v).2 + (sAct i w).2) := by
  rcases v with ⟨v1, v2⟩; rcases w with ⟨w1, w2⟩
  fin_cases i <;> ext <;> dsimp [sAct] <;> ring

private lemma sAct_u (i : Fin 3) : sAct i (6, 3) = (6, 3) := by
  fin_cases i <;> decide

private lemma sAct_zero (i : Fin 3) : sAct i (0, 0) = (0, 0) := by
  fin_cases i <;> decide

private lemma sAct_comp (i j : Fin 3) (v : ZMod 9 × ZMod 9) :
    sAct i (sAct j v) = sAct ⟨(i.val + j.val) % 3, Nat.mod_lt _ (by omega)⟩ v := by
  rcases v with ⟨a, b⟩
  fin_cases i <;> fin_cases j <;> ext <;> dsimp [sAct] <;> ring

/-- Group multiplication on `PGrp` with cocycle `u = (6, 3) = (-3, 3) mod 9`. -/
def mulP (x y : PGrp) : PGrp :=
  let w := sAct x.i (y.a, y.b)
  let c : ZMod 9 := if 3 ≤ x.i.val + y.i.val then 1 else 0
  ⟨x.a + w.1 + c * 6, x.b + w.2 + c * 3, ⟨(x.i.val + y.i.val) % 3, Nat.mod_lt _ (by omega)⟩⟩

/-- Identity element `(0, 0, 0)` of `PGrp`. -/
def oneP : PGrp := ⟨0, 0, 0⟩

/-- Inverse in `PGrp`. -/
def invP (x : PGrp) : PGrp :=
  match x.i with
  | ⟨0, _⟩ => ⟨-x.a, -x.b, 0⟩
  | ⟨1, _⟩ =>
    let w := sAct 2 (-x.a - 6, -x.b - 3)
    ⟨w.1, w.2, 2⟩
  | ⟨2, _⟩ =>
    let w := sAct 1 (-x.a - 6, -x.b - 3)
    ⟨w.1, w.2, 1⟩

private lemma nine_eq_zero : (9 : ZMod 9) = 0 := rfl

private lemma mulP_assoc (x y z : PGrp) : mulP (mulP x y) z = mulP x (mulP y z) := by
  rcases x with ⟨xa, xb, xi⟩
  rcases y with ⟨ya, yb, yi⟩
  rcases z with ⟨za, zb, zi⟩
  have h9 := nine_eq_zero
  fin_cases xi <;> fin_cases yi <;> fin_cases zi <;>
    · ext <;> dsimp [mulP, sAct] <;>
        (try simp only [Nat.reduceLeDiff, ↓reduceIte, zero_mul, one_mul, add_zero]) <;>
        first | rfl | decide | linear_combination | linear_combination h9

private lemma oneP_mul (x : PGrp) : mulP oneP x = x := by
  rcases x with ⟨xa, xb, xi⟩
  fin_cases xi <;>
    · ext <;> dsimp [mulP, oneP, sAct] <;> first | rfl | ring

private lemma mulP_one (x : PGrp) : mulP x oneP = x := by
  rcases x with ⟨xa, xb, xi⟩
  fin_cases xi <;>
    · ext <;> dsimp [mulP, oneP, sAct] <;> first | rfl | ring

private lemma invP_mul (x : PGrp) : mulP (invP x) x = oneP := by
  rcases x with ⟨xa, xb, xi⟩
  have h9 := nine_eq_zero
  fin_cases xi <;>
    · ext <;> dsimp [mulP, oneP, invP, sAct] <;>
        first | rfl | decide | linear_combination | linear_combination h9

instance : Group PGrp where
  mul := mulP
  one := oneP
  inv := invP
  mul_assoc := mulP_assoc
  one_mul := oneP_mul
  mul_one := mulP_one
  inv_mul_cancel := invP_mul

/-- The central order-3 element `u = ((6, 3), 0) ∈ PGrp`. -/
def uElem : PGrp := ⟨6, 3, 0⟩

private lemma mul_def (x y : PGrp) : x * y = mulP x y := rfl
private lemma one_def : (1 : PGrp) = oneP := rfl

lemma PGrp_nonabelian : ∃ x y : PGrp, x * y ≠ y * x := by
  refine ⟨⟨1, 0, 0⟩, ⟨0, 0, 1⟩, ?_⟩
  decide

lemma uElem_sq : uElem ^ 2 = ⟨3, 6, 0⟩ := by decide
lemma uElem_pow_three : uElem ^ 3 = 1 := by decide
lemma uElem_ne_one : uElem ≠ 1 := by decide
lemma uElem_sq_ne_one : uElem ^ 2 ≠ 1 := by decide
lemma uElem_ne_sq : uElem ≠ uElem ^ 2 := by decide

lemma orderOf_uElem : orderOf uElem = 3 := by
  rw [orderOf_eq_iff (by omega)]
  refine ⟨uElem_pow_three, fun m hm hpos => ?_⟩
  interval_cases m <;> decide

private lemma PGrp_pow_three_zero {a b : ZMod 9} :
    (⟨a, b, 0⟩ : PGrp) ^ 3 = ⟨3 * a, 3 * b, 0⟩ := by
  rw [pow_succ, pow_two]
  ext <;> dsimp [mul_def, mulP, sAct] <;> first | rfl | ring

private lemma PGrp_pow_three_one {a b : ZMod 9} :
    (⟨a, b, 1⟩ : PGrp) ^ 3 = uElem := by
  rw [pow_succ, pow_two]
  ext <;> dsimp [mul_def, mulP, sAct, uElem] <;> first | rfl | ring

private lemma PGrp_pow_three_two {a b : ZMod 9} :
    (⟨a, b, 2⟩ : PGrp) ^ 3 = uElem ^ 2 := by
  rw [pow_succ, pow_two, uElem_sq]
  have h9 := nine_eq_zero
  ext <;> dsimp [mul_def, mulP, sAct] <;>
    first | rfl | decide | linear_combination | linear_combination h9

lemma PGrp_pow_nine (x : PGrp) : x ^ 9 = 1 := by
  rcases x with ⟨a, b, i⟩
  rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul]
  fin_cases i
  · change ((⟨a, b, 0⟩ : PGrp) ^ 3) ^ 3 = 1
    rw [PGrp_pow_three_zero, PGrp_pow_three_zero]
    have h9 := nine_eq_zero
    ext <;> dsimp [one_def, oneP] <;> first | rfl | linear_combination a * h9 | linear_combination b * h9
  · change ((⟨a, b, 1⟩ : PGrp) ^ 3) ^ 3 = 1
    rw [PGrp_pow_three_one, uElem_pow_three]
  · change ((⟨a, b, 2⟩ : PGrp) ^ 3) ^ 3 = 1
    rw [PGrp_pow_three_two, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, uElem_pow_three, one_pow]

private lemma orderOf_PGrp_dvd_nine (x : PGrp) : orderOf x ∣ 9 :=
  orderOf_dvd_iff_pow_eq_one.mpr (PGrp_pow_nine x)

private lemma orderOf_PGrp_cases (x : PGrp) :
    orderOf x = 1 ∨ orderOf x = 3 ∨ orderOf x = 9 := by
  have hd := orderOf_PGrp_dvd_nine x
  have hle : orderOf x ≤ 9 := Nat.le_of_dvd (by omega) hd
  have hpos : 0 < orderOf x := orderOf_pos x
  interval_cases h : orderOf x <;> simp_all

private lemma orderOf_eq_three_iff (x : PGrp) :
    orderOf x = 3 ↔ x ≠ 1 ∧ x ^ 3 = 1 := by
  constructor
  · intro h
    refine ⟨fun h1 => by subst h1; simp at h, ?_⟩
    rw [← h, pow_orderOf_eq_one]
  · rintro ⟨hne, h3⟩
    rcases orderOf_PGrp_cases x with h1 | h3' | h9
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h3'
    · have hd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
      rw [h9] at hd
      omega

private lemma orderOf_eq_nine_iff (x : PGrp) :
    orderOf x = 9 ↔ x ^ 3 ≠ 1 := by
  constructor
  · intro h h3
    have hd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
    rw [h] at hd
    omega
  · intro hne
    rcases orderOf_PGrp_cases x with h1 | h3 | h9
    · exact absurd (by rw [orderOf_eq_one_iff.mp h1, one_pow]) hne
    · exact absurd (by rw [← h3, pow_orderOf_eq_one]) hne
    · exact h9

/-! ### Section 2: Cyclic subgroups, `N_p(P)`, `c_P(C)`, `(H1)`, and `(H2)` -/

/-- All cyclic subgroups of a finite group `H`. -/
noncomputable def allCyclic (H : Type*) [Group H] [Fintype H] : Finset (Subgroup H) :=
  Finset.univ.image Subgroup.zpowers

/-- Number `c_H(C)` of cyclic subgroups `D ≤ H` containing `C` as an index-`p` subgroup. -/
noncomputable def childrenCount {H : Type*} [Group H] [Fintype H] (p : ℕ) (C : Subgroup H) : ℕ :=
  ((allCyclic H).filter fun D => C < D ∧ Nat.card D = p * Nat.card C).card

/-- Number `N_p(H) = c_H(1)` of subgroups of `H` of prime order `p`. -/
noncomputable def Np (H : Type*) [Group H] [Fintype H] (p : ℕ) : ℕ :=
  childrenCount p (⊥ : Subgroup H)

private lemma zpowers_eq_iff_pow {H : Type*} [Group H] [Fintype H] {x y : H} :
    Subgroup.zpowers x = Subgroup.zpowers y ↔
      x ∈ Subgroup.zpowers y ∧ orderOf x = orderOf y := by
  constructor
  · intro h
    refine ⟨h ▸ Subgroup.mem_zpowers x, ?_⟩
    rw [← Nat.card_zpowers, ← Nat.card_zpowers, h]
  · rintro ⟨hmem, hord⟩
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hmem
    refine SetLike.ext' (Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle ?_)
    change Nat.card (Subgroup.zpowers y) ≤ Nat.card (Subgroup.zpowers x)
    rw [Nat.card_zpowers, Nat.card_zpowers, hord]

private lemma card_order3_elems :
    (Finset.univ.filter fun x : PGrp => orderOf x = 3).card = 8 := by
  have h8 : (Finset.univ.filter fun ab : ZMod 9 × ZMod 9 =>
      (ab.1 ≠ 0 ∨ ab.2 ≠ 0) ∧ 3 * ab.1 = 0 ∧ 3 * ab.2 = 0).card = 8 := by
    decide
  rw [← h8]
  refine Finset.card_bij (fun x _ => (x.a, x.b)) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    rcases x with ⟨a, b, i⟩
    have ⟨hne, h3⟩ := (orderOf_eq_three_iff ⟨a, b, i⟩).mp hx.2
    refine ⟨Finset.mem_univ _, ?_⟩
    fin_cases i
    · change (⟨a, b, 0⟩ : PGrp) ^ 3 = 1 at h3
      rw [PGrp_pow_three_zero] at h3
      have ha : 3 * a = 0 := congrArg PGrp.a h3
      have hb : 3 * b = 0 := congrArg PGrp.b h3
      refine ⟨?_, ha, hb⟩
      by_contra h0
      push Not at h0
      exact hne (PGrp.ext h0.1 h0.2 rfl)
    · change (⟨a, b, 1⟩ : PGrp) ^ 3 = 1 at h3
      rw [PGrp_pow_three_one] at h3
      exact absurd h3 uElem_ne_one
    · change (⟨a, b, 2⟩ : PGrp) ^ 3 = 1 at h3
      rw [PGrp_pow_three_two] at h3
      exact absurd h3 uElem_sq_ne_one
  · intro x₁ hx₁ x₂ hx₂ hEq
    rw [Finset.mem_filter] at hx₁ hx₂
    have hi0 : ∀ x : PGrp, orderOf x = 3 → x.i = 0 := by
      rintro ⟨a, b, i⟩ h
      have h3 := ((orderOf_eq_three_iff ⟨a, b, i⟩).mp h).2
      fin_cases i
      · rfl
      · change (⟨a, b, 1⟩ : PGrp) ^ 3 = 1 at h3
        rw [PGrp_pow_three_one] at h3; exact absurd h3 uElem_ne_one
      · change (⟨a, b, 2⟩ : PGrp) ^ 3 = 1 at h3
        rw [PGrp_pow_three_two] at h3; exact absurd h3 uElem_sq_ne_one
    exact PGrp.ext (congrArg Prod.fst hEq) (congrArg Prod.snd hEq)
      ((hi0 x₁ hx₁.2).trans (hi0 x₂ hx₂.2).symm)
  · intro ab hab
    rw [Finset.mem_filter] at hab
    refine ⟨⟨ab.1, ab.2, 0⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rw [orderOf_eq_three_iff]
    refine ⟨?_, ?_⟩
    · intro h1
      rcases hab.2.1 with h | h
      · exact h (congrArg PGrp.a h1)
      · exact h (congrArg PGrp.b h1)
    · rw [PGrp_pow_three_zero]
      exact PGrp.ext hab.2.2.1 hab.2.2.2 rfl

/-- Element-order profile of `PGrp`: `1` element of order `1`, `8` of order `3`, `234` of order `9`. -/
theorem PGrp_order_profile :
    (Finset.univ.filter fun x : PGrp => orderOf x = 1).card = 1 ∧
    (Finset.univ.filter fun x : PGrp => orderOf x = 3).card = 8 ∧
    (Finset.univ.filter fun x : PGrp => orderOf x = 9).card = 234 := by
  have h1 : (Finset.univ.filter fun x : PGrp => orderOf x = 1).card = 1 := by
    have hset : (Finset.univ.filter fun x : PGrp => orderOf x = 1) = {1} := by
      ext x; simp [orderOf_eq_one_iff]
    rw [hset, Finset.card_singleton]
  have h3 := card_order3_elems
  have h9 : (Finset.univ.filter fun x : PGrp => orderOf x = 9).card = 234 := by
    have hdisj13 : Disjoint (Finset.univ.filter fun x : PGrp => orderOf x = 1)
        (Finset.univ.filter fun x : PGrp => orderOf x = 3) := by
      rw [Finset.disjoint_filter]; intro _ _ h₁ h₃; omega
    have hdisj13_9 : Disjoint
        ((Finset.univ.filter fun x : PGrp => orderOf x = 1) ∪
          (Finset.univ.filter fun x : PGrp => orderOf x = 3))
        (Finset.univ.filter fun x : PGrp => orderOf x = 9) := by
      rw [Finset.disjoint_left]
      intro x hx h9'
      simp only [Finset.mem_union, Finset.mem_filter] at hx h9'
      rcases hx with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    have hunion :
        ((Finset.univ.filter fun x : PGrp => orderOf x = 1) ∪
          (Finset.univ.filter fun x : PGrp => orderOf x = 3)) ∪
          (Finset.univ.filter fun x : PGrp => orderOf x = 9) = Finset.univ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rcases orderOf_PGrp_cases x with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hcard := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj13_9, Finset.card_union_of_disjoint hdisj13,
      Finset.card_univ, card_PGrp, h1, h3] at hcard
    omega
  exact ⟨h1, h3, h9⟩

private lemma mem_zpowers_nat_pow {H : Type*} [Group H] {y x : H} (hy : 0 < orderOf y)
    (hx : x ∈ Subgroup.zpowers y) :
    ∃ k < orderOf y, y ^ k = x := by
  rcases Subgroup.mem_zpowers_iff.mp hx with ⟨m, rfl⟩
  refine ⟨(m % (orderOf y : ℤ)).toNat, ?_, ?_⟩
  · have hnn : 0 ≤ m % (orderOf y : ℤ) := Int.emod_nonneg m (by omega)
    have hlt : m % (orderOf y : ℤ) < (orderOf y : ℤ) := Int.emod_lt_of_pos m (by omega)
    omega
  · have hmod : m = (orderOf y : ℤ) * (m / (orderOf y : ℤ)) + m % (orderOf y : ℤ) :=
      (Int.mul_ediv_add_emod m (orderOf y : ℤ)).symm
    have hnn : 0 ≤ m % (orderOf y : ℤ) := Int.emod_nonneg m (by omega)
    conv_rhs => rw [hmod, zpow_add, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, one_mul]
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn]

/-- `N_3(P) = 4`, so `(H1)` holds for `p = 3` with `m_3 = 5` (`4 ≤ 2 * 5 = 10`). -/
theorem N3P_eq_four : Np PGrp 3 = 4 := by
  unfold Np childrenCount
  set S3 := Finset.univ.filter fun x : PGrp => orderOf x = 3
  set T3 := (allCyclic PGrp).filter fun D => (⊥ : Subgroup PGrp) < D ∧ Nat.card D = 3 * Nat.card (⊥ : Subgroup PGrp)
  have hbot : Nat.card (⊥ : Subgroup PGrp) = 1 := by simp
  have hmaps : ∀ x ∈ S3, Subgroup.zpowers x ∈ T3 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, ?_, ?_⟩
    · rw [bot_lt_iff_ne_bot]
      intro hbot'
      have h1 : x = 1 := by
        have hxmem : x ∈ (⊥ : Subgroup PGrp) := hbot' ▸ Subgroup.mem_zpowers x
        simpa using hxmem
      subst h1; simp at hx
    · rw [Nat.card_zpowers, hx.2, hbot, mul_one]
  have hfiber : ∀ D ∈ T3, (S3.filter fun x => Subgroup.zpowers x = D).card = 2 := by
    intro D hD
    rw [Finset.mem_filter] at hD
    rcases Finset.mem_image.mp hD.1 with ⟨y, _, rfl⟩
    have hy3 : orderOf y = 3 := by
      have := hD.2.2
      rw [Nat.card_zpowers, hbot, mul_one] at this
      exact this
    have hset : (S3.filter fun x => Subgroup.zpowers x = Subgroup.zpowers y) = {y, y ^ 2} := by
      ext x
      simp only [Finset.mem_filter, S3, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hx3, hEq⟩
        have hmem : x ∈ Subgroup.zpowers y := hEq ▸ Subgroup.mem_zpowers x
        obtain ⟨k, hk, rfl⟩ := mem_zpowers_nat_pow (by omega : 0 < orderOf y) hmem
        rw [hy3] at hk
        interval_cases k
        · simp at hx3
        · left; simp
        · right; rfl
      · rintro (rfl | rfl)
        · exact ⟨hy3, rfl⟩
        · have hy2_ord : orderOf (y ^ 2) = 3 := by
            rw [orderOf_pow, hy3]; norm_num
          refine ⟨hy2_ord, zpowers_eq_iff_pow.mpr ⟨?_, by rw [hy2_ord, hy3]⟩⟩
          exact Subgroup.npow_mem_zpowers y 2
    rw [hset, Finset.card_pair]
    intro hEq
    have hy1 : y = 1 := by
      have : y * 1 = y * y := by simpa [sq] using hEq
      exact (mul_left_cancel this).symm
    subst hy1; simp at hy3
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, card_order3_elems] at hsum
  omega

/-- `N_5(Z_5) = 1`, so `(H1)` holds for `p = 5` with `m_5 = 243` (`1 ≤ 2 * 243 = 486`). -/
theorem N5Z5_eq_one : Np (Multiplicative (ZMod 5)) 5 = 1 := by
  unfold Np childrenCount
  have hbot : Nat.card (⊥ : Subgroup (Multiplicative (ZMod 5))) = 1 := by simp
  have hset : ((allCyclic (Multiplicative (ZMod 5))).filter fun D =>
      (⊥ : Subgroup (Multiplicative (ZMod 5))) < D ∧
        Nat.card D = 5 * Nat.card (⊥ : Subgroup (Multiplicative (ZMod 5)))) = {⊤} := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_singleton, hbot, mul_one]
    constructor
    · rintro ⟨_, _, hcard⟩
      have htop_card : Nat.card (⊤ : Subgroup (Multiplicative (ZMod 5))) = 5 := by
        rw [Subgroup.card_top, Nat.card_eq_fintype_card]; simp [ZMod.card]
      refine SetLike.ext' (Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) (fun _ _ => trivial) ?_)
      change Nat.card (⊤ : Subgroup (Multiplicative (ZMod 5))) ≤ Nat.card D
      rw [htop_card, hcard]
    · rintro rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [allCyclic, Finset.mem_image]
        refine ⟨Multiplicative.ofAdd (1 : ZMod 5), Finset.mem_univ _, ?_⟩
        ext x
        simp only [Subgroup.mem_top, iff_true, Subgroup.mem_zpowers_iff]
        refine ⟨((Multiplicative.toAdd x).val : ℤ), ?_⟩
        change Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ℤ) • (1 : ZMod 5)) = x
        simp
      · rw [bot_lt_iff_ne_bot]
        intro h
        have : Multiplicative.ofAdd (1 : ZMod 5) ∈ (⊥ : Subgroup (Multiplicative (ZMod 5))) :=
          h ▸ trivial
        have h10 : (1 : ZMod 5) = 0 := by simpa using this
        exact absurd h10 (by decide)
      · rw [Subgroup.card_top, Nat.card_eq_fintype_card]; simp [ZMod.card]
  rw [hset, Finset.card_singleton]

private lemma card_cube_in_u :
    (Finset.univ.filter fun x : PGrp => x ^ 3 = uElem ∨ x ^ 3 = uElem ^ 2).card = 180 := by
  set Su := Finset.univ.filter fun x : PGrp => x ^ 3 = uElem ∨ x ^ 3 = uElem ^ 2
  have hsplit : Su =
      (Su.filter fun x => x.i = 0) ∪ ((Su.filter fun x => x.i = 1) ∪ (Su.filter fun x => x.i = 2)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      rcases x with ⟨a, b, i⟩
      fin_cases i
      · exact Or.inl ⟨hx, rfl⟩
      · exact Or.inr (Or.inl ⟨hx, rfl⟩)
      · exact Or.inr (Or.inr ⟨hx, rfl⟩)
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hdisj12 : Disjoint (Su.filter fun x => x.i = 1) (Su.filter fun x => x.i = 2) := by
    rw [Finset.disjoint_filter]; intro _ _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
  have hdisj012 : Disjoint (Su.filter fun x => x.i = 0)
      ((Su.filter fun x => x.i = 1) ∪ (Su.filter fun x => x.i = 2)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_union, Finset.mem_filter] at hx hy
    rcases hy with ⟨_, h1⟩ | ⟨_, h2⟩
    · rw [hx.2] at h1; exact absurd h1 (by decide)
    · rw [hx.2] at h2; exact absurd h2 (by decide)
  have hc0 : (Su.filter fun x => x.i = 0).card = 18 := by
    have h18 : (Finset.univ.filter fun ab : ZMod 9 × ZMod 9 =>
        (3 * ab.1 = 6 ∧ 3 * ab.2 = 3) ∨ (3 * ab.1 = 3 ∧ 3 * ab.2 = 6)).card = 18 := by
      decide
    rw [← h18]
    refine Finset.card_bij (fun x _ => (x.a, x.b)) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Su, Finset.mem_univ, true_and] at hx ⊢
      rcases x with ⟨a, b, i⟩
      dsimp at hx ⊢
      obtain ⟨hx1, rfl⟩ := hx
      rw [PGrp_pow_three_zero, uElem_sq] at hx1
      rcases hx1 with h | h
      · left; exact ⟨congrArg PGrp.a h, congrArg PGrp.b h⟩
      · right; exact ⟨congrArg PGrp.a h, congrArg PGrp.b h⟩
    · intro x₁ hx₁ x₂ hx₂ hEq
      simp only [Finset.mem_filter] at hx₁ hx₂
      exact PGrp.ext (congrArg Prod.fst hEq) (congrArg Prod.snd hEq) (hx₁.2.trans hx₂.2.symm)
    · intro ab hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
      refine ⟨⟨ab.1, ab.2, 0⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Su, Finset.mem_univ, true_and, and_true]
      rw [PGrp_pow_three_zero, uElem_sq]
      rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · left; exact PGrp.ext ha hb rfl
      · right; exact PGrp.ext ha hb rfl
  have hc1 : (Su.filter fun x => x.i = 1).card = 81 := by
    have h81 : (Finset.univ : Finset (ZMod 9 × ZMod 9)).card = 81 := by
      rw [Finset.card_univ, Fintype.card_prod, ZMod.card]
    rw [← h81]
    refine Finset.card_bij (fun x _ => (x.a, x.b)) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro x₁ hx₁ x₂ hx₂ hEq
      simp only [Finset.mem_filter] at hx₁ hx₂
      exact PGrp.ext (congrArg Prod.fst hEq) (congrArg Prod.snd hEq) (hx₁.2.trans hx₂.2.symm)
    · intro ab _
      refine ⟨⟨ab.1, ab.2, 1⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Su, Finset.mem_univ, true_and, and_true]
      exact Or.inl PGrp_pow_three_one
  have hc2 : (Su.filter fun x => x.i = 2).card = 81 := by
    have h81 : (Finset.univ : Finset (ZMod 9 × ZMod 9)).card = 81 := by
      rw [Finset.card_univ, Fintype.card_prod, ZMod.card]
    rw [← h81]
    refine Finset.card_bij (fun x _ => (x.a, x.b)) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro x₁ hx₁ x₂ hx₂ hEq
      simp only [Finset.mem_filter] at hx₁ hx₂
      exact PGrp.ext (congrArg Prod.fst hEq) (congrArg Prod.snd hEq) (hx₁.2.trans hx₂.2.symm)
    · intro ab _
      refine ⟨⟨ab.1, ab.2, 2⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Su, Finset.mem_univ, true_and, and_true]
      exact Or.inr PGrp_pow_three_two
  rw [hsplit, Finset.card_union_of_disjoint hdisj012, Finset.card_union_of_disjoint hdisj12,
    hc0, hc1, hc2]

private lemma zpowers_uElem_lt_iff (y : PGrp) :
    (Subgroup.zpowers uElem < Subgroup.zpowers y ∧
      Nat.card (Subgroup.zpowers y) = 3 * Nat.card (Subgroup.zpowers uElem)) ↔
      (y ^ 3 = uElem ∨ y ^ 3 = uElem ^ 2) := by
  have hu3 : Nat.card (Subgroup.zpowers uElem) = 3 := by
    rw [Nat.card_zpowers, orderOf_uElem]
  rw [hu3, Nat.card_zpowers]
  constructor
  · rintro ⟨hlt, hord⟩
    have humem : uElem ∈ Subgroup.zpowers y := hlt.le (Subgroup.mem_zpowers uElem)
    obtain ⟨k, hk, hky⟩ := mem_zpowers_nat_pow (by omega : 0 < orderOf y) humem
    rw [hord] at hk
    have h3k : y ^ (3 * k) = 1 := by
      rw [mul_comm, pow_mul, hky, uElem_pow_three]
    have hdvd : 9 ∣ 3 * k := by
      have := orderOf_dvd_iff_pow_eq_one.mpr h3k
      rwa [hord] at this
    interval_cases k
    · simp at hky; exact absurd hky.symm uElem_ne_one
    · omega
    · omega
    · left; exact hky
    · omega
    · omega
    · right
      have hsq : uElem ^ 2 = y ^ 12 := by rw [← hky, ← pow_mul]
      have h12 : y ^ 12 = y ^ 3 := by
        rw [show (12 : ℕ) = 9 + 3 by norm_num, pow_add, PGrp_pow_nine, one_mul]
      exact (hsq.trans h12).symm
    · omega
    · omega
  · intro hcube
    have hne1 : y ^ 3 ≠ 1 := by
      rcases hcube with h | h
      · rw [h]; exact uElem_ne_one
      · rw [h]; exact uElem_sq_ne_one
    have hy9 : orderOf y = 9 := (orderOf_eq_nine_iff y).mpr hne1
    have hle : Subgroup.zpowers uElem ≤ Subgroup.zpowers y := by
      rw [Subgroup.zpowers_le]
      rcases hcube with h | h
      · rw [← h]; exact Subgroup.npow_mem_zpowers y 3
      · have : uElem = y ^ 6 := by
          calc uElem = uElem ^ 4 := by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, uElem_pow_three, one_mul, pow_one]
            _ = (uElem ^ 2) ^ 2 := by rw [← pow_mul]
            _ = (y ^ 3) ^ 2 := by rw [h]
            _ = y ^ 6 := by rw [← pow_mul]
        rw [this]; exact Subgroup.npow_mem_zpowers y 6
    refine ⟨lt_of_le_of_ne hle ?_, by omega⟩
    intro hEq
    have hcard := congrArg (fun S : Subgroup PGrp => Nat.card S) hEq
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_uElem, hy9] at hcard
    omega

/-- `c_P(⟨u⟩) = 30`, violating `(H2)` for `p = 3` with `m_3 = 5` (`30 > 19 = 2 * φ(3) * 5 - 1`). -/
theorem childrenCount_uElem : childrenCount 3 (Subgroup.zpowers uElem) = 30 := by
  unfold childrenCount
  set Su := Finset.univ.filter fun x : PGrp => x ^ 3 = uElem ∨ x ^ 3 = uElem ^ 2
  set Tu := (allCyclic PGrp).filter fun D =>
    Subgroup.zpowers uElem < D ∧ Nat.card D = 3 * Nat.card (Subgroup.zpowers uElem)
  have hmaps : ∀ x ∈ Su, Subgroup.zpowers x ∈ Tu := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, (zpowers_uElem_lt_iff x).mpr hx.2⟩
  have hfiber : ∀ D ∈ Tu, (Su.filter fun x => Subgroup.zpowers x = D).card = 6 := by
    intro D hD
    rw [Finset.mem_filter] at hD
    rcases Finset.mem_image.mp hD.1 with ⟨y, _, rfl⟩
    have hycube := (zpowers_uElem_lt_iff y).mp hD.2
    have hy9 : orderOf y = 9 := (orderOf_eq_nine_iff y).mpr (by
      rcases hycube with h | h
      · rw [h]; exact uElem_ne_one
      · rw [h]; exact uElem_sq_ne_one)
    have hset : (Su.filter fun x => Subgroup.zpowers x = Subgroup.zpowers y) =
        ({1, 2, 4, 5, 7, 8} : Finset ℕ).image (fun k => y ^ k) := by
      ext x
      simp only [Finset.mem_filter, Su, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hEq⟩
        have hx9 : orderOf x = 9 := by
          have := (zpowers_eq_iff_pow.mp hEq).2
          omega
        have hmem : x ∈ Subgroup.zpowers y := hEq ▸ Subgroup.mem_zpowers x
        obtain ⟨k, hk, rfl⟩ := mem_zpowers_nat_pow (by omega : 0 < orderOf y) hmem
        rw [hy9] at hk
        interval_cases k
        · simp at hx9
        · exact ⟨1, by simp, rfl⟩
        · exact ⟨2, by simp, rfl⟩
        · rw [orderOf_pow, hy9] at hx9; norm_num at hx9
        · exact ⟨4, by simp, rfl⟩
        · exact ⟨5, by simp, rfl⟩
        · rw [orderOf_pow, hy9] at hx9; norm_num at hx9
        · exact ⟨7, by simp, rfl⟩
        · exact ⟨8, by simp, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        have hkord : orderOf (y ^ k) = 9 := by
          rw [orderOf_pow, hy9]
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
        have hEq : Subgroup.zpowers (y ^ k) = Subgroup.zpowers y :=
          zpowers_eq_iff_pow.mpr ⟨Subgroup.npow_mem_zpowers y k, by rw [hkord, hy9]⟩
        refine ⟨?_, hEq⟩
        have hD' : Subgroup.zpowers uElem < Subgroup.zpowers (y ^ k) ∧
            Nat.card (Subgroup.zpowers (y ^ k)) = 3 * Nat.card (Subgroup.zpowers uElem) := by
          rw [hEq]; exact hD.2
        exact (zpowers_uElem_lt_iff (y ^ k)).mp hD'
    rw [hset, Finset.card_image_of_injOn]
    · decide
    · intro k₁ hk₁ k₂ hk₂ hEq
      have h1 : k₁ < orderOf y := by
        rw [hy9]; simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hk₁
        rcases hk₁ with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have h2 : k₂ < orderOf y := by
        rw [hy9]; simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hk₂
        rcases hk₂ with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      exact pow_injOn_Iio_orderOf h1 h2 hEq
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, card_cube_in_u] at hsum
  omega

/-- Exact `(H1)` and `¬(H2)` verification for `K = PGrp × Z_5` (`m_3 = 5`, `m_5 = 243`). -/
theorem H1_holds_and_H2_fails_for_K :
    let m3 := Fintype.card (Multiplicative (ZMod 5))
    let m5 := Fintype.card PGrp
    -- (H1) at p = 3: N_3(P) ≤ 2 m_3
    Np PGrp 3 ≤ 2 * m3 ∧
    -- (H1) at p = 5: N_5(Z_5) ≤ 2 m_5
    Np (Multiplicative (ZMod 5)) 5 ≤ 2 * m5 ∧
    -- (H2) fails at p = 3, C = ⟨u⟩: c_P(C) > 2 φ(|C|) m_3 - 1
    childrenCount 3 (Subgroup.zpowers uElem) >
      2 * Nat.totient (Nat.card (Subgroup.zpowers uElem)) * m3 - 1 := by
  dsimp only
  have hm3 : Fintype.card (Multiplicative (ZMod 5)) = 5 := by simp [ZMod.card]
  have hu3 : Nat.card (Subgroup.zpowers uElem) = 3 := by rw [Nat.card_zpowers, orderOf_uElem]
  have hphi3 : Nat.totient 3 = 2 := by decide
  rw [hm3, card_PGrp, N3P_eq_four, N5Z5_eq_one, childrenCount_uElem, hu3, hphi3]
  omega

/-! ### Section 3: Prime index elements graph `Γ(G)` and direct non-Hamiltonicity -/

/-- `⟨x⟩` has prime index in `⟨y⟩` in a finite group `G`. -/
def hasPrimeIndexIn {G : Type*} [Group G] (x y : G) : Prop :=
  Subgroup.zpowers x ≤ Subgroup.zpowers y ∧
    ∃ p : ℕ, Nat.Prime p ∧ orderOf y = p * orderOf x

/-- The prime index elements graph `Γ(G)` of a finite group `G` (Manna–Mandal, §1). -/
def primeIndexGraph (G : Type*) [Group G] : SimpleGraph G where
  Adj x y := x ≠ y ∧ (hasPrimeIndexIn x y ∨ hasPrimeIndexIn y x)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The target group `G = PGrp × Multiplicative (ZMod 10) ≅ K × Z_2` of order `2430`. -/
abbrev TargetG := PGrp × Multiplicative (ZMod 10)

lemma card_TargetG : Fintype.card TargetG = 2430 := by
  simp [TargetG, Fintype.card_prod, card_PGrp, ZMod.card]

/-- The 20-vertex cut set `S = {(y, t) ∈ G | y ∈ {u, u^2}}`. -/
def cutSet : Finset TargetG :=
  Finset.univ.filter fun g => g.1 = uElem ∨ g.1 = uElem ^ 2

lemma card_cutSet : cutSet.card = 20 := by
  have h1 : (Finset.univ.filter fun y : PGrp => y = uElem ∨ y = uElem ^ 2).card = 2 := by
    have hset : (Finset.univ.filter fun y : PGrp => y = uElem ∨ y = uElem ^ 2) = {uElem, uElem ^ 2} := by
      ext y; simp
    rw [hset, Finset.card_pair uElem_ne_sq]
  have hprod : cutSet =
      (Finset.univ.filter fun y : PGrp => y = uElem ∨ y = uElem ^ 2) ×ˢ
        (Finset.univ : Finset (Multiplicative (ZMod 10))) := by
    ext ⟨y, t⟩
    simp [cutSet]
  rw [hprod, Finset.card_product, h1, Finset.card_univ]
  simp [ZMod.card]

/-- The 31-valued branch invariant on `TargetG \ cutSet`:
maps `g = (y, t)` to `some ⟨y⟩` when `y^3 ∈ {u, u^2}` (the 30 child branches of `⟨u⟩`),
and to `none` otherwise (the root branch). -/
noncomputable def branchLabel (g : TargetG) : Option (Subgroup PGrp) :=
  if g.1 ^ 3 = uElem ∨ g.1 ^ 3 = uElem ^ 2 then some (Subgroup.zpowers g.1) else none

lemma card_branchLabel_image :
    ((Finset.univ \ cutSet).image branchLabel).card = 31 := by
  set Tu := (allCyclic PGrp).filter fun D =>
    Subgroup.zpowers uElem < D ∧ Nat.card D = 3 * Nat.card (Subgroup.zpowers uElem)
  have hTu_card : Tu.card = 30 := childrenCount_uElem
  have hEq : (Finset.univ \ cutSet).image branchLabel = insert none (Tu.image some) := by
    ext o
    simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and, cutSet,
      Finset.mem_filter, Finset.mem_insert, branchLabel]
    constructor
    · rintro ⟨⟨y, t⟩, _, rfl⟩
      by_cases hy : y ^ 3 = uElem ∨ y ^ 3 = uElem ^ 2
      · right
        rw [if_pos hy]
        exact ⟨Subgroup.zpowers y,
          Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩,
            (zpowers_uElem_lt_iff y).mpr hy⟩, rfl⟩
      · left; rw [if_neg hy]
    · rintro (rfl | ⟨D, hD, rfl⟩)
      · refine ⟨(1, 1), ?_, ?_⟩
        · rintro (h | h)
          · exact uElem_ne_one h.symm
          · exact uElem_sq_ne_one h.symm
        · have h1 : ¬ ((1 : PGrp) ^ 3 = uElem ∨ (1 : PGrp) ^ 3 = uElem ^ 2) := by
            rw [one_pow]; rintro (h | h)
            · exact uElem_ne_one h.symm
            · exact uElem_sq_ne_one h.symm
          exact if_neg h1
      · rw [Finset.mem_filter] at hD
        rcases Finset.mem_image.mp hD.1 with ⟨y, _, rfl⟩
        have hycube := (zpowers_uElem_lt_iff y).mp hD.2
        have hynot : ¬ (y = uElem ∨ y = uElem ^ 2) := by
          have hy9 : orderOf y = 9 := (orderOf_eq_nine_iff y).mpr (by
            rcases hycube with h | h
            · rw [h]; exact uElem_ne_one
            · rw [h]; exact uElem_sq_ne_one)
          rintro (rfl | rfl)
          · rw [orderOf_uElem] at hy9; omega
          · have h2 : orderOf (uElem ^ 2) = 3 := by rw [orderOf_pow, orderOf_uElem]; norm_num
            omega
        exact ⟨(y, 1), hynot, if_pos hycube⟩
  rw [hEq, Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ (Option.some_injective (Subgroup PGrp)), hTu_card]

private lemma hasPrimeIndexIn_fst_ratio {g h : TargetG} (hgh : hasPrimeIndexIn g h) :
    Subgroup.zpowers g.1 ≤ Subgroup.zpowers h.1 ∧
    (orderOf h.1 = orderOf g.1 ∨ orderOf h.1 = 3 * orderOf g.1) := by
  rcases hgh with ⟨hsub, p, hp, hord⟩
  have hsub1 : Subgroup.zpowers g.1 ≤ Subgroup.zpowers h.1 := by
    have hgmem : g ∈ Subgroup.zpowers h := hsub (Subgroup.mem_zpowers g)
    rcases Subgroup.mem_zpowers_iff.mp hgmem with ⟨k, hk⟩
    rw [Subgroup.zpowers_le, Subgroup.mem_zpowers_iff]
    exact ⟨k, congrArg Prod.fst hk⟩
  refine ⟨hsub1, ?_⟩
  have hdvd : orderOf g.1 ∣ orderOf h.1 := by
    have hgmem : g.1 ∈ Subgroup.zpowers h.1 := hsub1 (Subgroup.mem_zpowers g.1)
    rcases Subgroup.mem_zpowers_iff.mp hgmem with ⟨k, hk⟩
    rw [orderOf_dvd_iff_pow_eq_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have h10 : ∀ t : Multiplicative (ZMod 10), orderOf t ∣ 10 := fun t => by
    rw [orderOf_dvd_iff_pow_eq_one]
    change (10 : ℕ) • (Multiplicative.toAdd t) = 0
    rw [nsmul_eq_mul, Nat.cast_ofNat, show (10 : ZMod 10) = 0 from rfl, zero_mul]
  have hcop : ∀ y : PGrp, ∀ t : Multiplicative (ZMod 10), Nat.Coprime (orderOf y) (orderOf t) := by
    intro y t
    exact Nat.Coprime.coprime_dvd_left (orderOf_PGrp_dvd_nine y)
      (Nat.Coprime.coprime_dvd_right (h10 t) (by decide))
  have hord_g : orderOf g = orderOf g.1 * orderOf g.2 := by
    rw [Prod.orderOf_mk, (hcop g.1 g.2).lcm_eq_mul]
  have hord_h : orderOf h = orderOf h.1 * orderOf h.2 := by
    rw [Prod.orderOf_mk, (hcop h.1 h.2).lcm_eq_mul]
  have hdvd2 : orderOf g.2 ∣ orderOf h.2 := by
    have hgmem : g ∈ Subgroup.zpowers h := hsub (Subgroup.mem_zpowers g)
    rcases Subgroup.mem_zpowers_iff.mp hgmem with ⟨k, hk⟩
    rw [orderOf_dvd_iff_pow_eq_one]
    have hk2 : h.2 ^ k = g.2 := congrArg Prod.snd hk
    rw [← hk2, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
      one_zpow]
  rcases hdvd with ⟨q1, hq1⟩
  rcases hdvd2 with ⟨q2, hq2⟩
  have hmul_eq : q1 * q2 = p := by
    have hpos1 : 0 < orderOf g.1 := orderOf_pos g.1
    have hpos2 : 0 < orderOf g.2 := orderOf_pos g.2
    rw [hord_h, hord_g, hq1, hq2] at hord
    have hlin : (orderOf g.1 * orderOf g.2) * (q1 * q2) = (orderOf g.1 * orderOf g.2) * p := by
      linarith
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos1 hpos2) hlin
  have hq1_dvd_p : q1 ∣ p := ⟨q2, hmul_eq.symm⟩
  have hq1_dvd_9 : q1 ∣ 9 :=
    dvd_trans ⟨orderOf g.1, by rw [hq1, mul_comm]⟩ (orderOf_PGrp_dvd_nine h.1)
  rcases hp.eq_one_or_self_of_dvd q1 hq1_dvd_p with hq1_1 | hq1_p
  · left; rw [hq1, hq1_1, mul_one]
  · right
    have hp_dvd_9 : p ∣ 9 := hq1_p ▸ hq1_dvd_9
    have hp3 : p = 3 := by
      have hle : p ≤ 9 := Nat.le_of_dvd (by omega) hp_dvd_9
      have hge : 2 ≤ p := hp.two_le
      interval_cases p
      · exfalso; norm_num at hp_dvd_9
      · rfl
      · exfalso; norm_num at hp
      · exfalso; norm_num at hp_dvd_9
      · exfalso; norm_num at hp
      · exfalso; norm_num at hp_dvd_9
      · exfalso; norm_num at hp
      · exfalso; norm_num at hp
    rw [hq1, hq1_p, hp3, mul_comm]

/-- Pure algebraic branch-preservation lemma on `PGrp`. -/
private lemma PGrp_branch_step {x y : PGrp} (hsub : Subgroup.zpowers x ≤ Subgroup.zpowers y) :
    (orderOf y = orderOf x →
      Subgroup.zpowers x = Subgroup.zpowers y ∧
        ((x ^ 3 = uElem ∨ x ^ 3 = uElem ^ 2) ↔ (y ^ 3 = uElem ∨ y ^ 3 = uElem ^ 2))) ∧
    (orderOf y = 3 * orderOf x →
      (y ^ 3 = uElem ∨ y ^ 3 = uElem ^ 2) → (x = uElem ∨ x = uElem ^ 2)) ∧
    (orderOf y = 3 * orderOf x → ¬ (x ^ 3 = uElem ∨ x ^ 3 = uElem ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have hEq : Subgroup.zpowers x = Subgroup.zpowers y :=
      zpowers_eq_iff_pow.mpr ⟨hsub (Subgroup.mem_zpowers x), heq.symm⟩
    refine ⟨hEq, ?_⟩
    rw [← zpowers_uElem_lt_iff x, ← zpowers_uElem_lt_iff y, hEq]
  · intro h3 hycube
    have hy9 : orderOf y = 9 := (orderOf_eq_nine_iff y).mpr (by
      rcases hycube with h | h
      · rw [h]; exact uElem_ne_one
      · rw [h]; exact uElem_sq_ne_one)
    have hx3 : orderOf x = 3 := by omega
    have hmem : x ∈ Subgroup.zpowers y := hsub (Subgroup.mem_zpowers x)
    obtain ⟨k, hk, rfl⟩ := mem_zpowers_nat_pow (by omega : 0 < orderOf y) hmem
    rw [hy9] at hk
    have h3k : (y ^ k) ^ 3 = 1 := by rw [← hx3, pow_orderOf_eq_one]
    rw [← pow_mul] at h3k
    have hdvd : 9 ∣ k * 3 := by
      have := orderOf_dvd_iff_pow_eq_one.mpr h3k
      rwa [hy9] at this
    interval_cases k
    · simp at hx3
    · omega
    · omega
    · exact hycube
    · omega
    · omega
    · rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]
      rcases hycube with h | h
      · right; rw [h]
      · left; rw [h, ← pow_mul, show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_add, uElem_pow_three, one_mul, pow_one]
    · omega
    · omega
  · intro h3 hxcube
    have hx9 : orderOf x = 9 := (orderOf_eq_nine_iff x).mpr (by
      rcases hxcube with h | h
      · rw [h]; exact uElem_ne_one
      · rw [h]; exact uElem_sq_ne_one)
    have hy9 : orderOf y ≤ 9 := Nat.le_of_dvd (by omega) (orderOf_PGrp_dvd_nine y)
    omega

/-- Every edge of `Γ(TargetG) - cutSet` preserves `branchLabel`. -/
lemma branchLabel_eq_of_adj {g h : TargetG} (hg : g ∉ cutSet) (hh : h ∉ cutSet)
    (hadj : (primeIndexGraph TargetG).Adj g h) : branchLabel g = branchLabel h := by
  have hdir : ∀ u v : TargetG, u ∉ cutSet → v ∉ cutSet → hasPrimeIndexIn u v →
      branchLabel u = branchLabel v := by
    intro u v hu _ huv
    rcases hasPrimeIndexIn_fst_ratio huv with ⟨hsub, heq | h3⟩
    · have hres := (PGrp_branch_step hsub).1 heq
      unfold branchLabel
      simp only [hres.1, hres.2]
    · have hu_not_cut : ¬ (u.1 = uElem ∨ u.1 = uElem ^ 2) := by
        simpa [cutSet] using hu
      have hv_not : ¬ (v.1 ^ 3 = uElem ∨ v.1 ^ 3 = uElem ^ 2) := fun hv =>
        hu_not_cut ((PGrp_branch_step hsub).2.1 h3 hv)
      have hu_not : ¬ (u.1 ^ 3 = uElem ∨ u.1 ^ 3 = uElem ^ 2) :=
        (PGrp_branch_step hsub).2.2 h3
      simp [branchLabel, hu_not, hv_not]
  rcases hadj.2 with h1 | h2
  · exact hdir g h hg hh h1
  · exact (hdir h g hh hg h2).symm

/-- Elementary pigeonhole cut-set bound for any path in a graph:
if `B : V → β` is constant along edges outside `S`, then any path `π : Fin N → V` visits at most
`|{i | π i ∈ S}| + (if last vertex ∉ S then 1 else 0)` distinct `B`-values outside `S`. -/
private lemma path_branch_card_le_aux {V β : Type*} [DecidableEq V] [DecidableEq β]
    (Γ : SimpleGraph V) (S : Finset V) (B : V → β)
    (hB : ∀ u v, u ∉ S → v ∉ S → Γ.Adj u v → B u = B v) :
    ∀ (N : ℕ) (π : Fin N → V),
      (∀ (i : ℕ) (hi : i + 1 < N), Γ.Adj (π ⟨i, by omega⟩) (π ⟨i + 1, hi⟩)) →
      ((Finset.univ.filter fun i : Fin N => π i ∉ S).image (fun i => B (π i))).card ≤
        (Finset.univ.filter fun i : Fin N => π i ∈ S).card +
          if h : 0 < N then (if π ⟨N - 1, by omega⟩ ∉ S then 1 else 0) else 0 := by
  intro N
  induction N with
  | zero =>
    intro _ _
    simp
  | succ N ih =>
    intro π hpath
    let π' : Fin N → V := fun i => π i.castSucc
    have hpath' : ∀ (i : ℕ) (hi : i + 1 < N), Γ.Adj (π' ⟨i, by omega⟩) (π' ⟨i + 1, hi⟩) :=
      fun i hi => hpath i (by omega)
    have hih := ih π' hpath'
    have hsplit_in : (Finset.univ.filter fun i : Fin (N + 1) => π i ∈ S).card =
        (Finset.univ.filter fun i : Fin N => π' i ∈ S).card +
          if π (Fin.last N) ∈ S then 1 else 0 := by
      have hset : (Finset.univ.filter fun i : Fin (N + 1) => π i ∈ S) =
          (if π (Fin.last N) ∈ S then {Fin.last N} else ∅) ∪
            (Finset.univ.filter fun i : Fin N => π' i ∈ S).image Fin.castSucc := by
        ext i
        refine Fin.lastCases ?_ (fun q => ?_) i
        · by_cases hmem : π (Fin.last N) ∈ S <;> simp [hmem, Fin.castSucc_ne_last]
        · by_cases hmem : π (Fin.last N) ∈ S <;>
            simp [hmem, Fin.castSucc_ne_last, π']
      rw [hset, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (Fin.castSucc_injective N)]
      · split_ifs <;> simp [add_comm]
      · rw [Finset.disjoint_left]
        intro x hx hy
        rcases Finset.mem_image.mp hy with ⟨q, _, rfl⟩
        split_ifs at hx
        · rw [Finset.mem_singleton] at hx; exact Fin.castSucc_ne_last q hx
        · simp at hx
    have hset_out : (Finset.univ.filter fun i : Fin (N + 1) => π i ∉ S).image (fun i => B (π i)) =
        (if π (Fin.last N) ∉ S then {B (π (Fin.last N))} else ∅) ∪
          (Finset.univ.filter fun i : Fin N => π' i ∉ S).image (fun i => B (π' i)) := by
      ext b
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro ⟨i, hi, rfl⟩
        refine Fin.lastCases (fun hlast => ?_) (fun q hq => ?_) i hi
        · left; simp [hlast]
        · right; exact ⟨q, hq, rfl⟩
      · rintro (hl | ⟨q, hq, rfl⟩)
        · by_cases hlast : π (Fin.last N) ∈ S
          · simp [hlast] at hl
          · simp only [hlast, not_false_eq_true, ↓reduceIte, Finset.mem_singleton] at hl
            exact ⟨Fin.last N, hlast, hl.symm⟩
        · exact ⟨q.castSucc, hq, rfl⟩
    have hlast_eq : (⟨N + 1 - 1, by omega⟩ : Fin (N + 1)) = Fin.last N := Fin.ext (by simp)
    rw [hset_out, hsplit_in, dif_pos (Nat.succ_pos N), hlast_eq]
    by_cases hlast : π (Fin.last N) ∈ S
    · simp only [hlast, not_true_eq_false, ↓reduceIte, Finset.empty_union, add_zero]
      split_ifs at hih <;> omega
    · simp only [hlast, not_false_eq_true, ↓reduceIte, add_zero]
      cases N with
      | zero => simp
      | succ M =>
        rw [dif_pos (Nat.succ_pos M)] at hih
        have hprev_eq : π' ⟨M + 1 - 1, by omega⟩ = π ⟨M, by omega⟩ := rfl
        rw [hprev_eq] at hih
        by_cases hprev : π ⟨M, by omega⟩ ∈ S
        · simp only [hprev, not_true_eq_false, ↓reduceIte, add_zero] at hih
          have hcard := Finset.card_union_le {B (π (Fin.last (M + 1)))}
            ((Finset.univ.filter fun i : Fin (M + 1) => π' i ∉ S).image (fun i => B (π' i)))
          rw [Finset.card_singleton] at hcard
          omega
        · simp only [hprev, not_false_eq_true, ↓reduceIte] at hih
          have hadj := hpath M (by omega)
          have hBeq : B (π ⟨M, by omega⟩) = B (π (Fin.last (M + 1))) := hB _ _ hprev hlast hadj
          have hmem : B (π (Fin.last (M + 1))) ∈
              (Finset.univ.filter fun i : Fin (M + 1) => π' i ∉ S).image (fun i => B (π' i)) := by
            rw [Finset.mem_image]
            exact ⟨⟨M, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprev⟩, hBeq⟩
          rw [Finset.singleton_union, Finset.insert_eq_of_mem hmem]
          exact hih

private lemma path_branch_card_le {V β : Type*} [DecidableEq V] [DecidableEq β]
    (Γ : SimpleGraph V) (S : Finset V) (B : V → β)
    (hB : ∀ u v, u ∉ S → v ∉ S → Γ.Adj u v → B u = B v)
    (N : ℕ) (π : Fin N → V)
    (hpath : ∀ (i : ℕ) (hi : i + 1 < N), Γ.Adj (π ⟨i, by omega⟩) (π ⟨i + 1, hi⟩)) :
    ((Finset.univ.filter fun i : Fin N => π i ∉ S).image (fun i => B (π i))).card ≤
      (Finset.univ.filter fun i : Fin N => π i ∈ S).card + 1 := by
  have h := path_branch_card_le_aux Γ S B hB N π hpath
  split_ifs at h <;> omega

private lemma no_ham_path_of_branch_cut {V β : Type*} [Fintype V] [DecidableEq V] [DecidableEq β]
    (Γ : SimpleGraph V) (S : Finset V) (B : V → β)
    (hB : ∀ u v, u ∉ S → v ∉ S → Γ.Adj u v → B u = B v)
    (hgt : S.card + 1 < ((Finset.univ \ S).image B).card)
    (N : ℕ) :
    ¬ ∃ π : Fin N ≃ V,
      ∀ (i : ℕ) (hi : i + 1 < N), Γ.Adj (π ⟨i, by omega⟩) (π ⟨i + 1, hi⟩) := by
  rintro ⟨π, hpath⟩
  have hle := path_branch_card_le Γ S B hB N π hpath
  have hin : (Finset.univ.filter fun i : Fin N => π i ∈ S).card = S.card := by
    refine Finset.card_bij (fun i _ => π i) ?_ ?_ ?_
    · intro i hi; exact (Finset.mem_filter.mp hi).2
    · intro i₁ _ i₂ _ hEq; exact π.injective hEq
    · intro v hv; exact ⟨π.symm v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hv⟩, by simp⟩
  have hout : (Finset.univ.filter fun i : Fin N => π i ∉ S).image (fun i => B (π i)) =
      (Finset.univ \ S).image B := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨π i, hi, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨π.symm v, by simpa using hv, by simp⟩
  rw [hin, hout] at hle
  omega

/-- **Main Theorem (Disproof of Manna–Mandal Problem 7.10, Question 2, arXiv:2611.27642v1):**
In `G = PGrp × Z_10 ≅ K × Z_2`, `K = PGrp × Z_5` satisfies `(H1)` for every prime dividing `|K|`
and violates `(H2)` at `C = ⟨u⟩`, and `Γ(G)` has neither a Hamiltonian path nor a Hamiltonian cycle. -/
theorem manna_mandal_problem_7_10_Q2_no_hamiltonian_path :
    ¬ ∃ π : Fin (Fintype.card TargetG) ≃ TargetG,
      ∀ (i : ℕ) (hi : i + 1 < Fintype.card TargetG),
        (primeIndexGraph TargetG).Adj (π ⟨i, by omega⟩) (π ⟨i + 1, hi⟩) :=
  no_ham_path_of_branch_cut (primeIndexGraph TargetG) cutSet branchLabel
    (fun _ _ hu hv hadj => branchLabel_eq_of_adj hu hv hadj)
    (by rw [card_cutSet, card_branchLabel_image]; omega)
    (Fintype.card TargetG)

/-- Corollary: `Γ(TargetG)` has no Hamiltonian cycle either. -/
theorem manna_mandal_problem_7_10_Q2_no_hamiltonian_cycle :
    ¬ ∃ π : Fin (Fintype.card TargetG) ≃ TargetG,
      (∀ (i : ℕ) (hi : i + 1 < Fintype.card TargetG),
        (primeIndexGraph TargetG).Adj (π ⟨i, by omega⟩) (π ⟨i + 1, hi⟩)) ∧
      (primeIndexGraph TargetG).Adj (π ⟨Fintype.card TargetG - 1, by rw [card_TargetG]; omega⟩)
        (π ⟨0, by rw [card_TargetG]; omega⟩) := by
  rintro ⟨π, hpath, _⟩
  exact manna_mandal_problem_7_10_Q2_no_hamiltonian_path ⟨π, hpath⟩

end MannaMandalPrimeIndexGraph
