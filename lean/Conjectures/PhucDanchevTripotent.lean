import Mathlib

/-!
# Complete Resolution of Phuc–Danchev Problem 4.10 (`arXiv:2611.24594v2`)

Reference: D. V. Phuc and P. V. Danchev, "A cubic obstruction to sums of tripotent and
square-zero matrices", arXiv:2611.24594v2 [math.RA] (21 Nov 2026), Section 4, Problem 4.10.

Verbatim Problem 4.10:
> "Determine all integers `d ≥ 7` with `3 ∤ d` for which `M_d(F_2) = T_d`. In particular,
> determine which orders `d = 8n + 4`, with `n ≥ 2` and `n ≢ 1 (mod 3)`, satisfy this equality."

Here `T_d = {T + N ∈ M_d(F_2) : T^3 = T, N^2 = 0}`.

We prove:
1. **Theorem 0 (`no_decomp_of_cubic_zero`):** In any nonzero ring of characteristic 2, no element
   `a` with `a^3 + a^2 + 1 = 0` equals `t + u` with `t^3 = t` and `u^2 = 0`.
2. **Lemma A (`finrank_ker_cubic_le`):** Over any field `F` of characteristic 2, any endomorphism
   `a = t + u` (`t^3 = t`, `u^2 = 0`) of a finite-dimensional `F`-space satisfies
   `finrank F (ker p(a)) ≤ 3 * finrank F (range p(a))`, where `p(x) = x^3 + x^2 + 1`.
3. **Lemma B (`equality_case_B_cubed_eq_sq`):** In the equality case `a = a₁ ⊕ B` on `K × U` with
   `p(a₁) = 0`, `p(B)` invertible, and `finrank F K = 3 * finrank F U`, `a = t + u` forces `B^3 = B^2`.
4. **Main Theorem (`phuc_danchev_problem_4_10`):** For EVERY `d ≥ 7` with `¬ (3 ∣ d)` (and in
   particular every `d = 8 * n + 4` with `n ≥ 1`), there exists `A : Matrix (Fin d) (Fin d) (ZMod 2)`
   not expressible as `T + N` with `T^3 = T` and `N^2 = 0`.
-/

namespace PhucDanchevTripotent

/-! ### Section 1: Characteristic-2 Noncommutative Ring Obstruction (Theorem 0) -/

section Char2Ring

variable {R : Type*} [Ring R]

private lemma add_self_c2 (h2 : (2 : R) = 0) (x : R) : x + x = 0 := by
  calc x + x = (2 : R) * x := (two_mul x).symm
    _ = 0 := by rw [h2, zero_mul]

private lemma eq_of_add_eq_zero_c2 (h2 : (2 : R) = 0) {x y : R} (h : x + y = 0) : x = y := by
  calc x = x + (y + y) := by rw [add_self_c2 h2, add_zero]
    _ = (x + y) + y := by rw [add_assoc]
    _ = y := by rw [h, zero_add]

private lemma add_eq_zero_of_eq_c2 (h2 : (2 : R) = 0) {x y : R} (h : x = y) : x + y = 0 := by
  rw [h, add_self_c2 h2]

private lemma eq_add_of_add_eq_c2 (h2 : (2 : R) = 0) {x y z : R} (h : x = y + z) : y = x + z := by
  calc y = y + (z + z) := by rw [add_self_c2 h2, add_zero]
    _ = (y + z) + z := by rw [add_assoc]
    _ = x + z := by rw [← h]

/-- Fundamental identity `(E1)` in characteristic 2: if `a = t + u` with `t^3 = t` and `u^2 = 0`,
then `a^3 + a + a^2 * u + a * u * a + u * a^2 + u * a * u + u = 0`. -/
lemma eq_E1 (h2 : (2 : R) = 0) {a t u : R} (ha : a = t + u) (ht : t ^ 3 = t) (hu : u ^ 2 = 0) :
    a ^ 3 + a + a ^ 2 * u + a * u * a + u * a ^ 2 + u * a * u + u = 0 := by
  have hta : t = a + u := eq_add_of_add_eq_c2 h2 ha
  have huu : u * u = 0 := by simpa [sq] using hu
  have ht2 : t ^ 2 = a ^ 2 + a * u + u * a := by
    rw [sq, hta, mul_add, add_mul, add_mul, huu, add_zero, ← sq]
    abel
  have ht3 : t ^ 3 = a ^ 3 + a ^ 2 * u + a * u * a + u * a ^ 2 + u * a * u := by
    rw [pow_succ, ht2, hta, mul_add, add_mul, add_mul, add_mul, add_mul]
    rw [mul_assoc a u u, huu, mul_zero, add_zero, ← pow_succ, mul_assoc u a a, ← sq a]
    abel
  have hzero : t ^ 3 + t = 0 := add_eq_zero_of_eq_c2 h2 ht
  rw [ht3, hta] at hzero
  calc a ^ 3 + a + a ^ 2 * u + a * u * a + u * a ^ 2 + u * a * u + u
      = (a ^ 3 + a ^ 2 * u + a * u * a + u * a ^ 2 + u * a * u) + (a + u) := by abel
    _ = 0 := hzero

/-- Right-multiplied identity `(E1u)`: `(a^3 + a) * u + a * u * a * u + u * a^2 * u = 0`. -/
lemma eq_E1u (h2 : (2 : R) = 0) {a t u : R} (ha : a = t + u) (ht : t ^ 3 = t) (hu : u ^ 2 = 0) :
    (a ^ 3 + a) * u + a * u * a * u + u * a ^ 2 * u = 0 := by
  have h1 := congrArg (· * u) (eq_E1 h2 ha ht hu)
  have huu : u * u = 0 := by simpa [sq] using hu
  rw [zero_mul] at h1
  simp only [add_mul, mul_assoc, huu, mul_zero, add_zero] at h1
  rw [add_mul]
  simpa only [mul_assoc, add_assoc] using h1

/-- **Theorem 0 (Phuc–Danchev Theorem 3.1, λ = 1):**
In a nonzero ring of characteristic 2, no element `a` with `a^3 + a^2 + 1 = 0`
can be written as `a = t + u` with `t^3 = t` and `u^2 = 0`. -/
theorem no_decomp_of_cubic_zero [Nontrivial R] (h2 : (2 : R) = 0) {a t u : R}
    (hp : a ^ 3 + a ^ 2 + 1 = 0) (ha : a = t + u) (ht : t ^ 3 = t) (hu : u ^ 2 = 0) : False := by
  have huu : u * u = 0 := by simpa [sq] using hu
  have huu_l : ∀ r : R, u * (u * r) = 0 := fun r => by rw [← mul_assoc, huu, zero_mul]
  have ha3 : a ^ 3 = a ^ 2 + 1 := eq_of_add_eq_zero_c2 h2 (by simpa [add_assoc] using hp)
  have ha4 : a ^ 4 = a ^ 2 + a + 1 := by
    calc a ^ 4 = a * a ^ 3 := by rw [pow_succ']
      _ = a * (a ^ 2 + 1) := by rw [ha3]
      _ = a ^ 3 + a := by rw [mul_add, mul_one, ← pow_succ']
      _ = a ^ 2 + a + 1 := by rw [ha3]; abel
  have hinv : (a ^ 2 + 1) * (a ^ 3 + a) = 1 := by
    calc (a ^ 2 + 1) * (a ^ 3 + a)
        = (a ^ 2 + 1) * (a ^ 2 + a + 1) := by rw [ha3]; abel_nf
      _ = a ^ 4 + a ^ 3 + a ^ 2 + a ^ 2 + a + 1 := by
            rw [add_mul, mul_add, mul_add, one_mul, mul_one, ← pow_add, ← pow_succ]
            abel
      _ = (a ^ 2 + a + 1) + (a ^ 2 + 1) + (a ^ 2 + a ^ 2) + a + 1 := by
            rw [ha4, ha3]; abel
      _ = (a ^ 2 + a ^ 2) + (a + a) + (1 + 1) + (a ^ 2 + a ^ 2) + 1 := by abel
      _ = 1 := by simp only [add_self_c2 h2, zero_add]
  have hE1 := eq_E1 h2 ha ht hu
  have hE1u := eq_E1u h2 ha ht hu
  set X := u * a * u
  set Y := u * a ^ 2 * u
  set Z := u * a * u * a * u
  -- Step 1: `u * (E1) * u = 0` gives `Y = X + Z`.
  have hY : Y = X + Z := by
    have h1 := congrArg (fun r => u * r * u) hE1
    rw [mul_zero, zero_mul] at h1
    simp only [mul_add, add_mul, mul_assoc, huu, huu_l, mul_zero, add_zero] at h1
    have huXu : u * (X * u) = 0 := by dsimp [X]; simp only [mul_assoc, huu, mul_zero]
    have hua3u : u * (a ^ 3 * u) = Y := by
      rw [ha3, add_mul, one_mul, mul_add, huu, add_zero]; dsimp [Y]; rw [mul_assoc]
    rw [hua3u, huXu, add_zero] at h1
    have hXZ : Y + (X + Z) = 0 := by
      dsimp [X, Z]
      calc Y + (u * a * u + u * a * u * a * u)
          = Y + u * (a * u) + u * (a * (u * (a * u))) := by simp only [mul_assoc]; abel
        _ = 0 := h1
    exact eq_of_add_eq_zero_c2 h2 hXZ
  -- Step 2: `S = t^2` satisfies `S^2 + S = 0`, so `u * (S^2 + S) * u = 0`, giving `X = Y*a*u + u*a*Y`.
  have hX : X = Y * a * u + u * a * Y := by
    have hta : t = a + u := eq_add_of_add_eq_c2 h2 ha
    set S := t ^ 2
    have hS : S = a ^ 2 + a * u + u * a := by
      dsimp [S]; rw [sq, hta, mul_add, add_mul, add_mul, huu, add_zero, ← sq]; abel
    have hS2 : S * S + S = 0 := by
      have ht4 : t ^ 4 = t ^ 2 := by
        calc t ^ 4 = t ^ 3 * t := pow_succ t 3
          _ = t * t := by rw [ht]
          _ = t ^ 2 := (sq t).symm
      exact add_eq_zero_of_eq_c2 h2 (by dsimp [S]; rw [← pow_add, show 2 + 2 = 4 from rfl, ht4])
    have huS2 : u * (S * S + S) * u = 0 := by rw [hS2, mul_zero, zero_mul]
    rw [hS] at huS2
    simp only [mul_add, add_mul, mul_assoc, huu, huu_l, mul_zero, add_zero] at huS2
    have hua4u : u * (a ^ 2 * (a ^ 2 * u)) = Y + X := by
      have ha22 : a ^ 2 * (a ^ 2 * u) = a ^ 4 * u := by rw [← mul_assoc, ← pow_add]
      rw [ha22, ha4, add_mul, add_mul, one_mul, mul_add, mul_add, huu, add_zero]
      dsimp [Y, X]; simp only [mul_assoc]
    rw [hua4u] at huS2
    have hrew : X + (Y * a * u + u * a * Y) = 0 := by
      have hYY : Y + Y = 0 := add_self_c2 h2 Y
      have hterm : (Y + X) + u * (a ^ 2 * (u * (a * u))) + u * (a * (u * (a ^ 2 * u))) + u * (a ^ 2 * u) = 0 := by
        calc (Y + X) + u * (a ^ 2 * (u * (a * u))) + u * (a * (u * (a ^ 2 * u))) + u * (a ^ 2 * u)
            = Y + (X + (u * (a * (u * (a ^ 2 * u))) + (u * (a ^ 2 * (u * (a * u))) + u * (a ^ 2 * u)))) := by abel
          _ = 0 := by simpa only [add_assoc] using huS2
      have ht1 : u * (a ^ 2 * (u * (a * u))) = Y * a * u := by dsimp [Y]; simp only [mul_assoc]
      have ht2 : u * (a * (u * (a ^ 2 * u))) = u * a * Y := by dsimp [Y]; simp only [mul_assoc]
      have ht3 : u * (a ^ 2 * u) = Y := by dsimp [Y]; simp only [mul_assoc]
      rw [ht1, ht2, ht3] at hterm
      calc X + (Y * a * u + u * a * Y)
          = (Y + Y) + (X + (Y * a * u + u * a * Y)) := by rw [hYY, zero_add]
        _ = (Y + X) + Y * a * u + u * a * Y + Y := by abel
        _ = 0 := hterm
    exact eq_of_add_eq_zero_c2 h2 hrew
  -- Step 3: `Y * a * u = u * a * Y`, hence `X = 0`, `Z = 0`, `Y = 0`.
  have hYcomm : Y * a * u = u * a * Y := by
    rw [hY, add_mul, add_mul, mul_add]
    dsimp [X, Z]
    simp only [mul_assoc]
  have hX0 : X = 0 := by rw [hX, hYcomm, add_self_c2 h2]
  have hZ0 : Z = 0 := by
    change u * a * u * a * u = 0
    have : u * a * u * a * u = X * a * u := rfl
    rw [this, hX0, zero_mul, zero_mul]
  have hY0 : Y = 0 := by rw [hY, hX0, hZ0, add_zero]
  -- Step 4: `(E1u)` gives `(a^3 + a) * u = 0`, hence `u = 0`, hence `a^3 + a = 0`, hence `1 = 0`.
  have hu0 : u = 0 := by
    have h1 : (a ^ 3 + a) * u = 0 := by
      have : (a ^ 3 + a) * u + a * X + Y = 0 := by
        dsimp [X, Y] at hE1u ⊢
        simp only [mul_assoc] at hE1u ⊢
        exact hE1u
      rwa [hX0, mul_zero, add_zero, hY0, add_zero] at this
    calc u = 1 * u := (one_mul u).symm
      _ = (a ^ 2 + 1) * ((a ^ 3 + a) * u) := by rw [← mul_assoc, hinv]
      _ = 0 := by rw [h1, mul_zero]
  have hat : a = t := by rw [ha, hu0, add_zero]
  have ha3a : a ^ 3 + a = 0 := add_eq_zero_of_eq_c2 h2 (by rw [hat, ht])
  have h10 : (1 : R) = 0 := by rw [← hinv, ha3a, mul_zero]
  exact one_ne_zero h10

end Char2Ring

/-! ### Section 2: Lemma A (Sharp Rank Inequality) -/

section LinearAlgebra

variable {F : Type*} [Field F] [CharP F 2]

private lemma add_self_v (F : Type*) [Field F] [CharP F 2]
    {V : Type*} [AddCommGroup V] [Module F V] (x : V) : x + x = 0 := by
  calc x + x = (1 : F) • x + (1 : F) • x := by rw [one_smul]
    _ = ((1 : F) + 1) • x := (add_smul 1 1 x).symm
    _ = ((2 : ℕ) : F) • x := by norm_num
    _ = 0 := by rw [CharP.cast_eq_zero F 2, zero_smul]

private lemma end_two_eq_zero {V : Type*} [AddCommGroup V] [Module F V] :
    (2 : Module.End F V) = 0 := by
  apply LinearMap.ext; intro x
  rw [show (2 : Module.End F V) = 1 + 1 by norm_num, LinearMap.add_apply]
  exact add_self_v F x

/-- **Lemma A (Sharp rank inequality):**
Over any field `F` of characteristic 2, if `a = t + u ∈ End_F(V)` with `t^3 = t` and `u^2 = 0`,
then `K₁ = {x ∈ ker p(a) | e(u x) = e(u (a x)) = e(u (a^2 x)) = 0} = ⊥`, and therefore
`finrank F (ker p(a)) ≤ 3 * finrank F (range p(a))`. -/
theorem ker_triple_eq_bot {V : Type*} [AddCommGroup V] [Module F V]
    {a t u : Module.End F V} (ha : a = t + u) (ht : t ^ 3 = t) (hu : u ^ 2 = 0) :
    let e : Module.End F V := a ^ 3 + a ^ 2 + 1
    LinearMap.ker e ⊓ LinearMap.ker (e ∘ₗ u) ⊓ LinearMap.ker (e ∘ₗ u ∘ₗ a) ⊓
      LinearMap.ker (e ∘ₗ u ∘ₗ a ^ 2) = ⊥ := by
  intro e
  set K₁ : Submodule F V :=
    LinearMap.ker e ⊓ LinearMap.ker (e ∘ₗ u) ⊓ LinearMap.ker (e ∘ₗ u ∘ₗ a) ⊓
      LinearMap.ker (e ∘ₗ u ∘ₗ a ^ 2)
  have h2V : (2 : Module.End F V) = 0 := end_two_eq_zero
  have he_comm : e * a = a * e := by
    dsimp [e]; noncomm_ring
  have he_app_a : ∀ x : V, e (a x) = a (e x) := fun x =>
    congrArg (fun f : Module.End F V => f x) he_comm
  have hE1 : a ^ 3 + a + a ^ 2 * u + a * u * a + u * a ^ 2 + u * a * u + u = 0 :=
    eq_E1 h2V ha ht hu
  have hE1u : (a ^ 3 + a) * u + a * u * a * u + u * a ^ 2 * u = 0 :=
    eq_E1u h2V ha ht hu
  have hmem_K1 : ∀ x : V, x ∈ K₁ ↔
      e x = 0 ∧ e (u x) = 0 ∧ e (u (a x)) = 0 ∧ e (u ((a ^ 2) x)) = 0 := by
    intro x
    simp only [K₁, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.comp_apply]
    tauto
  have ha_inv : ∀ x ∈ K₁, a x ∈ K₁ := by
    intro x hx
    obtain ⟨h0, h1, h2, h3⟩ := (hmem_K1 x).mp hx
    rw [hmem_K1]
    have ha3x : (a ^ 3) x = (a ^ 2) x + x := by
      have hx0 : (a ^ 3) x + (a ^ 2) x + x = 0 := by
        simpa [e, LinearMap.add_apply] using h0
      have : (a ^ 3) x + ((a ^ 2) x + x) = 0 := by simpa [add_assoc] using hx0
      calc (a ^ 3) x = (a ^ 3) x + (((a ^ 2) x + x) + ((a ^ 2) x + x)) := by
              rw [add_self_v F, add_zero]
        _ = ((a ^ 3) x + ((a ^ 2) x + x)) + ((a ^ 2) x + x) := by abel
        _ = (a ^ 2) x + x := by rw [this, zero_add]
    refine ⟨by rw [he_app_a, h0, map_zero], h2, by simpa [sq] using h3, ?_⟩
    have ha2a : (a ^ 2) (a x) = (a ^ 3) x := by
      change ((a ^ 2) * a) x = (a ^ 3) x; rw [← pow_succ]
    rw [ha2a, ha3x, map_add, map_add, h3, h1, add_zero]
  have hu_inv : ∀ x ∈ K₁, u x ∈ K₁ := by
    intro x hx
    obtain ⟨h0, h1, h2, h3⟩ := (hmem_K1 x).mp hx
    rw [hmem_K1]
    have huu : ∀ y : V, u (u y) = 0 := fun y => by
      have := congrArg (fun f : Module.End F V => f y) hu
      simpa [sq] using this
    have he_a2 : ∀ y, e ((a ^ 2) y) = (a ^ 2) (e y) := fun y => by
      simp only [sq, Module.End.mul_apply, he_app_a]
    have he_a3 : ∀ y, e ((a ^ 3) y) = (a ^ 3) (e y) := fun y => by
      rw [show a ^ 3 = a * (a * a) by rw [pow_succ, sq, mul_assoc]]
      simp only [Module.End.mul_apply, he_app_a]
    have he_uau : e (u (a (u x))) = 0 := by
      have h1x := congrArg (fun f : Module.End F V => e (f x)) hE1
      rw [LinearMap.zero_apply, map_zero] at h1x
      simp only [LinearMap.add_apply, map_add, Module.End.mul_apply,
        he_a3, he_a2, he_app_a, h0, h1, h2, h3, map_zero, zero_add, add_zero] at h1x
      exact h1x
    have he_ua2u : e (u ((a ^ 2) (u x))) = 0 := by
      have h2x := congrArg (fun f : Module.End F V => e (f x)) hE1u
      rw [LinearMap.zero_apply, map_zero] at h2x
      simp only [LinearMap.add_apply, map_add, Module.End.mul_apply,
        he_a3, he_app_a, h1, he_uau, map_zero, zero_add] at h2x
      exact h2x
    exact ⟨h1, by rw [huu, map_zero], he_uau, he_ua2u⟩
  have ht_inv : ∀ x ∈ K₁, t x ∈ K₁ := by
    intro x hx
    have hta : t = a + u := eq_add_of_add_eq_c2 h2V ha
    rw [hta, LinearMap.add_apply]
    exact K₁.add_mem (ha_inv x hx) (hu_inv x hx)
  by_contra hne
  have hnt_K1 : Nontrivial K₁ := by
    rw [nontrivial_iff]
    obtain ⟨x, hx, hx0⟩ : ∃ x ∈ K₁, x ≠ 0 := by
      by_contra hall; push Not at hall
      exact hne ((Submodule.eq_bot_iff K₁).mpr fun x hx => hall x hx)
    exact ⟨⟨x, hx⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩
  have hnt_End : Nontrivial (Module.End F K₁) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : K₁)
    exact ⟨⟨1, 0, fun h => hv (by have := congrArg (fun f : Module.End F K₁ => f v) h; simpa using this)⟩⟩
  let aR : Module.End F K₁ := a.restrict ha_inv
  let tR : Module.End F K₁ := t.restrict ht_inv
  let uR : Module.End F K₁ := u.restrict hu_inv
  have hpow_restrict : ∀ (f : Module.End F V) (hf : ∀ x ∈ K₁, f x ∈ K₁) (k : ℕ) (v : K₁),
      ((f.restrict hf ^ k) v).1 = (f ^ k) v.1 := by
    intro f hf k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
        intro v
        rw [pow_succ', pow_succ']
        change f ((f.restrict hf ^ k) v).1 = f ((f ^ k) v.1)
        rw [ih v]
  have hpR : aR ^ 3 + aR ^ 2 + 1 = 0 := by
    apply LinearMap.ext; intro v
    apply Subtype.ext
    have h0 := ((hmem_K1 v.1).mp v.2).1
    change ((aR ^ 3) v).1 + ((aR ^ 2) v).1 + v.1 = 0
    rw [hpow_restrict a ha_inv 3 v, hpow_restrict a ha_inv 2 v]
    simpa [e, LinearMap.add_apply] using h0
  have haR : aR = tR + uR := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    exact congrArg (fun f : Module.End F V => f v.1) ha
  have htR : tR ^ 3 = tR := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    change ((tR ^ 3) v).1 = t v.1
    rw [hpow_restrict t ht_inv 3 v]
    exact congrArg (fun f : Module.End F V => f v.1) ht
  have huR : uR ^ 2 = 0 := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    change ((uR ^ 2) v).1 = 0
    rw [hpow_restrict u hu_inv 2 v]
    exact congrArg (fun f : Module.End F V => f v.1) hu
  exact no_decomp_of_cubic_zero end_two_eq_zero hpR haR htR huR

theorem finrank_ker_cubic_le {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {a t u : Module.End F V} (ha : a = t + u) (ht : t ^ 3 = t) (hu : u ^ 2 = 0) :
    let e : Module.End F V := a ^ 3 + a ^ 2 + 1
    Module.finrank F (LinearMap.ker e) ≤ 3 * Module.finrank F (LinearMap.range e) := by
  intro e
  let Ψ : LinearMap.ker e →ₗ[F] (LinearMap.range e × LinearMap.range e × LinearMap.range e) :=
    { toFun := fun x =>
        (⟨e (u x.1), LinearMap.mem_range_self e _⟩,
         ⟨e (u (a x.1)), LinearMap.mem_range_self e _⟩,
         ⟨e (u ((a ^ 2) x.1)), LinearMap.mem_range_self e _⟩)
      map_add' := fun x y => by ext <;> simp
      map_smul' := fun r x => by ext <;> simp }
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h1 : e (u x.1) = 0 := congrArg (fun p => p.1.1) hx
    have h2 : e (u (a x.1)) = 0 := congrArg (fun p => p.2.1.1) hx
    have h3 : e (u ((a ^ 2) x.1)) = 0 := congrArg (fun p => p.2.2.1) hx
    have hbot := ker_triple_eq_bot ha ht hu
    have hmem : x.1 ∈ (⊥ : Submodule F V) := by
      rw [← hbot]
      refine ⟨⟨⟨x.2, h1⟩, h2⟩, h3⟩
    exact Subtype.ext (by simpa using hmem)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, Module.finrank_prod] at hle
  omega

/-! ### Section 3: Lemma B (Equality-Case Rigidity) -/

/-- **Lemma B (Equality-case rigidity):**
Let `a = a₁ ⊕ B` on `K × U` over a field `F` of characteristic 2 with `a₁^3 + a₁^2 + 1 = 0`,
`B^3 + B^2 + 1` invertible, and `finrank F K = 3 * finrank F U`.
If `a = t + u` with `t^3 = t` and `u^2 = 0`, then `B^3 = B^2`. -/
theorem equality_case_B_cubed_eq_sq
    {K U : Type*} [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    {a₁ : Module.End F K} {B : Module.End F U}
    (ha₁ : a₁ ^ 3 + a₁ ^ 2 + 1 = 0)
    (_hB_unit : IsUnit (B ^ 3 + B ^ 2 + 1))
    (hdim : Module.finrank F K = 3 * Module.finrank F U)
    {t u : Module.End F (K × U)}
    (ha : LinearMap.prodMap a₁ B = t + u)
    (ht : t ^ 3 = t) (hu : u ^ 2 = 0) :
    B ^ 3 = B ^ 2 := by
  set a : Module.End F (K × U) := LinearMap.prodMap a₁ B
  set e : Module.End F (K × U) := a ^ 3 + a ^ 2 + 1
  set eB : Module.End F U := B ^ 3 + B ^ 2 + 1
  have ha_pow : ∀ (k : ℕ) (x : K) (y : U), (a ^ k) (x, y) = ((a₁ ^ k) x, (B ^ k) y) := by
    intro k
    induction k with
    | zero => intro x y; rfl
    | succ k ih =>
        intro x y
        rw [pow_succ', pow_succ', pow_succ']
        change a ((a ^ k) (x, y)) = (a₁ ((a₁ ^ k) x), B ((B ^ k) y))
        rw [ih x y]
        rfl
  have he_apply : ∀ (x : K) (y : U), e (x, y) = (0, eB y) := by
    intro x y
    change (a ^ 3) (x, y) + (a ^ 2) (x, y) + (x, y) = (0, eB y)
    rw [ha_pow 3, ha_pow 2]
    apply Prod.ext
    · change (a₁ ^ 3 + a₁ ^ 2 + 1 : Module.End F K) x = 0; rw [ha₁, LinearMap.zero_apply]
    · rfl
  -- Extract the four block maps of `u` on `K × U`.
  let u₁₁ : Module.End F K := LinearMap.fst F K U ∘ₗ u ∘ₗ LinearMap.inl F K U
  let u₁₂ : U →ₗ[F] K := LinearMap.fst F K U ∘ₗ u ∘ₗ LinearMap.inr F K U
  let u₂₁ : K →ₗ[F] U := LinearMap.snd F K U ∘ₗ u ∘ₗ LinearMap.inl F K U
  let c : Module.End F U := LinearMap.snd F K U ∘ₗ u ∘ₗ LinearMap.inr F K U
  have hu_apply : ∀ (x : K) (y : U), u (x, y) = (u₁₁ x + u₁₂ y, u₂₁ x + c y) := by
    intro x y
    have hxy : (x, y) = LinearMap.inl F K U x + LinearMap.inr F K U y := by
      apply Prod.ext <;> simp
    rw [hxy, map_add]
    apply Prod.ext <;> rfl
  -- Build the isomorphism `Φ : K ≃ₗ[F] U × U × U`, `x ↦ (u₂₁ x, u₂₁ (a₁ x), u₂₁ (a₁^2 x))`.
  let Φ_lin : K →ₗ[F] (U × U × U) :=
    { toFun := fun x => (u₂₁ x, u₂₁ (a₁ x), u₂₁ ((a₁ ^ 2) x))
      map_add' := fun x y => Prod.ext (by simp) (Prod.ext (by simp) (by simp))
      map_smul' := fun r x => Prod.ext (by simp) (Prod.ext (by simp) (by simp)) }
  have hΦ_inj : Function.Injective Φ_lin := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h1 : u₂₁ x = 0 := congrArg Prod.fst hx
    have h2 : u₂₁ (a₁ x) = 0 := congrArg (fun p => p.2.1) hx
    have h3 : u₂₁ ((a₁ ^ 2) x) = 0 := congrArg (fun p => p.2.2) hx
    have hbot := ker_triple_eq_bot ha ht hu
    have hmem : (x, (0 : U)) ∈ (⊥ : Submodule F (K × U)) := by
      rw [← hbot]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · change e (x, 0) = 0; rw [he_apply, map_zero]; rfl
      · change e (u (x, 0)) = 0; rw [hu_apply x 0, map_zero, map_zero, add_zero, add_zero, he_apply, h1, map_zero]; rfl
      · change e (u (a (x, 0))) = 0
        have : a (x, 0) = (a₁ x, 0) := by change (a₁ x, B 0) = _; rw [map_zero]
        rw [this, hu_apply (a₁ x) 0, map_zero, map_zero, add_zero, add_zero, he_apply, h2, map_zero]; rfl
      · change e (u ((a ^ 2) (x, 0))) = 0
        rw [ha_pow 2, map_zero, hu_apply ((a₁ ^ 2) x) 0, map_zero, map_zero, add_zero, add_zero, he_apply, h3, map_zero]; rfl
    have hzero : (x, (0 : U)) = 0 := by simpa using hmem
    exact congrArg Prod.fst hzero
  have hΦ_bij : Function.Bijective Φ_lin := by
    refine ⟨hΦ_inj, ?_⟩
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hΦ_inj
    · rw [hdim, Module.finrank_prod, Module.finrank_prod]; omega
  let Φ : K ≃ₗ[F] (U × U × U) := LinearEquiv.ofBijective Φ_lin hΦ_bij
  -- Transport `a₁` and `u₁₁` via `Φ`.
  let M : Module.End F (U × U × U) := Φ.toLinearMap ∘ₗ a₁ ∘ₗ Φ.symm.toLinearMap
  let N : Module.End F (U × U × U) := Φ.toLinearMap ∘ₗ u₁₁ ∘ₗ Φ.symm.toLinearMap
  have hM_apply : ∀ x y z : U, M (x, y, z) = (y, z, x + z) := by
    intro x y z
    set k := Φ.symm (x, y, z)
    have hk : Φ k = (x, y, z) := Φ.apply_symm_apply (x, y, z)
    have hx : u₂₁ k = x := congrArg Prod.fst hk
    have hy : u₂₁ (a₁ k) = y := congrArg (fun p => p.2.1) hk
    have hz : u₂₁ ((a₁ ^ 2) k) = z := congrArg (fun p => p.2.2) hk
    have ha3k : (a₁ ^ 3) k = (a₁ ^ 2) k + k := by
      have h0 : (a₁ ^ 3 + a₁ ^ 2 + 1 : Module.End F K) k = 0 := by rw [ha₁]; rfl
      have h0' : (a₁ ^ 3) k + ((a₁ ^ 2) k + k) = 0 := by simpa [LinearMap.add_apply, add_assoc] using h0
      calc (a₁ ^ 3) k = (a₁ ^ 3) k + (((a₁ ^ 2) k + k) + ((a₁ ^ 2) k + k)) := by
              rw [add_self_v F, add_zero]
        _ = ((a₁ ^ 3) k + ((a₁ ^ 2) k + k)) + ((a₁ ^ 2) k + k) := by abel
        _ = (a₁ ^ 2) k + k := by rw [h0', zero_add]
    change (u₂₁ (a₁ k), u₂₁ (a₁ (a₁ k)), u₂₁ ((a₁ ^ 2) (a₁ k))) = (y, z, x + z)
    have h2 : a₁ (a₁ k) = (a₁ ^ 2) k := rfl
    have h3 : (a₁ ^ 2) (a₁ k) = (a₁ ^ 3) k := by change ((a₁ ^ 2) * a₁) k = _; rw [← pow_succ]
    rw [h2, h3, ha3k, map_add, hx, hy, hz, add_comm]
  have hu21_symm : ∀ x y z : U, u₂₁ (Φ.symm (x, y, z)) = x := fun x y z =>
    congrArg Prod.fst (Φ.apply_symm_apply (x, y, z))
  -- Block equations from `u^2 = 0`:
  have hu2_UK : ∀ k : K, u₂₁ (u₁₁ k) = c (u₂₁ k) := by
    intro k
    have h0 := congrArg (fun f : Module.End F (K × U) => (f (k, 0)).2) hu
    change (u (u (k, 0))).2 = 0 at h0
    rw [hu_apply k 0, map_zero, map_zero, add_zero, add_zero, hu_apply (u₁₁ k) (u₂₁ k)] at h0
    dsimp only at h0
    calc u₂₁ (u₁₁ k) = u₂₁ (u₁₁ k) + (c (u₂₁ k) + c (u₂₁ k)) := by rw [add_self_v F, add_zero]
      _ = (u₂₁ (u₁₁ k) + c (u₂₁ k)) + c (u₂₁ k) := by rw [add_assoc]
      _ = c (u₂₁ k) := by rw [h0, zero_add]
  have hu2_UU : ∀ w : U, u₂₁ (u₁₂ w) = (c ^ 2) w := by
    intro w
    have h0 := congrArg (fun f : Module.End F (K × U) => (f (0, w)).2) hu
    change (u (u (0, w))).2 = 0 at h0
    rw [hu_apply 0 w, map_zero, map_zero, zero_add, zero_add, hu_apply (u₁₂ w) (c w)] at h0
    dsimp only at h0
    change u₂₁ (u₁₂ w) = c (c w)
    calc u₂₁ (u₁₂ w) = u₂₁ (u₁₂ w) + (c (c w) + c (c w)) := by rw [add_self_v F, add_zero]
      _ = (u₂₁ (u₁₂ w) + c (c w)) + c (c w) := by rw [add_assoc]
      _ = c (c w) := by rw [h0, zero_add]
  -- Block equations from `(E1)`:
  have hE1 := eq_E1 end_two_eq_zero ha ht hu
  -- Row 1 of `N`:
  have hN1 : ∀ x y z : U, (N (x, y, z)).1 = c x := by
    intro x y z
    change u₂₁ (u₁₁ (Φ.symm (x, y, z))) = c x
    rw [hu2_UK, hu21_symm]
  -- Row 2 of `N`: from `UK`-block of `(E1)` at `(k, 0)`:
  have hN2 : ∀ x y z : U, (N (x, y, z)).2.1 = (B ^ 2) x + c (B x) + x + B y + z := by
    intro x y z
    set k := Φ.symm (x, y, z)
    have hE1_snd := congrArg (fun f : Module.End F (K × U) => (f (k, 0)).2) hE1
    rw [LinearMap.zero_apply] at hE1_snd
    have hk : Φ k = (x, y, z) := Φ.apply_symm_apply (x, y, z)
    have hx : u₂₁ k = x := congrArg Prod.fst hk
    have hy : u₂₁ (a₁ k) = y := congrArg (fun p => p.2.1) hk
    have hz : u₂₁ ((a₁ ^ 2) k) = z := congrArg (fun p => p.2.2) hk
    have hstep : (B ^ 2) x + B y + z + u₂₁ (a₁ (u₁₁ k)) + c (B x) + x = 0 := by
      have hterm : ((a ^ 3) (k, 0)).2 + (a (k, 0)).2 + ((a ^ 2) (u (k, 0))).2 +
          (a (u (a (k, 0)))).2 + (u ((a ^ 2) (k, 0))).2 + (u (a (u (k, 0)))).2 + (u (k, 0)).2 = 0 := by
        simpa [LinearMap.add_apply, Module.End.mul_apply] using hE1_snd
      have ha_k : a (k, 0) = (a₁ k, 0) := by change (a₁ k, B 0) = _; rw [map_zero]
      have ha2_k : (a ^ 2) (k, 0) = ((a₁ ^ 2) k, 0) := by rw [ha_pow 2, map_zero]
      have ha3_k : (a ^ 3) (k, 0) = ((a₁ ^ 3) k, 0) := by rw [ha_pow 3, map_zero]
      have hu_k : u (k, 0) = (u₁₁ k, x) := by rw [hu_apply k 0, map_zero, map_zero, add_zero, add_zero, hx]
      have hu_ak : u (a (k, 0)) = (u₁₁ (a₁ k), y) := by
        rw [ha_k, hu_apply (a₁ k) 0, map_zero, map_zero, add_zero, add_zero, hy]
      have ha_uk : a (u (k, 0)) = (a₁ (u₁₁ k), B x) := by rw [hu_k]; rfl
      rw [ha3_k, hu_ak, ha_k, ha_uk, hu_k, ha_pow 2, ha2_k,
        hu_apply ((a₁ ^ 2) k) 0, hu_apply (a₁ (u₁₁ k)) (B x)] at hterm
      dsimp only at hterm
      rw [add_zero, hz, map_zero, add_zero] at hterm
      change 0 + (B ^ 2) x + B y + z + (u₂₁ (a₁ (u₁₁ k)) + c (B x)) + x = 0 at hterm
      simpa only [zero_add, add_assoc] using hterm
    change u₂₁ (a₁ (u₁₁ k)) = (B ^ 2) x + c (B x) + x + B y + z
    have hsum : u₂₁ (a₁ (u₁₁ k)) + ((B ^ 2) x + c (B x) + x + B y + z) = 0 := by
      have : u₂₁ (a₁ (u₁₁ k)) + ((B ^ 2) x + c (B x) + x + B y + z) =
          (B ^ 2) x + B y + z + u₂₁ (a₁ (u₁₁ k)) + c (B x) + x := by abel
      rw [this, hstep]
    calc u₂₁ (a₁ (u₁₁ k))
        = u₂₁ (a₁ (u₁₁ k)) + (((B ^ 2) x + c (B x) + x + B y + z) + ((B ^ 2) x + c (B x) + x + B y + z)) := by
            rw [add_self_v F, add_zero]
      _ = (u₂₁ (a₁ (u₁₁ k)) + ((B ^ 2) x + c (B x) + x + B y + z)) + ((B ^ 2) x + c (B x) + x + B y + z) := by
            abel
      _ = (B ^ 2) x + c (B x) + x + B y + z := by rw [hsum, zero_add]
  -- `KK`-block of `(E1)` conjugated by `Φ`:
  have hKK : ∀ p : U × U × U,
      (M ^ 3) p + M p + (M ^ 2) (N p) + M (N (M p)) + N ((M ^ 2) p) + N (M (N p)) +
        Φ (u₁₂ (B p.1)) + N p = 0 := by
    intro p
    set k := Φ.symm p
    have hp : Φ k = p := Φ.apply_symm_apply p
    have hx : u₂₁ k = p.1 := congrArg Prod.fst hp
    have hE1_fst := congrArg (fun f : Module.End F (K × U) => (f (k, 0)).1) hE1
    rw [LinearMap.zero_apply] at hE1_fst
    have hterm : ((a ^ 3) (k, 0)).1 + (a (k, 0)).1 + ((a ^ 2) (u (k, 0))).1 +
        (a (u (a (k, 0)))).1 + (u ((a ^ 2) (k, 0))).1 + (u (a (u (k, 0)))).1 + (u (k, 0)).1 = 0 := by
      simpa [LinearMap.add_apply, Module.End.mul_apply] using hE1_fst
    have ha_k : a (k, 0) = (a₁ k, 0) := by change (a₁ k, B 0) = _; rw [map_zero]
    have ha2_k : (a ^ 2) (k, 0) = ((a₁ ^ 2) k, 0) := by rw [ha_pow 2, map_zero]
    have ha3_k : (a ^ 3) (k, 0) = ((a₁ ^ 3) k, 0) := by rw [ha_pow 3, map_zero]
    have hu_k : u (k, 0) = (u₁₁ k, p.1) := by rw [hu_apply k 0, map_zero, map_zero, add_zero, add_zero, hx]
    have hu_ak : u (a (k, 0)) = (u₁₁ (a₁ k), u₂₁ (a₁ k)) := by
      rw [ha_k, hu_apply (a₁ k) 0, map_zero, map_zero, add_zero, add_zero]
    have ha_uk : a (u (k, 0)) = (a₁ (u₁₁ k), B p.1) := by rw [hu_k]; rfl
    rw [ha3_k, hu_ak, ha_k, ha_uk, hu_k, ha_pow 2, ha2_k,
      hu_apply ((a₁ ^ 2) k) 0, hu_apply (a₁ (u₁₁ k)) (B p.1)] at hterm
    dsimp only at hterm
    rw [map_zero, add_zero] at hterm
    change (a₁ ^ 3) k + a₁ k + (a₁ ^ 2) (u₁₁ k) + a₁ (u₁₁ (a₁ k)) +
        u₁₁ ((a₁ ^ 2) k) + (u₁₁ (a₁ (u₁₁ k)) + u₁₂ (B p.1)) + u₁₁ k = 0 at hterm
    have hK_eq : (a₁ ^ 3) k + a₁ k + (a₁ ^ 2) (u₁₁ k) + a₁ (u₁₁ (a₁ k)) +
        u₁₁ ((a₁ ^ 2) k) + u₁₁ (a₁ (u₁₁ k)) + u₁₂ (B p.1) + u₁₁ k = 0 := by
      simpa only [add_assoc] using hterm
    have hΦ_eq := congrArg Φ hK_eq
    rw [map_zero] at hΦ_eq
    simp only [map_add] at hΦ_eq
    have hM_eq : ∀ q : K, Φ (a₁ q) = M (Φ q) := fun q => by
      dsimp [M]; simp
    have hN_eq : ∀ q : K, Φ (u₁₁ q) = N (Φ q) := fun q => by
      dsimp [N]; simp
    have hM2_eq : ∀ q : K, Φ ((a₁ ^ 2) q) = (M ^ 2) (Φ q) := fun q => by
      change Φ (a₁ (a₁ q)) = M (M (Φ q)); rw [hM_eq, hM_eq]
    have hM3_eq : ∀ q : K, Φ ((a₁ ^ 3) q) = (M ^ 3) (Φ q) := fun q => by
      rw [show a₁ ^ 3 = a₁ * a₁ ^ 2 by rw [pow_succ'], show M ^ 3 = M * M ^ 2 by rw [pow_succ']]
      change Φ (a₁ ((a₁ ^ 2) q)) = M ((M ^ 2) (Φ q)); rw [hM_eq, hM2_eq]
    rw [hM3_eq, hM_eq, hM2_eq, hN_eq, hM_eq, hN_eq, hM_eq, hN_eq, hM2_eq, hN_eq, hM_eq, hN_eq,
      hp] at hΦ_eq
    exact hΦ_eq
  -- Helper formulas for `M^2` and `M^3`:
  have hM2_apply : ∀ x y z : U, (M ^ 2) (x, y, z) = (z, x + z, y + x + z) := fun x y z => by
    change M (M (x, y, z)) = _
    rw [hM_apply, hM_apply]
    exact Prod.ext rfl (Prod.ext rfl (add_assoc y x z).symm)
  have hM3_apply : ∀ x y z : U, (M ^ 3) (x, y, z) = (x + z, y + x + z, z + y + x + z) := fun x y z => by
    rw [show M ^ 3 = M * (M ^ 2) by rw [pow_succ']]
    change M ((M ^ 2) (x, y, z)) = _
    rw [hM2_apply, hM_apply]
    exact Prod.ext rfl (Prod.ext rfl (by abel))
  -- Row 3 of `N`: from the 1st coordinate of `hKK (x, y, z)`:
  have hN3 : ∀ x y z : U, (N (x, y, z)).2.2 = c ((B ^ 2) x) + (B ^ 2) y + B z := by
    intro x y z
    have h1 := congrArg Prod.fst (hKK (x, y, z))
    dsimp only [Prod.fst_add, Prod.fst_zero] at h1
    have hM2N : ((M ^ 2) (N (x, y, z))).1 = (N (x, y, z)).2.2 := by
      rcases hN : N (x, y, z) with ⟨n1, n2, n3⟩; rw [hM2_apply]
    have hMNM : (M (N (M (x, y, z)))).1 = (N (y, z, x + z)).2.1 := by
      rw [hM_apply x y z]
      rcases hN : N (y, z, x + z) with ⟨n1, n2, n3⟩
      rw [hM_apply]
    have hNM2 : (N ((M ^ 2) (x, y, z))).1 = c z := by
      rw [hM2_apply, hN1]
    have hNMN : (N (M (N (x, y, z)))).1 = c ((N (x, y, z)).2.1) := by
      rcases hN : N (x, y, z) with ⟨n1, n2, n3⟩; rw [hM_apply, hN1]
    have hu12_1 : (Φ (u₁₂ (B x))).1 = (c ^ 2) (B x) := hu2_UU (B x)
    rw [hM3_apply, hM2N, hMNM, hNM2, hNMN, hM_apply, hu12_1, hN1, hN2, hN2] at h1
    dsimp only at h1
    simp only [map_add] at h1
    have hc2B : (c ^ 2) (B x) = c (c (B x)) := rfl
    rw [hc2B] at h1
    have hclean : (N (x, y, z)).2.2 + (c ((B ^ 2) x) + (B ^ 2) y + B z) = 0 := by
      have hcancel : (x + z) + y + (N (x, y, z)).2.2 + ((B ^ 2) y + c (B y) + y + B z + (x + z)) +
          c z + (c ((B ^ 2) x) + c (c (B x)) + c x + c (B y) + c z) + c (c (B x)) + c x =
          (N (x, y, z)).2.2 + (c ((B ^ 2) x) + (B ^ 2) y + B z) +
          (((x + z) + (x + z)) + (y + y) + (c (B y) + c (B y)) + (c z + c z) +
            (c (c (B x)) + c (c (B x))) + (c x + c x)) := by abel
      rw [hcancel] at h1
      simpa only [add_self_v F, add_zero] using h1
    calc (N (x, y, z)).2.2
        = (N (x, y, z)).2.2 + ((c ((B ^ 2) x) + (B ^ 2) y + B z) + (c ((B ^ 2) x) + (B ^ 2) y + B z)) := by
            rw [add_self_v F, add_zero]
      _ = ((N (x, y, z)).2.2 + (c ((B ^ 2) x) + (B ^ 2) y + B z)) + (c ((B ^ 2) x) + (B ^ 2) y + B z) := by
            abel
      _ = c ((B ^ 2) x) + (B ^ 2) y + B z := by rw [hclean, zero_add]
  -- Finally, evaluate the 3rd coordinate of `hKK (0, 0, w)` to obtain `B^3 w = B^2 w`!
  apply LinearMap.ext; intro w
  have h3 := congrArg (fun p : U × U × U => p.2.2) (hKK (0, 0, w))
  dsimp only [Prod.snd_add, Prod.snd_zero] at h3
  have hN00w : N (0, 0, w) = (0, w, B w) := by
    apply Prod.ext
    · rw [hN1, map_zero]
    apply Prod.ext
    · rw [hN2]; simp
    · rw [hN3]; simp
  have hM2N : ((M ^ 2) (N (0, 0, w))).2.2 = w + B w := by
    rw [hN00w, hM2_apply]; simp
  have hMNM : (M (N (M (0, 0, w)))).2.2 = (B ^ 2) w + B w := by
    rw [hM_apply 0 0 w, zero_add]
    have hN0ww : N (0, w, w) = (0, B w + w, (B ^ 2) w + B w) := by
      apply Prod.ext
      · rw [hN1, map_zero]
      apply Prod.ext
      · rw [hN2]; simp
      · rw [hN3]; simp
    rw [hN0ww, hM_apply]; simp
  have hNM2 : (N ((M ^ 2) (0, 0, w))).2.2 = c ((B ^ 2) w) + (B ^ 2) w + B w := by
    rw [hM2_apply]; simp [hN3]
  have hNMN : (N (M (N (0, 0, w)))).2.2 = c ((B ^ 2) w) + (B ^ 2) (B w) + B (B w) := by
    rw [hN00w, hM_apply, zero_add, hN3]
  have hu12_0 : (Φ (u₁₂ (B 0))).2.2 = 0 := by simp
  have hM3_00w : ((M ^ 3) (0, 0, w)).2.2 = 0 := by
    rw [hM3_apply]; simp; exact add_self_v F w
  have hM_00w : (M (0, 0, w)).2.2 = w := by
    rw [hM_apply]; simp
  rw [hM3_00w, hM2N, hMNM, hNM2, hNMN, hM_00w, hu12_0, hN00w] at h3
  dsimp only at h3
  have hB3_app : (B ^ 2) (B w) = (B ^ 3) w := by
    change ((B ^ 2) * B) w = _; rw [← pow_succ]
  have hB2_app : B (B w) = (B ^ 2) w := rfl
  rw [hB3_app, hB2_app] at h3
  have hsum : (B ^ 3) w + (B ^ 2) w = 0 := by
    have hcancel : 0 + w + (w + B w) + ((B ^ 2) w + B w) + (c ((B ^ 2) w) + (B ^ 2) w + B w) +
        (c ((B ^ 2) w) + (B ^ 3) w + (B ^ 2) w) + 0 + B w =
        ((B ^ 3) w + (B ^ 2) w) + ((w + w) + (B w + B w) + (B w + B w) +
          ((B ^ 2) w + (B ^ 2) w) + (c ((B ^ 2) w) + c ((B ^ 2) w))) := by abel
    rw [hcancel] at h3
    simpa only [add_self_v F, add_zero] using h3
  calc (B ^ 3) w = (B ^ 3) w + ((B ^ 2) w + (B ^ 2) w) := by rw [add_self_v F, add_zero]
    _ = ((B ^ 3) w + (B ^ 2) w) + (B ^ 2) w := by rw [add_assoc]
    _ = (B ^ 2) w := by rw [hsum, zero_add]

end LinearAlgebra

/-! ### Section 4: Explicit Matrix Witnesses & Complete Resolution of Problem 4.10 -/

/-- A matrix `A ∈ M_d(F_2)` lies in `T_d` if `A = T + N` with `T^3 = T` and `N^2 = 0`. -/
def isTripotentPlusSqZero {d : ℕ} (A : Matrix (Fin d) (Fin d) (ZMod 2)) : Prop :=
  ∃ T N : Matrix (Fin d) (Fin d) (ZMod 2), T ^ 3 = T ∧ N ^ 2 = 0 ∧ A = T + N

/-- The companion matrix `C` of `p(x) = x^3 + x^2 + 1` over `ZMod 2`. -/
def matC : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 1]

/-- The `2 × 2` matrix `B = !![0, 1; 1, 1]` with `B^3 = I_2 ≠ B^2` and `p(B) = B^2` invertible. -/
def matB : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![0, 1; 1, 1]

private lemma matC_cubic : matC ^ 3 + matC ^ 2 + 1 = 0 := by decide
private lemma matB_cubed_ne_sq : matB ^ 3 ≠ matB ^ 2 := by decide
private lemma matB_p_mul_B : (matB ^ 3 + matB ^ 2 + 1) * matB = 1 := by decide
private lemma matB_B_mul_p : matB * (matB ^ 3 + matB ^ 2 + 1) = 1 := by decide

private lemma toLin'_pow {d : ℕ} (A : Matrix (Fin d) (Fin d) (ZMod 2)) (k : ℕ) :
    Matrix.toLin' (A ^ k) = (Matrix.toLin' A) ^ k := by
  induction k with
  | zero => exact Matrix.toLin'_one
  | succ k ih => rw [pow_succ, pow_succ, Matrix.toLin'_mul, ih]; rfl

/-- Transfer `isTripotentPlusSqZero` from `Matrix` to `Module.End (ZMod 2) (Fin d → ZMod 2)`. -/
private lemma toLin'_decomp {d : ℕ} {A : Matrix (Fin d) (Fin d) (ZMod 2)}
    (h : isTripotentPlusSqZero A) :
    ∃ t u : Module.End (ZMod 2) (Fin d → ZMod 2),
      t ^ 3 = t ∧ u ^ 2 = 0 ∧ Matrix.toLin' A = t + u := by
  rcases h with ⟨T, N, hT, hN, rfl⟩
  refine ⟨Matrix.toLin' T, Matrix.toLin' N, ?_, ?_, by rw [map_add]⟩
  · rw [← toLin'_pow, hT]
  · rw [← toLin'_pow, hN, map_zero]

/-- Block-diagonal witness `C^⊕m ⊕ 0_r` on `Fin (3 * m + r)` (`r ∈ {1, 2}`). -/
def witnessFamily (m r : ℕ) : Matrix (Fin (3 * m + r)) (Fin (3 * m + r)) (ZMod 2) :=
  fun i j =>
    if i.val < 3 * m then
      if j.val < 3 * m then
        if i.val / 3 = j.val / 3 then matC ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ ⟨j.val % 3, Nat.mod_lt _ (by omega)⟩
        else 0
      else 0
    else 0

private lemma witnessFamily_mulVec (m r : ℕ) (v : Fin (3 * m + r) → ZMod 2) :
    let A := witnessFamily m r
    (∀ (b : ℕ) (hb : b < m) (c : Fin 3),
      (A.mulVec v) ⟨3 * b + c.val, by omega⟩ =
        (matC.mulVec (fun k : Fin 3 => v ⟨3 * b + k.val, by omega⟩)) c) ∧
    (∀ (q : ℕ) (hq : q < r), (A.mulVec v) ⟨3 * m + q, by omega⟩ = 0) := by
  intro A
  constructor
  · intro b hb c
    simp only [Matrix.mulVec, dotProduct]
    have hsplit : ∑ j : Fin (3 * m + r), A ⟨3 * b + c.val, by omega⟩ j * v j =
        ∑ k : Fin 3, matC c k * v ⟨3 * b + k.val, by omega⟩ := by
      have hsub : ∀ j : Fin (3 * m + r),
          A ⟨3 * b + c.val, by omega⟩ j * v j ≠ 0 →
            j ∈ (Finset.univ : Finset (Fin 3)).image (fun k : Fin 3 => (⟨3 * b + k.val, by omega⟩ : Fin (3 * m + r))) := by
        intro j hj
        by_contra hnot
        apply hj
        have hzero : A ⟨3 * b + c.val, by omega⟩ j = 0 := by
          dsimp [A, witnessFamily]
          have hlt1 : 3 * b + c.val < 3 * m := by have := c.isLt; omega
          rw [if_pos hlt1]
          by_cases hlt2 : j.val < 3 * m
          · rw [if_pos hlt2]
            have hdiv_ne : (3 * b + c.val) / 3 ≠ j.val / 3 := by
              intro hdiv
              have hdiv1 : (3 * b + c.val) / 3 = b := by have := c.isLt; omega
              rw [hdiv1] at hdiv
              apply hnot
              rw [Finset.mem_image]
              refine ⟨⟨j.val % 3, Nat.mod_lt _ (by omega)⟩, Finset.mem_univ _, Fin.ext ?_⟩
              dsimp only; omega
            rw [if_neg hdiv_ne]
          · rw [if_neg hlt2]
        rw [hzero, zero_mul]
      rw [← Finset.sum_subset (Finset.subset_univ _) (fun j _ hnot => by
        by_contra hne; exact hnot (hsub j hne))]
      rw [Finset.sum_image (fun k₁ _ k₂ _ hEq => Fin.ext (by have := congrArg Fin.val hEq; dsimp at this; omega))]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp [A, witnessFamily]
      have hlt1 : 3 * b + c.val < 3 * m := by have := c.isLt; omega
      have hlt2 : 3 * b + k.val < 3 * m := by have := k.isLt; omega
      have hdiv : (3 * b + c.val) / 3 = (3 * b + k.val) / 3 := by have := c.isLt; have := k.isLt; omega
      have hmod1 : (⟨(3 * b + c.val) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = c :=
        Fin.ext (by dsimp only; have := c.isLt; omega)
      have hmod2 : (⟨(3 * b + k.val) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = k :=
        Fin.ext (by dsimp only; have := k.isLt; omega)
      rw [if_pos hlt1, if_pos hlt2, if_pos hdiv, hmod1, hmod2]
    exact hsplit
  · intro q hq
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h0 : A ⟨3 * m + q, by omega⟩ j = 0 := by
      dsimp [A, witnessFamily]
      rw [if_neg (by omega)]
    rw [h0, zero_mul]

private lemma witnessFamily_cubic_mulVec (m r : ℕ) (v : Fin (3 * m + r) → ZMod 2) :
    let e := (Matrix.toLin' (witnessFamily m r)) ^ 3 + (Matrix.toLin' (witnessFamily m r)) ^ 2 + 1
    (∀ (i : Fin (3 * m + r)), i.val < 3 * m → e v i = 0) ∧
    (∀ (i : Fin (3 * m + r)), 3 * m ≤ i.val → e v i = v i) := by
  intro e
  set A := witnessFamily m r
  have hpow : ∀ (k : ℕ) (w : Fin (3 * m + r) → ZMod 2),
      (∀ (b : ℕ) (hb : b < m) (c : Fin 3),
        ((Matrix.toLin' A ^ k) w) ⟨3 * b + c.val, by omega⟩ =
          ((matC ^ k).mulVec (fun j : Fin 3 => w ⟨3 * b + j.val, by omega⟩)) c) ∧
      (k ≥ 1 → ∀ (q : ℕ) (hq : q < r), ((Matrix.toLin' A ^ k) w) ⟨3 * m + q, by omega⟩ = 0) := by
    intro k
    induction k with
    | zero =>
        intro w
        refine ⟨fun b hb c => by simp, fun h => by omega⟩
    | succ k ih =>
        intro w
        have hstep := witnessFamily_mulVec m r ((Matrix.toLin' A ^ k) w)
        refine ⟨fun b hb c => ?_, fun _ q hq => ?_⟩
        · rw [pow_succ']
          change (A.mulVec ((Matrix.toLin' A ^ k) w)) ⟨3 * b + c.val, by omega⟩ = _
          rw [hstep.1 b hb c]
          have hvec : (fun j : Fin 3 => ((Matrix.toLin' A ^ k) w) ⟨3 * b + j.val, by omega⟩) =
              (matC ^ k).mulVec (fun j : Fin 3 => w ⟨3 * b + j.val, by omega⟩) := by
            funext j; exact (ih w).1 b hb j
          rw [hvec, Matrix.mulVec_mulVec, ← pow_succ']
        · rw [pow_succ']
          change (A.mulVec ((Matrix.toLin' A ^ k) w)) ⟨3 * m + q, by omega⟩ = 0
          exact hstep.2 q hq
  constructor
  · intro i hi
    have hb : i.val / 3 < m := by omega
    set b := i.val / 3
    set c : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩
    have hi_eq : i = ⟨3 * b + c.val, by omega⟩ := Fin.ext (by dsimp [b, c]; omega)
    rw [hi_eq]
    change ((Matrix.toLin' A ^ 3) v) _ + ((Matrix.toLin' A ^ 2) v) _ + v _ = 0
    rw [(hpow 3 v).1 b hb c, (hpow 2 v).1 b hb c]
    set vb : Fin 3 → ZMod 2 := fun j => v ⟨3 * b + j.val, by omega⟩
    have hsum : (matC ^ 3).mulVec vb c + (matC ^ 2).mulVec vb c + vb c =
        ((matC ^ 3 + matC ^ 2 + 1).mulVec vb) c := by
      simp [Matrix.add_mulVec, Matrix.one_mulVec]
    rw [show v ⟨3 * b + c.val, by omega⟩ = vb c from rfl, hsum, matC_cubic, Matrix.zero_mulVec]
    rfl
  · intro i hi
    have hq : i.val - 3 * m < r := by have := i.isLt; omega
    have hi_eq : i = ⟨3 * m + (i.val - 3 * m), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hi_eq]
    change ((Matrix.toLin' A ^ 3) v) _ + ((Matrix.toLin' A ^ 2) v) _ + v _ = v _
    rw [(hpow 3 v).2 (by omega) (i.val - 3 * m) hq, (hpow 2 v).2 (by omega) (i.val - 3 * m) hq,
      zero_add, zero_add]

/-- Every `d = 3m + r` with `3m > 3r` (so `r = 1, m ≥ 2` or `r = 2, m ≥ 3`) fails `M_d(F_2) = T_d`. -/
theorem witnessFamily_not_in_Td {m r : ℕ} (hgt : r < m) :
    ¬ isTripotentPlusSqZero (witnessFamily m r) := by
  intro hdec
  obtain ⟨t, u, ht, hu, ha⟩ := toLin'_decomp hdec
  have hle := finrank_ker_cubic_le ha ht hu
  set e := (Matrix.toLin' (witnessFamily m r)) ^ 3 + (Matrix.toLin' (witnessFamily m r)) ^ 2 + 1
  -- Show `finrank (ker e) ≥ 3m` and `finrank (range e) ≤ r`!
  let ιK : (Fin (3 * m) → ZMod 2) →ₗ[ZMod 2] LinearMap.ker e :=
    { toFun := fun w =>
        ⟨fun i => if h : i.val < 3 * m then w ⟨i.val, h⟩ else 0, by
          rw [LinearMap.mem_ker]
          funext i
          by_cases h : i.val < 3 * m
          · exact (witnessFamily_cubic_mulVec m r _).1 i h
          · rw [(witnessFamily_cubic_mulVec m r _).2 i (by omega), dif_neg h]; rfl⟩
      map_add' := fun w₁ w₂ => by
        apply Subtype.ext; funext i; by_cases h : i.val < 3 * m <;> simp [h]
      map_smul' := fun c w => by
        apply Subtype.ext; funext i; by_cases h : i.val < 3 * m <;> simp [h] }
  have hιK_inj : Function.Injective ιK := by
    intro w₁ w₂ hEq
    funext i
    have h := congrArg (fun x : LinearMap.ker e => x.1 ⟨i.val, by omega⟩) hEq
    simpa [ιK, i.isLt] using h
  have hker_ge : 3 * m ≤ Module.finrank (ZMod 2) (LinearMap.ker e) := by
    have := LinearMap.finrank_le_finrank_of_injective hιK_inj
    simpa [Module.finrank_fin_fun] using this
  let πR : LinearMap.range e →ₗ[ZMod 2] (Fin r → ZMod 2) :=
    { toFun := fun y q => y.1 ⟨3 * m + q.val, by have := q.isLt; omega⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hπR_inj : Function.Injective πR := by
    intro y₁ y₂ hEq
    apply Subtype.ext; funext i
    obtain ⟨v₁, hv₁⟩ := y₁.2
    obtain ⟨v₂, hv₂⟩ := y₂.2
    by_cases h : i.val < 3 * m
    · rw [← hv₁, ← hv₂, (witnessFamily_cubic_mulVec m r v₁).1 i h,
        (witnessFamily_cubic_mulVec m r v₂).1 i h]
    · have hq : i.val - 3 * m < r := by have := i.isLt; omega
      have hfun := congrFun hEq ⟨i.val - 3 * m, hq⟩
      have hi_eq : (⟨3 * m + (i.val - 3 * m), by omega⟩ : Fin (3 * m + r)) = i :=
        Fin.ext (by dsimp; omega)
      simpa [πR, hi_eq] using hfun
  have hrng_le : Module.finrank (ZMod 2) (LinearMap.range e) ≤ r := by
    have := LinearMap.finrank_le_finrank_of_injective hπR_inj
    simpa [Module.finrank_fin_fun] using this
  omega

/-- The `8 × 8` witness `A_8 = C ⊕ C ⊕ B` (`B = !![0, 1; 1, 1]`). -/
def witness8 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  fun i j =>
    if i.val < 6 then
      if j.val < 6 then
        if i.val / 3 = j.val / 3 then matC ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ ⟨j.val % 3, Nat.mod_lt _ (by omega)⟩
        else 0
      else 0
    else if 6 ≤ j.val then
      matB ⟨i.val - 6, by have := i.isLt; omega⟩ ⟨j.val - 6, by have := j.isLt; omega⟩
    else 0

/-- Case `d = 8`: `witness8 = C ⊕ C ⊕ B` is not in `T_8`, by Lemma B (`B^3 ≠ B^2`). -/
theorem witness8_not_in_T8 : ¬ isTripotentPlusSqZero witness8 := by
  intro hdec
  obtain ⟨t, u, ht, hu, ha⟩ := toLin'_decomp hdec
  -- Build the linear equivalence `E : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] ((Fin 6 → ZMod 2) × (Fin 2 → ZMod 2))`.
  let E : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] ((Fin 6 → ZMod 2) × (Fin 2 → ZMod 2)) :=
    { toFun := fun v => (fun i => v ⟨i.val, by omega⟩, fun j => v ⟨6 + j.val, by omega⟩)
      invFun := fun p i => if h : i.val < 6 then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - 6, by have := i.isLt; omega⟩
      left_inv := fun v => by
        funext i
        by_cases h : i.val < 6
        · simp [h]
        · simp only [dif_neg h]; congr 1; exact Fin.ext (by dsimp; omega)
      right_inv := fun ⟨v1, v2⟩ => by
        apply Prod.ext
        · funext i; simp [i.isLt]
        · funext i
          simp only [show ¬ 6 + i.val < 6 by omega, ↓reduceDIte]
          congr 1; exact Fin.ext (by dsimp; omega)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let matC2 : Matrix (Fin 6) (Fin 6) (ZMod 2) := witnessFamily 2 0
  let a₁ : Module.End (ZMod 2) (Fin 6 → ZMod 2) := Matrix.toLin' matC2
  let B : Module.End (ZMod 2) (Fin 2 → ZMod 2) := Matrix.toLin' matB
  have ha₁_cubic : a₁ ^ 3 + a₁ ^ 2 + 1 = 0 := by
    apply LinearMap.ext; intro v; funext i
    exact (witnessFamily_cubic_mulVec 2 0 v).1 i i.isLt
  have hB_unit : IsUnit (B ^ 3 + B ^ 2 + 1) := by
    refine ⟨⟨B ^ 3 + B ^ 2 + 1, B, ?_, ?_⟩, rfl⟩
    · have h : (B ^ 3 + B ^ 2 + 1) * B = Matrix.toLin' ((matB ^ 3 + matB ^ 2 + 1) * matB) := by
        rw [Matrix.toLin'_mul, map_add, map_add, toLin'_pow, toLin'_pow, Matrix.toLin'_one]; rfl
      rw [h, matB_p_mul_B, Matrix.toLin'_one]; rfl
    · have h : B * (B ^ 3 + B ^ 2 + 1) = Matrix.toLin' (matB * (matB ^ 3 + matB ^ 2 + 1)) := by
        rw [Matrix.toLin'_mul, map_add, map_add, toLin'_pow, toLin'_pow, Matrix.toLin'_one]; rfl
      rw [h, matB_B_mul_p, Matrix.toLin'_one]; rfl
  have hdim : Module.finrank (ZMod 2) (Fin 6 → ZMod 2) =
      3 * Module.finrank (ZMod 2) (Fin 2 → ZMod 2) := by
    simp
  -- Conjugate `Matrix.toLin' witness8`, `t`, `u` by `E`.
  let t' : Module.End (ZMod 2) ((Fin 6 → ZMod 2) × (Fin 2 → ZMod 2)) := E.toLinearMap ∘ₗ t ∘ₗ E.symm.toLinearMap
  let u' : Module.End (ZMod 2) ((Fin 6 → ZMod 2) × (Fin 2 → ZMod 2)) := E.toLinearMap ∘ₗ u ∘ₗ E.symm.toLinearMap
  have hconj_pow : ∀ (f : Module.End (ZMod 2) (Fin 8 → ZMod 2)) (k : ℕ),
      (E.toLinearMap ∘ₗ f ∘ₗ E.symm.toLinearMap) ^ k = E.toLinearMap ∘ₗ (f ^ k) ∘ₗ E.symm.toLinearMap := by
    intro f k
    induction k with
    | zero =>
        apply LinearMap.ext; intro p
        simp
    | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        apply LinearMap.ext; intro p
        simp [Module.End.mul_apply]
  have ht' : t' ^ 3 = t' := by dsimp [t']; rw [hconj_pow, ht]
  have hu' : u' ^ 2 = 0 := by
    dsimp [u']; rw [hconj_pow, hu]
    apply LinearMap.ext; intro p; simp
  have ha' : LinearMap.prodMap a₁ B = t' + u' := by
    have hblock : LinearMap.prodMap a₁ B = E.toLinearMap ∘ₗ Matrix.toLin' witness8 ∘ₗ E.symm.toLinearMap := by
      apply LinearMap.ext; rintro ⟨v1, v2⟩
      apply Prod.ext
      · funext i
        change (matC2.mulVec v1) i = (witness8.mulVec (E.symm (v1, v2))) ⟨i.val, by omega⟩
        simp only [Matrix.mulVec, dotProduct]
        have hsum : ∑ j : Fin 8, witness8 ⟨i.val, by omega⟩ j * E.symm (v1, v2) j =
            ∑ j : Fin 6, matC2 i j * v1 j := by
          have hsub : ∀ j : Fin 8, witness8 ⟨i.val, by omega⟩ j * E.symm (v1, v2) j ≠ 0 →
              j ∈ (Finset.univ : Finset (Fin 6)).image (fun k : Fin 6 => (⟨k.val, by omega⟩ : Fin 8)) := by
            intro j hj
            by_contra hnot; apply hj
            have hge : ¬ j.val < 6 := by
              intro hlt; apply hnot
              rw [Finset.mem_image]
              exact ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
            have : witness8 ⟨i.val, by omega⟩ j = 0 := by
              dsimp [witness8]; rw [if_pos i.isLt, if_neg hge]
            rw [this, zero_mul]
          rw [← Finset.sum_subset (Finset.subset_univ _) (fun j _ hnot => by
            by_contra hne; exact hnot (hsub j hne))]
          refine (Finset.sum_bij (fun (k : Fin 6) _ => (⟨k.val, by omega⟩ : Fin 8))
            (fun k _ => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
            (fun k₁ _ k₂ _ hEq => Fin.ext (by have := congrArg Fin.val hEq; dsimp at this; omega))
            (fun j hj => by rcases Finset.mem_image.mp hj with ⟨k, _, rfl⟩; exact ⟨k, Finset.mem_univ _, rfl⟩)
            (fun k _ => by
              dsimp [witness8, matC2, witnessFamily, E]
              simp only [i.isLt, k.isLt, ↓reduceIte, ↓reduceDIte])).symm
        exact hsum.symm
      · funext i
        change (matB.mulVec v2) i = (witness8.mulVec (E.symm (v1, v2))) ⟨6 + i.val, by omega⟩
        simp only [Matrix.mulVec, dotProduct]
        have hsum : ∑ j : Fin 8, witness8 ⟨6 + i.val, by omega⟩ j * E.symm (v1, v2) j =
            ∑ j : Fin 2, matB i j * v2 j := by
          have hsub : ∀ j : Fin 8, witness8 ⟨6 + i.val, by omega⟩ j * E.symm (v1, v2) j ≠ 0 →
              j ∈ (Finset.univ : Finset (Fin 2)).image (fun k : Fin 2 => (⟨6 + k.val, by omega⟩ : Fin 8)) := by
            intro j hj
            by_contra hnot; apply hj
            have hlt : ¬ 6 ≤ j.val := by
              intro hge; apply hnot
              rw [Finset.mem_image]
              exact ⟨⟨j.val - 6, by have := j.isLt; omega⟩, Finset.mem_univ _, Fin.ext (by dsimp; omega)⟩
            have : witness8 ⟨6 + i.val, by omega⟩ j = 0 := by
              dsimp [witness8]; rw [if_neg (by omega), if_neg hlt]
            rw [this, zero_mul]
          rw [← Finset.sum_subset (Finset.subset_univ _) (fun j _ hnot => by
            by_contra hne; exact hnot (hsub j hne))]
          refine (Finset.sum_bij (fun (k : Fin 2) _ => (⟨6 + k.val, by omega⟩ : Fin 8))
            (fun k _ => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
            (fun k₁ _ k₂ _ hEq => Fin.ext (by have := congrArg Fin.val hEq; dsimp at this; omega))
            (fun j hj => by rcases Finset.mem_image.mp hj with ⟨k, _, rfl⟩; exact ⟨k, Finset.mem_univ _, rfl⟩)
            (fun k _ => by
              dsimp [witness8, E]
              rw [if_neg (by omega), if_pos (by omega), dif_neg (by omega)]
              have h1 : (⟨6 + i.val - 6, by have := i.isLt; omega⟩ : Fin 2) = i := Fin.ext (by dsimp; omega)
              have h2 : (⟨6 + k.val - 6, by have := k.isLt; omega⟩ : Fin 2) = k := Fin.ext (by dsimp; omega)
              rw [h1, h2])).symm
        exact hsum.symm
    rw [hblock, ha]
    apply LinearMap.ext; intro p; simp [t', u']
  have hB3_eq_B2 : B ^ 3 = B ^ 2 := equality_case_B_cubed_eq_sq ha₁_cubic hB_unit hdim ha' ht' hu'
  have hmat : matB ^ 3 = matB ^ 2 := by
    apply Matrix.toLin'.injective
    rw [toLin'_pow, toLin'_pow]
    exact hB3_eq_B2
  exact matB_cubed_ne_sq hmat

/-- **Main Theorem (Complete negative resolution of Phuc–Danchev Problem 4.10, arXiv:2611.24594v2):**
For every integer `d ≥ 7` with `¬ (3 ∣ d)`, there exists a matrix `A ∈ M_d(F_2)` that is NOT
the sum of a tripotent (`T^3 = T`) and a square-zero matrix (`N^2 = 0`). -/
theorem phuc_danchev_problem_4_10 {d : ℕ} (hd : 7 ≤ d) (hndvd : ¬ 3 ∣ d) :
    ∃ A : Matrix (Fin d) (Fin d) (ZMod 2), ¬ isTripotentPlusSqZero A := by
  have hmod : d % 3 = 1 ∨ d % 3 = 2 := by omega
  rcases hmod with h1 | h2
  · obtain ⟨m, rfl⟩ : ∃ m, d = 3 * m + 1 := ⟨d / 3, by omega⟩
    exact ⟨witnessFamily m 1, witnessFamily_not_in_Td (by omega)⟩
  · by_cases hd8 : d = 8
    · subst hd8
      exact ⟨witness8, witness8_not_in_T8⟩
    · obtain ⟨m, rfl⟩ : ∃ m, d = 3 * m + 2 := ⟨d / 3, by omega⟩
      exact ⟨witnessFamily m 2, witnessFamily_not_in_Td (by omega)⟩

/-- **Particular case of Problem 4.10:**
No order `d = 8 * n + 4` with `n ≥ 1` (in particular all `n ≥ 2` with `n ≢ 1 (mod 3)`)
satisfies `M_d(F_2) = T_d`. -/
theorem phuc_danchev_problem_4_10_8n_plus_4 {n : ℕ} (hn : 1 ≤ n) :
    ∃ A : Matrix (Fin (8 * n + 4)) (Fin (8 * n + 4)) (ZMod 2), ¬ isTripotentPlusSqZero A := by
  by_cases hdvd : 3 ∣ (8 * n + 4)
  · obtain ⟨m, hm⟩ := hdvd
    have hpos : 0 < m := by omega
    -- `C^⊕m` on `Fin (3 * m)` cannot decompose by Theorem 0 (`witnessFamily_not_in_Td` with `r = 0`)!
    have hnot : ¬ isTripotentPlusSqZero (witnessFamily m 0) := witnessFamily_not_in_Td hpos
    have heq : 3 * m + 0 = 8 * n + 4 := by omega
    exact heq ▸ ⟨witnessFamily m 0, hnot⟩
  · exact phuc_danchev_problem_4_10 (by omega) hdvd

end PhucDanchevTripotent
