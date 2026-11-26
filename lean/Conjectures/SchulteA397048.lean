import Mathlib

/-!
# Proof of Werner Schulte's OEIS A397048 Conjectures

Reference: W. Schulte, OEIS A397048 (June 14, 2026; rev. 34).
For `0 ≤ k ≤ n`,
  `T(n, k) = ((-1)^k / k!) * ∑_{i=0}^{k} (-1)^i * C(k, i) * (n + i)^n`.

We formalize:
- Falling-factorial polynomials `(x)_k` over `ℚ[X]`, uniqueness of coordinates, shift splitting
  `(x)_c * (x - c)_k = (x)_{c+k}`, and binomial orthogonality;
- Signed Stirling numbers of the first kind `stirling1` (A048994) and Stirling numbers of the
  second kind `stirling2` (A048993) via their defining recurrences;
- General base-point `c` triangle `T_c c n k = ∑_j C(n, j) c^(n-j) S(j, k)` (integrality,
  vanishing for `k > n`, and falling-factorial expansion of `(x + c)^n`);
- **Conjecture 1** (and general base-point `c` Stirling shift identity):
  `T(n, k) = ∑_{i=0}^{n-k} s(n, k + i) * S(n + k + i, n + k)`;
- **Conjecture 2**: `∑_{k=0}^{n} T(n, k) = A134980(n)`;
- **Conjecture 3**: `∑_{i=0}^{k} T(n, i) * (k! / (k - i)!) = (n + k)^n` for every `n, k ≥ 0`.
-/

namespace SchulteA397048

open Finset Polynomial

/-! ### Section 1: Falling-factorial polynomials and basis properties -/

/-- Falling-factorial polynomial `(x)_k = x (x - 1) ... (x - k + 1)` in `ℚ[X]`. -/
noncomputable def fallingPoly : ℕ → Polynomial ℚ
  | 0 => 1
  | k + 1 => fallingPoly k * (Polynomial.X - Polynomial.C (k : ℚ))

private lemma eval_fallingPoly_nat : ∀ (k m : ℕ),
    (fallingPoly k).eval (m : ℚ) =
      if k ≤ m then ((m.factorial / (m - k).factorial : ℕ) : ℚ) else 0 := by
  intro k
  induction k with
  | zero =>
    intro m
    simp [fallingPoly, Nat.div_self (Nat.factorial_pos m)]
  | succ k ih =>
    intro m
    simp only [fallingPoly, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, ih m]
    by_cases hkm : k + 1 ≤ m
    · have hk : k ≤ m := by omega
      rw [if_pos hk, if_pos hkm]
      have hfac1 : (m - k).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (by omega)
      have hfac2 : (m - (k + 1)).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (by omega)
      have hstep : (m - k).factorial = (m - k) * (m - (k + 1)).factorial := by
        have h1 : m - k = (m - (k + 1)) + 1 := by omega
        rw [h1, Nat.factorial_succ]
      have hdiv : m.factorial / (m - (k + 1)).factorial =
          (m.factorial / (m - k).factorial) * (m - k) := by
        have hpos : 0 < (m - k).factorial := Nat.factorial_pos _
        have hpos2 : 0 < (m - (k + 1)).factorial := Nat.factorial_pos _
        have hmul1 := Nat.div_mul_cancel hfac1
        have hmul2 := Nat.div_mul_cancel hfac2
        apply Nat.eq_of_mul_eq_mul_right hpos2
        calc (m.factorial / (m - (k + 1)).factorial) * (m - (k + 1)).factorial
            = m.factorial := hmul2
          _ = (m.factorial / (m - k).factorial) * (m - k).factorial := hmul1.symm
          _ = (m.factorial / (m - k).factorial) * ((m - k) * (m - (k + 1)).factorial) := by
              rw [hstep]
          _ = ((m.factorial / (m - k).factorial) * (m - k)) * (m - (k + 1)).factorial := by ring
      rw [hdiv, Nat.cast_mul, Nat.cast_sub hk]
    · rw [if_neg hkm]
      by_cases hk : k ≤ m
      · have heq : m = k := by omega
        subst heq
        simp
      · rw [if_neg hk, zero_mul]

private lemma eval_fallingPoly_nat_eq_choose (k m : ℕ) :
    (fallingPoly k).eval (m : ℚ) = (k.factorial : ℚ) * (Nat.choose m k : ℚ) := by
  rw [eval_fallingPoly_nat]
  by_cases hkm : k ≤ m
  · rw [if_pos hkm]
    have hch := Nat.choose_mul_factorial_mul_factorial hkm
    have hfac : (m - k).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (by omega)
    have hnat : m.factorial / (m - k).factorial = k.factorial * Nat.choose m k := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (m - k))
      rw [Nat.div_mul_cancel hfac]
      linarith [hch]
    rw [hnat, Nat.cast_mul]
  · rw [if_neg hkm, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

private lemma eval_fallingPoly_self (k : ℕ) :
    (fallingPoly k).eval (k : ℚ) = (k.factorial : ℚ) := by
  rw [eval_fallingPoly_nat_eq_choose, Nat.choose_self, Nat.cast_one, mul_one]

private lemma eval_fallingPoly_of_lt {m k : ℕ} (h : m < k) :
    (fallingPoly k).eval (m : ℚ) = 0 := by
  rw [eval_fallingPoly_nat, if_neg (by omega)]

/-- Uniqueness of coordinates in the falling-factorial basis `{(x)_k}`. -/
private lemma fallingPoly_coord_unique {N : ℕ} {a b : ℕ → ℚ}
    (h : ∑ k ∈ range (N + 1), Polynomial.C (a k) * fallingPoly k =
      ∑ k ∈ range (N + 1), Polynomial.C (b k) * fallingPoly k) :
    ∀ k ≤ N, a k = b k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hkN
    have hev := congrArg (Polynomial.eval (k : ℚ)) h
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C] at hev
    have hsplit : ∀ f : ℕ → ℚ,
        ∑ j ∈ range (N + 1), f j * (fallingPoly j).eval (k : ℚ) =
          (∑ j ∈ range k, f j * (fallingPoly j).eval (k : ℚ)) + f k * (k.factorial : ℚ) := by
      intro f
      have hsub : range (k + 1) ⊆ range (N + 1) := Finset.range_mono (by omega)
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_range_succ, eval_fallingPoly_self]
      · intro j hjN hjk
        have hlt : k < j := by
          simp only [Finset.mem_range] at hjN hjk
          omega
        rw [eval_fallingPoly_of_lt hlt, mul_zero]
    rw [hsplit a, hsplit b] at hev
    have hprev : ∑ j ∈ range k, a j * (fallingPoly j).eval (k : ℚ) =
        ∑ j ∈ range k, b j * (fallingPoly j).eval (k : ℚ) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjk : j < k := Finset.mem_range.mp hj
      rw [ih j hjk (by omega)]
    rw [hprev] at hev
    have hfac_ne : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    exact mul_right_cancel₀ hfac_ne (add_left_cancel hev)

/-- Shift splitting: `(x)_c * (x - c)_k = (x)_{c + k}` in `ℚ[X]`. -/
private lemma fallingPoly_shift (c k : ℕ) :
    fallingPoly c * (fallingPoly k).comp (Polynomial.X - Polynomial.C (c : ℚ)) =
      fallingPoly (c + k) := by
  induction k with
  | zero =>
    simp [fallingPoly]
  | succ k ih =>
    rw [show c + (k + 1) = (c + k) + 1 by omega]
    simp only [fallingPoly, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.X_comp,
      Polynomial.C_comp, Nat.cast_add]
    rw [← mul_assoc, ih]
    congr 1
    simp only [map_add]
    ring

/-- Binomial orthogonality: `∑_{i=0}^{k} (-1)^(k - i) C(k, i) (i)_m = k! * δ_{k, m}`. -/
private lemma binom_falling_orthog (k m : ℕ) :
    ∑ i ∈ range (k + 1), (-1 : ℚ) ^ (k - i) * (Nat.choose k i : ℚ) * (fallingPoly m).eval (i : ℚ) =
      if m = k then (k.factorial : ℚ) else 0 := by
  by_cases hmk : m ≤ k
  · have hzero : ∀ i ∈ range (k + 1), i < m →
        (-1 : ℚ) ^ (k - i) * (Nat.choose k i : ℚ) * (fallingPoly m).eval (i : ℚ) = 0 := by
      intro i _ hi
      rw [eval_fallingPoly_of_lt hi, mul_zero]
    have hsub : Finset.Ico m (k + 1) ⊆ range (k + 1) := by
      intro i hi
      simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · have hbij : ∑ i ∈ Finset.Ico m (k + 1),
          (-1 : ℚ) ^ (k - i) * (Nat.choose k i : ℚ) * (fallingPoly m).eval (i : ℚ) =
          ∑ r ∈ range (k - m + 1),
            ((m.factorial : ℚ) * (Nat.choose k m : ℚ)) *
              ((-1 : ℚ) ^ ((k - m) - r) * (Nat.choose (k - m) r : ℚ)) := by
        refine Finset.sum_nbij (fun i => i - m) ?_ ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
          omega
        · intro i₁ hi₁ i₂ hi₂ hEq
          simp only [Finset.mem_coe, Finset.mem_Ico] at hi₁ hi₂
          dsimp only at hEq
          omega
        · intro r hr
          simp only [Finset.mem_coe, Finset.mem_range] at hr
          refine ⟨m + r, ?_, ?_⟩
          · simp only [Finset.mem_coe, Finset.mem_Ico]; omega
          · dsimp only; omega
        · intro i hi
          simp only [Finset.mem_Ico] at hi
          rw [eval_fallingPoly_nat_eq_choose]
          have hch : Nat.choose k i * Nat.choose i m =
              Nat.choose k m * Nat.choose (k - m) (i - m) :=
            Nat.choose_mul (by omega)
          have hchQ : (Nat.choose k i : ℚ) * (Nat.choose i m : ℚ) =
              (Nat.choose k m : ℚ) * (Nat.choose (k - m) (i - m) : ℚ) := by
            exact_mod_cast hch
          have hexp : k - i = (k - m) - (i - m) := by omega
          rw [hexp]
          calc (-1 : ℚ) ^ ((k - m) - (i - m)) * (Nat.choose k i : ℚ) *
                  ((m.factorial : ℚ) * (Nat.choose i m : ℚ))
              = (-1 : ℚ) ^ ((k - m) - (i - m)) * (m.factorial : ℚ) *
                  ((Nat.choose k i : ℚ) * (Nat.choose i m : ℚ)) := by ring
            _ = (-1 : ℚ) ^ ((k - m) - (i - m)) * (m.factorial : ℚ) *
                  ((Nat.choose k m : ℚ) * (Nat.choose (k - m) (i - m) : ℚ)) := by rw [hchQ]
            _ = ((m.factorial : ℚ) * (Nat.choose k m : ℚ)) *
                  ((-1 : ℚ) ^ ((k - m) - (i - m)) * (Nat.choose (k - m) (i - m) : ℚ)) := by ring
      rw [hbij, ← Finset.mul_sum]
      have hbin : ∑ r ∈ range (k - m + 1),
          (-1 : ℚ) ^ ((k - m) - r) * (Nat.choose (k - m) r : ℚ) = (1 + (-1 : ℚ)) ^ (k - m) := by
        rw [add_pow]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        ring
      rw [hbin]
      by_cases heq : m = k
      · subst heq
        simp
      · rw [if_neg heq]
        have hpos : k - m ≠ 0 := by omega
        have h0 : (1 + (-1 : ℚ)) ^ (k - m) = 0 := by
          rw [add_neg_cancel, zero_pow hpos]
        rw [h0, mul_zero]
    · intro i hi hni
      simp only [Finset.mem_range, Finset.mem_Ico] at hi hni
      exact hzero i (Finset.mem_range.mpr hi) (by omega)
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hik : i < m := by
      have := Finset.mem_range.mp hi
      omega
    rw [eval_fallingPoly_of_lt hik, mul_zero]

/-! ### Section 2: Stirling numbers (OEIS A048994 & A048993) and Bell numbers (A000110) -/

/-- Signed Stirling numbers of the first kind `s(n, k)` (OEIS A048994). -/
def stirling1 : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling1 n k - (n : ℤ) * stirling1 n (k + 1)

/-- Stirling numbers of the second kind `S(n, k)` (OEIS A048993). -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)

/-- Bell numbers `B_n = ∑_{k=0}^{n} S(n, k)` (OEIS A000110). -/
def bellNumber (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), stirling2 n k

private lemma stirling1_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → stirling1 n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    cases k with
    | zero => omega
    | succ m => rfl
  | succ n ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ m =>
      simp only [stirling1, ih (by omega : n < m), ih (by omega : n < m + 1)]
      ring

private lemma stirling2_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → stirling2 n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    cases k with
    | zero => omega
    | succ m => rfl
  | succ n ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ m =>
      simp only [stirling2, ih (by omega : n < m), ih (by omega : n < m + 1)]
      ring

/-- `(x)_n = ∑_{k=0}^{n} s(n, k) x^k` in `ℚ[X]`. -/
theorem fallingPoly_eq_sum_stirling1 (n : ℕ) :
    fallingPoly n = ∑ k ∈ range (n + 1), Polynomial.C (stirling1 n k : ℚ) * Polynomial.X ^ k := by
  induction n with
  | zero =>
    simp [fallingPoly, stirling1]
  | succ n ih =>
    rw [fallingPoly, ih, mul_sub, Finset.sum_mul, Finset.sum_mul]
    -- Split RHS `∑_{k=0}^{n+1}` at `k = 0` (`s(n+1, 0) = 0`) and `k = j + 1`.
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [stirling1, Int.cast_zero, map_zero, zero_mul, add_zero]
    have hsplit : ∑ j ∈ range (n + 1),
        Polynomial.C ((stirling1 n j - (n : ℤ) * stirling1 n (j + 1) : ℤ) : ℚ) *
          Polynomial.X ^ (j + 1) =
        (∑ j ∈ range (n + 1), Polynomial.C (stirling1 n j : ℚ) * Polynomial.X ^ (j + 1)) -
        (∑ j ∈ range (n + 1),
          Polynomial.C (stirling1 n (j + 1) : ℚ) * Polynomial.X ^ (j + 1) * Polynomial.C (n : ℚ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, map_sub, map_mul]
      ring
    rw [hsplit]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [pow_succ]; ring
    · -- Shift index in the second sum (`s(n, 0) = 0` for `n ≥ 1`, and `C 0 = 0` for `n = 0`).
      by_cases hn : n = 0
      · subst hn
        simp [stirling1]
      · have h0 : stirling1 n 0 = 0 := by cases n with | zero => omega | succ m => rfl
        have htop : stirling1 n (n + 1) = 0 := stirling1_eq_zero_of_lt (by omega)
        rw [Finset.sum_range_succ' (f := fun k => Polynomial.C (stirling1 n k : ℚ) * Polynomial.X ^ k * Polynomial.C (n : ℚ)),
          h0]
        simp only [Int.cast_zero, map_zero, zero_mul, add_zero]
        rw [Finset.sum_range_succ (f := fun j => Polynomial.C (stirling1 n (j + 1) : ℚ) * Polynomial.X ^ (j + 1) * Polynomial.C (n : ℚ)),
          htop]
        simp

/-- `x^n = ∑_{k=0}^{n} S(n, k) (x)_k` in `ℚ[X]`. -/
theorem X_pow_eq_sum_stirling2 (n : ℕ) :
    Polynomial.X ^ n = ∑ k ∈ range (n + 1), Polynomial.C (stirling2 n k : ℚ) * fallingPoly k := by
  induction n with
  | zero =>
    simp [fallingPoly, stirling2]
  | succ n ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    have hmul : ∀ k ∈ range (n + 1),
        Polynomial.C (stirling2 n k : ℚ) * fallingPoly k * Polynomial.X =
          Polynomial.C (stirling2 n k : ℚ) * fallingPoly (k + 1) +
          Polynomial.C ((k : ℚ) * (stirling2 n k : ℚ)) * fallingPoly k := by
      intro k _
      have hx : fallingPoly k * Polynomial.X =
          fallingPoly (k + 1) + Polynomial.C (k : ℚ) * fallingPoly k := by
        simp only [fallingPoly]
        ring
      rw [mul_assoc, hx, mul_add, map_mul]
      ring
    rw [Finset.sum_congr rfl hmul, Finset.sum_add_distrib]
    -- Re-index RHS `∑_{k=0}^{n+1} S(n+1, k) (x)_k`:
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [stirling2, Nat.cast_zero, map_zero, zero_mul, add_zero]
    have hsplit : ∑ j ∈ range (n + 1),
        Polynomial.C ((stirling2 n j + (j + 1) * stirling2 n (j + 1) : ℕ) : ℚ) *
          fallingPoly (j + 1) =
        (∑ j ∈ range (n + 1), Polynomial.C (stirling2 n j : ℚ) * fallingPoly (j + 1)) +
        (∑ j ∈ range (n + 1),
          Polynomial.C (((j + 1 : ℕ) : ℚ) * (stirling2 n (j + 1) : ℚ)) * fallingPoly (j + 1)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Nat.cast_add, Nat.cast_mul, map_add, map_mul]
      ring
    rw [hsplit]
    congr 1
    -- Match the `k * S(n, k)` sums: `k = 0` has factor `0`, `j = n` has `S(n, n+1) = 0`.
    rw [Finset.sum_range_succ' (f := fun k => Polynomial.C ((k : ℚ) * (stirling2 n k : ℚ)) * fallingPoly k)]
    simp only [Nat.cast_zero, zero_mul, map_zero, add_zero]
    rw [Finset.sum_range_succ (f := fun j => Polynomial.C (((j + 1 : ℕ) : ℚ) * (stirling2 n (j + 1) : ℚ)) * fallingPoly (j + 1)),
      stirling2_eq_zero_of_lt (by omega : n < n + 1)]
    simp

/-! ### Section 3: The OEIS A397048 triangle and all three conjectures -/

/-- General base-point `c` forward-difference triangle:
`T_c(n, k) = ((-1)^k / k!) * ∑_{i=0}^{k} (-1)^i * C(k, i) * (c + i)^n`.
Setting `c = n` recovers OEIS A397048. -/
noncomputable def T_c (c n k : ℕ) : ℚ :=
  (∑ i ∈ range (k + 1), (-1 : ℚ) ^ i * (Nat.choose k i : ℚ) * ((c + i : ℕ) : ℚ) ^ n) *
    (-1 : ℚ) ^ k / (k.factorial : ℚ)

/-- OEIS A397048 triangle `T(n, k) = T_n(n, k)`. -/
noncomputable def A397048 (n k : ℕ) : ℚ := T_c n n k

/-- OEIS A134980(n) = `∑_{j=0}^{n} C(n, j) * n^(n - j) * B_j`. -/
def A134980 (n : ℕ) : ℕ :=
  ∑ j ∈ range (n + 1), Nat.choose n j * n ^ (n - j) * bellNumber j

/-- **Theorem 1 (Binomial–Stirling formula & integrality):**
For all `c, n, k ∈ ℕ`, `T_c(n, k) = ∑_{j=0}^{n} C(n, j) c^(n - j) S(j, k) ∈ ℕ`. -/
theorem T_c_eq_binom_stirling2 (c n k : ℕ) :
    T_c c n k = ((∑ j ∈ range (n + 1), Nat.choose n j * c ^ (n - j) * stirling2 j k : ℕ) : ℚ) := by
  let U : ℕ → ℚ := fun m =>
    ((∑ j ∈ range (n + 1), Nat.choose n j * c ^ (n - j) * stirling2 j m : ℕ) : ℚ)
  have hU_zero : ∀ m, n < m → U m = 0 := by
    intro m hm
    dsimp only [U]
    norm_cast
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [stirling2_eq_zero_of_lt (by omega), mul_zero]
  have hpoly : (Polynomial.X + Polynomial.C (c : ℚ)) ^ n =
      ∑ m ∈ range (n + 1), Polynomial.C (U m) * fallingPoly m := by
    rw [add_pow]
    have hstep : ∀ j ∈ range (n + 1),
        Polynomial.X ^ j * Polynomial.C (c : ℚ) ^ (n - j) * (Nat.choose n j : Polynomial ℚ) =
          ∑ m ∈ range (n + 1),
            Polynomial.C ((Nat.choose n j : ℚ) * (c : ℚ) ^ (n - j) * (stirling2 j m : ℚ)) *
              fallingPoly m := by
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [X_pow_eq_sum_stirling2 j]
      have hsub : range (j + 1) ⊆ range (n + 1) := Finset.range_mono (by omega)
      rw [Finset.sum_subset hsub]
      · rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        simp only [map_mul, map_pow, map_natCast]
        ring
      · intro m hm hmj
        have hlt : j < m := by simp only [Finset.mem_range] at hm hmj; omega
        rw [stirling2_eq_zero_of_lt hlt, Nat.cast_zero, map_zero, zero_mul]
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.sum_mul]
    congr 1
    dsimp only [U]
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, map_sum, map_mul, map_pow]
  -- Evaluate `(X + c)^n = ∑_{m=0}^{N} U(m) (X)_m` with `N = max n k` and apply binomial orthogonality.
  set N := max n k
  have hpolyN : (Polynomial.X + Polynomial.C (c : ℚ)) ^ n =
      ∑ m ∈ range (N + 1), Polynomial.C (U m) * fallingPoly m := by
    rw [hpoly]
    refine Finset.sum_subset (Finset.range_mono (by omega)) (fun m _ hmn => ?_)
    have hlt : n < m := by simp only [Finset.mem_range] at hmn; omega
    rw [hU_zero m hlt, map_zero, zero_mul]
  have heval_i : ∀ i : ℕ, ((c + i : ℕ) : ℚ) ^ n =
      ∑ m ∈ range (N + 1), U m * (fallingPoly m).eval (i : ℚ) := by
    intro i
    have h := congrArg (Polynomial.eval (i : ℚ)) hpolyN
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_finsetSum, Polynomial.eval_mul] at h
    rw [Nat.cast_add, add_comm (c : ℚ) (i : ℚ)]
    exact h
  have hsum : (k.factorial : ℚ) * T_c c n k = (k.factorial : ℚ) * U k := by
    have hfac_ne : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hT : (k.factorial : ℚ) * T_c c n k =
        ∑ i ∈ range (k + 1), (-1 : ℚ) ^ (k - i) * (Nat.choose k i : ℚ) * ((c + i : ℕ) : ℚ) ^ n := by
      unfold T_c
      rw [mul_div_cancel₀ _ hfac_ne, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hsign : (-1 : ℚ) ^ i * (-1 : ℚ) ^ k = (-1 : ℚ) ^ (k - i) := by
        have h1 : k = (k - i) + i := by omega
        calc (-1 : ℚ) ^ i * (-1 : ℚ) ^ k
            = (-1 : ℚ) ^ i * ((-1 : ℚ) ^ (k - i) * (-1 : ℚ) ^ i) := by
                conv_lhs => rw [h1, pow_add]
          _ = (-1 : ℚ) ^ (k - i) * ((-1 : ℚ) * (-1 : ℚ)) ^ i := by rw [mul_pow]; ring
          _ = (-1 : ℚ) ^ (k - i) := by norm_num
      calc (-1 : ℚ) ^ i * (Nat.choose k i : ℚ) * ((c + i : ℕ) : ℚ) ^ n * (-1 : ℚ) ^ k
          = ((-1 : ℚ) ^ i * (-1 : ℚ) ^ k) * (Nat.choose k i : ℚ) * ((c + i : ℕ) : ℚ) ^ n := by ring
        _ = (-1 : ℚ) ^ (k - i) * (Nat.choose k i : ℚ) * ((c + i : ℕ) : ℚ) ^ n := by rw [hsign]
    rw [hT]
    simp_rw [heval_i, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ m ∈ range (N + 1),
        ∑ i ∈ range (k + 1),
          (-1 : ℚ) ^ (k - i) * (Nat.choose k i : ℚ) * (U m * (fallingPoly m).eval (i : ℚ)) =
        if m = k then (k.factorial : ℚ) * U k else 0 := by
      intro m _
      have hfac : ∑ i ∈ range (k + 1),
          (-1 : ℚ) ^ (k - i) * (Nat.choose k i : ℚ) * (U m * (fallingPoly m).eval (i : ℚ)) =
          U m * ∑ i ∈ range (k + 1),
            (-1 : ℚ) ^ (k - i) * (Nat.choose k i : ℚ) * (fallingPoly m).eval (i : ℚ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [hfac, binom_falling_orthog k m]
      split_ifs with hmk
      · subst hmk; ring
      · ring
    rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_range.mpr (by omega))]
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)) hsum

/-- Vanishing: `T_c(n, k) = 0` whenever `k > n`. -/
theorem T_c_eq_zero_of_lt {c n k : ℕ} (h : n < k) : T_c c n k = 0 := by
  rw [T_c_eq_binom_stirling2]
  norm_cast
  refine Finset.sum_eq_zero (fun j hj => ?_)
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [stirling2_eq_zero_of_lt (by omega), mul_zero]

/-- Falling-factorial expansion `(x + c)^n = ∑_{k=0}^{n} T_c(n, k) (x)_k` in `ℚ[X]`. -/
theorem X_add_C_pow_eq_sum_T_c (c n : ℕ) :
    (Polynomial.X + Polynomial.C (c : ℚ)) ^ n =
      ∑ k ∈ range (n + 1), Polynomial.C (T_c c n k) * fallingPoly k := by
  rw [add_pow]
  have hstep : ∀ j ∈ range (n + 1),
      Polynomial.X ^ j * Polynomial.C (c : ℚ) ^ (n - j) * (Nat.choose n j : Polynomial ℚ) =
        ∑ k ∈ range (n + 1),
          Polynomial.C ((Nat.choose n j : ℚ) * (c : ℚ) ^ (n - j) * (stirling2 j k : ℚ)) *
            fallingPoly k := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [X_pow_eq_sum_stirling2 j, Finset.sum_subset (Finset.range_mono (by omega : j + 1 ≤ n + 1))]
    · rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [map_mul, map_pow, map_natCast]
      ring
    · intro k hk hkj
      have hlt : j < k := by simp only [Finset.mem_range] at hk hkj; omega
      rw [stirling2_eq_zero_of_lt hlt, Nat.cast_zero, map_zero, zero_mul]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_mul, T_c_eq_binom_stirling2]
  congr 1
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, map_sum, map_mul, map_pow]

/-- **General Stirling shift theorem:**
For all `c, n, k ∈ ℕ` with `k ≤ n`,
`T_c(n, k) = ∑_{m=0}^{c} s(c, m) * S(n + m, c + k)`. -/
theorem T_c_eq_stirling_shift (c n k : ℕ) (hk : k ≤ n) :
    T_c c n k = ∑ m ∈ range (c + 1), (stirling1 c m : ℚ) * (stirling2 (n + m) (c + k) : ℚ) := by
  -- Shift `X ↦ X - C c` in `(X + c)^n = ∑_{j=0}^{n} T_c(n, j) (X)_j` and multiply by `(X)_c`.
  have hshift := congrArg (fun p : Polynomial ℚ => p.comp (Polynomial.X - Polynomial.C (c : ℚ)))
    (X_add_C_pow_eq_sum_T_c c n)
  have hL_comp : ((Polynomial.X + Polynomial.C (c : ℚ)) ^ n).comp (Polynomial.X - Polynomial.C (c : ℚ)) =
      Polynomial.X ^ n := by
    simp [Polynomial.pow_comp, Polynomial.add_comp]
  have hsum_comp : ∀ (s : Finset ℕ) (f : ℕ → Polynomial ℚ) (q : Polynomial ℚ),
      (∑ j ∈ s, f j).comp q = ∑ j ∈ s, (f j).comp q := by
    intro s f q
    change Polynomial.compRingHom q (∑ j ∈ s, f j) = ∑ j ∈ s, Polynomial.compRingHom q (f j)
    exact map_sum (Polynomial.compRingHom q) f s
  rw [hL_comp, hsum_comp] at hshift
  have hmul_eq : Polynomial.X ^ n * fallingPoly c =
      ∑ K ∈ range (c + n + 1),
        Polynomial.C (if c ≤ K then T_c c n (K - c) else 0) * fallingPoly K := by
    have h1 : Polynomial.X ^ n * fallingPoly c =
        ∑ j ∈ range (n + 1), Polynomial.C (T_c c n j) * fallingPoly (c + j) := by
      rw [mul_comm, hshift, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Polynomial.mul_comp, Polynomial.C_comp, ← mul_assoc,
        mul_comm (fallingPoly c) (Polynomial.C (T_c c n j)), mul_assoc, fallingPoly_shift c j]
    rw [h1]
    have hsplit : ∑ K ∈ range (c + n + 1),
        Polynomial.C (if c ≤ K then T_c c n (K - c) else 0) * fallingPoly K =
        ∑ K ∈ Finset.Ico c (c + n + 1), Polynomial.C (T_c c n (K - c)) * fallingPoly K := by
      have hsub : Finset.Ico c (c + n + 1) ⊆ range (c + n + 1) := by
        intro K hK; simp only [Finset.mem_Ico, Finset.mem_range] at hK ⊢; omega
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl (fun K hK => ?_)
        have hcK : c ≤ K := (Finset.mem_Ico.mp hK).1
        rw [if_pos hcK]
      · intro K hK hnK
        simp only [Finset.mem_range, Finset.mem_Ico] at hK hnK
        rw [if_neg (by omega), map_zero, zero_mul]
    rw [hsplit]
    refine (Finset.sum_nbij (fun j => c + j) ?_ ?_ ?_ ?_)
    · intro j hj; simp only [Finset.mem_range, Finset.mem_Ico] at hj ⊢; omega
    · intro j₁ _ j₂ _ hEq; dsimp only at hEq; omega
    · intro K hK
      simp only [Finset.mem_coe, Finset.mem_Ico] at hK
      exact ⟨K - c, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
    · intro j _
      rw [Nat.add_sub_cancel_left]
  -- Expand `X^n * fallingPoly c` via Stirling numbers of the 1st and 2nd kind.
  have hRHS_eq : Polynomial.X ^ n * fallingPoly c =
      ∑ K ∈ range (c + n + 1),
        Polynomial.C (∑ m ∈ range (c + 1), (stirling1 c m : ℚ) * (stirling2 (n + m) K : ℚ)) *
          fallingPoly K := by
    rw [fallingPoly_eq_sum_stirling1 c, Finset.mul_sum]
    have hstep : ∀ m ∈ range (c + 1),
        Polynomial.X ^ n * (Polynomial.C (stirling1 c m : ℚ) * Polynomial.X ^ m) =
          ∑ K ∈ range (c + n + 1),
            Polynomial.C ((stirling1 c m : ℚ) * (stirling2 (n + m) K : ℚ)) * fallingPoly K := by
      intro m hm
      have hmc : m ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hpow : Polynomial.X ^ n * (Polynomial.C (stirling1 c m : ℚ) * Polynomial.X ^ m) =
          Polynomial.C (stirling1 c m : ℚ) * Polynomial.X ^ (n + m) := by
        rw [pow_add]; ring
      rw [hpow, X_pow_eq_sum_stirling2 (n + m)]
      rw [Finset.sum_subset (Finset.range_mono (by omega : n + m + 1 ≤ c + n + 1))]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun K _ => ?_)
        rw [map_mul, mul_assoc]
      · intro K hK hKm
        have hlt : n + m < K := by simp only [Finset.mem_range] at hK hKm; omega
        rw [stirling2_eq_zero_of_lt hlt, Nat.cast_zero, map_zero, zero_mul]
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    rw [← Finset.sum_mul, map_sum]
  have hcoord := fallingPoly_coord_unique (hmul_eq.symm.trans hRHS_eq) (c + k) (by omega)
  simp only [Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left] at hcoord
  exact hcoord

/-- **Conjecture 1 (OEIS A397048):**
For all `n ≥ 0` and `0 ≤ k ≤ n`,
`T(n, k) = ∑_{i=0}^{n - k} s(n, k + i) * S(n + k + i, n + k)`. -/
theorem schulte_A397048_conj1 (n k : ℕ) (hk : k ≤ n) :
    A397048 n k =
      ∑ i ∈ range (n - k + 1), (stirling1 n (k + i) : ℚ) * (stirling2 (n + k + i) (n + k) : ℚ) := by
  unfold A397048
  rw [T_c_eq_stirling_shift n n k hk]
  have hsub : Finset.Ico k (n + 1) ⊆ range (n + 1) := by
    intro m hm; simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢; omega
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_nbij (fun m => m - k) ?_ ?_ ?_ ?_
    · intro m hm; simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢; omega
    · intro m₁ hm₁ m₂ hm₂ hEq
      simp only [Finset.mem_coe, Finset.mem_Ico] at hm₁ hm₂
      dsimp only at hEq; omega
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_range] at hi
      exact ⟨k + i, Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩), by dsimp only; omega⟩
    · intro m hm
      have hkm : k ≤ m := (Finset.mem_Ico.mp hm).1
      have h1 : k + (m - k) = m := by omega
      have h2 : n + k + (m - k) = n + m := by omega
      rw [h1, h2]
  · intro m hm hnm
    simp only [Finset.mem_range, Finset.mem_Ico] at hm hnm
    rw [stirling2_eq_zero_of_lt (by omega : n + m < n + k), Nat.cast_zero, mul_zero]

/-- **Conjecture 2 (OEIS A397048):**
For every `n ≥ 0`, the `n`-th row sum equals `A134980(n)`. -/
theorem schulte_A397048_conj2 (n : ℕ) :
    ∑ k ∈ range (n + 1), A397048 n k = (A134980 n : ℚ) := by
  unfold A397048 A134980 bellNumber
  simp_rw [T_c_eq_binom_stirling2]
  norm_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← Finset.mul_sum]
  congr 1
  symm
  refine Finset.sum_subset (Finset.range_mono (by omega : j + 1 ≤ n + 1)) (fun k _ hkj => ?_)
  have hlt : j < k := by simp only [Finset.mem_range] at hkj; omega
  exact stirling2_eq_zero_of_lt hlt

/-- **Conjecture 3 (OEIS A397048):**
For all `n, k ≥ 0` (including `k > n`),
`∑_{i=0}^{k} T(n, i) * (k! / (k - i)!) = (n + k)^n`. -/
theorem schulte_A397048_conj3 (n k : ℕ) :
    ∑ i ∈ range (k + 1), A397048 n i * ((k.factorial / (k - i).factorial : ℕ) : ℚ) =
      ((n + k : ℕ) : ℚ) ^ n := by
  unfold A397048
  set N := max n k
  have hpolyN : (Polynomial.X + Polynomial.C (n : ℚ)) ^ n =
      ∑ i ∈ range (N + 1), Polynomial.C (T_c n n i) * fallingPoly i := by
    rw [X_add_C_pow_eq_sum_T_c n n]
    refine Finset.sum_subset (Finset.range_mono (by omega)) (fun i _ hin => ?_)
    have hlt : n < i := by simp only [Finset.mem_range] at hin; omega
    rw [T_c_eq_zero_of_lt hlt, map_zero, zero_mul]
  have hev := congrArg (Polynomial.eval (k : ℚ)) hpolyN
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul] at hev
  rw [Nat.cast_add, add_comm (n : ℚ) (k : ℚ), hev]
  symm
  refine Finset.sum_subset (Finset.range_mono (by omega : k + 1 ≤ N + 1)) ?_ |>.symm.trans ?_
  · intro i _ hik
    have hlt : k < i := by simp only [Finset.mem_range] at hik; omega
    rw [eval_fallingPoly_of_lt hlt, mul_zero]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [eval_fallingPoly_nat, if_pos hik]

end SchulteA397048
