import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Proof of the Second Chandra–Jain Conjecture and Exact Degree Criterion
# (arXiv:2608.11372v3, Section 5)

In *On The Spectral Properties of Discrete Landscape Functions* (`arXiv:2608.11372v3`,
Section 5, `conj:chandra-jain-second`), A. Chandra and S. R. Jain define for `N ≥ 3`
and odd `1 ≤ k < N` the discrete landscape expansion coefficient

  `c_k(N) = (1/4) √(2/N) cot(k π / (2 N)) csc²(k π / (2 N))`

and conjecture that whenever `d = gcd(N, k) > 1` and `N₀ = N / d`,

  `[ℚ(c_k(N)) : ℚ] ∈ {φ(N₀), 2 φ(N₀)}`.

They also leave open an arithmetic criterion distinguishing the two degrees.

We formalize the complete self-contained proof inside the cyclotomic field
`K = CyclotomicField (8 * N) ℚ`:
- `chandraJain_exact_degree` (Theorem B): exact degree for every `N ≥ 3` and every
  odd `1 ≤ k < N`: `φ(N₀)` when `N₀` is odd or every prime `p` with odd
  `d.factorization p` divides `N₀`, and `2 * φ(N₀)` otherwise.
- `chandraJain_dichotomy` (Theorem A): the Second Chandra–Jain Conjecture for `1 < gcd(N, k)`.
- `chandraJain_coprime_degree`: the coprime case `gcd(N, k) = 1` (`deg = φ(N)`),
  reproving and generalizing Zhou's theorem for `k = 1`.
-/

namespace ChandraJainSecondConjecture

open scoped BigOperators Cyclotomic Polynomial
open Real Complex Polynomial

/-- The discrete landscape expansion coefficient `c_k(N)` for odd `1 ≤ k < N`. -/
noncomputable def landscapeCoeff (k N : ℕ) : ℝ :=
  (1 / 4 : ℝ) * Real.sqrt (2 / (N : ℝ)) *
    (Real.cos ((k : ℝ) * Real.pi / (2 * (N : ℝ))) /
      Real.sin ((k : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 3)

/-- Equivalence with the `cot · csc²` form written in Chandra–Jain (arXiv:2608.11372v3). -/
lemma cot_mul_csc_sq_eq (θ : ℝ) :
    Real.cot θ * (Real.sin θ)⁻¹ ^ 2 = Real.cos θ / Real.sin θ ^ 3 := by
  rw [Real.cot_eq_cos_div_sin]
  ring

/-- Auxiliary trigonometric function `f(θ) = cos θ / sin³ θ`. -/
noncomputable def trigF (θ : ℝ) : ℝ :=
  Real.cos θ / Real.sin θ ^ 3

lemma trigF_add_pi (θ : ℝ) : trigF (θ + Real.pi) = trigF θ := by
  dsimp only [trigF]
  rw [Real.cos_add_pi, Real.sin_add_pi]
  ring

lemma trigF_sub_pi (θ : ℝ) : trigF (θ - Real.pi) = trigF θ := by
  have h := trigF_add_pi (θ - Real.pi)
  rw [sub_add_cancel] at h
  exact h.symm

lemma trigF_add_int_mul_pi (θ : ℝ) (m : ℤ) : trigF (θ + (m : ℝ) * Real.pi) = trigF θ := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show θ + ((k : ℝ) + 1) * Real.pi = (θ + (k : ℝ) * Real.pi) + Real.pi by ring,
      trigF_add_pi, ih]
  | pred k ih =>
    push_cast at ih ⊢
    rw [show θ + (-(k : ℝ) - 1) * Real.pi = (θ + -(k : ℝ) * Real.pi) - Real.pi by ring,
      trigF_sub_pi, ih]

lemma trigF_neg (θ : ℝ) : trigF (-θ) = -trigF θ := by
  dsimp only [trigF]
  rw [Real.cos_neg, Real.sin_neg]
  ring

lemma trigF_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) : 0 < trigF θ := by
  dsimp only [trigF]
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  positivity

lemma trigF_strictAntiOn : StrictAntiOn trigF (Set.Ioo 0 (Real.pi / 2)) := by
  intro x hx y hy hxy
  dsimp only [trigF]
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  have hcy : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith [hy.1, Real.pi_pos], hy.2⟩
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
  have hsy : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy.1 (by linarith [hy.2, Real.pi_pos])
  have hcos : Real.cos y < Real.cos x :=
    Real.strictAntiOn_cos ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
      ⟨le_of_lt hy.1, by linarith [hy.2, Real.pi_pos]⟩ hxy
  have hsin : Real.sin x < Real.sin y :=
    Real.strictMonoOn_sin ⟨by linarith [hx.1, Real.pi_pos], le_of_lt hx.2⟩
      ⟨by linarith [hy.1, Real.pi_pos], le_of_lt hy.2⟩ hxy
  have hsin3 : Real.sin x ^ 3 < Real.sin y ^ 3 :=
    pow_lt_pow_left₀ hsin (le_of_lt hsx) (by norm_num)
  rw [div_lt_div_iff₀ (pow_pos hsy 3) (pow_pos hsx 3)]
  calc
    Real.cos y * Real.sin x ^ 3 < Real.cos x * Real.sin x ^ 3 :=
      mul_lt_mul_of_pos_right hcos (pow_pos hsx 3)
    _ < Real.cos x * Real.sin y ^ 3 :=
      mul_lt_mul_of_pos_left hsin3 hcx

/-- Complex exponential expression for `trigF y / I`: with `z = exp (y * I)`,
`-4 * (z + z⁻¹) / (z - z⁻¹)^3 = (trigF y : ℂ) / I`. -/
lemma trigF_complex_eq (y : ℝ) (hsin : Real.sin y ≠ 0) :
    let z : ℂ := Complex.exp ((y : ℂ) * Complex.I)
    (-4 : ℂ) * (z + z⁻¹) / (z - z⁻¹) ^ 3 = ((trigF y : ℝ) : ℂ) / Complex.I := by
  intro z
  have hz_inv : z⁻¹ = Complex.exp (-(y : ℂ) * Complex.I) := by
    dsimp only [z]
    rw [← Complex.exp_neg]
    congr 1; ring
  have hadd : z + z⁻¹ = 2 * Complex.cos (y : ℂ) := by
    rw [hz_inv, Complex.cos]
    dsimp only [z]
    ring
  have hsub : z - z⁻¹ = 2 * Complex.I * Complex.sin (y : ℂ) := by
    rw [hz_inv, Complex.sin]
    dsimp only [z]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    field_simp [Complex.I_ne_zero]
    ring_nf
    rw [hI2]
    ring
  rw [hadd, hsub]
  dsimp only [trigF]
  push_cast
  have hsinC : Complex.sin (y : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]
    exact Complex.ofReal_ne_zero.mpr hsin
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = (-1) * Complex.I := by rw [Complex.I_sq]
      _ = -Complex.I := by ring
  have hpow : (2 * Complex.I * Complex.sin (y : ℂ)) ^ 3 =
      (-8) * Complex.I * Complex.sin (y : ℂ) ^ 3 := by
    calc
      (2 * Complex.I * Complex.sin (y : ℂ)) ^ 3
          = 8 * Complex.I ^ 3 * Complex.sin (y : ℂ) ^ 3 := by ring
      _ = 8 * (-Complex.I) * Complex.sin (y : ℂ) ^ 3 := by rw [hI3]
      _ = (-8) * Complex.I * Complex.sin (y : ℂ) ^ 3 := by ring
  rw [hpow]
  field_simp [Complex.I_ne_zero, hsinC]
  ring

/-! ### Minimal polynomial degree equals Galois orbit size -/

/-- In any finite Galois extension `K / ℚ`, the degree of the minimal polynomial of `x : K`
over `ℚ` equals the cardinality of its Galois orbit `{σ x | σ : Gal(K/ℚ)}`. -/
theorem natDegree_minpoly_eq_card_orbit {K : Type*} [Field K] [DecidableEq K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (x : K) :
    (minpoly ℚ x).natDegree =
      (Finset.univ.image (fun σ : K ≃ₐ[ℚ] K => σ x)).card := by
  set S : Finset K := Finset.univ.image (fun σ : K ≃ₐ[ℚ] K => σ x)
  have hx_int : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hmin_ne : minpoly ℚ x ≠ 0 := minpoly.ne_zero hx_int
  have hle : (minpoly ℚ x).natDegree ≤ S.card := by
    let P : K[X] := ∏ y ∈ S, (Polynomial.X - Polynomial.C y)
    have hP_monic : P.Monic := Polynomial.monic_prod_of_monic S _ fun y _ => Polynomial.monic_X_sub_C y
    have hP_deg : P.natDegree = S.card := by
      rw [Polynomial.natDegree_prod_of_monic S _ fun y _ => Polynomial.monic_X_sub_C y]
      simp
    have hP_fix : ∀ (σ : K ≃ₐ[ℚ] K), P.map σ.toRingHom = P := by
      intro σ
      dsimp only [P]
      rw [Polynomial.map_prod]
      refine Finset.prod_bij (fun y _ => σ y) ?_ ?_ ?_ (fun y _ => ?_)
      · intro y hy
        rcases Finset.mem_image.mp hy with ⟨τ, _, rfl⟩
        exact Finset.mem_image.mpr ⟨σ * τ, Finset.mem_univ _, rfl⟩
      · intro y₁ _ y₂ _ h; exact σ.injective h
      · intro y hy
        rcases Finset.mem_image.mp hy with ⟨τ, _, rfl⟩
        refine ⟨(σ⁻¹ * τ) x, Finset.mem_image.mpr ⟨σ⁻¹ * τ, Finset.mem_univ _, rfl⟩, ?_⟩
        simp
      · simp
    have hcoeff_rat : ∀ n : ℕ, ∃ q : ℚ, algebraMap ℚ K q = P.coeff n := by
      intro n
      have hmem : P.coeff n ∈ IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[ℚ] K)) := by
        intro ⟨σ, _⟩
        have h := congrArg (fun f : K[X] => f.coeff n) (hP_fix σ)
        simpa [Polynomial.coeff_map] using h
      rw [IsGalois.fixedField_top] at hmem
      exact IntermediateField.mem_bot.mp hmem
    choose qf hqf using hcoeff_rat
    let Q : ℚ[X] := ∑ n ∈ P.support, Polynomial.monomial n (qf n)
    have hQ_map : Q.map (algebraMap ℚ K) = P := by
      ext n
      rw [Polynomial.coeff_map]
      dsimp only [Q]
      rw [Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_monomial]
      rw [Finset.sum_ite_eq']
      by_cases hn : n ∈ P.support
      · rw [if_pos hn, hqf n]
      · rw [if_neg hn, map_zero]
        exact (Polynomial.notMem_support_iff.mp hn).symm
    have hQ_ne : Q ≠ 0 := by
      intro h0
      rw [h0, Polynomial.map_zero] at hQ_map
      exact hP_monic.ne_zero hQ_map.symm
    have hQ_deg : Q.natDegree = S.card := by
      rw [← hP_deg, ← hQ_map, Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ K).injective]
    have hQx : Polynomial.aeval x Q = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hQ_map]
      dsimp only [P]
      rw [Polynomial.eval_prod]
      refine Finset.prod_eq_zero (i := x) ?_ (by simp)
      exact Finset.mem_image.mpr ⟨AlgEquiv.refl, Finset.mem_univ _, rfl⟩
    have hdvd : minpoly ℚ x ∣ Q := minpoly.dvd ℚ x hQx
    have := Polynomial.natDegree_le_of_dvd hdvd hQ_ne
    omega
  have hge : S.card ≤ (minpoly ℚ x).natDegree := by
    let M : K[X] := (minpoly ℚ x).map (algebraMap ℚ K)
    have hM_ne : M ≠ 0 := Polynomial.map_ne_zero hmin_ne
    have hsub : S ⊆ M.roots.toFinset := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨σ, _, rfl⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hM_ne, Polynomial.IsRoot]
      have haev : Polynomial.aeval (σ x) (minpoly ℚ x) = 0 := by
        rw [show σ x = σ.toAlgHom x from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at haev
      exact haev
    calc
      S.card ≤ M.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ M.roots.card := Multiset.toFinset_card_le _
      _ ≤ M.natDegree := Polynomial.card_roots' M
      _ = (minpoly ℚ x).natDegree :=
        Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ K).injective _
  exact le_antisymm hle hge

/-! ### Counting odd coprime residues below `N₀` -/

/-- The set `J'(N₀) = {j ∈ (0, N₀) | Odd j ∧ j.Coprime N₀}`. -/
def oddUnitsBelow (N₀ : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 N₀).filter fun j => Odd j ∧ j.Coprime N₀

lemma card_oddUnitsBelow_even {N₀ : ℕ} (hN₀ : 2 ≤ N₀) (heven : Even N₀) :
    (oddUnitsBelow N₀).card = Nat.totient N₀ := by
  rw [Nat.totient_eq_card_coprime]
  dsimp only [oddUnitsBelow]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, hj⟩, _, hcop⟩
    exact ⟨hj, hcop.symm⟩
  · rintro ⟨hj, hcop⟩
    have hj0 : 0 < j := by
      by_contra h0
      have hjz : j = 0 := by omega
      subst hjz
      have : N₀ = 1 := by simpa using hcop
      omega
    have hodd : Odd j := by
      rcases heven with ⟨r, hr⟩
      by_contra hnot
      rw [Nat.not_odd_iff_even] at hnot
      rcases hnot with ⟨s, hs⟩
      have hdvd : 2 ∣ Nat.gcd N₀ j := Nat.dvd_gcd ⟨r, by omega⟩ ⟨s, by omega⟩
      rw [hcop.gcd_eq_one] at hdvd
      omega
    exact ⟨⟨hj0, hj⟩, hodd, hcop.symm⟩

lemma two_mul_card_oddUnitsBelow_odd {N₀ : ℕ} (hN₀ : 3 ≤ N₀) (hodd : Odd N₀) :
    2 * (oddUnitsBelow N₀).card = Nat.totient N₀ := by
  let U := (Finset.Ioo 0 N₀).filter fun j => j.Coprime N₀
  let E := (Finset.Ioo 0 N₀).filter fun j => Even j ∧ j.Coprime N₀
  have hU_card : U.card = Nat.totient N₀ := by
    rw [Nat.totient_eq_card_coprime]
    dsimp only [U]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hj⟩, hcop⟩; exact ⟨hj, hcop.symm⟩
    · rintro ⟨hj, hcop⟩
      have hj0 : 0 < j := by
        by_contra h0
        have hjz : j = 0 := by omega
        subst hjz
        have : N₀ = 1 := by simpa using hcop
        omega
      exact ⟨⟨hj0, hj⟩, hcop.symm⟩
  have hdisj : Disjoint (oddUnitsBelow N₀) E := by
    rw [Finset.disjoint_left]
    intro j hjO hjE
    have h1 := (Finset.mem_filter.mp hjO).2.1
    have h2 := (Finset.mem_filter.mp hjE).2.1
    rcases h1 with ⟨a, ha⟩; rcases h2 with ⟨b, hb⟩; omega
  have hunion : oddUnitsBelow N₀ ∪ E = U := by
    ext j
    simp only [Finset.mem_union, oddUnitsBelow, E, U, Finset.mem_filter, Finset.mem_Ioo]
    constructor
    · rintro (⟨hI, _, hc⟩ | ⟨hI, _, hc⟩) <;> exact ⟨hI, hc⟩
    · rintro ⟨hI, hc⟩
      rcases Nat.even_or_odd j with he | ho
      · exact Or.inr ⟨hI, he, hc⟩
      · exact Or.inl ⟨hI, ho, hc⟩
  have hbij : (oddUnitsBelow N₀).card = E.card := by
    refine Finset.card_bij (fun j _ => N₀ - j) ?_ ?_ ?_
    · intro j hj
      simp only [oddUnitsBelow, E, Finset.mem_filter, Finset.mem_Ioo] at hj ⊢
      rcases hj with ⟨⟨hj0, hjN⟩, hjodd, hcop⟩
      refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
      · rcases hodd with ⟨a, ha⟩; rcases hjodd with ⟨b, hb⟩; exact ⟨a - b, by omega⟩
      · have hcop' : (N₀ - j).Coprime N₀ := by
          rw [Nat.coprime_comm]
          have := (Nat.coprime_self_sub_right (le_of_lt hjN)).mpr hcop.symm
          exact this
        exact hcop'
    · intro j₁ hj₁ j₂ hj₂ h
      have h1 := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hj₁).1).2
      have h2 := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hj₂).1).2
      omega
    · intro j hj
      simp only [oddUnitsBelow, E, Finset.mem_filter, Finset.mem_Ioo] at hj ⊢
      rcases hj with ⟨⟨hj0, hjN⟩, hjeven, hcop⟩
      refine ⟨N₀ - j, ⟨⟨by omega, by omega⟩, ?_, ?_⟩, by omega⟩
      · rcases hodd with ⟨a, ha⟩; rcases hjeven with ⟨b, hb⟩; exact ⟨a - b, by omega⟩
      · rw [Nat.coprime_comm]
        exact (Nat.coprime_self_sub_right (le_of_lt hjN)).mpr hcop.symm
  have hcard_union := Finset.card_union_of_disjoint hdisj
  rw [hunion, hU_card, ← hbij] at hcard_union
  omega

/-! ### Cyclotomic field setup and explicit Gauss-sum representation of `i√(2N)` -/

/-- Sign character of `√2 = ζ₈ + ζ₈⁻¹` under `σ_a`: `+1` for `a ≡ ±1 (mod 8)`, `-1` for `a ≡ ±3 (mod 8)`. -/
def chi2Sign (a : ℕ) : ℤ :=
  if a % 8 = 1 ∨ a % 8 = 7 then 1 else -1

/-- Sign character of `i = ζ₄` under `σ_a`: `+1` for `a ≡ 1 (mod 4)`, `-1` for `a ≡ 3 (mod 4)`. -/
def chi4Sign (a : ℕ) : ℤ :=
  if a % 4 = 1 then 1 else -1

/-- Quadratic character `(a / p)` as an integer, defaulting to `1` when `p` is not prime. -/
noncomputable def legendreInt (p a : ℕ) : ℤ :=
  if hp : p.Prime then
    have : Fact p.Prime := ⟨hp⟩
    quadraticChar (ZMod p) (a : ZMod p)
  else 1

lemma legendreInt_of_prime {p : ℕ} [Fact p.Prime] (a : ℕ) :
    legendreInt p a = quadraticChar (ZMod p) (a : ZMod p) := by
  dsimp only [legendreInt]
  rw [dif_pos (Fact.out : p.Prime)]

lemma legendreInt_one (p : ℕ) : legendreInt p 1 = 1 := by
  dsimp only [legendreInt]
  split_ifs with hp
  · have : Fact p.Prime := ⟨hp⟩
    simp
  · rfl

lemma legendreInt_mod (p a : ℕ) : legendreInt p (a % p) = legendreInt p a := by
  dsimp only [legendreInt]
  split_ifs with hp
  · have : Fact p.Prime := ⟨hp⟩
    simp [ZMod.natCast_mod]
  · rfl

/-- Prime-factorization decomposition `2 N = m² · 2^ε · ∏_{p ∈ S} p` where `S` is the set
of odd primes dividing `N` to an odd power. -/
lemma two_mul_factorization_decomp {N : ℕ} (hN : 0 < N) :
    let n := 2 * N
    let m := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
    let S := n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)
    2 * N = m ^ 2 * (if Odd (n.factorization 2) then 2 else 1) * ∏ p ∈ S, p := by
  intro n m S
  have hn0 : n ≠ 0 := by omega
  have hprod : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n :=
    Nat.prod_factorization_pow_eq_self hn0
  have hsplit : ∀ p ∈ n.primeFactors,
      p ^ (n.factorization p) =
        (p ^ (n.factorization p / 2)) ^ 2 * (if Odd (n.factorization p) then p else 1) := by
    intro p _
    by_cases ho : Odd (n.factorization p)
    · rw [if_pos ho, ← pow_mul, ← pow_succ]
      congr 1
      rcases ho with ⟨r, hr⟩
      omega
    · rw [if_neg ho, mul_one, ← pow_mul]
      congr 1
      rw [Nat.not_odd_iff_even] at ho
      rcases ho with ⟨r, hr⟩
      omega
  have h2mem : 2 ∈ n.primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.prime_two, dvd_mul_right 2 N, hn0⟩
  have h1 : n = m ^ 2 * ∏ p ∈ n.primeFactors, (if Odd (n.factorization p) then p else 1) := by
    calc
      n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := hprod.symm
      _ = ∏ p ∈ n.primeFactors,
            ((p ^ (n.factorization p / 2)) ^ 2 * (if Odd (n.factorization p) then p else 1)) :=
            Finset.prod_congr rfl hsplit
      _ = (∏ p ∈ n.primeFactors, (p ^ (n.factorization p / 2)) ^ 2) *
            ∏ p ∈ n.primeFactors, (if Odd (n.factorization p) then p else 1) :=
            Finset.prod_mul_distrib
      _ = m ^ 2 * ∏ p ∈ n.primeFactors, (if Odd (n.factorization p) then p else 1) := by
            rw [Finset.prod_pow]
  have h2 : ∏ p ∈ n.primeFactors, (if Odd (n.factorization p) then p else 1) =
      (if Odd (n.factorization 2) then 2 else 1) * ∏ p ∈ S, p := by
    rw [← Finset.mul_prod_erase _ _ h2mem]
    congr 1
    rw [← Finset.prod_filter]
    congr 1
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_erase]
    tauto
  calc
    2 * N = n := rfl
    _ = m ^ 2 * ∏ p ∈ n.primeFactors, (if Odd (n.factorization p) then p else 1) := h1
    _ = m ^ 2 * ((if Odd (n.factorization 2) then 2 else 1) * ∏ p ∈ S, p) := by rw [h2]
    _ = m ^ 2 * (if Odd (n.factorization 2) then 2 else 1) * ∏ p ∈ S, p := by rw [mul_assoc]

/-- The Galois automorphism `σ_a` of `CyclotomicField (8 * N) ℚ / ℚ` corresponding to
`a ∈ (ZMod (8 * N))ˣ`, packaged as a `MulEquiv`. -/
noncomputable def cycAut (N : ℕ) (hN : 3 ≤ N)
    [NeZero (8 * N)] [IsCyclotomicExtension {8 * N} ℚ (CyclotomicField (8 * N) ℚ)] :
    (ZMod (8 * N))ˣ ≃* (CyclotomicField (8 * N) ℚ ≃ₐ[ℚ] CyclotomicField (8 * N) ℚ) :=
  (IsCyclotomicExtension.autEquivPow (CyclotomicField (8 * N) ℚ)
    (Polynomial.cyclotomic.irreducible_rat (by omega))).symm

/-- `cycAut N hN a` sends the canonical primitive `(8 * N)`-th root `ζ` to `ζ ^ a.val.val`. -/
lemma cycAut_zeta (N : ℕ) (hN : 3 ≤ N)
    [NeZero (8 * N)] [IsCyclotomicExtension {8 * N} ℚ (CyclotomicField (8 * N) ℚ)]
    (a : (ZMod (8 * N))ˣ) :
    cycAut N hN a (IsCyclotomicExtension.zeta (8 * N) ℚ (CyclotomicField (8 * N) ℚ)) =
      (IsCyclotomicExtension.zeta (8 * N) ℚ (CyclotomicField (8 * N) ℚ)) ^ a.val.val := by
  have hζ := IsCyclotomicExtension.zeta_spec (8 * N) ℚ (CyclotomicField (8 * N) ℚ)
  have hspec := hζ.autToPow_spec ℚ (cycAut N hN a)
  have hright :
      IsCyclotomicExtension.autEquivPow (CyclotomicField (8 * N) ℚ)
        (Polynomial.cyclotomic.irreducible_rat (by omega)) (cycAut N hN a) = a :=
    (IsCyclotomicExtension.autEquivPow (CyclotomicField (8 * N) ℚ)
      (Polynomial.cyclotomic.irreducible_rat (by omega))).apply_symm_apply a
  have hpow : hζ.autToPow ℚ (cycAut N hN a) = a := hright
  rw [hpow] at hspec
  exact hspec.symm

open Classical in
/-- Explicit character `χ_N : (ZMod (8 * N))ˣ → ℤ` governing `σ_a(i √(2 N)) = χ_N(a) · i √(2 N)`. -/
noncomputable def sqrtNegTwoMulChar (N : ℕ) (a : (ZMod (8 * N))ˣ) : ℤ :=
  let S := (2 * N).primeFactors.filter fun p => p ≠ 2 ∧ Odd ((2 * N).factorization p)
  let r := (S.filter fun p => p % 4 = 3).card
  (if Odd ((2 * N).factorization 2) then chi2Sign a.val.val else 1) *
    (chi4Sign a.val.val) ^ (1 + r) *
    ∏ p ∈ S, legendreInt p a.val.val

open Classical in
/-- Helper: in `CyclotomicField (8 * N) ℚ`, build an element `α` with `α ^ 2 = -(2 * N)`
and `cycAut N hN a α = (sqrtNegTwoMulChar N a : K) * α`. -/
lemma exists_sqrt_neg_two_mul_in_cyclotomic (N : ℕ) (hN : 3 ≤ N)
    [NeZero (8 * N)] [IsCyclotomicExtension {8 * N} ℚ (CyclotomicField (8 * N) ℚ)] :
    ∃ α : CyclotomicField (8 * N) ℚ, α ^ 2 = -((2 * N : ℕ) : CyclotomicField (8 * N) ℚ) ∧
      ∀ a : (ZMod (8 * N))ˣ,
        cycAut N hN a α = ((sqrtNegTwoMulChar N a : ℤ) : CyclotomicField (8 * N) ℚ) * α := by
  let K := CyclotomicField (8 * N) ℚ
  set S := (2 * N).primeFactors.filter fun p => p ≠ 2 ∧ Odd ((2 * N).factorization p)
  set r := (S.filter fun p => p % 4 = 3).card
  let twoOdd : Prop := Odd ((2 * N).factorization 2)
  set ζ : K := IsCyclotomicExtension.zeta (8 * N) ℚ (CyclotomicField (8 * N) ℚ)
  have hζ : IsPrimitiveRoot ζ (8 * N) :=
    IsCyclotomicExtension.zeta_spec (8 * N) ℚ (CyclotomicField (8 * N) ℚ)
  set iK : K := ζ ^ (2 * N)
  have hneg1 : ζ ^ (4 * N) = -1 := by
    have hsq : (ζ ^ (4 * N)) ^ 2 = 1 := by
      rw [← pow_mul, show 4 * N * 2 = 8 * N by omega]
      exact hζ.pow_eq_one
    have hne : ζ ^ (4 * N) ≠ 1 := by
      intro h1
      have hdvd : 8 * N ∣ 4 * N := hζ.dvd_of_pow_eq_one (4 * N) h1
      have hle : 8 * N ≤ 4 * N := Nat.le_of_dvd (by omega) hdvd
      omega
    rcases sq_eq_one_iff.mp hsq with h1 | hm1
    · exact False.elim (hne h1)
    · exact hm1
  have hiK_sq : iK ^ 2 = -1 := by
    dsimp only [iK]
    rw [← pow_mul, show 2 * N * 2 = 4 * N by omega, hneg1]
  have hiK_pow4 : iK ^ 4 = 1 := by
    calc
      iK ^ 4 = (iK ^ 2) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [hiK_sq]
      _ = 1 := by ring
  set z8 : K := ζ ^ N
  have hz8_4 : z8 ^ 4 = -1 := by
    dsimp only [z8]
    rw [← pow_mul, show N * 4 = 4 * N by omega, hneg1]
  have hz8_8 : z8 ^ 8 = 1 := by
    calc
      z8 ^ 8 = (z8 ^ 4) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [hz8_4]
      _ = 1 := by ring
  set s2K : K := z8 + z8 ^ 7
  have hs2K_sq : s2K ^ 2 = 2 := by
    dsimp only [s2K]
    have h2 : z8 ^ 2 + z8 ^ 14 = 0 := by
      calc
        z8 ^ 2 + z8 ^ 14 = z8 ^ 2 * (1 + (z8 ^ 4) ^ 3) := by ring
        _ = z8 ^ 2 * (1 + (-1) ^ 3) := by rw [hz8_4]
        _ = 0 := by ring
    calc
      (z8 + z8 ^ 7) ^ 2 = (z8 ^ 2 + z8 ^ 14) + 2 * z8 ^ 8 := by ring
      _ = 0 + 2 * 1 := by rw [h2, hz8_8]
      _ = 2 := by ring
  have ha_odd : ∀ a : (ZMod (8 * N))ˣ, a.val.val % 2 = 1 := by
    intro a
    have hcop : Nat.Coprime a.val.val (8 * N) := ZMod.val_coe_unit_coprime a
    have h2 : Nat.Coprime a.val.val 2 := hcop.coprime_dvd_right (by omega : 2 ∣ 8 * N)
    have hnot2 : ¬ 2 ∣ a.val.val := fun hd => by
      have := Nat.dvd_gcd hd (dvd_refl 2)
      rw [h2.gcd_eq_one] at this
      omega
    omega
  have hσ_iK : ∀ a : (ZMod (8 * N))ˣ, cycAut N hN a iK = ((chi4Sign a.val.val : ℤ) : K) * iK := by
    intro a
    have hpow : cycAut N hN a iK = iK ^ a.val.val := by
      dsimp only [iK]
      rw [map_pow, cycAut_zeta N hN a, ← pow_mul, mul_comm a.val.val (2 * N), pow_mul]
    rw [hpow]
    have hdiv : a.val.val = 4 * (a.val.val / 4) + a.val.val % 4 := (Nat.div_add_mod _ 4).symm
    have hred : iK ^ a.val.val = iK ^ (a.val.val % 4) := by
      conv_lhs => rw [hdiv, pow_add, pow_mul, hiK_pow4, one_pow, one_mul]
    rw [hred]
    have hodd := ha_odd a
    have hcases : a.val.val % 4 = 1 ∨ a.val.val % 4 = 3 := by omega
    rcases hcases with h1 | h3
    · simp only [chi4Sign, h1, ↓reduceIte, Int.cast_one, one_mul, pow_one]
    · simp only [chi4Sign, h3, show ¬ (3 = 1) by decide, ↓reduceIte, Int.cast_neg, Int.cast_one,
        neg_one_mul]
      calc
        iK ^ 3 = iK ^ 2 * iK := by ring
        _ = (-1) * iK := by rw [hiK_sq]
        _ = -iK := by ring
  have hσ_s2K : ∀ a : (ZMod (8 * N))ˣ, cycAut N hN a s2K = ((chi2Sign a.val.val : ℤ) : K) * s2K := by
    intro a
    have hpow : ∀ e : ℕ, cycAut N hN a (z8 ^ e) = z8 ^ ((a.val.val * e) % 8) := by
      intro e
      have h1 : cycAut N hN a (z8 ^ e) = z8 ^ (a.val.val * e) := by
        dsimp only [z8]
        rw [map_pow, map_pow, cycAut_zeta N hN a, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1; ring
      rw [h1]
      have hdiv : a.val.val * e = 8 * (a.val.val * e / 8) + (a.val.val * e) % 8 :=
        (Nat.div_add_mod _ 8).symm
      conv_lhs => rw [hdiv, pow_add, pow_mul, hz8_8, one_pow, one_mul]
    have hσs : cycAut N hN a s2K = z8 ^ (a.val.val % 8) + z8 ^ ((a.val.val * 7) % 8) := by
      dsimp only [s2K]
      rw [map_add, ← pow_one z8, hpow 1, pow_one, mul_one, hpow 7]
    rw [hσs]
    have hodd := ha_odd a
    have hcases : a.val.val % 8 = 1 ∨ a.val.val % 8 = 3 ∨ a.val.val % 8 = 5 ∨ a.val.val % 8 = 7 := by
      omega
    have hmod7 : (a.val.val * 7) % 8 = ((a.val.val % 8) * 7) % 8 := by
      rw [Nat.mul_mod, show 7 % 8 = 7 by decide]
    rw [hmod7]
    rcases hcases with h1 | h3 | h5 | h7
    · rw [chi2Sign, h1, if_pos (Or.inl rfl), show (1 * 7) % 8 = 7 by decide]
      simp [s2K]
    · rw [chi2Sign, h3, if_neg (by decide), show (3 * 7) % 8 = 5 by decide]
      simp only [Int.cast_neg, Int.cast_one, neg_one_mul, s2K]
      have hstep : z8 ^ 4 * z8 ^ 7 = z8 ^ 8 * z8 ^ 3 := by ring
      calc
        z8 ^ 3 + z8 ^ 5 = z8 ^ 8 * z8 ^ 3 + z8 ^ 4 * z8 := by rw [hz8_8]; ring
        _ = z8 ^ 4 * z8 ^ 7 + z8 ^ 4 * z8 := by rw [← hstep]
        _ = z8 ^ 4 * (z8 ^ 7 + z8) := by ring
        _ = (-1) * (z8 ^ 7 + z8) := by rw [hz8_4]
        _ = -(z8 + z8 ^ 7) := by ring
    · rw [chi2Sign, h5, if_neg (by decide), show (5 * 7) % 8 = 3 by decide]
      simp only [Int.cast_neg, Int.cast_one, neg_one_mul, s2K]
      have hstep : z8 ^ 4 * z8 ^ 7 = z8 ^ 8 * z8 ^ 3 := by ring
      calc
        z8 ^ 5 + z8 ^ 3 = z8 ^ 4 * z8 + z8 ^ 8 * z8 ^ 3 := by rw [hz8_8]; ring
        _ = z8 ^ 4 * z8 + z8 ^ 4 * z8 ^ 7 := by rw [← hstep]
        _ = z8 ^ 4 * (z8 + z8 ^ 7) := by ring
        _ = (-1) * (z8 + z8 ^ 7) := by rw [hz8_4]
        _ = -(z8 + z8 ^ 7) := by ring
    · rw [chi2Sign, h7, if_pos (Or.inr rfl), show (7 * 7) % 8 = 1 by decide]
      simp [s2K, add_comm]
  have hp_info : ∀ p ∈ S, p.Prime ∧ p ≠ 2 ∧ p ∣ 8 * N := by
    intro p hp
    simp only [S, Finset.mem_filter, Nat.mem_primeFactors] at hp
    refine ⟨hp.1.1, hp.2.1, dvd_trans hp.1.2.1 ⟨4, by omega⟩⟩
  let gp : ℕ → K := fun p =>
    if h : p ∈ S then
      have : Fact p.Prime := ⟨(hp_info p h).1⟩
      have : NeZero p := ⟨(hp_info p h).1.ne_zero⟩
      let ζp : K := ζ ^ (8 * N / p)
      have hζp : IsPrimitiveRoot ζp p := by
        have hdiv : 8 * N / p * p = 8 * N := Nat.div_mul_cancel (hp_info p h).2.2
        have hne : 8 * N / p ≠ 0 := by intro hz; rw [hz, zero_mul] at hdiv; omega
        have := hζ.pow_of_dvd hne (Nat.div_dvd_of_dvd (hp_info p h).2.2)
        rwa [Nat.div_div_self (hp_info p h).2.2 (by omega)] at this
      gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom K))
        (AddChar.zmodChar p hζp.pow_eq_one)
    else 1
  have hgp_sq : ∀ p ∈ S, gp p ^ 2 = (if p % 4 = 3 then (-1 : K) else 1) * (p : K) := by
    intro p hp
    have hp_prime : p.Prime := (hp_info p hp).1
    have hp_ne2 : p ≠ 2 := (hp_info p hp).2.1
    have : Fact p.Prime := ⟨hp_prime⟩
    have : NeZero p := ⟨hp_prime.ne_zero⟩
    have hchar_ne2 : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp_ne2
    dsimp only [gp]
    rw [dif_pos hp]
    set ζp : K := ζ ^ (8 * N / p)
    have hζp : IsPrimitiveRoot ζp p := by
      have hdiv : 8 * N / p * p = 8 * N := Nat.div_mul_cancel (hp_info p hp).2.2
      have hne : 8 * N / p ≠ 0 := by intro hz; rw [hz, zero_mul] at hdiv; omega
      have := hζ.pow_of_dvd hne (Nat.div_dvd_of_dvd (hp_info p hp).2.2)
      rwa [Nat.div_div_self (hp_info p hp).2.2 (by omega)] at this
    set χK := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom K)
    set ψK := AddChar.zmodChar p hζp.pow_eq_one
    have hχ_ne : χK ≠ 1 := by
      rw [MulChar.ringHomComp_ne_one_iff Int.cast_injective]
      exact quadraticChar_ne_one hchar_ne2
    have hχ_quad : χK.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
    have hψ_prim : ψK.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hζp
    have hsq := gaussSum_sq hχ_ne hχ_quad hψ_prim
    rw [ZMod.card p] at hsq
    rw [hsq]
    congr 1
    change ((quadraticChar (ZMod p) (-1) : ℤ) : K) = if p % 4 = 3 then (-1 : K) else 1
    rw [quadraticChar_neg_one hchar_ne2, ZMod.card p]
    have hodd_p : p % 2 = 1 := hp_prime.eq_two_or_odd.resolve_left hp_ne2
    by_cases h3 : p % 4 = 3
    · rw [if_pos h3]; simp [ZMod.χ₄_nat_three_mod_four h3]
    · rw [if_neg h3]
      have h1 : p % 4 = 1 := by omega
      simp [ZMod.χ₄_nat_one_mod_four h1]
  have hσ_gp : ∀ p ∈ S, ∀ a : (ZMod (8 * N))ˣ,
      cycAut N hN a (gp p) = ((legendreInt p a.val.val : ℤ) : K) * gp p := by
    intro p hp a
    have hp_prime : p.Prime := (hp_info p hp).1
    have : Fact p.Prime := ⟨hp_prime⟩
    have : NeZero p := ⟨hp_prime.ne_zero⟩
    rw [legendreInt_of_prime]
    dsimp only [gp]
    rw [dif_pos hp]
    set ζp : K := ζ ^ (8 * N / p)
    have hζp : IsPrimitiveRoot ζp p := by
      have hdiv : 8 * N / p * p = 8 * N := Nat.div_mul_cancel (hp_info p hp).2.2
      have hne : 8 * N / p ≠ 0 := by intro hz; rw [hz, zero_mul] at hdiv; omega
      have := hζ.pow_of_dvd hne (Nat.div_dvd_of_dvd (hp_info p hp).2.2)
      rwa [Nat.div_div_self (hp_info p hp).2.2 (by omega)] at this
    set χK := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom K)
    set ψK := AddChar.zmodChar p hζp.pow_eq_one
    have ha_cop : Nat.Coprime a.val.val p :=
      (ZMod.val_coe_unit_coprime a).coprime_dvd_right (hp_info p hp).2.2
    let ap : (ZMod p)ˣ := ZMod.unitOfCoprime a.val.val ha_cop
    have hmap : cycAut N hN a (gaussSum χK ψK) = gaussSum χK (ψK.mulShift (ap : ZMod p)) := by
      dsimp only [gaussSum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul]
      have hχ_fix : cycAut N hN a (χK x) = χK x := by
        change cycAut N hN a ((quadraticChar (ZMod p) x : ℤ) : K) = ((quadraticChar (ZMod p) x : ℤ) : K)
        exact map_intCast _ _
      rw [hχ_fix]
      congr 1
      rw [AddChar.mulShift_apply, AddChar.zmodChar_apply, AddChar.zmodChar_apply]
      have hmod : ((ap : ZMod p) * x).val % p = (a.val.val * x.val) % p := by
        have h1 : ((ap : ZMod p) * x : ZMod p) = ((a.val.val * x.val : ℕ) : ZMod p) := by
          simp [ap, ZMod.coe_unitOfCoprime]
        exact (ZMod.natCast_eq_natCast_iff ((ap : ZMod p) * x).val (a.val.val * x.val) p).mp
          (by rw [ZMod.natCast_zmod_val, h1])
      have hpow_red : ∀ t : ℕ, ζp ^ t = ζp ^ (t % p) := fun t => by
        conv_lhs => rw [← Nat.div_add_mod t p, pow_add, pow_mul, hζp.pow_eq_one, one_pow, one_mul]
      have hpow_mod : ζp ^ ((ap : ZMod p) * x).val = ζp ^ (a.val.val * x.val) := by
        rw [hpow_red ((ap : ZMod p) * x).val, hpow_red (a.val.val * x.val), hmod]
      rw [hpow_mod]
      dsimp only [ζp]
      rw [map_pow, map_pow, cycAut_zeta N hN a, ← pow_mul, ← pow_mul, ← pow_mul]
      congr 1; ring
    rw [hmap, gaussSum_mulShift_eq χK ψK ap]
    have hquad : χK.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
    rw [hquad.inv]
    simp only [χK, MulChar.ringHomComp, MulChar.coe_mk, Int.coe_castRingHom, ap,
      ZMod.coe_unitOfCoprime]
    rfl
  let m : ℕ := ∏ p ∈ (2 * N).primeFactors, p ^ ((2 * N).factorization p / 2)
  let α : K :=
    (m : K) * (if twoOdd then s2K else 1) * iK ^ (1 + r) * ∏ p ∈ S, gp p
  refine ⟨α, ?_, ?_⟩
  · have hprod_sq : (∏ p ∈ S, gp p) ^ 2 = ((-1 : K) ^ r) * ((∏ p ∈ S, p : ℕ) : K) := by
      rw [← Finset.prod_pow]
      have hcongr : ∏ p ∈ S, gp p ^ 2 =
          ∏ p ∈ S, ((if p % 4 = 3 then (-1 : K) else 1) * (p : K)) :=
        Finset.prod_congr rfl fun p hp => hgp_sq p hp
      rw [hcongr, Finset.prod_mul_distrib, Nat.cast_prod]
      congr 1
      rw [← Finset.prod_filter, Finset.prod_const]
    have hi_sq : (iK ^ (1 + r)) ^ 2 = (-1 : K) ^ (1 + r) := by
      rw [← pow_mul, mul_comm (1 + r) 2, pow_mul, hiK_sq]
    have hs2_sq : (if twoOdd then s2K else 1) ^ 2 = ((if twoOdd then (2 : ℕ) else 1 : ℕ) : K) := by
      by_cases h : twoOdd <;> simp [h, hs2K_sq]
    have hdecomp := two_mul_factorization_decomp (show 0 < N by omega)
    have hdecompK : ((2 * N : ℕ) : K) =
        (m : K) ^ 2 * ((if twoOdd then (2 : ℕ) else 1 : ℕ) : K) * ((∏ p ∈ S, p : ℕ) : K) := by
      exact_mod_cast hdecomp
    have hsq4 : ∀ x0 x1 x2 x3 : K, (x0 * x1 * x2 * x3) ^ 2 = x0 ^ 2 * x1 ^ 2 * x2 ^ 2 * x3 ^ 2 :=
      fun _ _ _ _ => by ring
    have hrearr2 : ∀ x0 x1 s1 s2 x3 : K, x0 * x1 * s1 * (s2 * x3) = (s1 * s2) * (x0 * x1 * x3) :=
      fun _ _ _ _ _ => by ring
    calc
      α ^ 2 = (m : K) ^ 2 * (if twoOdd then s2K else 1) ^ 2 * (iK ^ (1 + r)) ^ 2 *
          (∏ p ∈ S, gp p) ^ 2 := hsq4 _ _ _ _
      _ = (m : K) ^ 2 * ((if twoOdd then (2 : ℕ) else 1 : ℕ) : K) * (-1 : K) ^ (1 + r) *
          ((-1 : K) ^ r * ((∏ p ∈ S, p : ℕ) : K)) := by rw [hs2_sq, hi_sq, hprod_sq]
      _ = ((-1 : K) ^ (1 + r) * (-1 : K) ^ r) *
          ((m : K) ^ 2 * ((if twoOdd then (2 : ℕ) else 1 : ℕ) : K) * ((∏ p ∈ S, p : ℕ) : K)) :=
        hrearr2 _ _ _ _ _
      _ = (-1 : K) * ((2 * N : ℕ) : K) := by
          rw [← hdecompK, ← pow_add, show 1 + r + r = 2 * r + 1 by omega, pow_add, pow_mul,
            neg_one_sq, one_pow, one_mul, pow_one]
      _ = -((2 * N : ℕ) : K) := neg_one_mul _
  · intro a
    dsimp only [α, sqrtNegTwoMulChar]
    rw [map_mul, map_mul, map_mul, map_natCast, map_pow, map_prod]
    have hs2_act : cycAut N hN a (if twoOdd then s2K else 1) =
        (((if twoOdd then chi2Sign a.val.val else 1 : ℤ) : K)) * (if twoOdd then s2K else 1) := by
      by_cases h : twoOdd
      · rw [if_pos h, if_pos h, hσ_s2K a]
      · rw [if_neg h, if_neg h, map_one]; simp
    have hi_act : cycAut N hN a iK ^ (1 + r) =
        (((chi4Sign a.val.val : ℤ) ^ (1 + r) : ℤ) : K) * iK ^ (1 + r) := by
      rw [hσ_iK a, mul_pow, Int.cast_pow]
    have hgp_act : ∏ p ∈ S, cycAut N hN a (gp p) =
        (((∏ p ∈ S, legendreInt p a.val.val : ℤ) : K)) * ∏ p ∈ S, gp p := by
      have hcongr : ∏ p ∈ S, cycAut N hN a (gp p) =
          ∏ p ∈ S, (((legendreInt p a.val.val : ℤ) : K) * gp p) :=
        Finset.prod_congr rfl fun p hp => hσ_gp p hp a
      rw [hcongr, Finset.prod_mul_distrib, Int.cast_prod]
    have hrearr : ∀ x0 c1 x1 c2 x2 c3 x3 : K,
        x0 * (c1 * x1) * (c2 * x2) * (c3 * x3) = (c1 * c2 * c3) * (x0 * x1 * x2 * x3) :=
      fun _ _ _ _ _ _ _ => by ring
    rw [hs2_act, hi_act, hgp_act, Int.cast_mul, Int.cast_mul]
    exact hrearr _ _ _ _ _ _ _

/-! ### Orbit reduction (Lemmas 1–4) -/

open Classical in
/-- Helper Lemma (Lemmas 1–4 combined): reduces `(minpoly ℚ (landscapeCoeff k N)).natDegree`
to the sign-flip criterion on `sqrtNegTwoMulChar N` over `{u ∈ (ZMod (8 * N))ˣ | u ≡ 1 mod 2 N₀}`. -/
lemma landscapeCoeff_degree_via_sign_flip (N k : ℕ) (hN : 3 ≤ N) (hk : Odd k) (hkN : k < N) :
    let d := Nat.gcd N k
    let N₀ := N / d
    (minpoly ℚ (landscapeCoeff k N)).natDegree =
      if ∃ u : (ZMod (8 * N))ˣ, u.val.val % (2 * N₀) = 1 ∧ sqrtNegTwoMulChar N u = -1
      then 2 * (oddUnitsBelow N₀).card
      else (oddUnitsBelow N₀).card := by
  intro d N₀
  have hk_pos : 0 < k := by rcases hk with ⟨t, rfl⟩; omega
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left k (by omega)
  have hd_dvd_N : d ∣ N := Nat.gcd_dvd_left N k
  have hd_dvd_k : d ∣ k := Nat.gcd_dvd_right N k
  have hN_eq : d * N₀ = N := Nat.mul_div_cancel' hd_dvd_N
  set k' : ℕ := k / d
  have hk_eq : d * k' = k := Nat.mul_div_cancel' hd_dvd_k
  have hk'_odd : Odd k' := by
    rcases hk with ⟨t, ht⟩
    by_contra hnot
    rw [Nat.not_odd_iff_even] at hnot
    rcases hnot with ⟨u, hu⟩
    have h2 : k = 2 * (d * u) := by rw [← hk_eq, hu]; ring
    omega
  have hk'_lt : k' < N₀ := by nlinarith
  have hk'_pos : 0 < k' := by rcases hk'_odd with ⟨t, ht⟩; omega
  have hN₀_ge2 : 2 ≤ N₀ := by omega
  have hcop_k' : k'.Coprime N₀ := (Nat.coprime_div_gcd_div_gcd hd_pos (m := N) (n := k)).symm
  have hk'_cop_2N₀ : k'.Coprime (2 * N₀) := by
    have h2 : k'.Coprime 2 := by
      rcases hk'_odd with ⟨u, hu⟩
      exact Nat.coprime_comm.mp (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
    exact h2.mul_right hcop_k'
  have : NeZero (8 * N) := ⟨by omega⟩
  have : NeZero ((8 * N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  have : IsCyclotomicExtension {8 * N} ℚ (CyclotomicField (8 * N) ℚ) :=
    CyclotomicField.isCyclotomicExtension (8 * N) ℚ
  let K := CyclotomicField (8 * N) ℚ
  have hirr : Irreducible (cyclotomic (8 * N) ℚ) := Polynomial.cyclotomic.irreducible_rat (by omega)
  set ζK : K := IsCyclotomicExtension.zeta (8 * N) ℚ (CyclotomicField (8 * N) ℚ)
  have hζK : IsPrimitiveRoot ζK (8 * N) :=
    IsCyclotomicExtension.zeta_spec (8 * N) ℚ (CyclotomicField (8 * N) ℚ)
  set ζC : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((8 * N : ℕ) : ℂ))
  have hζC : IsPrimitiveRoot ζC (8 * N) := Complex.isPrimitiveRoot_exp (8 * N) (by omega)
  have hmin_ζK : minpoly ℚ ζK = cyclotomic (8 * N) ℚ :=
    (hζK.minpoly_eq_cyclotomic_of_irreducible hirr).symm
  have haev_ζC : Polynomial.aeval ζC (minpoly ℚ (hζK.powerBasis ℚ).gen) = 0 := by
    rw [IsPrimitiveRoot.powerBasis_gen, hmin_ζK, Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζC.isRoot_cyclotomic (by omega)
  let ι : K →ₐ[ℚ] ℂ := (hζK.powerBasis ℚ).lift ζC haev_ζC
  have hι_ζK : ι ζK = ζC := by
    have := (hζK.powerBasis ℚ).lift_gen ζC haev_ζC
    simpa [IsPrimitiveRoot.powerBasis_gen] using this
  set S := (2 * N).primeFactors.filter fun p => p ≠ 2 ∧ Odd ((2 * N).factorization p)
  set r := (S.filter fun p => p % 4 = 3).card
  let twoOdd : Prop := Odd ((2 * N).factorization 2)
  obtain ⟨α_raw, hα_sq, hα_act⟩ := exists_sqrt_neg_two_mul_in_cyclotomic N hN
  have hχ_pm : ∀ a : (ZMod (8 * N))ˣ, sqrtNegTwoMulChar N a = 1 ∨ sqrtNegTwoMulChar N a = -1 := by
    intro a
    have h1 : (if twoOdd then chi2Sign a.val.val else 1) = 1 ∨
        (if twoOdd then chi2Sign a.val.val else 1) = -1 := by
      by_cases h : twoOdd
      · rw [if_pos h]; dsimp only [chi2Sign]; split_ifs <;> simp
      · rw [if_neg h]; left; rfl
    have h2 : (chi4Sign a.val.val) ^ (1 + r) = 1 ∨ (chi4Sign a.val.val) ^ (1 + r) = -1 := by
      dsimp only [chi4Sign]; split_ifs
      · left; simp
      · rcases Nat.even_or_odd (1 + r) with he | ho
        · left; exact he.neg_one_pow
        · right; exact ho.neg_one_pow
    have h3 : (∏ p ∈ S, legendreInt p a.val.val) = 1 ∨
        (∏ p ∈ S, legendreInt p a.val.val) = -1 := by
      have hsq : (∏ p ∈ S, legendreInt p a.val.val) ^ 2 = 1 := by
        rw [← Finset.prod_pow]
        refine Finset.prod_eq_one fun p hp => ?_
        have hp_mem : p.Prime ∧ p ∣ 2 * N := by
          simp only [S, Finset.mem_filter, Nat.mem_primeFactors] at hp
          exact ⟨hp.1.1, hp.1.2.1⟩
        have : Fact p.Prime := ⟨hp_mem.1⟩
        rw [legendreInt_of_prime]
        have hcop : Nat.Coprime a.val.val p :=
          (ZMod.val_coe_unit_coprime a).coprime_dvd_right (dvd_trans hp_mem.2 ⟨4, by omega⟩)
        have hne : (a.val.val : ZMod p) ≠ 0 := by
          intro hz
          have hdvd : p ∣ a.val.val := (ZMod.natCast_eq_zero_iff a.val.val p).mp hz
          have h1dvd : p ∣ 1 := by
            have := Nat.dvd_gcd hdvd (dvd_refl p)
            rwa [hcop.gcd_eq_one] at this
          exact hp_mem.1.not_dvd_one h1dvd
        exact quadraticChar_sq_one hne
      exact sq_eq_one_iff.mp hsq
    dsimp only [sqrtNegTwoMulChar]
    change (if twoOdd then chi2Sign a.val.val else 1) *
        (chi4Sign a.val.val) ^ (1 + r) *
        ∏ p ∈ S, legendreInt p a.val.val = 1 ∨
      (if twoOdd then chi2Sign a.val.val else 1) *
        (chi4Sign a.val.val) ^ (1 + r) *
        ∏ p ∈ S, legendreInt p a.val.val = -1
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      rw [h1, h2, h3] <;> norm_num
  have hια_sq : (ι α_raw) ^ 2 = (Complex.I * ((Real.sqrt (2 * (N : ℝ)) : ℝ) : ℂ)) ^ 2 := by
    rw [← map_pow, hα_sq, map_neg, map_natCast, mul_pow, Complex.I_sq]
    have hsq : ((Real.sqrt (2 * (N : ℝ)) : ℝ) : ℂ) ^ 2 = ((2 * (N : ℝ) : ℝ) : ℂ) := by
      norm_cast; exact Real.sq_sqrt (by positivity)
    rw [hsq]; push_cast; ring
  obtain ⟨α, hια, hσα⟩ :
      ∃ α : K, ι α = Complex.I * ((Real.sqrt (2 * (N : ℝ)) : ℝ) : ℂ) ∧
        ∀ a : (ZMod (8 * N))ˣ, cycAut N hN a α = ((sqrtNegTwoMulChar N a : ℤ) : K) * α := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hια_sq with hpos | hneg
    · exact ⟨α_raw, hpos, hα_act⟩
    · refine ⟨-α_raw, by rw [map_neg, hneg, neg_neg], fun a => ?_⟩
      rw [map_neg, hα_act a]; ring
  set zK : K := ζK ^ (2 * k)
  let gK : K := (-4 : K) * (zK + zK⁻¹) / (zK - zK⁻¹) ^ 3
  let cK : K := (1 / (4 * (N : K))) * α * gK
  have hι_zK_pow : ∀ m : ℕ,
      ι (ζK ^ m) = Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / ((8 * N : ℕ) : ℂ)) := by
    intro m
    rw [map_pow, hι_ζK]
    dsimp only [ζC]
    rw [← Complex.exp_nat_mul]
    congr 1; ring
  have hsin_ne : ∀ a : (ZMod (8 * N))ˣ,
      Real.sin ((a.val.val : ℝ) * (k' : ℝ) * Real.pi / (2 * (N₀ : ℝ))) ≠ 0 := by
    intro a h0
    rw [Real.sin_eq_zero_iff] at h0
    rcases h0 with ⟨m, hm⟩
    have hN₀R : (2 * (N₀ : ℝ)) ≠ 0 := by positivity
    have heqR : (a.val.val : ℝ) * (k' : ℝ) = (m : ℝ) * (2 * (N₀ : ℝ)) := by
      have := congrArg (· * (2 * (N₀ : ℝ))) hm
      field_simp [hN₀R, Real.pi_ne_zero] at this
      linarith
    have heqZ : (a.val.val : ℤ) * (k' : ℤ) = m * (2 * (N₀ : ℤ)) := by exact_mod_cast heqR
    have ha_odd : a.val.val % 2 = 1 := by
      have hcop : Nat.Coprime a.val.val (8 * N) := ZMod.val_coe_unit_coprime a
      have h2 : Nat.Coprime a.val.val 2 := hcop.coprime_dvd_right (by omega : 2 ∣ 8 * N)
      have hnot2 : ¬ 2 ∣ a.val.val := fun hd => by
        have := Nat.dvd_gcd hd (dvd_refl 2); rw [h2.gcd_eq_one] at this; omega
      omega
    rcases hk'_odd with ⟨u, hu⟩
    have hmod1 : ((a.val.val : ℤ) * (k' : ℤ)) % 2 = 1 := by
      have h1 : (a.val.val : ℤ) % 2 = 1 := by omega
      have h2 : (k' : ℤ) % 2 = 1 := by omega
      rw [Int.mul_emod, h1, h2]; norm_num
    have hmod0 : ((a.val.val : ℤ) * (k' : ℤ)) % 2 = 0 := by
      have h2m : m * (2 * (N₀ : ℤ)) = 2 * (m * (N₀ : ℤ)) := by ring
      rw [heqZ, h2m]
      omega
    omega
  have hangle_eq : ∀ m : ℕ,
      (m : ℝ) * (k : ℝ) * Real.pi / (2 * (N : ℝ)) = (m : ℝ) * (k' : ℝ) * Real.pi / (2 * (N₀ : ℝ)) := by
    intro m
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hNR : (N : ℝ) = (d : ℝ) * (N₀ : ℝ) := by exact_mod_cast hN_eq.symm
    have hkR : (k : ℝ) = (d : ℝ) * (k' : ℝ) := by exact_mod_cast hk_eq.symm
    rw [hNR, hkR]
    field_simp [hdR]
  let valR : (ZMod (8 * N))ˣ → ℝ := fun a =>
    (sqrtNegTwoMulChar N a : ℝ) * ((1 / 4 : ℝ) * Real.sqrt (2 / (N : ℝ)) *
      trigF ((a.val.val : ℝ) * (k' : ℝ) * Real.pi / (2 * (N₀ : ℝ))))
  have hι_σ_cK : ∀ a : (ZMod (8 * N))ˣ, ι (cycAut N hN a cK) = (valR a : ℂ) := by
    intro a
    dsimp only [cK, gK, zK, valR]
    simp only [map_mul, map_div₀, map_add, map_sub, map_pow, map_inv₀, map_neg, map_ofNat,
      map_natCast, map_one, hσα a]
    rw [map_intCast]
    have hpow_z : ι (cycAut N hN a ζK) ^ (2 * k) =
        Complex.exp ((((a.val.val : ℝ) * (k' : ℝ) * Real.pi / (2 * (N₀ : ℝ)) : ℝ) : ℂ) * Complex.I) := by
      rw [cycAut_zeta N hN a, ← map_pow, ← pow_mul, hι_zK_pow]
      congr 1
      have h1 := hangle_eq a.val.val
      have hNR : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hangleC :
          ((a.val.val : ℂ) * (k : ℂ) * (Real.pi : ℂ) / (2 * (N : ℂ))) =
          ((a.val.val : ℂ) * (k' : ℂ) * (Real.pi : ℂ) / (2 * (N₀ : ℂ))) := by
        exact_mod_cast h1
      push_cast
      rw [← hangleC]
      field_simp [hNR]
      ring
    rw [hpow_z]
    have hf := trigF_complex_eq ((a.val.val : ℝ) * (k' : ℝ) * Real.pi / (2 * (N₀ : ℝ))) (hsin_ne a)
    dsimp only at hf
    rw [hf, hια]
    have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hsqrt : Real.sqrt (2 / (N : ℝ)) = Real.sqrt (2 * (N : ℝ)) / (N : ℝ) := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hsN : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      field_simp [hsN, hNR]
      nlinarith [hsqN]
    rw [hsqrt]
    push_cast
    field_simp [Complex.I_ne_zero, hNC]
  have hχ_one : sqrtNegTwoMulChar N 1 = 1 := by
    have : Fact (1 < 8 * N) := ⟨by omega⟩
    have h1val : ((1 : (ZMod (8 * N))ˣ) : ZMod (8 * N)).val = 1 := ZMod.val_one (8 * N)
    dsimp only [sqrtNegTwoMulChar, chi2Sign, chi4Sign]
    rw [h1val]
    have hprod1 : ∏ p ∈ S, legendreInt p 1 = 1 := Finset.prod_eq_one fun p _ => legendreInt_one p
    rw [hprod1]
    simp
  have hι_cK : ι cK = (landscapeCoeff k N : ℂ) := by
    have h := hι_σ_cK 1
    have hσ1 : cycAut N hN 1 cK = cK := by rw [map_one]; rfl
    have : Fact (1 < 8 * N) := ⟨by omega⟩
    have h1val : ((1 : (ZMod (8 * N))ˣ) : ZMod (8 * N)).val = 1 := ZMod.val_one (8 * N)
    rw [hσ1] at h
    rw [h]
    dsimp only [valR, landscapeCoeff, trigF]
    rw [hχ_one, h1val]
    have ha1 := hangle_eq 1
    simp only [Nat.cast_one, one_mul] at ha1 ⊢
    rw [Int.cast_one, one_mul, ha1]
  have hdeg_eq_orb : (minpoly ℚ (landscapeCoeff k N)).natDegree =
      (Finset.univ.image valR).card := by
    have hmin1 : minpoly ℚ (landscapeCoeff k N) = minpoly ℚ (landscapeCoeff k N : ℂ) :=
      (minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ ℝ ℂ) Complex.ofReal_injective _).symm
    have hmin2 : minpoly ℚ (ι cK) = minpoly ℚ cK := minpoly.algHom_eq ι ι.injective cK
    have : FiniteDimensional ℚ (CyclotomicField (8 * N) ℚ) :=
      IsCyclotomicExtension.finiteDimensional {8 * N} ℚ (CyclotomicField (8 * N) ℚ)
    have : IsGalois ℚ (CyclotomicField (8 * N) ℚ) :=
      IsCyclotomicExtension.isGalois {8 * N} ℚ (CyclotomicField (8 * N) ℚ)
    rw [hmin1, ← hι_cK, hmin2, natDegree_minpoly_eq_card_orbit (K := CyclotomicField (8 * N) ℚ) cK]
    have hcard_K : (Finset.univ.image (fun τ : K ≃ₐ[ℚ] K => τ cK)).card =
        (Finset.univ.image (fun a : (ZMod (8 * N))ˣ => cycAut N hN a cK)).card := by
      congr 1
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨τ, rfl⟩
        exact ⟨(cycAut N hN).symm τ, by simp⟩
      · rintro ⟨a, rfl⟩; exact ⟨cycAut N hN a, rfl⟩
    rw [hcard_K]
    have hcard_C : (Finset.univ.image (fun a : (ZMod (8 * N))ˣ => cycAut N hN a cK)).card =
        ((Finset.univ.image (fun a : (ZMod (8 * N))ˣ => cycAut N hN a cK)).image ι).card :=
      (Finset.card_image_of_injective _ ι.injective).symm
    rw [hcard_C, Finset.image_image]
    have hfun : (⇑ι ∘ fun a : (ZMod (8 * N))ˣ => cycAut N hN a cK) = Complex.ofReal ∘ valR :=
      funext hι_σ_cK
    rw [hfun, ← Finset.image_image]
    exact Finset.card_image_of_injective _ Complex.ofReal_injective
  rw [hdeg_eq_orb]
  set c₀ : ℝ := landscapeCoeff k N
  have hc₀_eq : valR 1 = c₀ := by
    apply Complex.ofReal_injective
    rw [← hι_σ_cK 1, show cycAut N hN 1 cK = cK by rw [map_one]; rfl, hι_cK]
  have hscale_pos : 0 < (1 / 4 : ℝ) * Real.sqrt (2 / (N : ℝ)) := by positivity
  let vJ : ℕ → ℝ := fun j =>
    (1 / 4 : ℝ) * Real.sqrt (2 / (N : ℝ)) * trigF ((j : ℝ) * Real.pi / (2 * (N₀ : ℝ)))
  have hvJ_pos : ∀ j ∈ oddUnitsBelow N₀, 0 < vJ j := by
    intro j hj
    rcases Finset.mem_Ioo.mp (Finset.mem_filter.mp hj).1 with ⟨hj0, hjN⟩
    have hjR : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj0
    have hθ0 : 0 < (j : ℝ) * Real.pi / (2 * (N₀ : ℝ)) := by positivity
    have hθ1 : (j : ℝ) * Real.pi / (2 * (N₀ : ℝ)) < Real.pi / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      have : (j : ℝ) < (N₀ : ℝ) := Nat.cast_lt.mpr hjN
      nlinarith [Real.pi_pos]
    exact mul_pos hscale_pos (trigF_pos hθ0 hθ1)
  have hvJ_inj : Set.InjOn vJ (oddUnitsBelow N₀ : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ heq
    have hI₁ := Finset.mem_Ioo.mp (Finset.mem_filter.mp hj₁).1
    have hI₂ := Finset.mem_Ioo.mp (Finset.mem_filter.mp hj₂).1
    have hj₁R : (0 : ℝ) < (j₁ : ℝ) := Nat.cast_pos.mpr hI₁.1
    have hj₂R : (0 : ℝ) < (j₂ : ℝ) := Nat.cast_pos.mpr hI₂.1
    have hθ₁ : (j₁ : ℝ) * Real.pi / (2 * (N₀ : ℝ)) ∈ Set.Ioo 0 (Real.pi / 2) := by
      refine ⟨by positivity, ?_⟩
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      have : (j₁ : ℝ) < (N₀ : ℝ) := Nat.cast_lt.mpr hI₁.2
      nlinarith [Real.pi_pos]
    have hθ₂ : (j₂ : ℝ) * Real.pi / (2 * (N₀ : ℝ)) ∈ Set.Ioo 0 (Real.pi / 2) := by
      refine ⟨by positivity, ?_⟩
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      have : (j₂ : ℝ) < (N₀ : ℝ) := Nat.cast_lt.mpr hI₂.2
      nlinarith [Real.pi_pos]
    have hfeq : trigF ((j₁ : ℝ) * Real.pi / (2 * (N₀ : ℝ))) =
        trigF ((j₂ : ℝ) * Real.pi / (2 * (N₀ : ℝ))) := mul_left_cancel₀ hscale_pos.ne' heq
    have hθeq := trigF_strictAntiOn.injOn hθ₁ hθ₂ hfeq
    have hcast : (j₁ : ℝ) = (j₂ : ℝ) := by
      have hN₀R : (2 * (N₀ : ℝ)) ≠ 0 := by positivity
      have := congrArg (fun x => x * (2 * (N₀ : ℝ)) / Real.pi) hθeq
      field_simp [hN₀R, Real.pi_ne_zero] at this
      exact this
    exact Nat.cast_injective hcast
  have h2N₀_dvd_M : 2 * N₀ ∣ 8 * N := ⟨4 * d, by nlinarith⟩
  have habs_valR : ∀ a : (ZMod (8 * N))ˣ,
      ∃ j ∈ oddUnitsBelow N₀,
        ((a.val.val * k' % (2 * N₀) = j ∧
            trigF ((a.val.val : ℝ) * (k' : ℝ) * Real.pi / (2 * (N₀ : ℝ))) =
              trigF ((j : ℝ) * Real.pi / (2 * (N₀ : ℝ)))) ∨
         (a.val.val * k' % (2 * N₀) = 2 * N₀ - j ∧
            trigF ((a.val.val : ℝ) * (k' : ℝ) * Real.pi / (2 * (N₀ : ℝ))) =
              -trigF ((j : ℝ) * Real.pi / (2 * (N₀ : ℝ))))) ∧
        |valR a| = vJ j := by
    intro a
    set rem := (a.val.val * k') % (2 * N₀)
    have hrem_lt : rem < 2 * N₀ := Nat.mod_lt _ (by omega)
    have ha_cop_2N₀ : Nat.Coprime a.val.val (2 * N₀) :=
      (ZMod.val_coe_unit_coprime a).coprime_dvd_right h2N₀_dvd_M
    have hprod_cop : Nat.Coprime (a.val.val * k') (2 * N₀) := ha_cop_2N₀.mul_left hk'_cop_2N₀
    have hrem_cop : Nat.Coprime rem (2 * N₀) := by
      change Nat.gcd rem (2 * N₀) = 1
      rw [(Nat.mod_modEq (a.val.val * k') (2 * N₀)).gcd_eq]
      exact hprod_cop.gcd_eq_one
    have hrem_odd : Odd rem := by
      have h2 : Nat.Coprime rem 2 := hrem_cop.coprime_dvd_right (dvd_mul_right 2 N₀)
      have hnot2 : ¬ 2 ∣ rem := fun hd => by
        have := Nat.dvd_gcd hd (dvd_refl 2); rw [h2.gcd_eq_one] at this; omega
      exact Nat.odd_iff.mpr (by omega)
    have hrem_pos : 0 < rem := by rcases hrem_odd with ⟨u, hu⟩; omega
    have hrem_cop_N₀ : rem.Coprime N₀ := hrem_cop.coprime_dvd_right (dvd_mul_left N₀ 2)
    have hrem_ne_N₀ : rem ≠ N₀ := by
      intro hEq; rw [hEq, Nat.coprime_self] at hrem_cop_N₀; omega
    have hq_eq : (a.val.val : ℝ) * (k' : ℝ) * Real.pi / (2 * (N₀ : ℝ)) =
        (rem : ℝ) * Real.pi / (2 * (N₀ : ℝ)) + (((a.val.val * k') / (2 * N₀) : ℕ) : ℤ) * Real.pi := by
      have hdiv : a.val.val * k' = 2 * N₀ * ((a.val.val * k') / (2 * N₀)) + rem :=
        (Nat.div_add_mod _ _).symm
      have hdivR : (a.val.val : ℝ) * (k' : ℝ) =
          (2 * (N₀ : ℝ)) * (((a.val.val * k') / (2 * N₀) : ℕ) : ℝ) + (rem : ℝ) := by
        exact_mod_cast hdiv
      rw [hdivR]
      have hN₀R : (2 * (N₀ : ℝ)) ≠ 0 := by positivity
      simp only [Int.cast_natCast]
      field_simp [hN₀R]
      ring
    have hf_rem : trigF ((a.val.val : ℝ) * (k' : ℝ) * Real.pi / (2 * (N₀ : ℝ))) =
        trigF ((rem : ℝ) * Real.pi / (2 * (N₀ : ℝ))) := by
      rw [hq_eq, trigF_add_int_mul_pi]
    have hχabs : |(sqrtNegTwoMulChar N a : ℝ)| = 1 := by
      rcases hχ_pm a with h | h <;> simp [h]
    by_cases hlt : rem < N₀
    · have hj_mem : rem ∈ oddUnitsBelow N₀ :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hrem_pos, hlt⟩, hrem_odd, hrem_cop_N₀⟩
      refine ⟨rem, hj_mem, Or.inl ⟨rfl, hf_rem⟩, ?_⟩
      dsimp only [valR]
      rw [hf_rem, abs_mul, hχabs, one_mul, abs_of_pos (hvJ_pos rem hj_mem)]
    · set j := 2 * N₀ - rem
      have hj_odd : Odd j := by rcases hrem_odd with ⟨u, hu⟩; exact ⟨N₀ - 1 - u, by omega⟩
      have hj_cop : j.Coprime N₀ := by
        have h2 : j.Coprime (2 * N₀) := by
          rw [Nat.coprime_comm]
          exact (Nat.coprime_self_sub_right (le_of_lt hrem_lt)).mpr hrem_cop.symm
        exact h2.coprime_dvd_right (dvd_mul_left N₀ 2)
      have hj_mem : j ∈ oddUnitsBelow N₀ :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, hj_odd, hj_cop⟩
      have hf_neg : trigF ((rem : ℝ) * Real.pi / (2 * (N₀ : ℝ))) =
          -trigF ((j : ℝ) * Real.pi / (2 * (N₀ : ℝ))) := by
        have hsum : (rem : ℝ) + (j : ℝ) = 2 * (N₀ : ℝ) := by exact_mod_cast (by omega : rem + j = 2 * N₀)
        have hsub : (rem : ℝ) * Real.pi / (2 * (N₀ : ℝ)) - Real.pi =
            -((j : ℝ) * Real.pi / (2 * (N₀ : ℝ))) := by
          have hN₀R : (2 * (N₀ : ℝ)) ≠ 0 := by positivity
          field_simp [hN₀R]
          nlinarith [hsum, Real.pi_pos]
        rw [← trigF_sub_pi, hsub, trigF_neg]
      refine ⟨j, hj_mem, Or.inr ⟨by omega, by rw [hf_rem, hf_neg]⟩, ?_⟩
      dsimp only [valR]
      rw [hf_rem, hf_neg, abs_mul, hχabs, one_mul, mul_neg, abs_neg, abs_of_pos (hvJ_pos j hj_mem)]
  have habs_image : (Finset.univ.image valR).image abs = (oddUnitsBelow N₀).image vJ := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      obtain ⟨j, hj, _, habs⟩ := habs_valR a
      exact ⟨j, hj, habs.symm⟩
    · rintro ⟨j, hj, rfl⟩
      have hI := Finset.mem_Ioo.mp (Finset.mem_filter.mp hj).1
      have hj_odd := (Finset.mem_filter.mp hj).2.1
      have hj_cop_N₀ := (Finset.mem_filter.mp hj).2.2
      have hj_cop_2N₀ : j.Coprime (2 * N₀) := by
        have h2 : j.Coprime 2 := by
          rcases hj_odd with ⟨u, hu⟩
          exact Nat.coprime_comm.mp (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
        exact h2.mul_right hj_cop_N₀
      let uj : (ZMod (2 * N₀))ˣ := ZMod.unitOfCoprime j hj_cop_2N₀
      let uk' : (ZMod (2 * N₀))ˣ := ZMod.unitOfCoprime k' hk'_cop_2N₀
      obtain ⟨a, ha⟩ := ZMod.unitsMap_surjective h2N₀_dvd_M (uj * uk'⁻¹)
      have ha_mod : a.val.val * k' % (2 * N₀) = j := by
        have hcast : ((a.val.val * k' : ℕ) : ZMod (2 * N₀)) = (j : ZMod (2 * N₀)) := by
          have ha_val : ((a.val.val : ℕ) : ZMod (2 * N₀)) = ((uj * uk'⁻¹ : (ZMod (2 * N₀))ˣ) : ZMod (2 * N₀)) := by
            have := congrArg (fun u : (ZMod (2 * N₀))ˣ => (u : ZMod (2 * N₀))) ha
            simpa [ZMod.unitsMap] using this
          calc
            ((a.val.val * k' : ℕ) : ZMod (2 * N₀))
                = ((a.val.val : ℕ) : ZMod (2 * N₀)) * (k' : ZMod (2 * N₀)) := by push_cast; rfl
            _ = ((uj * uk'⁻¹ : (ZMod (2 * N₀))ˣ) : ZMod (2 * N₀)) * ((uk' : (ZMod (2 * N₀))ˣ) : ZMod (2 * N₀)) := by
                rw [ha_val]; simp [uk', ZMod.coe_unitOfCoprime]
            _ = ((uj : (ZMod (2 * N₀))ˣ) : ZMod (2 * N₀)) := by
                rw [← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]
            _ = (j : ZMod (2 * N₀)) := by simp [uj, ZMod.coe_unitOfCoprime]
        have hmodEq := (ZMod.natCast_eq_natCast_iff (a.val.val * k') j (2 * N₀)).mp hcast
        dsimp only [Nat.ModEq] at hmodEq
        rwa [Nat.mod_eq_of_lt (by omega : j < 2 * N₀)] at hmodEq
      obtain ⟨j', hj', hcases, habs⟩ := habs_valR a
      have hI' := Finset.mem_Ioo.mp (Finset.mem_filter.mp hj').1
      have hjj' : j' = j := by rcases hcases with ⟨h1, _⟩ | ⟨h2, _⟩ <;> omega
      subst hjj'
      exact ⟨valR a, ⟨a, rfl⟩, habs⟩
  set orb := Finset.univ.image valR
  have horb_card : orb.card =
      if (-c₀) ∈ orb then 2 * (oddUnitsBelow N₀).card else (oddUnitsBelow N₀).card := by
    have hJcard : (orb.image abs).card = (oddUnitsBelow N₀).card := by
      rw [habs_image, Finset.card_image_of_injOn hvJ_inj]
    have hsym_iff : (-c₀) ∈ orb ↔ ∀ x ∈ orb, (-x) ∈ orb := by
      constructor
      · intro hneg x hx
        rcases Finset.mem_image.mp hneg with ⟨b, _, hb⟩
        rcases Finset.mem_image.mp hx with ⟨a, _, ha⟩
        have hbK : cycAut N hN b cK = -cK := by
          apply ι.injective
          change ι (cycAut N hN b cK) = ι (-cK)
          rw [hι_σ_cK b, hb, map_neg, hι_cK]; push_cast; rfl
        have hba : valR (a * b) = -valR a := by
          apply Complex.ofReal_injective
          have h1 : cycAut N hN (a * b) cK = -(cycAut N hN a cK) := by
            rw [MulEquiv.map_mul (cycAut N hN) a b, AlgEquiv.mul_apply, hbK, map_neg]
          rw [← hι_σ_cK (a * b), h1, map_neg, hι_σ_cK a]
          push_cast; rfl
        exact Finset.mem_image.mpr ⟨a * b, Finset.mem_univ _, by rw [hba, ha]⟩
      · intro hall
        exact hall c₀ (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, hc₀_eq⟩)
    have hne0 : ∀ x ∈ orb, x ≠ 0 := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨a, _, rfl⟩
      obtain ⟨j, hj, _, habs⟩ := habs_valR a
      intro h0
      have := hvJ_pos j hj
      rw [← habs, h0, abs_zero] at this
      linarith
    by_cases hneg : (-c₀) ∈ orb
    · rw [if_pos hneg]
      have hall := hsym_iff.mp hneg
      have hfib : ∀ y ∈ orb.image abs, (orb.filter fun x => |x| = y).card = 2 := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
        have hset : orb.filter (fun z => |z| = |x|) = {x, -x} := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨_, hEq⟩; exact abs_eq_abs.mp hEq
          · rintro (rfl | rfl)
            · exact ⟨hx, rfl⟩
            · exact ⟨hall x hx, abs_neg x⟩
        rw [hset, Finset.card_pair]
        intro hxx; exact hne0 x hx (by linarith)
      have hcard_fib := Finset.card_eq_sum_card_fiberwise (f := abs) (s := orb) (t := orb.image abs)
        (fun x hx => Finset.mem_image_of_mem abs hx)
      rw [hcard_fib, Finset.sum_congr rfl hfib, Finset.sum_const_nat (fun _ _ => rfl), hJcard, mul_comm]
    · rw [if_neg hneg]
      have hno : ∀ x ∈ orb, (-x) ∉ orb := by
        intro x hx hnx
        rcases Finset.mem_image.mp hx with ⟨a, _, ha⟩
        rcases Finset.mem_image.mp hnx with ⟨b, _, hb⟩
        have h1 : cycAut N hN b cK = -(cycAut N hN a cK) := by
          apply ι.injective
          change ι (cycAut N hN b cK) = ι (-(cycAut N hN a cK))
          rw [hι_σ_cK b, hb, map_neg, hι_σ_cK a, ha]; push_cast; rfl
        have hbaK : cycAut N hN (a⁻¹ * b) cK = -cK := by
          rw [MulEquiv.map_mul (cycAut N hN) a⁻¹ b, AlgEquiv.mul_apply, h1, map_neg,
            ← AlgEquiv.mul_apply, ← MulEquiv.map_mul (cycAut N hN) a⁻¹ a, inv_mul_cancel,
            map_one]; rfl
        have hval : valR (a⁻¹ * b) = -c₀ := by
          apply Complex.ofReal_injective
          rw [← hι_σ_cK (a⁻¹ * b), hbaK, map_neg, hι_cK]
          push_cast; rfl
        exact hneg (Finset.mem_image.mpr ⟨a⁻¹ * b, Finset.mem_univ _, hval⟩)
      have hinj : Set.InjOn abs (orb : Set ℝ) := by
        intro x hx y hy hEq
        rcases abs_eq_abs.mp hEq with rfl | rfl
        · rfl
        · exact False.elim (hno y hy hx)
      rw [← Finset.card_image_of_injOn hinj, hJcard]
  have hneg_iff : (-c₀) ∈ orb ↔
      ∃ u : (ZMod (8 * N))ˣ, u.val.val % (2 * N₀) = 1 ∧ sqrtNegTwoMulChar N u = -1 := by
    have hk'_mem : k' ∈ oddUnitsBelow N₀ :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hk'_pos, hk'_lt⟩, hk'_odd, hcop_k'⟩
    have hc₀_vJ : c₀ = vJ k' := by
      dsimp only [c₀, landscapeCoeff, vJ, trigF]
      have ha1 := hangle_eq 1
      simp only [Nat.cast_one, one_mul] at ha1
      rw [ha1]
    have hχ_neg1 : sqrtNegTwoMulChar N (-1) = -1 := by
      have hσ_conj : ι (cycAut N hN (-1) α) = -ι α := by
        have hconj_ζ : ι (cycAut N hN (-1) ζK) = starRingEnd ℂ (ι ζK) := by
          have hm1_val : ((-1 : (ZMod (8 * N))ˣ) : ZMod (8 * N)).val = 8 * N - 1 := by
            change (-1 : ZMod (8 * N)).val = 8 * N - 1
            cases h8 : 8 * N with
            | zero => omega
            | succ m => simp [ZMod.val_neg_one]
          rw [cycAut_zeta N hN (-1), hm1_val, hι_zK_pow, hι_ζK]
          dsimp only [ζC]
          rw [← Complex.exp_conj]
          have harg : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / ((8 * N : ℕ) : ℂ)) =
              -(2 * (Real.pi : ℂ) * Complex.I / ((8 * N : ℕ) : ℂ)) := by
            simp only [map_div₀, map_mul, map_ofNat, map_natCast, Complex.conj_ofReal, Complex.conj_I]
            ring
          rw [harg]
          have h2pi : 2 * (Real.pi : ℂ) * Complex.I * ((8 * N - 1 : ℕ) : ℂ) / ((8 * N : ℕ) : ℂ) =
              -(2 * (Real.pi : ℂ) * Complex.I / ((8 * N : ℕ) : ℂ)) + 2 * (Real.pi : ℂ) * Complex.I := by
            have hMC : ((8 * N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hsub : ((8 * N - 1 : ℕ) : ℂ) = ((8 * N : ℕ) : ℂ) - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ 8 * N), Nat.cast_one]
            rw [hsub]; field_simp [hMC]; ring
          rw [h2pi, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
        have hcomp : ∀ x : K, ι (cycAut N hN (-1) x) = starRingEnd ℂ (ι x) := by
          let a1 : K →ₐ[ℚ] ℂ := ι.comp (cycAut N hN (-1)).toAlgHom
          let a2 : K →ₐ[ℚ] ℂ :=
            { toRingHom := (starRingEnd ℂ).comp ι.toRingHom
              commutes' := fun q => by simp }
          have halg : a1 = a2 := (hζK.powerBasis ℚ).algHom_ext (by
            change ι (cycAut N hN (-1) ζK) = starRingEnd ℂ (ι ζK)
            exact hconj_ζ)
          intro x
          exact congrArg (fun f : K →ₐ[ℚ] ℂ => f x) halg
        rw [hcomp α, hια]
        simp [Complex.conj_I]
      rw [hσα (-1), map_mul, map_intCast] at hσ_conj
      have hια_ne : ι α ≠ 0 := by
        rw [hια]
        exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne')
      have hC : ((sqrtNegTwoMulChar N (-1) : ℤ) : ℂ) = -1 := by
        apply mul_right_cancel₀ hια_ne
        simpa using hσ_conj
      exact_mod_cast hC
    have hχ_mul : ∀ a b : (ZMod (8 * N))ˣ,
        sqrtNegTwoMulChar N (a * b) = sqrtNegTwoMulChar N a * sqrtNegTwoMulChar N b := by
      intro a b
      have h1 : cycAut N hN (a * b) α = ((sqrtNegTwoMulChar N (a * b) : ℤ) : K) * α := hσα (a * b)
      have h2 : cycAut N hN (a * b) α =
          ((sqrtNegTwoMulChar N a * sqrtNegTwoMulChar N b : ℤ) : K) * α := by
        rw [MulEquiv.map_mul (cycAut N hN) a b, AlgEquiv.mul_apply, hσα b,
          map_mul (cycAut N hN a), map_intCast (cycAut N hN a), hσα a, Int.cast_mul, mul_assoc]
        exact mul_left_comm _ _ _
      have hα_ne : α ≠ 0 := by
        intro h0; rw [h0, map_zero] at hια
        exact mul_ne_zero Complex.I_ne_zero
          (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne') hια.symm
      have hK : ((sqrtNegTwoMulChar N (a * b) : ℤ) : K) =
          ((sqrtNegTwoMulChar N a * sqrtNegTwoMulChar N b : ℤ) : K) :=
        mul_right_cancel₀ hα_ne (h1.symm.trans h2)
      exact Int.cast_injective hK
    have hvalR_of_mod1 : ∀ u : (ZMod (8 * N))ˣ, u.val.val % (2 * N₀) = 1 →
        valR u = (sqrtNegTwoMulChar N u : ℝ) * c₀ := by
      intro u hu
      dsimp only [valR]
      set q : ℕ := u.val.val / (2 * N₀)
      have hdiv : u.val.val = 2 * N₀ * q + 1 := by
        rw [← hu]
        exact (Nat.div_add_mod u.val.val (2 * N₀)).symm
      have harg : (u.val.val : ℝ) * (k' : ℝ) * Real.pi / (2 * (N₀ : ℝ)) =
          (k' : ℝ) * Real.pi / (2 * (N₀ : ℝ)) + ((q * k' : ℕ) : ℤ) * Real.pi := by
        have hR : (u.val.val : ℝ) = (2 * (N₀ : ℝ)) * (q : ℝ) + 1 := by exact_mod_cast hdiv
        rw [hR]
        have hN₀R : (2 * (N₀ : ℝ)) ≠ 0 := by positivity
        push_cast
        field_simp [hN₀R]
        ring
      rw [harg, trigF_add_int_mul_pi, hc₀_vJ]
    constructor
    · intro hmem
      rcases Finset.mem_image.mp hmem with ⟨a, _, ha⟩
      obtain ⟨j, hj, hcases, habs⟩ := habs_valR a
      have hv_eq : vJ j = vJ k' := by
        rw [← habs, ha, abs_neg, hc₀_vJ, abs_of_pos (hvJ_pos k' hk'_mem)]
      have hjk : j = k' := hvJ_inj hj hk'_mem hv_eq
      subst hjk
      let uk' : (ZMod (2 * N₀))ˣ := ZMod.unitOfCoprime k' hk'_cop_2N₀
      rcases hcases with ⟨hmod, _⟩ | ⟨hmod, hfeq⟩
      · have hu1 : a.val.val % (2 * N₀) = 1 := by
          have hcast : ((a.val.val * k' : ℕ) : ZMod (2 * N₀)) = ((1 * k' : ℕ) : ZMod (2 * N₀)) := by
            rw [ZMod.natCast_eq_natCast_iff]
            change a.val.val * k' % (2 * N₀) = (1 * k') % (2 * N₀)
            rw [hmod, one_mul, Nat.mod_eq_of_lt (by omega)]
          have h1 : (a.val.val : ZMod (2 * N₀)) * (uk' : ZMod (2 * N₀)) =
              (1 : ZMod (2 * N₀)) * (uk' : ZMod (2 * N₀)) := by
            simpa [uk', ZMod.coe_unitOfCoprime] using hcast
          have hcancel : (a.val.val : ZMod (2 * N₀)) = (1 : ZMod (2 * N₀)) := by
            have := congrArg (· * (uk'⁻¹ : ZMod (2 * N₀))) h1
            simpa [mul_assoc] using this
          have hmodEq := (ZMod.natCast_eq_natCast_iff a.val.val 1 (2 * N₀)).mp (by simpa using hcancel)
          dsimp only [Nat.ModEq] at hmodEq
          rwa [Nat.mod_eq_of_lt (by omega : 1 < 2 * N₀)] at hmodEq
        have hval := hvalR_of_mod1 a hu1
        rw [ha] at hval
        have hc₀_pos : 0 < c₀ := by rw [hc₀_vJ]; exact hvJ_pos k' hk'_mem
        have hχa : (sqrtNegTwoMulChar N a : ℝ) = -1 :=
          mul_right_cancel₀ hc₀_pos.ne' (by rw [← hval, neg_one_mul])
        exact ⟨a, hu1, by exact_mod_cast hχa⟩
      · let u : (ZMod (8 * N))ˣ := (-1) * a
        have hu1 : u.val.val % (2 * N₀) = 1 := by
          have hmod_neg : ((a.val.val * k' : ℕ) : ZMod (2 * N₀)) = (-(k' : ZMod (2 * N₀))) := by
            have h1 : ((a.val.val * k' : ℕ) : ZMod (2 * N₀)) = ((2 * N₀ - k' : ℕ) : ZMod (2 * N₀)) := by
              rw [ZMod.natCast_eq_natCast_iff]
              change a.val.val * k' % (2 * N₀) = (2 * N₀ - k') % (2 * N₀)
              rw [hmod, Nat.mod_eq_of_lt (by omega)]
            rw [h1, Nat.cast_sub (by omega : k' ≤ 2 * N₀)]
            simp
          have h1 : (a.val.val : ZMod (2 * N₀)) * (uk' : ZMod (2 * N₀)) =
              (-1 : ZMod (2 * N₀)) * (uk' : ZMod (2 * N₀)) := by
            simpa [uk', ZMod.coe_unitOfCoprime] using hmod_neg
          have ha_neg1 : (a.val.val : ZMod (2 * N₀)) = -1 := by
            have := congrArg (· * (uk'⁻¹ : ZMod (2 * N₀))) h1
            simpa [mul_assoc] using this
          have hu_cast : (u.val.val : ZMod (2 * N₀)) = (1 : ZMod (2 * N₀)) := by
            have hmap : ZMod.castHom h2N₀_dvd_M (ZMod (2 * N₀)) (u : ZMod (8 * N)) = 1 := by
              dsimp only [u]
              rw [Units.val_mul, map_mul]
              have h1' : ZMod.castHom h2N₀_dvd_M (ZMod (2 * N₀)) ((-1 : (ZMod (8 * N))ˣ) : ZMod (8 * N)) = -1 := by
                change ZMod.castHom h2N₀_dvd_M (ZMod (2 * N₀)) (-1 : ZMod (8 * N)) = -1
                rw [map_neg, map_one]
              have h2' : ZMod.castHom h2N₀_dvd_M (ZMod (2 * N₀)) (a : ZMod (8 * N)) = -1 := by
                rw [← ZMod.natCast_zmod_val (a : ZMod (8 * N)), map_natCast, ha_neg1]
              rw [h1', h2']; ring
            rw [← ZMod.natCast_zmod_val (u : ZMod (8 * N)), map_natCast] at hmap
            exact hmap
          have hmodEq := (ZMod.natCast_eq_natCast_iff u.val.val 1 (2 * N₀)).mp (by simpa using hu_cast)
          dsimp only [Nat.ModEq] at hmodEq
          rwa [Nat.mod_eq_of_lt (by omega : 1 < 2 * N₀)] at hmodEq
        have hval_a : valR a = -(sqrtNegTwoMulChar N a : ℝ) * c₀ := by
          dsimp only [valR]; rw [hfeq, hc₀_vJ]; dsimp only [vJ]; ring
        rw [ha] at hval_a
        have hc₀_pos : 0 < c₀ := by rw [hc₀_vJ]; exact hvJ_pos k' hk'_mem
        have hχa : sqrtNegTwoMulChar N a = 1 := by
          have hmul : (sqrtNegTwoMulChar N a : ℝ) * c₀ = 1 * c₀ := by
            have hneg := congrArg Neg.neg hval_a
            rw [neg_neg, neg_mul, neg_neg] at hneg
            rw [one_mul]
            exact hneg.symm
          have : (sqrtNegTwoMulChar N a : ℝ) = 1 := mul_right_cancel₀ hc₀_pos.ne' hmul
          exact_mod_cast this
        have hχu : sqrtNegTwoMulChar N u = -1 := by
          dsimp only [u]; rw [hχ_mul, hχ_neg1, hχa]; norm_num
        exact ⟨u, hu1, hχu⟩
    · rintro ⟨u, hu1, hχu⟩
      refine Finset.mem_image.mpr ⟨u, Finset.mem_univ _, ?_⟩
      rw [hvalR_of_mod1 u hu1, hχu]
      norm_num
  rw [horb_card]
  by_cases hneg : (-c₀) ∈ orb
  · rw [if_pos hneg, if_pos (hneg_iff.mp hneg)]
  · rw [if_neg hneg, if_neg (fun h => hneg (hneg_iff.mpr h))]

/-! ### Main Theorems (Exact Degree Criterion + Second Chandra–Jain Conjecture) -/

open Classical in
/-- **Theorem B (Exact Algebraic Degree Criterion for All Odd `1 ≤ k < N`):**
For every `N ≥ 3` and every odd `k` with `1 ≤ k < N`, let `d = gcd(N, k)` and `N₀ = N / d`.
Then `[ℚ(c_k(N)) : ℚ]` equals `φ(N₀)` if `N₀` is odd or every prime `p` with odd
`d.factorization p` divides `N₀`, and equals `2 φ(N₀)` otherwise. -/
theorem chandraJain_exact_degree (N k : ℕ) (hN : 3 ≤ N) (hk : Odd k) (hkN : k < N) :
    let d := Nat.gcd N k
    let N₀ := N / d
    (minpoly ℚ (landscapeCoeff k N)).natDegree =
      if Odd N₀ ∨ ∀ p : ℕ, p.Prime → Odd (d.factorization p) → p ∣ N₀
      then Nat.totient N₀
      else 2 * Nat.totient N₀ := by
  intro d N₀
  rw [landscapeCoeff_degree_via_sign_flip N k hN hk hkN]
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left k (by omega)
  have hd_dvd_N : d ∣ N := Nat.gcd_dvd_left N k
  have hd_dvd_k : d ∣ k := Nat.gcd_dvd_right N k
  have hN_eq : d * N₀ = N := Nat.mul_div_cancel' hd_dvd_N
  set k' : ℕ := k / d
  have hk_eq : d * k' = k := Nat.mul_div_cancel' hd_dvd_k
  have hd_odd : Odd d := by
    rcases hk with ⟨t, ht⟩
    by_contra hnot
    rw [Nat.not_odd_iff_even] at hnot
    rcases hnot with ⟨u, hu⟩
    have h2k : 2 ∣ k := dvd_trans ⟨u, by omega⟩ hd_dvd_k
    rcases h2k with ⟨v, hv⟩; omega
  have hk'_lt : k' < N₀ := by nlinarith
  have hk'_pos : 0 < k' := by
    have hk_pos : 0 < k := by rcases hk with ⟨t, rfl⟩; omega
    nlinarith
  have hN₀_ge2 : 2 ≤ N₀ := by omega
  have : NeZero (8 * N) := ⟨by omega⟩
  set M : ℕ := 8 * N
  set S := (2 * N).primeFactors.filter fun p => p ≠ 2 ∧ Odd ((2 * N).factorization p)
  have h2N₀_dvd_M : 2 * N₀ ∣ M := ⟨4 * d, by dsimp only [M]; nlinarith⟩
  by_cases hN₀_odd : Odd N₀
  · rw [if_pos (Or.inl hN₀_odd)]
    have hN_odd : Odd N := by rw [← hN_eq]; exact hd_odd.mul hN₀_odd
    have hcop8N : Nat.Coprime 8 N := by
      have h2N : Nat.Coprime 2 N := by
        rcases hN_odd with ⟨u, hu⟩
        exact Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
      simpa [show (8 : ℕ) = 2 ^ 3 by decide] using h2N.pow_left 3
    obtain ⟨aNat, ha8, haN⟩ := Nat.chineseRemainder hcop8N 5 1
    have ha_cop : aNat.Coprime M := by
      dsimp only [M]
      have h1 : aNat.Coprime 8 := by
        have : Nat.gcd aNat 8 = Nat.gcd 5 8 := ha8.gcd_eq
        simpa [Nat.Coprime] using this
      have h2 : aNat.Coprime N := by
        have : Nat.gcd aNat N = Nat.gcd 1 N := haN.gcd_eq
        simpa [Nat.Coprime] using this
      exact h1.mul_right h2
    let u : (ZMod M)ˣ := ZMod.unitOfCoprime aNat ha_cop
    have hu_val : u.val.val = aNat % M := by
      change ((aNat : ZMod M)).val = aNat % M
      exact ZMod.val_natCast (n := M) aNat
    have hu_mod8 : u.val.val % 8 = 5 := by
      rw [hu_val, Nat.mod_mod_of_dvd _ (dvd_mul_right 8 N)]
      exact ha8
    have hu_modN : u.val.val % N = 1 := by
      rw [hu_val, Nat.mod_mod_of_dvd _ (dvd_mul_left N 8)]
      have : 1 % N = 1 := Nat.mod_eq_of_lt (by omega)
      rwa [Nat.ModEq, this] at haN
    have hu_mod2N₀ : u.val.val % (2 * N₀) = 1 := by
      have hmodN₀ : u.val.val % N₀ = 1 := by
        have h1 : u.val.val % N % N₀ = 1 % N₀ := by rw [hu_modN]
        rw [Nat.mod_mod_of_dvd _ ⟨d, by rw [mul_comm, hN_eq]⟩, Nat.mod_eq_of_lt (show 1 < N₀ by omega)] at h1
        exact h1
      have hcop2N₀ : Nat.Coprime 2 N₀ := by
        rcases hN₀_odd with ⟨t, ht⟩
        exact Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
      have hmodEq : u.val.val ≡ 1 [MOD 2 * N₀] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop2N₀).mp
          ⟨by rw [Nat.ModEq]; omega, by rw [Nat.ModEq, Nat.mod_eq_of_lt (show 1 < N₀ by omega)]; exact hmodN₀⟩
      dsimp only [Nat.ModEq] at hmodEq
      rwa [Nat.mod_eq_of_lt (show 1 < 2 * N₀ by omega)] at hmodEq
    have htwoOdd : Odd ((2 * N).factorization 2) := by
      have hN2 : N.factorization 2 = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        rcases hN_odd with ⟨t, ht⟩; omega
      rw [Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply, hN2, add_zero,
        Nat.Prime.factorization_self Nat.prime_two]
      exact odd_one
    have hχu : sqrtNegTwoMulChar N u = -1 := by
      dsimp only [sqrtNegTwoMulChar]
      rw [if_pos htwoOdd]
      have hc2 : chi2Sign u.val.val = -1 := by dsimp only [chi2Sign]; rw [hu_mod8]; decide
      have hc4 : chi4Sign u.val.val = 1 := by
        have : u.val.val % 4 = 1 := by omega
        dsimp only [chi4Sign]; rw [this]; decide
      have hprod1 : ∏ p ∈ S, legendreInt p u.val.val = 1 := by
        refine Finset.prod_eq_one fun p hp => ?_
        have hp_mem : p.Prime ∧ p ≠ 2 ∧ p ∣ 2 * N := by
          simp only [S, Finset.mem_filter, Nat.mem_primeFactors] at hp
          exact ⟨hp.1.1, hp.2.1, hp.1.2.1⟩
        have hp_dvd_N : p ∣ N :=
          (hp_mem.1.dvd_mul.mp hp_mem.2.2).resolve_left fun h2 =>
            hp_mem.2.1 ((Nat.prime_dvd_prime_iff_eq hp_mem.1 Nat.prime_two).mp h2)
        have hmodp : u.val.val % p = 1 := by
          have := congrArg (· % p) hu_modN
          rw [Nat.mod_mod_of_dvd _ hp_dvd_N, Nat.mod_eq_of_lt hp_mem.1.one_lt] at this
          exact this
        rw [← legendreInt_mod, hmodp, legendreInt_one]
      rw [hc2, hc4, one_pow, hprod1]
      ring
    rw [if_pos ⟨u, hu_mod2N₀, hχu⟩]
    have hN₀_ge3 : 3 ≤ N₀ := by rcases hN₀_odd with ⟨t, ht⟩; omega
    exact two_mul_card_oddUnitsBelow_odd hN₀_ge3 hN₀_odd
  · have hN₀_even : Even N₀ := Nat.not_odd_iff_even.mp hN₀_odd
    have hcardJ : (oddUnitsBelow N₀).card = Nat.totient N₀ :=
      card_oddUnitsBelow_even hN₀_ge2 hN₀_even
    have hχ_on_U : ∀ u : (ZMod M)ˣ, u.val.val % (2 * N₀) = 1 →
        sqrtNegTwoMulChar N u = ∏ p ∈ S, legendreInt p u.val.val := by
      intro u hu1
      dsimp only [sqrtNegTwoMulChar]
      have h4_dvd : 4 ∣ 2 * N₀ := by rcases hN₀_even with ⟨t, ht⟩; exact ⟨t, by omega⟩
      have hu_mod4 : u.val.val % 4 = 1 := by
        have := congrArg (· % 4) hu1
        rwa [Nat.mod_mod_of_dvd _ h4_dvd] at this
      have hc4 : chi4Sign u.val.val = 1 := by dsimp only [chi4Sign]; rw [hu_mod4]; decide
      have hc2 : (if Odd ((2 * N).factorization 2) then chi2Sign u.val.val else 1) = 1 := by
        by_cases h2 : Odd ((2 * N).factorization 2)
        · rw [if_pos h2]
          have hv2_N : N.factorization 2 = N₀.factorization 2 := by
            rw [← hN_eq, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply]
            have hd2 : d.factorization 2 = 0 := by
              apply Nat.factorization_eq_zero_of_not_dvd
              rcases hd_odd with ⟨t, ht⟩; omega
            omega
          have hv2_2N : (2 * N).factorization 2 = 1 + N₀.factorization 2 := by
            rw [Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply,
              Nat.Prime.factorization_self Nat.prime_two, hv2_N]
          have hv2_pos : 0 < N₀.factorization 2 := by
            have h1 : 1 ≤ N₀.factorization 2 :=
              (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two (by omega)).mp
                (by rcases hN₀_even with ⟨t, ht⟩; exact ⟨t, by omega⟩)
            omega
          have hv2_ge2 : 2 ≤ N₀.factorization 2 := by
            rw [hv2_2N] at h2; rcases h2 with ⟨t, ht⟩; omega
          have h4_dvd_N₀ : 4 ∣ N₀ := by
            have hpow : 2 ^ 2 ∣ N₀ :=
              dvd_trans (Nat.pow_dvd_pow 2 hv2_ge2) (Nat.ordProj_dvd N₀ 2)
            simpa using hpow
          have h8_dvd : 8 ∣ 2 * N₀ := by rcases h4_dvd_N₀ with ⟨t, ht⟩; exact ⟨t, by omega⟩
          have hu_mod8 : u.val.val % 8 = 1 := by
            have := congrArg (· % 8) hu1
            rwa [Nat.mod_mod_of_dvd _ h8_dvd] at this
          dsimp only [chi2Sign]; rw [hu_mod8]; decide
        · rw [if_neg h2]
      rw [hc2, hc4, one_pow, one_mul, one_mul]
    have hSext_iff : ∀ p : ℕ, (p ∈ S ∧ ¬ p ∣ N₀) ↔ (p.Prime ∧ Odd (d.factorization p) ∧ ¬ p ∣ N₀) := by
      intro p
      constructor
      · rintro ⟨hpS, hndvd⟩
        simp only [S, Finset.mem_filter, Nat.mem_primeFactors] at hpS
        have hp_prime : p.Prime := hpS.1.1
        have hp_ne2 : p ≠ 2 := hpS.2.1
        have hfac : (2 * N).factorization p = d.factorization p := by
          rw [← hN_eq, Nat.factorization_mul (by norm_num) (by omega),
            Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply, Finsupp.add_apply]
          have h2p : (2 : ℕ).factorization p = 0 := by
            apply Nat.factorization_eq_zero_of_not_dvd
            intro hdvd; exact hp_ne2 ((Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp hdvd)
          have hN₀p : N₀.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hndvd
          omega
        exact ⟨hp_prime, by rw [← hfac]; exact hpS.2.2, hndvd⟩
      · rintro ⟨hp_prime, hodd_d, hndvd⟩
        have hp_ne2 : p ≠ 2 := by
          intro h2; subst h2
          rcases hN₀_even with ⟨t, ht⟩; exact hndvd ⟨t, by omega⟩
        have hp_dvd_d : p ∣ d :=
          (Nat.Prime.dvd_iff_one_le_factorization hp_prime (by omega)).mpr
            (by rcases hodd_d with ⟨t, ht⟩; omega)
        have hfac : (2 * N).factorization p = d.factorization p := by
          rw [← hN_eq, Nat.factorization_mul (by norm_num) (by omega),
            Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply, Finsupp.add_apply]
          have h2p : (2 : ℕ).factorization p = 0 := by
            apply Nat.factorization_eq_zero_of_not_dvd
            intro hdvd; exact hp_ne2 ((Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp hdvd)
          have hN₀p : N₀.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hndvd
          omega
        refine ⟨?_, hndvd⟩
        simp only [S, Finset.mem_filter, Nat.mem_primeFactors]
        exact ⟨⟨hp_prime, dvd_trans hp_dvd_d (dvd_trans hd_dvd_N (dvd_mul_left N 2)), by omega⟩,
          hp_ne2, by rwa [hfac]⟩
    by_cases hcrit : ∀ p : ℕ, p.Prime → Odd (d.factorization p) → p ∣ N₀
    · rw [if_pos (Or.inr hcrit)]
      have hno_wit : ¬ ∃ u : (ZMod M)ˣ, u.val.val % (2 * N₀) = 1 ∧ sqrtNegTwoMulChar N u = -1 := by
        rintro ⟨u, hu1, hχu⟩
        rw [hχ_on_U u hu1] at hχu
        have hprod1 : ∏ p ∈ S, legendreInt p u.val.val = 1 := by
          refine Finset.prod_eq_one fun p hp => ?_
          have hp_dvd_N₀ : p ∣ N₀ := by
            by_contra hndvd
            have h := (hSext_iff p).mp ⟨hp, hndvd⟩
            exact hndvd (hcrit p h.1 h.2.1)
          have hp_prime : p.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
          have hmodp : u.val.val % p = 1 := by
            have := congrArg (· % p) hu1
            rw [Nat.mod_mod_of_dvd _ (dvd_trans hp_dvd_N₀ (dvd_mul_left N₀ 2)),
              Nat.mod_eq_of_lt hp_prime.one_lt] at this
            exact this
          rw [← legendreInt_mod, hmodp, legendreInt_one]
        omega
      rw [if_neg hno_wit, hcardJ]
    · have hnot_cond : ¬ (Odd N₀ ∨ ∀ p : ℕ, p.Prime → Odd (d.factorization p) → p ∣ N₀) :=
        not_or.mpr ⟨hN₀_odd, hcrit⟩
      rw [if_neg hnot_cond]
      push Not at hcrit
      rcases hcrit with ⟨p₀, hp₀_prime, hp₀_odd, hp₀_ndvd⟩
      have hp₀_S : p₀ ∈ S := ((hSext_iff p₀).mpr ⟨hp₀_prime, hp₀_odd, hp₀_ndvd⟩).1
      have hp₀_ne2 : p₀ ≠ 2 := (Finset.mem_filter.mp hp₀_S).2.1
      have : Fact p₀.Prime := ⟨hp₀_prime⟩
      have hchar_ne2 : ringChar (ZMod p₀) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp₀_ne2
      obtain ⟨rUnit, hrUnit⟩ := quadraticChar_exists_neg_one' hchar_ne2
      set t : ℕ := M.factorization p₀
      set M' : ℕ := M / p₀ ^ t
      have hpt_dvd : p₀ ^ t ∣ M := Nat.ordProj_dvd M p₀
      have hM_split : p₀ ^ t * M' = M := Nat.mul_div_cancel' hpt_dvd
      have hp₀_ndvd_M' : ¬ p₀ ∣ M' := Nat.not_dvd_ordCompl hp₀_prime (by omega : M ≠ 0)
      have hcop_split : Nat.Coprime (p₀ ^ t) M' :=
        (hp₀_prime.coprime_iff_not_dvd.mpr hp₀_ndvd_M').pow_left t
      have h2N₀_dvd_M' : 2 * N₀ ∣ M' := by
        have hcop_2N₀ : Nat.Coprime (p₀ ^ t) (2 * N₀) := by
          have hp₀_ndvd_2N₀ : ¬ p₀ ∣ 2 * N₀ := by
            intro hdvd
            rcases hp₀_prime.dvd_mul.mp hdvd with h2 | hN₀d
            · exact hp₀_ne2 ((Nat.prime_dvd_prime_iff_eq hp₀_prime Nat.prime_two).mp h2)
            · exact hp₀_ndvd hN₀d
          exact (hp₀_prime.coprime_iff_not_dvd.mpr hp₀_ndvd_2N₀).pow_left t
        have hdvd_mul : 2 * N₀ ∣ p₀ ^ t * M' := by rw [hM_split]; exact h2N₀_dvd_M
        exact hcop_2N₀.symm.dvd_of_dvd_mul_left hdvd_mul
      have ht_pos : 0 < t := by
        have h1 : 1 ≤ M.factorization p₀ :=
          (Nat.Prime.dvd_iff_one_le_factorization hp₀_prime (by omega)).mp
            (dvd_trans (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp₀_S).1).2.1 ⟨4, by omega⟩)
        omega
      obtain ⟨aNat, ha_p₀, ha_M'⟩ := Nat.chineseRemainder hcop_split (rUnit : ZMod p₀).val 1
      have ha_cop : aNat.Coprime M := by
        rw [← hM_split]
        have h1 : aNat.Coprime (p₀ ^ t) := by
          have hp₀_cop_r : (rUnit : ZMod p₀).val.Coprime p₀ := ZMod.val_coe_unit_coprime rUnit
          have hp₀_cop_a : aNat.Coprime p₀ := by
            have hmod_p₀ : aNat ≡ (rUnit : ZMod p₀).val [MOD p₀] :=
              ha_p₀.of_dvd (dvd_pow_self p₀ (by omega))
            have := hmod_p₀.gcd_eq
            simpa [Nat.Coprime] using this.trans hp₀_cop_r.gcd_eq_one
          exact hp₀_cop_a.pow_right t
        have h2 : aNat.Coprime M' := by
          have := ha_M'.gcd_eq
          simpa [Nat.Coprime] using this
        exact h1.mul_right h2
      let u : (ZMod M)ˣ := ZMod.unitOfCoprime aNat ha_cop
      have hu_val : u.val.val = aNat % M := by
        change ((aNat : ZMod M)).val = aNat % M
        exact ZMod.val_natCast (n := M) aNat
      have hu_modM' : u.val.val % M' = 1 % M' := by
        rw [hu_val, Nat.mod_mod_of_dvd _ ⟨p₀ ^ t, by rw [mul_comm, hM_split]⟩]
        exact ha_M'
      have hu_mod2N₀ : u.val.val % (2 * N₀) = 1 := by
        have h1 := congrArg (· % (2 * N₀)) hu_modM'
        rw [Nat.mod_mod_of_dvd _ h2N₀_dvd_M', Nat.mod_mod_of_dvd _ h2N₀_dvd_M',
          Nat.mod_eq_of_lt (show 1 < 2 * N₀ by omega)] at h1
        exact h1
      have hχu : sqrtNegTwoMulChar N u = -1 := by
        rw [hχ_on_U u hu_mod2N₀, ← Finset.mul_prod_erase _ _ hp₀_S]
        have hp₀_val : legendreInt p₀ u.val.val = -1 := by
          rw [legendreInt_of_prime]
          have hp₀_dvd_pt : p₀ ∣ p₀ ^ t := dvd_pow_self p₀ (by omega)
          have hmod_p₀ : u.val.val ≡ (rUnit : ZMod p₀).val [MOD p₀] := by
            rw [hu_val]
            exact (Nat.mod_modEq aNat M).of_dvd (dvd_trans hp₀_dvd_pt hpt_dvd) |>.trans
              (ha_p₀.of_dvd hp₀_dvd_pt)
          have hcast : (u.val.val : ZMod p₀) = (rUnit : ZMod p₀) := by
            rw [(ZMod.natCast_eq_natCast_iff u.val.val (rUnit : ZMod p₀).val p₀).mpr hmod_p₀,
              ZMod.natCast_zmod_val]
          rw [hcast]
          exact hrUnit
        have hrest : ∏ p ∈ S.erase p₀, legendreInt p u.val.val = 1 := by
          refine Finset.prod_eq_one fun p hp => ?_
          rcases Finset.mem_erase.mp hp with ⟨hp_ne, hpS⟩
          have hp_prime : p.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpS).1).1
          have hp_dvd_M : p ∣ M :=
            dvd_trans (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpS).1).2.1 ⟨4, by omega⟩
          have hp_cop_pt : p.Coprime (p₀ ^ t) :=
            ((Nat.coprime_primes hp_prime hp₀_prime).mpr hp_ne).pow_right t
          have hp_dvd_M' : p ∣ M' := by
            have : p ∣ p₀ ^ t * M' := by rwa [hM_split]
            exact hp_cop_pt.dvd_of_dvd_mul_left this
          have hmodp : u.val.val % p = 1 := by
            have h1 := congrArg (· % p) hu_modM'
            rw [Nat.mod_mod_of_dvd _ hp_dvd_M', Nat.mod_mod_of_dvd _ hp_dvd_M',
              Nat.mod_eq_of_lt hp_prime.one_lt] at h1
            exact h1
          rw [← legendreInt_mod, hmodp, legendreInt_one]
        rw [hp₀_val, hrest, mul_one]
      have hwit : ∃ v : (ZMod (8 * N))ˣ, v.val.val % (2 * N₀) = 1 ∧ sqrtNegTwoMulChar N v = -1 :=
        ⟨u, hu_mod2N₀, hχu⟩
      rw [if_pos hwit, hcardJ]

/-- **Theorem A (Second Chandra–Jain Conjecture, arXiv:2608.11372v3, Sec. 5):**
For every `N ≥ 3` and every odd `k` with `1 ≤ k < N` and `1 < gcd(N, k)`, setting
`N₀ = N / gcd(N, k)`, we have `[ℚ(c_k(N)) : ℚ] ∈ {φ(N₀), 2 φ(N₀)}`. -/
theorem chandraJain_dichotomy (N k : ℕ) (hN : 3 ≤ N) (hk : Odd k) (hkN : k < N)
    (_hd : 1 < Nat.gcd N k) :
    (minpoly ℚ (landscapeCoeff k N)).natDegree ∈
      ({Nat.totient (N / Nat.gcd N k), 2 * Nat.totient (N / Nat.gcd N k)} : Set ℕ) := by
  have h := chandraJain_exact_degree N k hN hk hkN
  dsimp only at h
  rw [h]
  split_ifs
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

/-- **Corollary (Coprime Higher-Mode Degree & Zhou's Theorem):**
For every `N ≥ 3` and every odd `k` with `1 ≤ k < N` and `gcd(N, k) = 1`,
`[ℚ(c_k(N)) : ℚ] = φ(N)`. -/
theorem chandraJain_coprime_degree (N k : ℕ) (hN : 3 ≤ N) (hk : Odd k) (hkN : k < N)
    (hd : Nat.gcd N k = 1) :
    (minpoly ℚ (landscapeCoeff k N)).natDegree = Nat.totient N := by
  have h := chandraJain_exact_degree N k hN hk hkN
  dsimp only at h
  rw [hd, Nat.div_one] at h
  have hvac : ∀ p : ℕ, p.Prime → Odd ((1 : ℕ).factorization p) → p ∣ N := by
    intro p _ ho
    simp at ho
  rw [if_pos (Or.inr hvac)] at h
  exact h

end ChandraJainSecondConjecture
