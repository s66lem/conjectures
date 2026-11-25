import Mathlib

/-!
# Multi-label radio labelings of paths and cycles

Formalization for O. Togni, "On Multi-label radio Labelings of Graphs" (arXiv:2610.25863).
With `S = ⌈(k+1)²/2⌉` (`S_val`, see `S_val_eq_ceil`):

* `conjecture1_path_upper_bound`: every path `P_n` has an `(m,k)`-radio labeling with all
  labels in `[0, m S - 1]` (upper half of Conjecture 1).
* `conjecture2_cycle`: if `k S (m S + 1) ≤ 2 n`, the cycle `C_n` has an `(m,k)`-radio labeling
  with all labels in `[0, m S]` (Conjecture 2).

Both rest on `lattice_min_norm`: the lattice `{(h,z) : S ∣ z - a h}` has minimum nonzero
Manhattan norm `k + 1`, where `a = k` for odd `k` and `a = k + 1` for even `k`.
-/

namespace TogniRadio

/-! ## Definitions -/

/-- Graph distance in the path `P_n` on `Fin n`. -/
def pathDist {n : ℕ} (i j : Fin n) : ℕ := Int.natAbs (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))

/-- Graph distance in the cycle `C_n` on `Fin n` (see `cycleDist_exists`, `cycleDist_le`). -/
def cycleDist (n : ℕ) (i j : Fin n) : ℕ :=
  min ((i.val + n - j.val) % n) ((j.val + n - i.val) % n)

/-- Definition 1.1: `f` assigns `m` labels to each vertex; two labels at one vertex differ by at
least `k + 1`, and labels `c₁ ∈ f u`, `c₂ ∈ f v` at distinct vertices satisfy
`dist u v + |c₁ - c₂| ≥ k + 1`. -/
def IsMultiRadioLabeling {V : Type*} (dist : V → V → ℕ) (k m : ℕ) (f : V → Finset ℕ) : Prop :=
  (∀ v, (f v).card = m) ∧
  (∀ v, ∀ c₁ ∈ f v, ∀ c₂ ∈ f v, c₁ ≠ c₂ → k + 1 ≤ Int.natAbs ((c₁ : ℤ) - c₂)) ∧
  (∀ u v, u ≠ v → ∀ c₁ ∈ f u, ∀ c₂ ∈ f v, k + 1 ≤ dist u v + Int.natAbs ((c₁ : ℤ) - c₂))

/-- `S = ⌈(k+1)²/2⌉`. -/
def S_val (k : ℕ) : ℕ := ((k + 1) ^ 2 + 1) / 2

/-- The lattice slope: `k` for odd `k`, `k + 1` for even `k`. -/
def aVal (k : ℕ) : ℕ := if k % 2 = 1 then k else k + 1

/-! ## Basic facts -/

theorem isMultiRadioLabeling_of {V : Type*} {dist : V → V → ℕ} {k m : ℕ} {f : V → Finset ℕ}
    (hd : ∀ v, dist v v = 0) (hcard : ∀ v, (f v).card = m)
    (H : ∀ u v, ∀ c₁ ∈ f u, ∀ c₂ ∈ f v, (u ≠ v ∨ c₁ ≠ c₂) →
      k + 1 ≤ dist u v + Int.natAbs ((c₁ : ℤ) - c₂)) :
    IsMultiRadioLabeling dist k m f :=
  ⟨hcard, fun v c₁ h₁ c₂ h₂ hne => by simpa [hd v] using H v v c₁ h₁ c₂ h₂ (Or.inr hne),
    fun u v huv c₁ h₁ c₂ h₂ => H u v c₁ h₁ c₂ h₂ (Or.inl huv)⟩

theorem S_val_add_self (r : ℕ) : S_val (r + r) = 2 * r ^ 2 + 2 * r + 1 := by
  unfold S_val
  rw [show (r + r + 1) ^ 2 + 1 = 2 * (2 * r ^ 2 + 2 * r + 1) by ring,
    Nat.mul_div_cancel_left _ two_pos]

theorem S_val_two_mul_add_one (s : ℕ) : S_val (2 * s + 1) = 2 * (s + 1) ^ 2 := by
  unfold S_val
  rw [show (2 * s + 1 + 1) ^ 2 + 1 = 1 + 2 * (2 * (s + 1) ^ 2) by ring,
    Nat.add_mul_div_left _ _ two_pos]
  norm_num

theorem aVal_add_self (r : ℕ) : aVal (r + r) = r + r + 1 := by
  unfold aVal; rw [if_neg (by omega)]

theorem aVal_two_mul_add_one (s : ℕ) : aVal (2 * s + 1) = 2 * s + 1 := by
  unfold aVal; rw [if_pos (by omega)]

theorem two_mul_S_val_of_odd {k : ℕ} (hk : Odd k) : 2 * S_val k = (k + 1) ^ 2 := by
  obtain ⟨s, rfl⟩ := hk
  rw [S_val_two_mul_add_one]; ring

theorem two_mul_S_val_of_even {k : ℕ} (hk : Even k) : 2 * S_val k = (k + 1) ^ 2 + 1 := by
  obtain ⟨r, rfl⟩ := hk
  rw [S_val_add_self]; ring

theorem S_val_eq_ceil (k : ℕ) : (S_val k : ℤ) = ⌈((k + 1 : ℚ) ^ 2) / 2⌉ := by
  rw [eq_comm, Int.ceil_eq_iff]
  push_cast
  rcases Nat.even_or_odd k with hk | hk
  · have h : (2 * S_val k : ℚ) = (k + 1) ^ 2 + 1 := by exact_mod_cast two_mul_S_val_of_even hk
    constructor <;> linarith
  · have h : (2 * S_val k : ℚ) = (k + 1) ^ 2 := by exact_mod_cast two_mul_S_val_of_odd hk
    constructor <;> linarith

theorem S_val_pos (k : ℕ) : 0 < S_val k := by
  rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨s, rfl⟩
  · rw [S_val_add_self]; omega
  · rw [S_val_two_mul_add_one]; positivity

/-! ## Cycle distance is the shortest-path distance -/

theorem cycleDist_exists (n : ℕ) (i j : Fin n) :
    ∃ h : ℤ, h.natAbs = cycleDist n i j ∧ (i.val : ℤ) + h ≡ j.val [ZMOD n] := by
  have hi := i.isLt
  have hj := j.isLt
  have hq : (((i.val + n - j.val) % n : ℕ) : ℤ) = ((i.val : ℤ) + n - j.val) % n := by
    rw [Int.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add]
  have hp : (((j.val + n - i.val) % n : ℕ) : ℤ) = ((j.val : ℤ) + n - i.val) % n := by
    rw [Int.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add]
  unfold cycleDist
  rcases le_total ((i.val + n - j.val) % n) ((j.val + n - i.val) % n) with hle | hle
  · refine ⟨-(((i.val + n - j.val) % n : ℕ) : ℤ), by rw [Int.natAbs_neg, min_eq_left hle]; rfl, ?_⟩
    rw [hq, Int.modEq_iff_dvd]
    exact ⟨1 - ((i.val : ℤ) + n - j.val) / n, by rw [Int.emod_def]; ring⟩
  · refine ⟨(((j.val + n - i.val) % n : ℕ) : ℤ), by rw [min_eq_right hle]; rfl, ?_⟩
    rw [hp, Int.modEq_iff_dvd]
    exact ⟨((j.val : ℤ) + n - i.val) / n - 1, by rw [Int.emod_def]; ring⟩

theorem cycleDist_le (n : ℕ) (i j : Fin n) (h : ℤ) (hmod : (i.val : ℤ) + h ≡ j.val [ZMOD n]) :
    cycleDist n i j ≤ h.natAbs := by
  have hi := i.isLt
  have hj := j.isLt
  have hn : (0 : ℤ) < n := by omega
  obtain ⟨c, hc⟩ := Int.ModEq.dvd hmod
  have small : ∀ x : ℤ, 0 ≤ x → x % n ≤ x := fun x hx => by
    have := mul_nonneg hn.le (Int.ediv_nonneg hx hn.le)
    rw [Int.emod_def]; linarith
  unfold cycleDist
  rcases le_total 0 h with h0 | h0
  · apply le_trans (min_le_right _ _)
    have hp : (((j.val + n - i.val) % n : ℕ) : ℤ) = h % n := by
      rw [Int.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add]
      exact (Int.modEq_iff_dvd.mpr ⟨c + 1, by linarith⟩ : h ≡ (j.val : ℤ) + n - i.val [ZMOD n]).symm
    have := small h h0
    have := Int.natAbs_of_nonneg h0
    omega
  · apply le_trans (min_le_left _ _)
    have hq : (((i.val + n - j.val) % n : ℕ) : ℤ) = (-h) % n := by
      rw [Int.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add]
      exact (Int.modEq_iff_dvd.mpr ⟨1 - c, by linarith⟩ :
        -h ≡ (i.val : ℤ) + n - j.val [ZMOD n]).symm
    have := small (-h) (by linarith)
    have := Int.natAbs_neg h ▸ Int.natAbs_of_nonneg (show 0 ≤ -h by linarith)
    omega

/-! ## The lattice -/

theorem lattice_min_norm_abs (k : ℕ) (h z : ℤ) (hdvd : (S_val k : ℤ) ∣ z - aVal k * h)
    (hne : (h, z) ≠ (0, 0)) : (k : ℤ) + 1 ≤ |h| + |z| := by
  rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨s, rfl⟩
  · -- k = 2r: S = 2r² + 2r + 1, a = 2r + 1, orthogonal basis (r, -r-1), (r+1, r)
    rw [S_val_add_self, aVal_add_self] at hdvd
    push_cast at hdvd ⊢
    obtain ⟨c, hc⟩ := hdvd
    have hr : (0 : ℤ) ≤ r := by positivity
    have hX : (r : ℤ) * h - (r + 1) * z = (2 * r ^ 2 + 2 * r + 1) * (-(r + 1) * c - h) := by
      linear_combination (-((r : ℤ) + 1)) * hc
    have hY : ((r : ℤ) + 1) * h + r * z = (2 * r ^ 2 + 2 * r + 1) * (r * c + h) := by
      linear_combination (r : ℤ) * hc
    have bound : ∀ (X q : ℤ), X = (2 * r ^ 2 + 2 * r + 1) * q → q ≠ 0 →
        |X| ≤ (r + 1) * (|h| + |z|) → (r : ℤ) + r + 1 ≤ |h| + |z| := by
      intro X q hXq hq hle
      have h1 : |X| = (2 * r ^ 2 + 2 * r + 1) * |q| := by
        rw [hXq, abs_mul, abs_of_pos (by positivity)]
      have h2 := mul_le_mul_of_nonneg_left (Int.one_le_abs hq)
        (show (0 : ℤ) ≤ 2 * r ^ 2 + 2 * r + 1 by positivity)
      by_contra hlt
      have h3 := mul_le_mul_of_nonneg_left (show |h| + |z| ≤ 2 * r by linarith)
        (show (0 : ℤ) ≤ r + 1 by positivity)
      nlinarith
    have hh0 := abs_nonneg h
    have hz0 := abs_nonneg z
    by_cases hq1 : -((r : ℤ) + 1) * c - h = 0
    · by_cases hq2 : (r : ℤ) * c + h = 0
      · have hc0 : c = 0 := by linarith
        subst hc0
        have hh : h = 0 := by linarith
        subst hh
        exact absurd (by simpa using hc) (fun hz : z = 0 => hne (by simp [hz]))
      · refine bound _ _ hY hq2 ?_
        calc |((r : ℤ) + 1) * h + r * z| ≤ |((r : ℤ) + 1) * h| + |(r : ℤ) * z| := abs_add_le _ _
          _ = (r + 1) * |h| + r * |z| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg (show (0 : ℤ) ≤ r + 1 by positivity)]
          _ ≤ (r + 1) * (|h| + |z|) := by nlinarith
    · refine bound _ _ hX hq1 ?_
      calc |(r : ℤ) * h - (r + 1) * z| ≤ |(r : ℤ) * h| + |((r : ℤ) + 1) * z| := abs_sub _ _
        _ = r * |h| + (r + 1) * |z| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg (show (0 : ℤ) ≤ r + 1 by positivity)]
        _ ≤ (r + 1) * (|h| + |z|) := by nlinarith
  · -- k = 2s+1: S = 2(s+1)², a = 2s+1; 2(s+1) divides h + z
    rw [S_val_two_mul_add_one, aVal_two_mul_add_one] at hdvd
    push_cast at hdvd ⊢
    obtain ⟨c, hc⟩ := hdvd
    have hR : (0 : ℤ) < s + 1 := by positivity
    have hw : h + z = 2 * (s + 1) * ((s + 1) * c + h) := by linear_combination hc
    by_cases hq : ((s : ℤ) + 1) * c + h = 0
    · have hc0 : c ≠ 0 := by
        rintro rfl
        have hh : h = 0 := by linarith
        subst hh
        have hz : z = 0 := by simpa using hc
        exact hne (by simp [hz])
      have hh : h = -(((s : ℤ) + 1) * c) := by linarith
      have hz : z = ((s : ℤ) + 1) * c := by rw [hq, mul_zero] at hw; linarith
      rw [hh, hz, abs_neg, abs_mul, abs_of_pos hR]
      nlinarith [Int.one_le_abs hc0]
    · have h1 : |h + z| = 2 * (s + 1) * |((s : ℤ) + 1) * c + h| := by
        rw [hw, abs_mul, abs_of_pos (by positivity)]
      nlinarith [Int.one_le_abs hq, abs_add_le h z]

/-- Every nonzero `(h, z)` with `S ∣ z - a h` has `|h| + |z| ≥ k + 1`. -/
theorem lattice_min_norm (k : ℕ) (h z : ℤ) (hdvd : (S_val k : ℤ) ∣ z - aVal k * h)
    (hne : (h, z) ≠ (0, 0)) : k + 1 ≤ h.natAbs + z.natAbs := by
  have := lattice_min_norm_abs k h z hdvd hne
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at this
  exact_mod_cast this

/-! ## Paths -/

/-- Upper bound of Conjecture 1: labels `(a i mod S) + j S`, `0 ≤ j < m`, at vertex `i`. -/
theorem conjecture1_path_upper_bound (n k m : ℕ) (_hk : 1 ≤ k) (_hm : 1 ≤ m) :
    ∃ f : Fin n → Finset ℕ, IsMultiRadioLabeling pathDist k m f ∧
      ∀ v, ∀ c ∈ f v, c ≤ m * S_val k - 1 := by
  have hS := S_val_pos k
  refine ⟨fun i => (Finset.range m).image fun j => aVal k * i.val % S_val k + j * S_val k,
    isMultiRadioLabeling_of (fun v => by simp [pathDist]) (fun v => ?_) ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
    intro j₁ j₂ hj
    simp only at hj
    exact Nat.eq_of_mul_eq_mul_right hS (Nat.add_left_cancel hj)
  · intro u v c₁ h₁ c₂ h₂ huv
    simp only [Finset.mem_image, Finset.mem_range] at h₁ h₂
    obtain ⟨j₁, -, rfl⟩ := h₁
    obtain ⟨j₂, -, rfl⟩ := h₂
    have hdvd : (S_val k : ℤ) ∣ (((aVal k * u.val % S_val k + j₁ * S_val k : ℕ) : ℤ) -
        ((aVal k * v.val % S_val k + j₂ * S_val k : ℕ) : ℤ)) -
        aVal k * (((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)) := by
      push_cast
      exact ⟨-((aVal k : ℤ) * u.val / S_val k) + (aVal k : ℤ) * v.val / S_val k + j₁ - j₂, by
        rw [Int.emod_def, Int.emod_def]; ring⟩
    have hne : ((((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)),
        (((aVal k * u.val % S_val k + j₁ * S_val k : ℕ) : ℤ) -
          ((aVal k * v.val % S_val k + j₂ * S_val k : ℕ) : ℤ))) ≠ (0, 0) := by
      intro heq
      simp only [Prod.mk.injEq, sub_eq_zero] at heq
      rcases huv with huv | huv
      · exact huv (Fin.ext (by exact_mod_cast heq.1))
      · exact huv (by exact_mod_cast heq.2)
    exact lattice_min_norm k _ _ hdvd hne
  · intro v c hc
    simp only [Finset.mem_image, Finset.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    have h1 := Nat.mod_lt (aVal k * v.val) hS
    have h2 := Nat.mul_le_mul_right (S_val k) (show j + 1 ≤ m by omega)
    rw [add_mul, one_mul] at h2
    omega

/-! ## Cycles -/

/-- `F(i,j) = ⌊M (t i + j n) / (m n)⌋`. -/
def cycF (M t n m i j : ℤ) : ℤ := M * (t * i + j * n) / (m * n)

theorem cycF_add_period (M t n m i j w : ℤ) (hmn : m * n ≠ 0) :
    cycF M t n m i (j + m * w) = cycF M t n m i j + M * w := by
  unfold cycF
  rw [show M * (t * i + (j + m * w) * n) = M * (t * i + j * n) + M * w * (m * n) by ring,
    Int.add_mul_ediv_right _ _ hmn]

theorem cycF_shift (M t n m i j w : ℤ) :
    cycF M t n m (i + n * w) j = cycF M t n m i (j + t * w) := by
  unfold cycF; congr 1; ring

theorem cycF_emod (M t n m i j : ℤ) (hmn : m * n ≠ 0) :
    ∃ w, cycF M t n m i j % M = cycF M t n m i (j + m * w) :=
  ⟨-(cycF M t n m i j / M), by rw [cycF_add_period _ _ _ _ _ _ _ hmn, Int.emod_def]; ring⟩

/-- Flooring preserves an integer lower bound on a difference. -/
theorem floor_gap {N X Y q : ℤ} (hN : 0 < N) (h : q * N ≤ |X - Y|) : q ≤ |X / N - Y / N| := by
  rcases le_total Y X with hXY | hXY
  · rw [abs_of_nonneg (sub_nonneg.mpr hXY)] at h
    have : (Y + q * N) / N ≤ X / N := Int.ediv_le_ediv hN (by linarith)
    rw [Int.add_mul_ediv_right _ _ hN.ne'] at this
    exact le_trans (by linarith) (le_abs_self _)
  · rw [abs_of_nonpos (sub_nonpos.mpr hXY)] at h
    have : (X + q * N) / N ≤ Y / N := Int.ediv_le_ediv hN (by linarith)
    rw [Int.add_mul_ediv_right _ _ hN.ne'] at this
    exact le_trans (by linarith) (neg_le_abs _)

theorem exists_nearest (S a n : ℤ) (hS : 0 < S) : ∃ t : ℤ, 2 * |t * S - a * n| ≤ S := by
  refine ⟨(2 * a * n + S) / (2 * S), ?_⟩
  have h1 := Int.emod_def (2 * a * n + S) (2 * S)
  have h2 := Int.emod_nonneg (2 * a * n + S) (show 2 * S ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos (2 * a * n + S) (show 0 < 2 * S by omega)
  have : |2 * ((2 * a * n + S) / (2 * S) * S - a * n)| ≤ S := abs_le.mpr ⟨by linarith, by linarith⟩
  rwa [abs_mul, abs_two] at this

/-- Core estimate: for a lift `(i, j)`, `(i + h, j')` of two labels with `|h| ≤ k`,
`|h| + |F(i,j) - F(i+h,j')| ≥ k + 1`. -/
theorem cycF_core {k S a m n t M : ℤ} (hS : 0 < S) (hm : 0 < m) (hn : 0 < n)
    (hM : M = m * S + 1) (he : 2 * |t * S - a * n| ≤ S) (hcond : k * S * M ≤ 2 * n)
    (hlat : ∀ h z : ℤ, S ∣ z - a * h → (h, z) ≠ (0, 0) → k + 1 ≤ |h| + |z|)
    (i h j j' : ℤ) (hh : |h| ≤ k) (hne : h ≠ 0 ∨ j ≠ j') :
    k + 1 ≤ |h| + |cycF M t n m i j - cycF M t n m (i + h) j'| := by
  subst hM
  have hz0 : (h, a * h + S * (j' - j)) ≠ (0, 0) := by
    intro heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, h2⟩ := heq
    have : S * (j' - j) = 0 := by linarith
    rcases mul_eq_zero.mp this with h3 | h3
    · linarith
    · rcases hne with h4 | h4
      · exact h4 rfl
      · exact h4 (by linarith)
  have hL := hlat h _ ⟨j' - j, by ring⟩ hz0
  set z := a * h + S * (j' - j) with hz
  have hz1 : 1 ≤ |z| := by
    rcases eq_or_ne z 0 with h0 | h0
    · rw [h0, abs_zero] at hL; linarith
    · exact Int.one_le_abs h0
  have hmn : 0 < m * n := mul_pos hm hn
  have hE0 := abs_nonneg (t * S - a * n)
  have hh0 := abs_nonneg h
  have hMpos : 0 < m * S + 1 := by nlinarith
  have A : 2 * |t * S - a * n| * |h| ≤ S * k :=
    le_trans (mul_le_mul_of_nonneg_right he hh0) (mul_le_mul_of_nonneg_left hh hS.le)
  have B : (m * S + 1) * (2 * |t * S - a * n| * |h|) ≤ 2 * n :=
    le_trans (mul_le_mul_of_nonneg_left A hMpos.le) (by linarith)
  have hSXY : S * ((m * S + 1) * (t * (i + h) + j' * n) - (m * S + 1) * (t * i + j * n)) =
      (m * S + 1) * (z * n + (t * S - a * n) * h) := by rw [hz]; ring
  have C : |z * n| ≤ |z * n + (t * S - a * n) * h| + |(t * S - a * n) * h| := by
    have := abs_add_le (z * n + (t * S - a * n) * h) (-((t * S - a * n) * h))
    rwa [add_neg_cancel_right, abs_neg] at this
  rw [abs_mul, abs_mul, abs_of_pos hn] at C
  have D : |S * ((m * S + 1) * (t * (i + h) + j' * n) - (m * S + 1) * (t * i + j * n))| =
      S * |(m * S + 1) * (t * (i + h) + j' * n) - (m * S + 1) * (t * i + j * n)| := by
    rw [abs_mul, abs_of_pos hS]
  have D2 : |S * ((m * S + 1) * (t * (i + h) + j' * n) - (m * S + 1) * (t * i + j * n))| =
      (m * S + 1) * |z * n + (t * S - a * n) * h| := by
    rw [hSXY, abs_mul, abs_of_pos hMpos]
  have E1 := mul_le_mul_of_nonneg_left
    (show |z| * n - |t * S - a * n| * |h| ≤ |z * n + (t * S - a * n) * h| by linarith) hMpos.le
  have E2 : n ≤ n * |z| := le_mul_of_one_le_right hn.le hz1
  have E3 : S * (m * n * |z|) ≤
      S * |(m * S + 1) * (t * (i + h) + j' * n) - (m * S + 1) * (t * i + j * n)| := by
    rw [← D, D2]; linarith
  have E4 := le_of_mul_le_mul_left E3 hS
  have key : |z| ≤ |cycF (m * S + 1) t n m i j - cycF (m * S + 1) t n m (i + h) j'| :=
    floor_gap hmn (by rw [abs_sub_comm]; linarith)
  linarith

theorem cycle_construction (k m n : ℕ) (S a : ℤ) (hS : 0 < S) (hm : 0 < m) (hn : 0 < n)
    (hcond : (k : ℤ) * S * (m * S + 1) ≤ 2 * n)
    (hlat : ∀ h z : ℤ, S ∣ z - a * h → (h, z) ≠ (0, 0) → (k : ℤ) + 1 ≤ |h| + |z|) :
    ∃ f : Fin n → Finset ℕ, IsMultiRadioLabeling (cycleDist n) k m f ∧
      ∀ v, ∀ c ∈ f v, (c : ℤ) ≤ m * S := by
  obtain ⟨t, ht⟩ := exists_nearest S a n hS
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hmn : (m : ℤ) * n ≠ 0 := (mul_pos hm' hn').ne'
  obtain ⟨M, hMdef⟩ : ∃ M : ℤ, M = m * S + 1 := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; nlinarith
  rw [← hMdef] at hcond
  obtain ⟨F, hF⟩ : ∃ F : ℤ → ℤ → ℤ, F = cycF M t n m := ⟨_, rfl⟩
  have hcore : ∀ i h j j' : ℤ, |h| ≤ k → (h ≠ 0 ∨ j ≠ j') → (k : ℤ) + 1 ≤ |h| + |F i j - F (i + h) j'| := by
    subst hF; exact fun i h j j' => cycF_core hS hm' hn' hMdef ht hcond hlat i h j j'
  have hrep : ∀ i j : ℤ, ∃ w, F i j % M = F i (j + m * w) := by
    subst hF; exact fun i j => cycF_emod _ _ _ _ _ _ hmn
  have hshift : ∀ i j w : ℤ, F (i + n * w) j = F i (j + t * w) := by
    subst hF; exact fun i j w => cycF_shift _ _ _ _ _ _ _
  have hnn : ∀ x : ℤ, ((x % M).toNat : ℤ) = x % M := fun x => Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  have hmem : ∀ (v : Fin n) (c : ℕ),
      c ∈ (Finset.range m).image (fun j : ℕ => (F (v.val : ℤ) j % M).toNat) →
      ∃ J, (c : ℤ) = F v.val J := by
    intro v c hc
    simp only [Finset.mem_image, Finset.mem_range] at hc
    obtain ⟨j, -, rfl⟩ := hc
    obtain ⟨w, hw⟩ := hrep v.val j
    exact ⟨_, by rw [hnn, hw]⟩
  refine ⟨fun i => (Finset.range m).image fun j : ℕ => (F (i.val : ℤ) j % M).toNat,
    isMultiRadioLabeling_of (fun v => by simp [cycleDist]) (fun v => ?_) ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.coe_range, Set.mem_Iio] at hj₁ hj₂ heq
    have heq' : F v.val j₁ % M = F v.val j₂ % M := by rw [← hnn, ← hnn (F v.val j₂), heq]
    obtain ⟨w₁, hw₁⟩ := hrep v.val j₁
    obtain ⟨w₂, hw₂⟩ := hrep v.val j₂
    rw [hw₁, hw₂] at heq'
    have hJ : (j₁ : ℤ) + m * w₁ = j₂ + m * w₂ := by
      by_contra hne
      have := hcore v.val 0 _ _ (by simp) (Or.inr hne)
      rw [add_zero, heq', sub_self, abs_zero] at this
      have : (0 : ℤ) ≤ k := by positivity
      linarith
    have hd : (m : ℤ) ∣ (j₁ : ℤ) - j₂ := ⟨w₂ - w₁, by linarith⟩
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    omega
  · intro u v c₁ h₁ c₂ h₂ huv
    obtain ⟨J₁, hc₁⟩ := hmem u c₁ h₁
    obtain ⟨J₂, hc₂⟩ := hmem v c₂ h₂
    obtain ⟨h, habs, hmod⟩ := cycleDist_exists n u v
    obtain ⟨w, hw⟩ := Int.ModEq.dvd hmod
    have hv : (v.val : ℤ) = u.val + h + n * w := by linarith
    rw [hv, hshift] at hc₂
    by_cases hfar : k < cycleDist n u v
    · omega
    have hh : |h| ≤ k := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast (show h.natAbs ≤ k by omega)
    have hne : h ≠ 0 ∨ J₁ ≠ J₂ + t * w := by
      by_contra hcon
      push Not at hcon
      obtain ⟨rfl, hJ⟩ := hcon
      have hu := u.isLt
      have hv' := v.isLt
      have huv' : u = v := by
        have hd : (n : ℤ) ∣ (v.val : ℤ) - u.val := ⟨w, by linarith⟩
        have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
        exact Fin.ext (by omega)
      have hcc : c₁ = c₂ := by
        have : (c₁ : ℤ) = c₂ := by rw [hc₁, hc₂, add_zero, hJ]
        exact_mod_cast this
      rcases huv with huv | huv <;> contradiction
    have := hcore u.val h J₁ (J₂ + t * w) hh hne
    rw [← hc₁, ← hc₂, Int.abs_eq_natAbs, Int.abs_eq_natAbs, habs] at this
    exact_mod_cast this
  · intro v c hc
    simp only [Finset.mem_image, Finset.mem_range] at hc
    obtain ⟨j, -, rfl⟩ := hc
    rw [hnn]
    have := Int.emod_lt_of_pos (F v.val j) hM
    linarith

/-- Conjecture 2: if `k S (m S + 1) ≤ 2 n`, then `C_n` has an `(m,k)`-radio labeling with all
labels in `[0, m S]`. -/
theorem conjecture2_cycle (k m n : ℕ) (_hk : 1 ≤ k) (hm : 1 ≤ m) (hn : 3 ≤ n)
    (hcond : k * S_val k * (m * S_val k + 1) ≤ 2 * n) :
    ∃ f : Fin n → Finset ℕ, IsMultiRadioLabeling (cycleDist n) k m f ∧
      ∀ v, ∀ c ∈ f v, c ≤ m * S_val k := by
  obtain ⟨f, hf, hb⟩ := cycle_construction k m n (S_val k) (aVal k)
    (by exact_mod_cast S_val_pos k) (by omega) (by omega) (by exact_mod_cast hcond)
    (lattice_min_norm_abs k)
  exact ⟨f, hf, fun v c hc => by exact_mod_cast hb v c hc⟩

end TogniRadio

#print axioms TogniRadio.lattice_min_norm
#print axioms TogniRadio.S_val_eq_ceil
#print axioms TogniRadio.cycleDist_exists
#print axioms TogniRadio.conjecture1_path_upper_bound
#print axioms TogniRadio.conjecture2_cycle
