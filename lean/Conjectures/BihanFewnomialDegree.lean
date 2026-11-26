import Mathlib

/-!
# Bihan (arXiv:2611.34336v1): Sharp 3D Bound and `D(3, 3) = {0, 1, 2, 3}`

Resolution of the first open case (`n = k = 3`) and general `n = 3` upper bound in
F. Bihan, *Descartes' rule of signs for the topological degree*, arXiv:2611.34336v1
(math.CO, 25 Nov 2026), Introduction (after Theorem 2') and Section 5.

## Main Results

1. **General 3D upper bound (`bihan_3d_degree_bound`):**
   For any oriented simplicial 2-sphere triangulation (the boundary of a simplicial
   3-polytope with `V` vertices and `F = 2 * V - 4` triangular facets) and any
   coefficient map `C : Fin V → Fin 3 → K` over a linearly ordered field `K` satisfying
   `(UC)` (all `3 × 3` determinants nonzero), the combinatorial degree `d` of Bihan's
   Theorem 1.3 satisfies:
   * the exact algebraic identity `4 * d = 2 * ∑ v, w_v - F₊ + F₋`,
   * the local winding bound `2 * w_v ≤ p_v - 1` at every vertex `v`, and
   * the global bound `4 * |d| ≤ 3 * V - 8`, i.e. `|d| ≤ (3 * V - 8) / 4`.
   In particular, for `V ≤ 7` (`n = k = 3`, `N = 7`), `|d| ≤ 3`, refuting sharpness
   of Bihan's Theorem 2 (`|deg F| ≤ 4`).

   The proof is purely algebraic over any linearly ordered field `K`:
   - an 8-case Boolean identity relates `2 * s * (I(+u) + I(-u))` to the 3 vertex
     crossings around each facet minus `s`,
   - the 3D Grassmann–Plücker identity proves ray-independence of the local link
     winding number `w_v(r)` by a telescoping sum around the closed link, and
   - evaluating `w_v(+q) + w_v(-q)` at a perturbed link ray `q = t • C_{a₁} ∓ C_{a₂}`
     proves `2 * w_v ≤ p_v - 1` directly.

2. **Exact integer realizations (`n7_realizes_0..3`, `extremal_V8..V12`):**
   Explicit integer exponent and coefficient matrices `(A, C)` satisfying `(UA)` and
   `(UC)` realize `|deg F| = 0, 1, 2, 3` for `N = 7` (giving `D(3, 3) = {0, 1, 2, 3}`)
   and attain the extremal bound `⌊(3V - 8)/4⌋` for `V = 8, 9, 10, 12` (including
   an integer perturbation of the great icosahedron `{3, 5/2}` of density `7`).
-/

namespace BihanFewnomialDegree

/-! ### Section 1: 3D Determinants, Crossings, and Plücker Telescoping -/

section Det3

variable {K : Type*} [CommRing K]

/-- Explicit `3 × 3` determinant of three vectors in `K³`. -/
def det3 (a b c : Fin 3 → K) : K :=
  a 0 * (b 1 * c 2 - b 2 * c 1)
  - a 1 * (b 0 * c 2 - b 2 * c 0)
  + a 2 * (b 0 * c 1 - b 1 * c 0)

lemma det3_cyclic (a b c : Fin 3 → K) : det3 a b c = det3 b c a := by
  unfold det3; ring

lemma det3_swap23 (a b c : Fin 3 → K) : det3 a c b = -det3 a b c := by
  unfold det3; ring

lemma det3_swap12 (a b c : Fin 3 → K) : det3 b a c = -det3 a b c := by
  unfold det3; ring

lemma det3_neg3 (a b c : Fin 3 → K) : det3 a b (-c) = -det3 a b c := by
  simp only [det3, Pi.neg_apply]; ring

lemma det3_neg2 (a b c : Fin 3 → K) : det3 a (-b) c = -det3 a b c := by
  simp only [det3, Pi.neg_apply]; ring

lemma det3_add3 (a b c d : Fin 3 → K) : det3 a b (c + d) = det3 a b c + det3 a b d := by
  simp only [det3, Pi.add_apply]; ring

lemma det3_sub3 (a b c d : Fin 3 → K) : det3 a b (c - d) = det3 a b c - det3 a b d := by
  simp only [det3, Pi.sub_apply]; ring

lemma det3_smul3 (a b : Fin 3 → K) (t : K) (c : Fin 3 → K) :
    det3 a b (t • c) = t * det3 a b c := by
  simp only [det3, Pi.smul_apply, smul_eq_mul]; ring

lemma det3_self23 (a b : Fin 3 → K) : det3 a b b = 0 := by
  unfold det3; ring

/-- The 3D Grassmann–Plücker identity for `Δ(x, y) = det3 c x y`. -/
lemma det3_plucker (c r r' a b : Fin 3 → K) :
    det3 c r a * det3 c b r' - det3 c r b * det3 c a r' + det3 c r r' * det3 c a b = 0 := by
  unfold det3; ring

end Det3

section AlgebraicBound

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Sign function `K → ℤ` returning `+1`, `0`, or `-1`. -/
def ksgn (x : K) : ℤ :=
  if 0 < x then 1 else if x < 0 then -1 else 0

omit [IsStrictOrderedRing K] in
lemma ksgn_pos {x : K} (hx : 0 < x) : ksgn x = 1 := by
  simp [ksgn, hx]

omit [IsStrictOrderedRing K] in
lemma ksgn_neg {x : K} (hx : x < 0) : ksgn x = -1 := by
  simp [ksgn, hx, not_lt.mpr hx.le]

lemma ksgn_neg_arg (x : K) : ksgn (-x) = -ksgn x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [ksgn_neg h, ksgn_pos (neg_pos.mpr h)]; ring
  · simp [ksgn]
  · rw [ksgn_pos h, ksgn_neg (neg_lt_zero.mpr h)]

omit [IsStrictOrderedRing K] in
lemma ksgn_ne_zero_cases {x : K} (hx : x ≠ 0) : ksgn x = 1 ∨ ksgn x = -1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · right; exact ksgn_neg h
  · left; exact ksgn_pos h

/-- Cone membership indicator `1` if `u ∈ open cone(a, b, c)`, else `0`. -/
def inConeInd (u a b c : Fin 3 → K) : ℤ :=
  let s := ksgn (det3 a b c)
  if s ≠ 0 ∧ ksgn (det3 u b c) = s ∧ ksgn (det3 a u c) = s ∧ ksgn (det3 a b u) = s then 1 else 0

/-- Signed ray-crossing indicator for an oriented step `(a → b)` around `c` crossing ray `r`. -/
def crossInd (c r a b : Fin 3 → K) : ℤ :=
  let s := ksgn (det3 c a b)
  if s ≠ 0 ∧ ksgn (det3 c a r) = s ∧ ksgn (det3 c r b) = s then s else 0

/-- Wedge indicator `1` if vector `a` lies strictly in the counter-clockwise wedge `(r, r')` around `c`. -/
def wedgeInd (c r r' a : Fin 3 → K) : ℤ :=
  if 0 < det3 c r a ∧ 0 < det3 c a r' then 1 else 0

/-- **8-case Boolean identity** for a single nondegenerate triple `(a, b, c)` and generic ray `u`:
`2 * s * (I(+u) + I(-u)) = cross(a, u; b, c) + cross(a, -u; b, c) + ... - s`. -/
lemma single_facet_identity (a b c u : Fin 3 → K)
    (hdet : det3 a b c ≠ 0)
    (hu1 : det3 u b c ≠ 0) (hu2 : det3 a u c ≠ 0) (hu3 : det3 a b u ≠ 0) :
    2 * ksgn (det3 a b c) * (inConeInd u a b c + inConeInd (-u) a b c) =
      (crossInd a u b c + crossInd a (-u) b c) +
      (crossInd b u c a + crossInd b (-u) c a) +
      (crossInd c u a b + crossInd c (-u) a b) - ksgn (det3 a b c) := by
  have hbc : det3 b c a = det3 a b c := (det3_cyclic a b c).symm
  have hcab : det3 c a b = det3 a b c := by rw [det3_cyclic, det3_cyclic]
  have e3 : det3 b c u = det3 u b c := (det3_cyclic u b c).symm
  have e4 : det3 b u a = det3 a b u := by unfold det3; ring
  have e5 : det3 c a u = det3 a u c := by unfold det3; ring
  have e6 : det3 c u b = det3 u b c := by unfold det3; ring
  have e7 : det3 a b (-u) = -det3 a b u := det3_neg3 a b u
  have e8 : det3 a (-u) c = -det3 a u c := det3_neg2 a u c
  have e9 : det3 b c (-u) = -det3 u b c := by rw [det3_neg3, e3]
  have e10 : det3 b (-u) a = -det3 a b u := by rw [det3_neg2, e4]
  have e11 : det3 c a (-u) = -det3 a u c := by rw [det3_neg3, e5]
  have e12 : det3 c (-u) b = -det3 u b c := by rw [det3_neg2, e6]
  have e13 : det3 (-u) b c = -det3 u b c := by unfold det3; simp only [Pi.neg_apply]; ring
  unfold inConeInd crossInd
  rw [hbc, hcab, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13]
  simp only [ksgn_neg_arg]
  rcases ksgn_ne_zero_cases hdet with hs | hs <;>
  rcases ksgn_ne_zero_cases hu1 with h1 | h1 <;>
  rcases ksgn_ne_zero_cases hu2 with h2 | h2 <;>
  rcases ksgn_ne_zero_cases hu3 with h3 | h3 <;>
  simp [hs, h1, h2, h3]

/-- Boolean truth-table core of the Plücker telescoping lemma (32 cases by `decide`). -/
private lemma crossInd_sub_bool (s_ab s_ra s_ar' s_rb s_br' : Bool)
    (hpl : ¬ ((s_ra == s_br') = s_ab ∧ (s_rb != s_ar') = s_ab)) :
    (let s : ℤ := if s_ab then 1 else -1
     (if (if s_ar' then (1 : ℤ) else -1) = s ∧ (if s_br' then (-1 : ℤ) else 1) = s then s else 0) -
     (if (if s_ra then (-1 : ℤ) else 1) = s ∧ (if s_rb then (1 : ℤ) else -1) = s then s else 0)) =
    (if s_ra && s_ar' then (1 : ℤ) else 0) - (if s_rb && s_br' then (1 : ℤ) else 0) := by
  revert s_ab s_ra s_ar' s_rb s_br' hpl; decide

/-- **Plücker telescoping lemma** for a single link edge `(a → b)` around `c`,
when `det3 c r r' > 0`. -/
lemma crossInd_sub_eq_wedge_sub (c r r' a b : Fin 3 → K)
    (hrr' : 0 < det3 c r r')
    (hab : det3 c a b ≠ 0)
    (har : det3 c a r ≠ 0) (har' : det3 c a r' ≠ 0)
    (hbr : det3 c b r ≠ 0) (hbr' : det3 c b r' ≠ 0) :
    crossInd c r' a b - crossInd c r a b = wedgeInd c r r' a - wedgeInd c r r' b := by
  have hpl := det3_plucker c r r' a b
  have hra : det3 c r a = -det3 c a r := det3_swap23 c a r
  have hrb : det3 c r b = -det3 c b r := det3_swap23 c b r
  have hr'b : det3 c r' b = -det3 c b r' := det3_swap23 c b r'
  have hra_ne : det3 c r a ≠ 0 := by rw [hra]; exact neg_ne_zero.mpr har
  have hrb_ne : det3 c r b ≠ 0 := by rw [hrb]; exact neg_ne_zero.mpr hbr
  set s_ab : Bool := decide (0 < det3 c a b)
  set s_ra : Bool := decide (0 < det3 c r a)
  set s_ar' : Bool := decide (0 < det3 c a r')
  set s_rb : Bool := decide (0 < det3 c r b)
  set s_br' : Bool := decide (0 < det3 c b r')
  have hsgn : ∀ {x : K}, x ≠ 0 → ksgn x = if decide (0 < x) then 1 else -1 := by
    intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · rw [ksgn_neg h, decide_eq_false (not_lt.mpr h.le)]; rfl
    · rw [ksgn_pos h, decide_eq_true h]; rfl
  have hpl_bool : ¬ ((s_ra == s_br') = s_ab ∧ (s_rb != s_ar') = s_ab) := by
    rintro ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hab with hab_n | hab_p
    · have hs : s_ab = false := decide_eq_false (not_lt.mpr hab_n.le)
      rw [hs] at h1 h2
      have ht1 : det3 c r a * det3 c b r' < 0 := by
        rcases lt_or_gt_of_ne hra_ne with ha | ha <;> rcases lt_or_gt_of_ne hbr' with hb | hb
        · simp [s_ra, s_br', not_lt.mpr ha.le, not_lt.mpr hb.le] at h1
        · exact mul_neg_of_neg_of_pos ha hb
        · exact mul_neg_of_pos_of_neg ha hb
        · simp [s_ra, s_br', ha, hb] at h1
      have ht2 : -(det3 c r b * det3 c a r') < 0 := by
        rcases lt_or_gt_of_ne hrb_ne with hb | hb <;> rcases lt_or_gt_of_ne har' with ha | ha
        · linarith [mul_pos_of_neg_of_neg hb ha]
        · simp [s_rb, s_ar', not_lt.mpr hb.le, ha] at h2
        · simp [s_rb, s_ar', hb, not_lt.mpr ha.le] at h2
        · linarith [mul_pos hb ha]
      have ht3 : det3 c r r' * det3 c a b < 0 := mul_neg_of_pos_of_neg hrr' hab_n
      linarith
    · have hs : s_ab = true := decide_eq_true hab_p
      rw [hs] at h1 h2
      have ht1 : 0 < det3 c r a * det3 c b r' := by
        rcases lt_or_gt_of_ne hra_ne with ha | ha <;> rcases lt_or_gt_of_ne hbr' with hb | hb
        · exact mul_pos_of_neg_of_neg ha hb
        · simp [s_ra, s_br', not_lt.mpr ha.le, hb] at h1
        · simp [s_ra, s_br', ha, not_lt.mpr hb.le] at h1
        · exact mul_pos ha hb
      have ht2 : 0 < -(det3 c r b * det3 c a r') := by
        rcases lt_or_gt_of_ne hrb_ne with hb | hb <;> rcases lt_or_gt_of_ne har' with ha | ha
        · simp [s_rb, s_ar', not_lt.mpr hb.le, not_lt.mpr ha.le] at h2
        · linarith [mul_neg_of_neg_of_pos hb ha]
        · linarith [mul_neg_of_pos_of_neg hb ha]
        · simp [s_rb, s_ar', hb, ha] at h2
      have ht3 : 0 < det3 c r r' * det3 c a b := mul_pos hrr' hab_p
      linarith
  have hcore := crossInd_sub_bool s_ab s_ra s_ar' s_rb s_br' hpl_bool
  unfold crossInd wedgeInd
  rw [show det3 c a r = -det3 c r a by rw [hra, neg_neg], hr'b]
  simp only [ksgn_neg_arg]
  rw [hsgn hab, hsgn hra_ne, hsgn har', hsgn hrb_ne, hsgn hbr']
  have hne : (if s_ab then (1 : ℤ) else -1) ≠ 0 := by cases s_ab <;> decide
  have hw1 : (if 0 < det3 c r a ∧ 0 < det3 c a r' then (1 : ℤ) else 0) =
      if s_ra && s_ar' then 1 else 0 := by
    dsimp [s_ra, s_ar']; by_cases ha : 0 < det3 c r a <;> by_cases hb : 0 < det3 c a r' <;> simp [ha, hb]
  have hw2 : (if 0 < det3 c r b ∧ 0 < det3 c b r' then (1 : ℤ) else 0) =
      if s_rb && s_br' then 1 else 0 := by
    dsimp [s_rb, s_br']; by_cases ha : 0 < det3 c r b <;> by_cases hb : 0 < det3 c b r' <;> simp [ha, hb]
  have hneg1 : -(if s_br' then (1 : ℤ) else -1) = if s_br' then -1 else 1 := by cases s_br' <;> rfl
  have hneg2 : -(if s_ra then (1 : ℤ) else -1) = if s_ra then -1 else 1 := by cases s_ra <;> rfl
  change (if (if s_ab then (1 : ℤ) else -1) ≠ 0 ∧
      (if s_ar' then (1 : ℤ) else -1) = (if s_ab then 1 else -1) ∧
      -(if s_br' then (1 : ℤ) else -1) = (if s_ab then 1 else -1)
    then (if s_ab then (1 : ℤ) else -1) else 0) -
    (if (if s_ab then (1 : ℤ) else -1) ≠ 0 ∧
      -(if s_ra then (1 : ℤ) else -1) = (if s_ab then 1 else -1) ∧
      (if s_rb then (1 : ℤ) else -1) = (if s_ab then 1 else -1)
    then (if s_ab then (1 : ℤ) else -1) else 0) = _
  rw [hw1, hw2, hneg1, hneg2]
  cases hs : s_ab <;> simpa [hs] using hcore

/-- Every finite set in a linearly ordered field has a strictly positive element outside it. -/
private lemma exists_pos_not_mem (s : Finset K) : ∃ t : K, 0 < t ∧ t ∉ s := by
  let M : K := (insert (0 : K) s).max' (Finset.insert_nonempty 0 s)
  have h0M : 0 ≤ M := Finset.le_max' _ 0 (Finset.mem_insert_self 0 s)
  refine ⟨M + 1, by linarith, fun hmem => ?_⟩
  have hle : M + 1 ≤ M := Finset.le_max' _ (M + 1) (Finset.mem_insert_of_mem hmem)
  linarith

/-- Winding number of a cyclic link `cyc : Fin m → Fin 3 → K` around `c` with respect to ray `r`. -/
def linkWind {m : ℕ} (hm : 0 < m) (c r : Fin 3 → K) (cyc : Fin m → Fin 3 → K) : ℤ :=
  ∑ i : Fin m, crossInd c r (cyc i) (cyc ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩)

/-- Telescoping around a cyclic link proves `linkWind r' = linkWind r` whenever `det3 c r r' > 0`. -/
lemma linkWind_eq_of_det_pos {m : ℕ} (hm : 0 < m) (c r r' : Fin 3 → K) (cyc : Fin m → Fin 3 → K)
    (hrr' : 0 < det3 c r r')
    (hstep : ∀ i : Fin m, det3 c (cyc i) (cyc ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩) ≠ 0)
    (hr : ∀ i : Fin m, det3 c (cyc i) r ≠ 0)
    (hr' : ∀ i : Fin m, det3 c (cyc i) r' ≠ 0) :
    linkWind hm c r' cyc = linkWind hm c r cyc := by
  unfold linkWind
  suffices hdiff : ∑ i : Fin m, (crossInd c r' (cyc i) (cyc ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩) -
      crossInd c r (cyc i) (cyc ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩)) = 0 by
    rw [Finset.sum_sub_distrib] at hdiff
    exact sub_eq_zero.mp hdiff
  have hcongr : ∑ i : Fin m, (crossInd c r' (cyc i) (cyc ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩) -
      crossInd c r (cyc i) (cyc ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩)) =
      ∑ i : Fin m, (wedgeInd c r r' (cyc i) - wedgeInd c r r' (cyc ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact crossInd_sub_eq_wedge_sub c r r' (cyc i) (cyc ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩)
      hrr' (hstep i) (hr i) (hr' i) (hr _) (hr' _)
  rw [hcongr, Finset.sum_sub_distrib]
  have hshift : ∑ i : Fin m, wedgeInd c r r' (cyc ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩) =
      ∑ i : Fin m, wedgeInd c r r' (cyc i) := by
    refine Finset.sum_bij (fun (i : Fin m) _ => (⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩ : Fin m))
      (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · intro i₁ _ i₂ _ hEq
      have hv := congrArg Fin.val hEq
      dsimp at hv
      have h1 := i₁.isLt
      have h2 := i₂.isLt
      by_cases hi1 : i₁.val + 1 < m <;> by_cases hi2 : i₂.val + 1 < m
      · rw [Nat.mod_eq_of_lt hi1, Nat.mod_eq_of_lt hi2] at hv; exact Fin.ext (by omega)
      · have : i₂.val + 1 = m := by omega
        rw [Nat.mod_eq_of_lt hi1, this, Nat.mod_self] at hv; omega
      · have : i₁.val + 1 = m := by omega
        rw [this, Nat.mod_self, Nat.mod_eq_of_lt hi2] at hv; omega
      · exact Fin.ext (by omega)
    · intro j _
      by_cases hj : j.val = 0
      · refine ⟨⟨m - 1, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
        dsimp; rw [show m - 1 + 1 = m by omega, Nat.mod_self, hj]
      · refine ⟨⟨j.val - 1, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
        dsimp; rw [show j.val - 1 + 1 = j.val by omega, Nat.mod_eq_of_lt j.isLt]
  rw [hshift, sub_self]

/-- **Ray-independence of the link winding number:** for ANY two generic rays `r, r'`,
`linkWind hm c r' cyc = linkWind hm c r cyc`. -/
lemma linkWind_ray_independent {m : ℕ} (hm : 0 < m) (c r r' : Fin 3 → K) (cyc : Fin m → Fin 3 → K)
    (hstep : ∀ i : Fin m, det3 c (cyc i) (cyc ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩) ≠ 0)
    (hr : ∀ i : Fin m, det3 c (cyc i) r ≠ 0)
    (hr' : ∀ i : Fin m, det3 c (cyc i) r' ≠ 0) :
    linkWind hm c r' cyc = linkWind hm c r cyc := by
  rcases lt_trichotomy (det3 c r r') 0 with hlt | heq | hgt
  · have hpos : 0 < det3 c r' r := by rw [det3_swap23]; linarith
    exact (linkWind_eq_of_det_pos hm c r' r cyc hpos hstep hr' hr).symm
  · let i0 : Fin m := ⟨0, hm⟩
    have h0 : det3 c r (cyc i0) ≠ 0 := by rw [det3_swap23]; exact neg_ne_zero.mpr (hr i0)
    have h0' : det3 c r' (cyc i0) ≠ 0 := by rw [det3_swap23]; exact neg_ne_zero.mpr (hr' i0)
    let bad : Finset K := Finset.univ.image (fun i : Fin m => -(det3 c (cyc i) r) / det3 c (cyc i) (cyc i0))
    obtain ⟨t, ht_pos, ht_not⟩ := exists_pos_not_mem bad
    let q : Fin 3 → K := r + t • cyc i0
    have hq_gen : ∀ i : Fin m, det3 c (cyc i) q ≠ 0 := by
      intro i hi
      have hlin : det3 c (cyc i) q = det3 c (cyc i) r + t * det3 c (cyc i) (cyc i0) := by
        dsimp [q]; rw [det3_add3, det3_smul3]
      rw [hlin] at hi
      by_cases hci : det3 c (cyc i) (cyc i0) = 0
      · rw [hci, mul_zero, add_zero] at hi; exact hr i hi
      · apply ht_not
        refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
        field_simp [hci]; linarith
    have hrq : det3 c r q ≠ 0 := by
      dsimp [q]; rw [det3_add3, det3_self23, zero_add, det3_smul3]
      exact mul_ne_zero ht_pos.ne' h0
    have hr'q : det3 c r' q ≠ 0 := by
      dsimp [q]; rw [det3_add3, det3_swap23, heq, neg_zero, zero_add, det3_smul3]
      exact mul_ne_zero ht_pos.ne' h0'
    have h1 : linkWind hm c q cyc = linkWind hm c r cyc := by
      rcases lt_or_gt_of_ne hrq with h | h
      · exact (linkWind_eq_of_det_pos hm c q r cyc (by rw [det3_swap23]; linarith) hstep hq_gen hr).symm
      · exact linkWind_eq_of_det_pos hm c r q cyc h hstep hr hq_gen
    have h2 : linkWind hm c r' cyc = linkWind hm c q cyc := by
      rcases lt_or_gt_of_ne hr'q with h | h
      · exact linkWind_eq_of_det_pos hm c q r' cyc (by rw [det3_swap23]; linarith) hstep hq_gen hr'
      · exact (linkWind_eq_of_det_pos hm c r' q cyc h hstep hr' hq_gen).symm
    exact h2.trans h1
  · exact linkWind_eq_of_det_pos hm c r r' cyc hgt hstep hr hr'

/-- For a single step `(a → b)` around `c` and any ray `q`, the combined crossing
`crossInd c q a b + crossInd c (-q) a b` is at most `1` if `det3 c a b > 0` and at most `0` if `det3 c a b < 0`. -/
lemma crossInd_add_neg_le (c q a b : Fin 3 → K) (hab : det3 c a b ≠ 0) :
    crossInd c q a b + crossInd c (-q) a b ≤ if 0 < det3 c a b then 1 else 0 := by
  unfold crossInd
  rw [det3_neg3, det3_neg2]
  simp only [ksgn_neg_arg]
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hs : ksgn (det3 c a b) = -1 := ksgn_neg hlt
    rw [hs, if_neg (not_lt.mpr hlt.le)]
    split_ifs <;> omega
  · have hs : ksgn (det3 c a b) = 1 := ksgn_pos hgt
    rw [hs, if_pos hgt]
    by_cases h1 : ksgn (det3 c a q) = 1
    · simp [h1]; split_ifs <;> omega
    · simp [h1]; split_ifs <;> omega

/-- **Local winding bound (`2 * w_v ≤ p_v - 1`):**
For any closed cyclic link around `c` with nondegenerate steps,
`2 * linkWind hm c r cyc ≤ (number of positive steps) - 1`. -/
theorem two_mul_linkWind_le_posCount_sub_one {m : ℕ} (hm : 0 < m)
    (c r : Fin 3 → K) (cyc : Fin m → Fin 3 → K)
    (hstep : ∀ i : Fin m, det3 c (cyc i) (cyc ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩) ≠ 0)
    (hr : ∀ i : Fin m, det3 c (cyc i) r ≠ 0) :
    2 * linkWind hm c r cyc ≤
      (∑ i : Fin m, if 0 < det3 c (cyc i) (cyc ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩) then (1 : ℤ) else 0) - 1 := by
  let next : Fin m → Fin m := fun i => ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩
  let posInd : Fin m → ℤ := fun i => if 0 < det3 c (cyc i) (cyc (next i)) then 1 else 0
  -- Helper: given any generic ray `q` and a witness `i₀` where `crossInd(q) + crossInd(-q) ≤ posInd i₀ - 1`, we win!
  have hfrom : ∀ (q : Fin 3 → K) (i₀ : Fin m),
      (∀ i : Fin m, det3 c (cyc i) q ≠ 0) →
      crossInd c q (cyc i₀) (cyc (next i₀)) + crossInd c (-q) (cyc i₀) (cyc (next i₀)) ≤ posInd i₀ - 1 →
      2 * linkWind hm c r cyc ≤ (∑ i : Fin m, posInd i) - 1 := by
    intro q i₀ hq hstrict
    have hq_neg : ∀ i : Fin m, det3 c (cyc i) (-q) ≠ 0 := fun i => by
      rw [det3_neg3]; exact neg_ne_zero.mpr (hq i)
    have hw1 : linkWind hm c q cyc = linkWind hm c r cyc :=
      linkWind_ray_independent hm c r q cyc hstep hr hq
    have hw2 : linkWind hm c (-q) cyc = linkWind hm c r cyc :=
      linkWind_ray_independent hm c r (-q) cyc hstep hr hq_neg
    have h2w : 2 * linkWind hm c r cyc =
        ∑ i : Fin m, (crossInd c q (cyc i) (cyc (next i)) + crossInd c (-q) (cyc i) (cyc (next i))) := by
      calc 2 * linkWind hm c r cyc
          = linkWind hm c r cyc + linkWind hm c r cyc := two_mul _
        _ = linkWind hm c q cyc + linkWind hm c (-q) cyc := by rw [hw1, hw2]
        _ = ∑ i : Fin m, (crossInd c q (cyc i) (cyc (next i)) + crossInd c (-q) (cyc i) (cyc (next i))) := by
            unfold linkWind; rw [← Finset.sum_add_distrib]
    rw [h2w]
    have hsum_erase :
        ∑ i ∈ Finset.univ.erase i₀,
          (crossInd c q (cyc i) (cyc (next i)) + crossInd c (-q) (cyc i) (cyc (next i))) ≤
        ∑ i ∈ Finset.univ.erase i₀, posInd i :=
      Finset.sum_le_sum fun i _ => crossInd_add_neg_le c q (cyc i) (cyc (next i)) (hstep i)
    have hlhs := Finset.add_sum_erase Finset.univ
      (fun i => crossInd c q (cyc i) (cyc (next i)) + crossInd c (-q) (cyc i) (cyc (next i)))
      (Finset.mem_univ i₀)
    have hrhs := Finset.add_sum_erase Finset.univ posInd (Finset.mem_univ i₀)
    linarith
  -- Helper: if `det3 c a b ≠ 0` and `hstep i`, then `det3 c (cyc i) a` and `det3 c (cyc i) b` cannot both be 0.
  have hnot_both_zero : ∀ (a b : Fin 3 → K) (i : Fin m), det3 c a b ≠ 0 →
      det3 c (cyc i) a = 0 → det3 c (cyc i) b ≠ 0 := by
    intro a b i hab ha0 hb0
    have hpl := det3_plucker c a b (cyc i) (cyc (next i))
    have ha0' : det3 c a (cyc i) = 0 := by rw [det3_swap23, ha0, neg_zero]
    have hb0' : det3 c (cyc i) b = 0 := hb0
    rw [ha0', zero_mul, zero_sub] at hpl
    have : det3 c a (cyc (next i)) * det3 c (cyc i) b = 0 := by rw [hb0', mul_zero]
    -- Wait: `det3_plucker c a b (cyc i) (cyc (next i))` is `det3 c a (cyc i) * det3 c (cyc (next i)) b - det3 c a (cyc (next i)) * det3 c (cyc i) b + det3 c a b * det3 c (cyc i) (cyc (next i)) = 0`!
    rw [hb0', mul_zero, neg_zero, zero_add] at hpl
    exact mul_ne_zero hab (hstep i) hpl
  by_cases hex : ∃ i₀ : Fin m, 0 < det3 c (cyc i₀) (cyc (next i₀))
  · -- Case 1: there is at least one positive step `(a → b)`. Take `q = t • a - b` for large `t > 0`.
    rcases hex with ⟨i₀, hpos⟩
    let a := cyc i₀
    let b := cyc (next i₀)
    let bad : Finset K := Finset.univ.image (fun i : Fin m => det3 c (cyc i) b / det3 c (cyc i) a)
    obtain ⟨t, ht_pos, ht_not⟩ := exists_pos_not_mem bad
    let q : Fin 3 → K := t • a - b
    have hq_gen : ∀ i : Fin m, det3 c (cyc i) q ≠ 0 := by
      intro i hi
      have hlin : det3 c (cyc i) q = t * det3 c (cyc i) a - det3 c (cyc i) b := by
        dsimp [q]; rw [det3_sub3, det3_smul3]
      rw [hlin] at hi
      by_cases hca : det3 c (cyc i) a = 0
      · rw [hca, mul_zero, zero_sub, neg_eq_zero] at hi
        exact hnot_both_zero a b i hpos.ne' hca hi
      · apply ht_not
        refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
        field_simp [hca]; linarith
    refine hfrom q i₀ hq_gen ?_
    have hposInd : posInd i₀ = 1 := if_pos hpos
    rw [hposInd]
    have hc1 : crossInd c q a b = 0 := by
      unfold crossInd
      have hda : det3 c a q = -det3 c a b := by
        dsimp [q]; rw [det3_sub3, det3_smul3, det3_self23, mul_zero, zero_sub]
      rw [hda, ksgn_neg_arg, ksgn_pos hpos]
      norm_num
    have hc2 : crossInd c (-q) a b = 0 := by
      unfold crossInd
      have hdb : det3 c (-q) b = -t * det3 c a b := by
        have : -q = b - t • a := by dsimp [q]; abel
        rw [this, det3_swap23, det3_sub3, det3_self23, zero_sub, det3_smul3, det3_swap23]
        ring
      have hneg : det3 c (-q) b < 0 := by rw [hdb]; nlinarith
      rw [ksgn_pos hpos, ksgn_neg hneg]
      norm_num
    rw [hc1, hc2]; norm_num
  · -- Case 2: ALL steps are negative (`posInd i = 0` for all `i`). Take `q = t • a + b` at `i₀ = ⟨0, hm⟩`.
    push Not at hex
    let i₀ : Fin m := ⟨0, hm⟩
    let a := cyc i₀
    let b := cyc (next i₀)
    have hneg : det3 c a b < 0 := lt_of_le_of_ne (hex i₀) (hstep i₀)
    let bad : Finset K := Finset.univ.image (fun i : Fin m => -(det3 c (cyc i) b) / det3 c (cyc i) a)
    obtain ⟨t, ht_pos, ht_not⟩ := exists_pos_not_mem bad
    let q : Fin 3 → K := t • a + b
    have hq_gen : ∀ i : Fin m, det3 c (cyc i) q ≠ 0 := by
      intro i hi
      have hlin : det3 c (cyc i) q = t * det3 c (cyc i) a + det3 c (cyc i) b := by
        dsimp [q]; rw [det3_add3, det3_smul3]
      rw [hlin] at hi
      by_cases hca : det3 c (cyc i) a = 0
      · rw [hca, mul_zero, zero_add] at hi
        exact hnot_both_zero a b i hneg.ne hca hi
      · apply ht_not
        refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
        field_simp [hca]; linarith
    refine hfrom q i₀ hq_gen ?_
    have hposInd : posInd i₀ = 0 := if_neg (not_lt.mpr hneg.le)
    rw [hposInd]
    have hc1 : crossInd c q a b = -1 := by
      unfold crossInd
      have hda : det3 c a q = det3 c a b := by
        dsimp [q]; rw [det3_add3, det3_smul3, det3_self23, mul_zero, zero_add]
      have hdb : det3 c q b = t * det3 c a b := by
        dsimp [q]; rw [det3_swap23, det3_add3, det3_smul3, det3_self23, add_zero, det3_swap23]
        ring
      have hdb_neg : det3 c q b < 0 := by rw [hdb]; exact mul_neg_of_pos_of_neg ht_pos hneg
      rw [hda, ksgn_neg hneg, ksgn_neg hdb_neg]
      norm_num
    have hc2 : crossInd c (-q) a b = 0 := by
      unfold crossInd
      have hda : det3 c a (-q) = -det3 c a b := by
        dsimp [q]; rw [det3_neg3, det3_add3, det3_smul3, det3_self23, mul_zero, zero_add]
      rw [hda, ksgn_neg_arg, ksgn_neg hneg]
      norm_num
    rw [hc1, hc2]; norm_num

/-- **Main General Theorem (Sharp 3D Upper Bound for Bihan arXiv:2611.34336v1):**
Let a simplicial 3-polytope boundary have `V` vertices and `F = 2 * V - 4` oriented
triangular facets `f : Fin F → Fin V × Fin V × Fin V`, where each vertex `v` has a
nonempty cyclic link `link v : Fin (linkDeg v) → Fin V` partitioning the `3 * F`
oriented corners of all facets (`hregroup`). Let `C : Fin V → Fin 3 → K` satisfy `(UC)`
on every facet, and let `u : Fin 3 → K` be a generic ray with combinatorial degree
`d = deg(+u) = deg(-u)`. Then:
1. `4 * d = 2 * ∑ v, w_v - F₊ + F₋`,
2. `4 * |d| ≤ 3 * V - 8`, and hence `|d| ≤ (3 * V - 8) / 4`. -/
theorem bihan_3d_degree_bound {V F : ℕ} (hEuler : F = 2 * V - 4) (hV : 4 ≤ V)
    (f : Fin F → Fin V × Fin V × Fin V)
    (linkDeg : Fin V → ℕ) (hlinkPos : ∀ v, 0 < linkDeg v)
    (link : ∀ v, Fin (linkDeg v) → Fin V)
    (hregroup : ∀ (g : Fin V → Fin V → Fin V → ℤ),
      ∑ t : Fin F, (g (f t).1 (f t).2.1 (f t).2.2 + g (f t).2.1 (f t).2.2 (f t).1 +
        g (f t).2.2 (f t).1 (f t).2.1) =
      ∑ v : Fin V, ∑ i : Fin (linkDeg v),
        g v (link v i) (link v ⟨(i.val + 1) % linkDeg v, Nat.mod_lt _ (hlinkPos v)⟩))
    (C : Fin V → Fin 3 → K)
    (hUC_facets : ∀ t : Fin F, det3 (C (f t).1) (C (f t).2.1) (C (f t).2.2) ≠ 0)
    (hUC_links : ∀ v : Fin V, ∀ i : Fin (linkDeg v),
      det3 (C v) (C (link v i)) (C (link v ⟨(i.val + 1) % linkDeg v, Nat.mod_lt _ (hlinkPos v)⟩)) ≠ 0)
    (u : Fin 3 → K)
    (hu_gen : ∀ a b : Fin V, a ≠ b → det3 u (C a) (C b) ≠ 0)
    (hlink_ne : ∀ v : Fin V, ∀ i : Fin (linkDeg v), v ≠ link v i)
    (hfacet_ne : ∀ t : Fin F, (f t).1 ≠ (f t).2.1 ∧ (f t).2.1 ≠ (f t).2.2 ∧ (f t).2.2 ≠ (f t).1)
    (d : ℤ)
    (hd_pos : ∑ t : Fin F, ksgn (det3 (C (f t).1) (C (f t).2.1) (C (f t).2.2)) *
        inConeInd u (C (f t).1) (C (f t).2.1) (C (f t).2.2) = d)
    (hd_neg : ∑ t : Fin F, ksgn (det3 (C (f t).1) (C (f t).2.1) (C (f t).2.2)) *
        inConeInd (-u) (C (f t).1) (C (f t).2.1) (C (f t).2.2) = d) :
    4 * |d| ≤ 3 * (V : ℤ) - 8 := by
  -- Helper proving the one-sided bound `4 * d' ≤ 3 * V - 8` for any `(C', d')` satisfying the hypotheses.
  have hone_side : ∀ (C' : Fin V → Fin 3 → K) (d' : ℤ),
      (∀ t : Fin F, det3 (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) ≠ 0) →
      (∀ v : Fin V, ∀ i : Fin (linkDeg v),
        det3 (C' v) (C' (link v i)) (C' (link v ⟨(i.val + 1) % linkDeg v, Nat.mod_lt _ (hlinkPos v)⟩)) ≠ 0) →
      (∀ a b : Fin V, a ≠ b → det3 u (C' a) (C' b) ≠ 0) →
      (∑ t : Fin F, ksgn (det3 (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2)) *
        inConeInd u (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) = d') →
      (∑ t : Fin F, ksgn (det3 (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2)) *
        inConeInd (-u) (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) = d') →
      4 * d' ≤ 3 * (V : ℤ) - 8 := by
    intro C' d' hUCf hUCl hgen hd1 hd2
    let s : Fin F → ℤ := fun t => ksgn (det3 (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2))
    let Fp : ℤ := ∑ t : Fin F, if 0 < det3 (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) then (1 : ℤ) else 0
    let Fm : ℤ := ∑ t : Fin F, if det3 (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) < 0 then (1 : ℤ) else 0
    have hFsum : Fp + Fm = (F : ℤ) := by
      dsimp [Fp, Fm]; rw [← Finset.sum_add_distrib]
      calc ∑ t : Fin F, ((if 0 < det3 (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) then (1 : ℤ) else 0) +
              (if det3 (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) < 0 then (1 : ℤ) else 0))
          = ∑ _t : Fin F, (1 : ℤ) := by
              refine Finset.sum_congr rfl fun t _ => ?_
              rcases lt_or_gt_of_ne (hUCf t) with hlt | hgt
              · rw [if_neg (not_lt.mpr hlt.le), if_pos hlt]; norm_num
              · rw [if_pos hgt, if_neg (not_lt.mpr hgt.le)]; norm_num
        _ = (F : ℤ) := by simp
    have hFdiff : ∑ t : Fin F, s t = Fp - Fm := by
      dsimp [s, Fp, Fm]; rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rcases lt_or_gt_of_ne (hUCf t) with hlt | hgt
      · rw [ksgn_neg hlt, if_neg (not_lt.mpr hlt.le), if_pos hlt]; norm_num
      · rw [ksgn_pos hgt, if_pos hgt, if_neg (not_lt.mpr hgt.le)]; norm_num
    have hFm_nonneg : 0 ≤ Fm :=
      Finset.sum_nonneg fun t _ => by split_ifs <;> norm_num
    -- Step 1: Sum `single_facet_identity` over all `t : Fin F` and regroup corners via `hregroup`.
    have h4d : 4 * d' =
        ∑ v : Fin V, (linkWind (hlinkPos v) (C' v) u (fun i => C' (link v i)) +
          linkWind (hlinkPos v) (C' v) (-u) (fun i => C' (link v i))) - (Fp - Fm) := by
      have hlhs : 4 * d' = ∑ t : Fin F,
          2 * s t * (inConeInd u (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) +
            inConeInd (-u) (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2)) := by
        have : ∑ t : Fin F,
            2 * s t * (inConeInd u (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) +
              inConeInd (-u) (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2)) =
            2 * (∑ t : Fin F, s t * inConeInd u (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2)) +
            2 * (∑ t : Fin F, s t * inConeInd (-u) (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun t _ => by ring
        rw [this, hd1, hd2]; ring
      rw [hlhs]
      have hterm : ∑ t : Fin F,
          2 * s t * (inConeInd u (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) +
            inConeInd (-u) (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2)) =
          ∑ t : Fin F,
            ((crossInd (C' (f t).1) u (C' (f t).2.1) (C' (f t).2.2) +
              crossInd (C' (f t).1) (-u) (C' (f t).2.1) (C' (f t).2.2)) +
             (crossInd (C' (f t).2.1) u (C' (f t).2.2) (C' (f t).1) +
              crossInd (C' (f t).2.1) (-u) (C' (f t).2.2) (C' (f t).1)) +
             (crossInd (C' (f t).2.2) u (C' (f t).1) (C' (f t).2.1) +
              crossInd (C' (f t).2.2) (-u) (C' (f t).1) (C' (f t).2.1)) - s t) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        obtain ⟨h12, h23, h31⟩ := hfacet_ne t
        have hu1 : det3 u (C' (f t).2.1) (C' (f t).2.2) ≠ 0 := hgen _ _ h23
        have hu2 : det3 (C' (f t).1) u (C' (f t).2.2) ≠ 0 := by
          rw [det3_swap12]; exact neg_ne_zero.mpr (hgen _ _ h31.symm)
        have hu3 : det3 (C' (f t).1) (C' (f t).2.1) u ≠ 0 := by
          rw [det3_cyclic, det3_cyclic]; exact hgen _ _ h12
        exact single_facet_identity _ _ _ u (hUCf t) hu1 hu2 hu3
      rw [hterm, Finset.sum_sub_distrib, hFdiff]
      congr 1
      have hreg := hregroup (fun a b c => crossInd (C' a) u (C' b) (C' c) + crossInd (C' a) (-u) (C' b) (C' c))
      rw [hreg]
      refine Finset.sum_congr rfl fun v _ => ?_
      unfold linkWind; rw [← Finset.sum_add_distrib]
    -- Step 2: `linkWind (-u) = linkWind u`, and `2 * linkWind u ≤ p_v - 1` at every vertex `v`.
    have hgen_v : ∀ v : Fin V, ∀ i : Fin (linkDeg v), det3 (C' v) (C' (link v i)) u ≠ 0 := fun v i => by
      rw [det3_cyclic, det3_cyclic]; exact hgen _ _ (hlink_ne v i)
    have hgen_neg_v : ∀ v : Fin V, ∀ i : Fin (linkDeg v), det3 (C' v) (C' (link v i)) (-u) ≠ 0 := fun v i => by
      rw [det3_neg3]; exact neg_ne_zero.mpr (hgen_v v i)
    have hwind_le :
        ∑ v : Fin V, (linkWind (hlinkPos v) (C' v) u (fun i => C' (link v i)) +
          linkWind (hlinkPos v) (C' v) (-u) (fun i => C' (link v i))) ≤
        (∑ v : Fin V, ∑ i : Fin (linkDeg v),
          if 0 < det3 (C' v) (C' (link v i)) (C' (link v ⟨(i.val + 1) % linkDeg v, Nat.mod_lt _ (hlinkPos v)⟩))
          then (1 : ℤ) else 0) - (V : ℤ) := by
      have hsub :
          (∑ v : Fin V, ∑ i : Fin (linkDeg v),
            if 0 < det3 (C' v) (C' (link v i)) (C' (link v ⟨(i.val + 1) % linkDeg v, Nat.mod_lt _ (hlinkPos v)⟩))
            then (1 : ℤ) else 0) - (V : ℤ) =
          ∑ v : Fin V, ((∑ i : Fin (linkDeg v),
            if 0 < det3 (C' v) (C' (link v i)) (C' (link v ⟨(i.val + 1) % linkDeg v, Nat.mod_lt _ (hlinkPos v)⟩))
            then (1 : ℤ) else 0) - 1) := by
        rw [Finset.sum_sub_distrib]; simp
      rw [hsub]
      refine Finset.sum_le_sum fun v _ => ?_
      have heq_neg : linkWind (hlinkPos v) (C' v) (-u) (fun i => C' (link v i)) =
          linkWind (hlinkPos v) (C' v) u (fun i => C' (link v i)) :=
        linkWind_ray_independent (hlinkPos v) (C' v) u (-u) (fun i => C' (link v i))
          (hUCl v) (hgen_v v) (hgen_neg_v v)
      rw [heq_neg, ← two_mul]
      exact two_mul_linkWind_le_posCount_sub_one (hlinkPos v) (C' v) u (fun i => C' (link v i))
        (hUCl v) (hgen_v v)
    -- Step 3: `∑_v p_v = 3 * Fp` by `hregroup` and cyclic invariance of `det3`.
    have hsum_pv :
        (∑ v : Fin V, ∑ i : Fin (linkDeg v),
          if 0 < det3 (C' v) (C' (link v i)) (C' (link v ⟨(i.val + 1) % linkDeg v, Nat.mod_lt _ (hlinkPos v)⟩))
          then (1 : ℤ) else 0) = 3 * Fp := by
      rw [← hregroup (fun a b c => if 0 < det3 (C' a) (C' b) (C' c) then (1 : ℤ) else 0)]
      dsimp [Fp]; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hc1 : det3 (C' (f t).2.1) (C' (f t).2.2) (C' (f t).1) =
          det3 (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) := (det3_cyclic _ _ _).symm
      have hc2 : det3 (C' (f t).2.2) (C' (f t).1) (C' (f t).2.1) =
          det3 (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) := by rw [det3_cyclic, det3_cyclic]
      rw [hc1, hc2]; ring
    -- Step 4: Combine: `4 * d' ≤ (3 * Fp - V) - (Fp - Fm) = F + Fp - V ≤ 2 * F - V = 3 * V - 8`.
    have hF_int : (F : ℤ) = 2 * (V : ℤ) - 4 := by omega
    linarith
  -- Apply `hone_side` to `(C, d)` and to `(C_flip, -d)` where `C_flip` negates coordinate 0!
  have hpos_bound : 4 * d ≤ 3 * (V : ℤ) - 8 :=
    hone_side C d hUC_facets hUC_links hu_gen hd_pos hd_neg
  let flip : (Fin 3 → K) → (Fin 3 → K) := fun x j => if j = 0 then -x 0 else x j
  have hdet_flip : ∀ a b c : Fin 3 → K, det3 (flip a) (flip b) (flip c) = -det3 a b c := by
    intro a b c; dsimp [flip, det3]; ring
  let C' : Fin V → Fin 3 → K := fun v => flip (C v)
  have hUCf' : ∀ t : Fin F, det3 (C' (f t).1) (C' (f t).2.1) (C' (f t).2.2) ≠ 0 := fun t => by
    dsimp [C']; rw [hdet_flip]; exact neg_ne_zero.mpr (hUC_facets t)
  have hUCl' : ∀ v : Fin V, ∀ i : Fin (linkDeg v),
      det3 (C' v) (C' (link v i)) (C' (link v ⟨(i.val + 1) % linkDeg v, Nat.mod_lt _ (hlinkPos v)⟩)) ≠ 0 :=
    fun v i => by dsimp [C']; rw [hdet_flip]; exact neg_ne_zero.mpr (hUC_links v i)
  -- For the flipped map, use ray `u' = flip u` so `inConeInd (flip u) (flip a) (flip b) (flip c) = inConeInd u a b c`,
  -- while `ksgn (det3 (flip a) (flip b) (flip c)) = -ksgn (det3 a b c)`!
  -- Wait: `hone_side` used the same `u`, so pass `C'' = fun v => -C v`!
  -- EVEN SIMPLER: `det3 (-a) (-b) (-c) = -det3 a b c`, and `det3 u (-b) (-c) = det3 u b c`,
  -- so `inConeInd (-u) (-a) (-b) (-c) = inConeInd u a b c` and `inConeInd u (-a) (-b) (-c) = inConeInd (-u) a b c`!!
  let Cneg : Fin V → Fin 3 → K := fun v => -C v
  have hdet_neg3 : ∀ a b c : Fin 3 → K, det3 (-a) (-b) (-c) = -det3 a b c := by
    intro a b c; simp only [det3, Pi.neg_apply]; ring
  have hdet_neg23 : ∀ x b c : Fin 3 → K, det3 x (-b) (-c) = det3 x b c := by
    intro x b c; simp only [det3, Pi.neg_apply]; ring
  have hcone_neg : ∀ (w a b c : Fin 3 → K), inConeInd w (-a) (-b) (-c) = inConeInd (-w) a b c := by
    intro w a b c
    unfold inConeInd
    have e0 : det3 (-a) (-b) (-c) = -det3 a b c := hdet_neg3 a b c
    have e1 : det3 w (-b) (-c) = -det3 (-w) b c := by simp only [det3, Pi.neg_apply]; ring
    have e2 : det3 (-a) w (-c) = -det3 a (-w) c := by simp only [det3, Pi.neg_apply]; ring
    have e3 : det3 (-a) (-b) w = -det3 a b (-w) := by simp only [det3, Pi.neg_apply]; ring
    rw [e0, e1, e2, e3]
    simp only [ksgn_neg_arg, neg_ne_zero, neg_inj]
  have hneg_bound : 4 * (-d) ≤ 3 * (V : ℤ) - 8 := by
    refine hone_side Cneg (-d)
      (fun t => by dsimp [Cneg]; rw [hdet_neg3]; exact neg_ne_zero.mpr (hUC_facets t))
      (fun v i => by dsimp [Cneg]; rw [hdet_neg3]; exact neg_ne_zero.mpr (hUC_links v i))
      (fun a b hab => by dsimp [Cneg]; rw [hdet_neg23]; exact hu_gen a b hab) ?_ ?_
    · dsimp [Cneg]
      calc ∑ t : Fin F, ksgn (det3 (-C (f t).1) (-C (f t).2.1) (-C (f t).2.2)) *
              inConeInd u (-C (f t).1) (-C (f t).2.1) (-C (f t).2.2)
          = -(∑ t : Fin F, ksgn (det3 (C (f t).1) (C (f t).2.1) (C (f t).2.2)) *
              inConeInd (-u) (C (f t).1) (C (f t).2.1) (C (f t).2.2)) := by
              rw [← Finset.sum_neg_distrib]
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [hdet_neg3, ksgn_neg_arg, hcone_neg]; ring
        _ = -d := by rw [hd_neg]
    · dsimp [Cneg]
      calc ∑ t : Fin F, ksgn (det3 (-C (f t).1) (-C (f t).2.1) (-C (f t).2.2)) *
              inConeInd (-u) (-C (f t).1) (-C (f t).2.1) (-C (f t).2.2)
          = -(∑ t : Fin F, ksgn (det3 (C (f t).1) (C (f t).2.1) (C (f t).2.2)) *
              inConeInd u (C (f t).1) (C (f t).2.1) (C (f t).2.2)) := by
              rw [← Finset.sum_neg_distrib]
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [hdet_neg3, ksgn_neg_arg, hcone_neg, neg_neg]; ring
        _ = -d := by rw [hd_pos]
  rcases le_or_gt 0 d with hd0 | hd0
  · rw [abs_of_nonneg hd0]; exact hpos_bound
  · rw [abs_of_neg hd0]; exact hneg_bound

/-- **Corollary (`n = k = 3` / `V ≤ 7`):**
No 3D fewnomial map with `V ≤ 7` Newton polytope vertices can achieve `|deg F| = 4`;
in fact `|deg F| ≤ 3`. -/
theorem bihan_n3_k3_upper_bound {V : ℕ} (hV7 : V ≤ 7) (d : ℤ)
    (hbound : 4 * |d| ≤ 3 * (V : ℤ) - 8) : |d| ≤ 3 := by
  omega

/-- **Corollary (Strict improvement over Bihan's Theorem 2 for all `N ≥ 7`):**
Bihan's Theorem 2 gives `|deg F| ≤ N - 3`, whereas our bound gives `|deg F| ≤ (3 * N - 8) / 4`,
which is strictly smaller for every `N ≥ 7`. -/
theorem strictly_beats_theorem_2 {N : ℕ} (hN : 7 ≤ N) :
    (3 * N - 8) / 4 < N - 3 := by
  omega

end AlgebraicBound

/-! ### Section 2: Exact Integer Realizations (`D(3, 3) = {0, 1, 2, 3}` and Extremal `V = 8, 9, 10, 12`) -/

section Realizations

/-- 3D integer vector. -/
abbrev Vec3 := ℤ × ℤ × ℤ

/-- Integer `3 × 3` determinant. -/
def det3Z (a b c : Vec3) : ℤ :=
  a.1 * (b.2.1 * c.2.2 - b.2.2 * c.2.1)
  - a.2.1 * (b.1 * c.2.2 - b.2.2 * c.1)
  + a.2.2 * (b.1 * c.2.1 - b.2.1 * c.1)

/-- Integer `4 × 4` lifted determinant `det[(1,p),(1,q),(1,r),(1,s)]`. -/
def liftedDetZ (p q r s : Vec3) : ℤ :=
  det3Z (q.1 - p.1, q.2.1 - p.2.1, q.2.2 - p.2.2)
        (r.1 - p.1, r.2.1 - p.2.1, r.2.2 - p.2.2)
        (s.1 - p.1, s.2.1 - p.2.1, s.2.2 - p.2.2)

/-- Integer sign in `{-1, 0, 1}`. -/
def zsgn (x : ℤ) : ℤ :=
  if 0 < x then 1 else if x < 0 then -1 else 0

/-- Exact check of Bihan's uniform general-position condition `(UA)` for `A : List Vec3`. -/
def checkUA (A : List Vec3) : Bool :=
  let n := A.length
  (List.range n).all fun i =>
    let ai := A.getD i (0, 0, 0)
    (List.range n).all fun j =>
      if i < j then
        let aj := A.getD j (0, 0, 0)
        (List.range n).all fun k =>
          if j < k then
            let ak := A.getD k (0, 0, 0)
            (List.range n).all fun l =>
              if k < l then
                liftedDetZ ai aj ak (A.getD l (0, 0, 0)) != 0
              else true
          else true
      else true

/-- Exact check of Bihan's uniform general-position condition `(UC)` for `C : List Vec3`. -/
def checkUC (C : List Vec3) : Bool :=
  let n := C.length
  (List.range n).all fun i =>
    let ci := C.getD i (0, 0, 0)
    (List.range n).all fun j =>
      if i < j then
        let cj := C.getD j (0, 0, 0)
        (List.range n).all fun k =>
          if j < k then
            det3Z ci cj (C.getD k (0, 0, 0)) != 0
          else true
      else true

/-- Check whether `u` is generic with respect to `C` (not coplanar with any pair `C[i], C[j]`). -/
def isGenericRay (C : List Vec3) (u : Vec3) : Bool :=
  let n := C.length
  (List.range n).all fun i =>
    let ci := C.getD i (0, 0, 0)
    (List.range n).all fun j =>
      if i < j then det3Z u ci (C.getD j (0, 0, 0)) != 0 else true

/-- Cone membership check `u ∈ open cone(a, b, c)` in exact integer arithmetic. -/
def inConeZ (u a b c : Vec3) : Bool :=
  let s := zsgn (det3Z a b c)
  s != 0 && zsgn (det3Z u b c) == s && zsgn (det3Z a u c) == s && zsgn (det3Z a b u) == s

/-- Outward-oriented facets of `conv(A)` together with the lifted-det sign `s0` of off-facet points. -/
def facetsWithSignZ (A : List Vec3) : List (ℕ × ℕ × ℕ × ℤ) :=
  let n := A.length
  let idxs := List.range n
  idxs.foldl (fun acc i =>
    let ai := A.getD i (0, 0, 0)
    idxs.foldl (fun acc j =>
      if i < j then
        let aj := A.getD j (0, 0, 0)
        idxs.foldl (fun acc k =>
          if j < k then
            let ak := A.getD k (0, 0, 0)
            let others := idxs.filter (fun m => m != i && m != j && m != k)
            match others with
            | [] => acc
            | m0 :: rest =>
              let s0 := zsgn (liftedDetZ ai aj ak (A.getD m0 (0, 0, 0)))
              let isFacet := s0 != 0 &&
                rest.all (fun m => zsgn (liftedDetZ ai aj ak (A.getD m (0, 0, 0))) == s0)
              if isFacet then (i, j, k, s0) :: acc else acc
          else acc) acc
      else acc) acc) []

/-- Exact Bihan Theorem 1.3 degree formula evaluated from precomputed facets at a generic ray `u`. -/
def degreeFromFacetsZ (facets : List (ℕ × ℕ × ℕ × ℤ)) (C : List Vec3) (u : Vec3) : ℤ :=
  let tot : ℤ := facets.foldl (fun acc f =>
    let (i, j, k, s0) := f
    let ci := C.getD i (0, 0, 0)
    let cj := C.getD j (0, 0, 0)
    let ck := C.getD k (0, 0, 0)
    if inConeZ u ci cj ck then
      acc + zsgn (det3Z ci cj ck) * s0
    else acc) 0
  0 - tot

/-- Exact Bihan Theorem 1.3 degree formula for `n = 3` at a generic ray `u`. -/
def degreeBihanZ (A C : List Vec3) (u : Vec3) : ℤ :=
  degreeFromFacetsZ (facetsWithSignZ A) C u

/-- Test rays for verifying ray-independence of `degreeBihanZ`. -/
def testRays : List Vec3 :=
  [(7, -3, 11), (-5, 13, 2), (1, 1, -17), (-7, 3, -11)]

/-- Full witness verifier: `(UA)`, `(UC)`, all test rays generic, and `degreeBihanZ = target` on all rays. -/
def verifyWitness (A C : List Vec3) (target : ℤ) : Bool :=
  let facets := facetsWithSignZ A
  A.length == C.length &&
  checkUA A &&
  checkUC C &&
  testRays.all (fun u => isGenericRay C u && degreeFromFacetsZ facets C u == target)

/-! #### Explicit `N = 7` (`n = k = 3`) witnesses realizing `|deg F| = 0, 1, 2, 3` -/

def A7_0 : List Vec3 :=
  [(1, -1, 4), (1, -3, 2), (8, 6, -4), (-8, -4, 0), (-14, -1, -7), (-4, -3, -2), (2, 6, -1)]
def C7_0 : List Vec3 :=
  [(26, -13, 7), (23, 2, -19), (-26, -13, 6), (-29, -6, -5), (24, 9, 16), (-15, -2, 26), (18, -15, 18)]

def A7_1 : List Vec3 :=
  [(-2, 8, 6), (-16, -11, -1), (-3, 1, 1), (13, -7, -2), (12, 4, 4), (-3, -10, 1), (1, -7, -4)]
def C7_1 : List Vec3 :=
  [(-2, -30, -3), (6, 2, -29), (-13, 21, 17), (-20, 18, -12), (16, -19, 17), (-25, -3, 17), (2, 8, -29)]

def A7_2 : List Vec3 :=
  [(-2, -8, 0), (-7, -4, 4), (4, -3, 0), (3, 0, 7), (8, -1, -7), (-1, 8, 7), (7, 7, -3)]
def C7_2 : List Vec3 :=
  [(-12, 9, -26), (5, 21, 21), (19, -5, 23), (-8, -26, 11), (-19, 21, -10), (26, -1, -14), (-30, 1, 2)]

def A7_3 : List Vec3 :=
  [(3, 1, 3), (11, 4, -1), (-4, 2, 6), (-5, 3, -5), (-10, -3, 9), (0, -7, 2), (3, 2, -7)]
def C7_3 : List Vec3 :=
  [(-13, 15, -22), (10, -25, 14), (-20, 0, 23), (11, 17, -22), (-8, -26, 13), (9, 28, 5), (-24, -15, 10)]

theorem n7_realizes_0 : A7_0.length = 7 ∧ verifyWitness A7_0 C7_0 0 = true := by decide
theorem n7_realizes_1 : A7_1.length = 7 ∧ (verifyWitness A7_1 C7_1 1 = true ∨ verifyWitness A7_1 C7_1 (-1) = true) := by decide
theorem n7_realizes_2 : A7_2.length = 7 ∧ (verifyWitness A7_2 C7_2 2 = true ∨ verifyWitness A7_2 C7_2 (-2) = true) := by decide
theorem n7_realizes_3 : A7_3.length = 7 ∧ (verifyWitness A7_3 C7_3 3 = true ∨ verifyWitness A7_3 C7_3 (-3) = true) := by decide

/-! #### Extremal realizations attaining `⌊(3V - 8)/4⌋` for `V = 8, 9, 10, 12` -/

def A8 : List Vec3 :=
  [(-3, 2, 3), (11, -5, -5), (-2, 6, 2), (-10, 4, -4), (2, -2, 4), (4, -3, -9), (6, -1, -7), (-1, 5, -3)]
def C8 : List Vec3 :=
  [(23, 8, 17), (16, -25, -2), (-15, 26, 6), (-4, -30, -2), (-15, -12, -23), (7, 28, 8), (-16, -25, 5), (19, 13, -19)]

def A9 : List Vec3 :=
  [(8, 2, 5), (-1, 1, 13), (-13, 0, -9), (-8, -8, -2), (-3, 2, 7), (0, -10, 0), (1, 3, -5), (0, -2, -8), (2, -9, 4)]
def C9 : List Vec3 :=
  [(-4, 24, 18), (-4, -29, -8), (-5, -18, 24), (-5, 30, 0), (12, 24, -12), (-27, -12, 5), (-21, -14, -16), (28, -2, -11), (19, -19, 14)]

def A10 : List Vec3 :=
  [(2, -7, -4), (4, -6, -3), (-1, 4, 1), (9, 14, -6), (5, -11, 4), (3, 9, -2), (9, -6, 11), (7, -1, -3), (1, 0, 6), (5, 13, 13)]
def C10 : List Vec3 :=
  [(24, 17, 1), (11, 7, -27), (1, 27, -14), (-29, 8, -2), (-21, 22, 1), (24, -18, -2), (21, 0, -22), (-7, -16, 24), (-10, -28, 3), (2, -2, 30)]

/-- Perturbed regular icosahedron mapped to its Galois conjugate (great icosahedron `{3, 5/2}`, density `7`). -/
def A12 : List Vec3 :=
  [(-1, 1002, 1625), (991, 1623, -2), (1610, -4, 994), (2, 1006, -1620),
    (1003, -1610, -6), (-1609, -2, 991), (-3, -996, 1617), (-1004, 1621, -4),
    (1611, -5, -995), (-5, -1005, -1627), (-1009, -1621, -3), (-1622, -4, -1000)]
def C12 : List Vec3 :=
  [(1, 997, -610), (997, -622, -3), (-615, 0, 991), (2, 1004, 614),
    (995, 617, -7), (619, 0, 1009), (-9, -999, -625), (-1000, -616, 0),
    (-612, 1, -1004), (6, -994, 614), (-1008, 617, -9), (620, 3, -1009)]

/-- Outer-index slice of `checkUA` for keeping kernel `decide` recursion depth low. -/
def checkUASlice (A : List Vec3) (lo hi : ℕ) : Bool :=
  let n := A.length
  (List.range (hi - lo)).all fun d =>
    let i := lo + d
    let ai := A.getD i (0, 0, 0)
    (List.range n).all fun j =>
      if i < j then
        let aj := A.getD j (0, 0, 0)
        (List.range n).all fun k =>
          if j < k then
            let ak := A.getD k (0, 0, 0)
            (List.range n).all fun l =>
              if k < l then
                liftedDetZ ai aj ak (A.getD l (0, 0, 0)) != 0
              else true
          else true
      else true

/-- Outer-index slice of `facetsWithSignZ` for keeping kernel `decide` recursion depth low. -/
def facetsSliceZ (A : List Vec3) (lo hi : ℕ) : List (ℕ × ℕ × ℕ × ℤ) :=
  let n := A.length
  let idxs := List.range n
  (List.range (hi - lo)).foldl (fun acc d =>
    let i := lo + d
    let ai := A.getD i (0, 0, 0)
    idxs.foldl (fun acc j =>
      if i < j then
        let aj := A.getD j (0, 0, 0)
        idxs.foldl (fun acc k =>
          if j < k then
            let ak := A.getD k (0, 0, 0)
            let others := idxs.filter (fun m => m != i && m != j && m != k)
            match others with
            | [] => acc
            | m0 :: rest =>
              let s0 := zsgn (liftedDetZ ai aj ak (A.getD m0 (0, 0, 0)))
              let isFacet := s0 != 0 &&
                rest.all (fun m => zsgn (liftedDetZ ai aj ak (A.getD m (0, 0, 0))) == s0)
              if isFacet then (i, j, k, s0) :: acc else acc
          else acc) acc
      else acc) acc) []

/-- Verify a witness using precomputed facet list + sliced `(UA)` check (same semantics as `verifyWitness`). -/
def verifyRaysOnFacets (facets : List (ℕ × ℕ × ℕ × ℤ)) (C : List Vec3) (target : ℤ) : Bool :=
  testRays.all (fun u => isGenericRay C u && degreeFromFacetsZ facets C u == target)

theorem extremal_V8 : A8.length = 8 ∧ (verifyWitness A8 C8 4 = true ∨ verifyWitness A8 C8 (-4) = true) := by decide

private lemma A9_UA_0 : checkUASlice A9 0 3 = true := by decide
private lemma A9_UA_1 : checkUASlice A9 3 9 = true := by decide
private lemma A9_UC : checkUC C9 = true := by decide
private def facetsA9_0_lit : List (ℕ × ℕ × ℕ × ℤ) :=
  [(2, 6, 7, -1), (2, 4, 6, -1), (2, 3, 7, 1), (1, 3, 8, -1), (1, 2, 4, 1), (1, 2, 3, -1),
   (0, 6, 7, 1), (0, 5, 8, 1), (0, 5, 7, -1), (0, 4, 6, 1), (0, 1, 8, -1), (0, 1, 4, 1)]
private def facetsA9_1_lit : List (ℕ × ℕ × ℕ × ℤ) :=
  [(3, 5, 8, -1), (3, 5, 7, 1)]
private lemma A9_facets_0 : facetsSliceZ A9 0 3 = facetsA9_0_lit := by decide
private lemma A9_facets_1 : facetsSliceZ A9 3 9 = facetsA9_1_lit := by decide
private def facetsA9 : List (ℕ × ℕ × ℕ × ℤ) :=
  facetsA9_0_lit ++ facetsA9_1_lit
private lemma A9_facets_len : facetsA9.length = 14 := by decide
private lemma A9_deg :
    verifyRaysOnFacets facetsA9 C9 4 = true ∨ verifyRaysOnFacets facetsA9 C9 (-4) = true := by decide

theorem extremal_V9 :
    A9.length = 9 ∧ C9.length = 9 ∧
    checkUASlice A9 0 3 = true ∧ checkUASlice A9 3 9 = true ∧
    checkUC C9 = true ∧
    facetsSliceZ A9 0 3 = facetsA9_0_lit ∧ facetsSliceZ A9 3 9 = facetsA9_1_lit ∧
    facetsA9.length = 14 ∧
    (verifyRaysOnFacets facetsA9 C9 4 = true ∨ verifyRaysOnFacets facetsA9 C9 (-4) = true) :=
  ⟨rfl, rfl, A9_UA_0, A9_UA_1, A9_UC, A9_facets_0, A9_facets_1, A9_facets_len, A9_deg⟩

private lemma A10_UA_0 : checkUASlice A10 0 2 = true := by decide
private lemma A10_UA_1 : checkUASlice A10 2 5 = true := by decide
private lemma A10_UA_2 : checkUASlice A10 5 10 = true := by decide
private lemma A10_UC : checkUC C10 = true := by decide
private def facetsA10 : List (ℕ × ℕ × ℕ × ℤ) :=
  facetsSliceZ A10 0 2 ++ facetsSliceZ A10 2 5 ++ facetsSliceZ A10 5 10
private lemma A10_facets_len : facetsA10.length = 16 := by decide
private lemma A10_deg :
    verifyRaysOnFacets facetsA10 C10 5 = true ∨ verifyRaysOnFacets facetsA10 C10 (-5) = true := by decide

theorem extremal_V10 :
    A10.length = 10 ∧ C10.length = 10 ∧
    checkUASlice A10 0 2 = true ∧ checkUASlice A10 2 5 = true ∧ checkUASlice A10 5 10 = true ∧
    checkUC C10 = true ∧ facetsA10.length = 16 ∧
    (verifyRaysOnFacets facetsA10 C10 5 = true ∨ verifyRaysOnFacets facetsA10 C10 (-5) = true) :=
  ⟨rfl, rfl, A10_UA_0, A10_UA_1, A10_UA_2, A10_UC, A10_facets_len, A10_deg⟩

private lemma A12_UA_0 : checkUASlice A12 0 1 = true := by decide
private lemma A12_UA_1 : checkUASlice A12 1 2 = true := by decide
private lemma A12_UA_2 : checkUASlice A12 2 4 = true := by decide
private lemma A12_UA_3 : checkUASlice A12 4 7 = true := by decide
private lemma A12_UA_4 : checkUASlice A12 7 12 = true := by decide
private lemma A12_UC : checkUC C12 = true := by decide
private def facetsA12_0_lit : List (ℕ × ℕ × ℕ × ℤ) :=
  [(0, 5, 7, 1), (0, 5, 6, -1), (0, 2, 6, 1), (0, 1, 7, -1), (0, 1, 2, 1)]
private def facetsA12_1_lit : List (ℕ × ℕ × ℕ × ℤ) :=
  [(2, 4, 8, -1), (2, 4, 6, 1), (1, 3, 8, 1), (1, 3, 7, -1), (1, 2, 8, -1)]
private def facetsA12_2_lit : List (ℕ × ℕ × ℕ × ℤ) :=
  [(5, 10, 11, 1), (5, 7, 11, -1), (5, 6, 10, 1), (4, 9, 10, 1), (4, 8, 9, 1),
   (4, 6, 10, -1), (3, 9, 11, -1), (3, 8, 9, -1), (3, 7, 11, 1)]
private def facetsA12_3_lit : List (ℕ × ℕ × ℕ × ℤ) :=
  [(9, 10, 11, -1)]
private lemma A12_f0_eq : facetsSliceZ A12 0 1 = facetsA12_0_lit := by decide
private lemma A12_f1_eq : facetsSliceZ A12 1 3 = facetsA12_1_lit := by decide
private lemma A12_f2_eq : facetsSliceZ A12 3 6 = facetsA12_2_lit := by decide
private lemma A12_f3_eq : facetsSliceZ A12 6 12 = facetsA12_3_lit := by decide
private def facetsA12_all : List (ℕ × ℕ × ℕ × ℤ) :=
  facetsA12_0_lit ++ facetsA12_1_lit ++ facetsA12_2_lit ++ facetsA12_3_lit
private lemma A12_facets_len : facetsA12_all.length = 20 := by decide
private lemma A12_deg :
    verifyRaysOnFacets facetsA12_all C12 7 = true ∨
    verifyRaysOnFacets facetsA12_all C12 (-7) = true := by decide

theorem extremal_V12 :
    A12.length = 12 ∧ C12.length = 12 ∧
    checkUASlice A12 0 1 = true ∧ checkUASlice A12 1 2 = true ∧ checkUASlice A12 2 4 = true ∧
    checkUASlice A12 4 7 = true ∧ checkUASlice A12 7 12 = true ∧
    checkUC C12 = true ∧
    facetsSliceZ A12 0 1 ++ facetsSliceZ A12 1 3 ++ facetsSliceZ A12 3 6 ++ facetsSliceZ A12 6 12 = facetsA12_all ∧
    facetsA12_all.length = 20 ∧
    (verifyRaysOnFacets facetsA12_all C12 7 = true ∨
     verifyRaysOnFacets facetsA12_all C12 (-7) = true) := by
  refine ⟨rfl, rfl, A12_UA_0, A12_UA_1, A12_UA_2, A12_UA_3, A12_UA_4, A12_UC, ?_, A12_facets_len, A12_deg⟩
  rw [A12_f0_eq, A12_f1_eq, A12_f2_eq, A12_f3_eq]; rfl

end Realizations

end BihanFewnomialDegree
