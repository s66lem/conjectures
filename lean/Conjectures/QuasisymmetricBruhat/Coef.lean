import Conjectures.QuasisymmetricBruhat.Basis

/-!
# Computable forest coefficients of `Rᵢ P_F` and `L_k P_F`

Peeling the last (terminal) position `j` of `G` with `ecoeff_extract` gives recursions for the
coefficient of `P_G` in `Rᵢ P_F` and in `(x₁ + ⋯ + x_k) P_F`; the case analysis follows NST's
commutation relations (7.1) and the twisted Leibniz rule.  The recursions only manipulate codes,
so they can be evaluated by `decide`.

`lowR`/`lowL` list all `F` with a nonzero coefficient for fixed `G` (lower covers), and
`upR`/`upL` all `G` for fixed `F` (upper covers).
-/

namespace QuasisymmetricBruhat

open MvPolynomial Finset Forest

/-- Coefficient of `P_G` in `Rᵢ P_F` (fuel `n = |G|`). -/
def coefRAux : ℕ → Forest → ℕ → Forest → ℤ
  | 0, _, _, F => if F = empty then 1 else 0
  | n + 1, G, i, F =>
    if G.len + 1 < i then
      (if F.term G.len then coefRAux n (rem G.len G) (i - 1) (rem G.len F) else 0)
    else if i ≤ G.len then
      (if F.term (G.len + 1) then coefRAux n (rem G.len G) i (rem (G.len + 1) F) else 0)
    else
      (if F.term (i - 1) then coefRAux n (rem G.len G) i (rem (i - 1) F) else 0) +
        (if F.term i then coefRAux n (rem G.len G) (i - 1) (rem i F) else 0)

/-- Coefficient of `P_G` in `L_k P_F` (fuel `n = |G|`). -/
def coefLAux : ℕ → Forest → ℕ → Forest → ℤ
  | 0, _, _, _ => 0
  | n + 1, G, k, F =>
    if G.len ≠ k then
      (if F.term G.len then
        coefLAux n (rem G.len G) (if G.len < k then k - 1 else k) (rem G.len F) else 0)
    else
      (if F.term k then coefLAux n (rem G.len G) k (rem k F) else 0) +
        coefRAux n (rem G.len G) k F

/-- Coefficient of `P_G` in `Rᵢ P_F`. -/
def coefR (G : Forest) (i : ℕ) (F : Forest) : ℤ := coefRAux G.size G i F

/-- Coefficient of `P_G` in `L_k P_F`. -/
def coefL (G : Forest) (k : ℕ) (F : Forest) : ℤ := coefLAux G.size G k F

lemma ite_mem_supported {b : Prop} [Decidable b] {f : Pol} (hf : f ∈ supported ℤ posVars) :
    (if b then f else 0) ∈ supported ℤ posVars := by
  split_ifs
  · exact hf
  · exact Subalgebra.zero_mem _

lemma ecoeff_ite {b : Prop} [Decidable b] (f : Pol) (G : Forest) :
    ecoeff (if b then f else 0) G = if b then ecoeff f G else 0 := by
  split_ifs
  · rfl
  · rw [ecoeff_zero]; rfl

lemma RP_mem {i : ℕ} (hi : 1 ≤ i) (F : Forest) : R i (forestPoly F) ∈ supported ℤ posVars :=
  R_mem_supported hi (forestPoly_mem_supported F)

lemma LP_mem (k : ℕ) (F : Forest) : L k * forestPoly F ∈ supported ℤ posVars :=
  Subalgebra.mul_mem _ (L_mem_supported k) (forestPoly_mem_supported F)

lemma R_x_of_lt {i j : ℕ} (h : j < i) : R i (x j) = x j := by simp [x, R_X, h]

lemma R_x_of_gt {i j : ℕ} (h : i < j) : R i (x j) = x (j - 1) := by
  simp [x, R_X, show ¬ j < i by omega, show j ≠ i by omega]

theorem coefR_correct : ∀ n (G : Forest), G.size = n → ∀ i (F : Forest), 1 ≤ i →
    ecoeff (R i (forestPoly F)) G = coefRAux n G i F := by
  intro n
  induction n with
  | zero =>
    intro G hG i F hi
    rw [(eq_empty_iff_size G).2 hG, ecoeff_empty (RP_mem hi F), R_constantCoeff,
      constantCoeff_forestPoly, coefRAux]
  | succ n ih =>
    intro G hG i F hi
    have hne : G ≠ empty := fun h => by rw [h] at hG; simp [empty, size] at hG
    have hterm := term_len hne
    set j := G.len with hjdef
    have hj : 1 ≤ j := hterm.1
    have hsize : (rem j G).size = n := by have := size_rem hterm; omega
    simp only [coefRAux, ← hjdef]
    by_cases h1 : j + 1 < i
    · rw [if_pos h1]
      have hD : D j (R i (forestPoly F)) =
          x j * (if F.term j then R (i - 1) (forestPoly (rem j F)) else 0) := by
        rw [D_R_low h1, D_forestPoly hj]
        split_ifs
        · rw [map_mul, R_x_of_lt (by omega)]
        · simp
      rw [ecoeff_extract (RP_mem hi F) hj hD hterm, ecoeff_ite]
      split_ifs
      · exact ih _ hsize _ _ (by omega)
      · rfl
    · rw [if_neg h1]
      by_cases h2 : i ≤ j
      · rw [if_pos h2]
        have hD : D j (R i (forestPoly F)) =
            x j * (if F.term (j + 1) then R i (forestPoly (rem (j + 1) F)) else 0) := by
          rw [D_R_high h2, D_forestPoly (by omega)]
          split_ifs
          · rw [map_mul, R_x_of_gt (by omega), Nat.add_sub_cancel]
          · simp
        rw [ecoeff_extract (RP_mem hi F) hj hD hterm, ecoeff_ite]
        split_ifs
        · exact ih _ hsize _ _ hi
        · rfl
      · rw [if_neg h2]
        obtain rfl : i = j + 1 := by omega
        have hD : D j (R (j + 1) (forestPoly F)) =
            x j * ((if F.term j then R (j + 1) (forestPoly (rem j F)) else 0) +
              (if F.term (j + 1) then R j (forestPoly (rem (j + 1) F)) else 0)) := by
          have := D_R_mid (i := j + 1) (by omega) (forestPoly F)
          simp only [Nat.add_sub_cancel] at this
          rw [this, D_forestPoly hj, D_forestPoly (by omega), mul_add]
          congr 1
          · split_ifs
            · rw [map_mul, R_x_of_lt (by omega)]
            · simp
          · split_ifs
            · rw [map_mul, R_x_of_gt (by omega), Nat.add_sub_cancel]
            · simp
        rw [ecoeff_extract (RP_mem hi F) hj hD hterm,
          ecoeff_add (ite_mem_supported (RP_mem hi _)) (ite_mem_supported (RP_mem hj _)),
          Finsupp.add_apply, ecoeff_ite, ecoeff_ite, Nat.add_sub_cancel]
        congr 1
        · split_ifs
          · exact ih _ hsize _ _ hi
          · rfl
        · split_ifs
          · exact ih _ hsize _ _ hj
          · rfl

theorem coefL_correct : ∀ n (G : Forest), G.size = n → ∀ k (F : Forest), 1 ≤ k →
    ecoeff (L k * forestPoly F) G = coefLAux n G k F := by
  intro n
  induction n with
  | zero =>
    intro G hG k F hk
    rw [(eq_empty_iff_size G).2 hG, ecoeff_empty (LP_mem k F), map_mul, L_constantCoeff,
      zero_mul, coefLAux]
  | succ n ih =>
    intro G hG k F hk
    have hne : G ≠ empty := fun h => by rw [h] at hG; simp [empty, size] at hG
    have hterm := term_len hne
    set j := G.len with hjdef
    have hj : 1 ≤ j := hterm.1
    have hsize : (rem j G).size = n := by have := size_rem hterm; omega
    simp only [coefLAux, ← hjdef]
    rw [mul_comm]
    by_cases h1 : j ≠ k
    · rw [if_pos h1]
      have hD : D j (forestPoly F * L k) =
          x j * (if F.term j then L (if j < k then k - 1 else k) * forestPoly (rem j F)
            else 0) := by
        have hif : (if j + 1 ≤ k then k - 1 else k) = (if j < k then k - 1 else k) := by
          split_ifs <;> first | rfl | omega
        rw [D_mul, D_L hj, if_neg h1, mul_zero, add_zero, R_L (by omega), D_forestPoly hj, hif]
        by_cases h3 : F.term j
        · rw [if_pos h3, if_pos h3]; ring
        · rw [if_neg h3, if_neg h3, zero_mul, mul_zero]
      rw [ecoeff_extract (by rw [mul_comm]; exact LP_mem k F) hj hD hterm, ecoeff_ite]
      by_cases h3 : F.term j
      · rw [if_pos h3, if_pos h3]
        exact ih _ hsize _ _ (by split_ifs <;> omega)
      · rw [if_neg h3, if_neg h3]
    · rw [if_neg h1]
      obtain rfl : j = k := by omega
      have hD : D j (forestPoly F * L j) =
          x j * ((if F.term j then L j * forestPoly (rem j F) else 0) + R j (forestPoly F)) := by
        rw [D_mul, D_L hj, if_pos rfl, R_L (by omega), if_neg (show ¬ j + 1 ≤ j by omega),
          D_forestPoly hj]
        by_cases h3 : F.term j
        · rw [if_pos h3, if_pos h3]; ring
        · rw [if_neg h3, if_neg h3]; ring
      rw [ecoeff_extract (by rw [mul_comm]; exact LP_mem j F) hj hD hterm,
        ecoeff_add (ite_mem_supported (LP_mem _ _)) (RP_mem hj F), Finsupp.add_apply, ecoeff_ite,
        coefR_correct n _ hsize _ _ hj]
      congr 1
      split_ifs
      · exact ih _ hsize _ _ hj
      · rfl

lemma coefR_eq {G : Forest} {i : ℕ} (hi : 1 ≤ i) (F : Forest) :
    ecoeff (R i (forestPoly F)) G = coefR G i F := coefR_correct _ G rfl i F hi

lemma coefL_eq {G : Forest} {k : ℕ} (hk : 1 ≤ k) (F : Forest) :
    ecoeff (L k * forestPoly F) G = coefL G k F := coefL_correct _ G rfl k F hk

/-! ### Sizes and the range of `k` -/

lemma coefRAux_size : ∀ n (G : Forest), G.size = n → ∀ i (F : Forest), coefRAux n G i F ≠ 0 →
    G.size = F.size := by
  intro n
  induction n with
  | zero =>
    intro G hG i F h
    simp only [coefRAux] at h
    split_ifs at h with hF
    · rw [hG, hF]; rfl
    · exact absurd rfl h
  | succ n ih =>
    intro G hG i F h
    have hne : G ≠ empty := fun h => by rw [h] at hG; simp [empty, size] at hG
    have hterm := term_len hne
    have hsize : (rem G.len G).size = n := by have := size_rem hterm; omega
    simp only [coefRAux] at h
    have key : ∀ t i', F.term t → coefRAux n (rem G.len G) i' (rem t F) ≠ 0 →
        G.size = F.size := by
      intro t i' ht hc
      have := ih _ hsize _ _ hc
      have := size_rem ht; omega
    by_cases h1 : G.len + 1 < i
    · rw [if_pos h1] at h
      by_cases ht : F.term G.len
      · rw [if_pos ht] at h; exact key _ _ ht h
      · rw [if_neg ht] at h; exact absurd rfl h
    · rw [if_neg h1] at h
      by_cases h2 : i ≤ G.len
      · rw [if_pos h2] at h
        by_cases ht : F.term (G.len + 1)
        · rw [if_pos ht] at h; exact key _ _ ht h
        · rw [if_neg ht] at h; exact absurd rfl h
      · rw [if_neg h2] at h
        by_cases ht1 : F.term (i - 1)
        · by_cases hc : coefRAux n (rem G.len G) i (rem (i - 1) F) = 0
          · rw [if_pos ht1, hc, zero_add] at h
            by_cases ht2 : F.term i
            · rw [if_pos ht2] at h; exact key _ _ ht2 h
            · rw [if_neg ht2] at h; exact absurd rfl h
          · exact key _ _ ht1 hc
        · rw [if_neg ht1, zero_add] at h
          by_cases ht2 : F.term i
          · rw [if_pos ht2] at h; exact key _ _ ht2 h
          · rw [if_neg ht2] at h; exact absurd rfl h

lemma coefLAux_size : ∀ n (G : Forest), G.size = n → ∀ k (F : Forest), coefLAux n G k F ≠ 0 →
    G.size = F.size + 1 := by
  intro n
  induction n with
  | zero => intro G hG k F h; simp [coefLAux] at h
  | succ n ih =>
    intro G hG k F h
    have hne : G ≠ empty := fun h => by rw [h] at hG; simp [empty, size] at hG
    have hterm := term_len hne
    have hsize : (rem G.len G).size = n := by have := size_rem hterm; omega
    simp only [coefLAux] at h
    by_cases h1 : G.len ≠ k
    · rw [if_pos h1] at h
      by_cases ht : F.term G.len
      · rw [if_pos ht] at h; have := ih _ hsize _ _ h; have := size_rem ht; omega
      · rw [if_neg ht] at h; exact absurd rfl h
    · rw [if_neg h1] at h
      by_cases ht : F.term k
      · by_cases hc : coefLAux n (rem G.len G) k (rem k F) = 0
        · rw [if_pos ht, hc, zero_add] at h; have := coefRAux_size n _ hsize _ _ h; omega
        · have := ih _ hsize _ _ hc; have := size_rem ht; omega
      · rw [if_neg ht, zero_add] at h; have := coefRAux_size n _ hsize _ _ h; omega

lemma coefLAux_bound : ∀ n (G : Forest), G.size = n → ∀ k (F : Forest), coefLAux n G k F ≠ 0 →
    k ≤ G.len + G.size := by
  intro n
  induction n with
  | zero => intro G hG k F h; simp [coefLAux] at h
  | succ n ih =>
    intro G hG k F h
    have hne : G ≠ empty := fun h => by rw [h] at hG; simp [empty, size] at hG
    have hterm := term_len hne
    have hsize : (rem G.len G).size = n := by have := size_rem hterm; omega
    have hlen := len_rem_le G.len G
    simp only [coefLAux] at h
    by_cases h1 : G.len ≠ k
    · rw [if_pos h1] at h
      by_cases ht : F.term G.len
      · rw [if_pos ht] at h
        have := ih _ hsize _ _ h
        by_cases h2 : G.len < k
        · rw [if_pos h2] at this; omega
        · rw [if_neg h2] at this; omega
      · rw [if_neg ht] at h; exact absurd rfl h
    · omega

/-! ### Candidate lists -/

/-- All `F` with `coefRAux n G i F ≠ 0`. -/
def lowRAux : ℕ → Forest → ℕ → List Forest
  | 0, _, _ => [empty]
  | n + 1, G, i =>
    if G.len + 1 < i then (lowRAux n (rem G.len G) (i - 1)).map (ins G.len)
    else if i ≤ G.len then (lowRAux n (rem G.len G) i).map (ins (G.len + 1))
    else (lowRAux n (rem G.len G) i).map (ins (i - 1)) ++
      (lowRAux n (rem G.len G) (i - 1)).map (ins i)

/-- All `F` with `coefLAux n G k F ≠ 0`. -/
def lowLAux : ℕ → Forest → ℕ → List Forest
  | 0, _, _ => []
  | n + 1, G, k =>
    if G.len ≠ k then
      (lowLAux n (rem G.len G) (if G.len < k then k - 1 else k)).map (ins G.len)
    else (lowLAux n (rem G.len G) k).map (ins k) ++ lowRAux n (rem G.len G) k

lemma mem_map_ins {t : ℕ} {F : Forest} {l : List Forest} (ht : F.term t) (h : rem t F ∈ l) :
    F ∈ l.map (ins t) := List.mem_map.2 ⟨_, h, ins_rem ht⟩

lemma lowRAux_sound : ∀ n G i (F : Forest), coefRAux n G i F ≠ 0 → F ∈ lowRAux n G i := by
  intro n
  induction n with
  | zero =>
    intro G i F h
    simp only [coefRAux] at h
    split_ifs at h with hF
    · simp [lowRAux, hF]
    · exact absurd rfl h
  | succ n ih =>
    intro G i F h
    simp only [coefRAux] at h
    simp only [lowRAux]
    by_cases h1 : G.len + 1 < i
    · rw [if_pos h1] at h ⊢
      by_cases ht : F.term G.len
      · rw [if_pos ht] at h; exact mem_map_ins ht (ih _ _ _ h)
      · rw [if_neg ht] at h; exact absurd rfl h
    · rw [if_neg h1] at h ⊢
      by_cases h2 : i ≤ G.len
      · rw [if_pos h2] at h ⊢
        by_cases ht : F.term (G.len + 1)
        · rw [if_pos ht] at h; exact mem_map_ins ht (ih _ _ _ h)
        · rw [if_neg ht] at h; exact absurd rfl h
      · rw [if_neg h2] at h ⊢
        apply List.mem_append.2
        by_cases ht1 : F.term (i - 1)
        · by_cases hc : coefRAux n (rem G.len G) i (rem (i - 1) F) = 0
          · rw [if_pos ht1, hc, zero_add] at h
            by_cases ht2 : F.term i
            · rw [if_pos ht2] at h; exact Or.inr (mem_map_ins ht2 (ih _ _ _ h))
            · rw [if_neg ht2] at h; exact absurd rfl h
          · exact Or.inl (mem_map_ins ht1 (ih _ _ _ hc))
        · rw [if_neg ht1, zero_add] at h
          by_cases ht2 : F.term i
          · rw [if_pos ht2] at h; exact Or.inr (mem_map_ins ht2 (ih _ _ _ h))
          · rw [if_neg ht2] at h; exact absurd rfl h

lemma lowLAux_sound : ∀ n G k (F : Forest), coefLAux n G k F ≠ 0 → F ∈ lowLAux n G k := by
  intro n
  induction n with
  | zero => intro G k F h; simp [coefLAux] at h
  | succ n ih =>
    intro G k F h
    simp only [coefLAux] at h
    simp only [lowLAux]
    by_cases h1 : G.len ≠ k
    · rw [if_pos h1] at h ⊢
      by_cases ht : F.term G.len
      · rw [if_pos ht] at h; exact mem_map_ins ht (ih _ _ _ h)
      · rw [if_neg ht] at h; exact absurd rfl h
    · rw [if_neg h1] at h ⊢
      apply List.mem_append.2
      by_cases ht : F.term k
      · by_cases hc : coefLAux n (rem G.len G) k (rem k F) = 0
        · rw [if_pos ht, hc, zero_add] at h; exact Or.inr (lowRAux_sound _ _ _ _ h)
        · exact Or.inl (mem_map_ins ht (ih _ _ _ hc))
      · rw [if_neg ht, zero_add] at h; exact Or.inr (lowRAux_sound _ _ _ _ h)

/-- All `G` with `coefR G i F ≠ 0` (fuel `|F|`). -/
def upRAux : ℕ → ℕ → Forest → List Forest
  | 0, _, F => if F = empty then [empty] else []
  | m + 1, i, F => (if F = empty then [empty] else []) ++
    F.termList.flatMap (fun t =>
      if t + 1 < i then (upRAux m (i - 1) (rem t F)).map (ins t)
      else if t + 1 = i then (upRAux m i (rem t F)).map (ins t)
      else if t = i then (upRAux m (i - 1) (rem t F)).map (ins (i - 1))
      else (upRAux m i (rem t F)).map (ins (t - 1)))

/-- All `G` with `coefL G k F ≠ 0` (fuel `|F|`). -/
def upLAux : ℕ → ℕ → Forest → List Forest
  | 0, k, F => (upRAux 0 k F).map (ins k)
  | m + 1, k, F => (upRAux (m + 1) k F).map (ins k) ++
    F.termList.flatMap (fun t =>
      if t = k then (upLAux m k (rem k F)).map (ins k)
      else (upLAux m (if t < k then k - 1 else k) (rem t F)).map (ins t))

/-- Candidate upper covers of `F` via `L_k`. -/
def upL (k : ℕ) (F : Forest) : List Forest := upLAux F.size k F

lemma upRAux_succ_of_term {m t i : ℕ} {F : Forest} (ht : F.term t) {G : Forest}
    (h : G ∈ (if t + 1 < i then (upRAux m (i - 1) (rem t F)).map (ins t)
      else if t + 1 = i then (upRAux m i (rem t F)).map (ins t)
      else if t = i then (upRAux m (i - 1) (rem t F)).map (ins (i - 1))
      else (upRAux m i (rem t F)).map (ins (t - 1)))) : G ∈ upRAux (m + 1) i F := by
  simp only [upRAux]
  exact List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨t, mem_termList.2 ht, h⟩))

lemma size_pos_of_term {F : Forest} {t : ℕ} (h : F.term t) : F.size = (rem t F).size + 1 :=
  (size_rem h).symm

lemma upRAux_sound : ∀ n (G : Forest), G.size = n → ∀ i (F : Forest), 1 ≤ i →
    coefRAux n G i F ≠ 0 → G ∈ upRAux F.size i F := by
  intro n
  induction n with
  | zero =>
    intro G hG i F hi h
    simp only [coefRAux] at h
    split_ifs at h with hF
    · subst hF; rw [(eq_empty_iff_size G).2 hG]; simp [upRAux, empty, size]
    · exact absurd rfl h
  | succ n ih =>
    intro G hG i F hi h
    have hne : G ≠ empty := fun h => by rw [h] at hG; simp [empty, size] at hG
    have hterm := term_len hne
    have hsize : (rem G.len G).size = n := by have := size_rem hterm; omega
    have hj1 : 1 ≤ G.len := hterm.1
    have memIns : ∀ {t : ℕ} {l : List Forest}, t = G.len → rem G.len G ∈ l → G ∈ l.map (ins t) :=
      fun ht hl => List.mem_map.2 ⟨_, hl, by rw [ht]; exact ins_rem hterm⟩
    simp only [coefRAux] at h
    by_cases h1 : G.len + 1 < i
    · rw [if_pos h1] at h
      by_cases ht : F.term G.len
      · rw [if_pos ht] at h
        rw [size_pos_of_term ht]
        refine upRAux_succ_of_term ht ?_
        rw [if_pos h1]; exact memIns rfl (ih _ hsize _ _ (by omega) h)
      · rw [if_neg ht] at h; exact absurd rfl h
    · rw [if_neg h1] at h
      by_cases h2 : i ≤ G.len
      · rw [if_pos h2] at h
        by_cases ht : F.term (G.len + 1)
        · rw [if_pos ht] at h
          rw [size_pos_of_term ht]
          refine upRAux_succ_of_term ht ?_
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          exact memIns (by omega) (ih _ hsize _ _ hi h)
        · rw [if_neg ht] at h; exact absurd rfl h
      · rw [if_neg h2] at h
        have caseA : F.term (i - 1) → coefRAux n (rem G.len G) i (rem (i - 1) F) ≠ 0 →
            G ∈ upRAux F.size i F := by
          intro ht hc
          rw [size_pos_of_term ht]
          refine upRAux_succ_of_term ht ?_
          rw [if_neg (by omega), if_pos (by omega)]
          exact memIns (by omega) (ih _ hsize _ _ hi hc)
        have caseB : F.term i → coefRAux n (rem G.len G) (i - 1) (rem i F) ≠ 0 →
            G ∈ upRAux F.size i F := by
          intro ht hc
          rw [size_pos_of_term ht]
          refine upRAux_succ_of_term ht ?_
          rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
          exact memIns (by omega) (ih _ hsize _ _ (by omega) hc)
        by_cases ht1 : F.term (i - 1)
        · by_cases hc : coefRAux n (rem G.len G) i (rem (i - 1) F) = 0
          · rw [if_pos ht1, hc, zero_add] at h
            by_cases ht2 : F.term i
            · rw [if_pos ht2] at h; exact caseB ht2 h
            · rw [if_neg ht2] at h; exact absurd rfl h
          · exact caseA ht1 hc
        · rw [if_neg ht1, zero_add] at h
          by_cases ht2 : F.term i
          · rw [if_pos ht2] at h; exact caseB ht2 h
          · rw [if_neg ht2] at h; exact absurd rfl h

lemma upLAux_sound : ∀ n (G : Forest), G.size = n → ∀ k (F : Forest), 1 ≤ k →
    coefLAux n G k F ≠ 0 → G ∈ upLAux F.size k F := by
  intro n
  induction n with
  | zero => intro G hG k F hk h; simp [coefLAux] at h
  | succ n ih =>
    intro G hG k F hk h
    have hne : G ≠ empty := fun h => by rw [h] at hG; simp [empty, size] at hG
    have hterm := term_len hne
    have hsize : (rem G.len G).size = n := by have := size_rem hterm; omega
    have hj1 : 1 ≤ G.len := hterm.1
    have memIns : ∀ {t : ℕ} {l : List Forest}, t = G.len → rem G.len G ∈ l → G ∈ l.map (ins t) :=
      fun ht hl => List.mem_map.2 ⟨_, hl, by rw [ht]; exact ins_rem hterm⟩
    have hflat : ∀ t, F.term t → ∀ G', G' ∈ (if t = k then (upLAux (rem t F).size k (rem k F)).map
        (ins k) else (upLAux (rem t F).size (if t < k then k - 1 else k) (rem t F)).map (ins t)) →
        G' ∈ upLAux F.size k F := by
      intro t ht G' hG'
      rw [size_pos_of_term ht]
      simp only [upLAux]
      exact List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨t, mem_termList.2 ht, hG'⟩))
    have hR : coefRAux n (rem G.len G) k F ≠ 0 → G.len = k → G ∈ upLAux F.size k F := by
      intro hc hk'
      have hmem := upRAux_sound n _ hsize _ _ hk hc
      rcases Nat.eq_zero_or_pos F.size with h0 | h0
      · rw [h0]; simp only [upLAux]; rw [← h0]; exact memIns hk'.symm hmem
      · obtain ⟨m, hm⟩ : ∃ m, F.size = m + 1 := ⟨F.size - 1, by omega⟩
        rw [hm]; simp only [upLAux]; rw [← hm]
        exact List.mem_append.2 (Or.inl (memIns hk'.symm hmem))
    simp only [coefLAux] at h
    by_cases h1 : G.len ≠ k
    · rw [if_pos h1] at h
      by_cases ht : F.term G.len
      · rw [if_pos ht] at h
        refine hflat _ ht G ?_
        rw [if_neg h1]
        exact memIns rfl (ih _ hsize _ _ (by split_ifs <;> omega) h)
      · rw [if_neg ht] at h; exact absurd rfl h
    · rw [if_neg h1] at h
      by_cases ht : F.term k
      · by_cases hc : coefLAux n (rem G.len G) k (rem k F) = 0
        · rw [if_pos ht, hc, zero_add] at h; exact hR h (by omega)
        · refine hflat _ ht G ?_
          rw [if_pos rfl]
          exact memIns (by omega) (ih _ hsize _ _ hk hc)
      · rw [if_neg ht, zero_add] at h; exact hR h (by omega)

/-- Candidate lower covers of `G` via `L_k`. -/
def lowL (G : Forest) (k : ℕ) : List Forest := lowLAux G.size G k

end QuasisymmetricBruhat
