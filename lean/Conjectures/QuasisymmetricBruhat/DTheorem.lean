import Conjectures.QuasisymmetricBruhat.Ops

/-!
# The divided-difference formula `Dⱼ P_F = [j ∈ term F] · xⱼ · P_{F/j}`

This is NST's `Tⱼ P_F = P_{F/j}` (or `0`), multiplied by `xⱼ`, proved directly from
Definition 2.3.  Writing `R_a P_F` as a sum over labelings avoiding the value `a`, the labelings
avoiding both `j` and `j+1` cancel; relabelling `j+1 ↦ j` matches the labelings that use `j+1`
with those using `j` only at vertices with `ρ ≥ j+1`.  What is left are the labelings with a
vertex `v` of `ρ(v) = j` labelled `j`; such a labeling forces a terminal node at `j` labelled
`j`, and deleting it is a bijection onto the labelings of `F/j`.
-/

namespace QuasisymmetricBruhat

open MvPolynomial Finset Forest

/-- Relabelling after deleting the value `a`. -/
def dl (a l : ℕ) : ℕ := if l < a then l else l - 1

lemma R_prod (F : Forest) (lam : ℕ × ℕ → ℕ) (a : ℕ) :
    R a (∏ v ∈ F.IN, x (lam v)) =
      if ∀ v ∈ F.IN, lam v ≠ a then ∏ v ∈ F.IN, x (dl a (lam v)) else 0 := by
  rw [map_prod]
  split_ifs with h
  · apply prod_congr rfl; intro v hv
    rw [x, R_X, dl]; have := h v hv
    split_ifs <;> rfl
  · obtain ⟨v, hv, hva⟩ : ∃ v ∈ F.IN, lam v = a := by
      by_contra hc; exact h (fun v hv hva => hc ⟨v, hv, hva⟩)
    exact prod_eq_zero hv (by rw [x, R_X, hva]; simp)

lemma R_forestPoly (F : Forest) (a : ℕ) :
    R a (forestPoly F) = ∑ lam ∈ F.labelings.filter (fun lam => ∀ v ∈ F.IN, lam v ≠ a),
      ∏ v ∈ F.IN, x (dl a (lam v)) := by
  rw [forestPoly, map_sum, sum_filter]
  exact sum_congr rfl fun lam _ => R_prod F lam a

lemma valid_comp {F : Forest} {lam : ℕ × ℕ → ℕ} (φ : ℕ → ℕ) (hv : F.Valid lam)
    (hb : ∀ v ∈ F.IN, 1 ≤ φ (lam v) ∧ φ (lam v) ≤ v.1)
    (hle : ∀ v ∈ F.IN, ∀ u ∈ F.IN, lam v ≤ lam u → φ (lam v) ≤ φ (lam u))
    (hlt : ∀ v ∈ F.IN, ∀ u ∈ F.IN, lam v < lam u → φ (lam v) < φ (lam u)) :
    F.Valid (fun v => φ (lam v)) := by
  intro v hvm
  obtain ⟨-, -, hl, hr⟩ := hv v hvm
  refine ⟨(hb v hvm).1, (hb v hvm).2, fun u hu => ?_, fun u hu => ?_⟩
  · exact hle v hvm u (lc_mem hvm hu).1 (hl u hu)
  · exact hlt v hvm u (rc_mem hu).1 (hr u hu)

lemma chain_le {F : Forest} {lam : ℕ × ℕ → ℕ} (hv : F.Valid lam) {i s : ℕ} (hs : 1 ≤ s) :
    ∀ n, (i, s + n) ∈ F.IN → lam (i, s + n) ≤ lam (i, s) := by
  intro n
  induction n with
  | zero => intro _; exact le_rfl
  | succ n ih =>
    intro hm
    have hm' : (i, s + n) ∈ F.IN := by
      rw [mem_IN] at hm ⊢; simp only at hm ⊢; omega
    have := (hv _ hm).2.2.1 (i, s + n) (by simp [lc]; omega)
    exact le_trans this (ih hm')

section
variable (F : Forest) (j : ℕ)

/-- The labelings that survive the cancellations. -/
noncomputable def surv : Finset (ℕ × ℕ → ℕ) := by
  classical
  exact F.labelings.filter (fun lam => (∀ v ∈ F.IN, lam v ≠ j + 1) ∧
    ∃ v ∈ F.IN, lam v = j ∧ v.1 ≤ j)

lemma mem_surv {lam : ℕ × ℕ → ℕ} : lam ∈ surv F j ↔ lam ∈ F.labelings ∧
    (∀ v ∈ F.IN, lam v ≠ j + 1) ∧ ∃ v ∈ F.IN, lam v = j ∧ v.1 ≤ j := by
  classical
  simp only [surv, mem_filter]

end

section cancel
variable (F : Forest) (j : ℕ)

/-- `λ` avoids the value `a`. -/
def Av (a : ℕ) (lam : ℕ × ℕ → ℕ) : Prop := ∀ v ∈ F.IN, lam v ≠ a

instance (a : ℕ) : DecidablePred (Av F a) := fun lam => by unfold Av; infer_instance

/-- The image of the term of `λ` under `R_a`. -/
noncomputable def TT (a : ℕ) (lam : ℕ × ℕ → ℕ) : Pol := ∏ v ∈ F.IN, x (dl a (lam v))

/-- Labelings using `j+1` but not `j`. -/
noncomputable def setC : Finset (ℕ × ℕ → ℕ) :=
  (F.labelings.filter (Av F j)).filter (fun lam => ¬ Av F (j + 1) lam)

/-- Labelings using `j` but not `j+1`. -/
noncomputable def setB : Finset (ℕ × ℕ → ℕ) :=
  (F.labelings.filter (Av F (j + 1))).filter (fun lam => ¬ Av F j lam)

/-- Every vertex labelled `j` has `ρ ≥ j + 1`. -/
def Cond (lam : ℕ × ℕ → ℕ) : Prop := ∀ v ∈ F.IN, lam v = j → j + 1 ≤ v.1

instance : DecidablePred (Cond F j) := fun lam => by unfold Cond; infer_instance

lemma R_forestPoly' (a : ℕ) :
    R a (forestPoly F) = ∑ lam ∈ F.labelings.filter (Av F a), TT F a lam := by
  rw [R_forestPoly]; rfl

lemma stepA :
    ∑ lam ∈ (F.labelings.filter (Av F (j + 1))).filter (Av F j), TT F (j + 1) lam =
      ∑ lam ∈ (F.labelings.filter (Av F j)).filter (Av F (j + 1)), TT F j lam := by
  rw [Finset.filter_comm]
  apply sum_congr rfl
  intro lam hl
  simp only [mem_filter] at hl
  apply prod_congr rfl; intro v hv
  have h1 := hl.1.2 v hv; have h2 := hl.2 v hv
  simp only [dl]; congr 1; split_ifs <;> omega

lemma stepC (hj : 1 ≤ j) :
    ∑ lam ∈ setC F j, TT F j lam = ∑ lam ∈ (setB F j).filter (Cond F j), TT F (j + 1) lam := by
  apply sum_nbij' (fun lam v => if lam v = j + 1 then j else lam v)
    (fun mu v => if mu v = j then j + 1 else mu v)
  · intro lam hl
    simp only [setC, setB, Cond, Av, mem_filter, not_forall, not_not] at hl ⊢
    obtain ⟨⟨hlab, hav⟩, v0, hv0, hv0j⟩ := hl
    obtain ⟨hval, hz⟩ := mem_labelings.1 hlab
    refine ⟨⟨⟨mem_labelings.2 ⟨?_, fun v hv => by simp [hz v hv]⟩, fun v hv => by
      split_ifs <;> omega⟩, v0, hv0, by simp [hv0j]⟩, fun v hv h => ?_⟩
    · refine valid_comp (fun l => if l = j + 1 then j else l) hval (fun v hv => ?_)
        (fun v hv u hu h => ?_) (fun v hv u hu h => ?_)
      · have := hval v hv; have := hav v hv; simp only [rho] at *; split_ifs <;> omega
      · have := hav v hv; have := hav u hu; split_ifs <;> omega
      · have := hav v hv; have := hav u hu; split_ifs <;> omega
    · have := hval v hv; have := hav v hv; simp only [rho] at *
      split_ifs at h <;> omega
  · intro mu hm
    simp only [setC, setB, Cond, Av, mem_filter, not_forall, not_not] at hm ⊢
    obtain ⟨⟨⟨hlab, hav⟩, v0, hv0, hv0j⟩, hcond⟩ := hm
    obtain ⟨hval, hz⟩ := mem_labelings.1 hlab
    refine ⟨⟨mem_labelings.2 ⟨?_, fun v hv => by simp [hz v hv]; omega⟩, fun v hv => by
      split_ifs <;> omega⟩, v0, hv0, by simp [hv0j]⟩
    refine valid_comp (fun l => if l = j then j + 1 else l) hval (fun v hv => ?_)
      (fun v hv u hu h => ?_) (fun v hv u hu h => ?_)
    · have := hval v hv; have := hav v hv; have := hcond v hv
      simp only [rho] at *; split_ifs <;> omega
    · have := hav v hv; have := hav u hu; split_ifs <;> omega
    · have := hav v hv; have := hav u hu; split_ifs <;> omega
  · intro lam hl
    unfold setC at hl; rw [mem_filter, mem_filter] at hl
    funext v
    dsimp only
    by_cases hv : v ∈ F.IN
    · have := hl.1.2 v hv; split_ifs <;> omega
    · have := (mem_labelings.1 hl.1.1).2 v hv; split_ifs <;> omega
  · intro mu hm
    rw [mem_filter] at hm; unfold setB at hm; rw [mem_filter, mem_filter] at hm
    funext v
    dsimp only
    by_cases hv : v ∈ F.IN
    · have := hm.1.1.2 v hv; split_ifs <;> omega
    · have := (mem_labelings.1 hm.1.1.1).2 v hv; split_ifs <;> omega
  · intro lam hl
    unfold setC at hl; rw [mem_filter, mem_filter] at hl
    apply prod_congr rfl; intro v hv
    have := hl.1.2 v hv
    simp only [dl]; congr 1; split_ifs <;> omega

lemma stepS : (setB F j).filter (fun lam => ¬ Cond F j lam) = surv F j := by
  ext lam
  simp only [setB, Cond, Av, mem_filter, mem_surv, not_forall, not_not, exists_prop]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, -⟩, v, hv, h3, h4⟩
    exact ⟨h1, h2, v, hv, h3, by omega⟩
  · rintro ⟨h1, h2, v, hv, h3, h4⟩
    have := ((mem_labelings.1 h1).1 v hv).2.1; simp only [rho] at this
    exact ⟨⟨⟨h1, h2⟩, v, hv, h3⟩, v, hv, h3, by omega⟩

lemma D_forestPoly_surv (hj : 1 ≤ j) :
    D j (forestPoly F) = ∑ lam ∈ surv F j, ∏ v ∈ F.IN, x (dl (j + 1) (lam v)) := by
  rw [D, R_forestPoly', R_forestPoly',
    ← sum_filter_add_sum_filter_not (F.labelings.filter (Av F (j + 1))) (Av F j),
    ← sum_filter_add_sum_filter_not (F.labelings.filter (Av F j)) (Av F (j + 1)), stepA]
  change _ + ∑ lam ∈ setB F j, TT F (j + 1) lam - (_ + ∑ lam ∈ setC F j, TT F j lam) = _
  rw [stepC F j hj, add_sub_add_left_eq_sub,
    ← sum_filter_add_sum_filter_not (setB F j) (Cond F j), add_sub_cancel_left, stepS]
  rfl

end cancel

lemma surv_spec {F : Forest} {j : ℕ} {lam : ℕ × ℕ → ℕ} (hl : lam ∈ surv F j) :
    F.term j ∧ (j, 1) ∈ F.IN ∧ lam (j, 1) = j := by
  obtain ⟨hlab, hav, v, hv, hvj, hv1⟩ := (mem_surv F j).1 hl
  have hval := (mem_labelings.1 hlab).1
  have hb := hval v hv
  simp only [rho] at hb
  obtain ⟨a, t⟩ := v
  simp only at hv1 hvj hb
  obtain rfl : a = j := by omega
  have hmem := mem_IN.1 hv
  simp only at hmem
  have h1 : (a, 1) ∈ F.IN := mem_IN.2 ⟨hmem.1, le_rfl, by simp only; omega⟩
  have hchain := chain_le hval (i := a) (s := 1) le_rfl (t - 1)
    (by rw [show 1 + (t - 1) = t by omega]; exact hv)
  rw [show 1 + (t - 1) = t by omega] at hchain
  have hb1 := (hval _ h1).2.1; simp only [rho] at hb1
  have hlam1 : lam (a, 1) = a := by omega
  refine ⟨⟨hmem.1, by omega, ?_⟩, h1, hlam1⟩
  by_contra hc
  have hrc : F.rc (a, 1) = some (a + 1, F.c (a + 1)) := by
    rw [rc_of_endAt (e := a) (by simp [endAt])]
    rw [if_pos (by omega)]
  obtain ⟨hum, -⟩ := rc_mem hrc
  have h2 := (hval _ h1).2.2.2 _ hrc
  have h3 := (hval _ hum).2.1; simp only [rho] at h3
  have h4 := hav _ hum
  omega

lemma D_forestPoly_of_not_term {F : Forest} {j : ℕ} (hj : 1 ≤ j) (h : ¬ F.term j) :
    D j (forestPoly F) = 0 := by
  rw [D_forestPoly_surv F j hj]
  apply sum_eq_zero; intro lam hl
  exact absurd (surv_spec hl).1 h

/-- Inverse of `psi j` away from the new vertex. -/
def psiInv (j : ℕ) (v : ℕ × ℕ) : ℕ × ℕ :=
  if v.1 < j then v else if v.1 = j then (j, v.2 - 1) else (v.1 - 1, v.2)

lemma psiInv_psi (j : ℕ) (v : ℕ × ℕ) : psiInv j (psi j v) = v := by
  obtain ⟨a, b⟩ := v
  simp only [psi]
  split_ifs with h1 h2 <;> simp only [psiInv] <;> split_ifs <;> simp_all <;> omega

/-- Insert back the value `j+1` after the label `j` of the new vertex. -/
def ep (j l : ℕ) : ℕ := if l ≤ j then l else l + 1

lemma D_forestPoly_ins {j : ℕ} (hj : 1 ≤ j) (G : Forest) :
    D j (forestPoly (ins j G)) = x j * forestPoly G := by
  classical
  set H := ins j G
  have hIN : H.IN = insert (j, 1) (G.IN.image (psi j)) := IN_ins hj G
  have hnot : (j, 1) ∉ G.IN.image (psi j) := by
    simp only [mem_image, not_exists, not_and]
    intro v hv; exact psi_ne j v (mem_IN.1 hv).2.1
  have hmemH : ∀ v' ∈ G.IN, psi j v' ∈ H.IN := fun v' hv' => by
    rw [hIN]; exact mem_insert_of_mem (mem_image_of_mem _ hv')
  have hpre : ∀ v ∈ H.IN, v ≠ (j, 1) → psiInv j v ∈ G.IN ∧ psi j (psiInv j v) = v := by
    intro v hv hne
    rw [hIN, mem_insert] at hv
    rcases hv with rfl | hv
    · exact absurd rfl hne
    · obtain ⟨v', hv', rfl⟩ := mem_image.1 hv
      rw [psiInv_psi]; exact ⟨hv', rfl⟩
  have hfst : ∀ v' : ℕ × ℕ, (psi j v').1 = if v'.1 ≤ j then v'.1 else v'.1 + 1 := by
    intro v'; simp only [psi]; split_ifs <;> simp <;> omega
  rw [D_forestPoly_surv H j hj, forestPoly, mul_sum]
  symm
  apply sum_nbij' (fun mu v => if v = (j, 1) then j else if v ∈ H.IN then ep j (mu (psiInv j v))
      else 0)
    (fun lam v' => if v' ∈ G.IN then dl (j + 1) (lam (psi j v')) else 0)
  · -- labelings of `G` go to surviving labelings of `H`
    intro mu hm
    obtain ⟨hval, hz⟩ := mem_labelings.1 hm
    have hbd : ∀ v' ∈ G.IN, 1 ≤ mu v' ∧ mu v' ≤ v'.1 := fun v' hv' =>
      ⟨(hval v' hv').1, (hval v' hv').2.1⟩
    rw [mem_surv]
    have hH1 : (j, 1) ∈ H.IN := by rw [hIN]; exact mem_insert_self _ _
    refine ⟨mem_labelings.2 ⟨fun v hv => ?_, fun v hv => ?_⟩, fun v hv => ?_,
      ⟨(j, 1), hH1, by simp, le_rfl⟩⟩
    · dsimp only
      by_cases hv1 : v = (j, 1)
      · subst hv1
        simp only [if_true]
        refine ⟨hj, by simp [rho], fun u hu => by simp [lc] at hu, fun u hu => ?_⟩
        rw [rc_ins_new hj G] at hu; cases hu
      · obtain ⟨hv', hpv⟩ := hpre v hv hv1
        set v' := psiInv j v
        have hval' : ∀ w ∈ H.IN, w ≠ (j, 1) → ∀ w' ∈ G.IN, psi j w' = w →
            (if w = (j, 1) then j else if w ∈ H.IN then ep j (mu (psiInv j w)) else 0) =
              ep j (mu w') := by
          intro w hw hw1 w' hw' hpw
          rw [if_neg hw1, if_pos hw, ← hpw, psiInv_psi]
        rw [hval' v hv hv1 v' hv' hpv]
        have hb := hbd v' hv'
        have hrho : ep j (mu v') ≤ v.1 := by
          rw [← hpv, hfst]; simp only [ep]; split_ifs <;> omega
        refine ⟨by simp only [ep]; split_ifs <;> omega, hrho, fun u hu => ?_, fun u hu => ?_⟩
        · rw [← hpv, lc_ins hj G v' hv'] at hu
          split_ifs at hu with hex
          · cases hu
            rw [if_pos rfl]
            have : v.1 = j := by rw [← hpv, hfst, hex.1, if_pos le_rfl]
            omega
          · obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.1 hu
            have hu'm := (lc_mem hv' hu').1
            rw [hval' _ (hmemH u' hu'm) (psi_ne j u' (mem_IN.1 hu'm).2.1) u' hu'm rfl]
            have := (hval v' hv').2.2.1 u' hu'
            simp only [ep]; split_ifs <;> omega
        · rw [← hpv, rc_ins hj G v' hv'] at hu
          split_ifs at hu with hex
          · cases hu
            rw [if_pos rfl]
            have : v.1 < j := by rw [← hpv, hfst, if_pos (le_of_lt hex.1)]; exact hex.1
            omega
          · obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.1 hu
            have hu'm := (rc_mem hu').1
            rw [hval' _ (hmemH u' hu'm) (psi_ne j u' (mem_IN.1 hu'm).2.1) u' hu'm rfl]
            have := (hval v' hv').2.2.2 u' hu'
            simp only [ep]; split_ifs <;> omega
    · have hv1 : v ≠ (j, 1) := fun h => hv (h ▸ hH1)
      simp [hv1, hv]
    · by_cases hv1 : v = (j, 1)
      · simp [hv1]
      · simp only [hv1, if_false, hv, if_true, ep]; split_ifs <;> omega
  · -- surviving labelings of `H` go to labelings of `G`
    intro lam hl
    obtain ⟨hterm, hH1, hlam1⟩ := surv_spec hl
    obtain ⟨hlab, hav, -⟩ := (mem_surv H j).1 hl
    obtain ⟨hval, hz⟩ := mem_labelings.1 hlab
    refine mem_labelings.2 ⟨fun v' hv' => ?_, fun v' hv' => by simp [hv']⟩
    dsimp only
    have hv := hmemH v' hv'
    have hval' : ∀ w' ∈ G.IN,
        (if w' ∈ G.IN then dl (j + 1) (lam (psi j w')) else 0) = dl (j + 1) (lam (psi j w')) :=
      fun w' hw' => if_pos hw'
    rw [hval' v' hv']
    obtain ⟨hb1, hb2, hl', hr'⟩ := hval _ hv
    have hne := hav _ hv
    simp only [rho] at hb2
    rw [hfst] at hb2
    refine ⟨by simp only [dl]; split_ifs <;> omega,
      by split_ifs at hb2 <;> simp only [dl, rho] <;> split_ifs <;> omega,
      fun u' hu' => ?_, fun u' hu' => ?_⟩
    · have hu'm := (lc_mem hv' hu').1
      rw [hval' u' hu'm]
      have := hl' (psi j u') (by
        rw [lc_ins hj G v' hv', if_neg (by
          rintro ⟨-, h2⟩; simp [lc, h2] at hu'), hu']; rfl)
      have := hav _ (hmemH u' hu'm)
      simp only [dl]; split_ifs <;> omega
    · have hu'm := (rc_mem hu').1
      rw [hval' u' hu'm]
      have := hr' (psi j u') (by
        rw [rc_ins hj G v' hv', if_neg (by
          rintro ⟨-, h2, h3⟩
          rw [rc_of_endAt (e := G.endAt v'.1 (v'.2 - 1)) rfl, h2, h3] at hu'
          simp at hu'), hu']; rfl)
      have := hav _ (hmemH u' hu'm)
      simp only [dl]; split_ifs <;> omega
  · -- left inverse
    intro mu hm
    have hz := (mem_labelings.1 hm).2
    funext v'
    by_cases hv' : v' ∈ G.IN
    · dsimp only
      rw [if_pos hv', if_neg (psi_ne j v' (mem_IN.1 hv').2.1), if_pos (hmemH v' hv'),
        psiInv_psi]
      simp only [dl, ep]; split_ifs <;> omega
    · rw [if_neg hv', hz v' hv']
  · -- right inverse
    intro lam hl
    obtain ⟨-, -, hlam1⟩ := surv_spec hl
    obtain ⟨hlab, hav, -⟩ := (mem_surv H j).1 hl
    have hz := (mem_labelings.1 hlab).2
    funext v
    by_cases hv1 : v = (j, 1)
    · rw [if_pos hv1, hv1, hlam1]
    · rw [if_neg hv1]
      by_cases hv : v ∈ H.IN
      · obtain ⟨hv', hpv⟩ := hpre v hv hv1
        rw [if_pos hv]; dsimp only; rw [if_pos hv', hpv]
        have := hav v hv
        simp only [dl, ep]; split_ifs <;> omega
      · rw [if_neg hv, hz v hv]
  · -- the monomials agree
    intro mu hm
    have hz := (mem_labelings.1 hm).2
    rw [hIN, prod_insert hnot, prod_image (fun a _ b _ h => psi_injective j h)]
    simp only [if_true, dl, show j < j + 1 by omega]
    congr 1
    apply prod_congr rfl; intro v' hv'
    have hmem : psi j v' ∈ insert (j, 1) (image (psi j) G.IN) := hIN ▸ hmemH v' hv'
    rw [if_neg (psi_ne j v' (mem_IN.1 hv').2.1), if_pos hmem, psiInv_psi]
    simp only [ep]; congr 1; split_ifs <;> omega

/-- `Dⱼ P_F = xⱼ P_{F/j}` if `j` is terminal in `F`, and `0` otherwise. -/
theorem D_forestPoly {F : Forest} {j : ℕ} (hj : 1 ≤ j) :
    D j (forestPoly F) = if F.term j then x j * forestPoly (rem j F) else 0 := by
  split_ifs with h
  · conv_lhs => rw [← ins_rem h]
    exact D_forestPoly_ins hj _
  · exact D_forestPoly_of_not_term hj h

end QuasisymmetricBruhat
