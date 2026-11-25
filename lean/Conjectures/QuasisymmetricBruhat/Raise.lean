import Conjectures.QuasisymmetricBruhat.Order

/-!
# Raising the first code entry

If the final piece at the leaf `1` is followed by a bare leaf, raising `c₁` adds a new root
`(1, c₁ + 1)` whose right child is that leaf; its label is forced to be `1`, so
`P_{c + e₁} = x₁ · P_c`.  Hence `F ⋖ F + e₁` with the single-term Monk product `L₁ P_F`.
-/

namespace QuasisymmetricBruhat

open MvPolynomial Finset Forest

section raise
variable {F G : Forest} (h1 : G.c 1 = F.c 1 + 1) (h2 : ∀ i, 2 ≤ i → G.c i = F.c i)
include h1 h2

omit h1 in
lemma E_raise : ∀ p, 2 ≤ p → G.E p = F.E p := by
  apply F.E_unique (fun p => G.E p) (a := 2) (by omega)
  intro p hp
  rw [G.E_eq (by omega), endAt, h2 p hp]

omit h1 in
lemma endAt_raise (p t : ℕ) (hp : 1 ≤ p) : G.endAt p t = F.endAt p t := by
  simp only [endAt]
  exact iterate_congr_on (a := 1) (fun e he => E_raise h2 _ (by omega))
    (fun e _ => by have := F.le_E (e + 1); omega) t p hp

lemma IN_raise : G.IN = insert (1, F.c 1 + 1) F.IN := by
  ext ⟨i, t⟩
  simp only [mem_insert, mem_IN, Prod.mk.injEq]
  constructor
  · rintro ⟨hi, ht, hc⟩
    by_cases hi1 : i = 1
    · subst hi1; rw [h1] at hc
      by_cases htc : t = F.c 1 + 1
      · exact Or.inl ⟨rfl, htc⟩
      · exact Or.inr ⟨le_rfl, ht, by omega⟩
    · exact Or.inr ⟨hi, ht, by rw [← h2 i (by omega)]; exact hc⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hi, ht, hc⟩)
    · exact ⟨le_rfl, by omega, by rw [h1]⟩
    · refine ⟨hi, ht, ?_⟩
      by_cases hi1 : i = 1
      · subst hi1; rw [h1]; omega
      · rw [h2 i (by omega)]; exact hc

omit h1 in
lemma rc_raise (v : ℕ × ℕ) (hv : 1 ≤ v.1) : G.rc v = F.rc v := by
  have hq : 2 ≤ F.endAt v.1 (v.2 - 1) + 1 := by have := F.le_endAt v.1 (v.2 - 1); omega
  rw [rc_of_endAt (endAt_raise h2 _ _ hv), rc_of_endAt rfl, h2 _ hq]

/-- `P_{c + e₁} = x₁ P_c` when the piece at `1` is followed by a bare leaf. -/
theorem forestPoly_raise (hleaf : F.c (F.E 1 + 1) = 0) :
    forestPoly G = x 1 * forestPoly F := by
  classical
  set a := F.c 1
  set w : ℕ × ℕ := (1, a + 1)
  have hwF : w ∉ F.IN := by simp [w, mem_IN, a]
  have hINF : ∀ v ∈ F.IN, v ≠ w := fun v hv h => hwF (h ▸ hv)
  have hrcw : G.rc w = none := by
    rw [rc_of_endAt (e := F.E 1) (by
      simp only [w, Nat.add_sub_cancel]; rw [endAt_raise h2 _ _ le_rfl, F.E_eq le_rfl])]
    rw [h2 _ (by have := F.le_E 1; omega), hleaf]; simp
  have hnotchild : ∀ v ∈ F.IN, ∀ u, (lc v = some u ∨ G.rc v = some u) → u ≠ w := by
    intro v hv u hu huw
    subst huw
    rcases hu with hu | hu
    · unfold lc at hu; split_ifs at hu with h
      simp only [Option.some.injEq, Prod.mk.injEq, w] at hu
      have := (mem_IN.1 hv).2.2; rw [hu.1] at this; omega
    · have := (rc_mem hu).2; rw [rc_raise h2 v (mem_IN.1 hv).1] at hu
      have := (rc_mem hu).2; simp [w] at this; have := (mem_IN.1 hv).1; omega
  rw [forestPoly, forestPoly, mul_sum, IN_raise h1 h2]
  symm
  apply sum_nbij' (fun lam => Function.update lam w 1) (fun mu => Function.update mu w 0)
  · intro lam hl
    obtain ⟨hval, hz⟩ := mem_labelings.1 hl
    refine mem_labelings.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [IN_raise h1 h2] at hv
      by_cases hvw : v = w
      · subst hvw
        simp only [Function.update_self]
        refine ⟨le_rfl, by simp [rho, w], fun u hu => ?_, fun u hu => by rw [hrcw] at hu; cases hu⟩
        unfold lc at hu; split_ifs at hu with h
        simp only [w, Option.some.injEq] at hu
        subst hu
        rw [show ((1 : ℕ), a + 1 - 1) = (1, a) by simp]
        have hu' : (1, a) ∈ F.IN := mem_IN.2 ⟨le_rfl, by simp only [w] at h; omega, le_rfl⟩
        rw [Function.update_of_ne (hINF _ hu')]
        exact (hval _ hu').1
      · have hvF : v ∈ F.IN := by
          rcases mem_insert.1 hv with h | h
          · exact absurd h hvw
          · exact h
        obtain ⟨b1, b2, bl, br⟩ := hval v hvF
        rw [Function.update_of_ne hvw]
        refine ⟨b1, b2, fun u hu => ?_, fun u hu => ?_⟩
        · rw [Function.update_of_ne (hnotchild v hvF u (Or.inl hu))]; exact bl u hu
        · rw [Function.update_of_ne (hnotchild v hvF u (Or.inr hu))]
          rw [rc_raise h2 v (mem_IN.1 hvF).1] at hu; exact br u hu
    · rw [IN_raise h1 h2, mem_insert, not_or] at hv
      rw [Function.update_of_ne hv.1]; exact hz v hv.2
  · intro mu hm
    obtain ⟨hval, hz⟩ := mem_labelings.1 hm
    refine mem_labelings.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hvG : v ∈ G.IN := by rw [IN_raise h1 h2]; exact mem_insert_of_mem hv
      obtain ⟨b1, b2, bl, br⟩ := hval v hvG
      rw [Function.update_of_ne (hINF v hv)]
      refine ⟨b1, b2, fun u hu => ?_, fun u hu => ?_⟩
      · rw [Function.update_of_ne (hnotchild v hv u (Or.inl hu))]; exact bl u hu
      · have hu' : G.rc v = some u := by rw [rc_raise h2 v (mem_IN.1 hv).1]; exact hu
        rw [Function.update_of_ne (hnotchild v hv u (Or.inr hu'))]; exact br u hu'
    · by_cases hvw : v = w
      · subst hvw; simp
      · rw [Function.update_of_ne hvw]
        apply hz
        rw [IN_raise h1 h2, mem_insert, not_or]; exact ⟨hvw, hv⟩
  · intro lam hl
    have hz := (mem_labelings.1 hl).2
    funext v
    by_cases hvw : v = w
    · subst hvw; simp [hz _ hwF]
    · simp [Function.update_of_ne hvw]
  · intro mu hm
    obtain ⟨hval, -⟩ := mem_labelings.1 hm
    have hwG : w ∈ G.IN := by rw [IN_raise h1 h2]; exact mem_insert_self _ _
    have hmw : mu w = 1 := by
      obtain ⟨b1, b2, -, -⟩ := hval w hwG
      simp only [rho, w] at b1 b2 ⊢; omega
    funext v
    by_cases hvw : v = w
    · subst hvw; simp [hmw]
    · simp [Function.update_of_ne hvw]
  · intro lam hl
    rw [prod_insert hwF, Function.update_self]
    congr 1
    apply prod_congr rfl; intro v hv
    rw [Function.update_of_ne (hINF v hv)]

end raise

/-- Code raising at position `1` gives a Monk cover when `c_{E(1)+1} = 0`. -/
theorem monkCover_raise {F G : Forest} (h1 : G.c 1 = F.c 1 + 1) (h2 : ∀ i, 2 ≤ i → G.c i = F.c i)
    (hleaf : F.c (F.E 1 + 1) = 0) : MonkCover F G := by
  refine ⟨1, le_rfl, {G}, mem_singleton_self _, ?_⟩
  rw [sum_singleton, forestPoly_raise h1 h2 hleaf]
  simp [L, x]

end QuasisymmetricBruhat
