import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Finset.Sort
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith

/-! Largest-gap cuts of cyclic perfect difference sets uniquely minimize length
in their real Golomb ruler chamber (Notik, §7). -/

namespace SingerGolombChamber

open Finset

def IsCyclicPDS (N : ℕ) [NeZero N] (D : Finset (ZMod N)) : Prop :=
  2 ≤ D.card ∧ ∀ r : ZMod N, r ≠ 0 → ∃! p : ZMod N × ZMod N,
    p.1 ∈ D ∧ p.2 ∈ D ∧ p.1 ≠ p.2 ∧ p.1 - p.2 = r

def IsRealGolomb {n : ℕ} [NeZero n] (x : Fin n → ℝ) : Prop :=
  x 0 = 0 ∧ StrictMono x ∧ (∀ i j : Fin n, i < j → 1 ≤ x j - x i) ∧
    ∀ i j k l : Fin n, i < j → k < l → (i, j) ≠ (k, l) →
      1 ≤ |(x j - x i) - (x l - x k)|

def InChamber {n : ℕ} [NeZero n] (x y : Fin n → ℝ) : Prop :=
  y 0 = 0 ∧ (∀ i j : Fin n, i < j → 1 ≤ y j - y i) ∧
    ∀ i j k l : Fin n, i < j → k < l → x j - x i < x l - x k →
      1 ≤ (y l - y k) - (y j - y i)

variable {N : ℕ} [NeZero N] {D : Finset (ZMod N)}

private theorem affine_image (h : IsCyclicPDS N D) (e f : ZMod N ≃ ZMod N)
    (hf : f 0 = 0) (he : ∀ a b, e a - e b = f (a - b)) :
    IsCyclicPDS N (D.image e) := by
  refine ⟨by simpa [card_image_of_injective _ e.injective] using h.1, ?_⟩
  intro r hr
  have hn : f.symm r ≠ 0 := fun hh => hr (by rw [← f.apply_symm_apply r, hh, hf])
  obtain ⟨⟨a,b⟩, ⟨ha,hb,hab,hd⟩, hu⟩ := h.2 _ hn
  refine ⟨(e a, e b), ⟨mem_image_of_mem _ ha, mem_image_of_mem _ hb, e.injective.ne hab,
    by simp [he, hd]⟩, ?_⟩
  rintro ⟨s,t⟩ ⟨hs,ht,hst,hsub⟩
  obtain ⟨u,hu',rfl⟩ := mem_image.mp hs
  obtain ⟨v,hv,rfl⟩ := mem_image.mp ht
  have hh := hu (u,v) ⟨hu', hv, fun huv => hst (congrArg e huv),
    f.injective (by simpa [← he] using hsub)⟩
  exact congrArg (fun p : ZMod N × ZMod N => (e p.1, e p.2)) hh

theorem IsCyclicPDS.mul_unit (h : IsCyclicPDS N D) (t : (ZMod N)ˣ) :
    IsCyclicPDS N (D.image (fun a => (t : ZMod N) * a)) := by
  let e := t.mulLeft
  exact affine_image h e e (mul_zero _) (fun _ _ => (mul_sub ..).symm)

theorem IsCyclicPDS.translate (h : IsCyclicPDS N D) (c : ZMod N) :
    IsCyclicPDS N (D.image (fun a => a + c)) :=
  affine_image h (Equiv.addRight c) (Equiv.refl _) rfl (fun a b => by simp)

/-- Length of the cut starting at the residue `a`. -/
def cutSpan (D : Finset (ZMod N)) (a : ZMod N) : ℕ :=
  D.sup fun d => (d - a).val

/-- The mark following the largest gap minimizes the complementary span. -/
noncomputable def cutAnchor (D : Finset (ZMod N)) (h : D.Nonempty) : ZMod N :=
  (D.exists_min_image (cutSpan D) h).choose

omit [NeZero N] in
theorem cutAnchor_spec (h : D.Nonempty) :
    cutAnchor D h ∈ D ∧ ∀ b ∈ D, cutSpan D (cutAnchor D h) ≤ cutSpan D b :=
  (D.exists_min_image (cutSpan D) h).choose_spec

private def reps (D : Finset (ZMod N)) (a : ZMod N) :=
  D.image fun d => (d - a).val

private theorem reps_card (D : Finset (ZMod N)) (a : ZMod N) :
    (reps D a).card = D.card :=
  card_image_of_injective _ fun _ _ h => sub_left_injective ((ZMod.val_injective N) h)

/-- Increasing integer representatives of the cut starting at `a`. -/
noncomputable def cutMarks (D : Finset (ZMod N)) (a : ZMod N) : Fin D.card ↪o ℕ :=
  (reps D a).orderEmbOfFin (reps_card D a)

private theorem range_marks (a : ZMod N) :
    Set.range (cutMarks D a) = reps D a := range_orderEmbOfFin ..

private theorem marks_mem (a : ZMod N) (i : Fin D.card) :
    cutMarks D a i ∈ reps D a := orderEmbOfFin_mem ..

private theorem mark_spec (a : ZMod N) (i : Fin D.card) :
    (cutMarks D a i : ZMod N) + a ∈ D ∧ cutMarks D a i < N := by
  obtain ⟨d,hd,he⟩ := mem_image.mp (marks_mem a i)
  rw [← he]
  simpa using And.intro hd (ZMod.val_lt (d-a))

private theorem mark_index (a : ZMod N) {d : ZMod N} (hd : d ∈ D) :
    ∃ i, cutMarks D a i = (d-a).val := by
  change (d-a).val ∈ Set.range (cutMarks D a)
  rw [range_marks]
  exact mem_image_of_mem _ hd

private theorem val_sub_wrap {a b : ZMod N} (h : a.val < b.val) :
    (a-b).val = N - (b.val - a.val) := by
  have hn : b - a ≠ 0 := sub_ne_zero.mpr fun e => h.ne (congrArg ZMod.val e.symm)
  rw [← neg_sub b a, ZMod.neg_val, if_neg hn, ZMod.val_sub h.le]

private theorem pair_unique (h : IsCyclicPDS N D) {a b c d : ZMod N}
    (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hd : d ∈ D)
    (hab : a ≠ b) (he : a-b = c-d) : (a,b) = (c,d) := by
  have hn := sub_ne_zero.mpr hab
  exact (h.2 _ hn).unique ⟨ha,hb,hab,rfl⟩
    ⟨hc,hd,sub_ne_zero.mp (he ▸ hn),he.symm⟩


section Nonempty
variable [NeZero D.card]

/-- Final index, including when the number of marks is given as a cardinality. -/
def lastIndex (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, by have := NeZero.pos n; omega⟩

private theorem le_lastIndex {n : ℕ} [NeZero n] (i : Fin n) : i ≤ lastIndex n := by
  change i.val ≤ n - 1
  omega

theorem cutMarks_zero {a : ZMod N} (ha : a ∈ D) : cutMarks D a 0 = 0 := by
  obtain ⟨i,hi⟩ := mark_index a ha
  simpa [hi] using (cutMarks D a).monotone (Fin.zero_le i)

theorem cutMarks_last (a : ZMod N) :
    cutMarks D a (lastIndex D.card) = cutSpan D a := by
  apply le_antisymm
  · obtain ⟨d,hd,he⟩ := mem_image.mp (marks_mem a (lastIndex D.card))
    exact he ▸ le_sup (f := fun d => (d-a).val) hd
  · apply Finset.sup_le
    intro d hd
    obtain ⟨i,hi⟩ := mark_index a hd
    exact hi ▸ (cutMarks D a).monotone (le_lastIndex i)

omit [NeZero D.card] in
theorem cutMarks_recover (a : ZMod N) :
    univ.image (fun i => (cutMarks D a i : ZMod N) + a) = D := by
  ext d
  constructor
  · rintro hd
    obtain ⟨i,_,rfl⟩ := mem_image.mp hd
    exact (mark_spec a i).1
  · intro hd
    obtain ⟨i,hi⟩ := mark_index a hd
    exact mem_image.mpr ⟨i, mem_univ _, by simp [hi]⟩

private theorem span_bounds (h : IsCyclicPDS N D) (a : ZMod N) :
    0 < cutSpan D a ∧ cutSpan D a < N := by
  rw [← cutMarks_last]
  have hc := h.1
  have hi : (0 : Fin D.card) < lastIndex D.card := by
    change 0 < D.card - 1
    omega
  exact ⟨lt_of_le_of_lt (Nat.zero_le _) ((cutMarks D a).strictMono hi), (mark_spec ..).2⟩

/-- Distinct anchors of a perfect difference set have distinct cut lengths. -/
theorem cutSpan_injective (h : IsCyclicPDS N D) {a b : ZMod N} (ha : a ∈ D) (hb : b ∈ D)
    (he : cutSpan D a = cutSpan D b) : a = b := by
  have ea := (mark_spec (D := D) a (lastIndex D.card)).1
  have eb := (mark_spec (D := D) b (lastIndex D.card)).1
  rw [cutMarks_last] at ea eb
  have hs := span_bounds h a
  have hn : (cutSpan D a : ZMod N) ≠ 0 := by
    intro hh
    have := congrArg ZMod.val hh
    simp [ZMod.val_natCast_of_lt hs.2, hs.1.ne'] at this
  have hh := pair_unique h ea ha eb hb (by simpa using hn) (by simp [he])
  exact congrArg Prod.snd hh

/-- Each retained clockwise gap is strictly shorter than the omitted gap. -/
theorem cutMarks_gap_lt (h : IsCyclicPDS N D) (hne : D.Nonempty)
    (i j : Fin D.card) (hij : j.val = i.val + 1) :
    let a := cutAnchor D hne
    cutMarks D a j - cutMarks D a i < N - cutSpan D a := by
  let a := cutAnchor D hne
  let m := cutMarks D a
  let b := (m j : ZMod N) + a
  change m j - m i < N - cutSpan D a
  have ha := cutAnchor_spec hne
  have hb : b ∈ D := (mark_spec a j).1
  have hlt : i < j := Fin.mk_lt_mk.mpr (by omega)
  have hm := m.strictMono hlt
  have hab : a ≠ b := by
    intro hh
    have hz : (m j : ZMod N) = 0 := by simpa [b] using hh.symm
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (mark_spec a j).2, ZMod.val_zero] at hv
    change m j = 0 at hv
    omega
  have hstrict : cutSpan D a < cutSpan D b :=
    lt_of_le_of_ne (ha.2 b hb) (fun e => hab (cutSpan_injective h ha.1 hb e))
  have hbound : cutSpan D b ≤ N - (m j - m i) := by
    apply Finset.sup_le
    intro d hd
    obtain ⟨k,hk⟩ := mark_index a hd
    change m k = _ at hk
    have hv : ((m j : ZMod N)).val = m j := ZMod.val_natCast_of_lt (mark_spec a j).2
    have hid : d-b = (d-a) - (m j : ZMod N) := by simp [b, sub_sub, add_comm]
    rw [hid]
    by_cases hjk : j ≤ k
    · have hle := m.monotone hjk
      rw [ZMod.val_sub (by rw [hv, ← hk]; exact hle), hv, ← hk]
      have := (mark_spec a k).2
      change m k < N at this
      omega
    · have hki : k ≤ i := Fin.mk_le_mk.mpr (by change ¬ j.val ≤ k.val at hjk; omega)
      have hle := m.monotone hki
      have hsm : (d-a).val < (m j : ZMod N).val := by
        rw [hv, ← hk]
        exact lt_of_le_of_lt hle hm
      rw [val_sub_wrap hsm, hv, ← hk]
      change N - (m j - m k) ≤ N - (m j - m i)
      omega
  have hjN : m j < N := (mark_spec a j).2
  omega

end Nonempty


private theorem small_difference [NeZero D.card] (h : IsCyclicPDS N D) (a : ZMod N)
    {r : ℕ} (hr : 0 < r) (hg : r < N - cutSpan D a) :
    ∃ i j, i < j ∧ cutMarks D a j - cutMarks D a i = r := by
  have hrN : r < N := by omega
  have hv : (r : ZMod N).val = r := ZMod.val_natCast_of_lt hrN
  have hn : (r : ZMod N) ≠ 0 := fun z => hr.ne' (by rw [← hv, z, ZMod.val_zero])
  obtain ⟨⟨d,e⟩,⟨hd,he,_,hde⟩,_⟩ := h.2 _ hn
  obtain ⟨j,hj⟩ := mark_index a hd
  obtain ⟨i,hi⟩ := mark_index a he
  change d - e = _ at hde
  have hv' : ((d-a) - (e-a)).val = r := by simpa [hde] using hv
  by_cases hle : (e-a).val ≤ (d-a).val
  · rw [ZMod.val_sub hle, ← hi, ← hj] at hv'
    exact ⟨i,j,(cutMarks D a).lt_iff_lt.mp (by omega),hv'⟩
  · rw [val_sub_wrap (lt_of_not_ge hle), ← hi, ← hj] at hv'
    have hs := (cutMarks D a).monotone (le_lastIndex i)
    rw [cutMarks_last] at hs
    omega

private theorem difference_injective (h : IsCyclicPDS N D) (a : ZMod N)
    {i j k l : Fin D.card} (hij : i < j) (hkl : k < l)
    (he : cutMarks D a j - cutMarks D a i = cutMarks D a l - cutMarks D a k) :
    (i,j) = (k,l) := by
  let m := cutMarks D a
  let d (s : Fin D.card) := (m s : ZMod N) + a
  have hinj : Function.Injective d := by
    intro u v huv
    apply m.injective
    have hh : (m u : ZMod N) = (m v : ZMod N) := add_right_cancel huv
    have hu : (m u : ZMod N).val = m u := ZMod.val_natCast_of_lt (mark_spec a u).2
    have hv : (m v : ZMod N).val = m v := ZMod.val_natCast_of_lt (mark_spec a v).2
    simpa only [hu, hv] using congrArg ZMod.val hh
  have hcast := congrArg (fun t : ℕ => (t : ZMod N)) he
  simp only [Nat.cast_sub ((cutMarks D a).monotone hij.le),
    Nat.cast_sub ((cutMarks D a).monotone hkl.le)] at hcast
  have hp := pair_unique h (mark_spec a j).1 (mark_spec a i).1
    (mark_spec a l).1 (mark_spec a k).1 (hinj.ne hij.ne')
    (by simpa only [add_sub_add_right_eq_sub] using hcast)
  exact Prod.ext (hinj (congrArg Prod.snd hp)) (hinj (congrArg Prod.fst hp))

/-- Real mark coordinates of the canonical largest-gap cut. -/
noncomputable def largestGapCut (D : Finset (ZMod N)) (hne : D.Nonempty) (i : Fin D.card) : ℝ :=
  cutMarks D (cutAnchor D hne) i

/-- Length of the omitted clockwise gap. -/
noncomputable def largestGap (D : Finset (ZMod N)) (hne : D.Nonempty) : ℕ :=
  N - cutSpan D (cutAnchor D hne)

private theorem cast_difference (a : ZMod N) {i j : Fin D.card} (hij : i < j) :
    ((cutMarks D a j - cutMarks D a i : ℕ) : ℝ) = cutMarks D a j - cutMarks D a i :=
  Nat.cast_sub ((cutMarks D a).monotone hij.le)

private theorem cut_feasible [NeZero D.card] (h : IsCyclicPDS N D) (hne : D.Nonempty) :
    let x := largestGapCut D hne
    IsRealGolomb x ∧ InChamber x x := by
  let a := cutAnchor D hne
  let m := cutMarks D a
  let x := largestGapCut D hne
  have hm : StrictMono x := fun _ _ hij => Nat.cast_lt.mpr (m.strictMono hij)
  have hz : x 0 = 0 := by simp [x, largestGapCut, cutMarks_zero (cutAnchor_spec hne).1]
  have hu (i j : Fin D.card) (hij : i < j) : 1 ≤ x j - x i := by
    rw [show x j - x i = ((m j - m i : ℕ) : ℝ) from (cast_difference a hij).symm]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.sub_pos_of_lt (m.strictMono hij)).ne'
  have hsep (i j k l : Fin D.card) (hij : i < j) (hkl : k < l)
      (hc : x j - x i < x l - x k) : 1 ≤ (x l - x k) - (x j - x i) := by
    change (m j : ℝ) - m i < (m l : ℝ) - m k at hc
    change 1 ≤ ((m l : ℝ) - m k) - ((m j : ℝ) - m i)
    rw [← cast_difference a hij, ← cast_difference a hkl] at hc ⊢
    have hh := Nat.succ_le_of_lt (Nat.cast_lt.mp hc)
    apply (le_sub_iff_add_le').mpr
    exact_mod_cast hh
  refine ⟨⟨hz,hm,hu,?_⟩,hz,hu,hsep⟩
  intro i j k l hij hkl hn
  have hne' : x j - x i ≠ x l - x k := by
    intro he
    change (cutMarks D a j : ℝ) - cutMarks D a i = (cutMarks D a l : ℝ) - cutMarks D a k at he
    rw [← cast_difference a hij, ← cast_difference a hkl] at he
    exact hn (difference_injective h a hij hkl (Nat.cast_inj.mp he))
  rcases lt_or_gt_of_ne hne' with hh | hh
  · rw [abs_of_neg (sub_neg.mpr hh)]
    linarith [hsep i j k l hij hkl hh]
  · rw [abs_of_pos (sub_pos.mpr hh)]
    exact hsep k l i j hkl hij hh


/-- The chamber inequalities force a difference of integer length `r < G`
to be at least `r` throughout the chamber. -/
private theorem chamber_prefix [NeZero D.card] (h : IsCyclicPDS N D) (hne : D.Nonempty)
    {y : Fin D.card → ℝ} (hy : InChamber (largestGapCut D hne) y) (r : ℕ)
    (hr : 0 < r) (hg : r < largestGap D hne) (i j : Fin D.card) (hij : i < j)
    (he : largestGapCut D hne j - largestGapCut D hne i = r) : (r : ℝ) ≤ y j - y i := by
  induction r generalizing i j with
  | zero => omega
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hp
    · simpa using hy.2.1 i j hij
    · obtain ⟨k,l,hkl,hd⟩ := small_difference h (cutAnchor D hne) hp (Nat.lt_of_succ_lt hg)
      have he' : largestGapCut D hne l - largestGapCut D hne k = r :=
        (cast_difference _ hkl).symm.trans (congrArg Nat.cast hd)
      have hb := ih hp (Nat.lt_of_succ_lt hg) k l hkl he'
      have hc := hy.2.2 k l i j hkl hij (by rw [he', he]; simp)
      push_cast
      linarith

private theorem monotone_of_adjacent {n : ℕ} (f : Fin n → ℝ)
    (h : ∀ i j : Fin n, j.val = i.val + 1 → f i ≤ f j) : Monotone f := by
  cases n with
  | zero => intro i; exact i.elim0
  | succ n => exact Fin.monotone_iff_le_succ.mpr (fun i => h i.castSucc i.succ rfl)

/-- For the cut after the unique largest cyclic gap, every successive gap
is minimized at the integer ruler. Equality of total lengths forces equality
of all marks. The anchor and integer representatives are given by `cutAnchor`
and `cutMarks`; `cutMarks_recover` translates them back to the original set. -/
theorem pds_largest_gap_unique_shortest (_hN : 2 ≤ N) (h : IsCyclicPDS N D) :
    letI : NeZero D.card := ⟨by have := h.1; omega⟩
    let hne : D.Nonempty := card_pos.mp (NeZero.pos D.card)
    let x := largestGapCut D hne
    IsRealGolomb x ∧ InChamber x x ∧
      x (lastIndex D.card) = ((N - largestGap D hne : ℕ) : ℝ) ∧
      ∀ y : Fin D.card → ℝ, InChamber x y →
        (∀ i : Fin (D.card - 1),
          x ⟨i.val + 1, by omega⟩ - x ⟨i.val, by omega⟩ ≤
          y ⟨i.val + 1, by omega⟩ - y ⟨i.val, by omega⟩) ∧
        x (lastIndex D.card) ≤ y (lastIndex D.card) ∧
        (y (lastIndex D.card) = x (lastIndex D.card) → y = x) := by
  dsimp only
  let : NeZero D.card := ⟨by have := h.1; omega⟩
  let hne := card_pos.mp (NeZero.pos D.card)
  let a := cutAnchor D hne
  let x := largestGapCut D hne
  have hf := cut_feasible h hne
  refine ⟨hf.1,hf.2,?_,?_⟩
  · simp only [largestGapCut, cutMarks_last, largestGap]
    congr 1
    have := (span_bounds h a).2
    change cutSpan D a = N - (N - cutSpan D a)
    omega
  intro y hy
  have hg (i j : Fin D.card) (hij : j.val = i.val + 1) :
      x j - x i ≤ y j - y i := by
    have hlt : i < j := Fin.mk_lt_mk.mpr (by omega)
    have he := cast_difference (D := D) a hlt
    change _ = x j - x i at he
    rw [← he]
    exact chamber_prefix h hne hy _ (Nat.sub_pos_of_lt ((cutMarks D a).strictMono hlt))
      (cutMarks_gap_lt h hne i j hij) i j hlt he.symm
  have hm := monotone_of_adjacent (fun i => y i - x i) fun i j hij => by
    linarith [hg i j hij]
  have hz : y 0 - x 0 = 0 := sub_eq_zero.mpr (hy.1.trans hf.1.1.symm)
  have hlo (i : Fin D.card) : 0 ≤ y i - x i := hz ▸ hm (Fin.zero_le i)
  refine ⟨fun i => hg _ _ rfl, sub_nonneg.mp (hlo _), ?_⟩
  intro he
  funext i
  have hup := hm (le_lastIndex i)
  change y i - x i ≤ y _ - x _ at hup
  change y _ = x _ at he
  rw [he, sub_self] at hup
  exact sub_eq_zero.mp (le_antisymm hup (hlo i))


open Polynomial

/-- Writing `x = z^(q-1)` in the cubic trace equation gives Singer's
polynomial. The factor `z` accounts for the zero vector excluded from
projective space. -/
theorem singer_trace_identity {K : Type*} [Field K] (q : ℕ) (hq : 0 < q) (z : K) :
    z * ((z^(q-1))^(q+1) + z^(q-1) + 1) = z^(q^2) + z^q + z := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  simp only [Nat.succ_sub_one, ← pow_mul, mul_add, mul_one, ← pow_succ']
  congr 2
  apply congrArg (z ^ ·)
  simp only [Nat.succ_eq_add_one]
  ring

/-- The roots of the normalized trace equation are distinct norm-one elements. -/
private theorem singer_roots (K : Type*) [Field K] [IsAlgClosed K] (q : ℕ)
    (hq : 0 < q) (hchar : (q : K) = 0)
    (frob : K →+* K) (hf : ∀ x, frob x = x ^ q) :
    ∃ S : Finset K, S.card = q + 1 ∧
      (∀ x, x ∈ S ↔ x ^ (q+1) + x + 1 = 0) ∧ ∀ x ∈ S, x ^ (q^2+q+1) = 1 := by
  classical
  let P : K[X] := X ^ (q+1) + (X + C 1)
  have hdeg : P.natDegree = q + 1 := by
    unfold P
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_add_C, natDegree_X_pow]
    omega
  have hn : P ≠ 0 := fun e => by simp [e] at hdeg
  have hsep : P.Separable := by
    have hd : derivative P = X ^ q + 1 := by
      simp [P, hchar]
    refine ⟨1, -X, ?_⟩
    rw [hd]
    simp [P, pow_succ]
    ring
  let S := P.roots.toFinset
  have hmem (x : K) : x ∈ S ↔ x ^ (q+1) + x + 1 = 0 := by
    change x ∈ P.roots.toFinset ↔ _
    rw [Multiset.mem_toFinset, mem_roots hn]
    simp [IsRoot, P, add_assoc]
  refine ⟨S,?_,hmem,?_⟩
  · rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep),
        ← (IsAlgClosed.splits P).natDegree_eq_card_roots, hdeg]
  · intro x hx
    have he := (hmem x).mp hx
    have hh := congrArg frob he
    simp only [map_add, map_pow, map_one, map_zero] at hh
    rw [hf, ← pow_mul, Nat.mul_comm q (q+1)] at hh
    rw [show q^2 + q + 1 = (q+1)*q + 1 by ring, pow_succ]
    rw [pow_succ x q] at he
    linear_combination x * hh - he

/-- A nonidentity ratio can occur for at most one ordered pair of roots.
Subtracting the two polynomial equations gives a linear equation for the
denominator of the ratio. -/
private theorem singer_ratio_unique {K : Type*} [Field K] {q : ℕ} {u x y : K}
    (hu : u ≠ 1) (hx : x^q + x + 1 = 0) (hy : y^q + y + 1 = 0)
    (hux : (u*x)^q + u*x + 1 = 0) (huy : (u*y)^q + u*y + 1 = 0) : x = y := by
  rw [mul_pow] at hux huy
  have hlin : (u-u^q)*x + (1-u^q) = 0 := by linear_combination hux - u^q * hx
  have hc : u-u^q ≠ 0 := by
    intro e
    rw [e, zero_mul, zero_add] at hlin
    exact hu ((sub_eq_zero.mp e).trans (sub_eq_zero.mp hlin).symm)
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show (u-u^q)*(x-y) = 0 from by
    linear_combination hlin - huy + u^q * hy)).resolve_left hc

private theorem pds_of_count {q : ℕ} (hq : 0 < q) {S : Finset (ZMod (q^2+q+1))}
    (hs : S.card = q+1)
    (hinj : Set.InjOn (fun p : ZMod (q^2+q+1) × ZMod (q^2+q+1) => p.1-p.2) S.offDiag) :
    IsCyclicPDS (q^2+q+1) S := by
  classical
  let diff (p : ZMod (q^2+q+1) × ZMod (q^2+q+1)) := p.1 - p.2
  have hall : S.offDiag.image diff = univ.erase 0 := by
    apply eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hr
      exact mem_erase.mpr ⟨sub_ne_zero.mpr (mem_offDiag.mp hp).2.2, mem_univ _⟩
    · rw [card_image_of_injOn hinj, offDiag_card, hs, card_erase_of_mem (mem_univ _),
        card_univ, ZMod.card]
      simp [pow_two, Nat.add_mul, Nat.mul_add, Nat.add_assoc]
      omega
  refine ⟨by omega, fun r hr => ?_⟩
  have hm : r ∈ S.offDiag.image diff := hall ▸ mem_erase.mpr ⟨hr,mem_univ _⟩
  obtain ⟨p,hp,hpr⟩ := mem_image.mp hm
  obtain ⟨ha,hb,hne⟩ := mem_offDiag.mp hp
  exact ⟨p,⟨ha,hb,hne,hpr⟩,fun s ⟨hs₁,hs₂,hs₃,hs₄⟩ =>
    hinj (mem_offDiag.mpr ⟨hs₁,hs₂,hs₃⟩) hp (hs₄.trans hpr.symm)⟩

/-- Singer's cyclic perfect difference set for every prime power `q`. -/
theorem singer_pds_exists (q : ℕ) (hq : IsPrimePow q) :
    ∃ D : Finset (ZMod (q^2+q+1)), IsCyclicPDS (q^2+q+1) D ∧ D.card = q+1 := by
  classical
  obtain ⟨p,k,hp,hk,hpk⟩ := (isPrimePow_nat_iff q).mp hq
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  have hchar : (q : K) = 0 := by
    rw [← hpk, Nat.cast_pow, CharP.cast_eq_zero K p, zero_pow hk.ne']
  let N := q^2+q+1
  have : NeZero (N : K) := ⟨by simp [N, hchar]⟩
  obtain ⟨g,hg⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K N
  let t (i : ZMod N) := g ^ i.val
  have ht : Function.Injective t := fun i j he =>
    ZMod.val_injective N (hg.pow_inj i.val_lt j.val_lt he)
  have hadd (i j : ZMod N) : t (i+j) = t i * t j := by
    dsimp [t]
    rw [ZMod.val_add, ← pow_add]
    simpa only [← hg.eq_orderOf] using pow_mod_orderOf g (i.val + j.val)
  obtain ⟨S,hS,hmem,hord⟩ := singer_roots K q (by have := hq.one_lt; omega)
    hchar (iterateFrobenius K p k) (by simp [iterateFrobenius_def, hpk])
  let D := univ.filter (fun i : ZMod N => t i ∈ S)
  have him : D.image t = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hi).2
    · intro hx
      obtain ⟨i,hi,he⟩ := hg.eq_pow_of_pow_eq_one (hord x hx)
      have hti : t (i : ZMod N) = x := by simpa [t, ZMod.val_natCast_of_lt hi] using he
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _, hti ▸ hx⟩,hti⟩
  have hcard : D.card = q + 1 := by rwa [← him, card_image_of_injective _ ht] at hS
  refine ⟨D,pds_of_count (by have := hq.one_lt; omega) hcard ?_,hcard⟩
  rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
  obtain ⟨ha,hb,hab'⟩ := mem_offDiag.mp hab
  obtain ⟨hc,hd,_⟩ := mem_offDiag.mp hcd
  change a - b = c - d at he
  let r := a - b
  have hr : r ≠ 0 := sub_ne_zero.mpr hab'
  have hu : t r ≠ 1 := fun hh => hr (ht (show t r = t 0 by simpa [t] using hh))
  have root (i : ZMod N) (hi : i ∈ D) := (hmem (t i)).mp (mem_filter.mp hi).2
  have ha' : r + b = a := sub_add_cancel a b
  have hc' : r + d = c := by change (a-b)+d = c; rw [he, sub_add_cancel]
  have hbd : b = d := ht (singer_ratio_unique hu (root b hb) (root d hd)
    (by simpa only [← hadd, ha'] using root a ha)
    (by simpa only [← hadd, hc'] using root c hc))
  exact Prod.ext (ha'.symm.trans ((congrArg (r + ·) hbd).trans hc')) hbd

end SingerGolombChamber

#print axioms SingerGolombChamber.IsCyclicPDS.mul_unit
#print axioms SingerGolombChamber.IsCyclicPDS.translate
#print axioms SingerGolombChamber.cutAnchor_spec
#print axioms SingerGolombChamber.cutMarks_zero
#print axioms SingerGolombChamber.cutMarks_last
#print axioms SingerGolombChamber.cutMarks_gap_lt
#print axioms SingerGolombChamber.cutSpan_injective
#print axioms SingerGolombChamber.cutMarks_recover
#print axioms SingerGolombChamber.pds_largest_gap_unique_shortest
#print axioms SingerGolombChamber.singer_trace_identity
#print axioms SingerGolombChamber.singer_pds_exists

