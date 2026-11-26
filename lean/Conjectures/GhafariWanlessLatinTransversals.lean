import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Conjectures.GhafariWanlessData
import Conjectures.GhafariWanlessCore
import Conjectures.GhafariWanlessTailBase
import Conjectures.GhafariWanlessEvenTail
import Conjectures.GhafariWanlessOddTail

/-!
# Complete Proof of Conjecture 3 (Wormald's Question) of Ghafari & Wanless (`arXiv:2607.17547v1`)

This file proves:
- `ghafari_wanless_all_even_ge_22_ne_24`: For every even integer $n \ge 22$ with $n \ne 24$,
  there exists a Latin square of order $n$ with no two disjoint transversals and no pinned entry.
- `ghafari_wanless_conjecture3`: For every even integer $n \ge 28$, there exists a Latin square
  of order $n$ with no two disjoint transversals and no pinned entry (settling Conjecture 3 of
  Ghafari & Wanless, `arXiv:2607.17547v1`, including $n = 30$ and all even $n > 10\,000$).

All proofs use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) with zero
`sorry` and zero `native_decide`.
-/

namespace GhafariWanless

open GhafariWanless.Data

/-! ## Section 4A: Small Witnesses, Base Witnesses, and Universal Gluing -/

/-- Check a `SmallWitnessData` record in `O(n)` inverse lookups. -/
def checkSmallWitness (w : SmallWitnessData) : Bool :=
  allLt w.n fun r =>
    let c0 := w.t0.getD r w.n
    let c1 := w.t1.getD r w.n
    let c2 := w.t2.getD r w.n
    (c0 < w.n) && (c1 < w.n) && (c2 < w.n) &&
    (w.c0.getD c0 w.n == r) && (w.c1.getD c1 w.n == r) && (w.c2.getD c2 w.n == r) &&
    (w.s0.getD (modEntryVal w.n w.n r c0) w.n == r) &&
    (w.s1.getD (modEntryVal w.n w.n r c1) w.n == r) &&
    (w.s2.getD (modEntryVal w.n w.n r c2) w.n == r) &&
    !(c0 == c1 && c1 == c2)

/-- Soundness of `checkSmallWitness`: yields `HasNoPinnedEntry` for `modLatinSquare w.n w.n`. -/
theorem smallWitness_no_pinned (w : SmallWitnessData)
    (hn : 22 ≤ w.n) (hne24 : w.n ≠ 24) (heven : w.n % 2 = 0)
    (hchk : checkSmallWitness w = true) :
    HasNoPinnedEntry (modLatinSquare w.n w.n hn hne24 heven le_rfl (by simp)) := by
  have hall := allLt_true hchk
  have hrow : ∀ r < w.n,
      let c0 := w.t0.getD r w.n
      let c1 := w.t1.getD r w.n
      let c2 := w.t2.getD r w.n
      c0 < w.n ∧ c1 < w.n ∧ c2 < w.n ∧
      w.c0.getD c0 w.n = r ∧ w.c1.getD c1 w.n = r ∧ w.c2.getD c2 w.n = r ∧
      w.s0.getD (modEntryVal w.n w.n r c0) w.n = r ∧
      w.s1.getD (modEntryVal w.n w.n r c1) w.n = r ∧
      w.s2.getD (modEntryVal w.n w.n r c2) w.n = r ∧
      ¬ (c0 = c1 ∧ c1 = c2) := by
    intro r hr
    have h := hall r hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_true_eq, beq_iff_eq, beq_eq_false_iff_ne] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
    rintro ⟨e1, e2⟩
    rcases h10 with hne | hne
    · exact hne e1
    · exact hne e2
  let L := modLatinSquare w.n w.n hn hne24 heven le_rfl (by simp)
  let T0 : Fin w.n → Fin w.n := fun r => ⟨w.t0.getD r.val w.n, (hrow r.val r.isLt).1⟩
  let T1 : Fin w.n → Fin w.n := fun r => ⟨w.t1.getD r.val w.n, (hrow r.val r.isLt).2.1⟩
  let T2 : Fin w.n → Fin w.n := fun r => ⟨w.t2.getD r.val w.n, (hrow r.val r.isLt).2.2.1⟩
  have hT0 : IsTransversal L T0 := by
    refine ⟨(Finite.injective_iff_bijective).mp ?_, (Finite.injective_iff_bijective).mp ?_⟩
    · intro a b hab; apply Fin.ext
      have h1 := (hrow a.val a.isLt).2.2.2.1
      have h2 := (hrow b.val b.isLt).2.2.2.1
      have hv : w.t0.getD a.val w.n = w.t0.getD b.val w.n := congrArg Fin.val hab
      rw [← h1, ← h2, hv]
    · intro a b hab; apply Fin.ext
      have h1 := (hrow a.val a.isLt).2.2.2.2.2.2.1
      have h2 := (hrow b.val b.isLt).2.2.2.2.2.2.1
      have hv : modEntryVal w.n w.n a.val (w.t0.getD a.val w.n) =
                modEntryVal w.n w.n b.val (w.t0.getD b.val w.n) := congrArg Fin.val hab
      rw [← h1, ← h2, hv]
  have hT1 : IsTransversal L T1 := by
    refine ⟨(Finite.injective_iff_bijective).mp ?_, (Finite.injective_iff_bijective).mp ?_⟩
    · intro a b hab; apply Fin.ext
      have h1 := (hrow a.val a.isLt).2.2.2.2.1
      have h2 := (hrow b.val b.isLt).2.2.2.2.1
      have hv : w.t1.getD a.val w.n = w.t1.getD b.val w.n := congrArg Fin.val hab
      rw [← h1, ← h2, hv]
    · intro a b hab; apply Fin.ext
      have h1 := (hrow a.val a.isLt).2.2.2.2.2.2.2.1
      have h2 := (hrow b.val b.isLt).2.2.2.2.2.2.2.1
      have hv : modEntryVal w.n w.n a.val (w.t1.getD a.val w.n) =
                modEntryVal w.n w.n b.val (w.t1.getD b.val w.n) := congrArg Fin.val hab
      rw [← h1, ← h2, hv]
  have hT2 : IsTransversal L T2 := by
    refine ⟨(Finite.injective_iff_bijective).mp ?_, (Finite.injective_iff_bijective).mp ?_⟩
    · intro a b hab; apply Fin.ext
      have h1 := (hrow a.val a.isLt).2.2.2.2.2.1
      have h2 := (hrow b.val b.isLt).2.2.2.2.2.1
      have hv : w.t2.getD a.val w.n = w.t2.getD b.val w.n := congrArg Fin.val hab
      rw [← h1, ← h2, hv]
    · intro a b hab; apply Fin.ext
      have h1 := (hrow a.val a.isLt).2.2.2.2.2.2.2.2.1
      have h2 := (hrow b.val b.isLt).2.2.2.2.2.2.2.2.1
      have hv : modEntryVal w.n w.n a.val (w.t2.getD a.val w.n) =
                modEntryVal w.n w.n b.val (w.t2.getD b.val w.n) := congrArg Fin.val hab
      rw [← h1, ← h2, hv]
  refine no_pinned_of_three_transversals hT0 hT1 hT2 ?_
  intro r ⟨e1, e2⟩
  exact (hrow r.val r.isLt).2.2.2.2.2.2.2.2.2 ⟨congrArg Fin.val e1, congrArg Fin.val e2⟩

/-- Full existence theorem from any verified `SmallWitnessData` record. -/
private theorem exists_from_small (w : SmallWitnessData)
    (hn : 22 ≤ w.n) (hne24 : w.n ≠ 24) (heven : w.n % 2 = 0)
    (hchk : checkSmallWitness w = true) :
    ∃ L : LatinSquare w.n,
      (∀ T₁ T₂, IsTransversal L T₁ → IsTransversal L T₂ → ¬ DisjointTransversals T₁ T₂) ∧
      HasNoPinnedEntry L :=
  ⟨modLatinSquare w.n w.n hn hne24 heven le_rfl (by simp),
   modLatinSquare_no_disjoint w.n w.n hn hne24 heven le_rfl (by simp),
   smallWitness_no_pinned w hn hne24 heven hchk⟩

/-- Check a `BaseWitnessData` record: three unwrapped `[n0/2, 3n0/2)` transversals with empty
triple intersection. -/
def checkBaseWitness (w : BaseWitnessData) : Bool :=
  let h := w.n0 / 2
  (2 * h == w.n0) &&
  allLt w.n0 fun r =>
    let c0 := w.t0.getD r w.n0
    let c1 := w.t1.getD r w.n0
    let c2 := w.t2.getD r w.n0
    let s0 : ℤ := (r : ℤ) + (c0 : ℤ) + deltaMod w.n0 r c0
    let s1 : ℤ := (r : ℤ) + (c1 : ℤ) + deltaMod w.n0 r c1
    let s2 : ℤ := (r : ℤ) + (c2 : ℤ) + deltaMod w.n0 r c2
    (c0 < w.n0) && (c1 < w.n0) && (c2 < w.n0) &&
    (w.c0.getD c0 w.n0 == r) && (w.c1.getD c1 w.n0 == r) && (w.c2.getD c2 w.n0 == r) &&
    ((h : ℤ) ≤ s0) && (s0 < (3 * h : ℤ)) && (w.s0.getD (s0 - (h : ℤ)).toNat w.n0 == r) &&
    ((h : ℤ) ≤ s1) && (s1 < (3 * h : ℤ)) && (w.s1.getD (s1 - (h : ℤ)).toNat w.n0 == r) &&
    ((h : ℤ) ≤ s2) && (s2 < (3 * h : ℤ)) && (w.s2.getD (s2 - (h : ℤ)).toNat w.n0 == r) &&
    !(c0 == c1 && c1 == c2)

/-- Valid base transversal package for gluing with an arbitrary tail. -/
structure ValidBase (h : ℕ) where
  b0 : ℕ → ℕ
  b1 : ℕ → ℕ
  b2 : ℕ → ℕ
  lt0 : ∀ r < 2 * h, b0 r < 2 * h
  lt1 : ∀ r < 2 * h, b1 r < 2 * h
  lt2 : ∀ r < 2 * h, b2 r < 2 * h
  inj0 : ∀ r₁ < 2 * h, ∀ r₂ < 2 * h, b0 r₁ = b0 r₂ → r₁ = r₂
  inj1 : ∀ r₁ < 2 * h, ∀ r₂ < 2 * h, b1 r₁ = b1 r₂ → r₁ = r₂
  inj2 : ∀ r₁ < 2 * h, ∀ r₂ < 2 * h, b2 r₁ = b2 r₂ → r₁ = r₂
  sym_lo0 : ∀ r < 2 * h, (h : ℤ) ≤ (r : ℤ) + (b0 r : ℤ) + deltaMod (2 * h) r (b0 r)
  sym_hi0 : ∀ r < 2 * h, (r : ℤ) + (b0 r : ℤ) + deltaMod (2 * h) r (b0 r) < (3 * h : ℤ)
  sym_inj0 : ∀ r₁ < 2 * h, ∀ r₂ < 2 * h,
    (r₁ : ℤ) + (b0 r₁ : ℤ) + deltaMod (2 * h) r₁ (b0 r₁) =
    (r₂ : ℤ) + (b0 r₂ : ℤ) + deltaMod (2 * h) r₂ (b0 r₂) → r₁ = r₂
  sym_lo1 : ∀ r < 2 * h, (h : ℤ) ≤ (r : ℤ) + (b1 r : ℤ) + deltaMod (2 * h) r (b1 r)
  sym_hi1 : ∀ r < 2 * h, (r : ℤ) + (b1 r : ℤ) + deltaMod (2 * h) r (b1 r) < (3 * h : ℤ)
  sym_inj1 : ∀ r₁ < 2 * h, ∀ r₂ < 2 * h,
    (r₁ : ℤ) + (b1 r₁ : ℤ) + deltaMod (2 * h) r₁ (b1 r₁) =
    (r₂ : ℤ) + (b1 r₂ : ℤ) + deltaMod (2 * h) r₂ (b1 r₂) → r₁ = r₂
  sym_lo2 : ∀ r < 2 * h, (h : ℤ) ≤ (r : ℤ) + (b2 r : ℤ) + deltaMod (2 * h) r (b2 r)
  sym_hi2 : ∀ r < 2 * h, (r : ℤ) + (b2 r : ℤ) + deltaMod (2 * h) r (b2 r) < (3 * h : ℤ)
  sym_inj2 : ∀ r₁ < 2 * h, ∀ r₂ < 2 * h,
    (r₁ : ℤ) + (b2 r₁ : ℤ) + deltaMod (2 * h) r₁ (b2 r₁) =
    (r₂ : ℤ) + (b2 r₂ : ℤ) + deltaMod (2 * h) r₂ (b2 r₂) → r₁ = r₂
  no_common : ∀ r < 2 * h, ¬ (b0 r = b1 r ∧ b1 r = b2 r)

def validBase_of_check (w : BaseWitnessData) (h : ℕ) (heq : w.n0 = 2 * h)
    (hchk : checkBaseWitness w = true) : ValidBase h := by
  have hall : ∀ r < 2 * h,
      let c0 := w.t0.getD r (2 * h)
      let c1 := w.t1.getD r (2 * h)
      let c2 := w.t2.getD r (2 * h)
      let s0 : ℤ := (r : ℤ) + (c0 : ℤ) + deltaMod (2 * h) r c0
      let s1 : ℤ := (r : ℤ) + (c1 : ℤ) + deltaMod (2 * h) r c1
      let s2 : ℤ := (r : ℤ) + (c2 : ℤ) + deltaMod (2 * h) r c2
      c0 < 2 * h ∧ c1 < 2 * h ∧ c2 < 2 * h ∧
      w.c0.getD c0 (2 * h) = r ∧ w.c1.getD c1 (2 * h) = r ∧ w.c2.getD c2 (2 * h) = r ∧
      (h : ℤ) ≤ s0 ∧ s0 < (3 * h : ℤ) ∧ w.s0.getD (s0 - (h : ℤ)).toNat (2 * h) = r ∧
      (h : ℤ) ≤ s1 ∧ s1 < (3 * h : ℤ) ∧ w.s1.getD (s1 - (h : ℤ)).toNat (2 * h) = r ∧
      (h : ℤ) ≤ s2 ∧ s2 < (3 * h : ℤ) ∧ w.s2.getD (s2 - (h : ℤ)).toNat (2 * h) = r ∧
      ¬ (c0 = c1 ∧ c1 = c2) := by
    unfold checkBaseWitness at hchk
    simp only [heq, show 2 * h / 2 = h by omega, beq_self_eq_true, Bool.true_and] at hchk
    intro r hr
    have hr' := allLt_true hchk r hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_true_eq, beq_iff_eq, beq_eq_false_iff_ne] at hr'
    rcases hr' with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, ?_⟩
    rintro ⟨e1, e2⟩
    rcases h16 with hne | hne
    · exact hne e1
    · exact hne e2
  exact {
    b0 := fun r => w.t0.getD r (2 * h)
    b1 := fun r => w.t1.getD r (2 * h)
    b2 := fun r => w.t2.getD r (2 * h)
    lt0 := fun r hr => (hall r hr).1
    lt1 := fun r hr => (hall r hr).2.1
    lt2 := fun r hr => (hall r hr).2.2.1
    inj0 := fun r₁ hr₁ r₂ hr₂ he => by
      have h1 := (hall r₁ hr₁).2.2.2.1; have h2 := (hall r₂ hr₂).2.2.2.1; rw [← h1, ← h2, he]
    inj1 := fun r₁ hr₁ r₂ hr₂ he => by
      have h1 := (hall r₁ hr₁).2.2.2.2.1; have h2 := (hall r₂ hr₂).2.2.2.2.1; rw [← h1, ← h2, he]
    inj2 := fun r₁ hr₁ r₂ hr₂ he => by
      have h1 := (hall r₁ hr₁).2.2.2.2.2.1; have h2 := (hall r₂ hr₂).2.2.2.2.2.1; rw [← h1, ← h2, he]
    sym_lo0 := fun r hr => (hall r hr).2.2.2.2.2.2.1
    sym_hi0 := fun r hr => (hall r hr).2.2.2.2.2.2.2.1
    sym_inj0 := fun r₁ hr₁ r₂ hr₂ he => by
      have h1 := (hall r₁ hr₁).2.2.2.2.2.2.2.2.1
      have h2 := (hall r₂ hr₂).2.2.2.2.2.2.2.2.1
      rw [← h1, ← h2, he]
    sym_lo1 := fun r hr => (hall r hr).2.2.2.2.2.2.2.2.2.1
    sym_hi1 := fun r hr => (hall r hr).2.2.2.2.2.2.2.2.2.2.1
    sym_inj1 := fun r₁ hr₁ r₂ hr₂ he => by
      have h1 := (hall r₁ hr₁).2.2.2.2.2.2.2.2.2.2.2.1
      have h2 := (hall r₂ hr₂).2.2.2.2.2.2.2.2.2.2.2.1
      rw [← h1, ← h2, he]
    sym_lo2 := fun r hr => (hall r hr).2.2.2.2.2.2.2.2.2.2.2.2.1
    sym_hi2 := fun r hr => (hall r hr).2.2.2.2.2.2.2.2.2.2.2.2.2.1
    sym_inj2 := fun r₁ hr₁ r₂ hr₂ he => by
      have h1 := (hall r₁ hr₁).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h2 := (hall r₂ hr₂).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [← h1, ← h2, he]
    no_common := fun r hr => (hall r hr).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  }

/-- **Universal Glue Theorem:** gluing three unwrapped base transversals on `[0, 2h)` with two
disjoint valid tail transversals on `[0, 4t)` yields three transversals of `L_{2h + 4t, 2h}` with
empty triple intersection, hence `HasNoPinnedEntry`. -/
theorem glue_base_and_tail {h t : ℕ} (hh : 11 ≤ h) (hne12 : h ≠ 12) (ht : h ≤ t)
    (B : ValidBase h) (V₁ V₂ : ValidTail h t) (hdisj : ∀ i < 4 * t, V₁.col i ≠ V₂.col i) :
    HasNoPinnedEntry (modLatinSquare (2 * h + 4 * t) (2 * h) (by omega) (by omega) (by omega)
      (by omega) (by omega)) := by
  let n := 2 * h + 4 * t
  let L := modLatinSquare n (2 * h) (by omega) (by omega) (by omega) (by omega) (by omega)
  have mk_trans : ∀ (b : ℕ → ℕ)
      (hlt : ∀ r < 2 * h, b r < 2 * h)
      (hinj : ∀ r₁ < 2 * h, ∀ r₂ < 2 * h, b r₁ = b r₂ → r₁ = r₂)
      (hlo : ∀ r < 2 * h, (h : ℤ) ≤ (r : ℤ) + (b r : ℤ) + deltaMod (2 * h) r (b r))
      (hhi : ∀ r < 2 * h, (r : ℤ) + (b r : ℤ) + deltaMod (2 * h) r (b r) < (3 * h : ℤ))
      (hsinj : ∀ r₁ < 2 * h, ∀ r₂ < 2 * h,
        (r₁ : ℤ) + (b r₁ : ℤ) + deltaMod (2 * h) r₁ (b r₁) =
        (r₂ : ℤ) + (b r₂ : ℤ) + deltaMod (2 * h) r₂ (b r₂) → r₁ = r₂)
      (V : ValidTail h t),
      IsTransversal L (fun r : Fin n =>
        ⟨if r.val < 2 * h then b r.val else 2 * h + V.col (r.val - 2 * h), by
          split_ifs with hr
          · have := hlt r.val hr; omega
          · have := V.col_lt (r.val - 2 * h) (by omega); omega⟩) := by
    intro b hlt hinj hlo hhi hsinj V
    refine ⟨(Finite.injective_iff_bijective).mp ?_, (Finite.injective_iff_bijective).mp ?_⟩
    · intro r₁ r₂ heq
      have hv := congrArg Fin.val heq
      dsimp only at hv
      split_ifs at hv with h1 h2 h2
      · exact Fin.ext (hinj r₁.val h1 r₂.val h2 hv)
      · have := hlt r₁.val h1; omega
      · have := hlt r₂.val h2; omega
      · have := V.col_inj (r₁.val - 2 * h) (by omega) (r₂.val - 2 * h) (by omega) (by omega)
        exact Fin.ext (by omega)
    · have hsym_base : ∀ r < 2 * h,
          ((modEntryVal n (2 * h) r (b r) : ℕ) : ℤ) = (r : ℤ) + (b r : ℤ) + deltaMod (2 * h) r (b r) ∧
          (h : ℤ) ≤ (modEntryVal n (2 * h) r (b r) : ℤ) ∧
          (modEntryVal n (2 * h) r (b r) : ℤ) < (3 * h : ℤ) := by
        intro r hr
        have h1 := hlo r hr; have h2 := hhi r hr
        unfold modEntryVal
        rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_of_nonneg (by omega)]
        omega
      have hsym_tail : ∀ i < 4 * t,
          let s : ℤ := (i : ℤ) + (V.col i : ℤ) + tailDelta i (V.col i)
          let m : ℤ := (modEntryVal n (2 * h) (2 * h + i) (2 * h + V.col i) : ℤ)
          (m < (h : ℤ) ∨ (3 * h : ℤ) ≤ m) ∧
          (m = 4 * (h : ℤ) + s ∨ m = 4 * (h : ℤ) + s - (n : ℤ)) := by
        intro i hi; dsimp only
        unfold modEntryVal
        rw [deltaMod_tail_eq h i (V.col i) hh]
        set s : ℤ := (i : ℤ) + (V.col i : ℤ) + tailDelta i (V.col i)
        have hsum : ((2 * h + i : ℕ) : ℤ) + ((2 * h + V.col i : ℕ) : ℤ) + tailDelta i (V.col i) =
            4 * (h : ℤ) + s := by push_cast; ring
        rw [hsum]
        rcases V.sym_band i hi with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
        · by_cases hlt_n : 4 * (h : ℤ) + s < (n : ℤ)
          · rw [Int.emod_eq_of_lt (by omega) hlt_n, Int.toNat_of_nonneg (by omega)]
            exact ⟨Or.inr (by omega), Or.inl rfl⟩
          · have hmod : (4 * (h : ℤ) + s) % (n : ℤ) = 4 * (h : ℤ) + s - (n : ℤ) := by
              have h1 : 4 * (h : ℤ) + s = (n : ℤ) * 1 + (4 * (h : ℤ) + s - (n : ℤ)) := by ring
              rw [h1, Int.mul_add_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]; ring
            rw [hmod, Int.toNat_of_nonneg (by omega)]
            exact ⟨Or.inl (by omega), Or.inr rfl⟩
        · have hmod : (4 * (h : ℤ) + s) % (n : ℤ) = 4 * (h : ℤ) + s - (n : ℤ) := by
            have h1 : 4 * (h : ℤ) + s = (n : ℤ) * 1 + (4 * (h : ℤ) + s - (n : ℤ)) := by ring
            rw [h1, Int.mul_add_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]; ring
          rw [hmod, Int.toNat_of_nonneg (by omega)]
          exact ⟨Or.inr (by omega), Or.inr rfl⟩
      intro r₁ r₂ heq
      have hv : (modEntryVal n (2 * h) r₁.val (if r₁.val < 2 * h then b r₁.val else 2 * h + V.col (r₁.val - 2 * h)) : ℤ) =
                (modEntryVal n (2 * h) r₂.val (if r₂.val < 2 * h then b r₂.val else 2 * h + V.col (r₂.val - 2 * h)) : ℤ) := by
        exact_mod_cast congrArg Fin.val heq
      by_cases h1 : r₁.val < 2 * h <;> by_cases h2 : r₂.val < 2 * h
      · simp only [h1, h2, ↓reduceIte] at hv
        have hb1 := hsym_base r₁.val h1; have hb2 := hsym_base r₂.val h2
        exact Fin.ext (hsinj r₁.val h1 r₂.val h2 (by omega))
      · simp only [h1, h2, ↓reduceIte] at hv
        have hb1 := hsym_base r₁.val h1
        have ht2 := hsym_tail (r₂.val - 2 * h) (by omega)
        rw [show 2 * h + (r₂.val - 2 * h) = r₂.val by omega] at ht2
        omega
      · simp only [h1, h2, ↓reduceIte] at hv
        have ht1 := hsym_tail (r₁.val - 2 * h) (by omega)
        have hb2 := hsym_base r₂.val h2
        rw [show 2 * h + (r₁.val - 2 * h) = r₁.val by omega] at ht1
        omega
      · simp only [h1, h2, ↓reduceIte] at hv
        have ht1 := hsym_tail (r₁.val - 2 * h) (by omega)
        have ht2 := hsym_tail (r₂.val - 2 * h) (by omega)
        rw [show 2 * h + (r₁.val - 2 * h) = r₁.val by omega] at ht1
        rw [show 2 * h + (r₂.val - 2 * h) = r₂.val by omega] at ht2
        have hband1 := V.sym_band (r₁.val - 2 * h) (by omega)
        have hband2 := V.sym_band (r₂.val - 2 * h) (by omega)
        have hseq : ((r₁.val - 2 * h : ℕ) : ℤ) + (V.col (r₁.val - 2 * h) : ℤ) + tailDelta (r₁.val - 2 * h) (V.col (r₁.val - 2 * h)) =
                    ((r₂.val - 2 * h : ℕ) : ℤ) + (V.col (r₂.val - 2 * h) : ℤ) + tailDelta (r₂.val - 2 * h) (V.col (r₂.val - 2 * h)) := by
          rcases ht1.2 with e1 | e1 <;> rcases ht2.2 with e2 | e2 <;>
            rcases hband1 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases hband2 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        have hi := V.sym_inj (r₁.val - 2 * h) (by omega) (r₂.val - 2 * h) (by omega) hseq
        exact Fin.ext (by omega)
  refine no_pinned_of_three_transversals
    (mk_trans B.b0 B.lt0 B.inj0 B.sym_lo0 B.sym_hi0 B.sym_inj0 V₁)
    (mk_trans B.b1 B.lt1 B.inj1 B.sym_lo1 B.sym_hi1 B.sym_inj1 V₁)
    (mk_trans B.b2 B.lt2 B.inj2 B.sym_lo2 B.sym_hi2 B.sym_inj2 V₂) ?_
  intro r ⟨e1, e2⟩
  have hv1 := congrArg Fin.val e1; have hv2 := congrArg Fin.val e2
  dsimp only at hv1 hv2
  by_cases hr : r.val < 2 * h
  · simp only [hr, ↓reduceIte] at hv1 hv2
    exact B.no_common r.val hr ⟨hv1, hv2⟩
  · simp only [hr, ↓reduceIte] at hv1 hv2
    exact hdisj (r.val - 2 * h) (by omega) (by omega)

private theorem exists_from_glue {h t : ℕ} (hh : 11 ≤ h) (hne12 : h ≠ 12) (ht : h ≤ t)
    (B : ValidBase h) (V₁ V₂ : ValidTail h t) (hdisj : ∀ i < 4 * t, V₁.col i ≠ V₂.col i) :
    ∃ L : LatinSquare (2 * h + 4 * t),
      (∀ T₁ T₂, IsTransversal L T₁ → IsTransversal L T₂ → ¬ DisjointTransversals T₁ T₂) ∧
      HasNoPinnedEntry L :=
  ⟨modLatinSquare (2 * h + 4 * t) (2 * h) (by omega) (by omega) (by omega) (by omega) (by omega),
   modLatinSquare_no_disjoint (2 * h + 4 * t) (2 * h) (by omega) (by omega) (by omega) (by omega) (by omega),
   glue_base_and_tail hh hne12 ht B V₁ V₂ hdisj⟩

/-! ## Section 4B: Verified Base Witnesses and 42 Small Even Orders -/

private def validBase_22 : ValidBase 11 := validBase_of_check baseData_22 11 rfl (by decide)
private def validBase_26 : ValidBase 13 := validBase_of_check baseData_26 13 rfl (by decide)
private def validBase_30 : ValidBase 15 := validBase_of_check baseData_30 15 rfl (by decide)
private def validBase_32 : ValidBase 16 := validBase_of_check baseData_32 16 rfl (by decide)

private theorem small_22 : checkSmallWitness smallData_22 = true := by decide
private theorem small_26 : checkSmallWitness smallData_26 = true := by decide
private theorem small_28 : checkSmallWitness smallData_28 = true := by decide
private theorem small_30 : checkSmallWitness smallData_30 = true := by decide
private theorem small_32 : checkSmallWitness smallData_32 = true := by decide
private theorem small_34 : checkSmallWitness smallData_34 = true := by decide
private theorem small_36 : checkSmallWitness smallData_36 = true := by decide
private theorem small_38 : checkSmallWitness smallData_38 = true := by decide
private theorem small_40 : checkSmallWitness smallData_40 = true := by decide
private theorem small_42 : checkSmallWitness smallData_42 = true := by decide
private theorem small_44 : checkSmallWitness smallData_44 = true := by decide
private theorem small_46 : checkSmallWitness smallData_46 = true := by decide
private theorem small_48 : checkSmallWitness smallData_48 = true := by decide
private theorem small_50 : checkSmallWitness smallData_50 = true := by decide
private theorem small_52 : checkSmallWitness smallData_52 = true := by decide
private theorem small_54 : checkSmallWitness smallData_54 = true := by decide
private theorem small_56 : checkSmallWitness smallData_56 = true := by decide
private theorem small_58 : checkSmallWitness smallData_58 = true := by decide
private theorem small_60 : checkSmallWitness smallData_60 = true := by decide
private theorem small_62 : checkSmallWitness smallData_62 = true := by decide
private theorem small_64 : checkSmallWitness smallData_64 = true := by decide
private theorem small_66 : checkSmallWitness smallData_66 = true := by decide
private theorem small_68 : checkSmallWitness smallData_68 = true := by decide
private theorem small_70 : checkSmallWitness smallData_70 = true := by decide
private theorem small_72 : checkSmallWitness smallData_72 = true := by decide
private theorem small_74 : checkSmallWitness smallData_74 = true := by decide
private theorem small_76 : checkSmallWitness smallData_76 = true := by decide
private theorem small_78 : checkSmallWitness smallData_78 = true := by decide
private theorem small_80 : checkSmallWitness smallData_80 = true := by decide
private theorem small_82 : checkSmallWitness smallData_82 = true := by decide
private theorem small_84 : checkSmallWitness smallData_84 = true := by decide
private theorem small_86 : checkSmallWitness smallData_86 = true := by decide
private theorem small_88 : checkSmallWitness smallData_88 = true := by decide
private theorem small_90 : checkSmallWitness smallData_90 = true := by decide
private theorem small_92 : checkSmallWitness smallData_92 = true := by decide
private theorem small_94 : checkSmallWitness smallData_94 = true := by decide
private theorem small_96 : checkSmallWitness smallData_96 = true := by decide
private theorem small_98 : checkSmallWitness smallData_98 = true := by decide
private theorem small_100 : checkSmallWitness smallData_100 = true := by decide
private theorem small_104 : checkSmallWitness smallData_104 = true := by decide
private theorem small_106 : checkSmallWitness smallData_106 = true := by decide
private theorem small_110 : checkSmallWitness smallData_110 = true := by decide

/-! ## Section 4C: Main Theorems -/

/-- **Complete Classification for Even Orders `n ≥ 22, n ≠ 24`:**
For every even integer `n ≥ 22` with `n ≠ 24`, there exists a Latin square of order `n` having
no two disjoint transversals and no pinned entry. -/
theorem ghafari_wanless_all_even_ge_22_ne_24 :
    ∀ n : ℕ, 22 ≤ n → n ≠ 24 → Even n →
      ∃ L : LatinSquare n,
        (∀ T₁ T₂, IsTransversal L T₁ → IsTransversal L T₂ → ¬ DisjointTransversals T₁ T₂) ∧
        HasNoPinnedEntry L := by
  intro n hn hne24 heven
  rcases heven with ⟨m, rfl⟩
  have hm : 11 ≤ m := by omega
  have hm12 : m ≠ 12 := by omega
  have hmod : (m + m) % 16 = 0 ∨ (m + m) % 16 = 2 ∨ (m + m) % 16 = 4 ∨ (m + m) % 16 = 6 ∨
      (m + m) % 16 = 8 ∨ (m + m) % 16 = 10 ∨ (m + m) % 16 = 12 ∨ (m + m) % 16 = 14 := by omega
  rcases hmod with h0 | h2 | h4 | h6 | h8 | h10 | h12 | h14
  · -- n ≡ 0 (mod 16): small {32, 48, 64, 80, 96}, infinite n ≥ 112 via evenTail_0
    by_cases hlt : m + m < 112
    · rcases (by omega : m + m = 32 ∨ m + m = 48 ∨ m + m = 64 ∨ m + m = 80 ∨ m + m = 96) with
        e | e | e | e | e <;> rw [e]
      · exact exists_from_small smallData_32 (by decide) (by decide) (by decide) small_32
      · exact exists_from_small smallData_48 (by decide) (by decide) (by decide) small_48
      · exact exists_from_small smallData_64 (by decide) (by decide) (by decide) small_64
      · exact exists_from_small smallData_80 (by decide) (by decide) (by decide) small_80
      · exact exists_from_small smallData_96 (by decide) (by decide) (by decide) small_96
    · have hp : m + m = 2 * evenTail_0.h + 4 * (4 * ((m + m - 112) / 16) + evenTail_0.R) := by
        change m + m = 2 * 16 + 4 * (4 * ((m + m - 112) / 16) + 20); omega
      rw [hp]
      exact exists_from_glue (by decide) (by decide) (by change 16 ≤ 4 * _ + 20; omega)
        validBase_32 (evenTailValid evenTail_0 checkEvenTail_0 _ false)
        (evenTailValid evenTail_0 checkEvenTail_0 _ true)
        (evenTail_disjoint evenTail_0 checkEvenTail_0 _)
  · -- n ≡ 2 (mod 16): small {34, 50, 66, 82, 98}, infinite n ≥ 114 via oddTail_2
    by_cases hlt : m + m < 114
    · rcases (by omega : m + m = 34 ∨ m + m = 50 ∨ m + m = 66 ∨ m + m = 82 ∨ m + m = 98) with
        e | e | e | e | e <;> rw [e]
      · exact exists_from_small smallData_34 (by decide) (by decide) (by decide) small_34
      · exact exists_from_small smallData_50 (by decide) (by decide) (by decide) small_50
      · exact exists_from_small smallData_66 (by decide) (by decide) (by decide) small_66
      · exact exists_from_small smallData_82 (by decide) (by decide) (by decide) small_82
      · exact exists_from_small smallData_98 (by decide) (by decide) (by decide) small_98
    · have hq : m + m = 2 * oddTail_2.h + 4 * (4 * ((m + m - 114) / 16 + 1) + oddTail_2.R) := by
        change m + m = 2 * 13 + 4 * (4 * ((m + m - 114) / 16 + 1) + 18); omega
      rw [hq]
      exact exists_from_glue (by decide) (by decide) (by change 13 ≤ 4 * _ + 18; omega)
        validBase_26 (oddTail1Valid oddTail_2 checkOddTail_2 _)
        (oddTail2Valid oddTail_2 checkOddTail_2 _)
        (oddTail_disjoint oddTail_2 checkOddTail_2 _)
  · -- n ≡ 4 (mod 16): small {36, 52, 68, 84, 100}, infinite n ≥ 116 via evenTail_4
    by_cases hlt : m + m < 116
    · rcases (by omega : m + m = 36 ∨ m + m = 52 ∨ m + m = 68 ∨ m + m = 84 ∨ m + m = 100) with
        e | e | e | e | e <;> rw [e]
      · exact exists_from_small smallData_36 (by decide) (by decide) (by decide) small_36
      · exact exists_from_small smallData_52 (by decide) (by decide) (by decide) small_52
      · exact exists_from_small smallData_68 (by decide) (by decide) (by decide) small_68
      · exact exists_from_small smallData_84 (by decide) (by decide) (by decide) small_84
      · exact exists_from_small smallData_100 (by decide) (by decide) (by decide) small_100
    · have hp : m + m = 2 * evenTail_4.h + 4 * (4 * ((m + m - 116) / 16) + evenTail_4.R) := by
        change m + m = 2 * 16 + 4 * (4 * ((m + m - 116) / 16) + 21); omega
      rw [hp]
      exact exists_from_glue (by decide) (by decide) (by change 16 ≤ 4 * _ + 21; omega)
        validBase_32 (evenTailValid evenTail_4 checkEvenTail_4 _ false)
        (evenTailValid evenTail_4 checkEvenTail_4 _ true)
        (evenTail_disjoint evenTail_4 checkEvenTail_4 _)
  · -- n ≡ 6 (mod 16): small {22, 38, 54, 70, 86}, infinite n ≥ 102 via oddTail_6
    by_cases hlt : m + m < 102
    · rcases (by omega : m + m = 22 ∨ m + m = 38 ∨ m + m = 54 ∨ m + m = 70 ∨ m + m = 86) with
        e | e | e | e | e <;> rw [e]
      · exact exists_from_small smallData_22 (by decide) (by decide) (by decide) small_22
      · exact exists_from_small smallData_38 (by decide) (by decide) (by decide) small_38
      · exact exists_from_small smallData_54 (by decide) (by decide) (by decide) small_54
      · exact exists_from_small smallData_70 (by decide) (by decide) (by decide) small_70
      · exact exists_from_small smallData_86 (by decide) (by decide) (by decide) small_86
    · have hq : m + m = 2 * oddTail_6.h + 4 * (4 * ((m + m - 102) / 16 + 1) + oddTail_6.R) := by
        change m + m = 2 * 11 + 4 * (4 * ((m + m - 102) / 16 + 1) + 16); omega
      rw [hq]
      exact exists_from_glue (by decide) (by decide) (by change 11 ≤ 4 * _ + 16; omega)
        validBase_22 (oddTail1Valid oddTail_6 checkOddTail_6 _)
        (oddTail2Valid oddTail_6 checkOddTail_6 _)
        (oddTail_disjoint oddTail_6 checkOddTail_6 _)
  · -- n ≡ 8 (mod 16): small {40, 56, 72, 88, 104} (24 excluded), infinite n ≥ 120 via evenTail_8
    by_cases hlt : m + m < 120
    · rcases (by omega : m + m = 40 ∨ m + m = 56 ∨ m + m = 72 ∨ m + m = 88 ∨ m + m = 104) with
        e | e | e | e | e <;> rw [e]
      · exact exists_from_small smallData_40 (by decide) (by decide) (by decide) small_40
      · exact exists_from_small smallData_56 (by decide) (by decide) (by decide) small_56
      · exact exists_from_small smallData_72 (by decide) (by decide) (by decide) small_72
      · exact exists_from_small smallData_88 (by decide) (by decide) (by decide) small_88
      · exact exists_from_small smallData_104 (by decide) (by decide) (by decide) small_104
    · have hp : m + m = 2 * evenTail_8.h + 4 * (4 * ((m + m - 120) / 16) + evenTail_8.R) := by
        change m + m = 2 * 16 + 4 * (4 * ((m + m - 120) / 16) + 22); omega
      rw [hp]
      exact exists_from_glue (by decide) (by decide) (by change 16 ≤ 4 * _ + 22; omega)
        validBase_32 (evenTailValid evenTail_8 checkEvenTail_8 _ false)
        (evenTailValid evenTail_8 checkEvenTail_8 _ true)
        (evenTail_disjoint evenTail_8 checkEvenTail_8 _)
  · -- n ≡ 10 (mod 16): small {26, 42, 58, 74, 90, 106}, infinite n ≥ 122 via oddTail_10
    by_cases hlt : m + m < 122
    · rcases (by omega : m + m = 26 ∨ m + m = 42 ∨ m + m = 58 ∨ m + m = 74 ∨ m + m = 90 ∨ m + m = 106) with
        e | e | e | e | e | e <;> rw [e]
      · exact exists_from_small smallData_26 (by decide) (by decide) (by decide) small_26
      · exact exists_from_small smallData_42 (by decide) (by decide) (by decide) small_42
      · exact exists_from_small smallData_58 (by decide) (by decide) (by decide) small_58
      · exact exists_from_small smallData_74 (by decide) (by decide) (by decide) small_74
      · exact exists_from_small smallData_90 (by decide) (by decide) (by decide) small_90
      · exact exists_from_small smallData_106 (by decide) (by decide) (by decide) small_106
    · have hq : m + m = 2 * oddTail_10.h + 4 * (4 * ((m + m - 122) / 16 + 1) + oddTail_10.R) := by
        change m + m = 2 * 13 + 4 * (4 * ((m + m - 122) / 16 + 1) + 20); omega
      rw [hq]
      exact exists_from_glue (by decide) (by decide) (by change 13 ≤ 4 * _ + 20; omega)
        validBase_26 (oddTail1Valid oddTail_10 checkOddTail_10 _)
        (oddTail2Valid oddTail_10 checkOddTail_10 _)
        (oddTail_disjoint oddTail_10 checkOddTail_10 _)
  · -- n ≡ 12 (mod 16): small {28, 44, 60, 76, 92}, infinite n ≥ 108 via evenTail_12
    by_cases hlt : m + m < 108
    · rcases (by omega : m + m = 28 ∨ m + m = 44 ∨ m + m = 60 ∨ m + m = 76 ∨ m + m = 92) with
        e | e | e | e | e <;> rw [e]
      · exact exists_from_small smallData_28 (by decide) (by decide) (by decide) small_28
      · exact exists_from_small smallData_44 (by decide) (by decide) (by decide) small_44
      · exact exists_from_small smallData_60 (by decide) (by decide) (by decide) small_60
      · exact exists_from_small smallData_76 (by decide) (by decide) (by decide) small_76
      · exact exists_from_small smallData_92 (by decide) (by decide) (by decide) small_92
    · have hp : m + m = 2 * evenTail_12.h + 4 * (4 * ((m + m - 108) / 16) + evenTail_12.R) := by
        change m + m = 2 * 16 + 4 * (4 * ((m + m - 108) / 16) + 19); omega
      rw [hp]
      exact exists_from_glue (by decide) (by decide) (by change 16 ≤ 4 * _ + 19; omega)
        validBase_32 (evenTailValid evenTail_12 checkEvenTail_12 _ false)
        (evenTailValid evenTail_12 checkEvenTail_12 _ true)
        (evenTail_disjoint evenTail_12 checkEvenTail_12 _)
  · -- n ≡ 14 (mod 16): small {30, 46, 62, 78, 94, 110}, infinite n ≥ 126 via oddTail_14
    by_cases hlt : m + m < 126
    · rcases (by omega : m + m = 30 ∨ m + m = 46 ∨ m + m = 62 ∨ m + m = 78 ∨ m + m = 94 ∨ m + m = 110) with
        e | e | e | e | e | e <;> rw [e]
      · exact exists_from_small smallData_30 (by decide) (by decide) (by decide) small_30
      · exact exists_from_small smallData_46 (by decide) (by decide) (by decide) small_46
      · exact exists_from_small smallData_62 (by decide) (by decide) (by decide) small_62
      · exact exists_from_small smallData_78 (by decide) (by decide) (by decide) small_78
      · exact exists_from_small smallData_94 (by decide) (by decide) (by decide) small_94
      · exact exists_from_small smallData_110 (by decide) (by decide) (by decide) small_110
    · have hq : m + m = 2 * oddTail_14.h + 4 * (4 * ((m + m - 126) / 16 + 1) + oddTail_14.R) := by
        change m + m = 2 * 15 + 4 * (4 * ((m + m - 126) / 16 + 1) + 20); omega
      rw [hq]
      exact exists_from_glue (by decide) (by decide) (by change 15 ≤ 4 * _ + 20; omega)
        validBase_30 (oddTail1Valid oddTail_14 checkOddTail_14 _)
        (oddTail2Valid oddTail_14 checkOddTail_14 _)
        (oddTail_disjoint oddTail_14 checkOddTail_14 _)

/-- **Conjecture 3 of Ghafari & Wanless (`arXiv:2607.17547v1`, July 2026):**
For every even integer `n ≥ 28`, there is a Latin square of order `n` that has no two disjoint
transversals and no pinned entry. -/
theorem ghafari_wanless_conjecture3 :
    ∀ n : ℕ, 28 ≤ n → Even n →
      ∃ L : LatinSquare n,
        (∀ T₁ T₂, IsTransversal L T₁ → IsTransversal L T₂ → ¬ DisjointTransversals T₁ T₂) ∧
        HasNoPinnedEntry L :=
  fun n hn heven => ghafari_wanless_all_even_ge_22_ne_24 n (by omega) (by omega) heven

end GhafariWanless
