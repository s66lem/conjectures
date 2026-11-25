import Conjectures.StableKneserK3.Reduction
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace StableKneserK3

open SimpleGraph

theorem cycle_adj_values {n : ℕ} (hn : 2 ≤ n) {a b : Fin n} :
    (cycleGraph n).Adj a b ↔
      a.val+1=b.val ∨ b.val+1=a.val ∨ a.val+1=n ∧ b.val=0 ∨ b.val+1=n ∧ a.val=0 := by
  have val (u v : Fin n) : (u-v).val = if v.val ≤ u.val then u.val-v.val else n-v.val+u.val := by
    split
    · exact Fin.sub_val_of_le ‹_›
    · rw [Fin.val_sub, Nat.mod_eq_of_lt (by have := v.isLt; omega)]
  rw [cycleGraph_adj', val, val]
  have ha := a.isLt
  have hb := b.isLt
  split <;> split <;> omega

private theorem tight_cycle_deletion {m : ℕ} (hm : 5 ≤ m) (ht : K3Tight (cycleGraph m))
    (x : Fin (m+1)) : K3Tight ((cycleGraph (m+1)).induce {v | v ≠ x}) := by
  let W := {v : Fin (m+1) // v ≠ x}
  have pos (v : W) : 0 < (v.val - x).val := by
    have h : v.val - x ≠ 0 := sub_ne_zero.mpr v.property
    exact Nat.pos_of_ne_zero (fun he => h (Fin.ext he))
  let g (v : W) : Fin m := ⟨(v.val-x).val-1, by have := (v.val-x).isLt; omega⟩
  have inj : Function.Injective g := by
    intro a b he
    have h := congrArg Fin.val he
    change (a.val-x).val-1 = (b.val-x).val-1 at h
    have h' : a.val-x = b.val-x := Fin.ext (by have := pos a; have := pos b; omega)
    exact Subtype.ext (sub_left_inj.mp h')
  have cardW : Fintype.card W = m := by simp [W]
  apply tight_of_subgraph ⟨g,inj⟩ (G := cycleGraph m) _ (by omega) ht
  intro a b h
  have hrot : (cycleGraph (m+1)).Adj (a.val-x) (b.val-x) := by
    change (cycleGraph (m+1)).Adj a.val b.val at h
    rw [cycleGraph_adj']
    simpa only [sub_sub_sub_cancel_right] using cycleGraph_adj'.mp h
  obtain hr := (cycle_adj_values (by omega)).mp hrot
  apply (cycle_adj_values (by omega)).mpr
  change (a.val-x).val-1+1 = (b.val-x).val-1 ∨ (b.val-x).val-1+1 = (a.val-x).val-1 ∨ _
  have := pos a
  have := pos b
  omega

/-- A star in a deficient coloring reduces a cycle to the previous order. -/
theorem cycle_tight_of_star {m : ℕ} (hm : 5 ≤ m) (ht : K3Tight (cycleGraph m))
    (hstar : ∀ c : Triple (cycleGraph (m+1)) → Fin (m+1-5), IsProperColoring _ _ c →
      ∃ i x, ∀ s, c s = i → x ∈ s.val) : K3Tight (cycleGraph (m+1)) := by
  refine ⟨?_,upper_bound _ (by simpa using (show 5 ≤ m+1 by omega))⟩
  rw [Fintype.card_fin]
  rintro ⟨c,hc⟩
  obtain ⟨i,x,hx⟩ := hstar c hc
  apply (tight_cycle_deletion hm ht x).1
  have h := delete_star_color c hc i x hx
  convert h using 1
  change Fintype.card {v : Fin (m+1) // v ≠ x} - 5 = m+1-5-1
  have : Fintype.card {v : Fin (m+1) // v ≠ x} = m := by simp
  omega

/-- For cycles, all larger orders follow from the fourteen base orders by vertex deletion. -/
theorem cycle_tight_of_finite (hbase : ∀ m, 6 ≤ m → m ≤ 19 → K3Tight (cycleGraph m))
    (m : ℕ) (hm : 6 ≤ m) : K3Tight (cycleGraph m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hsmall : m ≤ 19
    · exact hbase m hm hsmall
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' (show 3 ≤ m by omega)
    by_contra hbad
    have hdeg (v : Fin (k+3)) : (cycleGraph (k+3)).degree v ≤ 2 := cycleGraph_degree_three_le.le
    have htri (a b c : Fin (k+3)) (ab : (cycleGraph (k+3)).Adj a b)
        (bc : (cycleGraph (k+3)).Adj b c) (ac : (cycleGraph (k+3)).Adj a c) : False := by
      have := (cycle_adj_values (by omega)).mp ab
      have := (cycle_adj_values (by omega)).mp bc
      have := (cycle_adj_values (by omega)).mp ac
      have := a.isLt
      have := b.isLt
      have := c.isLt
      omega
    have h := minimal_failure_order_le_nineteen hdeg htri hbad
      (tight_cycle_deletion (m := k+2) (by omega) (ih (k+2) (by omega) (by omega)))
    rw [Fintype.card_fin] at h
    omega

end StableKneserK3

