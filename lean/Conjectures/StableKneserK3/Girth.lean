import Conjectures.StableKneserK3.FiniteReduction
import Conjectures.StableKneserK3.Cycles

namespace StableKneserK3

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Starting from a directed edge, extend a walk without immediately reversing it. -/
def returnsTo (start : V) : ℕ → V → V → Bool
  | 0, _, v => decide (v = start)
  | k+1, prev, v => decide (∃ w ∈ G.neighborFinset v, w ≠ prev ∧ returnsTo start k v w)

private theorem find_return {m : ℕ} (hm : 3 ≤ m) (f : Copy (cycleGraph m) G) :
    ∃ a b : V, G.Adj a b ∧ returnsTo G a (m-1) a b := by
  have : NeZero m := ⟨by omega⟩
  let atV (j : ℕ) := f (Fin.ofNat m j)
  have edge (j : ℕ) : G.Adj (atV j) (atV (j+1)) := by
    apply f.toHom.map_rel'
    apply (cycle_adj_values (by omega)).mpr
    change j%m+1=(j+1)%m ∨ (j+1)%m+1=j%m ∨ _ ∨ _
    rw [Nat.add_mod]
    simp only [Nat.mod_eq_of_lt (show 1 < m by omega)]
    have hl := Nat.mod_lt j (by omega : 0 < m)
    by_cases hj : j%m+1<m
    · exact Or.inl (Nat.mod_eq_of_lt hj).symm
    · have hh : j%m+1=m := by omega
      exact Or.inr (Or.inr (Or.inl ⟨hh,by change (j+1)%m=0; rw [Nat.add_mod]; simp [Nat.mod_eq_of_lt (show 1<m by omega),hh]⟩))
  have skip (j : ℕ) : atV (j+2) ≠ atV j := by
    intro eq
    have h := congrArg Fin.val (f.injective eq)
    change (j+2)%m=j%m at h
    rw [Nat.add_mod] at h
    simp only [Nat.mod_eq_of_lt (show 2<m by omega)] at h
    have hl := Nat.mod_lt j (by omega : 0<m)
    by_cases hj : j%m+2<m
    · rw [Nat.mod_eq_of_lt hj] at h; omega
    · rw [Nat.mod_eq_sub_mod (by omega : m ≤ j%m+2),
        Nat.mod_eq_of_lt (by omega : j%m+2-m < m)] at h
      omega
  have path (k j : ℕ) (endAt : j+1+k=m) :
      returnsTo G (atV 0) k (atV j) (atV (j+1)) := by
    induction k generalizing j with
    | zero =>
      simp only [Nat.add_zero] at endAt
      simp [returnsTo,endAt,atV,Fin.ofNat]
    | succ k ih =>
      exact decide_eq_true ⟨atV (j+2),(G.mem_neighborFinset ..).mpr (edge (j+1)),skip j,ih (j+1) (by omega)⟩
  exact ⟨_,_,edge 0,path (m-1) 0 (by omega)⟩

def girthCheck : Bool :=
  decide (∀ j : Fin 6, ∀ x : V, ∀ y ∈ G.neighborFinset x, returnsTo G x (j.val+2) x y = false)

theorem qualifies_of_check (hd : ∀ v, G.degree v ≤ 2) (h : girthCheck G) : Qualifies G := by
  refine ⟨hd,fun m hm hs _ => ⟨fun f => ?_⟩⟩
  obtain ⟨x,y,he,hr⟩ := find_return G hm f
  have check := of_decide_eq_true h (⟨m-3,by omega⟩ : Fin 6) x y ((G.mem_neighborFinset ..).mpr he)
  change returnsTo G x (m-3+2) x y = false at check
  rw [show m-3+2=m-1 by omega,hr] at check
  contradiction

end StableKneserK3
