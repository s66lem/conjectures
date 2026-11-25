import Conjectures.StableKneserK3.CaseReduction
import Conjectures.StableKneserK3.Girth
import Conjectures.StableKneserK3.Isolate9
import Conjectures.StableKneserK3.Dual9r2
import Conjectures.StableKneserK3.Dual9r3
import Conjectures.StableKneserK3.Dual10r2
import Conjectures.StableKneserK3.Dual10r1
import Conjectures.StableKneserK3.Dual11r1
import Conjectures.StableKneserK3.TwoCycleWeights
import Conjectures.StableKneserK3.TwoCycleReversed
import Conjectures.StableKneserK3.PathWeights13
import Conjectures.StableKneserK3.PathWeights14
import Conjectures.StableKneserK3.PathWeights15
import Conjectures.StableKneserK3.PathWeights16
import Conjectures.StableKneserK3.PathWeights17
import Conjectures.StableKneserK3.PathWeights18
import Conjectures.StableKneserK3.PathWeights19

import Mathlib.Tactic.IntervalCases

namespace StableKneserK3
open SimpleGraph

private abbrev Below (n : ℕ) := ∀ {V : Type} [Fintype V] (G : SimpleGraph V)
  [DecidableRel G.Adj], 7 ≤ Fintype.card V → Fintype.card V < n → Qualifies G → K3Tight G

private theorem from_star {n : ℕ} (hn : 8 ≤ n) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hf : StarForced H (n-5)) (hg : Qualifies H) (ih : Below n) : K3Tight H := by
  apply tight_of_forced_star H (by simpa using (show 6 ≤ n by omega)) (by simpa using hf)
  intro x
  let J := H.induce {v | v ≠ x}
  have card : Fintype.card {v : Fin n // v ≠ x} = n-1 := by simp
  apply ih J (by change 7 ≤ Fintype.card {v : Fin n // v ≠ x}; omega)
    (by change Fintype.card {v : Fin n // v ≠ x} < n; omega)
  exact qualifies_subgraph hg (Copy.induce H _)

private theorem enlarge {m r : ℕ} (ht : K3Tight (componentGraph (m+r) m r true)) (hn : 5 ≤ m+r) :
    K3Tight (componentGraph (m+r) m r false) := by
  apply tight_of_subgraph (G := componentGraph (m+r) m r true) (Function.Embedding.refl _) _
    (by simpa using hn) ht
  intro x y h
  exact ⟨h.1, h.2.imp id (fun ⟨a,b,c,d,e⟩ => ⟨a,b,c,d,
    e.imp_right (fun h => h.imp_right (fun ⟨hf,_⟩ => by contradiction))⟩)⟩


private theorem case9_9_0_1 (ih : Below 18) : K3Tight (componentGraph 18 9 9 true) :=
  from_star (by decide) _ Weights9_9_0_1.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case9_10_0_1 (ih : Below 19) : K3Tight (componentGraph 19 9 10 true) :=
  from_star (by decide) _ Weights9_10_0_1.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case10_9_0_1 (ih : Below 19) : K3Tight (componentGraph 19 10 9 true) :=
  from_star (by decide) _ Weights10_9_0_1.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case9_9_1_1 (ih : Below 19) : K3Tight (componentGraph 19 9 9 true) :=
  from_star (by decide) _ Weights9_9_1_1.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem two_tight {n : ℕ} (hn : n ≤ 19) (ih : Below n)
    (m r : ℕ) (hm : 9 ≤ m) (hr : 9 ≤ r) (hle : m+r ≤ n) : K3Tight (componentGraph n m r true) := by
  have cases : (m=9 ∧ r=9 ∧ n=18) ∨ (m=9 ∧ r=10 ∧ n=19) ∨ (m=10 ∧ r=9 ∧ n=19) ∨ (m=9 ∧ r=9 ∧ n=19) := by omega
  rcases cases with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> first | exact case9_9_0_1 ih | exact case9_10_0_1 ih | exact case10_9_0_1 ih | exact case9_9_1_1 ih

private theorem order7 (_ih : Below 7) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=7) :
    K3Tight (componentGraph 7 m r false) := by
  omega

private theorem order8 (_ih : Below 8) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=8) :
    K3Tight (componentGraph 8 m r false) := by
  omega

private theorem order9 (_ih : Below 9) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=9) :
    K3Tight (componentGraph 9 m r false) := by
  omega

private theorem case9_1_0_0 (_ : Below 10) : K3Tight (componentGraph 10 9 1 false) := component9_1_tight

private theorem order10 (ih : Below 10) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=10) :
    K3Tight (componentGraph 10 m r false) := by
  have cases : m=9 := by omega
  subst m
  have h : r=1 := by omega
  rw [h]; exact case9_1_0_0 ih

private theorem case9_2_0_0 (ih : Below 11) : K3Tight (componentGraph 11 9 2 false) :=
  from_star (by decide) _ Dual9_2.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case10_1_0_0 (ih : Below 11) : K3Tight (componentGraph 11 10 1 false) :=
  from_star (by decide) _ Dual10_1.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem order11 (ih : Below 11) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=11) :
    K3Tight (componentGraph 11 m r false) := by
  have cases : m=9 ∨ m=10 := by omega
  rcases cases with rfl | rfl
  · have h : r=2 := by omega
    rw [h]; exact case9_2_0_0 ih
  · have h : r=1 := by omega
    rw [h]; exact case10_1_0_0 ih

private theorem case9_3_0_0 (ih : Below 12) : K3Tight (componentGraph 12 9 3 false) :=
  from_star (by decide) _ Dual9_3.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case10_2_0_0 (ih : Below 12) : K3Tight (componentGraph 12 10 2 false) :=
  from_star (by decide) _ Dual10_2.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case11_1_0_0 (ih : Below 12) : K3Tight (componentGraph 12 11 1 false) :=
  from_star (by decide) _ Dual11_1.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem order12 (ih : Below 12) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=12) :
    K3Tight (componentGraph 12 m r false) := by
  have cases : m=9 ∨ m=10 ∨ m=11 := by omega
  rcases cases with rfl | rfl | rfl
  · have h : r=3 := by omega
    rw [h]; exact case9_3_0_0 ih
  · have h : r=2 := by omega
    rw [h]; exact case10_2_0_0 ih
  · have h : r=1 := by omega
    rw [h]; exact case11_1_0_0 ih

private theorem case9_4_0_0 (ih : Below 13) : K3Tight (componentGraph 13 9 4 false) :=
  from_star (by decide) _ Weights9_4_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case10_3_0_0 (ih : Below 13) : K3Tight (componentGraph 13 10 3 false) :=
  from_star (by decide) _ Weights10_3_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case11_2_0_0 (ih : Below 13) : K3Tight (componentGraph 13 11 2 false) :=
  from_star (by decide) _ Weights11_2_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case12_1_0_0 (ih : Below 13) : K3Tight (componentGraph 13 12 1 false) :=
  from_star (by decide) _ Weights12_1_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem order13 (ih : Below 13) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=13) :
    K3Tight (componentGraph 13 m r false) := by
  have cases : m=9 ∨ m=10 ∨ m=11 ∨ m=12 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · have h : r=4 := by omega
    rw [h]; exact case9_4_0_0 ih
  · have h : r=3 := by omega
    rw [h]; exact case10_3_0_0 ih
  · have h : r=2 := by omega
    rw [h]; exact case11_2_0_0 ih
  · have h : r=1 := by omega
    rw [h]; exact case12_1_0_0 ih

private theorem case9_5_0_0 (ih : Below 14) : K3Tight (componentGraph 14 9 5 false) :=
  from_star (by decide) _ Weights9_5_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case10_4_0_0 (ih : Below 14) : K3Tight (componentGraph 14 10 4 false) :=
  from_star (by decide) _ Weights10_4_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case11_3_0_0 (ih : Below 14) : K3Tight (componentGraph 14 11 3 false) :=
  from_star (by decide) _ Weights11_3_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case12_2_0_0 (ih : Below 14) : K3Tight (componentGraph 14 12 2 false) :=
  from_star (by decide) _ Weights12_2_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case13_1_0_0 (ih : Below 14) : K3Tight (componentGraph 14 13 1 false) :=
  from_star (by decide) _ Weights13_1_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem order14 (ih : Below 14) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=14) :
    K3Tight (componentGraph 14 m r false) := by
  have cases : m=9 ∨ m=10 ∨ m=11 ∨ m=12 ∨ m=13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · have h : r=5 := by omega
    rw [h]; exact case9_5_0_0 ih
  · have h : r=4 := by omega
    rw [h]; exact case10_4_0_0 ih
  · have h : r=3 := by omega
    rw [h]; exact case11_3_0_0 ih
  · have h : r=2 := by omega
    rw [h]; exact case12_2_0_0 ih
  · have h : r=1 := by omega
    rw [h]; exact case13_1_0_0 ih

private theorem case9_6_0_0 (ih : Below 15) : K3Tight (componentGraph 15 9 6 false) :=
  from_star (by decide) _ Weights9_6_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case10_5_0_0 (ih : Below 15) : K3Tight (componentGraph 15 10 5 false) :=
  from_star (by decide) _ Weights10_5_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case11_4_0_0 (ih : Below 15) : K3Tight (componentGraph 15 11 4 false) :=
  from_star (by decide) _ Weights11_4_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case12_3_0_0 (ih : Below 15) : K3Tight (componentGraph 15 12 3 false) :=
  from_star (by decide) _ Weights12_3_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case13_2_0_0 (ih : Below 15) : K3Tight (componentGraph 15 13 2 false) :=
  from_star (by decide) _ Weights13_2_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case14_1_0_0 (ih : Below 15) : K3Tight (componentGraph 15 14 1 false) :=
  from_star (by decide) _ Weights14_1_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem order15 (ih : Below 15) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=15) :
    K3Tight (componentGraph 15 m r false) := by
  have cases : m=9 ∨ m=10 ∨ m=11 ∨ m=12 ∨ m=13 ∨ m=14 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · have h : r=6 := by omega
    rw [h]; exact case9_6_0_0 ih
  · have h : r=5 := by omega
    rw [h]; exact case10_5_0_0 ih
  · have h : r=4 := by omega
    rw [h]; exact case11_4_0_0 ih
  · have h : r=3 := by omega
    rw [h]; exact case12_3_0_0 ih
  · have h : r=2 := by omega
    rw [h]; exact case13_2_0_0 ih
  · have h : r=1 := by omega
    rw [h]; exact case14_1_0_0 ih

private theorem case9_7_0_0 (ih : Below 16) : K3Tight (componentGraph 16 9 7 false) :=
  from_star (by decide) _ Weights9_7_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case10_6_0_0 (ih : Below 16) : K3Tight (componentGraph 16 10 6 false) :=
  from_star (by decide) _ Weights10_6_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case11_5_0_0 (ih : Below 16) : K3Tight (componentGraph 16 11 5 false) :=
  from_star (by decide) _ Weights11_5_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case12_4_0_0 (ih : Below 16) : K3Tight (componentGraph 16 12 4 false) :=
  from_star (by decide) _ Weights12_4_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case13_3_0_0 (ih : Below 16) : K3Tight (componentGraph 16 13 3 false) :=
  from_star (by decide) _ Weights13_3_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case14_2_0_0 (ih : Below 16) : K3Tight (componentGraph 16 14 2 false) :=
  from_star (by decide) _ Weights14_2_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case15_1_0_0 (ih : Below 16) : K3Tight (componentGraph 16 15 1 false) :=
  from_star (by decide) _ Weights15_1_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem order16 (ih : Below 16) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=16) :
    K3Tight (componentGraph 16 m r false) := by
  have cases : m=9 ∨ m=10 ∨ m=11 ∨ m=12 ∨ m=13 ∨ m=14 ∨ m=15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h : r=7 := by omega
    rw [h]; exact case9_7_0_0 ih
  · have h : r=6 := by omega
    rw [h]; exact case10_6_0_0 ih
  · have h : r=5 := by omega
    rw [h]; exact case11_5_0_0 ih
  · have h : r=4 := by omega
    rw [h]; exact case12_4_0_0 ih
  · have h : r=3 := by omega
    rw [h]; exact case13_3_0_0 ih
  · have h : r=2 := by omega
    rw [h]; exact case14_2_0_0 ih
  · have h : r=1 := by omega
    rw [h]; exact case15_1_0_0 ih

private theorem case9_8_0_0 (ih : Below 17) : K3Tight (componentGraph 17 9 8 false) :=
  from_star (by decide) _ Weights9_8_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case10_7_0_0 (ih : Below 17) : K3Tight (componentGraph 17 10 7 false) :=
  from_star (by decide) _ Weights10_7_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case11_6_0_0 (ih : Below 17) : K3Tight (componentGraph 17 11 6 false) :=
  from_star (by decide) _ Weights11_6_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case12_5_0_0 (ih : Below 17) : K3Tight (componentGraph 17 12 5 false) :=
  from_star (by decide) _ Weights12_5_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case13_4_0_0 (ih : Below 17) : K3Tight (componentGraph 17 13 4 false) :=
  from_star (by decide) _ Weights13_4_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case14_3_0_0 (ih : Below 17) : K3Tight (componentGraph 17 14 3 false) :=
  from_star (by decide) _ Weights14_3_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case15_2_0_0 (ih : Below 17) : K3Tight (componentGraph 17 15 2 false) :=
  from_star (by decide) _ Weights15_2_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case16_1_0_0 (ih : Below 17) : K3Tight (componentGraph 17 16 1 false) :=
  from_star (by decide) _ Weights16_1_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem order17 (ih : Below 17) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=17) :
    K3Tight (componentGraph 17 m r false) := by
  have cases : m=9 ∨ m=10 ∨ m=11 ∨ m=12 ∨ m=13 ∨ m=14 ∨ m=15 ∨ m=16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h : r=8 := by omega
    rw [h]; exact case9_8_0_0 ih
  · have h : r=7 := by omega
    rw [h]; exact case10_7_0_0 ih
  · have h : r=6 := by omega
    rw [h]; exact case11_6_0_0 ih
  · have h : r=5 := by omega
    rw [h]; exact case12_5_0_0 ih
  · have h : r=4 := by omega
    rw [h]; exact case13_4_0_0 ih
  · have h : r=3 := by omega
    rw [h]; exact case14_3_0_0 ih
  · have h : r=2 := by omega
    rw [h]; exact case15_2_0_0 ih
  · have h : r=1 := by omega
    rw [h]; exact case16_1_0_0 ih

private theorem case9_9_0_0 (ih : Below 18) : K3Tight (componentGraph 18 9 9 false) := enlarge (m := 9) (r := 9) (case9_9_0_1 ih) (by decide)

private theorem case10_8_0_0 (ih : Below 18) : K3Tight (componentGraph 18 10 8 false) :=
  from_star (by decide) _ Weights10_8_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case11_7_0_0 (ih : Below 18) : K3Tight (componentGraph 18 11 7 false) :=
  from_star (by decide) _ Weights11_7_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case12_6_0_0 (ih : Below 18) : K3Tight (componentGraph 18 12 6 false) :=
  from_star (by decide) _ Weights12_6_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case13_5_0_0 (ih : Below 18) : K3Tight (componentGraph 18 13 5 false) :=
  from_star (by decide) _ Weights13_5_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case14_4_0_0 (ih : Below 18) : K3Tight (componentGraph 18 14 4 false) :=
  from_star (by decide) _ Weights14_4_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case15_3_0_0 (ih : Below 18) : K3Tight (componentGraph 18 15 3 false) :=
  from_star (by decide) _ Weights15_3_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case16_2_0_0 (ih : Below 18) : K3Tight (componentGraph 18 16 2 false) :=
  from_star (by decide) _ Weights16_2_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case17_1_0_0 (ih : Below 18) : K3Tight (componentGraph 18 17 1 false) :=
  from_star (by decide) _ Weights17_1_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem order18 (ih : Below 18) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=18) :
    K3Tight (componentGraph 18 m r false) := by
  have cases : m=9 ∨ m=10 ∨ m=11 ∨ m=12 ∨ m=13 ∨ m=14 ∨ m=15 ∨ m=16 ∨ m=17 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h : r=9 := by omega
    rw [h]; exact case9_9_0_0 ih
  · have h : r=8 := by omega
    rw [h]; exact case10_8_0_0 ih
  · have h : r=7 := by omega
    rw [h]; exact case11_7_0_0 ih
  · have h : r=6 := by omega
    rw [h]; exact case12_6_0_0 ih
  · have h : r=5 := by omega
    rw [h]; exact case13_5_0_0 ih
  · have h : r=4 := by omega
    rw [h]; exact case14_4_0_0 ih
  · have h : r=3 := by omega
    rw [h]; exact case15_3_0_0 ih
  · have h : r=2 := by omega
    rw [h]; exact case16_2_0_0 ih
  · have h : r=1 := by omega
    rw [h]; exact case17_1_0_0 ih

private theorem case9_10_0_0 (ih : Below 19) : K3Tight (componentGraph 19 9 10 false) := enlarge (m := 9) (r := 10) (case9_10_0_1 ih) (by decide)

private theorem case10_9_0_0 (ih : Below 19) : K3Tight (componentGraph 19 10 9 false) := enlarge (m := 10) (r := 9) (case10_9_0_1 ih) (by decide)

private theorem case11_8_0_0 (ih : Below 19) : K3Tight (componentGraph 19 11 8 false) :=
  from_star (by decide) _ Weights11_8_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case12_7_0_0 (ih : Below 19) : K3Tight (componentGraph 19 12 7 false) :=
  from_star (by decide) _ Weights12_7_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case13_6_0_0 (ih : Below 19) : K3Tight (componentGraph 19 13 6 false) :=
  from_star (by decide) _ Weights13_6_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case14_5_0_0 (ih : Below 19) : K3Tight (componentGraph 19 14 5 false) :=
  from_star (by decide) _ Weights14_5_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case15_4_0_0 (ih : Below 19) : K3Tight (componentGraph 19 15 4 false) :=
  from_star (by decide) _ Weights15_4_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case16_3_0_0 (ih : Below 19) : K3Tight (componentGraph 19 16 3 false) :=
  from_star (by decide) _ Weights16_3_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case17_2_0_0 (ih : Below 19) : K3Tight (componentGraph 19 17 2 false) :=
  from_star (by decide) _ Weights17_2_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem case18_1_0_0 (ih : Below 19) : K3Tight (componentGraph 19 18 1 false) :=
  from_star (by decide) _ Weights18_1_0_0.hasStar (qualifies_of_check _ (by decide +kernel) (by decide +kernel)) ih

private theorem order19 (ih : Below 19) (m r : ℕ) (hm : 9 ≤ m) (hr : 1 ≤ r) (eq : m+r=19) :
    K3Tight (componentGraph 19 m r false) := by
  have cases : m=9 ∨ m=10 ∨ m=11 ∨ m=12 ∨ m=13 ∨ m=14 ∨ m=15 ∨ m=16 ∨ m=17 ∨ m=18 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h : r=10 := by omega
    rw [h]; exact case9_10_0_0 ih
  · have h : r=9 := by omega
    rw [h]; exact case10_9_0_0 ih
  · have h : r=8 := by omega
    rw [h]; exact case11_8_0_0 ih
  · have h : r=7 := by omega
    rw [h]; exact case12_7_0_0 ih
  · have h : r=6 := by omega
    rw [h]; exact case13_6_0_0 ih
  · have h : r=5 := by omega
    rw [h]; exact case14_5_0_0 ih
  · have h : r=4 := by omega
    rw [h]; exact case15_4_0_0 ih
  · have h : r=3 := by omega
    rw [h]; exact case16_3_0_0 ih
  · have h : r=2 := by omega
    rw [h]; exact case17_2_0_0 ih
  · have h : r=1 := by omega
    rw [h]; exact case18_1_0_0 ih

theorem finite_cases_of_cycles (hcyc : ∀ m ≥ 6, K3Tight (cycleGraph m)) (n : ℕ)
    (hn : 7 ≤ n) (hs : n ≤ 19) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hg : Qualifies G) : K3Tight G := by
  suffices h : ∀ {V : Type} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = n → Qualifies H → K3Tight H by exact h G (Fintype.card_fin n) hg
  clear! G
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ H _ card qual
    have small : Below n := by
      intro W _ J _ hj hj' hqual
      exact ih _ hj' hj (by omega) J rfl hqual
    obtain ⟨ms,r,hlen,hlong,f,he⟩ := canonical_layout H qual card
    apply tight_canonical card hn hs hcyc _ (two_tight hs small) ms r hlen hlong f he
    interval_cases n <;> first | exact order7 small | exact order8 small | exact order9 small | exact order10 small | exact order11 small | exact order12 small | exact order13 small | exact order14 small | exact order15 small | exact order16 small | exact order17 small | exact order18 small | exact order19 small

end StableKneserK3
