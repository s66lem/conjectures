import Conjectures.StableKneserK3.CycleReduction
import Conjectures.StableKneserK3.SmallComponents

namespace StableKneserK3

open SimpleGraph

private instance isolateDecidable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (withIsolate G).Adj
  | .inl a, .inl b => inferInstanceAs (Decidable (G.Adj a b))
  | .inl _, .inr _ => isFalse (by change false ≠ true; decide)
  | .inr _, .inl _ => isFalse (by change false ≠ true; decide)
  | .inr _, .inr _ => isFalse id

/-- Conjecture 1.3 at uniformity three, in its forbidden-subgraph formulation. -/
theorem conjecture_1_3_k3 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 7 ≤ Fintype.card V) : K3Tight G ↔ Qualifies G :=
  tight_iff_qualifies_of_finite (finite_cases_of_cycles schrijver_k3) G hn

/-- A cycle and an isolated vertex attain the exact chromatic bound at every length
covered by the conjecture. -/
theorem isolate_k3 (m : ℕ) (hm : 9 ≤ m) : K3Tight (withIsolate (cycleGraph m)) := by
  by_cases hl : 15 ≤ m
  · exact large_isolate_k3 m hl
  have hu : m ≤ 14 := by omega
  interval_cases m <;> apply (conjecture_1_3_k3 _ (by decide)).mpr <;>
    exact qualifies_of_check _ (by decide +kernel) (by decide +kernel)

end StableKneserK3
