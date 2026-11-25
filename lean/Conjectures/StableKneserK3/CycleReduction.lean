import Conjectures.StableKneserK3.Cycles
import Conjectures.StableKneserK3.SmallCycles
import Conjectures.StableKneserK3.Cycle10
import Conjectures.StableKneserK3.Cycle11
import Conjectures.StableKneserK3.Dual12
import Conjectures.StableKneserK3.Dual13r0
import Conjectures.StableKneserK3.Weight14
import Conjectures.StableKneserK3.Weight15
import Conjectures.StableKneserK3.Weight16
import Conjectures.StableKneserK3.Weight17
import Conjectures.StableKneserK3.Weight18
import Conjectures.StableKneserK3.Weight19
import Conjectures.StableKneserK3.Mantel
import Mathlib.Tactic.IntervalCases
import Conjectures.StableKneserK3.Components

namespace StableKneserK3

open SimpleGraph

theorem schrijver_k3 (n : ℕ) (hn : 6 ≤ n) : K3Tight (cycleGraph n) := by
  have h12 := cycle_tight_of_star (by decide) cycle11_tight Dual12_0.hasStar
  have h13 := cycle_tight_of_star (by decide) h12 Dual13_0.hasStar
  have h14 := cycle_tight_of_star (by decide) h13 Weights14.hasStar
  have h15 := cycle_tight_of_star (by decide) h14 Weights15.hasStar
  have h16 := cycle_tight_of_star (by decide) h15 Weights16.hasStar
  have h17 := cycle_tight_of_star (by decide) h16 Weights17.hasStar
  have h18 := cycle_tight_of_star (by decide) h17 Weights18.hasStar
  have h19 := cycle_tight_of_star (by decide) h18 Weights19.hasStar
  apply cycle_tight_of_finite _ n hn
  intro m hm hlo
  have h6 := cycle6_tight
  have h7 := cycle7_tight
  have h8 := cycle8_tight
  have h9 := cycle9_tight
  have h10 := cycle10_tight
  have h11 := cycle11_tight
  interval_cases m <;> assumption

theorem large_isolate_k3 (n : ℕ) (hn : 15 ≤ n) : K3Tight (withIsolate (cycleGraph n)) := by
  apply tight_withIsolate_of_cycle_lower hn
  simpa using (schrijver_k3 n (by omega)).1

end StableKneserK3
