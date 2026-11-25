import Conjectures.StableKneserK3.Cycle10
import Conjectures.StableKneserK3.Cycles
import Conjectures.StableKneserK3.Dual11r0

namespace StableKneserK3

theorem cycle11_tight : K3Tight (SimpleGraph.cycleGraph 11) :=
  cycle_tight_of_star (by decide) cycle10_tight Dual11_0.hasStar

end StableKneserK3
