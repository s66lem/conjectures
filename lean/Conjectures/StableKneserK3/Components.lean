import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Finset.Basic

namespace StableKneserK3

/-- A cycle on the first interval, a path or cycle on the next interval, and isolated
vertices on the remainder. -/
def componentGraph (n m r : ℕ) (close : Bool) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧
    (a.val < m ∧ b.val < m ∧ (a.val+1=b.val ∨ b.val+1=a.val ∨
      a.val=0 ∧ b.val+1=m ∨ b.val=0 ∧ a.val+1=m) ∨
    m ≤ a.val ∧ m ≤ b.val ∧ a.val < m+r ∧ b.val < m+r ∧
      (a.val+1=b.val ∨ b.val+1=a.val ∨ close ∧
        (a.val=m ∧ b.val+1=m+r ∨ b.val=m ∧ a.val+1=m+r)))
  symm := ⟨by intro a b h; grind⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (n m r : ℕ) (close : Bool) : DecidableRel (componentGraph n m r close).Adj :=
  fun _ _ => by unfold componentGraph; dsimp; infer_instance

namespace WeightCertificate

/-- The low fifteen bits contain three five-bit ground-vertex indices. -/
def sample (n : ℕ) [NeZero n] (code : ℕ) : Finset (Fin n) × ℕ :=
  ({Fin.ofNat n (code % 32), Fin.ofNat n (code / 32 % 32), Fin.ofNat n (code / 1024 % 32)},
    code / 32768)

end WeightCertificate
end StableKneserK3
