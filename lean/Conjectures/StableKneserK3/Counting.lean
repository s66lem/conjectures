import Conjectures.StableKneserK3.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith

namespace StableKneserK3

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def stableTriples : Finset (Finset V) :=
  (univ.powersetCard 3).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, ¬ G.Adj x y)

theorem mem_stableTriples {s : Finset V} : s ∈ stableTriples G ↔ StableTriple G s := by
  simp [stableTriples, StableTriple]

/-- A mixed vertex of a triple is adjacent to exactly one of the other two vertices. -/
private def Mixed (s : Finset V) (x : V) : Prop :=
  ∃ a b, s = {x, a, b} ∧ G.Adj x a ∧ b ≠ x ∧ ¬ G.Adj x b

omit [Fintype V] in
private theorem two_mixed {s : Finset V} (hs : s.card = 3) (hbad : ¬ StableTriple G s)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj x z) :
    ∃ x y, x ≠ y ∧ Mixed G s x ∧ Mixed G s y := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hs
  have mix {x y z : V} (he : G.Adj x y) (hn : ¬ G.Adj x z) (h : z ≠ x)
      (hp : ({a,b,c} : Finset V) = {x,y,z}) : Mixed G {a,b,c} x :=
    ⟨y, z, hp, he, h, hn⟩
  by_cases ab : G.Adj a b <;> by_cases ac : G.Adj a c <;> by_cases bc : G.Adj b c
  · exact False.elim (htri a b c ab bc ac)
  · exact ⟨b, c, hbc, mix ab.symm bc hbc.symm (by grind),
      mix ac.symm (fun h => bc h.symm) hbc (by grind)⟩
  · exact ⟨a, c, hac, mix ab ac hac.symm (by grind),
      mix bc.symm (fun h => ac h.symm) hac (by grind)⟩
  · exact ⟨a, b, hab, mix ab ac hac.symm (by grind), mix ab.symm bc hbc.symm (by grind)⟩
  · exact ⟨a, b, hab, mix ac ab hab.symm (by grind),
      mix bc (fun h => ab h.symm) hab (by grind)⟩
  · exact ⟨a, c, hac, mix ac ab hab.symm (by grind),
      mix ac.symm (fun h => bc h.symm) hbc (by grind)⟩
  · exact ⟨b, c, hbc, mix bc (fun h => ab h.symm) hab (by grind),
      mix bc.symm (fun h => ac h.symm) hac (by grind)⟩
  · exfalso
    apply hbad
    refine ⟨hs, ?_⟩
    intro x hx y hy hxy
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact hxy.ne rfl | contradiction | exact ab hxy.symm | exact ac hxy.symm |
        exact bc hxy.symm

/-- Triangle-free graphs of maximum degree two have at least as many stable triples as a cycle. -/
theorem stableTriple_count_lower (hn : 5 ≤ Fintype.card V)
    (hdeg : ∀ v, G.degree v ≤ 2)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj x z) :
    Fintype.card V * (Fintype.card V - 4) * (Fintype.card V - 5) ≤ 6 * (stableTriples G).card := by
  classical
  let n := Fintype.card V
  let bad := (univ.powersetCard 3) \ stableTriples G
  have lower (s) (hs : s ∈ bad) : 2 ≤ (univ.bipartiteAbove (Mixed G) s).card := by
    obtain ⟨ha, hb⟩ := mem_sdiff.mp hs
    obtain ⟨x, y, hxy, hx, hy⟩ := two_mixed G (mem_powersetCard.mp ha).2
      (fun h => hb ((mem_stableTriples G).mpr h)) htri
    have hsub : {x,y} ⊆ univ.bipartiteAbove (Mixed G) s := by
      simp [insert_subset_iff, bipartiteAbove, hx, hy]
    simpa [hxy] using card_le_card hsub
  have upper (x : V) (_ : x ∈ (univ : Finset V)) :
      (bad.bipartiteBelow (Mixed G) x).card ≤ 2 * (n - 3) := by
    let N := G.neighborFinset x
    let O := (insert x N)ᶜ
    have hsub : bad.bipartiteBelow (Mixed G) x ⊆
        (N ×ˢ O).image (fun p : V × V => {x,p.1,p.2}) := by
      intro s hs
      obtain ⟨a, b, rfl, ha, hbx, hb⟩ := (mem_filter.mp hs).2
      exact mem_image.mpr ⟨(a,b), mem_product.mpr
        ⟨(G.mem_neighborFinset _ _).mpr ha, by simpa [O, N, hbx] using hb⟩, rfl⟩
    have hnx : x ∉ N := by simp [N]
    have ho : O.card = n - (G.degree x + 1) := by
      change (insert x N)ᶜ.card = _
      rw [card_compl, card_insert_of_notMem hnx]
      rfl
    have hd := hdeg x
    calc
      _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_image_le
      _ = G.degree x * (n - (G.degree x + 1)) := by rw [card_product, ho]; rfl
      _ ≤ _ := by
        rcases (show G.degree x = 0 ∨ G.degree x = 1 ∨ G.degree x = 2 by omega) with h | h | h <;>
          rw [h] <;> dsimp [n] <;> omega
  have count := card_nsmul_le_card_nsmul (Mixed G) lower upper
  rw [card_univ, smul_eq_mul, smul_eq_mul] at count
  have hb : bad.card + (stableTriples G).card = n.choose 3 := by
    calc
      _ = (univ.powersetCard 3 : Finset (Finset V)).card :=
        card_sdiff_add_card_eq_card (filter_subset _ _)
      _ = _ := by simp [n]
  have hchoose := Nat.descFactorial_eq_factorial_mul_choose n 3
  simp [Nat.descFactorial_succ, Nat.factorial] at hchoose
  change n * (n - 4) * (n - 5) ≤ _
  change 5 ≤ n at hn
  change bad.card * 2 ≤ n * (2 * (n - 3)) at count
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hn
  simp [hd] at count hchoose hb ⊢
  rw [show 5+d-3 = d+2 by omega] at count
  rw [show 5+d-2 = d+3 by omega] at hchoose
  rw [show 5+d-4 = d+1 by omega]
  nlinarith

/-- At order twenty the stable-triple lower bound first beats the Hilton–Milner capacity. -/
theorem hiltonMilner_cutoff {n : ℕ} (hn : 20 ≤ n) :
    6 * ((n - 5) * (3 * n - 8)) < n * (n - 4) * (n - 5) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h : 3 * (20 + d) - 8 = 52 + 3*d := by omega
  rw [h]
  rw [show 20+d-4 = d+16 by omega, show 20+d-5 = d+15 by omega]
  nlinarith [Nat.zero_le (d*d*d), Nat.zero_le (d*d)]

end StableKneserK3

