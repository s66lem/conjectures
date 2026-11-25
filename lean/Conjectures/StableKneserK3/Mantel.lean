import Conjectures.StableKneserK3.Anchors
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic.Linarith

namespace StableKneserK3

open Finset SimpleGraph
open scoped Sym2

variable {V : Type*} [Fintype V]

private theorem mantel (J : SimpleGraph V) [DecidableRel J.Adj] (hf : J.CliqueFree 3) :
    4 * J.edgeFinset.card ≤ (Fintype.card V)^2 := by
  have h := CliqueFree.card_edgeFinset_le (r := 2) hf
  have hm : Fintype.card V % 2 < 2 := Nat.mod_lt _ (by decide)
  have hz := Nat.choose_eq_zero_of_lt hm
  simp [hz] at h
  omega

/-- Count the edges of the graph formed by the ground edges and the pairs of the anchors. -/
theorem anchor_mantel_bound (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}
    (hcol : Colorable (withIsolate G) q) (hmin : ¬ Colorable G (q-1)) :
    4 * (Fintype.card V).choose 2 ≤ 4 * (G.edgeFinset.card + 3*q) + (Fintype.card V)^2 := by
  classical
  obtain ⟨c, hc⟩ := hcol
  obtain ⟨A, hA⟩ := exists_anchors c hc hmin
  let P (i : Fin q) := (⊤ : SimpleGraph (A i).val).map (Function.Embedding.subtype (· ∈ (A i).val))
  let E := G.edgeFinset ∪ univ.biUnion (fun i => (P i).edgeFinset)
  let H := fromEdgeSet (E : Set (Sym2 V))
  have hG : G ≤ H := by
    intro x y h
    exact ⟨mem_union_left _ ((G.mem_edgeFinset).mpr h), h.ne⟩
  have hf : Hᶜ.CliqueFree 3 := by
    intro t ht
    have hstable : StableTriple G t := by
      refine ⟨ht.card_eq, fun x hx y hy h => ?_⟩
      exact (ht.isClique hx hy h.ne).2 (hG h)
    let s : Triple G := ⟨t, hstable⟩
    let i := c (onBase s)
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (hA s)
    obtain ⟨hxt, hxa⟩ := mem_inter.mp hx
    obtain ⟨hyt, hya⟩ := mem_inter.mp hy
    have hp : (P i).Adj x y := SimpleGraph.map_adj_apply.mpr (show
      (⊤ : SimpleGraph (A i).val).Adj ⟨x,hxa⟩ ⟨y,hya⟩ from fun h => hxy (congrArg Subtype.val h))
    have he : s(x,y) ∈ E := mem_union_right _ (mem_biUnion.mpr
      ⟨i, mem_univ i, (P i).mem_edgeFinset.mpr hp⟩)
    exact (ht.isClique hxt hyt hxy).2 ⟨he,hxy⟩
  have hedges : H.edgeFinset ⊆ E := by
    intro e he
    exact (edgeSet_fromEdgeSet _ ▸ H.mem_edgeFinset.mp he).1
  have hthree (i : Fin q) : (P i).edgeFinset.card = 3 := by
    dsimp only [P]
    rw [card_edgeFinset_map, card_edgeFinset_top_eq_card_choose_two, Fintype.card_coe, (A i).property.1]
    decide
  have hcount : H.edgeFinset.card ≤ G.edgeFinset.card + 3*q := calc
    _ ≤ E.card := card_le_card hedges
    _ ≤ _ := card_union_le _ _
    _ ≤ G.edgeFinset.card + ∑ i : Fin q, (P i).edgeFinset.card := Nat.add_le_add_left card_biUnion_le _
    _ = _ := by simp [hthree, Nat.mul_comm]
  have htotal : (Fintype.card V).choose 2 ≤ H.edgeFinset.card + Hᶜ.edgeFinset.card := by
    calc
      _ = (⊤ : SimpleGraph V).edgeFinset.card := card_edgeFinset_top_eq_card_choose_two.symm
      _ = (H.edgeFinset ∪ Hᶜ.edgeFinset).card := by
        congr 1
        ext e
        induction e using Sym2.ind with
        | _ x y => simp [SimpleGraph.mem_edgeFinset, SimpleGraph.compl_adj]; grind [Adj.ne]
      _ ≤ _ := card_union_le _ _
  have hm := mantel Hᶜ hf
  omega

/-- The cycle-plus-isolate conclusion for large cycles, given the lower bound on the cycle. -/
theorem tight_withIsolate_of_cycle_lower {m : ℕ} (hm : 15 ≤ m)
    (hcycle : ¬ Colorable (cycleGraph m) (m-5)) : K3Tight (withIsolate (cycleGraph m)) := by
  have hn : Fintype.card (Fin m ⊕ Unit) = m+1 := by simp
  refine ⟨?_, upper_bound _ (by omega)⟩
  rw [hn, show m+1-5=m-4 by omega]
  intro hc
  have hmin : ¬ Colorable (cycleGraph m) (m-4-1) := by
    rwa [show m-4-1=m-5 by omega]
  have h := anchor_mantel_bound _ hc hmin
  have he : (cycleGraph m).edgeFinset.card = m := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' (show 3 ≤ m by omega)
    have hsum := (cycleGraph (t+3)).sum_degrees_eq_twice_card_edges
    simp [cycleGraph_degree_three_le] at hsum
    omega
  rw [Fintype.card_fin, he, Nat.choose_two_right] at h
  have h2 : 2 ∣ m*(m-1) := (Nat.even_mul_pred_self m).two_dvd
  have hd := Nat.div_mul_cancel h2
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show 15+t-1=t+14 by omega] at hd
  rw [show 15+t-1=t+14 by omega, show 15+t-4=t+11 by omega] at h
  nlinarith [Nat.zero_le (t*t)]

end StableKneserK3

