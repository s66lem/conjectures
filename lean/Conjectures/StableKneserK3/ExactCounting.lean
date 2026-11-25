import Conjectures.StableKneserK3.Counting
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.IntervalCases

namespace StableKneserK3

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private abbrev mixed (s : Finset V) (x : V) :=
  x ∈ s ∧ (s.filter (G.Adj x)).card = 1

private theorem mixed_total (t : Finset V) (ht : t.card=3) (tri : ∀ a b c, G.Adj a b →
    G.Adj b c → ¬ G.Adj a c) :
    (t.filter (fun x => (t.filter (G.Adj x)).card = 1)).card =
      if t ∈ stableTriples G then 0 else 2 := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := card_eq_three.mp ht
  have cb : G.Adj c b ↔ G.Adj b c := G.adj_comm ..
  have ca : G.Adj c a ↔ G.Adj a c := G.adj_comm ..
  have ba : G.Adj b a ↔ G.Adj a b := G.adj_comm ..
  by_cases ab : G.Adj a b <;> by_cases ac : G.Adj a c <;> by_cases bc : G.Adj b c
  all_goals first
    | exact (tri a b c ab bc ac).elim
    | simp [stableTriples, filter_insert, filter_singleton, *]

private theorem mixed_fibre (x : V) :
    let N := G.neighborFinset x
    let O := (insert x N)ᶜ
    ((univ.powersetCard 3).filter (fun t => mixed G t x)).card = N.card * O.card := by
  classical
  let N := G.neighborFinset x
  let O := (insert x N)ᶜ
  let pair (p : V × V) : Finset V := {x,p.1,p.2}
  let P := N ×ˢ O
  let T := (univ.powersetCard 3).filter (fun t => mixed G t x)
  have props {p : V × V} (hp : p ∈ P) : G.Adj x p.1 ∧ x ≠ p.2 ∧ ¬ G.Adj x p.2 := by
    obtain ⟨h₁,h₂⟩ := mem_product.mp hp
    have hh : p.2 ≠ x ∧ ¬G.Adj x p.2 := by simpa [O,N] using h₂
    exact ⟨(G.mem_neighborFinset ..).mp h₁,hh.1.symm,hh.2⟩
  have distinct {p : V × V} (hp : p ∈ P) : p.1 ≠ p.2 := by
    intro e
    exact (props hp).2.2 (e ▸ (props hp).1)
  have img : P.image pair = T := by
    ext t
    constructor
    · rintro ht
      obtain ⟨p,hp,rfl⟩ := mem_image.mp ht
      obtain ⟨ha,hb,hn⟩ := props hp
      apply mem_filter.mpr
      refine ⟨mem_powersetCard.mpr ⟨subset_univ _,?_⟩,?_,?_⟩ <;>
        simp [pair,filter_insert,ha,hn,ha.ne,hb,distinct hp]
    · intro ht
      obtain ⟨ht,hm⟩ := mem_filter.mp ht
      obtain ⟨hx,hcard⟩ := hm
      obtain ⟨a,ha⟩ := card_eq_one.mp hcard
      have haa : a ∈ t ∧ G.Adj x a := mem_filter.mp (ha ▸ mem_singleton_self a)
      have htwo : (t.erase x).card=2 := by
        rw [card_erase_of_mem hx,(mem_powersetCard.mp ht).2]
      have hae := mem_erase.mpr ⟨haa.2.ne.symm,haa.1⟩
      have hone : ((t.erase x).erase a).card=1 := by rw [card_erase_of_mem hae,htwo]
      obtain ⟨b,hb⟩ := card_eq_one.mp hone
      have hmem : b ∈ (t.erase x).erase a := hb ▸ mem_singleton_self b
      obtain ⟨hba,hbx,hbt⟩ := (show b ≠ a ∧ b ≠ x ∧ b ∈ t by simpa using hmem)
      have hnb : ¬G.Adj x b := fun h => hba (mem_singleton.mp (ha ▸ mem_filter.mpr ⟨hbt,h⟩))
      refine mem_image.mpr ⟨(a,b),mem_product.mpr ⟨(G.mem_neighborFinset ..).mpr haa.2,?_⟩,?_⟩
      · simp [O,N,hbx,hnb]
      · change insert x (insert a {b}) = t
        rw [← hb,insert_erase hae,insert_erase hx]
  have injective : Set.InjOn pair P := by
    intro p hp q hq eq
    obtain ⟨ha,hb,hn⟩ := props hp
    obtain ⟨hA,hB,hN⟩ := props hq
    have h₁ : p.1 ∈ pair q := eq ▸ (by simp [pair])
    have h₂ : p.2 ∈ pair q := eq ▸ (by simp [pair])
    simp only [pair,mem_insert,mem_singleton] at h₁ h₂
    exact Prod.ext (by grind [Adj.ne]) (by grind)
  change T.card = N.card * O.card
  rw [← img,card_image_of_injOn injective,card_product]

theorem stableTriple_count_exact (hn : 5 ≤ Fintype.card V) (deg : ∀ v, G.degree v ≤ 2)
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c) :
    let n := Fintype.card V
    let leaves := (univ.filter (fun v => G.degree v = 1)).card
    let isolates := (univ.filter (fun v => G.degree v = 0)).card
    6*(stableTriples G).card =
      n*(n-4)*(n-5) + 3*(leaves + 2*isolates)*(n-4) + 6*isolates := by
  classical
  let n := Fintype.card V
  let allT := (univ : Finset V).powersetCard 3
  let bad := allT \ stableTriples G
  let leaves := (univ.filter (fun v => G.degree v = 1)).card
  let isolates := (univ.filter (fun v => G.degree v = 0)).card
  change 6*_ = n*(n-4)*(n-5)+3*(leaves+2*isolates)*(n-4)+6*isolates
  have count := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := mixed G) (s := allT) (t := (univ : Finset V))
  have lhs : (∑ t ∈ allT, (univ.bipartiteAbove (mixed G) t).card) = bad.card*2 := by
    have eq (t) (ht : t ∈ allT) :
        (univ.bipartiteAbove (mixed G) t).card = if t ∈ bad then 2 else 0 := by
      have H : univ.bipartiteAbove (mixed G) t = t.filter (fun x => (t.filter (G.Adj x)).card=1) := by
        ext v; simp only [bipartiteAbove,mem_filter,mem_univ,true_and,mixed]
      rw [H,mixed_total G _ (mem_powersetCard.mp ht).2 tri]
      simp [bad,ht]
    rw [sum_congr rfl eq]
    simp only [← sum_filter]
    have he : allT.filter (· ∈ bad) = bad := by ext t; simp [bad]
    simp [he]
  rw [lhs] at count
  let loss (v : V) := (if G.degree v = 1 then n-4 else 0) +
    (if G.degree v = 0 then 2*(n-3) else 0)
  have vertex (v : V) : (allT.bipartiteBelow (mixed G) v).card + loss v = 2*(n-3) := by
    change ((univ.powersetCard 3).filter _).card + _ = _
    rw [mixed_fibre G]
    simp only [card_compl,card_insert_of_notMem (G.notMem_neighborFinset_self v),card_neighborFinset_eq_degree]
    have hd := deg v
    have h5 : 5 ≤ n := hn
    change G.degree v * (n - (G.degree v + 1)) + loss v = _
    interval_cases h : G.degree v <;> (simp [loss,h]; try omega)
  have vcount := sum_congr (s₁ := (univ : Finset V)) rfl (fun v _ => vertex v)
  rw [sum_add_distrib, ← count] at vcount
  simp only [loss,sum_add_distrib, ← sum_filter,sum_const,smul_eq_mul,card_univ] at vcount
  change bad.card*2 + (leaves*(n-4) + isolates*(2*(n-3))) = n*(2*(n-3)) at vcount
  have htotal : bad.card + (stableTriples G).card = n.choose 3 := by
    calc
      _ = allT.card := card_sdiff_add_card_eq_card (filter_subset _ _)
      _ = _ := by simp [allT,n]
  have hchoose := Nat.descFactorial_eq_factorial_mul_choose n 3
  simp [Nat.descFactorial_succ,Nat.factorial] at hchoose
  obtain ⟨j,he⟩ := Nat.exists_eq_add_of_le (show 5 ≤ n from hn)
  rw [he] at vcount htotal hchoose ⊢
  simp only [show 5+j-3=j+2 by omega,show 5+j-4=j+1 by omega,show 5+j-5=j by omega,
    show 5+j-1=j+4 by omega,show 5+j-2=j+3 by omega] at *
  nlinarith only [vcount,htotal,hchoose]

end StableKneserK3
