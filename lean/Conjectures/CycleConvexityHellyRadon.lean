import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# Disproof of the Cycle Convexity Helly–Radon Conjecture (arXiv:2609.34236v1)

This file formalizes the refutation of Conjecture 1 of R. S. Nair, B. S. Anand,
Ullas Chandran S. V., J. R. Nascimento, and A. Anil, *Computing the Helly Number,
Radon Number and Rank in Cycle Convexity*, arXiv:2609.34236v1 (2026), Section 5
("Conclusion"), which asks whether `hl_cc(G) = rd_cc(G)` for every connected graph
`G` of order `n ≥ 2`.

We prove:
1. For every finite graph `G`, `hellyNumber G ≤ radonNumber G`.
2. For an explicit 16-vertex, 36-edge connected graph `G16` (three `K_5` cliques
   `K^(0), K^(1), K^(2)`, a central vertex `x = 15` joined to one vertex `u_i` in
   each clique, and three cyclic port edges `p_i - q_{i+1}`):
   - `G16.Connected`,
   - `hellyNumber G16 = 5`,
   - `radonNumber G16 = 6`.
3. Consequently, Conjecture 1 is false (`hellyNumber G16 < radonNumber G16`).
-/

namespace CycleConvexityHellyRadon

open SimpleGraph

/-! ### Cycle convexity, Helly number, and Radon number -/

/-- A vertex `w` belongs to the cycle interval `I_{cc}(S)` if `w ∈ S` or `w` lies on
a cycle of `G` whose other vertices all lie in `S`. -/
def cycleInterval {V : Type*} (G : SimpleGraph V) (S : Set V) : Set V :=
  {w | w ∈ S ∨ ∃ c : G.Walk w w, c.IsCycle ∧ ∀ z ∈ c.support, z = w ∨ z ∈ S}

/-- A vertex set `W` is cycle convex if `I_{cc}(W) = W`. -/
def IsCycleConvex {V : Type*} (G : SimpleGraph V) (W : Set V) : Prop :=
  cycleInterval G W = W

/-- The cycle convex hull `Hull_{cc}(S)` is the intersection of all cycle convex
sets containing `S`. -/
def cycleHull {V : Type*} (G : SimpleGraph V) (S : Set V) : Set V :=
  ⋂₀ {W : Set V | S ⊆ W ∧ IsCycleConvex G W}

/-- `S` is Helly independent in cycle convexity if `⋂_{a ∈ S} Hull_{cc}(S \ {a}) = ∅`. -/
def IsHellyIndep {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ v : V, ∃ a ∈ S, v ∉ cycleHull G (S \ {a})

/-- `S` is Radon independent in cycle convexity if no bipartition `{A, B}` of `S`
has `Hull_{cc}(A) ∩ Hull_{cc}(B) ≠ ∅`. -/
def IsRadonIndep {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ A B : Set V, A ⊆ S → B ⊆ S → A ∪ B = S → Disjoint A B →
    A.Nonempty → B.Nonempty → Disjoint (cycleHull G A) (cycleHull G B)

open Classical in
/-- The cycle Helly number `hl_{cc}(G)`: maximum cardinality of a Helly-independent set. -/
noncomputable def hellyNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter fun S : Finset V => IsHellyIndep G (S : Set V)).sup Finset.card

open Classical in
/-- The cycle Radon number `rd_{cc}(G)`: maximum cardinality of a Radon-independent set. -/
noncomputable def radonNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter fun S : Finset V => IsRadonIndep G (S : Set V)).sup Finset.card

/-! ### Basic properties of cycle intervals, hulls, and the Levi inequality -/

lemma subset_cycleInterval {V : Type*} (G : SimpleGraph V) (S : Set V) :
    S ⊆ cycleInterval G S :=
  fun _ hw => Or.inl hw

lemma isCycleConvex_iff {V : Type*} (G : SimpleGraph V) (W : Set V) :
    IsCycleConvex G W ↔ cycleInterval G W ⊆ W := by
  constructor
  · intro h; rw [h]
  · intro h; exact Set.Subset.antisymm h (subset_cycleInterval G W)

lemma subset_cycleHull {V : Type*} (G : SimpleGraph V) (S : Set V) :
    S ⊆ cycleHull G S := by
  intro x hx W hW
  exact hW.1 hx

lemma cycleHull_mono {V : Type*} (G : SimpleGraph V) {S T : Set V} (hST : S ⊆ T) :
    cycleHull G S ⊆ cycleHull G T := by
  intro x hx W hW
  exact hx W ⟨hST.trans hW.1, hW.2⟩

lemma cycleHull_minimal {V : Type*} (G : SimpleGraph V) {S W : Set V}
    (hSW : S ⊆ W) (hW : IsCycleConvex G W) : cycleHull G S ⊆ W :=
  fun _ hx => hx W ⟨hSW, hW⟩

lemma isCycleConvex_cycleHull {V : Type*} (G : SimpleGraph V) (S : Set V) :
    IsCycleConvex G (cycleHull G S) := by
  rw [isCycleConvex_iff]
  intro w hw W hW
  rcases hw with hw | ⟨c, hc, hsupp⟩
  · exact hw W hW
  · rw [← hW.2]
    refine Or.inr ⟨c, hc, fun z hz => ?_⟩
    rcases hsupp z hz with rfl | hzH
    · exact Or.inl rfl
    · exact Or.inr (hzH W hW)

lemma mem_cycleHull_of_cycle {V : Type*} (G : SimpleGraph V) {S : Set V} {w : V}
    (c : G.Walk w w) (hc : c.IsCycle) (hsupp : ∀ z ∈ c.support, z = w ∨ z ∈ cycleHull G S) :
    w ∈ cycleHull G S := by
  have hconv := (isCycleConvex_iff G (cycleHull G S)).mp (isCycleConvex_cycleHull G S)
  exact hconv (Or.inr ⟨c, hc, hsupp⟩)

/-- If `w` is adjacent to two distinct adjacent vertices `u, v ∈ cycleHull G S`, then
`w ∈ cycleHull G S` via the triangle `w - u - v - w`. -/
lemma mem_cycleHull_of_adj_edge {V : Type*} (G : SimpleGraph V) {S : Set V} {w u v : V}
    (hu : u ∈ cycleHull G S) (hv : v ∈ cycleHull G S)
    (hwu : G.Adj w u) (huv : G.Adj u v) (hvw : G.Adj v w) :
    w ∈ cycleHull G S := by
  let c : G.Walk w w := Walk.cons hwu (Walk.cons huv (Walk.cons hvw Walk.nil))
  have htrail : c.IsTrail := by
    refine Walk.IsTrail.mk ?_
    simp [c, SimpleGraph.Walk.edges_cons, hwu.ne, huv.ne, hvw.ne, hwu.ne.symm, hvw.ne.symm]
  have hcirc : c.IsCircuit := Walk.IsCircuit.mk htrail (by simp [c])
  have hc : c.IsCycle := Walk.IsCycle.mk hcirc (by simp [c, huv.ne, hvw.ne, hwu.ne.symm])
  refine mem_cycleHull_of_cycle G c hc ?_
  intro z hz
  simp only [c, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr hu
  · exact Or.inr hv
  · exact Or.inl rfl

/-- If `w` is adjacent to `u₁, u₂` and `u₁ - a - b - u₂` is a 4-vertex path in `cycleHull G S`
with all 5 vertices `w, u₁, a, b, u₂` pairwise distinct, then `w ∈ cycleHull G S`. -/
lemma mem_cycleHull_of_five_cycle {V : Type*} (G : SimpleGraph V) {S : Set V}
    {w u₁ a b u₂ : V}
    (hu₁ : u₁ ∈ cycleHull G S) (ha : a ∈ cycleHull G S)
    (hb : b ∈ cycleHull G S) (hu₂ : u₂ ∈ cycleHull G S)
    (h1 : G.Adj w u₁) (h2 : G.Adj u₁ a) (h3 : G.Adj a b) (h4 : G.Adj b u₂) (h5 : G.Adj u₂ w)
    (hnd : [u₁, a, b, u₂, w].Nodup) :
    w ∈ cycleHull G S := by
  let c : G.Walk w w :=
    Walk.cons h1 (Walk.cons h2 (Walk.cons h3 (Walk.cons h4 (Walk.cons h5 Walk.nil))))
  have htail : c.support.tail.Nodup := by simpa [c] using hnd
  have htrail : c.IsTrail := by
    refine Walk.IsTrail.mk ?_
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    rcases hnd with ⟨⟨hu1a, hu1b, hu1u2, hu1w⟩, ⟨hab, hau2, haw⟩, ⟨hbu2, hbw⟩, hu2w, _⟩
    simp [c, SimpleGraph.Walk.edges_cons,
      hu1a, hu1b, hu1u2, hu1w, hab, hau2, haw, hbu2, hbw, hu2w,
      Ne.symm hu1w, Ne.symm haw, Ne.symm hbw, Ne.symm hu2w]
  have hcirc : c.IsCircuit := Walk.IsCircuit.mk htrail (by simp [c])
  have hc : c.IsCycle := Walk.IsCycle.mk hcirc htail
  refine mem_cycleHull_of_cycle G c hc ?_
  intro z hz
  simp only [c, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr hu₁
  · exact Or.inr ha
  · exact Or.inr hb
  · exact Or.inr hu₂
  · exact Or.inl rfl

/-- Characterization of `w ∈ cycleInterval G W` for `w ∉ W`: `w` must have two distinct
neighbors `u ≠ v` in `W` that are joined by a walk inside `G.induce W`. -/
lemma cycle_gives_two_reachable_nbrs {V : Type*} {G : SimpleGraph V} {W : Set V} {w : V}
    (hw : w ∉ W) (c : G.Walk w w) (hc : c.IsCycle) (hsupp : ∀ z ∈ c.support, z = w ∨ z ∈ W) :
    ∃ u v : V, ∃ hu : u ∈ W, ∃ hv : v ∈ W, u ≠ v ∧ G.Adj w u ∧ G.Adj w v ∧
      (G.induce W).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  cases c with
  | nil => exact False.elim (hc.ne_nil rfl)
  | cons hwu p =>
    rename_i u
    have htail : p.support.Nodup := by simpa [Walk.support_cons] using hc.support_nodup
    have hp_len : 2 ≤ p.length := by
      have h3 := hc.three_le_length
      simp only [Walk.length_cons] at h3
      omega
    have hu_ne_w : u ≠ w := hwu.ne.symm
    have huW : u ∈ W := by
      have := hsupp u (by simp [Walk.support_cons])
      exact this.resolve_left hu_ne_w
    -- Peel the last edge `v - w` from `p : G.Walk u w`
    have hp_ne_nil : ¬ p.Nil := by
      cases p with
      | nil => simp at hp_len
      | cons _ _ => simp
    let v : V := p.penultimate
    let q : G.Walk u v := p.dropLast
    have hvw : G.Adj v w := p.adj_penultimate hp_ne_nil
    have hp_eq : p = q.concat hvw := (Walk.concat_dropLast hvw).symm
    have hv_ne_w : v ≠ w := hvw.ne
    have hvW : v ∈ W := by
      have hv_mem : v ∈ p.support := by
        rw [hp_eq, Walk.support_concat]
        exact List.mem_append_left _ (Walk.end_mem_support q)
      have := hsupp v (by simp [Walk.support_cons, hv_mem])
      exact this.resolve_left hv_ne_w
    have hq_len : 1 ≤ q.length := by
      have hlen : p.length = q.length + 1 := by
        rw [hp_eq, Walk.length_concat]
      omega
    have hq_supp_eq : p.support = q.support ++ [w] := by
      rw [hp_eq, Walk.support_concat]
    have huv : u ≠ v := by
      intro heq
      have hnot_nodup : ∀ {x y : V} (r : G.Walk x y), 1 ≤ r.length → x = y → ¬ r.support.Nodup := by
        rintro x _ r hr rfl
        cases r with
        | nil => simp at hr
        | cons _ r' =>
          simp only [Walk.support_cons, List.nodup_cons]
          intro ⟨hnot, _⟩
          exact hnot (Walk.end_mem_support r')
      rw [hq_supp_eq] at htail
      exact hnot_nodup q hq_len heq (List.Nodup.of_append_left htail)
    have hq_in_W : ∀ z ∈ q.support, z ∈ W := by
      intro z hz
      have hz_p : z ∈ p.support := by rw [hq_supp_eq]; exact List.mem_append_left _ hz
      have hz_ne_w : z ≠ w := by
        intro hzw
        subst hzw
        rw [hq_supp_eq] at htail
        have hdisj := List.disjoint_of_nodup_append htail
        exact hdisj hz (List.mem_singleton_self _)
      exact (hsupp z (by simp [Walk.support_cons, hz_p])).resolve_left hz_ne_w
    have hreach : (G.induce W).Reachable ⟨u, huW⟩ ⟨v, hvW⟩ := by
      refine ⟨Walk.induce W q hq_in_W⟩
    exact ⟨u, v, huW, hvW, huv, hwu, hvw.symm, hreach⟩

/-- Convenience criterion for cycle convexity: if every `w ∉ W` fails to have two distinct
neighbors in `W` connected within `G.induce W`, then `W` is cycle convex. -/
lemma isCycleConvex_of_no_two_reachable_nbrs {V : Type*} {G : SimpleGraph V} {W : Set V}
    (h : ∀ w ∉ W, ∀ u v : V, ∀ hu : u ∈ W, ∀ hv : v ∈ W,
      u ≠ v → G.Adj w u → G.Adj w v → ¬ (G.induce W).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    IsCycleConvex G W := by
  rw [isCycleConvex_iff]
  intro w hw
  rcases hw with hw | ⟨c, hc, hsupp⟩
  · exact hw
  · by_contra hnot
    obtain ⟨u, v, hu, hv, huv, hwu, hwv, hreach⟩ :=
      cycle_gives_two_reachable_nbrs hnot c hc hsupp
    exact h w hnot u v hu hv huv hwu hwv hreach

/-- **General Levi inequality for cycle convexity:** every Helly-independent set is
Radon-independent. -/
lemma isRadonIndep_of_isHellyIndep {V : Type*} {G : SimpleGraph V} {S : Set V}
    (hH : IsHellyIndep G S) : IsRadonIndep G S := by
  intro A B hAS hBS hAB hdisj _ _
  rw [Set.disjoint_left]
  intro v hvA hvB
  obtain ⟨a, haS, haNot⟩ := hH v
  have ha_cases : a ∈ A ∨ a ∈ B := by rwa [← hAB] at haS
  rcases ha_cases with haA | haB
  · have hBsub : B ⊆ S \ {a} := by
      intro x hxB
      refine ⟨hBS hxB, ?_⟩
      intro hxa
      subst hxa
      exact Set.disjoint_left.mp hdisj haA hxB
    exact haNot (cycleHull_mono G hBsub hvB)
  · have hAsub : A ⊆ S \ {a} := by
      intro x hxA
      refine ⟨hAS hxA, ?_⟩
      intro hxa
      subst hxa
      exact Set.disjoint_left.mp hdisj hxA haB
    exact haNot (cycleHull_mono G hAsub hvA)

/-- **Theorem (General Bound):** For every finite graph `G`, `hl_{cc}(G) ≤ rd_{cc}(G)`. -/
theorem hellyNumber_le_radonNumber {V : Type*} [Fintype V] (G : SimpleGraph V) :
    hellyNumber G ≤ radonNumber G := by
  classical
  unfold hellyNumber radonNumber
  refine Finset.sup_mono ?_
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
  exact isRadonIndep_of_isHellyIndep hS

/-- Any set containing a triangle (three pairwise adjacent vertices) is Helly dependent. -/
lemma not_isHellyIndep_of_triangle {V : Type*} {G : SimpleGraph V} {S : Set V}
    {a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    ¬ IsHellyIndep G S := by
  intro hH
  obtain ⟨z, hzS, hzNot⟩ := hH a
  by_cases hza : z = a
  · subst hza
    have hb' : b ∈ cycleHull G (S \ {z}) :=
      subset_cycleHull G _ ⟨hb, hab.ne.symm⟩
    have hc' : c ∈ cycleHull G (S \ {z}) :=
      subset_cycleHull G _ ⟨hc, hca.ne⟩
    exact hzNot (mem_cycleHull_of_adj_edge G hb' hc' hab hbc hca)
  · exact hzNot (subset_cycleHull G _ ⟨ha, fun h => hza h.symm⟩)

/-- Any set containing a triangle is also Radon dependent. -/
lemma not_isRadonIndep_of_triangle {V : Type*} {G : SimpleGraph V} {S : Set V}
    {a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    ¬ IsRadonIndep G S := by
  intro hR
  have hAsub : ({a} : Set V) ⊆ S := Set.singleton_subset_iff.mpr ha
  have hBsub : S \ {a} ⊆ S := Set.sdiff_subset
  have hAB : ({a} : Set V) ∪ (S \ {a}) = S := Set.union_sdiff_cancel hAsub
  have hdisj : Disjoint ({a} : Set V) (S \ {a}) := disjoint_sdiff_self_right
  have hAne : ({a} : Set V).Nonempty := Set.singleton_nonempty a
  have hBne : (S \ {a}).Nonempty := ⟨b, hb, hab.ne.symm⟩
  have hdisjHull := hR {a} (S \ {a}) hAsub hBsub hAB hdisj hAne hBne
  have haA : a ∈ cycleHull G {a} := subset_cycleHull G _ (Set.mem_singleton a)
  have hbB : b ∈ cycleHull G (S \ {a}) := subset_cycleHull G _ ⟨hb, hab.ne.symm⟩
  have hcB : c ∈ cycleHull G (S \ {a}) := subset_cycleHull G _ ⟨hc, hca.ne⟩
  have haB : a ∈ cycleHull G (S \ {a}) := mem_cycleHull_of_adj_edge G hbB hcB hab hbc hca
  exact Set.disjoint_left.mp hdisjHull haA haB

/-! ### The 16-vertex counterexample graph `G16` -/

/-- Adjacency predicate for `G16` on `Fin 16`.
Vertices `5*i + r` (`i ∈ {0,1,2}`, `r ∈ {0,1,2,3,4}`) are `s_i, t_i, u_i, p_i, q_i`
in clique `K^(i) ≅ K_5`; vertex `15` is the central vertex `x` adjacent to `u_0, u_1, u_2`;
port edges connect `p_i = 5*i + 3` to `q_{i+1} = 5*((i+1)%3) + 4`. -/
def adj16 (a b : Fin 16) : Prop :=
  a ≠ b ∧
    ((a.val < 15 ∧ b.val < 15 ∧ a.val / 5 = b.val / 5) ∨
     (a.val = 15 ∧ (b.val = 2 ∨ b.val = 7 ∨ b.val = 12)) ∨
     (b.val = 15 ∧ (a.val = 2 ∨ a.val = 7 ∨ a.val = 12)) ∨
     (a.val = 3 ∧ b.val = 9) ∨ (a.val = 9 ∧ b.val = 3) ∨
     (a.val = 8 ∧ b.val = 14) ∨ (a.val = 14 ∧ b.val = 8) ∨
     (a.val = 13 ∧ b.val = 4) ∨ (a.val = 4 ∧ b.val = 13))

/-- The 16-vertex, 36-edge connected counterexample graph `G16`. -/
def G16 : SimpleGraph (Fin 16) where
  Adj := adj16
  symm := ⟨fun a b h => by
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with ⟨ha, hb, hd⟩ | h | h | h | h | h | h | h | h <;>
      first
      | exact Or.inl ⟨hb, ha, hd.symm⟩
      | (right; tauto)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Vertex `x = 15` (the central hub). -/
def vx : Fin 16 := 15

/-- The `i`-th `K_5` clique (`i : Fin 3`): `{5*i, 5*i+1, 5*i+2, 5*i+3, 5*i+4}`. -/
def cliqueFinset (i : Fin 3) : Finset (Fin 16) :=
  Finset.univ.filter fun v : Fin 16 => v.val < 15 ∧ v.val / 5 = i.val

/-- The 6-vertex witness set `S = {s_0, t_0, s_1, t_1, s_2, t_2} = {0, 1, 5, 6, 10, 11}`. -/
def witnessS : Finset (Fin 16) :=
  {0, 1, 5, 6, 10, 11}

/-- The 5-vertex Helly-independent witness `{0, 1, 5, 6, 10}`. -/
def witnessH5 : Finset (Fin 16) :=
  {0, 1, 5, 6, 10}

lemma G16_connected : G16.Connected := by
  refine Connected.mk ?_
  have hto_x : ∀ w : Fin 16, G16.Reachable w vx := by
    intro w
    by_cases hwx : w = vx
    · subst hwx; exact Reachable.refl _
    · have hwlt : w.val < 15 := by
        have : w.val ≠ 15 := fun h => hwx (Fin.ext h)
        omega
      let u : Fin 16 := ⟨5 * (w.val / 5) + 2, by omega⟩
      have hux : G16.Adj u vx := by
        refine ⟨by intro h; have := congrArg Fin.val h; dsimp only [u, vx] at this; omega, ?_⟩
        right; right; left
        refine ⟨rfl, ?_⟩
        change 5 * (w.val / 5) + 2 = 2 ∨ 5 * (w.val / 5) + 2 = 7 ∨ 5 * (w.val / 5) + 2 = 12
        omega
      by_cases hwu : w = u
      · rw [hwu]; exact hux.reachable
      · have hwadj : G16.Adj w u := by
          refine ⟨hwu, Or.inl ⟨hwlt, ?_, ?_⟩⟩
          · change 5 * (w.val / 5) + 2 < 15; omega
          · change w.val / 5 = (5 * (w.val / 5) + 2) / 5; omega
        exact hwadj.reachable.trans hux.reachable
  intro u v
  exact (hto_x u).trans (hto_x v).symm

lemma G16_clique_adj {i : Fin 3} {a b : Fin 16}
    (ha : a ∈ cliqueFinset i) (hb : b ∈ cliqueFinset i) (hab : a ≠ b) :
    G16.Adj a b := by
  simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact ⟨hab, Or.inl ⟨ha.1, hb.1, ha.2.trans hb.2.symm⟩⟩

/-- Any two distinct vertices in clique `K^(i)` generate the entire clique `K^(i)`. -/
lemma clique_subset_cycleHull_of_two {A : Set (Fin 16)} {i : Fin 3} {a b : Fin 16}
    (haA : a ∈ A) (hbA : b ∈ A) (ha : a ∈ cliqueFinset i) (hb : b ∈ cliqueFinset i)
    (hab : a ≠ b) :
    (cliqueFinset i : Set (Fin 16)) ⊆ cycleHull G16 A := by
  intro w hw
  by_cases hwa : w = a
  · subst hwa; exact subset_cycleHull G16 A haA
  · by_cases hwb : w = b
    · subst hwb; exact subset_cycleHull G16 A hbA
    · exact mem_cycleHull_of_adj_edge G16
        (subset_cycleHull G16 A haA) (subset_cycleHull G16 A hbA)
        (G16_clique_adj hw ha hwa) (G16_clique_adj ha hb hab) (G16_clique_adj hb hw (Ne.symm hwb))

/-- If `cycleHull G16 A` contains two distinct full cliques `K^(i)` and `K^(j)`, then
it also contains the central hub `x = 15`. -/
lemma vx_mem_cycleHull_of_two_cliques {A : Set (Fin 16)} {i j : Fin 3} (hij : i ≠ j)
    (hi : (cliqueFinset i : Set (Fin 16)) ⊆ cycleHull G16 A)
    (hj : (cliqueFinset j : Set (Fin 16)) ⊆ cycleHull G16 A) :
    vx ∈ cycleHull G16 A := by
  -- Either `j = i + 1 (mod 3)` or `i = j + 1 (mod 3)`, so a port edge `p - q` connects them.
  have hstep : ∀ k : Fin 3,
      (cliqueFinset k : Set (Fin 16)) ⊆ cycleHull G16 A →
      (cliqueFinset ⟨(k.val + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Set (Fin 16)) ⊆ cycleHull G16 A →
      vx ∈ cycleHull G16 A := by
    intro k hk1 hk2
    fin_cases k
    · exact mem_cycleHull_of_five_cycle G16
        (hk1 (by simp [cliqueFinset] : (2 : Fin 16) ∈ cliqueFinset 0))
        (hk1 (by simp [cliqueFinset] : (3 : Fin 16) ∈ cliqueFinset 0))
        (hk2 (by simp [cliqueFinset] : (9 : Fin 16) ∈ cliqueFinset 1))
        (hk2 (by simp [cliqueFinset] : (7 : Fin 16) ∈ cliqueFinset 1))
        (by simp [G16, adj16, vx]) (by simp [G16, adj16]) (by simp [G16, adj16])
        (by simp [G16, adj16]) (by simp [G16, adj16, vx]) (by decide)
    · exact mem_cycleHull_of_five_cycle G16
        (hk1 (by simp [cliqueFinset] : (7 : Fin 16) ∈ cliqueFinset 1))
        (hk1 (by simp [cliqueFinset] : (8 : Fin 16) ∈ cliqueFinset 1))
        (hk2 (by simp [cliqueFinset] : (14 : Fin 16) ∈ cliqueFinset 2))
        (hk2 (by simp [cliqueFinset] : (12 : Fin 16) ∈ cliqueFinset 2))
        (by simp [G16, adj16, vx]) (by simp [G16, adj16]) (by simp [G16, adj16])
        (by simp [G16, adj16]) (by simp [G16, adj16, vx]) (by decide)
    · exact mem_cycleHull_of_five_cycle G16
        (hk1 (by simp [cliqueFinset] : (12 : Fin 16) ∈ cliqueFinset 2))
        (hk1 (by simp [cliqueFinset] : (13 : Fin 16) ∈ cliqueFinset 2))
        (hk2 (by simp [cliqueFinset] : (4 : Fin 16) ∈ cliqueFinset 0))
        (hk2 (by simp [cliqueFinset] : (2 : Fin 16) ∈ cliqueFinset 0))
        (by simp [G16, adj16, vx]) (by simp [G16, adj16]) (by simp [G16, adj16])
        (by simp [G16, adj16]) (by simp [G16, adj16, vx]) (by decide)
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact hstep 0 hi hj
  · exact hstep 2 hj hi
  · exact hstep 0 hj hi
  · exact False.elim (hij rfl)
  · exact hstep 1 hi hj
  · exact hstep 2 hi hj
  · exact hstep 1 hj hi
  · exact False.elim (hij rfl)

/-! ### Exact convex hull characterization for subsets of `witnessS` -/

/-- The explicit closed set `W_A` for `A ⊆ witnessS`:
full clique `K^(i)` whenever both `s_i, t_i ∈ A`, plus `A`, plus `{x}` iff at least
two cliques are full. -/
def closedHullModel (A : Set (Fin 16)) : Set (Fin 16) :=
  {v | v ∈ A ∨
       (∃ i : Fin 3, ⟨5 * i.val, by omega⟩ ∈ A ∧ ⟨5 * i.val + 1, by omega⟩ ∈ A ∧
         v ∈ cliqueFinset i) ∨
       (v = vx ∧ ∃ i j : Fin 3, i ≠ j ∧
         ⟨5 * i.val, by omega⟩ ∈ A ∧ ⟨5 * i.val + 1, by omega⟩ ∈ A ∧
         ⟨5 * j.val, by omega⟩ ∈ A ∧ ⟨5 * j.val + 1, by omega⟩ ∈ A)}

private lemma G16_vx_nbrs : ∀ u : Fin 16, G16.Adj vx u → u = 2 ∨ u = 7 ∨ u = 12 := by
  intro u ⟨_, h⟩
  dsimp only [vx] at h
  rcases h with ⟨h15, _, _⟩ | ⟨_, h2 | h7 | h12⟩ | ⟨h15, _⟩ | ⟨h3, _⟩ | ⟨h9, _⟩ | ⟨h8, _⟩ | ⟨h14, _⟩ | ⟨h13, _⟩ | ⟨h4, _⟩
  · exact False.elim (by omega)
  · left; exact Fin.ext h2
  · right; left; exact Fin.ext h7
  · right; right; exact Fin.ext h12
  · exact False.elim (by omega)
  · exact False.elim (by omega)
  · exact False.elim (by omega)
  · exact False.elim (by omega)
  · exact False.elim (by omega)
  · exact False.elim (by omega)
  · exact False.elim (by omega)

private lemma witnessS_mod5 :
    ∀ z : Fin 16, z ∈ witnessS → z.val < 15 ∧ (z.val % 5 = 0 ∨ z.val % 5 = 1) := by
  intro z hz
  simp only [witnessS, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

private lemma G16_st_adj_same_clique :
    ∀ z y : Fin 16, z ∈ witnessS → G16.Adj z y → y.val < 15 ∧ y.val / 5 = z.val / 5 := by
  intro z y hz ⟨_, hzy⟩
  have hm := witnessS_mod5 z hz
  rcases hzy with ⟨_, hy, hd⟩ | ⟨h15, _⟩ | ⟨_, h2 | h7 | h12⟩ | ⟨h3, _⟩ | ⟨h9, _⟩ | ⟨h8, _⟩ | ⟨h14, _⟩ | ⟨h13, _⟩ | ⟨h4, _⟩
  · exact ⟨hy, hd.symm⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private def outNbrVal (w : ℕ) : ℕ :=
  match w with
  | 2 | 7 | 12 => 15
  | 3 => 9
  | 9 => 3
  | 8 => 14
  | 14 => 8
  | 13 => 4
  | 4 => 13
  | _ => 0

private lemma G16_out_nbr_val (w y : Fin 16) (hw : w.val < 15)
    (hnot : ¬ (y.val < 15 ∧ y.val / 5 = w.val / 5)) (ha : G16.Adj w y) :
    y.val = outNbrVal w.val := by
  rcases ha with ⟨_, h⟩
  rcases h with ⟨_, hy, hd⟩ | ⟨h15, _⟩ | ⟨hy15, h2 | h7 | h12⟩ | ⟨hw3, hy9⟩ | ⟨hw9, hy3⟩ | ⟨hw8, hy14⟩ | ⟨hw14, hy8⟩ | ⟨hw13, hy4⟩ | ⟨hw4, hy13⟩
  · exact False.elim (hnot ⟨hy, hd.symm⟩)
  · omega
  · rw [h2, hy15]; rfl
  · rw [h7, hy15]; rfl
  · rw [h12, hy15]; rfl
  · rw [hw3, hy9]; rfl
  · rw [hw9, hy3]; rfl
  · rw [hw8, hy14]; rfl
  · rw [hw14, hy8]; rfl
  · rw [hw13, hy4]; rfl
  · rw [hw4, hy13]; rfl

private lemma G16_out_nbr_unique
    (w y₁ y₂ : Fin 16) (hw : w.val < 15)
    (h1 : ¬ (y₁.val < 15 ∧ y₁.val / 5 = w.val / 5))
    (h2 : ¬ (y₂.val < 15 ∧ y₂.val / 5 = w.val / 5))
    (ha1 : G16.Adj w y₁) (ha2 : G16.Adj w y₂) : y₁ = y₂ :=
  Fin.ext ((G16_out_nbr_val w y₁ hw h1 ha1).trans (G16_out_nbr_val w y₂ hw h2 ha2).symm)

private lemma witnessS_mem_cases :
    ∀ (z : Fin 16) (i : Fin 3), z ∈ witnessS → z ∈ cliqueFinset i →
      z = ⟨5 * i.val, by omega⟩ ∨ z = ⟨5 * i.val + 1, by omega⟩ := by
  intro z i hz hi
  simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have hm := witnessS_mod5 z hz
  rcases hm.2 with h0 | h1
  · left; exact Fin.ext (by dsimp only; omega)
  · right; exact Fin.ext (by dsimp only; omega)

private lemma clique_s_mem (i : Fin 3) : (⟨5 * i.val, by omega⟩ : Fin 16) ∈ cliqueFinset i := by
  simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨by omega, by omega⟩

private lemma clique_t_mem (i : Fin 3) : (⟨5 * i.val + 1, by omega⟩ : Fin 16) ∈ cliqueFinset i := by
  simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨by omega, by omega⟩

private lemma clique_u_mem (i : Fin 3) : (⟨5 * i.val + 2, by omega⟩ : Fin 16) ∈ cliqueFinset i := by
  simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨by omega, by omega⟩

lemma closedHullModel_isCycleConvex {A : Set (Fin 16)} (hAS : A ⊆ (witnessS : Set (Fin 16))) :
    IsCycleConvex G16 (closedHullModel A) := by
  let W := closedHullModel A
  have hA_in_st : ∀ z ∈ A, z.val < 15 ∧ (z.val % 5 = 0 ∨ z.val % 5 = 1) :=
    fun z hz => witnessS_mod5 z (hAS hz)
  have hfull_iff : ∀ k : Fin 3,
      (⟨5 * k.val, by omega⟩ ∈ A ∧ ⟨5 * k.val + 1, by omega⟩ ∈ A) ↔
        ∃ z ∈ W, z ∈ cliqueFinset k ∧ (z.val % 5 = 2 ∨ z.val % 5 = 3 ∨ z.val % 5 = 4) := by
    intro k
    constructor
    · rintro ⟨hs, ht⟩
      refine ⟨⟨5 * k.val + 2, by omega⟩, Or.inr (Or.inl ⟨k, hs, ht, clique_u_mem k⟩),
        clique_u_mem k, Or.inl (by change (5 * k.val + 2) % 5 = 2; omega)⟩
    · rintro ⟨z, hzW, hzk, hmod⟩
      rcases hzW with hzA | ⟨i, hsi, hti, hzi⟩ | ⟨rfl, _⟩
      · have := (hA_in_st z hzA).2; omega
      · have hik : i = k := by
          simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hzk hzi
          exact Fin.ext (by omega)
        subst hik; exact ⟨hsi, hti⟩
      · simp [cliqueFinset, vx] at hzk
  refine isCycleConvex_of_no_two_reachable_nbrs ?_
  intro w hw u v huW hvW huv hwu hwv hreach
  by_cases hwx : w = vx
  · subst hwx
    have hu_nbr := G16_vx_nbrs u hwu
    have hv_nbr := G16_vx_nbrs v hwv
    have hfull_u : ⟨5 * (u.val / 5), by omega⟩ ∈ A ∧ ⟨5 * (u.val / 5) + 1, by omega⟩ ∈ A := by
      rcases hu_nbr with rfl | rfl | rfl
      · exact (hfull_iff 0).mpr ⟨2, huW, by decide, Or.inl rfl⟩
      · exact (hfull_iff 1).mpr ⟨7, huW, by decide, Or.inl rfl⟩
      · exact (hfull_iff 2).mpr ⟨12, huW, by decide, Or.inl rfl⟩
    have hfull_v : ⟨5 * (v.val / 5), by omega⟩ ∈ A ∧ ⟨5 * (v.val / 5) + 1, by omega⟩ ∈ A := by
      rcases hv_nbr with rfl | rfl | rfl
      · exact (hfull_iff 0).mpr ⟨2, hvW, by decide, Or.inl rfl⟩
      · exact (hfull_iff 1).mpr ⟨7, hvW, by decide, Or.inl rfl⟩
      · exact (hfull_iff 2).mpr ⟨12, hvW, by decide, Or.inl rfl⟩
    have hne_clq : (⟨u.val / 5, by rcases hu_nbr with rfl | rfl | rfl <;> omega⟩ : Fin 3) ≠
        ⟨v.val / 5, by rcases hv_nbr with rfl | rfl | rfl <;> omega⟩ := by
      rcases hu_nbr with rfl | rfl | rfl <;> rcases hv_nbr with rfl | rfl | rfl <;>
        first | exact False.elim (huv rfl) | (intro h; have := congrArg Fin.val h; dsimp only at this; omega)
    exact hw (Or.inr (Or.inr ⟨rfl,
      ⟨u.val / 5, by rcases hu_nbr with rfl | rfl | rfl <;> omega⟩,
      ⟨v.val / 5, by rcases hv_nbr with rfl | rfl | rfl <;> omega⟩,
      hne_clq, hfull_u.1, hfull_u.2, hfull_v.1, hfull_v.2⟩))
  · have hw_lt : w.val < 15 := by
      have : w.val ≠ 15 := fun h => hwx (Fin.ext h)
      omega
    let k : Fin 3 := ⟨w.val / 5, by omega⟩
    have hwk : w ∈ cliqueFinset k := by simp [cliqueFinset, k, hw_lt]
    have hk_not_full : ¬ (⟨5 * k.val, by omega⟩ ∈ A ∧ ⟨5 * k.val + 1, by omega⟩ ∈ A) := by
      intro hfull
      exact hw (Or.inr (Or.inl ⟨k, hfull.1, hfull.2, hwk⟩))
    have hW_in_k : ∀ z ∈ W, z ∈ cliqueFinset k → z ∈ A := by
      intro z hzW hzk
      rcases hzW with hzA | ⟨i, hsi, hti, hzi⟩ | ⟨rfl, _⟩
      · exact hzA
      · have hik : i = k := by
          simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hzk hzi
          exact Fin.ext (by omega)
        subst hik
        exact False.elim (hk_not_full ⟨hsi, hti⟩)
      · simp [cliqueFinset, vx] at hzk
    have hW_k_unique : ∀ z₁ ∈ W, ∀ z₂ ∈ W, z₁ ∈ cliqueFinset k → z₂ ∈ cliqueFinset k → z₁ = z₂ := by
      intro z₁ hz₁ z₂ hz₂ hk₁ hk₂
      have h1A := hW_in_k z₁ hz₁ hk₁
      have h2A := hW_in_k z₂ hz₂ hk₂
      have h1c := witnessS_mem_cases z₁ k (hAS h1A) hk₁
      have h2c := witnessS_mem_cases z₂ k (hAS h2A) hk₂
      rcases h1c with rfl | rfl <;> rcases h2c with rfl | rfl
      · rfl
      · exact False.elim (hk_not_full ⟨h1A, h2A⟩)
      · exact False.elim (hk_not_full ⟨h2A, h1A⟩)
      · rfl
    have hW_k_isolated : ∀ z ∈ W, z ∈ cliqueFinset k → ∀ y ∈ W, ¬ G16.Adj z y := by
      intro z hzW hzk y hyW hzy
      have hzA := hW_in_k z hzW hzk
      have hsame := G16_st_adj_same_clique z y (hAS hzA) hzy
      have hzk' := hzk
      simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hzk'
      have hyk : y ∈ cliqueFinset k := by
        simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hsame.1, hsame.2.trans hzk'.2⟩
      exact hzy.ne (hW_k_unique z hzW y hyW hzk hyk)
    have hw_out_unique : ∀ y₁ y₂ : Fin 16,
        y₁ ∉ cliqueFinset k → y₂ ∉ cliqueFinset k → G16.Adj w y₁ → G16.Adj w y₂ → y₁ = y₂ := by
      intro y₁ y₂ hy₁ hy₂ h1 h2
      simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and, k] at hy₁ hy₂
      exact G16_out_nbr_unique w y₁ y₂ hw_lt hy₁ hy₂ h1 h2
    by_cases huk : u ∈ cliqueFinset k
    · have hvk : v ∉ cliqueFinset k := fun h => huv (hW_k_unique u huW v hvW huk h)
      rcases hreach with ⟨p⟩
      cases p with
      | nil => exact huv rfl
      | cons hstep _ =>
        exact hW_k_isolated u huW huk _ (Subtype.prop _) hstep
    · by_cases hvk : v ∈ cliqueFinset k
      · rcases hreach.symm with ⟨p⟩
        cases p with
        | nil => exact huv rfl
        | cons hstep _ =>
          exact hW_k_isolated v hvW hvk _ (Subtype.prop _) hstep
      · exact huv (hw_out_unique u v huk hvk hwu hwv)

lemma cycleHull_eq_closedHullModel {A : Set (Fin 16)} (hAS : A ⊆ (witnessS : Set (Fin 16))) :
    cycleHull G16 A = closedHullModel A := by
  refine Set.Subset.antisymm ?_ ?_
  · refine cycleHull_minimal G16 (fun x hx => Or.inl hx) (closedHullModel_isCycleConvex hAS)
  · intro v hv
    rcases hv with hvA | ⟨i, hsi, hti, hvi⟩ | ⟨rfl, i, j, hij, hsi, hti, hsj, htj⟩
    · exact subset_cycleHull G16 A hvA
    · exact clique_subset_cycleHull_of_two hsi hti (clique_s_mem i) (clique_t_mem i)
        (by intro h; have := congrArg Fin.val h; dsimp only at this; omega) hvi
    · refine vx_mem_cycleHull_of_two_cliques hij ?_ ?_
      · exact clique_subset_cycleHull_of_two hsi hti (clique_s_mem i) (clique_t_mem i)
          (by intro h; have := congrArg Fin.val h; dsimp only at this; omega)
      · exact clique_subset_cycleHull_of_two hsj htj (clique_s_mem j) (clique_t_mem j)
          (by intro h; have := congrArg Fin.val h; dsimp only at this; omega)

/-! ### Exact values `radonNumber G16 = 6` and `hellyNumber G16 = 5` -/

lemma witnessS_isRadonIndep : IsRadonIndep G16 (witnessS : Set (Fin 16)) := by
  intro A B hAS hBS _ hdisj _ _
  rw [cycleHull_eq_closedHullModel hAS, cycleHull_eq_closedHullModel hBS, Set.disjoint_left]
  intro v hvA hvB
  have hnot_both_full : ∀ i : Fin 3,
      ¬ ((⟨5 * i.val, by omega⟩ ∈ A ∧ ⟨5 * i.val + 1, by omega⟩ ∈ A) ∧
         (⟨5 * i.val, by omega⟩ ∈ B ∧ ⟨5 * i.val + 1, by omega⟩ ∈ B)) := by
    intro i ⟨⟨hsA, _⟩, ⟨hsB, _⟩⟩
    exact Set.disjoint_left.mp hdisj hsA hsB
  have hA_not_full_B : ∀ {z : Fin 16} {i : Fin 3}, z ∈ A → z ∈ cliqueFinset i →
      ¬ (⟨5 * i.val, by omega⟩ ∈ B ∧ ⟨5 * i.val + 1, by omega⟩ ∈ B) := by
    intro z i hzA hzi ⟨hsB, htB⟩
    rcases witnessS_mem_cases z i (hAS hzA) hzi with rfl | rfl
    · exact Set.disjoint_left.mp hdisj hzA hsB
    · exact Set.disjoint_left.mp hdisj hzA htB
  have hB_not_full_A : ∀ {z : Fin 16} {i : Fin 3}, z ∈ B → z ∈ cliqueFinset i →
      ¬ (⟨5 * i.val, by omega⟩ ∈ A ∧ ⟨5 * i.val + 1, by omega⟩ ∈ A) := by
    intro z i hzB hzi ⟨hsA, htA⟩
    rcases witnessS_mem_cases z i (hBS hzB) hzi with rfl | rfl
    · exact Set.disjoint_left.mp hdisj hsA hzB
    · exact Set.disjoint_left.mp hdisj htA hzB
  have hvx_not_S : vx ∉ (witnessS : Set (Fin 16)) := by decide
  rcases hvA with hvA | ⟨i, hsiA, htiA, hvi⟩ | ⟨rfl, i₁, i₂, hi12, hsi1A, hti1A, hsi2A, hti2A⟩
  · rcases hvB with hvB | ⟨j, hsjB, htjB, hvj⟩ | ⟨rfl, _⟩
    · exact Set.disjoint_left.mp hdisj hvA hvB
    · exact hA_not_full_B hvA hvj ⟨hsjB, htjB⟩
    · exact hvx_not_S (hAS hvA)
  · rcases hvB with hvB | ⟨j, hsjB, htjB, hvj⟩ | ⟨rfl, _⟩
    · exact hB_not_full_A hvB hvi ⟨hsiA, htiA⟩
    · have hij : i = j := by
        simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hvi hvj
        exact Fin.ext (by omega)
      subst hij
      exact hnot_both_full i ⟨⟨hsiA, htiA⟩, ⟨hsjB, htjB⟩⟩
    · simp [cliqueFinset, vx] at hvi
  · rcases hvB with hvB | ⟨j, _, _, hvj⟩ | ⟨_, j₁, j₂, hj12, hsj1B, htj1B, hsj2B, htj2B⟩
    · exact hvx_not_S (hBS hvB)
    · simp [cliqueFinset, vx] at hvj
    · -- Two distinct full cliques in `A` and two distinct full cliques in `B` among 3 cliques
      -- must overlap by pigeonhole!
      fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
        first
        | exact False.elim (hi12 rfl)
        | exact False.elim (hj12 rfl)
        | exact hnot_both_full 0 ⟨⟨hsi1A, hti1A⟩, ⟨hsj1B, htj1B⟩⟩
        | exact hnot_both_full 0 ⟨⟨hsi1A, hti1A⟩, ⟨hsj2B, htj2B⟩⟩
        | exact hnot_both_full 0 ⟨⟨hsi2A, hti2A⟩, ⟨hsj1B, htj1B⟩⟩
        | exact hnot_both_full 0 ⟨⟨hsi2A, hti2A⟩, ⟨hsj2B, htj2B⟩⟩
        | exact hnot_both_full 1 ⟨⟨hsi1A, hti1A⟩, ⟨hsj1B, htj1B⟩⟩
        | exact hnot_both_full 1 ⟨⟨hsi1A, hti1A⟩, ⟨hsj2B, htj2B⟩⟩
        | exact hnot_both_full 1 ⟨⟨hsi2A, hti2A⟩, ⟨hsj1B, htj1B⟩⟩
        | exact hnot_both_full 1 ⟨⟨hsi2A, hti2A⟩, ⟨hsj2B, htj2B⟩⟩
        | exact hnot_both_full 2 ⟨⟨hsi1A, hti1A⟩, ⟨hsj1B, htj1B⟩⟩
        | exact hnot_both_full 2 ⟨⟨hsi1A, hti1A⟩, ⟨hsj2B, htj2B⟩⟩
        | exact hnot_both_full 2 ⟨⟨hsi2A, hti2A⟩, ⟨hsj1B, htj1B⟩⟩
        | exact hnot_both_full 2 ⟨⟨hsi2A, hti2A⟩, ⟨hsj2B, htj2B⟩⟩

lemma witnessH5_isHellyIndep : IsHellyIndep G16 (witnessH5 : Set (Fin 16)) := by
  have hsub : (witnessH5 : Set (Fin 16)) ⊆ (witnessS : Set (Fin 16)) := by
    have : witnessH5 ⊆ witnessS := by decide
    exact Finset.coe_subset.mpr this
  have h11_not : (11 : Fin 16) ∉ witnessH5 := by decide
  intro v
  by_cases hv1_eq : v = 1
  · subst hv1_eq
    refine ⟨1, by decide, ?_⟩
    rw [cycleHull_eq_closedHullModel (Set.sdiff_subset.trans hsub)]
    rintro (⟨_, hvne⟩ | ⟨i, _, hti, hvi⟩ | ⟨hEq, _⟩)
    · exact hvne rfl
    · have hi0 : i = 0 := by
        simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hvi
        exact Fin.ext (by omega)
      subst hi0
      exact hti.2 rfl
    · exact (by decide : (1 : Fin 16) ≠ vx) hEq
  · by_cases hv0 : v ∈ cliqueFinset 0
    · refine ⟨0, by decide, ?_⟩
      rw [cycleHull_eq_closedHullModel (Set.sdiff_subset.trans hsub)]
      rintro (⟨hv5, hvne⟩ | ⟨i, hsi, _, hvi⟩ | ⟨rfl, _⟩)
      · have : v = 0 ∨ v = 1 := by
          simp only [Finset.mem_coe, witnessH5, cliqueFinset, Finset.mem_insert,
            Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and] at hv5 hv0
          rcases hv5 with rfl | rfl | rfl | rfl | rfl
          · left; rfl
          · right; rfl
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
        rcases this with rfl | rfl
        · exact hvne rfl
        · exact hv1_eq rfl
      · have hi0 : i = 0 := by
          simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hv0 hvi
          exact Fin.ext (by omega)
        subst hi0
        exact hsi.2 rfl
      · exact (by decide : vx ∉ cliqueFinset 0) hv0
    · by_cases hv6_eq : v = 6
      · subst hv6_eq
        refine ⟨6, by decide, ?_⟩
        rw [cycleHull_eq_closedHullModel (Set.sdiff_subset.trans hsub)]
        rintro (⟨_, hvne⟩ | ⟨i, _, hti, hvi⟩ | ⟨hEq, _⟩)
        · exact hvne rfl
        · have hi1 : i = 1 := by
            simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hvi
            exact Fin.ext (by omega)
          subst hi1
          exact hti.2 rfl
        · exact (by decide : (6 : Fin 16) ≠ vx) hEq
      · by_cases hv1 : v ∈ cliqueFinset 1
        · refine ⟨5, by decide, ?_⟩
          rw [cycleHull_eq_closedHullModel (Set.sdiff_subset.trans hsub)]
          rintro (⟨hv5, hvne⟩ | ⟨i, hsi, _, hvi⟩ | ⟨rfl, _⟩)
          · have : v = 5 ∨ v = 6 := by
              simp only [Finset.mem_coe, witnessH5, cliqueFinset, Finset.mem_insert,
                Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and] at hv5 hv1
              rcases hv5 with rfl | rfl | rfl | rfl | rfl
              · exfalso; omega
              · exfalso; omega
              · left; rfl
              · right; rfl
              · exfalso; omega
            rcases this with rfl | rfl
            · exact hvne rfl
            · exact hv6_eq rfl
          · have hi1 : i = 1 := by
              simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hvi
              exact Fin.ext (by omega)
            subst hi1
            exact hsi.2 rfl
          · exact (by decide : vx ∉ cliqueFinset 1) hv1
        · by_cases hv10 : v = 10
          · subst hv10
            refine ⟨10, by decide, ?_⟩
            rw [cycleHull_eq_closedHullModel (Set.sdiff_subset.trans hsub)]
            rintro (⟨_, hvne⟩ | ⟨i, _, hti, hvi⟩ | ⟨hEq, _⟩)
            · exact hvne rfl
            · have hi2 : i = 2 := by
                simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hvi
                exact Fin.ext (by omega)
              subst hi2
              exact h11_not hti.1
            · exact (by decide : (10 : Fin 16) ≠ vx) hEq
          · refine ⟨0, by decide, ?_⟩
            rw [cycleHull_eq_closedHullModel (Set.sdiff_subset.trans hsub)]
            rintro (⟨hv5, _⟩ | ⟨i, hsi, hti, hvi⟩ | ⟨_, i, j, hij, hsi, hti, hsj, htj⟩)
            · have : v ∈ cliqueFinset 0 ∨ v ∈ cliqueFinset 1 ∨ v = 10 := by
                simp only [Finset.mem_coe, witnessH5, Finset.mem_insert, Finset.mem_singleton] at hv5
                rcases hv5 with rfl | rfl | rfl | rfl | rfl
                · left; simp [cliqueFinset]
                · left; simp [cliqueFinset]
                · right; left; simp [cliqueFinset]
                · right; left; simp [cliqueFinset]
                · right; right; rfl
              rcases this with h | h | h
              · exact hv0 h
              · exact hv1 h
              · exact hv10 h
            · fin_cases i
              · exact hsi.2 rfl
              · exact hv1 hvi
              · exact h11_not hti.1
            · fin_cases i <;> fin_cases j
              · exact hij rfl
              · exact hsi.2 rfl
              · exact hsi.2 rfl
              · exact hsj.2 rfl
              · exact hij rfl
              · exact h11_not htj.1
              · exact hsj.2 rfl
              · exact h11_not hti.1
              · exact hij rfl

/-- Any Radon-independent (hence also any Helly-independent) subset of `G16` contains
at most 2 vertices in each clique `K^(i)`. -/
lemma card_inter_clique_le_two {T : Finset (Fin 16)} (hR : IsRadonIndep G16 (T : Set (Fin 16)))
    (i : Fin 3) : (T ∩ cliqueFinset i).card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨s, hsSub, hsCard⟩ := Finset.exists_subset_card_eq hgt
  rw [Finset.card_eq_three] at hsCard
  rcases hsCard with ⟨a, b, c, hab, hac, hbc, rfl⟩
  have ha : a ∈ T ∩ cliqueFinset i := hsSub (by simp)
  have hb : b ∈ T ∩ cliqueFinset i := hsSub (by simp)
  have hc : c ∈ T ∩ cliqueFinset i := hsSub (by simp)
  rw [Finset.mem_inter] at ha hb hc
  exact not_isRadonIndep_of_triangle
    ha.1 hb.1 hc.1
    (G16_clique_adj ha.2 hb.2 hab)
    (G16_clique_adj hb.2 hc.2 hbc)
    (G16_clique_adj hc.2 ha.2 (Ne.symm hac))
    hR

/-- Partition of `Finset.card` for `T ⊆ Fin 16` into the three cliques plus `{vx}`. -/
lemma card_decomp_G16 (T : Finset (Fin 16)) :
    T.card = (T ∩ cliqueFinset 0).card + (T ∩ cliqueFinset 1).card +
      (T ∩ cliqueFinset 2).card + (if vx ∈ T then 1 else 0) := by
  have hunion :
      (Finset.univ : Finset (Fin 16)) =
        cliqueFinset 0 ∪ cliqueFinset 1 ∪ cliqueFinset 2 ∪ {vx} := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_singleton, cliqueFinset,
      Finset.mem_filter, true_and, true_iff]
    by_cases hv : v = vx
    · right; exact hv
    · left
      have hvlt : v.val < 15 := by
        have : v.val ≠ 15 := fun h => hv (Fin.ext h)
        omega
      have hdiv : v.val / 5 = 0 ∨ v.val / 5 = 1 ∨ v.val / 5 = 2 := by omega
      rcases hdiv with h0 | h1 | h2
      · left; left; exact ⟨hvlt, h0⟩
      · left; right; exact ⟨hvlt, h1⟩
      · right; exact ⟨hvlt, h2⟩
  have hd01 : Disjoint (cliqueFinset 0) (cliqueFinset 1) := by
    rw [Finset.disjoint_left]
    intro v h0 h1
    simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1
    omega
  have hd012 : Disjoint (cliqueFinset 0 ∪ cliqueFinset 1) (cliqueFinset 2) := by
    rw [Finset.disjoint_left]
    intro v h01 h2
    simp only [Finset.mem_union, cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at h01 h2
    omega
  have hd012x : Disjoint (cliqueFinset 0 ∪ cliqueFinset 1 ∪ cliqueFinset 2) {vx} := by
    rw [Finset.disjoint_left]
    intro v h012 hvx
    simp only [Finset.mem_singleton] at hvx; subst hvx
    simp only [Finset.mem_union, cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and, vx] at h012
    omega
  have hT : T = (T ∩ cliqueFinset 0) ∪ (T ∩ cliqueFinset 1) ∪ (T ∩ cliqueFinset 2) ∪ (T ∩ {vx}) := by
    calc
      T = T ∩ Finset.univ := (Finset.inter_univ T).symm
      _ = T ∩ (cliqueFinset 0 ∪ cliqueFinset 1 ∪ cliqueFinset 2 ∪ {vx}) := by rw [hunion]
      _ = (T ∩ cliqueFinset 0) ∪ (T ∩ cliqueFinset 1) ∪ (T ∩ cliqueFinset 2) ∪ (T ∩ {vx}) := by
          simp only [Finset.inter_union_distrib_left]
  have h1 : Disjoint (T ∩ cliqueFinset 0) (T ∩ cliqueFinset 1) :=
    hd01.mono Finset.inter_subset_right Finset.inter_subset_right
  have h2 : Disjoint ((T ∩ cliqueFinset 0) ∪ (T ∩ cliqueFinset 1)) (T ∩ cliqueFinset 2) :=
    hd012.mono (Finset.union_subset_union Finset.inter_subset_right Finset.inter_subset_right)
      Finset.inter_subset_right
  have h3 : Disjoint ((T ∩ cliqueFinset 0) ∪ (T ∩ cliqueFinset 1) ∪ (T ∩ cliqueFinset 2)) (T ∩ {vx}) :=
    hd012x.mono
      (Finset.union_subset_union
        (Finset.union_subset_union Finset.inter_subset_right Finset.inter_subset_right)
        Finset.inter_subset_right)
      Finset.inter_subset_right
  have hx : (T ∩ {vx}).card = if vx ∈ T then 1 else 0 := by
    by_cases h : vx ∈ T
    · rw [if_pos h, Finset.inter_singleton_of_mem h, Finset.card_singleton]
    · rw [if_neg h, Finset.inter_singleton_of_notMem h, Finset.card_empty]
  conv_lhs => rw [hT]
  rw [Finset.card_union_of_disjoint h3, Finset.card_union_of_disjoint h2,
    Finset.card_union_of_disjoint h1, hx]

/-- Helper: if `A : Set (Fin 16)` contains at least 2 vertices in each of two distinct cliques
`K^(i)` and `K^(j)`, then `vx ∈ cycleHull G16 A`. -/
lemma vx_mem_cycleHull_of_two_full_inter {T : Finset (Fin 16)} {i j : Fin 3} (hij : i ≠ j)
    (hi : 2 ≤ (T ∩ cliqueFinset i).card) (hj : 2 ≤ (T ∩ cliqueFinset j).card) :
    vx ∈ cycleHull G16 (T : Set (Fin 16)) := by
  obtain ⟨a₁, ha₁, a₂, ha₂, ha12⟩ := Finset.one_lt_card.mp (by omega : 1 < (T ∩ cliqueFinset i).card)
  obtain ⟨b₁, hb₁, b₂, hb₂, hb12⟩ := Finset.one_lt_card.mp (by omega : 1 < (T ∩ cliqueFinset j).card)
  rw [Finset.mem_inter] at ha₁ ha₂ hb₁ hb₂
  exact vx_mem_cycleHull_of_two_cliques hij
    (clique_subset_cycleHull_of_two ha₁.1 ha₂.1 ha₁.2 ha₂.2 ha12)
    (clique_subset_cycleHull_of_two hb₁.1 hb₂.1 hb₁.2 hb₂.2 hb12)

lemma hellyIndep_G16_card_le_five {T : Finset (Fin 16)} (hH : IsHellyIndep G16 (T : Set (Fin 16))) :
    T.card ≤ 5 := by
  have hR := isRadonIndep_of_isHellyIndep hH
  have hc0 := card_inter_clique_le_two hR 0
  have hc1 := card_inter_clique_le_two hR 1
  have hc2 := card_inter_clique_le_two hR 2
  have hdec := card_decomp_G16 T
  by_contra hgt
  push Not at hgt
  -- Show `vx ∈ cycleHull G16 (T \ {a})` for every `a ∈ T`, contradicting `hH vx`.
  obtain ⟨a, haT, haNot⟩ := hH vx
  have haT' : a ∈ T := haT
  by_cases hax : a = vx
  · subst hax
    -- Removing `vx` leaves all vertices in the three cliques; since `T.card ≥ 6`,
    -- `c0 + c1 + c2 ≥ 5`, so at least two cliques have 2 vertices in `T \ {vx}`.
    have hsum : (T ∩ cliqueFinset 0).card + (T ∩ cliqueFinset 1).card + (T ∩ cliqueFinset 2).card ≥ 5 := by
      rw [if_pos haT'] at hdec; omega
    have herase : ∀ i : Fin 3, ((T.erase vx) ∩ cliqueFinset i).card = (T ∩ cliqueFinset i).card := by
      intro i
      congr 1
      ext z
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · exact fun ⟨⟨_, hzT⟩, hzi⟩ => ⟨hzT, hzi⟩
      · refine fun ⟨hzT, hzi⟩ => ⟨⟨?_, hzT⟩, hzi⟩
        intro hzx; subst hzx; fin_cases i <;> exact (by decide : vx ∉ cliqueFinset _) hzi
    have hcast : ((T.erase vx : Finset (Fin 16)) : Set (Fin 16)) = (T : Set (Fin 16)) \ {vx} := by
      simp
    rw [← hcast] at haNot
    by_cases h01 : (T ∩ cliqueFinset 0).card = 2 ∧ (T ∩ cliqueFinset 1).card = 2
    · exact haNot (vx_mem_cycleHull_of_two_full_inter (by decide : (0 : Fin 3) ≠ 1)
        (by rw [herase]; omega) (by rw [herase]; omega))
    · by_cases h02 : (T ∩ cliqueFinset 0).card = 2 ∧ (T ∩ cliqueFinset 2).card = 2
      · exact haNot (vx_mem_cycleHull_of_two_full_inter (by decide : (0 : Fin 3) ≠ 2)
          (by rw [herase]; omega) (by rw [herase]; omega))
      · exact haNot (vx_mem_cycleHull_of_two_full_inter (by decide : (1 : Fin 3) ≠ 2)
          (by rw [herase]; omega) (by rw [herase]; omega))
  · by_cases hxT : vx ∈ T
    · exact haNot (subset_cycleHull G16 _ ⟨hxT, fun h => hax h.symm⟩)
    · -- `vx ∉ T` and `T.card ≥ 6` force all three cliques to have size 2 in `T`.
      rw [if_neg hxT] at hdec
      have heq0 : (T ∩ cliqueFinset 0).card = 2 := by omega
      have heq1 : (T ∩ cliqueFinset 1).card = 2 := by omega
      have heq2 : (T ∩ cliqueFinset 2).card = 2 := by omega
      have ha_lt : a.val < 15 := by
        have : a.val ≠ 15 := fun h => hax (Fin.ext h)
        omega
      have herase_other : ∀ i : Fin 3, i.val ≠ a.val / 5 →
          ((T.erase a) ∩ cliqueFinset i).card = (T ∩ cliqueFinset i).card := by
        intro i hi
        congr 1
        ext z
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · exact fun ⟨⟨_, hzT⟩, hzi⟩ => ⟨hzT, hzi⟩
        · refine fun ⟨hzT, hzi⟩ => ⟨⟨?_, hzT⟩, hzi⟩
          intro hza; subst hza
          simp only [cliqueFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hzi
          exact hi hzi.2.symm
      have hcast : ((T.erase a : Finset (Fin 16)) : Set (Fin 16)) = (T : Set (Fin 16)) \ {a} := by
        simp
      rw [← hcast] at haNot
      have hka : a.val / 5 = 0 ∨ a.val / 5 = 1 ∨ a.val / 5 = 2 := by omega
      rcases hka with h0 | h1 | h2
      · exact haNot (vx_mem_cycleHull_of_two_full_inter (by decide : (1 : Fin 3) ≠ 2)
          (by rw [herase_other 1 (by omega)]; omega) (by rw [herase_other 2 (by omega)]; omega))
      · exact haNot (vx_mem_cycleHull_of_two_full_inter (by decide : (0 : Fin 3) ≠ 2)
          (by rw [herase_other 0 (by omega)]; omega) (by rw [herase_other 2 (by omega)]; omega))
      · exact haNot (vx_mem_cycleHull_of_two_full_inter (by decide : (0 : Fin 3) ≠ 1)
          (by rw [herase_other 0 (by omega)]; omega) (by rw [herase_other 1 (by omega)]; omega))

lemma radonIndep_G16_card_le_six {T : Finset (Fin 16)} (hR : IsRadonIndep G16 (T : Set (Fin 16))) :
    T.card ≤ 6 := by
  have hc0 := card_inter_clique_le_two hR 0
  have hc1 := card_inter_clique_le_two hR 1
  have hc2 := card_inter_clique_le_two hR 2
  have hdec := card_decomp_G16 T
  by_contra hgt
  push Not at hgt
  have hxT : vx ∈ T := by
    by_contra hnot
    rw [if_neg hnot] at hdec
    omega
  rw [if_pos hxT] at hdec
  have heq0 : (T ∩ cliqueFinset 0).card = 2 := by omega
  have heq1 : (T ∩ cliqueFinset 1).card = 2 := by omega
  have hAsub : ({vx} : Set (Fin 16)) ⊆ (T : Set (Fin 16)) := Set.singleton_subset_iff.mpr hxT
  have hBsub : (T : Set (Fin 16)) \ {vx} ⊆ (T : Set (Fin 16)) := Set.sdiff_subset
  have hAB : ({vx} : Set (Fin 16)) ∪ ((T : Set (Fin 16)) \ {vx}) = (T : Set (Fin 16)) :=
    Set.union_sdiff_cancel hAsub
  have hdisj : Disjoint ({vx} : Set (Fin 16)) ((T : Set (Fin 16)) \ {vx}) := disjoint_sdiff_self_right
  have hAne : ({vx} : Set (Fin 16)).Nonempty := Set.singleton_nonempty vx
  have hBne : ((T : Set (Fin 16)) \ {vx}).Nonempty := by
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (T ∩ cliqueFinset 0).card)
    rw [Finset.mem_inter] at hz
    refine ⟨z, hz.1, ?_⟩
    intro hzx; subst hzx; exact (by decide : vx ∉ cliqueFinset 0) hz.2
  have hdisjHull := hR {vx} ((T : Set (Fin 16)) \ {vx}) hAsub hBsub hAB hdisj hAne hBne
  have hvxA : vx ∈ cycleHull G16 {vx} := subset_cycleHull G16 _ (Set.mem_singleton vx)
  have hcast : ((T.erase vx : Finset (Fin 16)) : Set (Fin 16)) = (T : Set (Fin 16)) \ {vx} := by
    simp
  have herase : ∀ i : Fin 3, ((T.erase vx) ∩ cliqueFinset i).card = (T ∩ cliqueFinset i).card := by
    intro i
    congr 1
    ext z
    simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · exact fun ⟨⟨_, hzT⟩, hzi⟩ => ⟨hzT, hzi⟩
    · refine fun ⟨hzT, hzi⟩ => ⟨⟨?_, hzT⟩, hzi⟩
      intro hzx; subst hzx; fin_cases i <;> exact (by decide : vx ∉ cliqueFinset _) hzi
  have hvxB : vx ∈ cycleHull G16 ((T : Set (Fin 16)) \ {vx}) := by
    rw [← hcast]
    exact vx_mem_cycleHull_of_two_full_inter (by decide : (0 : Fin 3) ≠ 1)
      (by rw [herase]; omega) (by rw [herase]; omega)
  exact Set.disjoint_left.mp hdisjHull hvxA hvxB

/-- **Exact Helly number of `G16`:** `hl_{cc}(G16) = 5`. -/
theorem hellyNumber_G16 : hellyNumber G16 = 5 := by
  classical
  refine le_antisymm ?_ ?_
  · unfold hellyNumber
    refine Finset.sup_le ?_
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    exact hellyIndep_G16_card_le_five hT
  · unfold hellyNumber
    have hmem : witnessH5 ∈ Finset.univ.filter fun S : Finset (Fin 16) =>
        IsHellyIndep G16 (S : Set (Fin 16)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact witnessH5_isHellyIndep
    have hcard : witnessH5.card = 5 := by decide
    rw [← hcard]
    exact Finset.le_sup (f := Finset.card) hmem

/-- **Exact Radon number of `G16`:** `rd_{cc}(G16) = 6`. -/
theorem radonNumber_G16 : radonNumber G16 = 6 := by
  classical
  refine le_antisymm ?_ ?_
  · unfold radonNumber
    refine Finset.sup_le ?_
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    exact radonIndep_G16_card_le_six hT
  · unfold radonNumber
    have hmem : witnessS ∈ Finset.univ.filter fun S : Finset (Fin 16) =>
        IsRadonIndep G16 (S : Set (Fin 16)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact witnessS_isRadonIndep
    have hcard : witnessS.card = 6 := by decide
    rw [← hcard]
    exact Finset.le_sup (f := Finset.card) hmem

/-- **Main Disproof (Refutation of Conjecture 1 of arXiv:2609.34236v1):**
There exists a finite connected graph `G` of order `n ≥ 2` (namely `G16`, with `n = 16`)
such that `hl_{cc}(G) ≠ rd_{cc}(G)` (in fact `hl_{cc}(G16) = 5 < 6 = rd_{cc}(G16)`). -/
theorem counterexample_cycle_convexity_helly_radon :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      2 ≤ Fintype.card V ∧ G.Connected ∧ hellyNumber G ≠ radonNumber G := by
  refine ⟨Fin 16, inferInstance, G16, by decide, G16_connected, ?_⟩
  rw [hellyNumber_G16, radonNumber_G16]
  omega

end CycleConvexityHellyRadon
