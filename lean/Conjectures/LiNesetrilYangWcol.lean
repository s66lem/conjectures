import Mathlib

/-!
# Disproof of Li–Nešetřil–Yang Problem 3.6 and the Weak Inequality of Problem 3.5

Reference: Wenwen Li, Jaroslav Nešetřil, Daqing Yang,
"Generalized oriented chromatic numbers and directed generalized coloring numbers of graphs",
arXiv:2611.33681v1 (25 Nov 2026), Section 3.2.

We formally prove:
1. **Forest Lemma (`forest_wcolPlus_eq_one`, `forest_colPlus_eq_one`):**
   Every orientation of every finite acyclic simple graph `F` admits a topological linear
   ordering, yielding `wcolPlus D k = colPlus D k = 1` for all `k ≥ 1`.
2. **Subgraph Monotonicity (`wcolGraph_mono`):**
   If `H ≤ G`, then `wcol H k ≤ wcol G k`.
3. **Disproof of Problem 3.6 and the factor-2 weak bound of Problem 3.5 (`p4_disproves_prob35_prob36`):**
   For `P₄` and every `k ≥ 2`, `wcol P₄ k = 3` whereas every orientation `D` of `P₄` has
   `wcolPlus D k = 1 ≠ ⌈3 / 2⌉ = 2` and `3 > 2 * 1`.
4. **Unbounded Separation (`no_uniform_weak_bound`):**
   For every `t ≥ 1`, `N = 2^t - 1`, and `k ≥ N - 1`, `wcol P_N k ≥ t` while
   `wcolPlus P_N k = 1`; hence no function `g : ℕ → ℕ` satisfies
   `wcol G k ≤ g (wcolPlus G k)` for all finite graphs `G` and `k ≥ 1`.
-/

namespace LiNesetrilYangWcol

open Finset
open Classical

/-! ### Section 1: Oriented graphs, directed walks, and weak/strong reachability -/

/-- An orientation of a simple graph `G` on vertex type `V`: each undirected edge `{u, v}`
is assigned a unique direction `arc u v` or `arc v u` (and non-edges have no arcs). -/
structure Orientation {V : Type*} (G : SimpleGraph V) where
  arc : V → V → Prop
  arc_dec : DecidableRel arc
  asymm : ∀ u v, arc u v → ¬ arc v u
  covers : ∀ u v, G.Adj u v ↔ arc u v ∨ arc v u

attribute [instance] Orientation.arc_dec

/-- A directed walk of length `≤ k` in an oriented graph `D` from `u` to `v` whose
vertices all satisfy predicate `P`. -/
inductive DirWalkLe {V : Type*} {G : SimpleGraph V} (D : Orientation G) (P : V → Prop) :
    ℕ → V → V → Prop
  | nil {u : V} (hu : P u) (k : ℕ) : DirWalkLe D P k u u
  | cons {k : ℕ} {u w v : V} (hu : P u) (harc : D.arc u w)
      (rest : DirWalkLe D P k w v) : DirWalkLe D P (k + 1) u v

lemma DirWalkLe.mono_k {V : Type*} {G : SimpleGraph V} {D : Orientation G} {P : V → Prop}
    {k₁ k₂ : ℕ} {u v : V} (hk : k₁ ≤ k₂) (h : DirWalkLe D P k₁ u v) :
    DirWalkLe D P k₂ u v := by
  induction h generalizing k₂ with
  | nil hu _ => exact .nil hu k₂
  | @cons k u w v hu harc rest ih =>
    cases k₂ with
    | zero => omega
    | succ k₂' => exact .cons hu harc (ih (by omega))

lemma DirWalkLe.mono_P {V : Type*} {G : SimpleGraph V} {D : Orientation G} {P Q : V → Prop}
    (hPQ : ∀ z, P z → Q z) {k : ℕ} {u v : V} (h : DirWalkLe D P k u v) :
    DirWalkLe D Q k u v := by
  induction h with
  | nil hu k => exact .nil (hPQ _ hu) k
  | cons hu harc _ ih => exact .cons (hPQ _ hu) harc ih

/-- A linear ordering of a finite type `V` is an injective rank function `pos : V → ℕ`. -/
structure VertexOrder (V : Type*) where
  pos : V → ℕ
  inj : Function.Injective pos

/-- Weak `(k, +)`-reachability: `x` is weakly `(k, +)`-reachable from `y` under `σ`
if `pos x ≤ pos y` and there is a directed `y → x` walk of length `≤ k` with all vertices `≥ x`. -/
def WeakReachPlus {V : Type*} {G : SimpleGraph V} (D : Orientation G)
    (σ : VertexOrder V) (k : ℕ) (y x : V) : Prop :=
  σ.pos x ≤ σ.pos y ∧ DirWalkLe D (fun z => σ.pos x ≤ σ.pos z) k y x

/-- Weak `(k, -)`-reachability: `x` is weakly `(k, -)`-reachable from `y` under `σ`
if `pos x ≤ pos y` and there is a directed `x → y` walk of length `≤ k` with all vertices `≥ x`. -/
def WeakReachMinus {V : Type*} {G : SimpleGraph V} (D : Orientation G)
    (σ : VertexOrder V) (k : ℕ) (y x : V) : Prop :=
  σ.pos x ≤ σ.pos y ∧ DirWalkLe D (fun z => σ.pos x ≤ σ.pos z) k x y

/-- Strong `(k, +)`-reachability: `x = y` or `pos x < pos y` with a directed `y → x` walk of
length `≤ k` whose internal vertices all satisfy `pos y < pos z`. -/
def StrongReachPlus {V : Type*} {G : SimpleGraph V} (D : Orientation G)
    (σ : VertexOrder V) (k : ℕ) (y x : V) : Prop :=
  x = y ∨ (σ.pos x < σ.pos y ∧ ∃ w, D.arc y w ∧
    ((w = x ∧ 1 ≤ k) ∨
      ∃ k', k' + 1 ≤ k ∧ σ.pos y < σ.pos w ∧
        DirWalkLe D (fun z => z = x ∨ σ.pos y < σ.pos z) k' w x))

/-- Weak `(k, +)`-reachability set `W^{k,+}_{D,σ}(y)`. -/
noncomputable def weakSetPlus {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (σ : VertexOrder V) (k : ℕ) (y : V) : Finset V :=
  Finset.univ.filter (fun x => WeakReachPlus D σ k y x)

/-- Combined weak `k`-reachability set `W^{k,+}_{D,σ}(y) ∪ W^{k,-}_{D,σ}(y)`. -/
noncomputable def weakSet {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (σ : VertexOrder V) (k : ℕ) (y : V) : Finset V :=
  Finset.univ.filter (fun x => WeakReachPlus D σ k y x ∨ WeakReachMinus D σ k y x)

/-- Strong `(k, +)`-reachability set `S^{k,+}_{D,σ}(y)`. -/
noncomputable def strongSetPlus {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (σ : VertexOrder V) (k : ℕ) (y : V) : Finset V :=
  Finset.univ.filter (fun x => StrongReachPlus D σ k y x)

private lemma mem_weakSetPlus {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (σ : VertexOrder V) (k : ℕ) (y x : V) :
    x ∈ weakSetPlus D σ k y ↔ WeakReachPlus D σ k y x := by
  simp [weakSetPlus]

private lemma mem_weakSet {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (σ : VertexOrder V) (k : ℕ) (y x : V) :
    x ∈ weakSet D σ k y ↔ WeakReachPlus D σ k y x ∨ WeakReachMinus D σ k y x := by
  simp [weakSet]

private lemma mem_strongSetPlus {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (σ : VertexOrder V) (k : ℕ) (y x : V) :
    x ∈ strongSetPlus D σ k y ↔ StrongReachPlus D σ k y x := by
  simp [strongSetPlus]

lemma mem_weakSetPlus_self {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (σ : VertexOrder V) (k : ℕ) (y : V) :
    y ∈ weakSetPlus D σ k y := by
  rw [mem_weakSetPlus]
  exact ⟨le_rfl, DirWalkLe.nil (P := fun z => σ.pos y ≤ σ.pos z) le_rfl k⟩

lemma mem_strongSetPlus_self {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (σ : VertexOrder V) (k : ℕ) (y : V) :
    y ∈ strongSetPlus D σ k y := by
  rw [mem_strongSetPlus]
  exact Or.inl rfl

/-- `wcolPlusOfOrder D σ k = max_{y} |W^{k,+}_{D,σ}(y)|`. -/
noncomputable def wcolPlusOfOrder {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (σ : VertexOrder V) (k : ℕ) : ℕ :=
  Finset.univ.sup (fun y => (weakSetPlus D σ k y).card)

/-- `colPlusOfOrder D σ k = max_{y} |S^{k,+}_{D,σ}(y)|`. -/
noncomputable def colPlusOfOrder {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (σ : VertexOrder V) (k : ℕ) : ℕ :=
  Finset.univ.sup (fun y => (strongSetPlus D σ k y).card)

/-- `wcolOfOrder D σ k = max_{y} |W^{k,+}_{D,σ}(y) ∪ W^{k,-}_{D,σ}(y)|`. -/
noncomputable def wcolOfOrder {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (σ : VertexOrder V) (k : ℕ) : ℕ :=
  Finset.univ.sup (fun y => (weakSet D σ k y).card)

/-- `wcolPlus D k = min_σ wcolPlusOfOrder D σ k` (using `sInf` on `ℕ`). -/
noncomputable def wcolPlus {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (k : ℕ) : ℕ :=
  sInf { m : ℕ | ∃ σ : VertexOrder V, wcolPlusOfOrder D σ k = m }

/-- `colPlus D k = min_σ colPlusOfOrder D σ k`. -/
noncomputable def colPlus {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (k : ℕ) : ℕ :=
  sInf { m : ℕ | ∃ σ : VertexOrder V, colPlusOfOrder D σ k = m }

/-- `wcol D k = min_σ wcolOfOrder D σ k`. -/
noncomputable def wcol {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (k : ℕ) : ℕ :=
  sInf { m : ℕ | ∃ σ : VertexOrder V, wcolOfOrder D σ k = m }

/-- Undirected `wcolPlusGraph G k = max_{D} wcolPlus D k` (via `sSup` on bounded `ℕ` set). -/
noncomputable def wcolPlusGraph {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ D : Orientation G, wcolPlus D k = m }

/-- Undirected `wcolGraph G k = max_{D} wcol D k`. -/
noncomputable def wcolGraph {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ D : Orientation G, wcol D k = m }

/-! ### Section 2: Forest Lemma (every orientation of every finite forest has `wcol+ = col+ = 1`) -/

/-- Every orientation of an acyclic simple graph has no non-trivial directed walk from a vertex
back to itself (and in fact any nonempty finite subset contains a source). -/
private lemma exists_source_in_forest {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hF : G.IsAcyclic) (D : Orientation G)
    (S : Finset V) (hS : S.Nonempty) :
    ∃ u ∈ S, ∀ w ∈ S, ¬ D.arc w u := by
  by_contra hno
  push Not at hno
  -- From any `x ∈ S`, choose an in-neighbor `f x ∈ S` with `D.arc (f x) x`.
  choose f hfS hfarc using hno
  -- Iterate `f` starting from `v₀ ∈ S` to build a chain `v(0), v(1), ..., v(S.card)` in `S`.
  obtain ⟨v₀, hv₀⟩ := hS
  let seq : ℕ → { x : V // x ∈ S } := Nat.rec ⟨v₀, hv₀⟩ (fun _ cur => ⟨f cur.1 cur.2, hfS cur.1 cur.2⟩)
  -- By pigeonhole on `Fin (S.card + 1) → S`, two indices `i < j` agree.
  have hnotinj : ¬ Function.Injective (fun i : Fin (S.card + 1) => seq i.val) := by
    intro hinj
    have hle := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at hle
    omega
  unfold Function.Injective at hnotinj
  push Not at hnotinj
  rcases hnotinj with ⟨i, j, heq, hne⟩
  -- Take a minimal-length repeated pair `i < j` with `seq i = seq j` and all intermediate distinct.
  have hex : ∃ d : ℕ, 1 ≤ d ∧ ∃ a : ℕ, (seq a).1 = (seq (a + d)).1 := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · refine ⟨j.val - i.val, by omega, i.val, ?_⟩
      have hadd : i.val + (j.val - i.val) = j.val := by omega
      rw [hadd]
      exact congrArg Subtype.val heq
    · refine ⟨i.val - j.val, by omega, j.val, ?_⟩
      have hadd : j.val + (i.val - j.val) = i.val := by omega
      rw [hadd]
      exact congrArg Subtype.val heq.symm
  set d₀ := Nat.find hex
  have hd₀_spec : 1 ≤ d₀ ∧ ∃ a : ℕ, (seq a).1 = (seq (a + d₀)).1 := Nat.find_spec hex
  have hd₀_pos : 1 ≤ d₀ := hd₀_spec.1
  rcases hd₀_spec.2 with ⟨a, ha_eq⟩
  -- Every consecutive pair `(seq t, seq (t + 1))` has `D.arc (seq (t+1)) (seq t)`, hence `G.Adj`.
  have hadj_step : ∀ t : ℕ, G.Adj (seq (t + 1)).1 (seq t).1 := fun t =>
    (D.covers _ _).mpr (Or.inl (hfarc (seq t).1 (seq t).2))
  -- Build a `G.Walk (seq (a + m)).1 (seq a).1` of length `m` along `seq`.
  have hwalk : ∀ m : ℕ, ∃ p : G.Walk (seq (a + m)).1 (seq a).1,
      p.length = m ∧ p.support = (List.range (m + 1)).reverse.map (fun r => (seq (a + r)).1) := by
    intro m
    induction m with
    | zero =>
      exact ⟨SimpleGraph.Walk.nil, rfl, by simp⟩
    | succ m ih =>
      rcases ih with ⟨p, hlen, hsup⟩
      refine ⟨SimpleGraph.Walk.cons (hadj_step (a + m)) p, by simp [hlen], ?_⟩
      rw [SimpleGraph.Walk.support_cons, hsup]
      simp [List.range_succ]
  -- `d₀ ≠ 1` (since `G` is loopless) and `d₀ ≠ 2` (since `D` is asymmetric).
  have hd₀_ge3 : 3 ≤ d₀ := by
    by_contra hlt3
    have h12 : d₀ = 1 ∨ d₀ = 2 := by omega
    rcases h12 with h1 | h2
    · rw [h1] at ha_eq
      exact G.loopless.irrefl _ (ha_eq ▸ hadj_step a)
    · rw [h2] at ha_eq
      have h1' : D.arc (seq (a + 1)).1 (seq a).1 := hfarc (seq a).1 (seq a).2
      have h2' : D.arc (seq (a + 2)).1 (seq (a + 1)).1 := hfarc (seq (a + 1)).1 (seq (a + 1)).2
      rw [← ha_eq] at h2'
      exact D.asymm _ _ h1' h2'
  -- The closed walk of length `d₀ ≥ 3` has distinct vertices `seq a, ..., seq (a + d₀ - 1)` by minimality of `d₀`.
  rcases hwalk d₀ with ⟨p, hlen, hsup⟩
  let c : G.Walk (seq a).1 (seq a).1 := p.copy ha_eq.symm rfl
  have hc_cyc : c.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isTrail_def]
      have hnodup_tail : c.support.tail.Nodup := by
        have hc_sup : c.support = (List.range (d₀ + 1)).reverse.map (fun r => (seq (a + r)).1) := by
          simpa [c] using hsup
        rw [hc_sup, List.range_succ, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.map_cons, List.tail_cons,
          List.nodup_map_iff_inj_on (List.nodup_reverse.mpr List.nodup_range)]
        intro r₁ hr₁ r₂ hr₂ hEq
        simp only [List.mem_reverse, List.mem_range] at hr₁ hr₂
        by_contra hne_r
        rcases lt_or_gt_of_ne hne_r with hlt | hlt
        · have hsmall : r₂ - r₁ < d₀ := by omega
          have hmem : 1 ≤ r₂ - r₁ ∧ ∃ b, (seq b).1 = (seq (b + (r₂ - r₁))).1 :=
            ⟨by omega, a + r₁, by rw [show a + r₁ + (r₂ - r₁) = a + r₂ by omega]; exact hEq⟩
          exact Nat.find_min hex hsmall hmem
        · have hsmall : r₁ - r₂ < d₀ := by omega
          have hmem : 1 ≤ r₁ - r₂ ∧ ∃ b, (seq b).1 = (seq (b + (r₁ - r₂))).1 :=
            ⟨by omega, a + r₂, by rw [show a + r₂ + (r₁ - r₂) = a + r₁ by omega]; exact hEq.symm⟩
          exact Nat.find_min hex hsmall hmem
      have hlen_c : c.length = d₀ := by simpa [c] using hlen
      cases hc : c with
      | nil => simp [hc] at hlen_c; omega
      | @cons _ w _ hadj rest =>
        rw [SimpleGraph.Walk.edges_cons, List.nodup_cons]
        have hrest_path : rest.IsPath := by
          rw [SimpleGraph.Walk.isPath_def]
          simpa [hc] using hnodup_tail
        refine ⟨?_, hrest_path.isTrail.edges_nodup⟩
        intro hmem
        have hrest_len : rest.length = d₀ - 1 := by
          have : rest.length + 1 = d₀ := by simpa [hc] using hlen_c
          omega
        have hcons_edge : ∀ {x y : V} (q : G.Walk x y), q.IsPath → 2 ≤ q.length → s(x, y) ∉ q.edges := by
          intro x y q hqp hqlen
          cases q with
          | nil => simp at hqlen
          | @cons _ z _ hxz q' =>
            rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
            push Not
            constructor
            · intro hsym
              rw [Sym2.eq_iff] at hsym
              rcases hsym with ⟨_, rfl⟩ | ⟨hxz', _⟩
              · have hq'p : q'.IsPath := hqp.of_cons
                cases q' with
                | nil => simp at hqlen
                | cons _ q'' =>
                  have hdup := hq'p.support_nodup
                  rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hdup
                  exact hdup.1 (SimpleGraph.Walk.end_mem_support q'')
              · exact G.loopless.irrefl x (hxz' ▸ hxz)
            · intro hmem'
              have hx_mem : x ∈ q'.support :=
                SimpleGraph.Walk.fst_mem_support_of_mem_edges q' hmem'
              have hdup := hqp.support_nodup
              rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hdup
              exact hdup.1 hx_mem
        rw [Sym2.eq_swap] at hmem
        exact hcons_edge rest hrest_path (by omega) hmem
    · intro hnil
      have : c.length = 0 := by rw [hnil]; rfl
      have hlen_c : c.length = d₀ := by simpa [c] using hlen
      omega
    · have hc_sup : c.support = (List.range (d₀ + 1)).reverse.map (fun r => (seq (a + r)).1) := by
        simpa [c] using hsup
      rw [hc_sup, List.range_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.map_cons, List.tail_cons,
        List.nodup_map_iff_inj_on (List.nodup_reverse.mpr List.nodup_range)]
      intro r₁ hr₁ r₂ hr₂ hEq
      simp only [List.mem_reverse, List.mem_range] at hr₁ hr₂
      by_contra hne_r
      rcases lt_or_gt_of_ne hne_r with hlt | hlt
      · have hsmall : r₂ - r₁ < d₀ := by omega
        have hmem : 1 ≤ r₂ - r₁ ∧ ∃ b, (seq b).1 = (seq (b + (r₂ - r₁))).1 :=
          ⟨by omega, a + r₁, by rw [show a + r₁ + (r₂ - r₁) = a + r₂ by omega]; exact hEq⟩
        exact Nat.find_min hex hsmall hmem
      · have hsmall : r₁ - r₂ < d₀ := by omega
        have hmem : 1 ≤ r₁ - r₂ ∧ ∃ b, (seq b).1 = (seq (b + (r₁ - r₂))).1 :=
          ⟨by omega, a + r₂, by rw [show a + r₂ + (r₁ - r₂) = a + r₁ by omega]; exact hEq.symm⟩
        exact Nat.find_min hex hsmall hmem
  exact hF c hc_cyc

/-- Every orientation of a finite acyclic simple graph admits a topological vertex ordering
(`D.arc u v → σ.pos u < σ.pos v`). -/
theorem exists_topological_order {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hF : G.IsAcyclic) (D : Orientation G) :
    ∃ σ : VertexOrder V, ∀ u v, D.arc u v → σ.pos u < σ.pos v := by
  -- Build by strong induction on `S.card` a topological ordering on any `S : Finset V`.
  have haux : ∀ n : ℕ, ∀ S : Finset V, S.card = n →
      ∃ pos : V → ℕ, (∀ u ∈ S, ∀ v ∈ S, pos u = pos v → u = v) ∧
        (∀ u ∈ S, pos u < n) ∧
        (∀ u ∈ S, ∀ v ∈ S, D.arc u v → pos u < pos v) := by
    intro n
    induction n with
    | zero =>
      intro S hcard
      have hempty : S = ∅ := Finset.card_eq_zero.mp hcard
      subst hempty
      exact ⟨fun _ => 0, by simp, by simp, by simp⟩
    | succ n ih =>
      intro S hcard
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨s, hsS, hsource⟩ := exists_source_in_forest hF D S hne
      have hcard' : (S.erase s).card = n := by rw [Finset.card_erase_of_mem hsS, hcard]; omega
      obtain ⟨pos', hinj', hlt', harc'⟩ := ih (S.erase s) hcard'
      refine ⟨fun x => if x = s then 0 else pos' x + 1, ?_, ?_, ?_⟩
      · intro u hu v hv hEq
        by_cases hus : u = s <;> by_cases hvs : v = s
        · exact hus.trans hvs.symm
        · simp [hus, hvs] at hEq
        · simp [hus, hvs] at hEq
        · simp only [hus, hvs, ↓reduceIte] at hEq
          exact hinj' u (Finset.mem_erase.mpr ⟨hus, hu⟩) v (Finset.mem_erase.mpr ⟨hvs, hv⟩) (by omega)
      · intro u hu
        by_cases hus : u = s
        · simp [hus]
        · simp only [hus, ↓reduceIte]
          have := hlt' u (Finset.mem_erase.mpr ⟨hus, hu⟩)
          omega
      · intro u hu v hv huv
        by_cases hus : u = s
        · by_cases hvs : v = s
          · exfalso; subst hus hvs; exact D.asymm _ _ huv huv
          · simp [hus, hvs]
        · by_cases hvs : v = s
          · exfalso; subst hvs; exact hsource u hu huv
          · simp only [hus, hvs, ↓reduceIte]
            have := harc' u (Finset.mem_erase.mpr ⟨hus, hu⟩) v (Finset.mem_erase.mpr ⟨hvs, hv⟩) huv
            omega
  obtain ⟨pos, hinj, _, harc⟩ := haux (Fintype.card V) Finset.univ Finset.card_univ
  exact ⟨⟨pos, fun u v h => hinj u (Finset.mem_univ _) v (Finset.mem_univ _) h⟩,
    fun u v huv => harc u (Finset.mem_univ _) v (Finset.mem_univ _) huv⟩

private lemma dirWalkLe_pos_le {V : Type*} {G : SimpleGraph V} {D : Orientation G}
    {σ : VertexOrder V} (htop : ∀ u v, D.arc u v → σ.pos u < σ.pos v)
    {P : V → Prop} {k : ℕ} {u v : V} (h : DirWalkLe D P k u v) :
    σ.pos u ≤ σ.pos v := by
  induction h with
  | nil _ _ => exact le_rfl
  | cons _ harc _ ih => exact le_trans (le_of_lt (htop _ _ harc)) ih

/-- **Forest Lemma (Weak):** Every orientation `D` of every finite nonempty acyclic graph `F`
satisfies `wcolPlus D k = 1` for every `k : ℕ`. -/
theorem forest_wcolPlus_eq_one {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} (hF : G.IsAcyclic) (D : Orientation G) (k : ℕ) :
    wcolPlus D k = 1 := by
  obtain ⟨σ, htop⟩ := exists_topological_order hF D
  have hle1 : wcolPlusOfOrder D σ k ≤ 1 := by
    unfold wcolPlusOfOrder
    rw [Finset.sup_le_iff]
    intro y _
    have hsub : weakSetPlus D σ k y ⊆ {y} := by
      intro x hx
      rw [mem_weakSetPlus] at hx
      have hge := dirWalkLe_pos_le htop hx.2
      have hpos : σ.pos x = σ.pos y := le_antisymm hx.1 hge
      exact Finset.mem_singleton.mpr (σ.inj hpos)
    exact (Finset.card_le_card hsub).trans (by simp)
  have hge1 : ∀ τ : VertexOrder V, 1 ≤ wcolPlusOfOrder D τ k := by
    intro τ
    obtain ⟨y₀⟩ := ‹Nonempty V›
    calc 1 ≤ (weakSetPlus D τ k y₀).card := Finset.one_le_card.mpr ⟨y₀, mem_weakSetPlus_self D τ k y₀⟩
      _ ≤ wcolPlusOfOrder D τ k := Finset.le_sup (f := fun y => (weakSetPlus D τ k y).card) (Finset.mem_univ y₀)
  have hmem1 : 1 ∈ { m : ℕ | ∃ τ : VertexOrder V, wcolPlusOfOrder D τ k = m } :=
    ⟨σ, le_antisymm hle1 (hge1 σ)⟩
  unfold wcolPlus
  exact le_antisymm (Nat.sInf_le hmem1) (le_csInf ⟨1, hmem1⟩ (by rintro m ⟨τ, rfl⟩; exact hge1 τ))

/-- **Forest Lemma (Strong):** Every orientation `D` of every finite nonempty acyclic graph `F`
satisfies `colPlus D k = 1` for every `k : ℕ`. -/
theorem forest_colPlus_eq_one {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} (hF : G.IsAcyclic) (D : Orientation G) (k : ℕ) :
    colPlus D k = 1 := by
  obtain ⟨σ, htop⟩ := exists_topological_order hF D
  have hle1 : colPlusOfOrder D σ k ≤ 1 := by
    unfold colPlusOfOrder
    rw [Finset.sup_le_iff]
    intro y _
    have hsub : strongSetPlus D σ k y ⊆ {y} := by
      intro x hx
      rw [mem_strongSetPlus] at hx
      rcases hx with rfl | ⟨hlt, w, harc, hrest⟩
      · exact Finset.mem_singleton_self _
      · exfalso
        have hw : σ.pos y < σ.pos w := htop y w harc
        rcases hrest with ⟨rfl, _⟩ | ⟨k', _, _, hwalk⟩
        · omega
        · have hwx := dirWalkLe_pos_le htop hwalk
          omega
    exact (Finset.card_le_card hsub).trans (by simp)
  have hge1 : ∀ τ : VertexOrder V, 1 ≤ colPlusOfOrder D τ k := by
    intro τ
    obtain ⟨y₀⟩ := ‹Nonempty V›
    calc 1 ≤ (strongSetPlus D τ k y₀).card := Finset.one_le_card.mpr ⟨y₀, mem_strongSetPlus_self D τ k y₀⟩
      _ ≤ colPlusOfOrder D τ k := Finset.le_sup (f := fun y => (strongSetPlus D τ k y).card) (Finset.mem_univ y₀)
  have hmem1 : 1 ∈ { m : ℕ | ∃ τ : VertexOrder V, colPlusOfOrder D τ k = m } :=
    ⟨σ, le_antisymm hle1 (hge1 σ)⟩
  unfold colPlus
  exact le_antisymm (Nat.sInf_le hmem1) (le_csInf ⟨1, hmem1⟩ (by rintro m ⟨τ, rfl⟩; exact hge1 τ))

/-- Every finite nonempty acyclic graph `F` has `wcolPlusGraph F k = 1` for every `k`. -/
theorem forest_wcolPlusGraph_eq_one {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} (hF : G.IsAcyclic) (k : ℕ) :
    wcolPlusGraph G k = 1 := by
  unfold wcolPlusGraph
  -- Construct one orientation of `G` via an arbitrary `LinearOrder` / `Fintype.equivFin V`
  let e := Fintype.equivFin V
  let D₀ : Orientation G :=
    { arc := fun u v => G.Adj u v ∧ (e u).val < (e v).val
      arc_dec := fun u v => by classical infer_instance
      asymm := fun u v h1 h2 => by omega
      covers := fun u v => by
        constructor
        · intro hadj
          have hne : (e u).val ≠ (e v).val := fun h => G.ne_of_adj hadj (e.injective (Fin.ext h))
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · exact Or.inl ⟨hadj, hlt⟩
          · exact Or.inr ⟨hadj.symm, hlt⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact h
          · exact h.symm }
  have hset : { m : ℕ | ∃ D : Orientation G, wcolPlus D k = m } = {1} := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨D, rfl⟩; exact forest_wcolPlus_eq_one hF D k
    · rintro rfl; exact ⟨D₀, forest_wcolPlus_eq_one hF D₀ k⟩
  rw [hset, csSup_singleton]

/-! ### Section 3: Subgraph Monotonicity (Lemma M) -/

private lemma wcolOfOrder_le_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (σ : VertexOrder V) (k : ℕ) :
    wcolOfOrder D σ k ≤ Fintype.card V := by
  unfold wcolOfOrder
  rw [Finset.sup_le_iff]
  intro y _
  exact Finset.card_le_univ _

private lemma wcol_le_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Orientation G) (k : ℕ) : wcol D k ≤ Fintype.card V := by
  let e := Fintype.equivFin V
  let σ₀ : VertexOrder V := ⟨fun v => (e v).val, fun u v h => e.injective (Fin.ext h)⟩
  unfold wcol
  exact (Nat.sInf_le (show wcolOfOrder D σ₀ k ∈ { m : ℕ | ∃ σ : VertexOrder V, wcolOfOrder D σ k = m } from ⟨σ₀, rfl⟩)).trans
    (wcolOfOrder_le_card D σ₀ k)

/-- **Lemma M (Subgraph Monotonicity):** If `H ≤ G` (on the same vertex set `V`),
then `wcolGraph H k ≤ wcolGraph G k`. -/
theorem wcolGraph_mono {V : Type*} [Fintype V] [DecidableEq V]
    {H G : SimpleGraph V} (hHG : H ≤ G) (k : ℕ) :
    wcolGraph H k ≤ wcolGraph G k := by
  unfold wcolGraph
  have hneH : { m : ℕ | ∃ D : Orientation H, wcol D k = m }.Nonempty := by
    let e := Fintype.equivFin V
    let D₀ : Orientation H :=
      { arc := fun u v => H.Adj u v ∧ (e u).val < (e v).val
        arc_dec := fun u v => by classical infer_instance
        asymm := fun u v h1 h2 => by omega
        covers := fun u v => by
          constructor
          · intro hadj
            have hne : (e u).val ≠ (e v).val := fun h => H.ne_of_adj hadj (e.injective (Fin.ext h))
            rcases lt_or_gt_of_ne hne with hlt | hlt
            · exact Or.inl ⟨hadj, hlt⟩
            · exact Or.inr ⟨hadj.symm, hlt⟩
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact h; exact h.symm] }
    exact ⟨wcol D₀ k, D₀, rfl⟩
  have hbddG : BddAbove { m : ℕ | ∃ D : Orientation G, wcol D k = m } :=
    ⟨Fintype.card V, by rintro m ⟨D, rfl⟩; exact wcol_le_card D k⟩
  apply csSup_le hneH
  rintro m ⟨DH, rfl⟩
  -- Extend `DH` to an orientation `DG` of `G` by orienting `G \ H` edges via `Fintype.equivFin`.
  let e := Fintype.equivFin V
  let DG : Orientation G :=
    { arc := fun u v => DH.arc u v ∨ (G.Adj u v ∧ ¬ H.Adj u v ∧ (e u).val < (e v).val)
      arc_dec := fun u v => by classical infer_instance
      asymm := fun u v h1 h2 => by
        rcases h1 with h1 | ⟨_, hnh1, hlt1⟩
        · rcases h2 with h2 | ⟨_, hnh2, _⟩
          · exact DH.asymm u v h1 h2
          · exact hnh2 (((DH.covers u v).mpr (Or.inl h1)).symm)
        · rcases h2 with h2 | ⟨_, _, hlt2⟩
          · exact hnh1 (((DH.covers v u).mpr (Or.inl h2)).symm)
          · omega
      covers := fun u v => by
        constructor
        · intro hadj
          by_cases hH : H.Adj u v
          · rcases (DH.covers u v).mp hH with h1 | h2
            · exact Or.inl (Or.inl h1)
            · exact Or.inr (Or.inl h2)
          · have hne : (e u).val ≠ (e v).val := fun h => G.ne_of_adj hadj (e.injective (Fin.ext h))
            rcases lt_or_gt_of_ne hne with hlt | hlt
            · exact Or.inl (Or.inr ⟨hadj, hH, hlt⟩)
            · exact Or.inr (Or.inr ⟨hadj.symm, fun h => hH h.symm, hlt⟩)
        · rintro (h | h)
          · rcases h with h1 | ⟨hG, _, _⟩
            · exact hHG ((DH.covers u v).mpr (Or.inl h1))
            · exact hG
          · rcases h with h2 | ⟨hG, _, _⟩
            · exact hHG ((DH.covers u v).mpr (Or.inr h2))
            · exact hG.symm }
  have hlift : ∀ {P : V → Prop} {k' : ℕ} {u v : V},
      DirWalkLe DH P k' u v → DirWalkLe DG P k' u v := by
    intro P k' u v hw
    induction hw with
    | nil hu k => exact .nil hu k
    | cons hu harc _ ih => exact .cons hu (Or.inl harc) ih
  have hle_wcol : wcol DH k ≤ wcol DG k := by
    unfold wcol
    have hneG : { n : ℕ | ∃ σ : VertexOrder V, wcolOfOrder DG σ k = n }.Nonempty := by
      let σ₀ : VertexOrder V := ⟨fun v => (e v).val, fun u v h => e.injective (Fin.ext h)⟩
      exact ⟨wcolOfOrder DG σ₀ k, σ₀, rfl⟩
    apply le_csInf hneG
    rintro n ⟨σ, rfl⟩
    calc sInf { n' : ℕ | ∃ τ : VertexOrder V, wcolOfOrder DH τ k = n' }
        ≤ wcolOfOrder DH σ k := Nat.sInf_le ⟨σ, rfl⟩
      _ ≤ wcolOfOrder DG σ k := by
          unfold wcolOfOrder
          rw [Finset.sup_le_iff]
          intro y _
          have hsub : weakSet DH σ k y ⊆ weakSet DG σ k y := by
            intro x hx
            rw [mem_weakSet] at hx ⊢
            rcases hx with ⟨hpos, hw⟩ | ⟨hpos, hw⟩
            · exact Or.inl ⟨hpos, hlift hw⟩
            · exact Or.inr ⟨hpos, hlift hw⟩
          exact (Finset.card_le_card hsub).trans
            (Finset.le_sup (f := fun z => (weakSet DG σ k z).card) (Finset.mem_univ y))
  exact hle_wcol.trans (le_csSup hbddG ⟨DG, rfl⟩)

/-! ### Section 4: Path graphs `P_N` — acyclicity and binary-halving lower bound (Lemma C) -/

/-- The undirected path graph `P_N` on `Fin N`: `i ~ j` iff `|i - j| = 1`. -/
def pathGraph (N : ℕ) : SimpleGraph (Fin N) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun i h => by omega⟩

/-- The canonical directed path orientation `0 → 1 → ... → N - 1` of `pathGraph N`. -/
def dirPath (N : ℕ) : Orientation (pathGraph N) where
  arc i j := i.val + 1 = j.val
  arc_dec := fun i j => inferInstanceAs (Decidable (i.val + 1 = j.val))
  asymm _ _ h1 h2 := by omega
  covers _ _ := Iff.rfl

/-- Every path graph `pathGraph N` is acyclic (a tree for `N ≥ 1`). -/
theorem pathGraph_isAcyclic (N : ℕ) : (pathGraph N).IsAcyclic := by
  intro v c hc
  have hlen3 : 3 ≤ c.length := hc.three_le_length
  have hne : c.support.tail.toFinset.Nonempty := by
    have hpos : 0 < c.support.tail.length := by
      have hlen_sup : c.support.length = c.length + 1 := c.length_support
      cases h : c.support with
      | nil => simp [h] at hlen_sup
      | cons _ tl =>
        rw [h] at hlen_sup
        simp only [List.length_cons, List.tail_cons] at hlen_sup ⊢
        omega
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
    exact ⟨x, List.mem_toFinset.mpr hx⟩
  -- Let `m` be the maximum element of `c.support.tail.toFinset` by `.val`.
  obtain ⟨m, hm_mem, hm_max⟩ := Finset.exists_max_image c.support.tail.toFinset (fun x : Fin N => x.val) hne
  have hm_sup : m ∈ c.support := List.mem_of_mem_tail (List.mem_toFinset.mp hm_mem)
  -- Rotate the cycle `c` to start at `m`!
  let c' := c.rotate m hm_sup
  have hc' : c'.IsCycle := hc.rotate hm_sup
  have hc'_len : 3 ≤ c'.length := hc'.three_le_length
  have hc'_sup_sub : ∀ x ∈ c'.support, x.val ≤ m.val := by
    intro x hx
    have hx' : x ∈ c.support := (SimpleGraph.Walk.mem_support_rotate_iff c m hm_sup).mp hx
    have hx_tail : x ∈ c.support.tail := by
      cases hq : c with
      | nil => simp [hq] at hlen3
      | cons _ rest =>
        rw [hq] at hx'
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx'
        rcases hx' with rfl | hrest
        · rw [SimpleGraph.Walk.support_cons, List.tail_cons]
          exact SimpleGraph.Walk.end_mem_support rest
        · rw [SimpleGraph.Walk.support_cons, List.tail_cons]
          exact hrest
    exact hm_max x (List.mem_toFinset.mpr hx_tail)
  cases hc'eq : c' with
  | nil => simp [hc'eq] at hc'_len
  | @cons _ u₁ _ hmu₁ rest =>
    have hrest_len : 2 ≤ rest.length := by
      have : rest.length + 1 = c'.length := by rw [hc'eq]; rfl
      omega
    cases hrev : rest.reverse with
    | nil =>
      have : rest.reverse.length = 0 := by rw [hrev]; rfl
      rw [SimpleGraph.Walk.length_reverse] at this; omega
    | @cons _ u₂ _ hmu₂ rest2 =>
      have hu₁_le : u₁.val ≤ m.val := hc'_sup_sub u₁ (by rw [hc'eq]; simp)
      have hu₂_le : u₂.val ≤ m.val := by
        apply hc'_sup_sub u₂
        rw [hc'eq, SimpleGraph.Walk.support_cons, List.mem_cons]
        right
        rw [← List.mem_reverse, ← SimpleGraph.Walk.support_reverse, hrev,
          SimpleGraph.Walk.support_cons, List.mem_cons]
        right
        exact SimpleGraph.Walk.start_mem_support rest2
      -- In `pathGraph N`, both `u₁` and `u₂` are adjacent to `m` and `≤ m`, so `u₁.val + 1 = m.val = u₂.val + 1`, hence `u₁ = u₂`!
      have hu₁_eq : u₁.val + 1 = m.val := by
        rcases hmu₁ with h | h <;> omega
      have hu₂_eq : u₂.val + 1 = m.val := by
        rcases hmu₂ with h | h <;> omega
      have hu12 : u₁ = u₂ := Fin.ext (by omega)
      -- Contradiction: `c'` is a cycle of length ≥ 3, so `u₁ = u₂` violates `c'.support.tail.Nodup`!
      have hnodup : rest.support.Nodup := by
        have h1 := hc'.support_nodup
        rw [hc'eq, SimpleGraph.Walk.support_cons, List.tail_cons] at h1
        exact h1
      have hrev_nodup : rest.reverse.support.Nodup := by
        rw [SimpleGraph.Walk.support_reverse, List.nodup_reverse]
        exact hnodup
      rw [hrev, SimpleGraph.Walk.support_cons, List.nodup_cons] at hrev_nodup
      -- `rest2` is a walk from `u₂` to `u₁` of length `rest.length - 1 ≥ 1`!
      have hrest2_len : 1 ≤ rest2.length := by
        have : rest2.length + 1 = rest.reverse.length := by rw [hrev]; rfl
        rw [SimpleGraph.Walk.length_reverse] at this
        omega
      cases hrest2 : rest2 with
      | nil => simp [hrest2] at hrest2_len
      | @cons _ w _ hu2w rest3 =>
        -- `rest2` starts at `u₂` and ends at `u₁ = u₂`, so `u₂ ∈ rest3.support`, contradicting `rest2.support.Nodup`!
        have hrest2_nodup : (SimpleGraph.Walk.cons hu2w rest3).support.Nodup := by
          rw [← hrest2]
          exact hrev_nodup.2
        rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hrest2_nodup
        exact hrest2_nodup.1 (hu12 ▸ SimpleGraph.Walk.end_mem_support rest3)

/-- Directed walk along an increasing contiguous subinterval `[a, b]` of `dirPath N`. -/
private lemma dirPath_walk_le {N : ℕ} {P : Fin N → Prop} {a b : Fin N}
    (hab : a.val ≤ b.val) (hP : ∀ z : Fin N, a.val ≤ z.val → z.val ≤ b.val → P z) :
    DirWalkLe (dirPath N) P (b.val - a.val) a b := by
  suffices h : ∀ d : ℕ, ∀ x : Fin N, (hxd : x.val + d < N) →
      (∀ z : Fin N, x.val ≤ z.val → z.val ≤ x.val + d → P z) →
      DirWalkLe (dirPath N) P d x ⟨x.val + d, hxd⟩ by
    have hbN : b.val < N := b.isLt
    have hb_eq : (⟨a.val + (b.val - a.val), by omega⟩ : Fin N) = b := Fin.ext (by dsimp only; omega)
    have hw := h (b.val - a.val) a (by omega) (fun z h1 h2 => hP z h1 (by omega))
    rwa [hb_eq] at hw
  intro d
  induction d with
  | zero =>
    intro x hxd hPx
    have hEq : (⟨x.val + 0, hxd⟩ : Fin N) = x := Fin.ext (by simp)
    rw [hEq]
    exact .nil (hPx x le_rfl (by omega)) 0
  | succ d ih =>
    intro x hxd hPx
    let x' : Fin N := ⟨x.val + 1, by omega⟩
    have hx' : x'.val = x.val + 1 := rfl
    have harc : (dirPath N).arc x x' := by dsimp [dirPath, x']
    have hEq : (⟨x'.val + d, by omega⟩ : Fin N) = ⟨x.val + (d + 1), hxd⟩ :=
      Fin.ext (by dsimp only; omega)
    rw [← hEq]
    exact .cons (hPx x le_rfl (by omega)) harc
      (ih x' (by omega) (fun z h1 h2 => hPx z (by omega) (by omega)))

/-- **Lemma C (Binary-Halving Chain on `P_N`):**
For every `t ≥ 1`, `N ≥ 2^t - 1`, `k ≥ N - 1`, and any linear ordering `σ` of `Fin N`,
there exists a vertex `y : Fin N` with `|weakSet (dirPath N) σ k y| ≥ t`. -/
theorem dirPath_halving_lower {N : ℕ} (σ : VertexOrder (Fin N)) {k : ℕ} (hk : N - 1 ≤ k) :
    ∀ t : ℕ, ∀ lo hi : ℕ, lo ≤ hi → hi < N → 2 ^ t - 1 ≤ hi - lo + 1 → 1 ≤ t →
      ∃ y : Fin N, lo ≤ y.val ∧ y.val ≤ hi ∧
        t ≤ (Finset.univ.filter (fun x : Fin N =>
          lo ≤ x.val ∧ x.val ≤ hi ∧ (WeakReachPlus (dirPath N) σ k y x ∨ WeakReachMinus (dirPath N) σ k y x))).card := by
  intro t
  induction t with
  | zero => intro _ _ _ _ _ ht; omega
  | succ t ih =>
    intro lo hi hlohi hhiN hsz _
    by_cases ht0 : t = 0
    · subst ht0
      refine ⟨⟨lo, by omega⟩, le_rfl, hlohi, ?_⟩
      refine Finset.one_le_card.mpr ⟨⟨lo, by omega⟩, ?_⟩
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨le_rfl, hlohi, Or.inl ⟨le_rfl, DirWalkLe.nil (P := fun z => σ.pos ⟨lo, by omega⟩ ≤ σ.pos z) le_rfl k⟩⟩
    · -- `t ≥ 1`, so `hi - lo + 1 ≥ 2^(t+1) - 1 ≥ 3`.
      let Q : Finset (Fin N) := Finset.univ.filter (fun z : Fin N => lo ≤ z.val ∧ z.val ≤ hi)
      have hQne : Q.Nonempty := ⟨⟨lo, by omega⟩, by simp [Q, hlohi]⟩
      obtain ⟨m, hmQ, hm_min⟩ := Finset.exists_min_image Q σ.pos hQne
      have hm_lo : lo ≤ m.val := (Finset.mem_filter.mp hmQ).2.1
      have hm_hi : m.val ≤ hi := (Finset.mem_filter.mp hmQ).2.2
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [pow_succ]; omega
      have hpow_pos : 1 ≤ 2 ^ t := Nat.one_le_two_pow
      -- Pick the larger of `[lo, m - 1]` and `[m + 1, hi]`; it has size `≥ 2^t - 1`.
      have hchoice : (lo < m.val ∧ 2 ^ t - 1 ≤ (m.val - 1) - lo + 1) ∨
          (m.val < hi ∧ 2 ^ t - 1 ≤ hi - (m.val + 1) + 1) := by
        have h2t : 2 ≤ 2 ^ t := by
          have : 2 ^ 1 ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) (by omega)
          simpa using this
        omega
      -- Helper to lift the induction witness from a strict subinterval `Q' ⊆ Q \ {m}`
      have hstep : ∀ lo' hi' : ℕ, lo ≤ lo' → hi' ≤ hi → lo' ≤ hi' →
          (m.val < lo' ∨ hi' < m.val) → 2 ^ t - 1 ≤ hi' - lo' + 1 →
          ∃ y : Fin N, lo ≤ y.val ∧ y.val ≤ hi ∧
            t + 1 ≤ (Finset.univ.filter (fun x : Fin N =>
              lo ≤ x.val ∧ x.val ≤ hi ∧
                (WeakReachPlus (dirPath N) σ k y x ∨ WeakReachMinus (dirPath N) σ k y x))).card := by
        intro lo' hi' hlo' hhi' hord hdisj hsz'
        obtain ⟨y, hy1, hy2, hcard⟩ := ih lo' hi' hord (by omega) hsz' (by omega)
        refine ⟨y, by omega, by omega, ?_⟩
        let S' := Finset.univ.filter (fun x : Fin N =>
          lo' ≤ x.val ∧ x.val ≤ hi' ∧ (WeakReachPlus (dirPath N) σ k y x ∨ WeakReachMinus (dirPath N) σ k y x))
        let S := Finset.univ.filter (fun x : Fin N =>
          lo ≤ x.val ∧ x.val ≤ hi ∧ (WeakReachPlus (dirPath N) σ k y x ∨ WeakReachMinus (dirPath N) σ k y x))
        have hm_not : m ∉ S' := by
          simp only [S', mem_filter, mem_univ, true_and]
          rintro ⟨h1, h2, _⟩; omega
        have hm_in : m ∈ S := by
          simp only [S, mem_filter, mem_univ, true_and]
          refine ⟨hm_lo, hm_hi, ?_⟩
          have hyQ : y ∈ Q := by simp only [Q, mem_filter, mem_univ, true_and]; omega
          have hpos_le : σ.pos m ≤ σ.pos y := hm_min y hyQ
          rcases hdisj with hmlt | hmgt
          · -- `m < y`: directed walk `m → ... → y` of length `y - m ≤ N - 1 ≤ k` inside `Q`.
            right
            refine ⟨hpos_le, (dirPath_walk_le (by omega) (fun z hz1 hz2 => ?_)).mono_k (by omega)⟩
            exact hm_min z (by simp only [Q, mem_filter, mem_univ, true_and]; omega)
          · -- `y < m`: directed walk `y → ... → m` of length `m - y ≤ N - 1 ≤ k` inside `Q`.
            left
            refine ⟨hpos_le, (dirPath_walk_le (by omega) (fun z hz1 hz2 => ?_)).mono_k (by omega)⟩
            exact hm_min z (by simp only [Q, mem_filter, mem_univ, true_and]; omega)
        have hsub : insert m S' ⊆ S := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hm_in
          · simp only [S', S, mem_filter, mem_univ, true_and] at hx' ⊢
            exact ⟨by omega, by omega, hx'.2.2⟩
        calc t + 1 ≤ S'.card + 1 := Nat.add_le_add_right hcard 1
          _ = (insert m S').card := (Finset.card_insert_of_notMem hm_not).symm
          _ ≤ S.card := Finset.card_le_card hsub
      rcases hchoice with ⟨hmlt, hszL⟩ | ⟨hmgt, hszR⟩
      · exact hstep lo (m.val - 1) le_rfl (by omega) (by omega) (Or.inr (by omega)) hszL
      · exact hstep (m.val + 1) hi (by omega) le_rfl (by omega) (Or.inl (by omega)) hszR

/-- For every `t ≥ 1`, `N = 2^t - 1`, and `k ≥ N - 1`, `wcolGraph (pathGraph N) k ≥ t`. -/
theorem pathGraph_wcol_ge {t k : ℕ} (ht : 1 ≤ t) (hk : (2 ^ t - 1) - 1 ≤ k) :
    t ≤ wcolGraph (pathGraph (2 ^ t - 1)) k := by
  set N := 2 ^ t - 1
  have hNpos : 1 ≤ N := by
    have : 2 ^ 1 ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
    omega
  have hwcol_dir : t ≤ wcol (dirPath N) k := by
    unfold wcol
    have hne : { m : ℕ | ∃ σ : VertexOrder (Fin N), wcolOfOrder (dirPath N) σ k = m }.Nonempty := by
      let σ₀ : VertexOrder (Fin N) := ⟨fun v => v.val, fun _ _ h => Fin.ext h⟩
      exact ⟨wcolOfOrder (dirPath N) σ₀ k, σ₀, rfl⟩
    apply le_csInf hne
    rintro m ⟨σ, rfl⟩
    obtain ⟨y, _, _, hcard⟩ := dirPath_halving_lower σ hk t 0 (N - 1) (by omega) (by omega) (by omega) ht
    have hsub : Finset.univ.filter (fun x : Fin N =>
        0 ≤ x.val ∧ x.val ≤ N - 1 ∧
          (WeakReachPlus (dirPath N) σ k y x ∨ WeakReachMinus (dirPath N) σ k y x)) ⊆
        weakSet (dirPath N) σ k y := by
      intro x hx
      rw [mem_weakSet]
      exact (Finset.mem_filter.mp hx).2.2.2
    calc t ≤ (weakSet (dirPath N) σ k y).card := hcard.trans (Finset.card_le_card hsub)
      _ ≤ wcolOfOrder (dirPath N) σ k :=
        Finset.le_sup (f := fun z => (weakSet (dirPath N) σ k z).card) (Finset.mem_univ y)
  have hbdd : BddAbove { m : ℕ | ∃ D : Orientation (pathGraph N), wcol D k = m } :=
    ⟨Fintype.card (Fin N), by rintro m ⟨D, rfl⟩; exact wcol_le_card D k⟩
  exact hwcol_dir.trans (le_csSup hbdd ⟨dirPath N, rfl⟩)

/-- **Main Theorem 1 (Disproof of General Weak Problem 3.5):**
There exists NO function `g : ℕ → ℕ` such that `wcolGraph G k ≤ g (wcolPlusGraph G k)` holds
for all finite nonempty graphs `G` and all `k ≥ 1`. -/
theorem no_uniform_weak_bound :
    ¬ ∃ g : ℕ → ℕ, ∀ (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N)) (k : ℕ), 1 ≤ k →
        wcolGraph G k ≤ g (wcolPlusGraph G k) := by
  rintro ⟨g, hg⟩
  let t := g 1 + 1
  have ht : 1 ≤ t := by omega
  let N := 2 ^ t - 1
  have hNpos : 1 ≤ N := by
    have : 2 ^ 1 ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
    omega
  have : NeZero N := ⟨by omega⟩
  let k := max 1 (N - 1)
  have hk1 : 1 ≤ k := le_max_left _ _
  have hkN : N - 1 ≤ k := le_max_right _ _
  have hupper := hg N (pathGraph N) k hk1
  have hwcolp : wcolPlusGraph (pathGraph N) k = 1 :=
    forest_wcolPlusGraph_eq_one (pathGraph_isAcyclic N) k
  have hwcol_lb : t ≤ wcolGraph (pathGraph N) k := pathGraph_wcol_ge ht hkN
  rw [hwcolp] at hupper
  omega

/-! ### Section 5: Exact `P₄` Counterexample to Problem 3.6 and Factor-2 Weak Bound (all `k ≥ 2`) -/

private lemma dirPath4_wcol_ge_three {k : ℕ} (hk : 2 ≤ k) :
    3 ≤ wcol (dirPath 4) k := by
  unfold wcol
  have hne : { m : ℕ | ∃ σ : VertexOrder (Fin 4), wcolOfOrder (dirPath 4) σ k = m }.Nonempty :=
    ⟨wcolOfOrder (dirPath 4) ⟨fun v => v.val, fun _ _ h => Fin.ext h⟩ k, _, rfl⟩
  apply le_csInf hne
  rintro m ⟨σ, rfl⟩
  -- Helper: show `a, b, c ∈ weakSet (dirPath 4) σ k y` for 3 pairwise distinct vertices
  have hcard3 : ∀ (y a b c : Fin 4), a ≠ b → a ≠ c → b ≠ c →
      (WeakReachPlus (dirPath 4) σ k y a ∨ WeakReachMinus (dirPath 4) σ k y a) →
      (WeakReachPlus (dirPath 4) σ k y b ∨ WeakReachMinus (dirPath 4) σ k y b) →
      (WeakReachPlus (dirPath 4) σ k y c ∨ WeakReachMinus (dirPath 4) σ k y c) →
      3 ≤ wcolOfOrder (dirPath 4) σ k := by
    intro y a b c hab hac hbc ha hb hc
    have hsub : ({a, b, c} : Finset (Fin 4)) ⊆ weakSet (dirPath 4) σ k y := by
      intro x hx
      rw [mem_weakSet]
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    have hc3 : ({a, b, c} : Finset (Fin 4)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    calc 3 = ({a, b, c} : Finset (Fin 4)).card := hc3.symm
      _ ≤ (weakSet (dirPath 4) σ k y).card := Finset.card_le_card hsub
      _ ≤ wcolOfOrder (dirPath 4) σ k :=
        Finset.le_sup (f := fun z => (weakSet (dirPath 4) σ k z).card) (Finset.mem_univ y)
  -- Helper for length-0, length-1, length-2 directed reachability on `dirPath 4`
  have hself : ∀ y : Fin 4, WeakReachPlus (dirPath 4) σ k y y ∨ WeakReachMinus (dirPath 4) σ k y y := by
    intro y
    exact Or.inl ⟨le_rfl, DirWalkLe.nil (P := fun z => σ.pos y ≤ σ.pos z) le_rfl k⟩
  have hstepR : ∀ {x y : Fin 4}, x.val + 1 = y.val → σ.pos x ≤ σ.pos y →
      WeakReachPlus (dirPath 4) σ k y x ∨ WeakReachMinus (dirPath 4) σ k y x := fun {x y} hxy hpos =>
    Or.inr ⟨hpos, (DirWalkLe.cons (P := fun z => σ.pos x ≤ σ.pos z) le_rfl hxy
      (DirWalkLe.nil (P := fun z => σ.pos x ≤ σ.pos z) hpos 0)).mono_k (by omega)⟩
  have hstepL : ∀ {x y : Fin 4}, y.val + 1 = x.val → σ.pos x ≤ σ.pos y →
      WeakReachPlus (dirPath 4) σ k y x ∨ WeakReachMinus (dirPath 4) σ k y x := fun {x y} hyx hpos =>
    Or.inl ⟨hpos, (DirWalkLe.cons (P := fun z => σ.pos x ≤ σ.pos z) hpos hyx
      (DirWalkLe.nil (P := fun z => σ.pos x ≤ σ.pos z) le_rfl 0)).mono_k (by omega)⟩
  have h2R : ∀ {x w y : Fin 4}, x.val + 1 = w.val → w.val + 1 = y.val →
      σ.pos x ≤ σ.pos w → σ.pos x ≤ σ.pos y →
      WeakReachPlus (dirPath 4) σ k y x ∨ WeakReachMinus (dirPath 4) σ k y x :=
    fun {x _ _} hxw hwy hpw hpy =>
      Or.inr ⟨hpy, (DirWalkLe.cons (P := fun z => σ.pos x ≤ σ.pos z) le_rfl hxw
        (DirWalkLe.cons (P := fun z => σ.pos x ≤ σ.pos z) hpw hwy
          (DirWalkLe.nil (P := fun z => σ.pos x ≤ σ.pos z) hpy 0))).mono_k hk⟩
  have h2L : ∀ {x w y : Fin 4}, y.val + 1 = w.val → w.val + 1 = x.val →
      σ.pos x ≤ σ.pos w → σ.pos x ≤ σ.pos y →
      WeakReachPlus (dirPath 4) σ k y x ∨ WeakReachMinus (dirPath 4) σ k y x :=
    fun {x _ _} hyw hwx hpw hpy =>
      Or.inl ⟨hpy, (DirWalkLe.cons (P := fun z => σ.pos x ≤ σ.pos z) hpy hyw
        (DirWalkLe.cons (P := fun z => σ.pos x ≤ σ.pos z) hpw hwx
          (DirWalkLe.nil (P := fun z => σ.pos x ≤ σ.pos z) le_rfl 0))).mono_k hk⟩
  -- Let `f` be the `σ`-minimum vertex of `Fin 4`.
  obtain ⟨f, _, hf_min⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 4)) σ.pos Finset.univ_nonempty
  have hf_le : ∀ z : Fin 4, σ.pos f ≤ σ.pos z := fun z => hf_min z (Finset.mem_univ z)
  fin_cases f
  · -- `f = 0`: split on `σ`-minimum `g` of `{1, 2, 3}`
    obtain ⟨g, hg_mem, hg_min⟩ := Finset.exists_min_image ({1, 2, 3} : Finset (Fin 4)) σ.pos (by simp)
    simp only [mem_insert, mem_singleton] at hg_mem
    rcases hg_mem with rfl | rfl | rfl
    · -- `g = 1`: `W(2) ⊇ {2, 1, 0}`
      exact hcard3 2 2 1 0 (by decide) (by decide) (by decide)
        (hself 2) (hstepR rfl (hg_min 2 (by simp))) (h2R rfl rfl (hf_le 1) (hf_le 2))
    · -- `g = 2`: `W(1) ⊇ {1, 0, 2}`
      exact hcard3 1 1 0 2 (by decide) (by decide) (by decide)
        (hself 1) (hstepR rfl (hf_le 1)) (hstepL rfl (hg_min 1 (by simp)))
    · -- `g = 3`: `W(2) ⊇ {2, 3, 0}`
      exact hcard3 2 2 3 0 (by decide) (by decide) (by decide)
        (hself 2) (hstepL rfl (hg_min 2 (by simp))) (h2R rfl rfl (hf_le 1) (hf_le 2))
  · -- `f = 1`: compare `pos 2` and `pos 3`
    rcases le_total (σ.pos 2) (σ.pos 3) with h23 | h32
    · exact hcard3 3 3 2 1 (by decide) (by decide) (by decide)
        (hself 3) (hstepR rfl h23) (h2R rfl rfl (hf_le 2) (hf_le 3))
    · exact hcard3 2 2 1 3 (by decide) (by decide) (by decide)
        (hself 2) (hstepR rfl (hf_le 2)) (hstepL rfl h32)
  · -- `f = 2`: compare `pos 1` and `pos 0`
    rcases le_total (σ.pos 1) (σ.pos 0) with h10 | h01
    · exact hcard3 0 0 1 2 (by decide) (by decide) (by decide)
        (hself 0) (hstepL rfl h10) (h2L rfl rfl (hf_le 1) (hf_le 0))
    · exact hcard3 1 1 2 0 (by decide) (by decide) (by decide)
        (hself 1) (hstepL rfl (hf_le 1)) (hstepR rfl h01)
  · -- `f = 3`: split on `σ`-minimum `g` of `{0, 1, 2}`
    obtain ⟨g, hg_mem, hg_min⟩ := Finset.exists_min_image ({0, 1, 2} : Finset (Fin 4)) σ.pos (by simp)
    simp only [mem_insert, mem_singleton] at hg_mem
    rcases hg_mem with rfl | rfl | rfl
    · -- `g = 0`: `W(1) ⊇ {1, 0, 3}`
      exact hcard3 1 1 0 3 (by decide) (by decide) (by decide)
        (hself 1) (hstepR rfl (hg_min 1 (by simp))) (h2L rfl rfl (hf_le 2) (hf_le 1))
    · -- `g = 1`: `W(2) ⊇ {2, 3, 1}`
      exact hcard3 2 2 3 1 (by decide) (by decide) (by decide)
        (hself 2) (hstepL rfl (hf_le 2)) (hstepR rfl (hg_min 2 (by simp)))
    · -- `g = 2`: `W(1) ⊇ {1, 2, 3}`
      exact hcard3 1 1 2 3 (by decide) (by decide) (by decide)
        (hself 1) (hstepL rfl (hg_min 1 (by simp))) (h2L rfl rfl (hf_le 2) (hf_le 1))

private lemma path4_wcol_le_three (D : Orientation (pathGraph 4)) (k : ℕ) :
    wcol D k ≤ 3 := by
  -- Use ordering `σ : 1 < 2 < 0 < 3` (positions: `pos 1 = 0, pos 2 = 1, pos 0 = 2, pos 3 = 3`).
  let pos4 : Fin 4 → ℕ
    | ⟨0, _⟩ => 2
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 1
    | ⟨3, _⟩ => 3
  let σ : VertexOrder (Fin 4) := ⟨pos4, by
    intro u v h; fin_cases u <;> fin_cases v <;> simp_all [pos4]⟩
  have hle : wcolOfOrder D σ k ≤ 3 := by
    unfold wcolOfOrder
    rw [Finset.sup_le_iff]
    intro y _
    -- Show `weakSet D σ k y` misses at least one vertex of `Fin 4`, so `card ≤ 3`!
    have hmiss : ∃ z : Fin 4, z ∉ weakSet D σ k y := by
      fin_cases y
      · -- `y = 0` (`pos = 2`): `3` has `pos = 3 > 2`, so `3 ∉ weakSet`
        refine ⟨3, ?_⟩
        rw [mem_weakSet]
        rintro (⟨h, _⟩ | ⟨h, _⟩) <;> simp [σ, pos4] at h
      · -- `y = 1` (`pos = 0`): `3 ∉ weakSet`
        refine ⟨3, ?_⟩
        rw [mem_weakSet]
        rintro (⟨h, _⟩ | ⟨h, _⟩) <;> simp [σ, pos4] at h
      · -- `y = 2` (`pos = 1`): `3 ∉ weakSet`
        refine ⟨3, ?_⟩
        rw [mem_weakSet]
        rintro (⟨h, _⟩ | ⟨h, _⟩) <;> simp [σ, pos4] at h
      · -- `y = 3` (`pos = 3`): `0 ∉ weakSet` because every walk between `0` and `3` visits `1` (`pos 1 = 0 < 2 = pos 0`)!
        refine ⟨0, ?_⟩
        rw [mem_weakSet]
        have htrap : ∀ {m' : ℕ} {a b : Fin 4},
            DirWalkLe D (fun z => σ.pos 0 ≤ σ.pos z) m' a b →
            b = 0 → (a = 2 ∨ a = 3) → False := by
          intro m' a b hwa
          induction hwa with
          | nil _ _ =>
            rintro rfl ha
            rcases ha with h | h <;> exact absurd h (by decide)
          | @cons _ a w b _ harc' rest' ih' =>
            rintro rfl ha
            have hadj' : (pathGraph 4).Adj a w := (D.covers a w).mpr (Or.inl harc')
            have hw_ok : σ.pos 0 ≤ σ.pos w := by
              cases rest' with
              | nil hw' _ => exact hw'
              | cons hw' _ _ => exact hw'
            have hw_ne1 : w ≠ 1 := by
              intro h1; subst h1; simp [σ, pos4] at hw_ok
            have hw23 : w = 2 ∨ w = 3 := by
              rcases ha with rfl | rfl
              · fin_cases w
                · simp [pathGraph] at hadj'
                · exact absurd rfl hw_ne1
                · exact Or.inl rfl
                · exact Or.inr rfl
              · fin_cases w
                · simp [pathGraph] at hadj'
                · simp [pathGraph] at hadj'
                · exact Or.inl rfl
                · exact Or.inr rfl
            exact ih' rfl hw23
        have hno_0_to_3 : ∀ {m' : ℕ} {a b : Fin 4},
            DirWalkLe D (fun z => σ.pos 0 ≤ σ.pos z) m' a b →
            a = 0 → b = 3 → False := by
          intro m' a b hwa
          cases hwa with
          | nil _ _ => rintro rfl h; exact absurd h (by decide)
          | @cons _ a w b _ harc' rest' =>
            rintro rfl rfl
            have hadj' : (pathGraph 4).Adj 0 w := (D.covers 0 w).mpr (Or.inl harc')
            have hw_ok : σ.pos 0 ≤ σ.pos w := by
              cases rest' with
              | nil hw' _ => exact hw'
              | cons hw' _ _ => exact hw'
            have hw1 : w = 1 := by
              fin_cases w <;> simp [pathGraph] at hadj' ⊢
            subst hw1
            simp [σ, pos4] at hw_ok
        rintro (⟨_, hw⟩ | ⟨_, hw⟩)
        · exact htrap hw rfl (Or.inr rfl)
        · exact hno_0_to_3 hw rfl rfl
    obtain ⟨z, hz⟩ := hmiss
    have hsub : weakSet D σ k y ⊆ Finset.univ.erase z := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun h => hz (h ▸ hx), Finset.mem_univ x⟩
    calc (weakSet D σ k y).card ≤ (Finset.univ.erase z).card := Finset.card_le_card hsub
      _ = 3 := by rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, Fintype.card_fin]
  unfold wcol
  exact (Nat.sInf_le (show wcolOfOrder D σ k ∈ { m : ℕ | ∃ τ : VertexOrder (Fin 4), wcolOfOrder D τ k = m } from ⟨σ, rfl⟩)).trans hle

/-- **Main Theorem 2 (`P₄` Exact Values & Disproof of Problem 3.6 and Factor-2 Weak Bound):**
For every `k ≥ 2`:
1. `wcolGraph (pathGraph 4) k = 3`;
2. `wcolPlusGraph (pathGraph 4) k = 1`, so `wcolGraph (pathGraph 4) k > 2 * wcolPlusGraph (pathGraph 4) k`;
3. No orientation `D` of `pathGraph 4` satisfies `wcolPlus D k = (wcolGraph (pathGraph 4) k + 1) / 2` (`= ⌈3/2⌉ = 2`). -/
theorem p4_disproves_prob35_prob36 {k : ℕ} (hk : 2 ≤ k) :
    wcolGraph (pathGraph 4) k = 3 ∧
    wcolPlusGraph (pathGraph 4) k = 1 ∧
    wcolGraph (pathGraph 4) k > 2 * wcolPlusGraph (pathGraph 4) k ∧
    ¬ ∃ D : Orientation (pathGraph 4),
        wcolPlus D k = (wcolGraph (pathGraph 4) k + 1) / 2 := by
  have hwcol_eq : wcolGraph (pathGraph 4) k = 3 := by
    unfold wcolGraph
    have hbdd : BddAbove { m : ℕ | ∃ D : Orientation (pathGraph 4), wcol D k = m } :=
      ⟨3, by rintro m ⟨D, rfl⟩; exact path4_wcol_le_three D k⟩
    have hne : { m : ℕ | ∃ D : Orientation (pathGraph 4), wcol D k = m }.Nonempty :=
      ⟨wcol (dirPath 4) k, dirPath 4, rfl⟩
    apply le_antisymm
    · exact csSup_le hne (by rintro m ⟨D, rfl⟩; exact path4_wcol_le_three D k)
    · exact (dirPath4_wcol_ge_three hk).trans (le_csSup hbdd ⟨dirPath 4, rfl⟩)
  have hwcolp_eq : wcolPlusGraph (pathGraph 4) k = 1 :=
    forest_wcolPlusGraph_eq_one (pathGraph_isAcyclic 4) k
  refine ⟨hwcol_eq, hwcolp_eq, by omega, ?_⟩
  rintro ⟨D, hD⟩
  have h1 : wcolPlus D k = 1 := forest_wcolPlus_eq_one (pathGraph_isAcyclic 4) D k
  rw [hwcol_eq, h1] at hD
  omega

end LiNesetrilYangWcol
