import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Disproof of Zai–Lv–Sabir / Tian–Dong Conjecture 1.14 for Every `r ≥ 5`

Disproves Conjecture 1.14 of Jingfan Zai, Wenjing Lv, and Eminjan Sabir,
*Spanning cyclability of split graphs* (`arXiv:2611.32794v1`, 24 Nov 2026;
originally Conjecture 6.1 of Tian–Dong `arXiv:2603.12770v1`):

> Let `r ≥ 3` be an integer. Every `r`-connected `{K_{1,r+1}, K_{1,r+1}+e}`-free
> split graph with at least `2r + 7` vertices is Hamilton-connected.

We construct a counterexample for **every** `r ≥ 5`:
- For `r = 5`: the 22-vertex Paley `(11, 5, 2)` biplane split graph (`m = 11`,
  connection set `S = {1, 3, 4, 5, 9} ⊆ ZMod 11`), satisfying `22 ≥ 17 = 2·5 + 7`.
- For every `r ≥ 6`: the `(2r + 8)`-vertex circulant split graph (`m = r + 4`,
  connection set `S = {0, 1, ..., r - 1} ⊆ Fin (r + 4)`), satisfying `2r + 8 ≥ 2r + 7`.

Both come from a single unified `splitCirculant m S` construction on `Fin m ⊕ Fin m`
with clique `Sum.inl` and independent set `Sum.inr`:
1. `r`-connected: after deleting `< r` vertices, the surviving clique is nonempty and
   every surviving independent vertex has a clique neighbor.
2. `{K_{1,r+1}, K_{1,r+1}+e}`-free: any `r + 1` neighbors of any center induce at
   least 2 edges (immediate from `|S| = r` and `∀ d ≠ 0, |S ∩ (S + d)| ≥ 2`).
3. Not Hamilton-connected: any spanning path between two distinct clique vertices
   injects the `m` independent positions `t ↦ p(t + 1)` into the `m - 1` clique
   vertices other than `p(0)`, contradiction.
-/

namespace ZaiLvSabirSplitHamilton

/-- A graph is a split graph if its vertices partition into a clique `C` and
an independent set `I = Cᶜ`. -/
def IsSplitGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ C : Set V,
    (∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v) ∧
    (∀ u ∉ C, ∀ v ∉ C, ¬ G.Adj u v)

/-- A graph `G` on `V` is `r`-connected (standard vertex connectivity):
`|V| > r` and removing any set `D` of fewer than `r` vertices leaves a
connected induced subgraph (every two vertices in `Dᶜ` are joined by a walk
avoiding `D`). -/
def IsRConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ) : Prop :=
  r < Fintype.card V ∧
  ∀ (D : Finset V), D.card < r →
    ∀ u v : V, u ∉ D → v ∉ D →
      ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∉ D

/-- A graph is `{K_{1,r+1}, K_{1,r+1}+e}`-free (induced) iff for every vertex `c`
and every `(r + 1)`-element subset `L` of `N(c)`, at least two unordered pairs
in `L` are adjacent in `G` (equivalently, there exist two distinct unordered
edges `{u₁, v₁} ≠ {u₂, v₂}` inside `L`, i.e., `card` of ordered adjacent pairs
in `L × L` is at least `4`). -/
def IsStarAndStarPlusEFree {V : Type*} [DecidableEq V] (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ (c : V) (L : Finset V),
    L.card = r + 1 →
    (∀ x ∈ L, G.Adj c x) →
    ∃ e₁ e₂ : Sym2 V,
      e₁ ≠ e₂ ∧
      e₁ ∈ G.edgeSet ∧ e₂ ∈ G.edgeSet ∧
      (∀ x ∈ e₁, x ∈ L) ∧ (∀ x ∈ e₂, x ∈ L)

/-- A Hamilton path from `u` to `v` in a finite graph `G` on `n` vertices is a
bijection `p : Fin n ≃ V` with `p 0 = u`, `p (n - 1) = v`, and consecutive
vertices adjacent. -/
structure HamiltonPath {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) where
  hn : 0 < Fintype.card V
  perm : Fin (Fintype.card V) ≃ V
  start_eq : perm ⟨0, hn⟩ = u
  end_eq : perm ⟨Fintype.card V - 1, Nat.sub_lt hn Nat.one_pos⟩ = v
  adj_step : ∀ (i : ℕ) (hi : i + 1 < Fintype.card V),
    G.Adj (perm ⟨i, Nat.lt_of_succ_lt hi⟩) (perm ⟨i + 1, hi⟩)

/-- A graph is Hamilton-connected if every pair of distinct vertices is joined by
a Hamilton path. -/
def IsHamiltonConnected {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → Nonempty (HamiltonPath G u v)

/-- The split circulant graph on `ZMod m ⊕ ZMod m` (for `m ≥ 1`):
`Sum.inl` forms a clique of size `m`, `Sum.inr` forms an independent set of size `m`,
and `Sum.inl a` is adjacent to `Sum.inr b` iff `b - a ∈ S`. -/
def splitCirculant (m : ℕ) [NeZero m] (S : Finset (ZMod m)) : SimpleGraph (ZMod m ⊕ ZMod m) where
  Adj x y :=
    match x, y with
    | Sum.inl a, Sum.inl b => a ≠ b
    | Sum.inl a, Sum.inr b => b - a ∈ S
    | Sum.inr b, Sum.inl a => b - a ∈ S
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨fun x y h => by cases x <;> cases y <;> simp_all [ne_comm]⟩
  loopless := ⟨fun x => by cases x <;> simp⟩

lemma splitCirculant_isSplit (m : ℕ) [NeZero m] (S : Finset (ZMod m)) :
    IsSplitGraph (splitCirculant m S) := by
  refine ⟨Set.range Sum.inl, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
    exact fun h => hne (congrArg Sum.inl h)
  · rintro x hx y hy
    cases x with
    | inl a => exact absurd ⟨a, rfl⟩ hx
    | inr a =>
      cases y with
      | inl b => exact absurd ⟨b, rfl⟩ hy
      | inr b => simp [splitCirculant]

private lemma mem_support_append {V : Type*} {G : SimpleGraph V} {u v w x : V}
    (p : G.Walk u v) (q : G.Walk v w) (hx : x ∈ (p.append q).support) :
    x ∈ p.support ∨ x ∈ q.support := by
  induction p with
  | nil => exact Or.inr hx
  | cons hadj p ih =>
    simp only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.support_cons, List.mem_cons] at hx ⊢
    rcases hx with rfl | htail
    · exact Or.inl (Or.inl rfl)
    · rcases ih q htail with h1 | h2
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h2

lemma splitCirculant_rConnected {m r : ℕ} [NeZero m] (S : Finset (ZMod m))
    (hS : S.card = r) (hm : r < m) :
    IsRConnected (splitCirculant m S) r := by
  constructor
  · simp [Fintype.card_sum, ZMod.card]; omega
  · intro D hD u v hu hv
    -- There exists a surviving clique vertex `c₀ ∉ D` since `m > r > D.card`
    have hex_c : ∃ a : ZMod m, Sum.inl a ∉ D := by
      by_contra hall
      push Not at hall
      have hsub : (Finset.univ.image (Sum.inl : ZMod m → ZMod m ⊕ ZMod m)) ⊆ D := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨a, _, rfl⟩
        exact hall a
      have hcard : m ≤ D.card := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ, ZMod.card] at h1
        exact h1
      omega
    -- Every vertex `w ∉ D` has a walk avoiding `D` to some clique vertex `Sum.inl a ∉ D`
    have htoClique : ∀ w : ZMod m ⊕ ZMod m, w ∉ D →
        ∃ a : ZMod m, Sum.inl a ∉ D ∧
          ∃ p : (splitCirculant m S).Walk w (Sum.inl a), ∀ z ∈ p.support, z ∉ D := by
      intro w hw
      cases w with
      | inl a => exact ⟨a, hw, SimpleGraph.Walk.nil, by simp [hw]⟩
      | inr b =>
        -- `b` has `r` clique neighbors `{Sum.inl (b - s) | s ∈ S}`; since `D.card < r`, one avoids `D`
        have hex_nbr : ∃ s ∈ S, Sum.inl (b - s) ∉ D := by
          by_contra hall
          push Not at hall
          have hsub : S.image (fun s => (Sum.inl (b - s) : ZMod m ⊕ ZMod m)) ⊆ D := by
            intro x hx
            rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
            exact hall s hs
          have hinj : Function.Injective (fun s : ZMod m => (Sum.inl (b - s) : ZMod m ⊕ ZMod m)) := by
            intro s₁ s₂ h
            have := Sum.inl.inj h
            exact sub_right_inj.mp this
          have hcard : r ≤ D.card := by
            have h1 := Finset.card_le_card hsub
            rw [Finset.card_image_of_injective _ hinj, hS] at h1
            exact h1
          omega
        rcases hex_nbr with ⟨s, hs, haD⟩
        have hadj : (splitCirculant m S).Adj (Sum.inr b) (Sum.inl (b - s)) := by
          simp [splitCirculant, sub_sub_cancel, hs]
        refine ⟨b - s, haD, SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
        intro z hz
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl <;> assumption
    rcases htoClique u hu with ⟨au, hauD, pu, hpu⟩
    rcases htoClique v hv with ⟨av, havD, pv, hpv⟩
    by_cases heq : au = av
    · subst heq
      refine ⟨pu.append pv.reverse, ?_⟩
      intro w hw
      rcases mem_support_append pu pv.reverse hw with h1 | h2
      · exact hpu w h1
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h2
        exact hpv w h2
    · have hadj : (splitCirculant m S).Adj (Sum.inl au) (Sum.inl av) := heq
      let mid : (splitCirculant m S).Walk (Sum.inl au) (Sum.inl av) :=
        SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
      refine ⟨(pu.append mid).append pv.reverse, ?_⟩
      intro w hw
      rcases mem_support_append (pu.append mid) pv.reverse hw with h12 | h3
      · rcases mem_support_append pu mid h12 with h1 | h2
        · exact hpu w h1
        · simp only [mid, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false] at h2
          rcases h2 with rfl | rfl <;> assumption
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h3
        exact hpv w h3

lemma splitCirculant_not_hamiltonConnected {m : ℕ} [NeZero m] (S : Finset (ZMod m))
    (hm : 2 ≤ m) :
    ¬ IsHamiltonConnected (splitCirculant m S) := by
  intro hHC
  have hne : (Sum.inl (0 : ZMod m) : ZMod m ⊕ ZMod m) ≠ Sum.inl 1 := by
    intro h
    have h01 : (0 : ZMod m) = 1 := Sum.inl.inj h
    have : Fact (1 < m) := ⟨by omega⟩
    exact zero_ne_one h01
  rcases hHC (Sum.inl 0) (Sum.inl 1) hne with ⟨hp⟩
  let N := Fintype.card (ZMod m ⊕ ZMod m)
  have hN : N = 2 * m := by simp [N, Fintype.card_sum, ZMod.card]; omega
  -- Set of positions `t : Fin N` mapped to `Sum.inr _` (independent set)
  let Ipos : Finset (Fin N) := Finset.univ.filter (fun t => (hp.perm t).isRight)
  have hIpos_card : Ipos.card = m := by
    have hbij : Ipos.card = (Finset.univ.filter (fun v : ZMod m ⊕ ZMod m => v.isRight)).card := by
      refine Finset.card_bij (fun t _ => hp.perm t) ?_ ?_ ?_
      · intro t ht
        simp only [Ipos, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        exact ht
      · intro t₁ _ t₂ _ heq; exact hp.perm.injective heq
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        refine ⟨hp.perm.symm v, ?_, hp.perm.apply_symm_apply v⟩
        simp only [Ipos, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.apply_symm_apply]
        exact hv
    rw [hbij]
    have hset : Finset.univ.filter (fun v : ZMod m ⊕ ZMod m => v.isRight) =
        Finset.univ.image (Sum.inr : ZMod m → ZMod m ⊕ ZMod m) := by
      ext v; cases v <;> simp
    rw [hset, Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, ZMod.card]
  -- Every `t ∈ Ipos` satisfies `t.val + 1 < N`, `hp.perm (t + 1)` is `Sum.inl _` and `≠ Sum.inl 0`
  let target : Finset (ZMod m) := Finset.univ.erase 0
  have htarget_card : target.card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hIpos_lt : ∀ t ∈ Ipos, t.val + 1 < N := by
    intro t ht
    simp only [Ipos, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    by_contra hge
    have hteq : t = ⟨N - 1, Nat.sub_lt hp.hn Nat.one_pos⟩ := Fin.ext (by change t.val = N - 1; omega)
    rw [hteq, hp.end_eq] at ht
    simp at ht
  have hsucc_left : ∀ (t : Fin N) (ht : t ∈ Ipos),
      ∃ a : ZMod m, a ≠ 0 ∧ hp.perm ⟨t.val + 1, hIpos_lt t ht⟩ = Sum.inl a := by
    intro t ht
    have htr : (hp.perm t).isRight := (Finset.mem_filter.mp ht).2
    have hadj := hp.adj_step t.val (hIpos_lt t ht)
    cases hpt : hp.perm t with
    | inl a => rw [hpt] at htr; simp at htr
    | inr b =>
      cases hpt1 : hp.perm ⟨t.val + 1, hIpos_lt t ht⟩ with
      | inr b' =>
        rw [hpt, hpt1] at hadj
        simp [splitCirculant] at hadj
      | inl a =>
        refine ⟨a, ?_, rfl⟩
        intro ha0
        subst ha0
        have heq0 : (⟨t.val + 1, hIpos_lt t ht⟩ : Fin N) = ⟨0, hp.hn⟩ :=
          hp.perm.injective (by rw [hpt1, hp.start_eq])
        have : t.val + 1 = 0 := congrArg Fin.val heq0
        omega
  -- Map `t ∈ Ipos` injectively into `target` (card `m - 1`) via `t ↦ a` where `hp.perm (t+1) = Sum.inl a`
  have hle : Ipos.card ≤ target.card := by
    refine Finset.card_le_card_of_injOn
      (fun t => match hp.perm ⟨(t.val + 1) % N, Nat.mod_lt _ hp.hn⟩ with
        | Sum.inl a => a
        | Sum.inr _ => 0) ?_ ?_
    · intro t ht
      dsimp only
      rcases hsucc_left t ht with ⟨a, ha0, haeq⟩
      have hmod : (t.val + 1) % N = t.val + 1 := Nat.mod_eq_of_lt (hIpos_lt t ht)
      have hfin : (⟨(t.val + 1) % N, Nat.mod_lt _ hp.hn⟩ : Fin N) = ⟨t.val + 1, hIpos_lt t ht⟩ :=
        Fin.ext hmod
      rw [hfin, haeq]
      exact Finset.mem_erase.mpr ⟨ha0, Finset.mem_univ _⟩
    · intro t₁ ht₁ t₂ ht₂ heq
      dsimp only at heq
      rcases hsucc_left t₁ ht₁ with ⟨a₁, _, haeq₁⟩
      rcases hsucc_left t₂ ht₂ with ⟨a₂, _, haeq₂⟩
      have hfin₁ : (⟨(t₁.val + 1) % N, Nat.mod_lt _ hp.hn⟩ : Fin N) = ⟨t₁.val + 1, hIpos_lt t₁ ht₁⟩ :=
        Fin.ext (Nat.mod_eq_of_lt (hIpos_lt t₁ ht₁))
      have hfin₂ : (⟨(t₂.val + 1) % N, Nat.mod_lt _ hp.hn⟩ : Fin N) = ⟨t₂.val + 1, hIpos_lt t₂ ht₂⟩ :=
        Fin.ext (Nat.mod_eq_of_lt (hIpos_lt t₂ ht₂))
      rw [hfin₁, haeq₁, hfin₂, haeq₂] at heq
      dsimp only at heq
      subst heq
      have hidx : (⟨t₁.val + 1, hIpos_lt t₁ ht₁⟩ : Fin N) = ⟨t₂.val + 1, hIpos_lt t₂ ht₂⟩ :=
        hp.perm.injective (haeq₁.trans haeq₂.symm)
      have hval : t₁.val + 1 = t₂.val + 1 := congrArg Fin.val hidx
      exact Fin.ext (by omega)
  omega

/-- Unified `{K_{1,r+1}, K_{1,r+1}+e}`-freeness criterion:
If `|S| = r` and every nonzero shift `d ≠ 0` satisfies `|S ∩ (S + d)| ≥ 2`,
then `splitCirculant m S` is `{K_{1,r+1}, K_{1,r+1}+e}`-free. -/
lemma splitCirculant_starFree {m r : ℕ} [NeZero m] (S : Finset (ZMod m))
    (hS : S.card = r)
    (hinter : ∀ d : ZMod m, d ≠ 0 → 2 ≤ (S ∩ S.image (· + d)).card) :
    IsStarAndStarPlusEFree (splitCirculant m S) r := by
  intro c L hLcard hLadj
  cases c with
  | inr b =>
    -- Center in `I` has only `r` neighbors, contradicting `L.card = r + 1`
    exfalso
    have hsub : L ⊆ S.image (fun s => (Sum.inl (b - s) : ZMod m ⊕ ZMod m)) := by
      intro x hx
      have hadj := hLadj x hx
      cases x with
      | inr _ => simp [splitCirculant] at hadj
      | inl a =>
        simp only [splitCirculant] at hadj
        exact Finset.mem_image.mpr ⟨b - a, hadj, by simp⟩
    have hle := Finset.card_le_card hsub
    have himg : (S.image (fun s => (Sum.inl (b - s) : ZMod m ⊕ ZMod m))).card ≤ r := by
      rw [← hS]; exact Finset.card_image_le
    omega
  | inl a =>
    -- Partition `L` into clique leaves `LC` and independent leaves `LI`
    let LC : Finset (ZMod m) := (L.filter (fun x => x.isLeft)).image
      (fun x => match x with | Sum.inl u => u | Sum.inr _ => 0)
    let LI : Finset (ZMod m) := (L.filter (fun x => x.isRight)).image
      (fun x => match x with | Sum.inr u => u | Sum.inl _ => 0)
    have hLC_mem : ∀ u, u ∈ LC ↔ Sum.inl u ∈ L := by
      intro u; simp only [LC, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨hxL, hxl⟩, rfl⟩
        cases x with
        | inl u' => exact hxL
        | inr _ => simp at hxl
      · intro hu; exact ⟨Sum.inl u, ⟨hu, rfl⟩, rfl⟩
    have hLI_mem : ∀ u, u ∈ LI ↔ Sum.inr u ∈ L := by
      intro u; simp only [LI, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨hxL, hxr⟩, rfl⟩
        cases x with
        | inr u' => exact hxL
        | inl _ => simp at hxr
      · intro hu; exact ⟨Sum.inr u, ⟨hu, rfl⟩, rfl⟩
    have hcard_sum : LC.card + LI.card = r + 1 := by
      have h1 : (L.filter (fun x => x.isLeft)).card = LC.card := by
        symm
        refine Finset.card_bij (fun u _ => Sum.inl u) ?_ ?_ ?_
        · intro u hu; exact Finset.mem_filter.mpr ⟨(hLC_mem u).mp hu, rfl⟩
        · intro _ _ _ _ h; exact Sum.inl.inj h
        · intro x hx
          rcases Finset.mem_filter.mp hx with ⟨hxL, hxl⟩
          cases x with
          | inl u => exact ⟨u, (hLC_mem u).mpr hxL, rfl⟩
          | inr _ => simp at hxl
      have h2 : (L.filter (fun x => x.isRight)).card = LI.card := by
        symm
        refine Finset.card_bij (fun u _ => Sum.inr u) ?_ ?_ ?_
        · intro u hu; exact Finset.mem_filter.mpr ⟨(hLI_mem u).mp hu, rfl⟩
        · intro _ _ _ _ h; exact Sum.inr.inj h
        · intro x hx
          rcases Finset.mem_filter.mp hx with ⟨hxL, hxr⟩
          cases x with
          | inr u => exact ⟨u, (hLI_mem u).mpr hxL, rfl⟩
          | inl _ => simp at hxr
      have hpart : (L.filter (fun x => x.isLeft)).card + (L.filter (fun x => x.isRight)).card = L.card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext x; cases x <;> simp
        · rw [Finset.disjoint_left]; intro x hx1 hx2
          cases x <;> simp_all
      omega
    -- Every `b ∈ LI` has `b - a ∈ S`, so `LI ⊆ S.image (· + a)` and `LI.card ≤ r`
    let N_a : Finset (ZMod m) := S.image (· + a)
    have hNa_card : N_a.card = r := by
      rw [Finset.card_image_of_injective _ (add_left_injective a), hS]
    have hLI_sub : LI ⊆ N_a := by
      intro b hb
      have hadj := hLadj (Sum.inr b) ((hLI_mem b).mp hb)
      simp only [splitCirculant] at hadj
      exact Finset.mem_image.mpr ⟨b - a, hadj, sub_add_cancel b a⟩
    have hLI_le : LI.card ≤ r := by rw [← hNa_card]; exact Finset.card_le_card hLI_sub
    -- Helper: for any `c' ∈ LC`, `|(N_a ∩ {b | b - c' ∈ S})| ≥ 2`
    have hcommon : ∀ c' ∈ LC, 2 ≤ (N_a.filter (fun b => b - c' ∈ S)).card := by
      intro c' hc'
      have hne : c' ≠ a := by
        have hadj := hLadj (Sum.inl c') ((hLC_mem c').mp hc')
        exact Ne.symm hadj
      have hd : c' - a ≠ 0 := sub_ne_zero.mpr hne
      have h2 := hinter (c' - a) hd
      have heq_card : (S ∩ S.image (· + (c' - a))).card ≤ (N_a.filter (fun b => b - c' ∈ S)).card := by
        refine Finset.card_le_card_of_injOn (· + a) ?_ (fun _ _ _ _ h => add_right_cancel h)
        intro s hs
        rcases Finset.mem_inter.mp hs with ⟨hsS, hsImg⟩
        rcases Finset.mem_image.mp hsImg with ⟨t, htS, hteq⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨s, hsS, rfl⟩, ?_⟩
        have : s + a - c' = t := by rw [← hteq]; ring
        rw [this]; exact htS
      omega
    -- Case split on `LC.card`: 1, 2, or ≥ 3
    have hLC_pos : 1 ≤ LC.card := by omega
    rcases (by omega : LC.card = 1 ∨ LC.card = 2 ∨ 3 ≤ LC.card) with h1 | h2 | h3
    · -- Case `LC.card = 1`: `LI = N_a`, and the unique `c' ∈ LC` has ≥ 2 neighbors in `LI`
      have hLI_eq : LI = N_a :=
        Finset.eq_of_subset_of_card_le hLI_sub (by omega)
      obtain ⟨c', hc'⟩ := Finset.card_pos.mp (by omega : 0 < LC.card)
      have hcn := hcommon c' hc'
      obtain ⟨b₁, hb₁, b₂, hb₂, hbne⟩ := Finset.one_lt_card.mp (by omega : 1 < (N_a.filter (fun b => b - c' ∈ S)).card)
      rcases Finset.mem_filter.mp hb₁ with ⟨hb₁N, hb₁S⟩
      rcases Finset.mem_filter.mp hb₂ with ⟨hb₂N, hb₂S⟩
      refine ⟨s(Sum.inl c', Sum.inr b₁), s(Sum.inl c', Sum.inr b₂), ?_, ?_, ?_, ?_, ?_⟩
      · intro h
        rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hbne (Sum.inr.inj h2)
        · exact Sum.inl_ne_inr h1
      · exact hb₁S
      · exact hb₂S
      · intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact (hLC_mem c').mp hc'
        · exact (hLI_mem b₁).mp (hLI_eq ▸ hb₁N)
      · intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact (hLC_mem c').mp hc'
        · exact (hLI_mem b₂).mp (hLI_eq ▸ hb₂N)
    · -- Case `LC.card = 2`: `LI.card = r - 1`, so `N_a \ LI` has size 1;
      -- pick `c₁ ≠ c₂` in `LC` (edge 1) and a neighbor `b₁ ∈ LI` of `c₁` (edge 2)
      obtain ⟨c₁, hc₁, c₂, hc₂, hcne⟩ := Finset.one_lt_card.mp (by omega : 1 < LC.card)
      have hcn := hcommon c₁ hc₁
      have hdiff_card : (N_a \ LI).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hLI_sub, hNa_card]; omega
      have hnonempty : ((N_a.filter (fun b => b - c₁ ∈ S)) ∩ LI).Nonempty := by
        apply Finset.card_pos.mp
        have hsub : N_a.filter (fun b => b - c₁ ∈ S) ⊆
            ((N_a.filter (fun b => b - c₁ ∈ S)) ∩ LI) ∪ (N_a \ LI) := by
          intro b hb
          by_cases hbLI : b ∈ LI
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hb, hbLI⟩)
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hb).1, hbLI⟩)
        have := Finset.card_le_card hsub
        have := Finset.card_union_le ((N_a.filter (fun b => b - c₁ ∈ S)) ∩ LI) (N_a \ LI)
        omega
      rcases hnonempty with ⟨b₁, hb₁⟩
      rcases Finset.mem_inter.mp hb₁ with ⟨hb₁F, hb₁LI⟩
      have hb₁S : b₁ - c₁ ∈ S := (Finset.mem_filter.mp hb₁F).2
      refine ⟨s(Sum.inl c₁, Sum.inl c₂), s(Sum.inl c₁, Sum.inr b₁), ?_, ?_, ?_, ?_, ?_⟩
      · intro h
        rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Sum.inl_ne_inr h2
        · exact Sum.inl_ne_inr h1
      · exact hcne
      · exact hb₁S
      · intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact (hLC_mem c₁).mp hc₁
        · exact (hLC_mem c₂).mp hc₂
      · intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact (hLC_mem c₁).mp hc₁
        · exact (hLI_mem b₁).mp hb₁LI
    · -- Case `LC.card ≥ 3`: any 3 distinct clique vertices give ≥ 2 clique edges
      obtain ⟨c₁, hc₁, c₂, hc₂, hc12⟩ := Finset.one_lt_card.mp (by omega : 1 < LC.card)
      have hcard_er : 0 < ((LC.erase c₁).erase c₂).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hc12.symm, hc₂⟩),
            Finset.card_erase_of_mem hc₁]
        omega
      obtain ⟨c₃, hc₃'⟩ := Finset.card_pos.mp hcard_er
      have hc32 : c₃ ≠ c₂ := (Finset.mem_erase.mp hc₃').1
      have hc₃'' := (Finset.mem_erase.mp hc₃').2
      have hc31 : c₃ ≠ c₁ := (Finset.mem_erase.mp hc₃'').1
      have hc₃ : c₃ ∈ LC := (Finset.mem_erase.mp hc₃'').2
      refine ⟨s(Sum.inl c₁, Sum.inl c₂), s(Sum.inl c₁, Sum.inl c₃), ?_, ?_, ?_, ?_, ?_⟩
      · intro h
        rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hc32 (Sum.inl.inj h2).symm
        · exact hc31 (Sum.inl.inj h1).symm
      · exact hc12
      · exact hc31.symm
      · intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact (hLC_mem c₁).mp hc₁
        · exact (hLC_mem c₂).mp hc₂
      · intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact (hLC_mem c₁).mp hc₁
        · exact (hLC_mem c₃).mp hc₃

/-- The Paley `(11, 5, 2)` difference set `{1, 3, 4, 5, 9} ⊆ ZMod 11`. -/
def paley11Set : Finset (ZMod 11) := {1, 3, 4, 5, 9}

/-- The Paley 22-vertex counterexample at `r = 5`. -/
def paley22Graph : SimpleGraph (ZMod 11 ⊕ ZMod 11) := splitCirculant 11 paley11Set

theorem paley22_counterexample :
    Fintype.card (ZMod 11 ⊕ ZMod 11) ≥ 2 * 5 + 7 ∧
    IsSplitGraph paley22Graph ∧
    IsRConnected paley22Graph 5 ∧
    IsStarAndStarPlusEFree paley22Graph 5 ∧
    ¬ IsHamiltonConnected paley22Graph := by
  have hcard : paley11Set.card = 5 := by decide
  have hinter : ∀ d : ZMod 11, d ≠ 0 → 2 ≤ (paley11Set ∩ paley11Set.image (· + d)).card := by
    decide
  refine ⟨by simp [Fintype.card_sum, ZMod.card],
    splitCirculant_isSplit 11 paley11Set,
    splitCirculant_rConnected paley11Set hcard (by omega),
    splitCirculant_starFree paley11Set hcard hinter,
    splitCirculant_not_hamiltonConnected paley11Set (by omega)⟩

/-- The interval connection set `{0, 1, ..., r - 1} ⊆ ZMod (r + 4)` for `r ≥ 6`. -/
def intervalSet (r : ℕ) : Finset (ZMod (r + 4)) :=
  (Finset.range r).image (fun k : ℕ => (k : ZMod (r + 4)))

/-- The `(2r + 8)`-vertex circulant split graph for `r ≥ 6`. -/
def circulantSplitGraph (r : ℕ) : SimpleGraph (ZMod (r + 4) ⊕ ZMod (r + 4)) :=
  splitCirculant (r + 4) (intervalSet r)

private lemma intervalSet_card (r : ℕ) : (intervalSet r).card = r := by
  unfold intervalSet
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range r
  · intro a ha b hb heq
    have ha' : a < r + 4 := by have := Finset.mem_range.mp ha; omega
    have hb' : b < r + 4 := by have := Finset.mem_range.mp hb; omega
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at hval
    exact hval

private lemma intervalSet_inter_ge_two {r : ℕ} (hr : 6 ≤ r) (d : ZMod (r + 4)) :
    2 ≤ (intervalSet r ∩ (intervalSet r).image (· + d)).card := by
  have h1 : (intervalSet r).card = r := intervalSet_card r
  have h2 : ((intervalSet r).image (· + d)).card = r := by
    rw [Finset.card_image_of_injective _ (add_left_injective d), h1]
  have hunion : (intervalSet r ∪ (intervalSet r).image (· + d)).card ≤ r + 4 := by
    have := Finset.card_le_univ (intervalSet r ∪ (intervalSet r).image (· + d))
    simpa [ZMod.card] using this
  have hinc := Finset.card_union_add_card_inter (intervalSet r) ((intervalSet r).image (· + d))
  omega

/-- For every `r ≥ 6`, `circulantSplitGraph r` is a `(2r + 8)`-vertex counterexample to
Conjecture 1.14 of Zai–Lv–Sabir (`arXiv:2611.32794v1`). -/
theorem circulant_counterexample_all_ge_6 {r : ℕ} (hr : 6 ≤ r) :
    Fintype.card (ZMod (r + 4) ⊕ ZMod (r + 4)) ≥ 2 * r + 7 ∧
    IsSplitGraph (circulantSplitGraph r) ∧
    IsRConnected (circulantSplitGraph r) r ∧
    IsStarAndStarPlusEFree (circulantSplitGraph r) r ∧
    ¬ IsHamiltonConnected (circulantSplitGraph r) := by
  have hcard := intervalSet_card r
  refine ⟨by simp [Fintype.card_sum, ZMod.card]; omega,
    splitCirculant_isSplit (r + 4) (intervalSet r),
    splitCirculant_rConnected (intervalSet r) hcard (by omega),
    splitCirculant_starFree (intervalSet r) hcard (fun d _ => intervalSet_inter_ge_two hr d),
    splitCirculant_not_hamiltonConnected (intervalSet r) (by omega)⟩

/-- **Complete disproof of Conjecture 1.14 of Zai–Lv–Sabir (`arXiv:2611.32794v1`) for every `r ≥ 5`**:
for every integer `r ≥ 5`, there exists a finite `r`-connected `{K_{1,r+1}, K_{1,r+1}+e}`-free
split graph on at least `2r + 7` vertices that is not Hamilton-connected. -/
theorem zai_lv_sabir_conjecture_1_14_false_all_ge_5 {r : ℕ} (hr : 5 ≤ r) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      n ≥ 2 * r + 7 ∧
      IsSplitGraph G ∧
      IsRConnected G r ∧
      IsStarAndStarPlusEFree G r ∧
      ¬ IsHamiltonConnected G := by
  -- Transport `SimpleGraph V` along `e : V ≃ Fin n`
  have transport : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V ≥ 2 * r + 7 →
      IsSplitGraph G →
      IsRConnected G r →
      IsStarAndStarPlusEFree G r →
      ¬ IsHamiltonConnected G →
      ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
        n ≥ 2 * r + 7 ∧
        IsSplitGraph H ∧
        IsRConnected H r ∧
        IsStarAndStarPlusEFree H r ∧
        ¬ IsHamiltonConnected H := by
    intro V _ _ G hord hsplit hconn hfree hnhc
    let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    let H : SimpleGraph (Fin (Fintype.card V)) := G.comap e.symm
    have hadj_iff : ∀ x y : Fin (Fintype.card V), H.Adj x y ↔ G.Adj (e.symm x) (e.symm y) :=
      fun _ _ => Iff.rfl
    let hom : G →g H :=
      { toFun := e
        map_rel' := fun {a b} hab => by
          show G.Adj (e.symm (e a)) (e.symm (e b))
          simpa using hab }
    refine ⟨Fintype.card V, H, hord, ?_, ?_, ?_, ?_⟩
    · rcases hsplit with ⟨C, hC, hI⟩
      refine ⟨e.symm ⁻¹' C, ?_, ?_⟩
      · intro u hu v hv hne
        exact (hadj_iff u v).mpr (hC _ hu _ hv (fun h => hne (e.symm.injective h)))
      · intro u hu v hv h
        exact hI _ hu _ hv ((hadj_iff u v).mp h)
    · refine ⟨by simpa using hconn.1, ?_⟩
      intro D hD u v hu hv
      let D' : Finset V := D.map e.symm.toEmbedding
      have hD' : D'.card < r := by simpa [D'] using hD
      have hu' : e.symm u ∉ D' := by simpa [D'] using hu
      have hv' : e.symm v ∉ D' := by simpa [D'] using hv
      rcases hconn.2 D' hD' (e.symm u) (e.symm v) hu' hv' with ⟨p, hp⟩
      refine ⟨(p.map hom).copy (e.apply_symm_apply u) (e.apply_symm_apply v), ?_⟩
      intro w hw
      rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hw
      rcases hw with ⟨z, hz, rfl⟩
      intro hmem
      have : z ∈ D' := Finset.mem_map.mpr ⟨hom z, hmem, by simp [hom]⟩
      exact hp z hz this
    · intro c L hLcard hLadj
      let L' : Finset V := L.map e.symm.toEmbedding
      have hL'card : L'.card = r + 1 := by simpa [L'] using hLcard
      have hL'adj : ∀ x ∈ L', G.Adj (e.symm c) x := by
        intro x hx
        rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact (hadj_iff c y).mp (hLadj y hy)
      rcases hfree (e.symm c) L' hL'card hL'adj with ⟨e₁, e₂, hne, he1, he2, h1L, h2L⟩
      refine ⟨e₁.map e, e₂.map e, ?_, ?_, ?_, ?_, ?_⟩
      · intro heq
        exact hne (Sym2.map.injective e.injective heq)
      · induction e₁ using Sym2.ind with
        | _ a b =>
          simp only [Sym2.map_mk, SimpleGraph.mem_edgeSet] at he1 ⊢
          exact (hadj_iff (e a) (e b)).mpr (by simpa using he1)
      · induction e₂ using Sym2.ind with
        | _ a b =>
          simp only [Sym2.map_mk, SimpleGraph.mem_edgeSet] at he2 ⊢
          exact (hadj_iff (e a) (e b)).mpr (by simpa using he2)
      · intro x hx
        rcases Sym2.mem_map.mp hx with ⟨y, hy, rfl⟩
        have hyL' := h1L y hy
        rcases Finset.mem_map.mp hyL' with ⟨z, hz, hzy⟩
        rw [← hzy]; simpa using hz
      · intro x hx
        rcases Sym2.mem_map.mp hx with ⟨y, hy, rfl⟩
        have hyL' := h2L y hy
        rcases Finset.mem_map.mp hyL' with ⟨z, hz, hzy⟩
        rw [← hzy]; simpa using hz
    · intro hHC
      apply hnhc
      intro u v huv
      rcases hHC (e u) (e v) (fun h => huv (e.injective h)) with ⟨hp⟩
      have hcardEq : Fintype.card (Fin (Fintype.card V)) = Fintype.card V := Fintype.card_fin _
      let castFin : Fin (Fintype.card V) ≃ Fin (Fintype.card (Fin (Fintype.card V))) :=
        finCongr hcardEq.symm
      refine ⟨{
        hn := by simpa [hcardEq] using hp.hn
        perm := castFin.trans (hp.perm.trans e.symm)
        start_eq := by
          have h0 : castFin ⟨0, by simpa [hcardEq] using hp.hn⟩ = ⟨0, hp.hn⟩ := Fin.ext rfl
          simp only [Equiv.trans_apply, h0, hp.start_eq, Equiv.symm_apply_apply]
        end_eq := by
          have h1 : castFin ⟨Fintype.card V - 1, Nat.sub_lt (by simpa [hcardEq] using hp.hn) Nat.one_pos⟩ =
              ⟨Fintype.card (Fin (Fintype.card V)) - 1, Nat.sub_lt hp.hn Nat.one_pos⟩ :=
            Fin.ext (by simp [castFin, hcardEq])
          simp only [Equiv.trans_apply, h1, hp.end_eq, Equiv.symm_apply_apply]
        adj_step := fun i hi => by
          have hi' : i + 1 < Fintype.card (Fin (Fintype.card V)) := by simpa [hcardEq] using hi
          have hstep := hp.adj_step i hi'
          have h1 : castFin ⟨i, Nat.lt_of_succ_lt hi⟩ = ⟨i, Nat.lt_of_succ_lt hi'⟩ := Fin.ext rfl
          have h2 : castFin ⟨i + 1, hi⟩ = ⟨i + 1, hi'⟩ := Fin.ext rfl
          simp only [Equiv.trans_apply, h1, h2]
          exact (hadj_iff _ _).mp hstep
      }⟩
  rcases (by omega : r = 5 ∨ 6 ≤ r) with rfl | hr6
  · rcases paley22_counterexample with ⟨h1, h2, h3, h4, h5⟩
    exact transport paley22Graph h1 h2 h3 h4 h5
  · rcases circulant_counterexample_all_ge_6 hr6 with ⟨h1, h2, h3, h4, h5⟩
    exact transport (circulantSplitGraph r) h1 h2 h3 h4 h5

end ZaiLvSabirSplitHamilton
