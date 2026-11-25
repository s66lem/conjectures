import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A weighted bond poset counterexample to González D'León and Wachs, Conjecture 4.13(2). -/

namespace WachsWeightedBond

open Finset Polynomial SimpleGraph

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- A block and its weight. The bounds and partition conditions are imposed in `WPi`. -/
abbrev WeightedBlock (V : Type*) := Finset V × ℕ

/-- A partition into connected induced subgraphs, with each block weighted from zero
through one less than its cardinality. -/
@[ext] structure WPi (G : SimpleGraph V) where
  blocks : Finset (WeightedBlock V)
  connected : ∀ b ∈ blocks, (G.induce (b.1 : Set V)).Connected
  weight_lt : ∀ b ∈ blocks, b.2 < b.1.card
  cover : ∀ v : V, ∃ b ∈ blocks, v ∈ b.1
  agree : ∀ a ∈ blocks, ∀ b ∈ blocks, ∀ v ∈ a.1, v ∈ b.1 → a = b

namespace WPi

variable {J : SimpleGraph V}

instance : DecidableEq (WPi J) := fun a b =>
  decidable_of_iff (a.blocks = b.blocks) ⟨fun h => WPi.ext h, congrArg WPi.blocks⟩

omit [DecidableEq V] in
private theorem nonempty_block {a : WPi J} {b : WeightedBlock V} (hb : b ∈ a.blocks) :
    b.1.Nonempty := card_pos.mp ((Nat.zero_le _).trans_lt (a.weight_lt _ hb))

/-- The blocks of a finer partition contained in the given vertex set. -/
private def rawUnder (a : Finset (WeightedBlock V)) (B : Finset V) :
    Finset (WeightedBlock V) := a.filter fun A => A.1 ⊆ B

def under (a : WPi J) (B : Finset V) : Finset (WeightedBlock V) := rawUnder a.blocks B

/-- Sum of the block weights. -/
def weight (a : WPi J) : ℕ := ∑ A ∈ a.blocks, A.2

/-- The order requires refinement. In each coarse block, the weight increment is between
zero and one less than the number of finer blocks it contains. The two inequalities
express this without truncated subtraction. -/
private def refinesWith (a b : Finset (WeightedBlock V))
    (underA : Finset V → Finset (WeightedBlock V)) : Prop :=
  (∀ A ∈ a, ∃ B ∈ b, A.1 ⊆ B.1) ∧
  ∀ B ∈ b,
    (∑ A ∈ underA B.1, A.2) ≤ B.2 ∧
      B.2 < (∑ A ∈ underA B.1, A.2) + (underA B.1).card

private abbrev rawRefines (a b : Finset (WeightedBlock V)) : Prop :=
  refinesWith a b (rawUnder a)

instance (a b : Finset (WeightedBlock V)) : Decidable (rawRefines a b) := by
  unfold rawRefines refinesWith
  infer_instance

def Refines (a b : WPi J) : Prop := refinesWith a.blocks b.blocks a.under

instance : LE (WPi J) := ⟨Refines⟩

instance : DecidableLE (WPi J) := fun a b => by
  change Decidable (rawRefines a.blocks b.blocks)
  infer_instance

private theorem under_self (a : WPi J) {B : WeightedBlock V} (hB : B ∈ a.blocks) :
    a.under B.1 = {B} := by
  ext A
  simp only [under, rawUnder, mem_filter, mem_singleton]
  constructor
  · rintro ⟨hA, hs⟩
    obtain ⟨v, hv⟩ := nonempty_block hA
    exact a.agree A hA B hB v hv (hs hv)
  · rintro rfl
    exact ⟨hB, Subset.rfl⟩

private theorem under_comp {a b c : WPi J} (hab : a ≤ b) (hbc : b ≤ c)
    {C : WeightedBlock V} (hC : C ∈ c.blocks) :
    a.under C.1 = (b.under C.1).biUnion (fun B => a.under B.1) := by
  ext A
  simp only [under, rawUnder, mem_filter, mem_biUnion]
  constructor
  · rintro ⟨hA, hAC⟩
    obtain ⟨B, hB, hAB⟩ := hab.1 A hA
    obtain ⟨D, hD, hBD⟩ := hbc.1 B hB
    obtain ⟨v, hv⟩ := nonempty_block hA
    have he := c.agree D hD C hC v (hBD (hAB hv)) (hAC hv)
    exact ⟨B, ⟨hB, he ▸ hBD⟩, hA, hAB⟩
  · rintro ⟨B, ⟨_, hBC⟩, hA, hAB⟩
    exact ⟨hA, hAB.trans hBC⟩

private theorem under_disjoint (a b : WPi J) (C : Finset V) :
    (↑(b.under C) : Set (WeightedBlock V)).PairwiseDisjoint (fun B => a.under B.1) := by
  intro B hB D hD hne
  refine disjoint_left.mpr fun A hAB hAD => hne ?_
  obtain ⟨hA, hAB⟩ := mem_filter.mp hAB
  obtain ⟨_, hAD⟩ := mem_filter.mp hAD
  obtain ⟨v, hv⟩ := nonempty_block hA
  exact b.agree B (mem_filter.mp hB).1 D (mem_filter.mp hD).1 v (hAB hv) (hAD hv)

private theorem weights_eq_of_mutual {a b : WPi J} (hab : a ≤ b) (hba : b ≤ a) :
    a.blocks ⊆ b.blocks := by
  intro A hA
  obtain ⟨B, hB, hAB⟩ := hab.1 A hA
  obtain ⟨D, hD, hBD⟩ := hba.1 B hB
  obtain ⟨v, hv⟩ := nonempty_block hA
  have hDA := a.agree D hD A hA v (hBD (hAB hv)) hv
  have hs : A.1 = B.1 := Subset.antisymm hAB (hDA ▸ hBD)
  have h₁ := (hab.2 B hB).1
  have h₂ := (hba.2 A hA).1
  rw [← hs, under_self a hA, sum_singleton] at h₁
  rw [hs, under_self b hB, sum_singleton] at h₂
  have he : A = B := Prod.ext hs (Nat.le_antisymm h₁ h₂)
  exact he ▸ hB

instance : PartialOrder (WPi J) where
  le_refl a := by
    exact ⟨fun A hA => ⟨A, hA, Subset.rfl⟩, fun B hB => by
      rw [under_self a hB, sum_singleton, card_singleton]
      exact ⟨le_rfl, Nat.lt_succ_self _⟩⟩
  le_trans a b c hab hbc := by
    refine ⟨?_, ?_⟩
    · intro A hA
      obtain ⟨B, hB, hAB⟩ := hab.1 A hA
      obtain ⟨C, hC, hBC⟩ := hbc.1 B hB
      exact ⟨C, hC, hAB.trans hBC⟩
    · intro C hC
      have hd := under_disjoint a b C.1
      have hl : (∑ B ∈ b.under C.1, ∑ A ∈ a.under B.1, A.2) ≤
          ∑ B ∈ b.under C.1, B.2 :=
        sum_le_sum fun B hB => (hab.2 B (mem_filter.mp hB).1).1
      have hu : (∑ B ∈ b.under C.1, (B.2 + 1)) ≤
          ∑ B ∈ b.under C.1, ((∑ A ∈ a.under B.1, A.2) + (a.under B.1).card) :=
        sum_le_sum fun B hB => (hab.2 B (mem_filter.mp hB).1).2
      rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul, mul_one] at hu
      rw [under_comp hab hbc hC, sum_biUnion hd, card_biUnion hd]
      have ht := hbc.2 C hC
      omega
  le_antisymm _ _ hab hba := WPi.ext <| Subset.antisymm
    (weights_eq_of_mutual hab hba) (weights_eq_of_mutual hba hab)

variable [Fintype V]

private def singletonBlock : V ↪ WeightedBlock V where
  toFun v := ({v}, 0)
  inj' := by intro a b h; simpa using congrArg Prod.fst h

omit [DecidableEq V] [Fintype V] in
@[simp] private theorem singletonBlock_fst (v : V) : (singletonBlock v).1 = {v} := rfl
omit [DecidableEq V] [Fintype V] in
@[simp] private theorem singletonBlock_snd (v : V) : (singletonBlock v).2 = 0 := rfl

omit [DecidableEq V] [Fintype V] in
private theorem singleton_connected (J : SimpleGraph V) (v : V) :
    (J.induce ({v} : Finset V)).Connected := by
  apply (connected_iff _).mpr
  refine ⟨?_, ⟨⟨v, by simp⟩⟩⟩
  intro a b
  have ea : a.val = v := by simpa using a.property
  have eb : b.val = v := by simpa using b.property
  rw [Subtype.ext (ea.trans eb.symm)]

instance : Bot (WPi J) where
  bot :=
    { blocks := univ.map singletonBlock
      connected := by
        intro b hb
        obtain ⟨v, _, rfl⟩ := mem_map.mp hb
        exact singleton_connected J v
      weight_lt := by
        intro b hb
        obtain ⟨v, _, rfl⟩ := mem_map.mp hb
        simp
      cover := fun v => ⟨singletonBlock v, mem_map.mpr ⟨v, mem_univ _, rfl⟩, by
        simp⟩
      agree := by
        intro a ha b hb v hva hvb
        obtain ⟨x, _, rfl⟩ := mem_map.mp ha
        obtain ⟨y, _, rfl⟩ := mem_map.mp hb
        simp only [singletonBlock_fst, mem_singleton] at hva hvb
        rw [← hva, ← hvb] }

omit [DecidableEq V] in
@[simp] theorem bot_blocks : (⊥ : WPi J).blocks = univ.map singletonBlock := rfl

private theorem bot_under (B : Finset V) : (⊥ : WPi J).under B = B.map singletonBlock := by
  ext A
  simp only [under, rawUnder, bot_blocks, mem_filter, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨⟨v, rfl⟩, hv⟩
    exact ⟨v, hv (by simp), rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, by simpa⟩

instance : OrderBot (WPi J) where
  bot_le a := by
    refine ⟨?_, ?_⟩
    · intro A hA
      obtain ⟨v, _, rfl⟩ := mem_map.mp hA
      obtain ⟨B, hB, hv⟩ := a.cover v
      exact ⟨B, hB, by simpa⟩
    · intro B hB
      rw [bot_under, sum_map, card_map]
      simpa using a.weight_lt B hB

private def boundedEncode (b : WeightedBlock V) : Finset V × Fin (Fintype.card V + 1) :=
  (b.1, ⟨b.2 % (Fintype.card V + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩)

instance : Finite (WPi J) := by
  apply Finite.of_injective (fun a : WPi J => a.blocks.image boundedEncode)
  intro a b hab
  apply WPi.ext
  ext B
  have hbnd (p : WPi J) (D : WeightedBlock V) (hD : D ∈ p.blocks) :
      D.2 < Fintype.card V + 1 :=
    (p.weight_lt D hD).trans ((card_le_univ D.1).trans_lt (Nat.lt_succ_self _))
  have transfer (x y : WPi J) (h : x.blocks.image boundedEncode =
      y.blocks.image boundedEncode) (hx : B ∈ x.blocks) : B ∈ y.blocks := by
    have hm := mem_image_of_mem boundedEncode hx
    rw [h] at hm
    obtain ⟨C, hC, he⟩ := mem_image.mp hm
    have hv := congrArg (fun q : Finset V × Fin (Fintype.card V + 1) => q.2.val) he
    change C.2 % _ = B.2 % _ at hv
    rw [Nat.mod_eq_of_lt (hbnd y C hC), Nat.mod_eq_of_lt (hbnd x B hx)] at hv
    have hs : C.1 = B.1 := congrArg (fun q : Finset V × Fin (Fintype.card V + 1) => q.1) he
    exact (Prod.ext hs hv : C = B) ▸ hC
  exact ⟨transfer a b hab, transfer b a hab.symm⟩

noncomputable instance : Fintype (WPi J) := Fintype.ofFinite _

noncomputable instance : LocallyFiniteOrder (WPi J) :=
  LocallyFiniteOrder.ofFiniteIcc fun _ _ => Set.toFinite _

end WPi

/-- Sum over the maximal weighted bond partitions, with exponent the total weight. -/
noncomputable def μ [Fintype V] (J : SimpleGraph V) : Polynomial ℤ := by
  classical
  exact ∑ a ∈ (univ : Finset (WPi J)).filter IsMax,
    monomial a.weight (IncidenceAlgebra.mu ℤ (⊥ : WPi J) a)

namespace WPi

variable {J : SimpleGraph V} {K : SimpleGraph W}
variable {U : Type*} [DecidableEq U] {L : SimpleGraph U}

private def blockMap (e : V ↪ U) : WeightedBlock V ↪ WeightedBlock U where
  toFun B := (B.1.map e, B.2)
  inj' := by
    intro A B h
    exact Prod.ext (Finset.map_injective e (congrArg Prod.fst h))
      (congrArg (fun q : WeightedBlock U => q.2) h)

omit [DecidableEq V] [DecidableEq U] in
@[simp] private theorem blockMap_fst (e : V ↪ U) (B : WeightedBlock V) :
    (blockMap e B).1 = B.1.map e := rfl

omit [DecidableEq V] [DecidableEq U] in
@[simp] private theorem blockMap_snd (e : V ↪ U) (B : WeightedBlock V) :
    (blockMap e B).2 = B.2 := rfl

private noncomputable def induceMapIso (e : J ↪g L) (s : Finset V) :
    J.induce (s : Set V) ≃g L.induce (s.map e.toEmbedding : Set U) where
  toEquiv := Equiv.ofBijective (fun v => ⟨e v.1, mem_map_of_mem _ v.2⟩)
    ⟨fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h)), by
      rintro ⟨u, hu⟩
      obtain ⟨v, hv, rfl⟩ := mem_map.mp hu
      exact ⟨⟨v, hv⟩, rfl⟩⟩
  map_rel_iff' := e.map_rel_iff

private abbrev leftBlock : WeightedBlock V ↪ WeightedBlock (V ⊕ W) :=
  blockMap Function.Embedding.inl

private abbrev rightBlock : WeightedBlock W ↪ WeightedBlock (V ⊕ W) :=
  blockMap Function.Embedding.inr

omit [DecidableEq V] [DecidableEq W] in
private theorem not_subset_cross {A : WeightedBlock V} {B : WeightedBlock W}
    (hA : A.1.Nonempty) : ¬ (leftBlock A).1 ⊆ (rightBlock B).1 := by
  obtain ⟨v, hv⟩ := hA
  intro h
  have hh := h (mem_map_of_mem Function.Embedding.inl hv)
  simp at hh

omit [DecidableEq V] [DecidableEq W] in
private theorem not_subset_cross' {A : WeightedBlock V} {B : WeightedBlock W}
    (hB : B.1.Nonempty) : ¬ (rightBlock B).1 ⊆ (leftBlock A).1 := by
  obtain ⟨v, hv⟩ := hB
  intro h
  have hh := h (mem_map_of_mem Function.Embedding.inr hv)
  simp at hh

private def join (a : WPi J) (b : WPi K) : WPi (J.sum K) where
  blocks := a.blocks.map leftBlock ∪ b.blocks.map rightBlock
  connected := by
    intro B hB
    rcases mem_union.mp hB with h | h
    · obtain ⟨A, hA, rfl⟩ := mem_map.mp h
      exact (induceMapIso (Embedding.sumInl (G := J) (H := K)) A.1).connected_iff.mp
        (a.connected A hA)
    · obtain ⟨A, hA, rfl⟩ := mem_map.mp h
      exact (induceMapIso (Embedding.sumInr (G := J) (H := K)) A.1).connected_iff.mp
        (b.connected A hA)
  weight_lt := by
    intro B hB
    rcases mem_union.mp hB with h | h
    · obtain ⟨A, hA, rfl⟩ := mem_map.mp h
      simpa using a.weight_lt A hA
    · obtain ⟨A, hA, rfl⟩ := mem_map.mp h
      simpa using b.weight_lt A hA
  cover := by
    rintro (v | v)
    · obtain ⟨A, hA, hv⟩ := a.cover v
      exact ⟨leftBlock A, mem_union_left _ (mem_map_of_mem _ hA), by simpa⟩
    · obtain ⟨A, hA, hv⟩ := b.cover v
      exact ⟨rightBlock A, mem_union_right _ (mem_map_of_mem _ hA), by simpa⟩
  agree := by
    intro A hA B hB v hvA hvB
    rcases mem_union.mp hA with h | h <;> obtain ⟨C, hC, rfl⟩ := mem_map.mp h <;>
      rcases mem_union.mp hB with h | h <;> obtain ⟨D, hD, rfl⟩ := mem_map.mp h <;>
      cases v <;> simp at hvA hvB
    · exact congrArg leftBlock (a.agree C hC D hD _ hvA hvB)
    · exact congrArg rightBlock (b.agree C hC D hD _ hvA hvB)

private theorem join_under_left (a : WPi J) (b : WPi K) (C : WeightedBlock V) :
    (join a b).under (leftBlock C).1 = (a.under C.1).map leftBlock := by
  ext A
  simp only [under, rawUnder, mem_filter, join, mem_union, mem_map]
  constructor
  · rintro ⟨h, hs⟩
    rcases h with ⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩
    · exact ⟨B, ⟨hB, by simpa using hs⟩, rfl⟩
    · exact (not_subset_cross' (nonempty_block hB) hs).elim
  · rintro ⟨B, ⟨hB, hs⟩, rfl⟩
    exact ⟨Or.inl ⟨B, hB, rfl⟩, by simpa using hs⟩

private theorem join_under_right (a : WPi J) (b : WPi K) (C : WeightedBlock W) :
    (join a b).under (rightBlock C).1 = (b.under C.1).map rightBlock := by
  ext A
  simp only [under, rawUnder, mem_filter, join, mem_union, mem_map]
  constructor
  · rintro ⟨h, hs⟩
    rcases h with ⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩
    · exact (not_subset_cross (nonempty_block hB) hs).elim
    · exact ⟨B, ⟨hB, by simpa using hs⟩, rfl⟩
  · rintro ⟨B, ⟨hB, hs⟩, rfl⟩
    exact ⟨Or.inr ⟨B, hB, rfl⟩, by simpa using hs⟩

private theorem join_le {a c : WPi J} {b d : WPi K} :
    join a b ≤ join c d ↔ a ≤ c ∧ b ≤ d := by
  change Refines (join a b) (join c d) ↔ Refines a c ∧ Refines b d
  unfold Refines refinesWith
  constructor
  · rintro ⟨href, hw⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro A hA
      obtain ⟨B, hB, hs⟩ := href (leftBlock A) (mem_union_left _ (mem_map_of_mem _ hA))
      rcases mem_union.mp hB with h | h <;> obtain ⟨C, hC, rfl⟩ := mem_map.mp h
      · exact ⟨C, hC, by simpa using hs⟩
      · exact (not_subset_cross (nonempty_block hA) hs).elim
    · intro C hC
      simpa only [join_under_left, sum_map, card_map, blockMap_snd] using
        hw (leftBlock C) (mem_union_left _ (mem_map_of_mem _ hC))
    · intro A hA
      obtain ⟨B, hB, hs⟩ := href (rightBlock A) (mem_union_right _ (mem_map_of_mem _ hA))
      rcases mem_union.mp hB with h | h <;> obtain ⟨C, hC, rfl⟩ := mem_map.mp h
      · exact (not_subset_cross' (nonempty_block hA) hs).elim
      · exact ⟨C, hC, by simpa using hs⟩
    · intro C hC
      simpa only [join_under_right, sum_map, card_map, blockMap_snd] using
        hw (rightBlock C) (mem_union_right _ (mem_map_of_mem _ hC))
  · rintro ⟨⟨ha, hwa⟩, ⟨hb, hwb⟩⟩
    constructor
    · intro A hA
      rcases mem_union.mp hA with h | h <;> obtain ⟨B, hB, rfl⟩ := mem_map.mp h
      · obtain ⟨C, hC, hs⟩ := ha B hB
        exact ⟨leftBlock C, mem_union_left _ (mem_map_of_mem _ hC), by simpa⟩
      · obtain ⟨C, hC, hs⟩ := hb B hB
        exact ⟨rightBlock C, mem_union_right _ (mem_map_of_mem _ hC), by simpa⟩
    · intro A hA
      rcases mem_union.mp hA with h | h <;> obtain ⟨B, hB, rfl⟩ := mem_map.mp h
      · simpa only [join_under_left, sum_map, card_map, blockMap_snd] using hwa B hB
      · simpa only [join_under_right, sum_map, card_map, blockMap_snd] using hwb B hB

omit [DecidableEq V] [DecidableEq W] in
private theorem block_one_side (p : WPi (J.sum K)) {B : WeightedBlock (V ⊕ W)}
    (hB : B ∈ p.blocks) : (∃ A, leftBlock A = B) ∨ (∃ A, rightBlock A = B) := by
  have no_cross (v : V) (w : W) (hv : Sum.inl v ∈ B.1) (hw : Sum.inr w ∈ B.1) : False :=
    not_reachable_sum_inl_inr v w
      (((p.connected B hB).preconnected ⟨_, hv⟩ ⟨_, hw⟩).map
        (Embedding.induce (B.1 : Set (V ⊕ W))).toHom)
  obtain ⟨v | w, hv⟩ := nonempty_block hB
  · left
    refine ⟨(B.1.toLeft, B.2), Prod.ext ?_ rfl⟩
    ext (x | y)
    · simp
    · simp [show Sum.inr y ∉ B.1 from fun hy => no_cross v y hv hy]
  · right
    refine ⟨(B.1.toRight, B.2), Prod.ext ?_ rfl⟩
    ext (x | y)
    · simp [show Sum.inl x ∉ B.1 from fun hx => no_cross x w hx hv]
    · simp

variable [Fintype V] [Fintype W]

private def pull (e : J ↪g (J.sum K)) (p : WPi (J.sum K)) : Finset (WeightedBlock V) :=
  ((univ : Finset (Finset V)).biUnion fun s => ({s} : Finset (Finset V)) ×ˢ range s.card).filter
    fun B => blockMap e.toEmbedding B ∈ p.blocks

omit [Fintype W] in
private theorem mem_pull (e : J ↪g (J.sum K)) (p : WPi (J.sum K)) (A : WeightedBlock V) :
    A ∈ pull e p ↔ blockMap e.toEmbedding A ∈ p.blocks := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    apply mem_filter.mpr
    refine ⟨mem_biUnion.mpr ⟨A.1, mem_univ _, ?_⟩, h⟩
    simpa using p.weight_lt _ h

private def pullLeft (p : WPi (J.sum K)) : WPi J where
  blocks := pull Embedding.sumInl p
  connected := by
    intro A hA
    exact (induceMapIso Embedding.sumInl A.1).connected_iff.mpr
      (p.connected _ ((mem_pull _ _ _).mp hA))
  weight_lt := by
    intro A hA
    simpa using p.weight_lt _ ((mem_pull _ _ _).mp hA)
  cover := by
    intro v
    obtain ⟨B, hB, hv⟩ := p.cover (.inl v)
    rcases block_one_side p hB with ⟨A, rfl⟩ | ⟨A, rfl⟩
    · exact ⟨A, (mem_pull _ _ _).mpr hB, by simpa using hv⟩
    · simp at hv
  agree := by
    intro A hA B hB v hvA hvB
    apply leftBlock.injective
    exact p.agree _ ((mem_pull _ _ _).mp hA) _ ((mem_pull _ _ _).mp hB)
      (.inl v) (by simpa) (by simpa)

private def pullRight (p : WPi (J.sum K)) : WPi K where
  blocks :=
    ((univ : Finset (Finset W)).biUnion fun s => ({s} : Finset (Finset W)) ×ˢ range s.card).filter
      fun B => rightBlock B ∈ p.blocks
  connected := by
    intro A hA
    exact (induceMapIso Embedding.sumInr A.1).connected_iff.mpr (p.connected _ (mem_filter.mp hA).2)
  weight_lt := by
    intro A hA
    simpa using p.weight_lt _ (mem_filter.mp hA).2
  cover := by
    intro v
    obtain ⟨B, hB, hv⟩ := p.cover (.inr v)
    rcases block_one_side p hB with ⟨A, rfl⟩ | ⟨A, rfl⟩
    · simp at hv
    · exact ⟨A, mem_filter.mpr ⟨mem_biUnion.mpr ⟨A.1, mem_univ _, by
          simpa using p.weight_lt _ hB⟩, hB⟩, by simpa using hv⟩
  agree := by
    intro A hA B hB v hvA hvB
    apply rightBlock.injective
    exact p.agree _ (mem_filter.mp hA).2 _ (mem_filter.mp hB).2
      (.inr v) (by simpa) (by simpa)

private theorem join_pull (p : WPi (J.sum K)) : join (pullLeft p) (pullRight p) = p := by
  apply WPi.ext
  ext B
  change B ∈ (pullLeft p).blocks.map leftBlock ∪ (pullRight p).blocks.map rightBlock ↔ _
  simp only [mem_union, mem_map]
  constructor
  · rintro (⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩)
    · exact (mem_pull _ _ _).mp hA
    · exact (mem_filter.mp hA).2
  · intro hB
    rcases block_one_side p hB with ⟨A, rfl⟩ | ⟨A, rfl⟩
    · exact Or.inl ⟨A, (mem_pull _ _ _).mpr hB, rfl⟩
    · exact Or.inr ⟨A, mem_filter.mpr ⟨mem_biUnion.mpr ⟨A.1, mem_univ _, by
        simpa using p.weight_lt _ hB⟩, hB⟩, rfl⟩

/-- A connected block lies in one summand, so the weighted bond poset splits as a product. -/
def sumOrderIso : WPi J × WPi K ≃o WPi (J.sum K) where
  toFun p := join p.1 p.2
  invFun p := (pullLeft p, pullRight p)
  left_inv p := by
    have hl := join_pull (join p.1 p.2)
    apply le_antisymm
    · exact join_le.mp hl.le
    · exact join_le.mp hl.ge
  right_inv := join_pull
  map_rel_iff' := join_le

omit [Fintype V] [Fintype W] in
private theorem join_weight (a : WPi J) (b : WPi K) :
    (join a b).weight = a.weight + b.weight := by
  have hd : Disjoint (a.blocks.map (leftBlock (W := W))) (b.blocks.map (rightBlock (V := V))) := by
    apply Finset.disjoint_left.mpr
    intro B hA hB
    obtain ⟨A, hA', rfl⟩ := mem_map.mp hA
    obtain ⟨C, _, he⟩ := mem_map.mp hB
    exact not_subset_cross (B := C) (nonempty_block hA') ((congrArg Prod.fst he).ge)
  simp [weight, join, sum_union hd, sum_map]

end WPi

private theorem interval_map {A B : Type*} [PartialOrder A] [PartialOrder B]
    [LocallyFiniteOrder A] [LocallyFiniteOrder B] (e : A ≃o B) (a b : A) :
    (Ico a b).map e.toEquiv.toEmbedding = Ico (e a) (e b) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  simp [mem_Ico]

private theorem incidence_mu_iso {A B : Type*} [PartialOrder A] [PartialOrder B]
    [Finite A] [LocallyFiniteOrder A] [LocallyFiniteOrder B] [DecidableEq A] [DecidableEq B]
    (e : A ≃o B) (a b : A) : IncidenceAlgebra.mu ℤ (e a) (e b) =
      IncidenceAlgebra.mu ℤ a b := by
  induction b using WellFoundedLT.induction with
  | ind b ih =>
    by_cases h : a = b
    · subst b
      simp
    · rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne (e.injective.ne h),
        IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne h, ← interval_map e, sum_map]
      congr 1
      apply sum_congr rfl
      intro x hx
      exact ih x (mem_Ico.mp hx).2

private theorem max_prod {A B : Type*} [PartialOrder A] [PartialOrder B] (a : A) (b : B) :
    IsMax ((a, b) : A × B) ↔ IsMax a ∧ IsMax b := by
  constructor
  · intro h
    exact ⟨fun x hx => (h (show (a, b) ≤ (x, b) from ⟨hx, le_rfl⟩)).1,
      fun y hy => (h (show (a, b) ≤ (a, y) from ⟨le_rfl, hy⟩)).2⟩
  · rintro ⟨ha, hb⟩ ⟨x, y⟩ h
    exact ⟨ha h.1, hb h.2⟩

theorem μ_sum [Fintype V] [Fintype W] (J : SimpleGraph V) (K : SimpleGraph W) :
    μ (J.sum K) = μ J * μ K := by
  classical
  let e : WPi J × WPi K ≃o WPi (J.sum K) := WPi.sumOrderIso
  let s := (univ : Finset (WPi J)).filter IsMax
  let t := (univ : Finset (WPi K)).filter IsMax
  have hf : (s ×ˢ t).map e.toEquiv.toEmbedding =
      (univ : Finset (WPi (J.sum K))).filter IsMax := by
    ext y
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective y
    simp [s, t, max_prod, show IsMax (e (a, b)) ↔ IsMax (a, b) from by
      constructor
      · intro h x hx
        exact e.le_iff_le.mp (h (e.le_iff_le.mpr hx))
      · intro h x hx
        obtain ⟨z, rfl⟩ := e.surjective x
        exact e.le_iff_le.mpr (h (e.le_iff_le.mp hx))]
  unfold μ
  rw [← hf, sum_map, sum_mul]
  simp_rw [mul_sum]
  rw [sum_product]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  change monomial (e (a, b)).weight (IncidenceAlgebra.mu ℤ ⊥ (e (a, b))) = _
  rw [← e.map_bot, incidence_mu_iso e, ← IncidenceAlgebra.mu_prod_mu]
  rw [monomial_mul_monomial]
  change monomial (WPi.join a b).weight _ = _
  rw [WPi.join_weight]
  rfl

namespace WPi

variable [Fintype V] {J : SimpleGraph V}

private def fullBlock (hJ : J.Connected) (w : Fin (Fintype.card V)) : WPi J where
  blocks := {(univ, w.val)}
  connected := by
    intro B hB
    obtain rfl := mem_singleton.mp hB
    rw [Finset.coe_univ]
    exact (induceUnivIso J).connected_iff.mpr hJ
  weight_lt := by
    intro B hB
    obtain rfl := mem_singleton.mp hB
    simp
  cover := fun v => ⟨(univ, w.val), mem_singleton_self _, mem_univ v⟩
  agree := by simp

private theorem fullBlock_spec (hJ : J.Connected) (a : WPi J) :
    IsMax a ↔ ∃ w, fullBlock hJ w = a := by
  constructor
  · intro h
    have hd : (↑a.blocks : Set (WeightedBlock V)).PairwiseDisjoint Prod.fst := by
      intro A hA B hB hne
      exact Finset.disjoint_left.mpr fun v hvA hvB => hne (a.agree A hA B hB v hvA hvB)
    have hu : a.blocks.biUnion Prod.fst = univ := by
      ext v
      simpa using a.cover v
    have hsum : a.weight + a.blocks.card ≤ Fintype.card V := by
      have h : (∑ B ∈ a.blocks, (B.2 + 1)) ≤ ∑ B ∈ a.blocks, B.1.card :=
        sum_le_sum fun B hB => a.weight_lt B hB
      rw [← card_biUnion hd, hu, card_univ, sum_add_distrib, sum_const,
        smul_eq_mul, mul_one] at h
      exact h
    obtain ⟨v⟩ := hJ.nonempty
    obtain ⟨B, hB, _⟩ := a.cover v
    have hpos := card_pos.mpr ⟨B, hB⟩
    let w : Fin (Fintype.card V) := ⟨a.weight, by omega⟩
    have hab : a ≤ fullBlock hJ w := by
      refine ⟨fun A _ => ⟨(univ, w.val), mem_singleton_self _, subset_univ _⟩, ?_⟩
      intro C hC
      change C ∈ ({(univ, w.val)} : Finset (WeightedBlock V)) at hC
      obtain rfl := mem_singleton.mp hC
      have he : a.under univ = a.blocks := by simp [under, rawUnder]
      rw [he]
      change a.weight ≤ w.val ∧ w.val < a.weight + a.blocks.card
      exact ⟨le_rfl, by dsimp [w]; omega⟩
    exact ⟨w, le_antisymm (h hab) hab⟩
  · rintro ⟨w, rfl⟩ b hb
    obtain ⟨C, hC, hs⟩ := hb.1 (univ, w.val) (mem_singleton_self _)
    have hCu : C.1 = univ := eq_univ_iff_forall.mpr fun v => hs (mem_univ v)
    have hbC : b.blocks = {C} := by
      ext D
      simp only [mem_singleton]
      constructor
      · intro hD
        obtain ⟨v, hv⟩ := nonempty_block hD
        exact b.agree D hD C hC v hv (hCu ▸ mem_univ v)
      · rintro rfl
        exact hC
    have hw := hb.2 C hC
    have hUnder : (fullBlock hJ w).under C.1 = {(univ, w.val)} := by
      rw [hCu]
      exact under_self (fullBlock hJ w) (B := (univ, w.val)) (mem_singleton_self _)
    rw [hUnder, sum_singleton, card_singleton] at hw
    have he : C = (univ, w.val) := Prod.ext hCu (by omega)
    exact (show b = fullBlock hJ w from WPi.ext (by rw [hbC, he]; rfl)).le

private def fullBlockEmbedding (hJ : J.Connected) : Fin (Fintype.card V) ↪ WPi J :=
  ⟨fullBlock hJ, fun _ _ h => Fin.ext <|
    congrArg (fun B : WeightedBlock V => B.2)
      (singleton_injective (congrArg WPi.blocks h))⟩

private theorem card_blocks_lt {a b : WPi J} (h : a < b) :
    b.blocks.card < a.blocks.card := by
  have hd : (↑b.blocks : Set (WeightedBlock V)).PairwiseDisjoint (fun B => a.under B.1) := by
    simpa [under, rawUnder] using under_disjoint a b (univ : Finset V)
  have hall : b.blocks.biUnion (fun B => a.under B.1) = a.blocks := by
    ext A
    simp only [mem_biUnion, under, rawUnder, mem_filter]
    exact ⟨fun ⟨_, _, ha, _⟩ => ha, fun ha => by
      obtain ⟨B, hb, hs⟩ := h.le.1 A ha
      exact ⟨B, hb, ha, hs⟩⟩
  have hcover (B : WeightedBlock V) (hB : B ∈ b.blocks) (v : V) (hv : v ∈ B.1) :
      ∃ A ∈ a.under B.1, v ∈ A.1 := by
    obtain ⟨A, hA, hAv⟩ := a.cover v
    obtain ⟨C, hC, hAC⟩ := h.le.1 A hA
    have he := b.agree C hC B hB v (hAC hAv) hv
    exact ⟨A, mem_filter.mpr ⟨hA, he ▸ hAC⟩, hAv⟩
  have hpos (B : WeightedBlock V) (hB : B ∈ b.blocks) : 0 < (a.under B.1).card := by
    obtain ⟨v, hv⟩ := nonempty_block hB
    obtain ⟨A, hA, _⟩ := hcover B hB v hv
    exact card_pos.mpr ⟨A, hA⟩
  have hsum : (∑ B ∈ b.blocks, (a.under B.1).card) = a.blocks.card := by
    rw [← card_biUnion hd, hall]
  have hle : (∑ _ ∈ b.blocks, 1) ≤ ∑ B ∈ b.blocks, (a.under B.1).card :=
    sum_le_sum hpos
  by_contra! hn
  have heq : (∑ _ ∈ b.blocks, 1) = ∑ B ∈ b.blocks, (a.under B.1).card := by
    simpa [hsum] using Nat.le_antisymm hle (by simpa [hsum] using hn)
  have hcard := (Finset.sum_eq_sum_iff_of_le hpos).mp heq
  apply h.not_ge
  have hs (B : WeightedBlock V) (hB : B ∈ b.blocks) : B ∈ a.blocks := by
    obtain ⟨A, hA⟩ := card_eq_one.mp ((hcard B hB).symm)
    have hmem : A ∈ a.under B.1 := by simp [hA]
    obtain ⟨hAa, hAB⟩ := mem_filter.mp hmem
    have hBA : B.1 ⊆ A.1 := by
      intro v hv
      obtain ⟨C, hC, hvC⟩ := hcover B hB v hv
      rw [hA, mem_singleton] at hC
      exact hC ▸ hvC
    have hw := h.le.2 B hB
    rw [hA, sum_singleton, card_singleton] at hw
    have hwt : A.2 = B.2 := by omega
    have eq : A = B := Prod.ext (Subset.antisymm hAB hBA) hwt
    exact eq ▸ hAa
  exact ⟨fun B hB => ⟨B, hs B hB, Subset.rfl⟩, fun A hA => by
    obtain ⟨B, hB, hab⟩ := h.le.1 A hA
    obtain ⟨v, hv⟩ := nonempty_block hA
    have he := a.agree A hA B (hs B hB) v hv (hab hv)
    have ha' : A ∈ b.blocks := he ▸ hB
    rw [under_self b ha', sum_singleton, card_singleton]
    exact ⟨le_rfl, Nat.lt_succ_self _⟩⟩

private theorem μ_connected (hJ : J.Connected) :
    μ J = ∑ w : Fin (Fintype.card V),
      monomial w.val (IncidenceAlgebra.mu ℤ (⊥ : WPi J) (fullBlock hJ w)) := by
  classical
  have he : (univ : Finset (WPi J)).filter IsMax = univ.map (fullBlockEmbedding hJ) := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_map]
    exact fullBlock_spec hJ a
  rw [μ, he, sum_map]
  apply sum_congr rfl
  intro w _
  change monomial (∑ A ∈ ({(univ, w.val)} : Finset (WeightedBlock V)), A.2) _ = _
  rw [sum_singleton]
  rfl

end WPi

section Enumeration

variable [Fintype V]

private def PartOn (allowed : Finset V → Prop) (p : Finset (WeightedBlock V)) (s : Finset V) :
    Prop :=
  (∀ B ∈ p, B.1 ⊆ s ∧ allowed B.1 ∧ B.2 < B.1.card) ∧
  (∀ v ∈ s, ∃ B ∈ p, v ∈ B.1) ∧
  ∀ A ∈ p, ∀ B ∈ p, ∀ v ∈ A.1, v ∈ B.1 → A = B

omit [DecidableEq V] [Fintype V] in
private theorem partOn_empty {allowed : Finset V → Prop} {p : Finset (WeightedBlock V)} :
    PartOn allowed p ∅ ↔ p = ∅ := by
  constructor
  · intro h
    apply eq_empty_iff_forall_notMem.mpr
    intro B hB
    have hsub := (h.1 B hB).1
    have hc := (h.1 B hB).2.2
    rw [subset_empty.mp hsub, card_empty] at hc
    exact Nat.not_lt_zero _ hc
  · rintro rfl
    simp [PartOn]

/-- Select the block containing the first remaining vertex, with each admissible weight. -/
private def listEnum (allowed : Finset V → Prop) [DecidablePred allowed] :
    ℕ → List V → List (Finset (WeightedBlock V))
  | _, [] => [∅]
  | 0, _ :: _ => []
  | fuel + 1, v :: t =>
    (t.sublists'.filter fun l => decide (allowed (v :: l).toFinset)).flatMap fun l =>
      let B := (v :: l).toFinset
      (List.range B.card).flatMap fun w =>
        (listEnum allowed fuel (t.filter fun u => decide (u ∉ B))).map (insert (B, w))

omit [Fintype V] in
private theorem listEnum_spec (allowed : Finset V → Prop) [DecidablePred allowed]
    (fuel : ℕ) (s : List V) (hs : s.toFinset.card ≤ fuel)
    (p : Finset (WeightedBlock V)) :
    p ∈ listEnum allowed fuel s ↔ PartOn allowed p s.toFinset := by
  induction fuel generalizing s p with
  | zero =>
    cases s with
    | nil => simp [listEnum, partOn_empty]
    | cons v t =>
      have hc : 0 < (v :: t).toFinset.card := card_pos.mpr ⟨v, by simp⟩
      omega
  | succ fuel ih =>
    cases s with
    | nil => simp [listEnum, partOn_empty]
    | cons v t =>
      simp only [listEnum, List.mem_flatMap, List.mem_filter, List.mem_sublists',
        decide_eq_true_eq, List.mem_range, List.mem_map]
      have rem_eq (B : Finset V) (hv : v ∈ B) :
          (t.filter fun u => decide (u ∉ B)).toFinset = (v :: t).toFinset \ B := by
        ext u
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_sdiff, List.mem_cons]
        constructor
        · exact fun ⟨ht, hB⟩ => ⟨Or.inr ht, hB⟩
        · rintro ⟨rfl | ht, hB⟩
          · exact (hB hv).elim
          · exact ⟨ht, hB⟩
      have smaller (B : Finset V) (hB : B ⊆ (v :: t).toFinset) (hv : v ∈ B) :
          (t.filter fun u => decide (u ∉ B)).toFinset.card ≤ fuel := by
        have hp := card_pos.mpr ⟨_, hv⟩
        rw [rem_eq B hv, card_sdiff_of_subset hB]
        omega
      constructor
      · rintro ⟨l, ⟨hl, ha⟩, w, hw, q, hq, rfl⟩
        let B := (v :: l).toFinset
        have hv : v ∈ B := by simp [B]
        have hsub : B ⊆ (v :: t).toFinset := by
          intro u hu
          simp only [B, List.mem_toFinset, List.mem_cons] at hu ⊢
          exact hu.imp_right (fun hu' => hl.subset hu')
        have h := (ih _ (smaller B hsub hv) q).mp hq
        rw [rem_eq B hv] at h
        refine ⟨?_, ?_, ?_⟩
        · intro A hA
          rcases mem_insert.mp hA with rfl | hA
          · exact ⟨hsub, ha, hw⟩
          · obtain ⟨hs', ha', hw'⟩ := h.1 A hA
            exact ⟨hs'.trans sdiff_subset, ha', hw'⟩
        · intro u hu
          by_cases hb : u ∈ B
          · exact ⟨(B, w), mem_insert_self _ _, hb⟩
          · obtain ⟨A, hA, hAu⟩ := h.2.1 u (mem_sdiff.mpr ⟨hu, hb⟩)
            exact ⟨A, mem_insert_of_mem hA, hAu⟩
        · intro A hA C hC u hAu hCu
          rcases mem_insert.mp hA with rfl | hA <;> rcases mem_insert.mp hC with rfl | hC
          · rfl
          · exact ((mem_sdiff.mp ((h.1 C hC).1 hCu)).2 hAu).elim
          · exact ((mem_sdiff.mp ((h.1 A hA).1 hAu)).2 hCu).elim
          · exact h.2.2 A hA C hC u hAu hCu
      · intro hp
        obtain ⟨A, hA, hv⟩ := hp.2.1 v (by simp)
        obtain ⟨hsub, ha, hw⟩ := hp.1 A hA
        let l := t.filter (fun u => decide (u ∈ A.1))
        have hl : (v :: l).toFinset = A.1 := by
          ext u
          have he := @hsub u
          simp only [l, List.mem_toFinset, List.mem_cons, List.mem_filter,
            decide_eq_true_eq] at he ⊢
          constructor
          · rintro (rfl | ⟨_, hu⟩)
            · exact hv
            · exact hu
          · intro hu
            exact (he hu).imp_right fun ht => ⟨ht, hu⟩
        refine ⟨l, ⟨List.filter_sublist, hl ▸ ha⟩, A.2, hl ▸ hw, p.erase A, ?_, ?_⟩
        · rw [hl]
          apply (ih _ (smaller A.1 hsub hv) _).mpr
          rw [rem_eq A.1 hv]
          refine ⟨?_, ?_, ?_⟩
          · intro B hB
            obtain ⟨hne, hBp⟩ := mem_erase.mp hB
            obtain ⟨hBs, hb, hbw⟩ := hp.1 B hBp
            exact ⟨fun u hu => mem_sdiff.mpr ⟨hBs hu, fun huA =>
              hne (hp.2.2 B hBp A hA u hu huA)⟩, hb, hbw⟩
          · intro u hu
            obtain ⟨B, hB, huB⟩ := hp.2.1 u (mem_sdiff.mp hu).1
            refine ⟨B, mem_erase.mpr ⟨?_, hB⟩, huB⟩
            rintro rfl
            exact (mem_sdiff.mp hu).2 huB
          · intro B hB C hC u huB huC
            exact hp.2.2 B (mem_of_mem_erase hB) C (mem_of_mem_erase hC) u huB huC
        · rw [hl]
          exact insert_erase hA

variable (J : SimpleGraph V)

omit [DecidableEq V] in
private theorem blocks_spec (p : Finset (WeightedBlock V)) :
    PartOn (fun B => (J.induce (B : Set V)).Connected) p univ ↔ ∃ a : WPi J, a.blocks = p := by
  constructor
  · rintro ⟨hb, hc, hd⟩
    exact ⟨⟨p, fun B hB => (hb B hB).2.1, fun B hB => (hb B hB).2.2,
      fun v => hc v (mem_univ _), hd⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨fun B hB => ⟨subset_univ _, a.connected B hB, a.weight_lt B hB⟩,
      fun v _ => a.cover v, a.agree⟩

variable [DecidableRel J.Adj]

private instance (B : Finset V) : DecidableRel (J.induce (B : Set V)).Adj :=
  fun v w => inferInstanceAs (Decidable (J.Adj v.val w.val))

private instance : DecidablePred (fun (B : Finset V) => (J.induce (B : Set V)).Connected) :=
  fun B => inferInstanceAs (Decidable (J.induce (B : Set V)).Connected)

private def blocksEmbedding : WPi J ↪ Finset (WeightedBlock V) :=
  ⟨WPi.blocks, fun _ _ => WPi.ext⟩

private def runRanks (bottom : Finset (WeightedBlock V))
    (s : Finset (Finset (WeightedBlock V))) (maxCard : ℕ) :
    ℕ → Finset (Finset (WeightedBlock V) × ℤ)
  | 0 => ∅
  | r + 1 =>
    let previous := runRanks bottom s maxCard r
    previous ∪ (s.filter fun b => b.card = maxCard - (r + 1)).image (fun b =>
      (b, if b = bottom then 1 else
        Int.neg (∑ x ∈ previous.filter (fun x => WPi.rawRefines x.1 b), x.2)))

private noncomputable def annotated (J : SimpleGraph V) :
    WPi J ↪ (Finset (WeightedBlock V) × ℤ) :=
  ⟨fun a => (a.blocks, IncidenceAlgebra.mu ℤ (⊥ : WPi J) a),
    fun _ _ h => WPi.ext (congrArg Prod.fst h)⟩

omit [DecidableRel J.Adj] in
private theorem runRanks_correct (s : Finset (Finset (WeightedBlock V)))
    (hs : s = (univ : Finset (WPi J)).map (blocksEmbedding J))
    (maxCard : ℕ) (hbound : ∀ a : WPi J, a.blocks.card < maxCard) (r : ℕ) (hr : r ≤ maxCard) :
    runRanks (⊥ : WPi J).blocks s maxCard r =
      (univ.filter fun a : WPi J => maxCard - r ≤ a.blocks.card).map (annotated J) := by
  classical
  have rank (a b : WPi J) (hab : a < b) := WPi.card_blocks_lt hab
  induction r with
  | zero =>
    simp [runRanks, show (univ.filter fun a : WPi J => maxCard ≤ a.blocks.card) = ∅ by
      ext a; simp [(hbound a).not_ge]]
  | succ r ih =>
    have hr' : r ≤ maxCard := by omega
    let previous := (univ.filter fun a : WPi J => maxCard - r ≤ a.blocks.card).map (annotated J)
    rw [runRanks, ih hr']
    have hval (b : WPi J) (hb : b.blocks.card = maxCard - (r + 1)) :
        (if b.blocks = (⊥ : WPi J).blocks then 1 else
          Int.neg (∑ x ∈ previous.filter (fun x => WPi.rawRefines x.1 b.blocks), x.2)) =
          IncidenceAlgebra.mu ℤ (⊥ : WPi J) b := by
      by_cases he : b = ⊥
      · subst b
        simp
      · rw [if_neg (fun h => he (WPi.ext h)), IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne (Ne.symm he)]
        have hf : previous.filter (fun x => WPi.rawRefines x.1 b.blocks) =
            (Ico (⊥ : WPi J) b).map (annotated J) := by
          ext x
          simp only [previous, mem_filter, mem_map, mem_univ, true_and, mem_Ico, bot_le]
          constructor
          · rintro ⟨⟨a, ha, rfl⟩, hab⟩
            change a ≤ b at hab
            have hlt : a < b := lt_of_le_of_ne hab (fun h => by rw [h, hb] at ha; omega)
            exact ⟨a, hlt, rfl⟩
          · rintro ⟨a, ha, rfl⟩
            have hlt := rank a b ha
            exact ⟨⟨a, by omega, rfl⟩, ha.le⟩
        rw [hf, sum_map]
        rfl
    change previous ∪ _ = _
    ext x
    simp only [previous, mem_union, mem_map, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨p, ⟨hp, hc⟩, rfl⟩)
      · exact ⟨a, by omega, rfl⟩
      · rw [hs] at hp
        obtain ⟨a, _, ha⟩ := mem_map.mp hp
        change a.blocks = p at ha
        subst p
        exact ⟨a, by omega, by rw [hval a hc]; rfl⟩
    · rintro ⟨a, ha, rfl⟩
      by_cases hp : maxCard - r ≤ a.blocks.card
      · exact Or.inl ⟨a, hp, rfl⟩
      · have hc : a.blocks.card = maxCard - (r + 1) := by omega
        refine Or.inr ⟨a.blocks, ⟨?_, hc⟩, ?_⟩
        · rw [hs]
          exact mem_map_of_mem _ (mem_univ a)
        · rw [hval a hc]
          rfl

private def forceEntry {A : Type*} (a : A) (v : ℤ) (tail : List (A × ℤ)) :
    List (A × ℤ) :=
  match v with
  | .ofNat n => (a, .ofNat n) :: tail
  | .negSucc n => (a, .negSucc n) :: tail

private theorem forceEntries_eq {A : Type*} (s : List A) (f : A → ℤ) :
    s.foldr (fun a tail => forceEntry a (f a) tail) [] = s.map (fun a => (a, f a)) := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [List.foldr_cons, List.map_cons, ih]
    cases f a <;> rfl

private def rankSweep {A : Type*} [DecidableEq A] (rank : A → ℕ) (refines : A → A → Bool)
    (bottom : A) (s : List A) (maxCard : ℕ) : ℕ → List (A × ℤ)
  | 0 => []
  | r + 1 =>
    let previous := rankSweep rank refines bottom s maxCard r
    previous ++ (s.filter fun b => rank b == maxCard - (r + 1)).foldr (fun b tail =>
      forceEntry b (if b = bottom then 1 else
        Int.neg ((previous.filter fun x => refines x.1 b).map Prod.snd).sum) tail) []

private theorem rankSweep_succ {A : Type*} [DecidableEq A] (rank : A → ℕ)
    (refines : A → A → Bool) (bottom : A) (s : List A) (maxCard r : ℕ) :
    rankSweep rank refines bottom s maxCard (r + 1) =
      let previous := rankSweep rank refines bottom s maxCard r
      previous ++ (s.filter fun b => rank b == maxCard - (r + 1)).map (fun b =>
        (b, if b = bottom then 1 else
          Int.neg ((previous.filter fun x => refines x.1 b).map Prod.snd).sum)) := by
  rw [rankSweep, forceEntries_eq]

private abbrev runList (bottom : Finset (WeightedBlock V))
    (s : List (Finset (WeightedBlock V))) (maxCard r : ℕ) :
    List (Finset (WeightedBlock V) × ℤ) :=
  rankSweep Finset.card (fun a b => decide (WPi.rawRefines a b)) bottom s maxCard r

omit [Fintype V] in
private theorem runList_rank (bottom : Finset (WeightedBlock V))
    (s : List (Finset (WeightedBlock V))) (maxCard r : ℕ) (x) (hx : x ∈ runList bottom s maxCard r) :
    maxCard - r ≤ x.1.card := by
  induction r with
  | zero => simp [runList, rankSweep] at hx
  | succ r ih =>
    simp only [runList, rankSweep_succ, List.mem_append, List.mem_map, List.mem_filter,
      beq_iff_eq] at hx
    rcases hx with hx | ⟨b, ⟨_, hb⟩, rfl⟩
    · exact (by omega : maxCard - (r + 1) ≤ maxCard - r).trans (ih hx)
    · exact hb.ge

omit [Fintype V] in
private theorem runList_correct (bottom : Finset (WeightedBlock V))
    (s : List (Finset (WeightedBlock V))) (hs : s.Nodup) (maxCard r : ℕ) (hr : r ≤ maxCard) :
    (runList bottom s maxCard r).Nodup ∧
      (↑(runList bottom s maxCard r) : Multiset _) = (runRanks bottom s.toFinset maxCard r).val := by
  induction r with
  | zero => simp [runList, rankSweep, runRanks]
  | succ r ih =>
    have hr' : r ≤ maxCard := by omega
    obtain ⟨hn, he⟩ := ih hr'
    let prev := runList bottom s maxCard r
    let bs := s.filter (fun b => b.card == maxCard - (r + 1))
    let entry (b : Finset (WeightedBlock V)) := (b, if b = bottom then 1 else
      Int.neg ((prev.filter fun x => decide (WPi.rawRefines x.1 b)).map Prod.snd).sum)
    have hinj : Function.Injective entry := fun _ _ h => congrArg Prod.fst h
    have hdisj : ∀ x ∈ prev, ∀ y ∈ bs.map entry, x ≠ y := by
      intro x hxp y hx heq
      subst y
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      have hp := runList_rank bottom s maxCard r (entry b) hxp
      have hbc : b.card = maxCard - (r + 1) := by simpa [bs] using (List.mem_filter.mp hb).2
      change maxCard - r ≤ b.card at hp
      omega
    have hf : bs.toFinset = s.toFinset.filter (fun b => b.card = maxCard - (r + 1)) := by
      ext b
      simp [bs]
    have hentry (b : Finset (WeightedBlock V)) :
        entry b = (b, if b = bottom then 1 else
          Int.neg (∑ x ∈ (runRanks bottom s.toFinset maxCard r).filter
            (fun x => WPi.rawRefines x.1 b), x.2)) := by
      have e := congrArg (fun t : Multiset _ =>
        ((t.filter fun x => WPi.rawRefines x.1 b).map Prod.snd).sum) he
      simpa [entry, prev, Finset.sum] using congrArg (fun z : ℤ =>
        (b, if b = bottom then 1 else Int.neg z)) e
    have hnd : (prev ++ bs.map entry).Nodup := List.nodup_append.mpr
      ⟨hn, (hs.filter _).map hinj, hdisj⟩
    unfold runList
    rw [rankSweep_succ]
    refine ⟨hnd, ?_⟩
    calc
      Multiset.ofList (prev ++ bs.map entry) = (prev ++ bs.map entry).toFinset.val :=
        congrArg Finset.val (List.toFinset_eq hnd)
      _ = _ := by
        apply congrArg Finset.val
        have hm : (bs.map entry).toFinset = bs.toFinset.image entry := by
          ext x
          simp [List.mem_map, mem_image]
        rw [List.toFinset_append, hm, hf, runRanks]
        rw [show prev.toFinset = runRanks bottom s.toFinset maxCard r from
          Finset.val_injective ((congrArg Finset.val (List.toFinset_eq hn)).symm.trans he)]
        congr 1
        exact image_congr (fun b _ => hentry b)

private def sumTopList (bottom : Finset (WeightedBlock V)) (s : List (Finset (WeightedBlock V)))
    (maxCard r : ℕ) (top : Finset (WeightedBlock V)) : ℤ :=
  (((runList bottom s maxCard r).filter fun b => decide (b.1 = top)).map Prod.snd).sum

omit [Fintype V] in
private theorem sumTopList_spec (bottom : Finset (WeightedBlock V))
    (s : List (Finset (WeightedBlock V))) (hs : s.Nodup) (maxCard r : ℕ)
    (hr : r ≤ maxCard) (top : Finset (WeightedBlock V)) :
    sumTopList bottom s maxCard r top =
      ∑ x ∈ (runRanks bottom s.toFinset maxCard r).filter (fun x => x.1 = top), x.2 := by
  have he := (runList_correct bottom s hs maxCard r hr).2
  have h := congrArg (fun t : Multiset _ => ((t.filter fun x => x.1 = top).map Prod.snd).sum) he
  simpa [sumTopList, Finset.sum] using h

private def mask {n : ℕ} (s : Finset (Fin n)) : ℕ :=
  s.fold (· ||| ·) 0 fun v => 2^v.val

private theorem mask_testBit {n : ℕ} (s : Finset (Fin n)) (i : ℕ) :
    (mask s).testBit i = true ↔ ∃ v ∈ s, v.val = i := by
  induction s using Finset.induction_on with
  | empty => simp [mask]
  | @insert v s hv ih =>
    unfold mask at *
    rw [Finset.fold_insert hv, Nat.testBit_or, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq, ih, mem_insert]
    constructor
    · rintro (rfl | ⟨w, hw, he⟩)
      · exact ⟨v, Or.inl rfl, rfl⟩
      · exact ⟨w, Or.inr hw, he⟩
    · rintro ⟨w, rfl | hw, he⟩
      · exact Or.inl he
      · exact Or.inr ⟨w, hw, he⟩

private theorem mask_subset {n : ℕ} (s t : Finset (Fin n)) :
    mask s &&& mask t = mask s ↔ s ⊆ t := by
  constructor
  · intro h v hv
    have hs : (mask s).testBit v.val = true := (mask_testBit _ _).2 ⟨v, hv, rfl⟩
    have ht := congrArg (fun m : ℕ => m.testBit v.val) h
    rw [Nat.testBit_and, hs, Bool.true_and] at ht
    obtain ⟨w, hw, he⟩ := (mask_testBit _ _).1 ht
    exact (Fin.ext he : w = v) ▸ hw
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hs : (mask s).testBit i
    · simp
    · obtain ⟨v, hv, hi⟩ := (mask_testBit _ _).1 hs
      rw [(mask_testBit _ _).2 ⟨v, h hv, hi⟩]
      rfl

open Prod.Lex in
private abbrev EncodedBlock := ℕ ×ₗ ℕ

private def encodeBlock {n : ℕ} : WeightedBlock (Fin n) ↪ EncodedBlock :=
  ⟨fun B => toLex (mask B.1, B.2), by
    intro A B h
    have he := congrArg ofLex h
    have hm : mask A.1 = mask B.1 := congrArg Prod.fst he
    exact Prod.ext
      (Subset.antisymm ((mask_subset _ _).1 (by simp [hm]))
        ((mask_subset _ _).1 (by simp [hm])))
      (congrArg (fun p : ℕ × ℕ => p.2) he)⟩

@[simp] private theorem encodeBlock_weight {n : ℕ} (B : WeightedBlock (Fin n)) :
    (ofLex (encodeBlock B)).2 = B.2 := rfl

private def encodePart {n : ℕ} (s : Finset (WeightedBlock (Fin n))) : List EncodedBlock :=
  (s.map encodeBlock).val.liftOn (List.insertionSort (· ≤ ·)) (fun a b h =>
    ((List.perm_insertionSort (· ≤ ·) a).trans
      (h.trans (List.perm_insertionSort (· ≤ ·) b).symm)).eq_of_pairwise'
      (List.pairwise_insertionSort (· ≤ ·) a) (List.pairwise_insertionSort (· ≤ ·) b))

private theorem encodePart_eq {n : ℕ} (s : Finset (WeightedBlock (Fin n))) :
    encodePart s = (s.map encodeBlock).sort := by
  unfold encodePart Finset.sort Multiset.sort
  induction (s.map encodeBlock).val using Quotient.inductionOn with
  | _ l => exact (List.mergeSort_eq_insertionSort (· ≤ ·) l).symm

private theorem encodePart_injective {n : ℕ} :
    Function.Injective (encodePart (n := n)) := by
  intro p q h
  have hh := congrArg List.toFinset h
  rw [encodePart_eq, encodePart_eq, sort_toFinset, sort_toFinset] at hh
  exact Finset.map_injective _ hh

private theorem encodePart_length {n : ℕ} (p : Finset (WeightedBlock (Fin n))) :
    (encodePart p).length = p.card := by simp [encodePart_eq]

private def fits (a b : EncodedBlock) : Bool :=
  decide ((ofLex a).1 &&& (ofLex b).1 = (ofLex a).1)

private def codeRefines (a b : List EncodedBlock) : Bool :=
  (a.all fun A => b.any (fits A)) && b.all (fun B =>
    let finer := a.filter (fun A => fits A B)
    let total := (finer.map (fun A => (ofLex A).2)).sum
    decide (total ≤ (ofLex B).2 ∧ (ofLex B).2 < total + finer.length))

private theorem codeRefines_correct {n : ℕ} (a b : Finset (WeightedBlock (Fin n))) :
    codeRefines (encodePart a) (encodePart b) = decide (WPi.rawRefines a b) := by
  have hf (B : WeightedBlock (Fin n)) :
      ((encodePart a).filter (fun A => fits A (encodeBlock B))).toFinset =
        (WPi.rawUnder a B.1).map encodeBlock := by
    ext u
    simp only [List.mem_toFinset, List.mem_filter, encodePart_eq, mem_sort, mem_map,
      WPi.rawUnder, mem_filter]
    constructor
    · rintro ⟨⟨A, ha, rfl⟩, hA⟩
      exact ⟨A, ⟨ha, (mask_subset _ _).mp (of_decide_eq_true hA)⟩, rfl⟩
    · rintro ⟨A, ⟨ha, hA⟩, rfl⟩
      exact ⟨⟨A, ha, rfl⟩, decide_eq_true ((mask_subset _ _).mpr hA)⟩
  have he (B : WeightedBlock (Fin n)) :
      (↑((encodePart a).filter (fun A => fits A (encodeBlock B))) : Multiset EncodedBlock) =
        ((WPi.rawUnder a B.1).map encodeBlock).val := by
    have hd := (Finset.sort_nodup (a.map encodeBlock) (· ≤ ·)).filter
        (fun A => fits A (encodeBlock B))
    rw [encodePart_eq]
    exact (congrArg Finset.val (List.toFinset_eq hd)).trans (congrArg Finset.val (by
      simpa only [encodePart_eq] using hf B))
  have hc (B : WeightedBlock (Fin n)) : ((encodePart a).filter (fun A =>
      fits A (encodeBlock B))).length = (WPi.rawUnder a B.1).card := by
    simpa using congrArg Multiset.card (he B)
  have hs (B : WeightedBlock (Fin n)) : (((encodePart a).filter (fun A =>
      fits A (encodeBlock B))).map (fun A => (ofLex A).2)).sum =
        ∑ A ∈ WPi.rawUnder a B.1, A.2 := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, he, ← Finset.sum, sum_map]
    simp
  have hm (u : EncodedBlock) (p : Finset (WeightedBlock (Fin n))) :
      u ∈ encodePart p ↔ ∃ A ∈ p, encodeBlock A = u := by simp [encodePart_eq]
  have hk : codeRefines (encodePart a) (encodePart b) = true ↔ WPi.rawRefines a b := by
    unfold codeRefines WPi.rawRefines WPi.refinesWith
    simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hr, hw⟩
      refine ⟨?_, ?_⟩
      · intro A hA
        obtain ⟨u, hu, hfit⟩ := hr _ ((hm _ _).mpr ⟨A, hA, rfl⟩)
        obtain ⟨B, hB, rfl⟩ := (hm _ _).mp hu
        exact ⟨B, hB, (mask_subset _ _).mp (of_decide_eq_true hfit)⟩
      · intro B hB
        simpa only [hs B, hc B, encodeBlock_weight] using hw _ ((hm _ _).mpr ⟨B, hB, rfl⟩)
    · rintro ⟨hr, hw⟩
      refine ⟨?_, ?_⟩
      · intro u hu
        obtain ⟨A, hA, rfl⟩ := (hm _ _).mp hu
        obtain ⟨B, hB, hAB⟩ := hr A hA
        exact ⟨_, (hm _ _).mpr ⟨B, hB, rfl⟩, decide_eq_true ((mask_subset _ _).mpr hAB)⟩
      · intro u hu
        obtain ⟨B, hB, rfl⟩ := (hm _ _).mp hu
        simpa only [hs B, hc B, encodeBlock_weight] using hw B hB
  cases ha : codeRefines (encodePart a) (encodePart b) <;>
    cases hb : decide (WPi.rawRefines a b) <;>
    simp_all

private theorem rankSweep_map {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (rankA : A → ℕ) (rankB : B → ℕ) (relA : A → A → Bool) (relB : B → B → Bool)
    (hrank : ∀ a, rankB (e a) = rankA a) (hrel : ∀ a b, relB (e a) (e b) = relA a b)
    (bottom : A) (s : List A) (maxCard r : ℕ) :
    rankSweep rankB relB (e bottom) (s.map e) maxCard r =
      (rankSweep rankA relA bottom s maxCard r).map (Prod.map e id) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [rankSweep_succ, rankSweep_succ, ih, List.map_append, List.filter_map]
    simp only [Function.comp_def, hrank, List.map_map]
    congr 1
    apply List.map_congr_left
    intro b _
    simp [e.apply_eq_iff_eq, List.filter_map, List.map_map, Function.comp_def, hrel]

private def sumTopCodeList {n : ℕ} (bottom : Finset (WeightedBlock (Fin n)))
    (s : List (Finset (WeightedBlock (Fin n)))) (maxCard r : ℕ)
    (top : Finset (WeightedBlock (Fin n))) : ℤ :=
  (((rankSweep List.length codeRefines (encodePart bottom) (s.map encodePart) maxCard r).filter
    fun x => decide (x.1 = encodePart top)).map Prod.snd).sum

private theorem sumTopCodeList_spec {n : ℕ} (bottom : Finset (WeightedBlock (Fin n)))
    (s : List (Finset (WeightedBlock (Fin n)))) (maxCard r : ℕ)
    (top : Finset (WeightedBlock (Fin n))) :
    sumTopCodeList bottom s maxCard r top = sumTopList bottom s maxCard r top := by
  let e : Finset (WeightedBlock (Fin n)) ↪ List EncodedBlock := ⟨encodePart, encodePart_injective⟩
  unfold sumTopCodeList sumTopList
  change (((rankSweep List.length codeRefines (e bottom) (s.map e) maxCard r).filter
    fun x => decide (x.1 = e top)).map Prod.snd).sum = _
  rw [rankSweep_map e Finset.card List.length _
    codeRefines encodePart_length codeRefines_correct bottom s maxCard r]
  simp [List.filter_map, List.map_map, Function.comp_def, e.apply_eq_iff_eq]

private def catalogTable {n : ℕ} (blocks : Finset (Finset (Fin n))) :
    List (List EncodedBlock × ℤ) :=
  let s := listEnum (· ∈ blocks) (Fintype.card (Fin n)) (List.finRange n)
  let bottom := encodePart ((univ : Finset (Fin n)).map WPi.singletonBlock)
  rankSweep List.length codeRefines bottom (s.map encodePart).dedup
    (Fintype.card (Fin n) + 1) (Fintype.card (Fin n))

private def catalogCoeff {n : ℕ} (table : List (List EncodedBlock × ℤ))
    (w : Fin (Fintype.card (Fin n))) : ℤ :=
  let top := encodePart ({(univ, w.val)} : Finset (WeightedBlock (Fin n)))
  ((table.filter (fun x => decide (x.1 = top))).map Prod.snd).sum

private def computeCatalog {n : ℕ} (blocks : Finset (Finset (Fin n)))
    (w : Fin (Fintype.card (Fin n))) : ℤ :=
  catalogCoeff (n := n) (catalogTable blocks) w

private def catalogCoeffs {n : ℕ} (blocks : Finset (Finset (Fin n))) : List ℤ :=
  let table := catalogTable blocks
  (List.finRange (Fintype.card (Fin n))).map (catalogCoeff (n := n) table)

private theorem catalogCoeffs_get {n : ℕ} (blocks : Finset (Finset (Fin n)))
    (w : Fin (Fintype.card (Fin n))) :
    (catalogCoeffs blocks)[w.val]? = some (computeCatalog blocks w) := by
  have hi : w.val < (catalogCoeffs blocks).length := by simpa [catalogCoeffs] using w.isLt
  rw [List.getElem?_eq_getElem hi]
  simp [catalogCoeffs, computeCatalog]

private theorem μ_catalog {n : ℕ} (J : SimpleGraph (Fin n)) [DecidableRel J.Adj]
    (hJ : J.Connected) (blocks : Finset (Finset (Fin n)))
    (h : ∀ (B : Finset (Fin n)), (J.induce (B : Set (Fin n))).Connected ↔ B ∈ blocks) :
    μ J = ∑ w : Fin (Fintype.card (Fin n)), monomial (Fin.val w) (computeCatalog blocks w) := by
  rw [WPi.μ_connected hJ]
  refine sum_congr rfl fun w _ => congrArg (fun c : ℤ => monomial (Fin.val w) c) ?_
  let s := listEnum (· ∈ blocks) (Fintype.card (Fin n)) (List.finRange n)
  have hd := List.nodup_dedup s
  have he : s.dedup.toFinset =
      (univ : Finset (WPi J)).map (blocksEmbedding J) := by
    ext p
    simp only [List.mem_toFinset, List.mem_dedup, s]
    rw [listEnum_spec _ (Fintype.card (Fin n)) (List.finRange n) (by simp),
      List.toFinset_finRange]
    simp only [mem_map, mem_univ, true_and]
    change _ ↔ ∃ a : WPi J, a.blocks = p
    simpa only [PartOn, ← h] using blocks_spec J p
  have hcomp : computeCatalog blocks w =
      sumTopList (⊥ : WPi J).blocks s.dedup (Fintype.card (Fin n) + 1)
        (Fintype.card (Fin n)) {(univ, w.val)} := by
    calc
      _ = sumTopCodeList (⊥ : WPi J).blocks s.dedup (Fintype.card (Fin n) + 1)
          (Fintype.card (Fin n)) {(univ, w.val)} := by
        simp only [computeCatalog, catalogCoeff, catalogTable, sumTopCodeList, s, WPi.bot_blocks,
          ← List.dedup_map_of_injective encodePart_injective]
      _ = _ := sumTopCodeList_spec _ _ _ _ _
  rw [hcomp, sumTopList_spec _ _ hd _ _ (Nat.le_succ _) _]
  have hb (a : WPi J) : a.blocks.card < Fintype.card (Fin n) + 1 := by
    by_cases ha : a = ⊥
    · subst a
      simp
    · have hc := WPi.card_blocks_lt (bot_lt_iff_ne_bot.mpr ha)
      simpa using hc.trans (Nat.lt_succ_self _)
  rw [runRanks_correct J _ he _ hb _ (Nat.le_succ _)]
  have hf : ((univ.filter (fun a : WPi J =>
      Fintype.card (Fin n) + 1 - Fintype.card (Fin n) ≤ a.blocks.card)).map (annotated J)).filter
      (fun x => x.1 = {(univ, w.val)}) = {annotated J (WPi.fullBlock hJ w)} := by
    ext x
    simp only [mem_filter, mem_map, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨⟨a, _, rfl⟩, hax⟩
      exact congrArg (annotated J) (WPi.ext hax)
    · rintro rfl
      exact ⟨⟨_, by change _ ≤ ({(univ, w.val)} : Finset _).card; simp, rfl⟩, rfl⟩
  rw [hf, sum_singleton]
  rfl

end Enumeration

def K3 : SimpleGraph (Fin 3) := ⊤
def P3 : SimpleGraph (Fin 3) := pathGraph 3
def C5 : SimpleGraph (Fin 5) := cycleGraph 5
def House : SimpleGraph (Fin 5) := C5 ⊔ edge 1 4

instance : DecidableRel K3.Adj := Top.adjDecidable _
instance : DecidableRel P3.Adj := fun _ _ => decidable_of_iff' _ pathGraph_adj
instance : DecidableRel C5.Adj := inferInstanceAs (DecidableRel (cycleGraph 5).Adj)
instance : DecidableRel House.Adj := fun u v =>
  decidable_of_iff' (C5.Adj u v ∨ ((u = 1 ∧ v = 4 ∨ u = 4 ∧ v = 1) ∧ u ≠ v))
    ((sup_adj C5 (edge 1 4) u v).trans (or_congr Iff.rfl (edge_adj (1 : Fin 5) 4 u v)))

theorem K3_connected : K3.Connected := connected_top_iff.mpr inferInstance
theorem P3_connected : P3.Connected := pathGraph_connected 2
theorem C5_connected : C5.Connected := cycleGraph_connected
theorem House_connected : House.Connected := C5_connected.mono le_sup_left

/- The closed equalities below evaluate the interval recurrence on the enumerated
partitions. The kernel checks the resulting coefficients. -/

private def pathBlocks : Finset (Finset (Fin 3)) :=
  {{0}, {1}, {2}, {0, 1}, {1, 2}, {0, 1, 2}}

private def triangleBlocks : Finset (Finset (Fin 3)) := insert {0, 2} pathBlocks

private theorem pathBlocks_spec (B : Finset (Fin 3)) :
    (P3.induce (B : Set (Fin 3))).Connected ↔ B ∈ pathBlocks := by
  fin_cases B <;> decide +kernel

private theorem triangleBlocks_spec (B : Finset (Fin 3)) :
    (K3.induce (B : Set (Fin 3))).Connected ↔ B ∈ triangleBlocks := by
  fin_cases B <;> decide +kernel

theorem μ_K3 : μ K3 = 2 + 5 * X + 2 * X^2 := by
  have hcoeff : catalogCoeffs triangleBlocks = [2, 5, 2] := by decide +kernel
  have h : ∀ w : Fin 3, computeCatalog triangleBlocks w = ![(2 : ℤ), 5, 2] w := by
    intro w
    have hw := congrArg (fun l : List ℤ => l[w.val]?) hcoeff
    exact Option.some.inj ((catalogCoeffs_get (n := 3) triangleBlocks w).symm.trans
      (hw.trans (by fin_cases w <;> rfl)))
  rw [μ_catalog K3 K3_connected triangleBlocks triangleBlocks_spec]
  trans ∑ w : Fin 3, monomial w.val (![(2 : ℤ), 5, 2] w)
  · exact sum_congr rfl fun w _ => congrArg (monomial w.val) (h w)
  norm_num [Fin.sum_univ_succ, ← C_mul_X_pow_eq_monomial]
  ring

theorem μ_P3 : μ P3 = 1 + 3 * X + X^2 := by
  have hcoeff : catalogCoeffs pathBlocks = [1, 3, 1] := by decide +kernel
  have h : ∀ w : Fin 3, computeCatalog pathBlocks w = ![(1 : ℤ), 3, 1] w := by
    intro w
    have hw := congrArg (fun l : List ℤ => l[w.val]?) hcoeff
    exact Option.some.inj ((catalogCoeffs_get (n := 3) pathBlocks w).symm.trans
      (hw.trans (by fin_cases w <;> rfl)))
  rw [μ_catalog P3 P3_connected pathBlocks pathBlocks_spec]
  trans ∑ w : Fin 3, monomial w.val (![(1 : ℤ), 3, 1] w)
  · exact sum_congr rfl fun w _ => congrArg (monomial w.val) (h w)
  norm_num [Fin.sum_univ_succ, ← C_mul_X_pow_eq_monomial]
  ring

private def cycleBlocks : Finset (Finset (Fin 5)) :=
  {{0}, {1}, {2}, {3}, {4},
   {0, 1}, {1, 2}, {2, 3}, {3, 4}, {0, 4},
   {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {0, 3, 4}, {0, 1, 4},
   {0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4},
   {0, 1, 2, 3, 4}}

private def houseBlocks : Finset (Finset (Fin 5)) :=
  insert {1, 4} (insert {1, 2, 4} (insert {1, 3, 4} cycleBlocks))

private theorem cycleBlocks_spec (B : Finset (Fin 5)) :
    (C5.induce (B : Set (Fin 5))).Connected ↔ B ∈ cycleBlocks := by
  fin_cases B <;> decide +kernel

private theorem houseBlocks_spec (B : Finset (Fin 5)) :
    (House.induce (B : Set (Fin 5))).Connected ↔ B ∈ houseBlocks := by
  fin_cases B <;> decide +kernel

set_option Elab.async false in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem μ_House : μ House = 6 + 49 * X + 92 * X^2 + 49 * X^3 + 6 * X^4 := by
  have hcoeff : catalogCoeffs houseBlocks = [6, 49, 92, 49, 6] := by decide +kernel
  have h : ∀ w : Fin 5, computeCatalog houseBlocks w = ![(6 : ℤ), 49, 92, 49, 6] w := by
    intro w
    have hw := congrArg (fun l : List ℤ => l[w.val]?) hcoeff
    exact Option.some.inj ((catalogCoeffs_get (n := 5) houseBlocks w).symm.trans
      (hw.trans (by fin_cases w <;> rfl)))
  rw [μ_catalog House House_connected houseBlocks houseBlocks_spec]
  trans ∑ w : Fin 5, monomial w.val (![(6 : ℤ), 49, 92, 49, 6] w)
  · exact sum_congr rfl fun w _ => congrArg (monomial w.val) (h w)
  norm_num [Fin.sum_univ_succ, ← C_mul_X_pow_eq_monomial]
  ring

set_option Elab.async false in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem μ_C5 : μ C5 = 4 + 34 * X + 64 * X^2 + 34 * X^3 + 4 * X^4 := by
  have hcoeff : catalogCoeffs cycleBlocks = [4, 34, 64, 34, 4] := by decide +kernel
  have h : ∀ w : Fin 5, computeCatalog cycleBlocks w = ![(4 : ℤ), 34, 64, 34, 4] w := by
    intro w
    have hw := congrArg (fun l : List ℤ => l[w.val]?) hcoeff
    exact Option.some.inj ((catalogCoeffs_get (n := 5) cycleBlocks w).symm.trans
      (hw.trans (by fin_cases w <;> rfl)))
  rw [μ_catalog C5 C5_connected cycleBlocks cycleBlocks_spec]
  trans ∑ w : Fin 5, monomial w.val (![(4 : ℤ), 34, 64, 34, 4] w)
  · exact sum_congr rfl fun w _ => congrArg (monomial w.val) (h w)
  norm_num [Fin.sum_univ_succ, ← C_mul_X_pow_eq_monomial]
  ring

def G : SimpleGraph (Fin 3 ⊕ Fin 5) := K3.sum House
def H : SimpleGraph (Fin 3 ⊕ Fin 5) := P3.sum C5

theorem H_le_G : H ≤ G := by
  rintro (u | u) (v | v) h
  · exact (show P3 ≤ K3 from le_top) h
  · exact h
  · exact h
  · exact (show C5 ≤ House from le_sup_left) h

private def sumComponents (J : SimpleGraph V) (K : SimpleGraph W) :
    (J.sum K).ConnectedComponent ≃ J.ConnectedComponent ⊕ K.ConnectedComponent where
  toFun := Quot.lift (Sum.map J.connectedComponentMk K.connectedComponentMk) (by
    intro u v h
    rw [reachable_eq_reflTransGen] at h
    induction h with
    | refl => rfl
    | @tail x y _ hxy ih =>
      refine ih.trans ?_
      cases x <;> cases y
      · exact congrArg (Sum.inl : J.ConnectedComponent → _)
          (ConnectedComponent.sound (sum_adj_inl.mp hxy).reachable)
      · exact (not_adj_sum_inl_inr _ _ hxy).elim
      · exact (not_adj_sum_inl_inr _ _ hxy.symm).elim
      · exact congrArg (Sum.inr : K.ConnectedComponent → _)
          (ConnectedComponent.sound (sum_adj_inr.mp hxy).reachable))
  invFun := Sum.elim (fun c => c.map Embedding.sumInl.toHom)
    (fun c => c.map Embedding.sumInr.toHom)
  left_inv := by rintro ⟨v | w⟩ <;> rfl
  right_inv := by
    rintro (c | c)
    · exact c.ind fun _ => rfl
    · exact c.ind fun _ => rfl

omit [DecidableEq V] in
private theorem component_card_connected {J : SimpleGraph V} (hJ : J.Connected) :
    Nat.card J.ConnectedComponent = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨?_⟩, hJ.nonempty.map J.connectedComponentMk⟩
  rintro ⟨v⟩ ⟨w⟩
  exact ConnectedComponent.sound (hJ.preconnected v w)

omit [DecidableEq V] [DecidableEq W] in
private theorem component_card_sum [Finite V] [Finite W] (J : SimpleGraph V) (K : SimpleGraph W) :
    Nat.card (J.sum K).ConnectedComponent =
      Nat.card J.ConnectedComponent + Nat.card K.ConnectedComponent := by
  let : Finite J.ConnectedComponent := Quot.finite _
  let : Finite K.ConnectedComponent := Quot.finite _
  rw [Nat.card_congr (sumComponents J K), Nat.card_sum]

theorem G_components : Nat.card G.ConnectedComponent = 2 := by
  rw [G, component_card_sum, component_card_connected K3_connected,
    component_card_connected House_connected]

theorem H_components : Nat.card H.ConnectedComponent = 2 := by
  rw [H, component_card_sum, component_card_connected P3_connected,
    component_card_connected C5_connected]

omit [DecidableEq V] in
private theorem WPi.eq_bot_of_edgeless [Fintype V] (a : WPi (⊥ : SimpleGraph V)) : a = ⊥ := by
  have single (B : WeightedBlock V) (hB : B ∈ a.blocks) (v : V) (hv : v ∈ B.1) :
      B = WPi.singletonBlock v := by
    have hset : B.1 = {v} := by
      apply Subset.antisymm _ (singleton_subset_iff.mpr hv)
      intro w hw
      apply mem_singleton.mpr
      exact reachable_bot.mp (((a.connected B hB).preconnected ⟨w, hw⟩ ⟨v, hv⟩).map
        (Embedding.induce (B.1 : Set V)).toHom)
    have hwt := a.weight_lt B hB
    rw [hset, card_singleton] at hwt
    exact Prod.ext hset (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hwt))
  apply WPi.ext
  rw [WPi.bot_blocks]
  ext B
  constructor
  · intro hB
    obtain ⟨v, hv⟩ := WPi.nonempty_block hB
    exact mem_map.mpr ⟨v, mem_univ _, (single B hB v hv).symm⟩
  · intro hB
    obtain ⟨v, _, rfl⟩ := mem_map.mp hB
    obtain ⟨A, hA, hv⟩ := a.cover v
    exact single A hA v hv ▸ hA

theorem μ_edgeless [Fintype V] : μ (⊥ : SimpleGraph V) = 1 := by
  classical
  have hmax : (univ : Finset (WPi (⊥ : SimpleGraph V))).filter IsMax = {⊥} := by
    ext a
    have h : IsMax a := fun b _ => by
      rw [WPi.eq_bot_of_edgeless a, WPi.eq_bot_of_edgeless b]
    exact ⟨fun _ => mem_singleton.mpr (WPi.eq_bot_of_edgeless a),
      fun _ => mem_filter.mpr ⟨mem_univ _, h⟩⟩
  rw [μ, hmax, sum_singleton, IncidenceAlgebra.mu_self]
  simp [WPi.weight, sum_map, monomial_zero_left]

private def edgelessComponents (V : Type*) :
    (⊥ : SimpleGraph V).ConnectedComponent ≃ V where
  toFun := Quot.lift id fun _ _ h => reachable_bot.mp h
  invFun := (⊥ : SimpleGraph V).connectedComponentMk
  left_inv := by rintro ⟨v⟩; rfl
  right_inv := fun _ => rfl

/-- Add `r` isolated vertices to each graph of the counterexample. -/
def GWithIsolates (r : ℕ) : SimpleGraph ((Fin 3 ⊕ Fin 5) ⊕ Fin r) := G.sum ⊥

def HWithIsolates (r : ℕ) : SimpleGraph ((Fin 3 ⊕ Fin 5) ⊕ Fin r) := H.sum ⊥

theorem HWithIsolates_le_GWithIsolates (r : ℕ) : HWithIsolates r ≤ GWithIsolates r := by
  rintro (u | u) (v | v) huv
  · exact H_le_G huv
  · exact huv
  · exact huv
  · exact huv

theorem GWithIsolates_components (r : ℕ) :
    Nat.card (GWithIsolates r).ConnectedComponent = 2 + r := by
  rw [GWithIsolates, component_card_sum, G_components, Nat.card_congr (edgelessComponents _)]
  simp

theorem HWithIsolates_components (r : ℕ) :
    Nat.card (HWithIsolates r).ConnectedComponent = 2 + r := by
  rw [HWithIsolates, component_card_sum, H_components, Nat.card_congr (edgelessComponents _)]
  simp

/-- The signed Möbius polynomial difference for the eight-vertex pair. -/
noncomputable def P : Polynomial ℤ :=
  8 + 82 * X + 271 * X^2 + 396 * X^3 + 271 * X^4 + 82 * X^5 + 8 * X^6

private def Q : Cubic ℝ := ⟨8, 82, 247, 232⟩

private theorem Q_nonreal_root :
    ∃ s : ℂ, s.im ≠ 0 ∧ 8 * s^3 + 82 * s^2 + 247 * s + 232 = 0 := by
  classical
  let f := Complex.ofRealHom
  have ha : Q.a ≠ 0 := by norm_num [Q]
  obtain ⟨x, y, z, hr⟩ := (Cubic.splits_iff_roots_eq_three (φ := f) ha).mp
    (IsAlgClosed.splits _)
  have hzero : (Q.map f).toPoly ≠ 0 := Cubic.ne_zero_of_a_ne_zero ((_root_.map_ne_zero f).mpr ha)
  have root (s : ℂ) (hs : s ∈ (Q.map f).roots) :
      8 * s^3 + 82 * s^2 + 247 * s + 232 = 0 := by
    have := (Cubic.mem_roots_iff hzero s).mp hs
    simpa [Q, Cubic.map, f] using this
  by_contra! h
  have hx : x.im = 0 := not_not.mp (fun hn => h x hn (root x (by simp [hr])))
  have hy : y.im = 0 := not_not.mp (fun hn => h y hn (root y (by simp [hr])))
  have hz : z.im = 0 := not_not.mp (fun hn => h z hn (root z (by simp [hr])))
  have real (s : ℂ) (hs : s.im = 0) : (s.re : ℂ) = s := by
    simpa [hs] using s.re_add_im
  have hd := Cubic.discr_eq_prod_three_roots ha hr
  change ((Q.discr : ℝ) : ℂ) =
    ((Q.a : ℂ) * (Q.a : ℂ) * (x - y) * (x - z) * (y - z)) ^ 2 at hd
  rw [← real x hx, ← real y hy, ← real z hz] at hd
  have hd' : Q.discr =
      (Q.a * Q.a * (x.re - y.re) * (x.re - z.re) * (y.re - z.re)) ^ 2 := by
    exact_mod_cast hd
  have hn : Q.discr = -22364 := by norm_num [Q, Cubic.discr]
  linarith [sq_nonneg (Q.a * Q.a * (x.re - y.re) * (x.re - z.re) * (y.re - z.re))]

theorem P_has_nonreal_root : ∃ z : ℂ, z.im ≠ 0 ∧ aeval z P = 0 := by
  obtain ⟨s, hs, hroot⟩ := Q_nonreal_root
  let q : Polynomial ℂ := C (1 : ℂ) * X^2 + C (-s) * X + C 1
  have hdeg : 0 < q.degree := by
    rw [show q.degree = 2 from degree_quadratic (by norm_num)]
    decide
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have he : z^2 - s * z + 1 = 0 := by
    simpa [q, IsRoot, sub_eq_add_neg] using hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num at he
  have hzs : z + z⁻¹ = s := by
    apply (mul_right_cancel₀ hz0)
    calc
      (z + z⁻¹) * z = z^2 + 1 := by rw [add_mul, inv_mul_cancel₀ hz0, pow_two]
      _ = s * z := by linear_combination he
  refine ⟨z, ?_, ?_⟩
  · intro h
    have hreal : (z.re : ℂ) = z := by simpa [h] using z.re_add_im
    apply hs
    rw [← hzs, ← hreal, ← Complex.ofReal_inv, ← Complex.ofReal_add, Complex.ofReal_im]
  · have hrec : z^3 * (8 * (z + z⁻¹)^3 + 82 * (z + z⁻¹)^2 +
        247 * (z + z⁻¹) + 232) = aeval z P := by
      simp only [P, map_add, map_mul, map_pow, aeval_X, map_ofNat]
      field_simp
      ring
    rw [← hrec, hzs, hroot, mul_zero]

/-- Mathlib 4.33 uses `Splits` for splitting over the coefficient field itself. -/
theorem P_not_splits : ¬ (P.map (Int.castRingHom ℝ)).Splits := by
  intro hr
  obtain ⟨z, hz, hPz⟩ := P_has_nonreal_root
  have hP0 : P.map (Int.castRingHom ℝ) ≠ 0 := by
    intro h
    have h' := congrArg (fun p : Polynomial ℝ => p.eval 0) h
    norm_num [P, Polynomial.eval_map] at h'
  have hroot : ((P.map (Int.castRingHom ℝ)).map Complex.ofRealHom).IsRoot z := by
    rw [Polynomial.map_map, show Complex.ofRealHom.comp (Int.castRingHom ℝ) =
      algebraMap ℤ ℂ from Subsingleton.elim _ _, IsRoot, eval_map_algebraMap]
    exact hPz
  obtain ⟨r, rfl⟩ := hr.mem_range_of_isRoot hP0 hroot
  exact hz (Complex.ofReal_im r)

theorem signed_μ_difference :
    C ((-1 : ℤ) ^ (8 - 2 : ℕ)) * (μ G - μ H) = P := by
  rw [G, H, μ_sum, μ_sum, μ_K3, μ_House, μ_P3, μ_C5]
  norm_num [P]
  ring

theorem signed_μ_difference_with_isolates (r : ℕ) :
    C ((-1 : ℤ) ^ ((8 + r) - (2 + r))) * (μ (GWithIsolates r) - μ (HWithIsolates r)) = P := by
  have h : (8 + r) - (2 + r) = (8 - 2 : ℕ) := by omega
  rw [GWithIsolates, HWithIsolates, μ_sum, μ_sum, μ_edgeless, mul_one, mul_one, h]
  exact signed_μ_difference

/-- The eight-vertex spanning counterexample to Conjecture 4.13(2). -/
theorem conjecture_4_13_2_counterexample :
    Fintype.card (Fin 3 ⊕ Fin 5) = 8 ∧ H ≤ G ∧
    Nat.card G.ConnectedComponent = 2 ∧ Nat.card H.ConnectedComponent = 2 ∧
    C ((-1 : ℤ) ^ (8 - 2 : ℕ)) * (μ G - μ H) = P ∧
    ¬ (P.map (Int.castRingHom ℝ)).Splits ∧
    (∃ z : ℂ, z.im ≠ 0 ∧ aeval z P = 0) :=
  ⟨by simp, H_le_G, G_components, H_components, signed_μ_difference,
    P_not_splits, P_has_nonreal_root⟩

/-- Adding any number of isolated vertices gives the same signed difference. -/
theorem conjecture_4_13_2_infinite_family (r : ℕ) :
    Fintype.card ((Fin 3 ⊕ Fin 5) ⊕ Fin r) = 8 + r ∧
    HWithIsolates r ≤ GWithIsolates r ∧
    Nat.card (GWithIsolates r).ConnectedComponent = 2 + r ∧
    Nat.card (HWithIsolates r).ConnectedComponent = 2 + r ∧
    C ((-1 : ℤ) ^ ((8 + r) - (2 + r))) * (μ (GWithIsolates r) - μ (HWithIsolates r)) = P ∧
    ¬ (P.map (Int.castRingHom ℝ)).Splits ∧
    (∃ z : ℂ, z.im ≠ 0 ∧ aeval z P = 0) :=
  ⟨by simp, HWithIsolates_le_GWithIsolates r, GWithIsolates_components r,
    HWithIsolates_components r, signed_μ_difference_with_isolates r, P_not_splits,
    P_has_nonreal_root⟩

#print axioms conjecture_4_13_2_counterexample
#print axioms conjecture_4_13_2_infinite_family

end WachsWeightedBond
