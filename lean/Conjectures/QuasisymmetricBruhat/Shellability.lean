import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic

/-!
# Shellability of bounded posets (Section 6.1)

For a bounded poset `P` with `0̂, 1̂`, shellability means shellability of the order complex of
the proper part `P ∖ {0̂, 1̂}`: an ordering `C₁, …, C_t` of all maximal chains such that for every
`j > 1` the intersection of `C_j` with `⋃_{i<j} C_i` is pure of codimension one in `C_j`.

* `fact61_left` / `fact61_right` (Fact 6.1, [Wachs, Cor. 3.1.9]): a shelling of `(a, b)`
  restricts to a shelling of `(x, b)` (resp. `(a, y)`), via the link of the face
  `c₀ ∪ {x}` for a maximal chain `c₀` of `(a, x)`.
* `not_shellable_of_split`: a shelling of a complex whose facets have at least two vertices
  cannot have its facets split into two nonempty vertex-disjoint classes; in particular a
  shellable pure one-dimensional complex is connected.
-/

namespace QuasisymmetricBruhat

section Shell

variable {α : Type*} (le : α → α → Prop)

/-- A finite chain contained in `P`. -/
def IsChainIn (P : Set α) (C : Finset α) : Prop :=
  (∀ a ∈ C, a ∈ P) ∧ ∀ a ∈ C, ∀ b ∈ C, le a b ∨ le b a

/-- A maximal chain of `P`. -/
def IsMaxChainIn (P : Set α) (C : Finset α) : Prop :=
  IsChainIn le P C ∧ ∀ D, IsChainIn le P D → C ⊆ D → D ⊆ C

/-- The open interval `(a, b)`. -/
def openInt (a b : α) : Set α := {w | le a w ∧ w ≠ a ∧ le w b ∧ w ≠ b}

/-- `C ∩ ⋃ prev` is pure of codimension one in `C`: every face of `C` lying in an earlier
facet extends to a codimension-one face of `C` lying in an earlier facet. -/
def PureCodimOne (C : Finset α) (prev : List (Finset α)) : Prop :=
  ∀ σ, σ ⊆ C → (∃ D ∈ prev, σ ⊆ D) →
    ∃ τ, σ ⊆ τ ∧ τ ⊆ C ∧ τ.card + 1 = C.card ∧ ∃ D ∈ prev, τ ⊆ D

/-- A shelling order of facets `C₁, C₂, …` (the list order). -/
def IsShellingOrder (l : List (Finset α)) : Prop :=
  ∀ pre C post, l = pre ++ C :: post → pre ≠ [] → PureCodimOne C pre

/-- The order complex of `Q` (maximal chains as facets) is shellable. -/
def ShellableProper (Q : Set α) : Prop :=
  ∃ l : List (Finset α), l.Nodup ∧ (∀ C, C ∈ l ↔ IsMaxChainIn le Q C) ∧ IsShellingOrder l

/-- A bounded poset `P` is shellable: it has a least element `0̂` and a greatest element `1̂`,
and the order complex of the proper part `P ∖ {0̂, 1̂}` is shellable. -/
def IsShellable (P : Set α) : Prop :=
  ∃ bot ∈ P, ∃ top ∈ P, (∀ p ∈ P, le bot p ∧ le p top) ∧ ShellableProper le (P \ {bot, top})

/-- `le` is a partial order. -/
structure IsPartialOrderRel : Prop where
  refl : ∀ a, le a a
  trans : ∀ a b c, le a b → le b c → le a c
  antisymm : ∀ a b, le a b → le b a → a = b

end Shell

/-! ### List lemmas -/

lemma filterMap_eq_append_cons {β γ : Type*} (f : β → Option γ) :
    ∀ (l : List β) (pre' : List γ) (c : γ) (post' : List γ), l.filterMap f = pre' ++ c :: post' →
      ∃ pre b post, l = pre ++ b :: post ∧ f b = some c ∧ pre.filterMap f = pre' := by
  intro l
  induction l with
  | nil => intro pre' c post' h; simp at h
  | cons b l ih =>
    intro pre' c post' h
    cases hfb : f b with
    | none =>
      rw [List.filterMap_cons, hfb] at h
      obtain ⟨pre, b', post, rfl, h1, h2⟩ := ih pre' c post' h
      exact ⟨b :: pre, b', post, rfl, h1, by rw [List.filterMap_cons, hfb]; exact h2⟩
    | some d =>
      rw [List.filterMap_cons, hfb] at h
      cases pre' with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        exact ⟨[], b, l, rfl, by rw [hfb, h.1], rfl⟩
      | cons p pre'' =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨pre, b', post, rfl, h1, h2⟩ := ih pre'' c post' h.2
        exact ⟨b :: pre, b', post, rfl, h1, by rw [List.filterMap_cons, hfb, h2, h.1]⟩

lemma exists_first {β : Type*} (q : β → Prop) [DecidablePred q] :
    ∀ l : List β, (∃ c ∈ l, ¬ q c) → ∃ pre c post, l = pre ++ c :: post ∧ ¬ q c ∧ ∀ d ∈ pre, q d := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons b l ih =>
    intro h
    by_cases hb : q b
    · obtain ⟨c, hc, hqc⟩ := h
      rcases List.mem_cons.1 hc with rfl | hc
      · exact absurd hb hqc
      · obtain ⟨pre, c', post, rfl, h1, h2⟩ := ih ⟨c, hc, hqc⟩
        refine ⟨b :: pre, c', post, rfl, h1, fun d hd => ?_⟩
        rcases List.mem_cons.1 hd with rfl | hd
        · exact hb
        · exact h2 d hd
    · exact ⟨[], b, l, rfl, hb, fun d hd => by simp at hd⟩

section Fact61

variable {α : Type*} [DecidableEq α] {le : α → α → Prop} (hpo : IsPartialOrderRel le)
  {a x b : α} {c0 : Finset α} (hc0 : IsMaxChainIn le (openInt le a x) c0)
  (hax : le a x) (hxa : x ≠ a) (hxb : le x b) (hbx : x ≠ b)
include hpo hc0 hax hxa hxb hbx

omit [DecidableEq α] hax hxa in
lemma c0_in_ab {w : α} (hw : w ∈ c0) : w ∈ openInt le a b := by
  obtain ⟨h1, h2, h3, h4⟩ := hc0.1.1 _ hw
  refine ⟨h1, h2, hpo.trans _ _ _ h3 hxb, fun hwb => ?_⟩
  subst hwb; exact hbx (hpo.antisymm _ _ hxb h3)

/-- Lifting a chain of `(x, b)` by the face `c₀ ∪ {x}`. -/
lemma chain_lift {E : Finset α} (hE : IsChainIn le (openInt le x b) E) :
    IsChainIn le (openInt le a b) (insert x c0 ∪ E) := by
  constructor
  · intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · exact ⟨hax, hxa, hxb, hbx⟩
      · exact c0_in_ab hpo hc0 hxb hbx hw
    · obtain ⟨h1, h2, h3, h4⟩ := hE.1 w hw
      refine ⟨hpo.trans _ _ _ hax h1, fun hwa => ?_, h3, h4⟩
      subst hwa; exact hxa (hpo.antisymm _ _ h1 hax)
  · have below : ∀ w ∈ insert x c0, le w x := fun w hw => by
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hpo.refl _
      · exact (hc0.1.1 _ hw).2.2.1
    intro u hu v hv
    rcases Finset.mem_union.1 hu with hu | hu <;> rcases Finset.mem_union.1 hv with hv | hv
    · by_cases hux : u = x
      · rw [hux]; exact Or.inr (below v hv)
      · by_cases hvx : v = x
        · rw [hvx]; exact Or.inl (below u hu)
        · exact hc0.1.2 u (Finset.mem_of_mem_insert_of_ne hu hux) v
            (Finset.mem_of_mem_insert_of_ne hv hvx)
    · exact Or.inl (hpo.trans _ _ _ (below u hu) (hE.1 v hv).1)
    · exact Or.inr (hpo.trans _ _ _ (below v hv) (hE.1 u hu).1)
    · exact hE.2 u hu v hv

lemma not_mem_face {E : Finset α} (hE : IsChainIn le (openInt le x b) E) {w : α} (hw : w ∈ E) :
    w ∉ insert x c0 := by
  intro h
  obtain ⟨h1, h2, -, -⟩ := hE.1 w hw
  rcases Finset.mem_insert.1 h with rfl | h
  · exact h2 rfl
  · exact h2 (hpo.antisymm _ _ (hc0.1.1 _ h).2.2.1 h1)

omit hax hxa hxb hbx in
/-- An element of `(a, b)` comparable with `x` and with all of `c₀` lies in `c₀ ∪ {x}` or
above `x`. -/
lemma above_or_face {w : α} (hw : w ∈ openInt le a b) (hcx : le w x ∨ le x w)
    (hcc : ∀ u ∈ c0, le u w ∨ le w u) : w ∈ insert x c0 ∨ (le x w ∧ w ≠ x) := by
  by_cases hwx : w = x
  · exact Or.inl (hwx ▸ Finset.mem_insert_self _ _)
  rcases hcx with h | h
  · left
    apply Finset.mem_insert_of_mem
    have hch : IsChainIn le (openInt le a x) (insert w c0) := by
      constructor
      · intro u hu
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact ⟨hw.1, hw.2.1, h, hwx⟩
        · exact hc0.1.1 u hu
      · intro u hu v hv
        by_cases huw : u = w
        · rw [huw]
          by_cases hvw : v = w
          · rw [hvw]; exact Or.inl (hpo.refl _)
          · exact (hcc v (Finset.mem_of_mem_insert_of_ne hv hvw)).symm
        · have hu' := Finset.mem_of_mem_insert_of_ne hu huw
          by_cases hvw : v = w
          · rw [hvw]; exact hcc u hu'
          · exact hc0.1.2 u hu' v (Finset.mem_of_mem_insert_of_ne hv hvw)
    exact hc0.2 _ hch (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)
  · exact Or.inr ⟨h, hwx⟩

lemma maxchain_lift {D : Finset α} (hD : IsMaxChainIn le (openInt le x b) D) :
    IsMaxChainIn le (openInt le a b) (insert x c0 ∪ D) := by
  refine ⟨chain_lift hpo hc0 hax hxa hxb hbx hD.1, fun E hE hsub w hw => ?_⟩
  have hxE : x ∈ E := hsub (Finset.mem_union_left _ (Finset.mem_insert_self _ _))
  have hcc : ∀ u ∈ c0, le u w ∨ le w u := fun u hu =>
    hE.2 u (hsub (Finset.mem_union_left _ (Finset.mem_insert_of_mem hu))) w hw
  rcases above_or_face hpo hc0 (hE.1 w hw) (hE.2 w hw x hxE) hcc with h | ⟨h1, h2⟩
  · exact Finset.mem_union_left _ h
  · apply Finset.mem_union_right
    have hch : IsChainIn le (openInt le x b) (insert w D) := by
      constructor
      · intro u hu
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact ⟨h1, h2, (hE.1 u hw).2.2.1, (hE.1 u hw).2.2.2⟩
        · exact hD.1.1 u hu
      · intro u hu v hv
        have hu' : u ∈ E := by
          rcases Finset.mem_insert.1 hu with rfl | hu
          · exact hw
          · exact hsub (Finset.mem_union_right _ hu)
        have hv' : v ∈ E := by
          rcases Finset.mem_insert.1 hv with rfl | hv
          · exact hw
          · exact hsub (Finset.mem_union_right _ hv)
        exact hE.2 u hu' v hv'
    exact hD.2 _ hch (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)

lemma maxchain_restrict {C : Finset α} (hC : IsMaxChainIn le (openInt le a b) C)
    (hσ : insert x c0 ⊆ C) : IsMaxChainIn le (openInt le x b) (C \ insert x c0) := by
  have hxC : x ∈ C := hσ (Finset.mem_insert_self _ _)
  have hchain : IsChainIn le (openInt le x b) (C \ insert x c0) := by
    constructor
    · intro w hw
      obtain ⟨hwC, hwσ⟩ := Finset.mem_sdiff.1 hw
      have hcc : ∀ u ∈ c0, le u w ∨ le w u := fun u hu =>
        hC.1.2 u (hσ (Finset.mem_insert_of_mem hu)) w hwC
      rcases above_or_face hpo hc0 (hC.1.1 w hwC) (hC.1.2 w hwC x hxC) hcc with
        h | ⟨h1, h2⟩
      · exact absurd h hwσ
      · exact ⟨h1, h2, (hC.1.1 w hwC).2.2.1, (hC.1.1 w hwC).2.2.2⟩
    · intro u hu v hv
      exact hC.1.2 u (Finset.mem_sdiff.1 hu).1 v (Finset.mem_sdiff.1 hv).1
  refine ⟨hchain, fun E hE hsub w hw => ?_⟩
  have hlift := chain_lift hpo hc0 hax hxa hxb hbx hE
  have hCsub : C ⊆ insert x c0 ∪ E := by
    intro u hu
    by_cases h : u ∈ insert x c0
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (hsub (Finset.mem_sdiff.2 ⟨hu, h⟩))
  have := hC.2 _ hlift hCsub (Finset.mem_union_right _ hw)
  exact Finset.mem_sdiff.2 ⟨this, not_mem_face hpo hc0 hax hxa hxb hbx hE hw⟩

/-- Fact 6.1 (left end): a shelling of `(a, b)` restricts to a shelling of `(x, b)`. -/
theorem fact61_left (hS : ShellableProper le (openInt le a b)) :
    ShellableProper le (openInt le x b) := by
  classical
  obtain ⟨l, hnd, hmem, hsh⟩ := hS
  set σ := insert x c0
  let f : Finset α → Option (Finset α) := fun C => if σ ⊆ C then some (C \ σ) else none
  refine ⟨l.filterMap f, ?_, ?_, ?_⟩
  · apply hnd.filterMap
    intro C C' D hC hC'
    simp only [f, Option.mem_def] at hC hC'
    split_ifs at hC hC' with h1 h2
    simp only [Option.some.injEq] at hC hC'
    rw [← Finset.sdiff_union_of_subset h1, ← Finset.sdiff_union_of_subset h2, hC, hC']
  · intro D
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨C, hCl, hfC⟩
      simp only [f] at hfC
      split_ifs at hfC with h
      simp only [Option.some.injEq] at hfC
      subst hfC
      exact maxchain_restrict hpo hc0 hax hxa hxb hbx ((hmem C).1 hCl) h
    · intro hD
      refine ⟨σ ∪ D, (hmem _).2 (maxchain_lift hpo hc0 hax hxa hxb hbx hD), ?_⟩
      simp only [f, Finset.subset_union_left, if_true, Option.some.injEq]
      ext w
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact absurd h h'
        · exact h
      · intro h; exact ⟨Or.inr h, not_mem_face hpo hc0 hax hxa hxb hbx hD.1 h⟩
  · intro pre' D post' hl' hpre'
    obtain ⟨pre, C, post, rfl, hfC, hpre⟩ := filterMap_eq_append_cons f l pre' D post' hl'
    simp only [f] at hfC
    split_ifs at hfC with hσC
    simp only [Option.some.injEq] at hfC
    subst hfC
    have hpre_ne : pre ≠ [] := by rintro rfl; exact hpre' (by rw [← hpre]; rfl)
    have hPC := hsh pre C post rfl hpre_ne
    intro σ' hσ'D ⟨D', hD'pre, hσ'D'⟩
    rw [← hpre, List.mem_filterMap] at hD'pre
    obtain ⟨C', hC'pre, hfC'⟩ := hD'pre
    simp only [f] at hfC'
    split_ifs at hfC' with hσC'
    simp only [Option.some.injEq] at hfC'
    subst hfC'
    have hσ'C : σ' ⊆ C := fun w hw => (Finset.mem_sdiff.1 (hσ'D hw)).1
    have hσ'σ : Disjoint σ' σ := Finset.disjoint_left.2 fun w hw => (Finset.mem_sdiff.1 (hσ'D hw)).2
    obtain ⟨τ, h1, h2, h3, C'', hC''pre, h4⟩ := hPC (σ' ∪ σ) (Finset.union_subset hσ'C hσC)
      ⟨C', hC'pre, Finset.union_subset (fun w hw => (Finset.mem_sdiff.1 (hσ'D' hw)).1) hσC'⟩
    have hστ : σ ⊆ τ := fun w hw => h1 (Finset.mem_union_right _ hw)
    have hσC'' : σ ⊆ C'' := hστ.trans h4
    refine ⟨τ \ σ, fun w hw => Finset.mem_sdiff.2 ⟨h1 (Finset.mem_union_left _ hw),
      Finset.disjoint_left.1 hσ'σ hw⟩, Finset.sdiff_subset_sdiff h2 le_rfl, ?_,
      C'' \ σ, ?_, Finset.sdiff_subset_sdiff h4 le_rfl⟩
    · rw [Finset.card_sdiff_of_subset hστ, Finset.card_sdiff_of_subset hσC]
      have := Finset.card_le_card hστ; omega
    · rw [← hpre, List.mem_filterMap]
      exact ⟨C'', hC''pre, by simp only [f, hσC'', if_true]⟩

end Fact61

section Dual

variable {α : Type*} {le : α → α → Prop}

lemma isChainIn_flip {P : Set α} {C : Finset α} :
    IsChainIn (flip le) P C ↔ IsChainIn le P C := by
  unfold IsChainIn flip
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, fun a ha b hb => (h2 a ha b hb).symm⟩

lemma isMaxChainIn_flip {P : Set α} {C : Finset α} :
    IsMaxChainIn (flip le) P C ↔ IsMaxChainIn le P C := by
  unfold IsMaxChainIn; simp only [isChainIn_flip]

lemma openInt_flip (a b : α) : openInt (flip le) b a = openInt le a b := by
  ext w; constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h3, h4, h1, h2⟩

lemma shellableProper_flip {Q : Set α} : ShellableProper (flip le) Q ↔ ShellableProper le Q := by
  unfold ShellableProper; simp only [isMaxChainIn_flip]

lemma IsPartialOrderRel.flip (hpo : IsPartialOrderRel le) : IsPartialOrderRel (flip le) :=
  ⟨fun a => hpo.refl a, fun _ _ _ h1 h2 => hpo.trans _ _ _ h2 h1,
    fun _ _ h1 h2 => hpo.antisymm _ _ h2 h1⟩

/-- Fact 6.1 (right end): a shelling of `(a, b)` restricts to a shelling of `(a, y)`. -/
theorem fact61_right [DecidableEq α] (hpo : IsPartialOrderRel le) {a y b : α} {c1 : Finset α}
    (hc1 : IsMaxChainIn le (openInt le y b) c1) (hay : le a y) (hya : y ≠ a) (hyb : le y b)
    (hby : y ≠ b) (hS : ShellableProper le (openInt le a b)) :
    ShellableProper le (openInt le a y) := by
  rw [← shellableProper_flip, ← openInt_flip]
  refine fact61_left hpo.flip (a := b) (x := y) (b := a) (c0 := c1) ?_ hyb hby hay hya ?_
  · rw [openInt_flip, isMaxChainIn_flip]; exact hc1
  · rw [openInt_flip, shellableProper_flip]; exact hS

end Dual

section Split

variable {α : Type*} {le : α → α → Prop}

/-- If the facets split into two nonempty classes with vertex-disjoint members, and every facet
has at least two vertices, there is no shelling.  For a pure one-dimensional complex this says
that a shellable graph is connected. -/
theorem not_shellable_of_split {Q : Set α} (hS : ShellableProper le Q)
    (hcard : ∀ C, IsMaxChainIn le Q C → 2 ≤ C.card) (p : Finset α → Prop)
    (h1 : ∃ C, IsMaxChainIn le Q C ∧ p C) (h2 : ∃ C, IsMaxChainIn le Q C ∧ ¬ p C)
    (hdisj : ∀ C D, IsMaxChainIn le Q C → IsMaxChainIn le Q D → p C → ¬ p D → Disjoint C D) :
    False := by
  classical
  obtain ⟨l, -, hmem, hsh⟩ := hS
  obtain ⟨C₁, hC₁, -⟩ := id h1
  cases l with
  | nil => exact absurd ((hmem C₁).2 hC₁) (by simp)
  | cons H l =>
    let q : Finset α → Prop := fun C => (p C ↔ p H)
    have hex : ∃ c ∈ H :: l, ¬ q c := by
      by_cases hpH : p H
      · obtain ⟨C, hC, hpC⟩ := h2
        exact ⟨C, (hmem C).2 hC, fun h => hpC (h.2 hpH)⟩
      · obtain ⟨C, hC, hpC⟩ := h1
        exact ⟨C, (hmem C).2 hC, fun h => hpH (h.1 hpC)⟩
    obtain ⟨pre, C, post, hl, hqC, hpre⟩ := exists_first q (H :: l) hex
    have hpre_ne : pre ≠ [] := by
      rintro rfl
      simp only [List.nil_append, List.cons.injEq] at hl
      exact hqC (hl.1 ▸ Iff.rfl)
    have hHpre : H ∈ pre := by
      cases pre with
      | nil => exact absurd rfl hpre_ne
      | cons p0 pre0 =>
        simp only [List.cons_append, List.cons.injEq] at hl
        rw [hl.1]; exact List.mem_cons_self
    obtain ⟨τ, -, hτC, hτcard, D, hDpre, hτD⟩ :=
      hsh pre C post hl hpre_ne ∅ (Finset.empty_subset _) ⟨H, hHpre, Finset.empty_subset _⟩
    have hCmax := (hmem C).1 (by rw [hl]; simp)
    have hDmax := (hmem D).1 (by rw [hl]; simp [hDpre])
    have hqD := hpre D hDpre
    have hdj : Disjoint C D := by
      by_cases hpC : p C
      · exact hdisj C D hCmax hDmax hpC (fun hpD => hqC ⟨fun _ => hqD.1 hpD, fun _ => hpC⟩)
      · have hpD : p D := by
          by_contra hpD
          exact hqC ⟨fun h => absurd h hpC, fun h => absurd (hqD.2 h) hpD⟩
        exact (hdisj D C hDmax hCmax hpD hpC).symm
    have : τ = ∅ := Finset.eq_empty_of_forall_notMem fun w hw =>
      Finset.disjoint_left.1 hdj (hτC hw) (hτD hw)
    have := hcard C hCmax
    subst_vars; simp at hτcard; omega

end Split

end QuasisymmetricBruhat
