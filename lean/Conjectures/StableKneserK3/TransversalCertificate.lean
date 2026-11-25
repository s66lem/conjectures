import Conjectures.StableKneserK3.Intersecting
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Preimage

namespace StableKneserK3.TransversalCertificate

open Finset

abbrev Point := Fin 10
abbrev TripleSet := Finset Point

def initial (n : ℕ) : TripleSet := univ.filter (fun x => x.val < n)

def fresh (n k : ℕ) : TripleSet := (initial (n+k)) \ initial n

private theorem initial_card (n : ℕ) (hn : n ≤ 10) : (initial n).card = n := by
  have he : initial n = (univ : Finset (Fin n)).map (Fin.castLEEmb hn) := by
    ext x
    simp only [initial, mem_filter, mem_univ, true_and, mem_map]
    exact ⟨fun h => ⟨⟨x.val,h⟩,rfl⟩, fun ⟨i,hi⟩ => hi ▸ i.isLt⟩
  simp [he]

private theorem initial_mono {a b : ℕ} (h : a ≤ b) : initial a ⊆ initial b := by
  intro x hx
  exact mem_filter.mpr ⟨mem_univ _,lt_of_lt_of_le (mem_filter.mp hx).2 h⟩

/-- A certificate uses the first available names for previously unseen vertices. -/
def Canonical (n : ℕ) (t : TripleSet) : Prop :=
  t \ initial n = fresh n (t \ initial n).card

instance (n) (t : TripleSet) : Decidable (Canonical n t) := by unfold Canonical; infer_instance

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem extend_labels (n : ℕ) (hn : n+3 ≤ 10) (f : Point ↪ V) (s : Finset V)
    (hs : s.card = 3) : ∃ (g : Point ↪ V) (t : TripleSet),
      (∀ a ∈ initial n, g a = f a) ∧ t.map g = s ∧ Canonical n t := by
  classical
  let I := initial n
  let U := I.map f
  let R := s \ U
  let k := R.card
  have hk : k ≤ 3 := (card_le_card sdiff_subset).trans hs.le
  let K := fresh n k
  have hK : K.card = R.card := by
    rw [show K = initial (n+k) \ I from rfl, card_sdiff_of_subset (initial_mono (by omega)),
      initial_card _ (by omega), show I.card = n from initial_card n (by omega)]
    omega
  let e := K.equivOfCardEq hK
  let D := I ∪ K
  let rep (a : D) : V :=
    if h : a.val ∈ K then (e ⟨a.val,h⟩).val else f a.val
  have hIK : Disjoint I K := disjoint_sdiff_self_right
  have repI (i : D) (hi : i.val ∈ I) : rep i = f i.val := by
    simp [rep, disjoint_left.mp hIK hi]
  have repK (i : D) (hi : i.val ∈ K) : rep i ∈ R := by simp [rep, hi]
  have inj : Function.Injective rep := by
    intro a b he
    by_cases ha : a.val ∈ K <;> by_cases hb : b.val ∈ K
    · simp only [rep, dif_pos ha, dif_pos hb] at he
      exact Subtype.ext (congrArg (fun z : K => z.val) (e.injective (Subtype.ext he)))
    · have hai := (mem_sdiff.mp (repK a ha)).2
      have hbi := (mem_union.mp b.property).resolve_right hb
      exact False.elim (hai (he ▸ (repI b hbi ▸ mem_map.mpr ⟨b.val,hbi,rfl⟩)))
    · have hbi := (mem_sdiff.mp (repK b hb)).2
      have hai := (mem_union.mp a.property).resolve_right ha
      exact False.elim (hbi (he ▸ (repI a hai ▸ mem_map.mpr ⟨a.val,hai,rfl⟩)))
    · simp only [rep, dif_neg ha, dif_neg hb] at he
      exact Subtype.ext (f.injective he)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair (fun a : D => f a.val) rep
    (f.injective.comp Subtype.val_injective) inj
  let g := f.trans σ.toEmbedding
  have hg (a : D) : g a.val = rep a := hσ a
  have hold (a) (ha : a ∈ I) : g a = f a :=
    (hg ⟨a,mem_union_left _ ha⟩).trans (repI _ ha)
  have hnew (a : K) : g a.val = (e a).val := by
    have h := hg ⟨a.val,mem_union_right _ a.property⟩
    simpa [rep,a.property] using h
  let A := s.preimage f f.injective.injOn ∩ I
  let t := A ∪ K
  refine ⟨g,t,hold,?_,?_⟩
  · ext v
    constructor
    · intro hv
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hv
      rcases mem_union.mp ha with ha | ha
      · rw [hold a (mem_inter.mp ha).2]
        exact mem_preimage.mp (mem_inter.mp ha).1
      · rw [hnew ⟨a,ha⟩]
        exact (mem_sdiff.mp (e ⟨a,ha⟩).property).1
    · intro hv
      by_cases hu : v ∈ U
      · obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
        exact mem_map.mpr ⟨a,mem_union_left _ (mem_inter.mpr ⟨mem_preimage.mpr hv,ha⟩),hold a ha⟩
      · let b : R := ⟨v,mem_sdiff.mpr ⟨hv,hu⟩⟩
        let a := e.symm b
        exact mem_map.mpr ⟨a.val,mem_union_right _ a.property,
          (hnew a).trans (congrArg Subtype.val (e.apply_symm_apply b))⟩
  · have he : t \ I = K := by
      ext a
      simp only [t, A, mem_sdiff, mem_union, mem_inter]
      by_cases h : a ∈ K
      · simp [h, disjoint_right.mp hIK h]
      · simp [h]
    change t \ I = fresh n (t \ I).card
    rw [he,hK]

/-- Canonical candidates compatible with the triples already selected, avoiding the specified pair. -/
def allowed (n : ℕ) (B : List TripleSet) (p : TripleSet) :=
  (univ.powersetCard 3).filter (fun t => Canonical n t ∧ Disjoint p t ∧ ∀ b ∈ B, ¬ Disjoint b t)

def Refutes (B : List TripleSet) : Prop :=
  ∀ (F : Finset (Finset V)) (f : Point ↪ V),
    (∀ t ∈ F, t.card = 3) → (F : Set (Finset V)).Intersecting → ¬ PairTransversal F →
    (∀ b ∈ B, b.map f ∈ F) → F.card ≤ 10

omit [Fintype V] in
theorem rename {B C : List TripleSet} (e : Point ↪ Point)
    (h : ∀ t ∈ B, t.map e ∈ C) (hr : Refutes (V := V) B) : Refutes (V := V) C := by
  intro F f hu hi hp hc
  apply hr F (e.trans f) hu hi hp
  intro t ht
  simpa only [map_map] using hc _ (h t ht)

omit [Fintype V] in
private theorem map_agree {f g : Point ↪ V} {s : TripleSet} (h : ∀ a ∈ s, f a = g a) :
    s.map f = s.map g := by
  simp only [map_eq_image]
  exact image_congr h

omit [Fintype V] in
private theorem normalize {n : ℕ} (hn : n+3 ≤ 10) {f : Point ↪ V} {s : Finset V}
    (hs : s.card = 3) {B : List TripleSet} {p : TripleSet}
    (hp : p ⊆ initial n) (hB : ∀ b ∈ B, b ⊆ initial n)
    (hd : Disjoint (p.map f) s) (hi : ∀ b ∈ B, ¬Disjoint (b.map f) s) :
    ∃ (g : Point ↪ V), ∃ t ∈ allowed n B p, t.map g = s ∧ ∀ a ∈ initial n, g a = f a := by
  obtain ⟨g,t,hg,hgs,hcanon⟩ := extend_labels n hn f s hs
  have same {u : TripleSet} (h : u ⊆ initial n) : u.map g = u.map f :=
    map_agree (fun a ha => hg a (h ha))
  refine ⟨g,t,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,?_⟩, hcanon,?_,?_⟩,hgs,hg⟩
  · rw [← hgs,card_map] at hs
    exact hs
  · apply (disjoint_map g).mp
    rwa [same hp,hgs]
  · intro b hb h
    have h' := (disjoint_map g).mpr h
    rw [same (hB b hb),hgs] at h'
    exact hi b hb h'

omit [Fintype V] in
theorem branch {B : List TripleSet} (n : ℕ) (hn : n+3 ≤ 10) (p : TripleSet)
    (hp : p = ∅ ∨ p.card = 2) (hpin : p ⊆ initial n) (hB : ∀ b ∈ B, b ⊆ initial n)
    (C : List TripleSet) (hC : ∀ t ∈ allowed n B p, t ∈ C)
    (next : ∀ t ∈ C, Refutes (V := V) (t :: B)) : Refutes (V := V) B := by
  intro F f hu hi ht hmem
  by_cases hF : F.Nonempty
  · have hw : ∃ s ∈ F, Disjoint (p.map f) s := by
      rcases hp with rfl | hp
      · obtain ⟨s,hs⟩ := hF
        exact ⟨s,hs,by simp⟩
      obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hp
      by_contra! h
      apply ht ⟨f x,f y,f.injective.ne hxy,?_⟩
      intro s hs
      obtain ⟨z,hz,hzs⟩ := not_disjoint_iff.mp (h s hs)
      simpa using (show ∃ z ∈ ({x,y} : TripleSet).map f, z ∈ s from ⟨z,hz,hzs⟩)
    obtain ⟨s,hs,hd⟩ := hw
    obtain ⟨g,t,ht',he,hg⟩ := normalize hn (hu s hs) hpin hB hd (fun b hb => hi (hmem b hb) hs)
    apply next t (hC t ht') F g hu hi ht
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · rwa [he]
    · rw [map_agree (fun a ha => hg a (hB b hb ha))]
      exact hmem b hb
  · simp [not_nonempty_iff_eq_empty.mp hF]

omit [Fintype V] in
theorem leaf {B : List TripleSet} (n : ℕ) (hn : n+3 ≤ 10) (hB : ∀ b ∈ B, b ⊆ initial n)
    (groups : List (List TripleSet)) (hlen : groups.length ≤ 10)
    (hgroups : ∀ t ∈ allowed n B ∅, t ⊆ initial n ∧ ∃ g ∈ groups, t ∈ g)
    (hdis : ∀ g ∈ groups, ∀ a ∈ g, ∀ b ∈ g, a ≠ b → Disjoint a b) :
    Refutes (V := V) B := by
  classical
  intro F f hu hi _ hmem
  let members (g : List TripleSet) := F ∩ (g.toFinset.image (fun t => t.map f))
  have hcover (s) (hs : s ∈ F) : ∃ g ∈ groups, s ∈ members g := by
    obtain ⟨g,t,ht,he,hg⟩ := normalize hn (hu s hs) (empty_subset _) hB
      (by simp : Disjoint ((∅ : TripleSet).map f) s) (fun b hb => hi (hmem b hb) hs)
    obtain ⟨hsub,C,hC,htC⟩ := hgroups t ht
    have heq : t.map f = s := (map_agree (fun a ha => (hg a (hsub ha)).symm)).trans he
    exact ⟨C,hC,mem_inter.mpr ⟨hs,mem_image.mpr ⟨t,List.mem_toFinset.mpr htC,heq⟩⟩⟩
  have hsmall (C) (hC : C ∈ groups) : (members C).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨haF,ha⟩ := mem_inter.mp ha
    obtain ⟨hbF,hb⟩ := mem_inter.mp hb
    obtain ⟨u,huC,rfl⟩ := mem_image.mp ha
    obtain ⟨v,hvC,rfl⟩ := mem_image.mp hb
    by_contra h
    exact hi haF hbF ((disjoint_map f).mpr (hdis C hC u (by simpa using huC) v (by simpa using hvC)
      (fun e => h (congrArg (Finset.map f) e))))
  have hsub : F ⊆ groups.toFinset.biUnion members := by
    intro s hs
    obtain ⟨g,hg,hgs⟩ := hcover s hs
    exact mem_biUnion.mpr ⟨g,List.mem_toFinset.mpr hg,hgs⟩
  calc
    F.card ≤ _ := card_le_card hsub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _ ∈ groups.toFinset, 1 := sum_le_sum (fun g hg => hsmall g (by simpa using hg))
    _ = groups.toFinset.card := by simp
    _ ≤ _ := List.toFinset_card_le ..
    _ ≤ 10 := hlen

end StableKneserK3.TransversalCertificate

