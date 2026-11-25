import Conjectures.FanelliMoscardelli.Market

namespace FanelliMoscardelli.Market
open Roommates Finset
variable {m : ℕ} {p : Market m}
local notation "V" => Agent m
local notation "r" => p.partnerRank
local notation "E" => Edge p
local notation "x" => mid p
local notation "f" => first p

variable (p) in
structure Packed (W : Finset V) : Prop where
  cover : Pairs Wᶜ E
  indep : ∀ i ∈ W, ∀ j ∈ W, ¬E i j

variable {W : Finset (Agent m)}

theorem Packed.even_erase (h : Packed p W) {u : V} (hu : u ∈ W) :
    Even (W.erase u).card := by
  obtain ⟨k,hk⟩ := h.cover.card_even (fun i _ ↦ edge_irrefl p i)
  have hc := Finset.card_compl_add_card W
  simp only [Fintype.card_fin] at hc
  have := Finset.card_erase_add_one hu
  exact ⟨m-k, by omega⟩

/-- If a completion fails, the middle choice of the single must belong to the
uncovered set and must prefer the single by at least the threshold. -/
theorem Packed.obstruction (h : Packed p W) (hm : 0 < m) (bad : ¬ Solved p)
    {u : V} (hu : u ∈ W) {B : V → V → Prop} (fill : Pairs (W.erase u) B)
    (hne : ∀ i ∈ W.erase u, ¬B i i) :
    x u ∈ W.erase u ∧ ∃ b ∈ W.erase u, B (x u) b ∧ r (x u) u + m ≤ r (x u) b := by
  classical
  let D i j := (i ∉ W ∧ E i j) ∨ (i = u ∧ j = u) ∨
    (i ∈ W.erase u ∧ j ∈ W.erase u ∧ B i j)
  have h₁ : Pairs Wᶜ D := h.cover.mono (by simp [D]; grind)
  have h₂ : Pairs {u} D := Pairs.single (by simp [D])
  have h₃ : Pairs (W.erase u) D := fill.mono (by simp [D]; grind)
  have hall : Wᶜ ∪ {u} ∪ W.erase u = univ := by ext; simp; grind
  have hp : Pairs univ D := hall ▸ (h₁.union h₂ (by simpa using hu)).union h₃ (by
    simp [Finset.disjoint_left]; grind)
  by_contra hno
  apply bad
  apply criterion p (u := u) hp
  · intro i hi
    have := edge_irrefl p i
    simp only [D] at hi
    grind
  · intro i j k l he hik hjl
    have hind := h.indep i
    have hi' := rank_pos p i j
    have hj' := rank_pos p j i
    simp only [D, mem_erase, Edge] at hik hjl
    by_cases hi : i ∈ W
    · have hj : j ∉ W := fun hj ↦ hind hi j hj he
      grind
    · grind
  · intro l hl
    have hx := mid_ne p hm u
    have hr := rank_pos p (x u) u
    simp only [D, Edge] at hl
    grind

theorem force_pair {S : Finset V} (hc : Even S.card)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    Pairs S (fun i j ↦ i ≠ j ∧ (i = a → j = b)) := by
  let T := (S.erase a).erase b
  have hb' := mem_erase.mpr ⟨hab.symm,hb⟩
  have ht : Even T.card := by
    obtain ⟨k,hk⟩ := hc
    have := card_erase_add_one ha
    have := card_erase_add_one hb'
    exact ⟨k-1, by dsimp [T]; omega⟩
  have heq : T ∪ {a,b} = S := by ext; simp [T]; grind
  rw [← heq]
  refine Pairs.union ?_ (Pairs.pair (a := a) (b := b) (by simp [hab]) (by simp [hab.symm])) ?_
  · apply (Pairs.of_even ht).mono
    simp [T]; grind
  · simp [Finset.disjoint_right, T]

theorem Packed.forced (h : Packed p W) (hm : 0 < m) (bad : ¬Solved p) {u : V} (hu : u ∈ W) :
    x u ∈ W ∧ r (x u) u ≤ m ∧
    ∀ v ∈ W, v ≠ u → v ≠ x u → r (x u) u + m ≤ r (x u) v := by
  have hc := h.even_erase hu
  obtain ⟨hx,b,_,hxb,hbd⟩ := h.obstruction hm bad hu (Pairs.of_even hc) (by simp)
  refine ⟨(mem_erase.mp hx).2, ?_, ?_⟩
  · have := rank_other p hxb.symm
    omega
  intro v hv hvu hvx
  have hpair := force_pair hc hx (mem_erase.mpr ⟨hvu,hv⟩) hvx.symm
  obtain ⟨_,z,_,hz,hbound⟩ := h.obstruction hm bad hu hpair (by simp)
  simpa only [hz.2 rfl] using hbound

variable (p) in
structure Cycles (W : Finset V) : Prop where
  mid_mem : ∀ u ∈ W, x u ∈ W
  first_mid : ∀ u ∈ W, f (x u) = u
  first_mem : ∀ u ∈ W, f u ∈ W
  mid_first : ∀ u ∈ W, x (f u) = u
  other : ∀ u ∈ W, ∀ v ∈ W, v ≠ f u → m < r u v

theorem Packed.cycles (h : Packed p W) (hm : 0 < m) (bad : ¬Solved p) : Cycles p W := by
  have H := fun (u : V) (hu : u ∈ W) ↦ h.forced hm bad hu
  have inv : ∀ u ∈ W, f (x u) = u := by
    intro u hu
    have hu' := H u hu
    have huu := H _ hu'.1
    have hne : x (x u) ≠ u := by
      intro he
      have hh := huu.2.1
      rw [he, rank_mid] at hh
      omega
    have hh := hu'.2.2 _ huu.1 hne (mid_ne p hm _)
    rw [rank_mid] at hh
    apply rank_inj p _
    rw [rank_first]
    have := rank_pos p (x u) u
    omega
  have onto : ∀ v ∈ W, ∃ u ∈ W, x u = v := by
    let g (u : ↥W) : ↥W := ⟨x u, (H _ u.property).1⟩
    have inj : Function.Injective g := by
      intro a b eq
      have eq' := congrArg Subtype.val eq
      change x a.val = x b.val at eq'
      apply Subtype.ext
      simpa only [inv _ a.property, inv _ b.property] using congrArg f eq'
    intro v hv
    obtain ⟨u, e⟩ := Finite.surjective_of_injective inj (⟨v,hv⟩ : ↥W)
    exact ⟨u,u.property,congrArg Subtype.val e⟩
  refine ⟨fun u hu ↦ (H _ hu).1, inv, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := onto _ hv
    rwa [inv _ hu]
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := onto _ hv
    rw [inv _ hu]
  · intro v hv a ha hne
    obtain ⟨u,hu,rfl⟩ := onto _ hv
    rw [inv _ hu] at hne
    by_cases he : a = x u
    · subst a; simp; omega
    · have := (H _ hu).2.2 a ha hne he
      have := rank_pos p (x u) u
      omega

end FanelliMoscardelli.Market
