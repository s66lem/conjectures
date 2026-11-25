import Conjectures.StableKneserK3.Basic

namespace StableKneserK3

namespace ColoringCertificate

/-- A depth-first coloring certificate names the next vertex at each visited node. -/
structure State (α : Type*) where
  used : ℕ
  assigned : List (α × ℕ)

variable {α : Type*}

def children (adj : α → α → Bool) (q : ℕ) (s : State α) (v : α) : List (State α) :=
  ((List.range (min q (s.used + 1))).filter (fun k =>
    s.assigned.all (fun p => !(decide (p.2 = k) && adj v p.1)))).map (fun k =>
      ⟨max s.used (k+1), (v,k) :: s.assigned⟩)

def step (adj : α → α → Bool) (q : ℕ) (states : List (State α)) (v : α) :=
  match states with
  | [] => []
  | s :: ss => children adj q s v ++ ss

def check (adj : α → α → Bool) (q : ℕ) (nodes : List α) : Bool :=
  (nodes.foldl (step adj q) [⟨0, []⟩]).isEmpty

def Realizable (adj : α → α → Bool) (q : ℕ) (s : State α) : Prop :=
  ∃ c : α → Fin q, (∀ a b, adj a b = true → c a ≠ c b) ∧
    ∀ p ∈ s.assigned, (c p.1).val = p.2 ∧ p.2 < s.used

private theorem child_realizable {adj : α → α → Bool} {q : ℕ} {s : State α}
    (h : Realizable adj q s) (v : α) : ∃ t ∈ children adj q s v, Realizable adj q t := by
  obtain ⟨c, hc, hs⟩ := h
  let k : Fin q := ⟨min (c v).val s.used, lt_of_le_of_lt (min_le_left ..) (c v).isLt⟩
  let d (x : α) := Equiv.swap (c v) k (c x)
  have hd (a b : α) (hab : adj a b) : d a ≠ d b :=
    fun he => hc a b hab ((Equiv.swap ..).injective he)
  have hv : d v = k := Equiv.swap_apply_left ..
  have hprev (p) (hp : p ∈ s.assigned) : (d p.1).val = p.2 := by
    obtain ⟨he, hl⟩ := hs p hp
    by_cases hsmall : (c v).val ≤ s.used
    · have heq : k = c v := Fin.ext (min_eq_left hsmall)
      simpa [d, heq] using he
    · have hk : k.val = s.used := min_eq_right (by omega)
      have h₁ : c p.1 ≠ c v := by intro h; have := congrArg Fin.val h; omega
      have h₂ : c p.1 ≠ k := by intro h; have := congrArg Fin.val h; omega
      rw [show d p.1 = c p.1 from Equiv.swap_apply_of_ne_of_ne h₁ h₂, he]
  have hku : k.val ≤ s.used := min_le_right ..
  refine ⟨⟨max s.used (k.val+1), (v,k.val) :: s.assigned⟩, List.mem_map.mpr ⟨k.val, ?_, rfl⟩,
    d, hd, ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (lt_min k.isLt (by omega)), List.all_eq_true.mpr ?_⟩
    intro p hp
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff]
    by_cases he : p.2 = k.val
    · right
      cases ha : adj v p.1
      · rfl
      · exact False.elim (hd _ _ ha (Fin.ext ((congrArg Fin.val hv).trans ((hprev p hp).trans he).symm)))
    · exact Or.inl (decide_eq_false he)
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨congrArg Fin.val hv, by simp⟩
    · exact ⟨hprev _ hp, lt_of_lt_of_le (hs _ hp).2 (le_max_left ..)⟩

private theorem fold_realizable {adj : α → α → Bool} {q : ℕ} (nodes : List α)
    (states : List (State α)) (h : ∃ s ∈ states, Realizable adj q s) :
    ∃ s ∈ nodes.foldl (step adj q) states, Realizable adj q s := by
  induction nodes generalizing states with
  | nil => exact h
  | cons v vs ih =>
    apply ih
    obtain ⟨s, hs, hr⟩ := h
    cases states with
    | nil => cases hs
    | cons a as =>
      rcases List.mem_cons.mp hs with rfl | hs
      · obtain ⟨t, ht, htr⟩ := child_realizable hr v
        exact ⟨t, List.mem_append_left _ ht, htr⟩
      · exact ⟨s, List.mem_append_right _ hs, hr⟩

def Possible (adj : α → α → Bool) (q : ℕ) (states : List (State α)) : Prop :=
  ∃ s ∈ states, Realizable adj q s

theorem advance {adj : α → α → Bool} {q : ℕ} {s t : List (State α)} (nodes : List α)
    (h : nodes.foldl (step adj q) s = t) : Possible adj q s → Possible adj q t :=
  h ▸ fold_realizable nodes s

theorem possible_start {adj : α → α → Bool} {q : ℕ} (c : α → Fin q)
    (hc : ∀ a b, adj a b = true → c a ≠ c b) : Possible adj q [⟨0, []⟩] :=
  ⟨_, List.mem_singleton_self _, c, hc, by simp⟩

theorem sound {adj : α → α → Bool} {q : ℕ} {nodes : List α}
    (h : check adj q nodes = true) (c : α → Fin q) :
    ¬ (∀ a b, adj a b = true → c a ≠ c b) := by
  intro hc
  obtain ⟨s, hs, _⟩ := fold_realizable (adj := adj) (q := q) nodes [⟨0, []⟩]
    ⟨_, List.mem_singleton_self _, c, hc, by simp⟩
  rw [List.isEmpty_iff.mp h] at hs
  cases hs

end ColoringCertificate
end StableKneserK3
