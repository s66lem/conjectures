import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

namespace AllieRemoteness

open SimpleGraph Finset

/-! ## Transmission and remoteness -/

section Trans
variable {V : Type*} [Fintype V]

/-- Transmission `σ(v, T) = ∑_u d(v, u)`. -/
noncomputable def trans (G : SimpleGraph V) (v : V) : ℕ := ∑ u, G.dist v u

/-- Maximum transmission `σ_max(T) = max_v σ(v, T)`. -/
noncomputable def maxTrans (G : SimpleGraph V) : ℕ := univ.sup (trans G)

/-- Remoteness `ρ(T) = σ_max(T) / (n - 1)`. -/
noncomputable def remoteness (G : SimpleGraph V) : ℚ :=
  (maxTrans G : ℚ) / ((Fintype.card V : ℚ) - 1)

end Trans

/-- Exact graph distances from a potential: `F v = 0`, `F` is 1-Lipschitz on edges, and
every `u ≠ v` has a neighbour one step closer. -/
theorem dist_eq_of_potential {V : Type*} (G : SimpleGraph V) (v : V) (F : V → ℕ)
    (h0 : F v = 0) (hlip : ∀ x y, G.Adj x y → F y ≤ F x + 1)
    (hdesc : ∀ u, u ≠ v → ∃ w, G.Adj w u ∧ F w + 1 = F u) (u : V) :
    G.dist v u = F u := by
  have walk : ∀ n u, F u = n → ∃ p : G.Walk v u, p.length = n := by
    intro n
    induction n with
    | zero =>
      intro u hu
      by_cases h : u = v
      · subst h; exact ⟨Walk.nil, rfl⟩
      · obtain ⟨w, -, hw⟩ := hdesc u h; omega
    | succ n ih =>
      intro u hu
      have hne : u ≠ v := by rintro rfl; omega
      obtain ⟨w, hwu, hw⟩ := hdesc u hne
      obtain ⟨p, hp⟩ := ih w (by omega)
      exact ⟨p.concat hwu, by simp [hp]⟩
  have lower : ∀ a b (p : G.Walk a b), F b ≤ F a + p.length := by
    intro a b p
    induction p with
    | nil => simp
    | cons h p ih => simp only [Walk.length_cons]; have := hlip _ _ h; omega
  obtain ⟨p, hp⟩ := walk _ u rfl
  obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
  have := lower _ _ q
  have := dist_le p
  omega

/-! ## Triangular numbers and path sums -/

/-- Triangular number `n(n+1)/2`. -/
def tri (n : ℕ) : ℕ := n * (n + 1) / 2

@[simp] lemma tri_zero : tri 0 = 0 := rfl

lemma tri_succ (n : ℕ) : tri (n + 1) = tri n + n + 1 := by
  unfold tri
  have : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
  rw [this, Nat.add_mul_div_left _ _ two_pos]; omega

lemma tri_add (a b : ℕ) : tri (a + b) = tri a + tri b + a * b := by
  induction b with
  | zero => simp [tri]
  | succ b ih => rw [← add_assoc, tri_succ, ih, tri_succ]; ring

/-- Absolute difference on `ℕ`. -/
def ad (a b : ℕ) : ℕ := a - b + (b - a)

lemma sum_ad_self (n : ℕ) : ∑ y ∈ range n, ad n y = tri n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : ∀ y, ad (n + 1) (y + 1) = ad n y := fun y => by unfold ad; omega
    rw [sum_range_succ', sum_congr rfl (fun y _ => h y), ih, tri_succ]; unfold ad; omega

lemma sum_ad (x n : ℕ) (h : x < n) : ∑ y ∈ range n, ad x y = tri x + tri (n - 1 - x) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sum_range_succ]
    rcases Nat.lt_or_ge x n with h' | h'
    · rw [ih h', show n + 1 - 1 - x = (n - 1 - x) + 1 by omega, tri_succ]; unfold ad; omega
    · obtain rfl : x = n := by omega
      rw [sum_ad_self]; simp [ad, tri]

lemma sum_lin (c n : ℕ) : ∑ s ∈ range n, (c + s + 1) = n * c + tri n := by
  induction n with
  | zero => simp [tri]
  | succ n ih => rw [sum_range_succ, ih, tri_succ]; ring

/-- A discretely convex sequence on `[0, N]` is bounded by its endpoint values. -/
lemma convex_le (f : ℕ → ℕ) (N M : ℕ) (h0 : f 0 ≤ M) (hN : f N ≤ M)
    (hc : ∀ x, 0 < x → x < N → 2 * f x ≤ f (x - 1) + f (x + 1)) : ∀ x ≤ N, f x ≤ M := by
  by_contra hne
  push Not at hne
  obtain ⟨y, hy, hyM⟩ := hne
  obtain ⟨z, hz, hzmax⟩ := exists_max_image (range (N + 1)) f ⟨y, mem_range.2 (by omega)⟩
  have hex : ∃ x, x ≤ N ∧ f x = f z := ⟨z, by simpa [Nat.lt_succ_iff] using hz, rfl⟩
  classical
  let x := Nat.find hex
  obtain ⟨hxN, hxz⟩ : x ≤ N ∧ f x = f z := Nat.find_spec hex
  have hmax : ∀ w ≤ N, f w ≤ f x := fun w hw => hxz ▸ hzmax w (mem_range.2 (by omega))
  have hyx := hmax y hy
  have hx0 : 0 < x := Nat.pos_of_ne_zero fun h => by rw [h] at hyx; omega
  have hxN' : x < N := lt_of_le_of_ne hxN fun h => by rw [h] at hyx; omega
  have hprev : f (x - 1) < f x := by
    have h1 := hmax (x - 1) (by omega)
    refine lt_of_le_of_ne h1 fun h => ?_
    have := Nat.find_min' hex ⟨(by omega : x - 1 ≤ N), h.trans hxz⟩
    omega
  have := hc x hx0 hxN'
  have := hmax (x + 1) (by omega)
  omega

/-! ## Caterpillar trees

A spine path `0, 1, …, L` and pendant paths `p : Fin m` with `len p` vertices attached at
spine vertex `pos p`. Every `D`-tree with at most two branch vertices, and the `(9, 3)`-`D`-tree
of `PROOF.md`, is such a caterpillar. -/

section Cat
variable {L m : ℕ} {len : Fin m → ℕ}

/-- Spine vertex `x`, or vertex `t` of pendant path `p` (at distance `t + 1` from the spine). -/
abbrev CV (L m : ℕ) (len : Fin m → ℕ) := Fin (L + 1) ⊕ Σ p : Fin m, Fin (len p)

variable (len) (pos : Fin m → Fin (L + 1))

/-- `R u w`: `u` is the parent of `w`. -/
def R : CV L m len → CV L m len → Prop
  | .inl x, .inl y => y.val = x.val + 1
  | .inl x, .inr ⟨p, t⟩ => (pos p).val = x.val ∧ t.val = 0
  | .inr ⟨p, t⟩, .inr ⟨q, s⟩ => p = q ∧ s.val = t.val + 1
  | .inr _, .inl _ => False

/-- The caterpillar graph. -/
def cat : SimpleGraph (CV L m len) := SimpleGraph.fromRel (R len pos)

/-- Distance formula in the caterpillar. -/
def D : CV L m len → CV L m len → ℕ
  | .inl x, .inl y => ad x y
  | .inl x, .inr ⟨p, t⟩ => ad x (pos p) + t + 1
  | .inr ⟨p, t⟩, .inl y => ad (pos p) y + t + 1
  | .inr ⟨p, t⟩, .inr ⟨q, s⟩ => if p = q then ad t s else ad (pos p) (pos q) + t + s + 2

lemma R_irrefl (u : CV L m len) : ¬ R len pos u u := by
  rcases u with a | ⟨p, t⟩ <;> simp [R]

lemma adj_of_R {w u : CV L m len} (h : R len pos w u) : (cat len pos).Adj w u :=
  ⟨by rintro rfl; exact R_irrefl len pos _ h, Or.inl h⟩

lemma adj_of_R' {w u : CV L m len} (h : R len pos u w) : (cat len pos).Adj w u :=
  ⟨by rintro rfl; exact R_irrefl len pos _ h, Or.inr h⟩

/-- Parent of a pendant vertex. -/
lemma pend_parent (p : Fin m) (t : Fin (len p)) :
    ∃ w, (cat len pos).Adj w (.inr ⟨p, t⟩) ∧ (∀ a, D len pos (.inl a) w + 1 = D len pos (.inl a) (.inr ⟨p, t⟩)) ∧
      ∀ q (s : Fin (len q)), q ≠ p → D len pos (.inr ⟨q, s⟩) w + 1 = D len pos (.inr ⟨q, s⟩) (.inr ⟨p, t⟩) := by
  by_cases ht : t.val = 0
  · refine ⟨.inl (pos p), adj_of_R len pos (by simp [R, ht]), fun a => ?_, fun q s hq => ?_⟩
    · simp [D, ht]
    · simp [D, hq, ht]
  · refine ⟨.inr ⟨p, ⟨t - 1, by omega⟩⟩, adj_of_R len pos (by simp [R]; omega), fun a => ?_,
      fun q s hq => ?_⟩
    · simp [D]; omega
    · simp [D, hq]; omega

lemma spine_step (a x : Fin (L + 1)) (h : a.val ≠ x.val) :
    ∃ y : Fin (L + 1), (cat len pos).Adj (.inl y) (.inl x) ∧ ad a y + 1 = ad a x := by
  have := a.isLt
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact ⟨⟨x - 1, by omega⟩, adj_of_R len pos (by simp [R]; omega), by simp [ad]; omega⟩
  · exact ⟨⟨x + 1, by omega⟩, adj_of_R' len pos (by simp [R]), by simp [ad]; omega⟩

theorem dist_cat (v u : CV L m len) : (cat len pos).dist v u = D len pos v u := by
  apply dist_eq_of_potential _ v (D len pos v)
  · rcases v with a | ⟨p, t⟩ <;> simp [D, ad]
  · intro x y hxy
    simp only [cat, fromRel_adj] at hxy
    obtain ⟨-, hxy⟩ := hxy
    rcases v with a | ⟨p, t⟩ <;> rcases x with b | ⟨q, s⟩ <;> rcases y with c | ⟨r, u⟩ <;>
      simp only [R, D, ad] at hxy ⊢ <;> rcases hxy with h | h <;> (try obtain ⟨rfl, h⟩ := h) <;>
      (try split_ifs) <;> (try subst_vars) <;> omega
  · intro u huv
    rcases v with a | ⟨q, s⟩ <;> rcases u with x | ⟨p, t⟩
    · obtain ⟨y, hy, he⟩ := spine_step len pos a x (fun h => huv (by rw [Fin.ext h]))
      exact ⟨_, hy, by simpa [D] using he⟩
    · obtain ⟨w, hw, h1, -⟩ := pend_parent len pos p t
      exact ⟨w, hw, h1 a⟩
    · by_cases hx : (pos q).val = x.val
      · refine ⟨.inr ⟨q, ⟨0, Nat.zero_lt_of_lt s.isLt⟩⟩, adj_of_R' len pos (by simp [R, hx]), ?_⟩
        simp [D, ad]; omega
      · obtain ⟨y, hy, he⟩ := spine_step len pos (pos q) x hx
        exact ⟨_, hy, by simp [D]; omega⟩
    · by_cases hpq : q = p
      · subst hpq
        have hst : s.val ≠ t.val := fun h => huv (by rw [Fin.ext h])
        rcases Nat.lt_or_gt_of_ne hst with h | h
        · refine ⟨.inr ⟨q, ⟨t - 1, by omega⟩⟩, adj_of_R len pos (by simp [R]; omega), ?_⟩
          simp [D, ad]; omega
        · refine ⟨.inr ⟨q, ⟨t + 1, by omega⟩⟩, adj_of_R' len pos (by simp [R]), ?_⟩
          simp [D, ad]; omega
      · obtain ⟨w, hw, -, h2⟩ := pend_parent len pos p t
        exact ⟨w, hw, h2 q s hpq⟩

theorem trans_inl (x : Fin (L + 1)) : trans (cat len pos) (.inl x) =
    tri x + tri (L - x) + ∑ p, (len p * ad x (pos p) + tri (len p)) := by
  unfold trans
  simp only [dist_cat, Fintype.sum_sum_type, Fintype.sum_sigma, D]
  rw [Fin.sum_univ_eq_sum_range (fun y => ad x y) (L + 1), sum_ad _ _ (by omega),
    show L + 1 - 1 - x = L - x by omega]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun s => ad x (pos p) + s + 1), sum_lin]

/-- Transmission of the leaf of pendant path `q`. -/
theorem trans_leaf (q : Fin m) (hq : 0 < len q) :
    trans (cat len pos) (.inr ⟨q, ⟨len q - 1, by omega⟩⟩) + len q * len q =
      tri (pos q) + tri (L - pos q) + L * len q +
        ∑ p, (len p * (ad (pos q) (pos p) + len q) + tri (len p)) := by
  unfold trans
  simp only [dist_cat, Fintype.sum_sum_type, Fintype.sum_sigma, D]
  rw [Fin.sum_univ_eq_sum_range (fun y => ad (pos q) y + (len q - 1) + 1) (L + 1),
    sum_add_distrib, sum_add_distrib, sum_ad _ _ (by omega),
    ← add_sum_erase _ _ (mem_univ q), ← add_sum_erase _ _ (mem_univ q)]
  have hrest : ∑ p ∈ univ.erase q, ∑ s : Fin (len p),
      (if q = p then ad (len q - 1) s else ad (pos q) (pos p) + (len q - 1) + s + 2) =
      ∑ p ∈ univ.erase q, (len p * (ad (pos q) (pos p) + len q) + tri (len p)) := by
    refine sum_congr rfl fun p hp => ?_
    have hpq : q ≠ p := fun h => by simp [h] at hp
    simp only [hpq, if_false]
    rw [show (∑ s : Fin (len p), (ad (pos q) (pos p) + (len q - 1) + (s : ℕ) + 2)) =
        ∑ s : Fin (len p), ((ad (pos q) (pos p) + len q) + (s : ℕ) + 1) from
        sum_congr rfl fun s _ => by omega,
      Fin.sum_univ_eq_sum_range (fun s => (ad (pos q) (pos p) + len q) + s + 1), sum_lin]
  rw [hrest]
  simp only [if_true]
  rw [Fin.sum_univ_eq_sum_range (fun s => ad (len q - 1) s), sum_ad _ _ (by omega)]
  have h1 : ad (pos q) (pos q) = 0 := by simp [ad]
  have h2 := tri_succ (len q - 1)
  rw [show len q - 1 + 1 = len q by omega] at h2
  simp only [sum_const, card_range, smul_eq_mul, h1, Nat.sub_self, tri_zero]
  generalize len q = n at *
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  rw [h2]; ring

/-- Parent of a vertex, rooting the caterpillar at spine vertex `0`. -/
def par : CV L m len → CV L m len
  | .inl x => .inl ⟨x - 1, by omega⟩
  | .inr ⟨p, t⟩ => if t.val = 0 then .inl (pos p) else .inr ⟨p, ⟨t - 1, by omega⟩⟩

lemma R_par (u : CV L m len) (hu : u ≠ .inl 0) : R len pos (par len pos u) u := by
  rcases u with x | ⟨p, t⟩
  · have : (x : ℕ) ≠ 0 := fun h => hu (by congr; exact Fin.ext (by simp [h]))
    simp [par, R]; omega
  · by_cases ht : t.val = 0 <;> simp [par, R, ht]; omega

lemma par_unique {a b : CV L m len} (h : R len pos a b) : a = par len pos b := by
  rcases a with x | ⟨p, t⟩ <;> rcases b with y | ⟨q, s⟩ <;> simp only [R] at h
  · simp only [par, Sum.inl.injEq]; ext; simp; omega
  · simp only [par, h.2, if_true, Sum.inl.injEq]; ext; simp [h.1]
  · obtain ⟨rfl, h⟩ := h
    simp only [par, show s.val ≠ 0 by omega, if_false, Sum.inr.injEq]
    congr; ext; simp; omega

lemma dep_R {a b : CV L m len} (h : R len pos a b) :
    D len pos (.inl 0) b = D len pos (.inl 0) a + 1 := by
  rcases a with x | ⟨p, t⟩ <;> rcases b with y | ⟨q, s⟩ <;> simp only [R] at h <;>
    (try obtain ⟨rfl, h⟩ := h) <;> simp [D, ad] <;> omega

lemma D_root_ne (u : CV L m len) (hu : u ≠ .inl 0) : D len pos (.inl 0) u ≠ 0 := by
  rcases u with x | ⟨p, t⟩
  · have : (x : ℕ) ≠ 0 := fun h => hu (by congr; exact Fin.ext (by simp [h]))
    simp only [D, ad, Fin.val_zero]; omega
  · simp [D]

/-- The caterpillar is a tree. -/
theorem cat_isTree : (cat len pos).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨connected_iff_exists_forall_reachable _ |>.2 ⟨.inl 0, fun w => ?_⟩, ?_⟩
  · by_cases hw : w = .inl 0
    · subst hw; rfl
    · exact Reachable.of_dist_ne_zero (by rw [dist_cat]; exact D_root_ne len pos w hw)
  · let f : {u : CV L m len // u ≠ .inl 0} → (cat len pos).edgeSet := fun u =>
      ⟨s(par len pos u.1, u.1), adj_of_R len pos (R_par len pos u.1 u.2)⟩
    have hf : Function.Bijective f := by
      refine ⟨fun u w huw => ?_, fun e => ?_⟩
      · have huw' := congrArg Subtype.val huw
        simp only [f, Sym2.eq_iff] at huw'
        rcases huw' with ⟨-, h⟩ | ⟨h1, h2⟩
        · exact Subtype.ext h
        · have e1 := dep_R len pos (R_par len pos u.1 u.2)
          have e2 := dep_R len pos (R_par len pos w.1 w.2)
          rw [h1] at e1; rw [← h2] at e2; omega
      · obtain ⟨e, he⟩ := e
        induction e using Sym2.ind with
        | h a b =>
          rw [mem_edgeSet] at he
          obtain ⟨-, hab | hba⟩ := he
          · have hb : b ≠ .inl 0 := fun h => by subst h; rcases a with x | ⟨p, t⟩ <;> simp [R] at hab
            exact ⟨⟨b, hb⟩, by simp [f, ← par_unique len pos hab, Sym2.eq_swap]⟩
          · have ha : a ≠ .inl 0 := fun h => by subst h; rcases b with x | ⟨p, t⟩ <;> simp [R] at hba
            exact ⟨⟨a, ha⟩, by simp [f, ← par_unique len pos hba]⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have : 0 < Fintype.card (CV L m len) := Fintype.card_pos_iff.2 ⟨.inl 0⟩
    omega

/-- Distance from spine vertex `x` (also defined for `x > L`). -/
def sdist (x : ℕ) : CV L m len → ℕ
  | .inl y => ad x y
  | .inr ⟨p, s⟩ => ad x (pos p) + s + 1

/-- Distance from the vertex at height `h` on pendant path `q` (`h = 0`: its spine root). -/
def pdist (q : Fin m) (h : ℕ) : CV L m len → ℕ
  | .inl y => ad (pos q) y + h
  | .inr ⟨p, s⟩ => if p = q then ad h (s + 1) else ad (pos q) (pos p) + h + s + 1

lemma D_inl (x : Fin (L + 1)) (u : CV L m len) : D len pos (.inl x) u = sdist len pos x u := by
  rcases u with y | ⟨p, s⟩ <;> rfl

lemma D_inr (q : Fin m) (t : Fin (len q)) (u : CV L m len) :
    D len pos (.inr ⟨q, t⟩) u = pdist len pos q (t + 1) u := by
  rcases u with y | ⟨p, s⟩ <;> simp only [D, pdist] <;> (try split_ifs) <;> subst_vars <;>
    simp_all [ad, eq_comm] <;> omega

lemma sdist_pos (q : Fin m) (u : CV L m len) : sdist len pos (pos q) u = pdist len pos q 0 u := by
  rcases u with y | ⟨p, s⟩ <;> simp only [sdist, pdist] <;> (try split_ifs) <;> subst_vars <;>
    simp [ad]

/-- The maximum transmission of a caterpillar is attained at a spine end or a pendant leaf. -/
theorem maxTrans_le (M : ℕ) (h0 : trans (cat len pos) (.inl 0) ≤ M)
    (hL : trans (cat len pos) (.inl (Fin.last L)) ≤ M)
    (hleaf : ∀ q (hq : 0 < len q), trans (cat len pos) (.inr ⟨q, ⟨len q - 1, by omega⟩⟩) ≤ M) :
    maxTrans (cat len pos) ≤ M := by
  have hsp : ∀ x ≤ L, ∑ u, sdist len pos x u ≤ M := by
    apply convex_le _ L M
    · simpa [trans, dist_cat, D_inl] using h0
    · simpa [trans, dist_cat, D_inl] using hL
    · intro x hx0 hxL
      rw [mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun u _ => ?_
      rcases u with y | ⟨p, s⟩ <;> simp only [sdist, ad] <;> omega
  have hpe : ∀ q, ∀ h ≤ len q, ∑ u, pdist len pos q h u ≤ M := by
    intro q
    rcases Nat.eq_zero_or_pos (len q) with hq | hq
    · intro h hh
      obtain rfl : h = 0 := by omega
      simpa [sdist_pos] using hsp (pos q) (by omega)
    apply convex_le _ (len q) M
    · simpa [sdist_pos] using hsp (pos q) (by omega)
    · have := hleaf q hq
      simp only [trans, dist_cat, D_inr] at this
      rwa [show len q - 1 + 1 = len q by omega] at this
    · intro h hh0 hhq
      rw [mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun u _ => ?_
      rcases u with y | ⟨p, s⟩ <;> simp only [pdist, ad] <;> (try split_ifs) <;> omega
  refine Finset.sup_le fun v _ => ?_
  rcases v with x | ⟨q, t⟩
  · simpa [trans, dist_cat, D_inl] using hsp x (by omega)
  · simpa [trans, dist_cat, D_inr] using hpe q (t + 1) (by omega)

end Cat

/-! ## `D`-trees with at most two branch vertices

`D = (ℓ_0, …, ℓ_{k-1})` is the segment sequence. `j = none` gives the starlike tree (all segments
pendant at one vertex). `j = some i` makes segment `i` the internal segment between the two
branch vertices (spine ends `0` and `L = ℓ_i`); `side p` selects the end at which every other
segment `p` hangs. Up to isomorphism this lists every `D`-tree with `h ≤ 2` branch vertices
(and some degenerate configurations, for which the bounds below hold as well). -/

section H2
variable {k : ℕ} (ℓ : Fin k → ℕ) (j : Option (Fin k)) (side : Fin k → Bool)

/-- Length of the spine (the internal segment, if any). -/
def spineLen : ℕ := match j with
  | none => 0
  | some i => ℓ i

/-- Pendant path lengths: segment `j` is the spine, so its pendant copy is empty. -/
def h2len (i : Fin k) : ℕ := if j = some i then 0 else ℓ i

/-- Spine end selected by `b`. -/
def endv {L : ℕ} (b : Bool) : Fin (L + 1) := if b then Fin.last L else 0

/-- The `D`-tree with at most two branch vertices. -/
def h2tree : SimpleGraph (CV (spineLen ℓ j) k (h2len ℓ j)) :=
  cat (h2len ℓ j) (fun i => endv (side i))

/-- Total pendant length at spine end `b`. -/
def W (b : Bool) : ℕ := ∑ i, if side i = b then h2len ℓ j i else 0

lemma h2_sum (g : ℕ → ℕ) (hg : g 0 = 0) :
    g (spineLen ℓ j) + ∑ i, g (h2len ℓ j i) = ∑ i, g (ℓ i) := by
  cases j with
  | none => simp [spineLen, h2len, hg]
  | some j0 =>
    rw [← add_sum_erase _ _ (mem_univ j0), ← add_sum_erase _ (fun i => g (ℓ i)) (mem_univ j0)]
    simp only [spineLen, h2len, if_true, hg, zero_add]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    have : j0 ≠ i := fun h => by simp [h] at hi
    simp [this]

lemma tri_endv {L : ℕ} (b : Bool) : tri (endv (L := L) b) + tri (L - endv (L := L) b) = tri L := by
  cases b <;> simp [endv]

lemma ad_endv {L : ℕ} (b b' : Bool) :
    ad (endv (L := L) b) (endv (L := L) b') = if b' = b then 0 else L := by
  cases b <;> cases b' <;> simp [endv, ad]

/-- Leaf transmission in a tree with `h ≤ 2` (the identity of `PROOF.md` §1). -/
theorem h2_leaf (q : Fin k) (hq : 0 < h2len ℓ j q) :
    trans (h2tree ℓ j side) (.inr ⟨q, ⟨h2len ℓ j q - 1, by omega⟩⟩) + h2len ℓ j q * h2len ℓ j q =
      ∑ i, tri (ℓ i) + h2len ℓ j q * ∑ i, ℓ i + spineLen ℓ j * W ℓ j side (!side q) := by
  rw [h2tree, trans_leaf _ _ q hq, tri_endv]
  have e1 : ∑ p, (h2len ℓ j p * (ad (endv (L := spineLen ℓ j) (side q))
      (endv (L := spineLen ℓ j) (side p)) + h2len ℓ j q) +
      tri (h2len ℓ j p)) = spineLen ℓ j * W ℓ j side (!side q) +
        h2len ℓ j q * ∑ p, h2len ℓ j p + ∑ p, tri (h2len ℓ j p) := by
    rw [W, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [ad_endv]
    cases side p <;> cases side q <;> simp <;> ring
  have e2 := h2_sum ℓ j id rfl
  have e3 := h2_sum ℓ j tri rfl
  simp only [id] at e2
  rw [e1, ← e2, ← e3]; ring

/-- Transmission of a spine end. -/
theorem h2_end (b : Bool) :
    trans (h2tree ℓ j side) (.inl (endv b)) = ∑ i, tri (ℓ i) + spineLen ℓ j * W ℓ j side (!b) := by
  rw [h2tree, trans_inl, tri_endv]
  have e1 : ∑ p, (h2len ℓ j p * ad (endv (L := spineLen ℓ j) b) (endv (L := spineLen ℓ j) (side p)) +
      tri (h2len ℓ j p)) =
      spineLen ℓ j * W ℓ j side (!b) + ∑ p, tri (h2len ℓ j p) := by
    rw [W, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [ad_endv]
    cases side p <;> cases b <;> simp <;> ring
  rw [e1, ← h2_sum ℓ j tri rfl]; ring

end H2

/-! ## The counterexample `D = (315, 116, 25, 21, 21, 1⁸)` and its multiples `t · D` -/

/-- The segment sequence `D` (`k = 13`, `n = 507`). -/
def Dl : Fin 13 → ℕ := ![315, 116, 25, 21, 21, 1, 1, 1, 1, 1, 1, 1, 1]

/-- The scaled segment sequence `t · D`. -/
def Dt (t : ℕ) (i : Fin 13) : ℕ := t * Dl i

lemma sum_Dt (t : ℕ) : ∑ i, Dt t i = t * 506 := by
  simp [Dt, ← mul_sum, Fin.sum_univ_succ, Dl]

/-- Unscaled pendant weight at end `b` when segment `0` (length 315) is the spine. -/
def W1 (s : Fin 13 → Bool) (b : Bool) : ℕ := ∑ i, if s i = b ∧ i ≠ 0 then Dl i else 0

/-- Some vertex of the `h = 2` tree with internal segment 315 is far enough (`PROOF.md` §2). -/
def good (s : Fin 13 → Bool) : Prop := (∃ b, 58150 ≤ 315 * W1 s b) ∨
  ∃ q : Fin 13, q ≠ 0 ∧ 58150 + Dl q * Dl q ≤ Dl q * 506 + 315 * W1 s (!s q)

instance : DecidablePred good := fun s => by unfold good; infer_instance

set_option maxRecDepth 100000 in
/-- All `2¹²` side assignments, checked by kernel evaluation. -/
theorem good_all : ∀ b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    good ![false, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12] := by
  decide +kernel

lemma W1_congr (s s' : Fin 13 → Bool) (h : ∀ i, i ≠ 0 → s i = s' i) (b : Bool) :
    W1 s b = W1 s' b := by
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : i = 0
  · simp [hi]
  · rw [h i hi]

theorem good_of (s : Fin 13 → Bool) : good s := by
  let s' : Fin 13 → Bool :=
    ![false, s 1, s 2, s 3, s 4, s 5, s 6, s 7, s 8, s 9, s 10, s 11, s 12]
  have hs : ∀ i, i ≠ 0 → s i = s' i := by
    intro i hi; fin_cases i <;> simp_all [s']
  have hg := good_all (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7) (s 8) (s 9) (s 10) (s 11) (s 12)
  rcases hg with ⟨b, hb⟩ | ⟨q, hq, h⟩
  · exact Or.inl ⟨b, by rwa [W1_congr s s' hs]⟩
  · refine Or.inr ⟨q, hq, ?_⟩
    rwa [W1_congr s s' hs, hs q hq]

lemma W_Dt (t : ℕ) (side : Fin 13 → Bool) (b : Bool) :
    W (Dt t) (some 0) side b = t * W1 side b := by
  rw [W, W1, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : i = 0
  · subst hi; simp [h2len]
  · have : (some 0 : Option (Fin 13)) ≠ some i := by simpa [eq_comm] using hi
    simp [h2len, this, hi, Dt]

lemma Dl_pos (i : Fin 13) : 0 < Dl i := by fin_cases i <;> decide

/-- **Lower bound.** Every `t · D`-tree with at most two branch vertices has
`σ_max ≥ C(t · D) + 58150 t²`. -/
theorem h2_lower (t : ℕ) (ht : 0 < t) (j : Option (Fin 13)) (side : Fin 13 → Bool) :
    ∑ i, tri (Dt t i) + 58150 * (t * t) ≤ maxTrans (h2tree (Dt t) j side) := by
  have hM : ∀ v, trans (h2tree (Dt t) j side) v ≤ maxTrans (h2tree (Dt t) j side) :=
    fun v => le_sup (mem_univ v)
  by_cases hj : j = some 0
  · subst hj
    have hL : spineLen (Dt t) (some 0) = t * 315 := by simp [spineLen, Dt, Dl]
    rcases good_of side with ⟨b, hb⟩ | ⟨q, hq0, hq⟩
    · have h := h2_end (Dt t) (some 0) side (!b)
      have h' := hM (.inl (endv (!b)))
      generalize trans (h2tree (Dt t) (some 0) side) _ = X at h h'
      rw [Bool.not_not, W_Dt, hL] at h
      have := Nat.mul_le_mul_left (t * t) hb
      nlinarith
    · have hl : h2len (Dt t) (some 0) q = t * Dl q := by
        have : (some 0 : Option (Fin 13)) ≠ some q := by simpa [eq_comm] using hq0
        simp [h2len, this, Dt]
      have hpos : 0 < h2len (Dt t) (some 0) q := by rw [hl]; exact Nat.mul_pos ht (Dl_pos q)
      have h := h2_leaf (Dt t) (some 0) side q hpos
      have h' := hM (.inr ⟨q, ⟨h2len (Dt t) (some 0) q - 1, by omega⟩⟩)
      generalize trans (h2tree (Dt t) (some 0) side) _ = X at h h'
      rw [hl, W_Dt, hL, sum_Dt] at h
      have := Nat.mul_le_mul_left (t * t) hq
      nlinarith
  · have hl : h2len (Dt t) j 0 = t * 315 := by simp [h2len, hj, Dt, Dl]
    have hpos : 0 < h2len (Dt t) j 0 := by rw [hl]; omega
    have h := h2_leaf (Dt t) j side 0 hpos
    have h' := hM (.inr ⟨0, ⟨h2len (Dt t) j 0 - 1, by omega⟩⟩)
    generalize trans (h2tree (Dt t) j side) _ = X at h h'
    rw [hl, sum_Dt] at h
    nlinarith [Nat.zero_le (spineLen (Dt t) j * W (Dt t) j side (!side 0))]

/-! ## The `(9, 3)`-`D`-tree `T*` (scaled by `t`)

Branch vertices `B₁ = 0`, `B₂ = 315`, `B₃ = 431` on a spine made of the internal segments
`315` and `116`; pendant segments `{21, 21}` at `B₁`, `{25}` at `B₂`, `{1⁸}` at `B₃`. -/

/-- Pendant attachment points (unscaled). -/
def Ppos : Fin 11 → ℕ := ![0, 0, 315, 431, 431, 431, 431, 431, 431, 431, 431]

/-- Pendant segment lengths (unscaled). -/
def Plen : Fin 11 → ℕ := ![21, 21, 25, 1, 1, 1, 1, 1, 1, 1, 1]

lemma Ppos_le (p : Fin 11) : Ppos p ≤ 431 := by fin_cases p <;> decide

/-- Scaled pendant lengths. -/
def starLen (t : ℕ) (p : Fin 11) : ℕ := t * Plen p

/-- Scaled attachment points. -/
def starPos (t : ℕ) (p : Fin 11) : Fin (t * 431 + 1) :=
  ⟨t * Ppos p, Nat.lt_succ_of_le (Nat.mul_le_mul_left t (Ppos_le p))⟩

/-- The `(9, 3)`-`(t · D)`-tree. -/
def Tstar (t : ℕ) : SimpleGraph (CV (t * 431) 11 (starLen t)) := cat (starLen t) (starPos t)

lemma ad_mul (t a b : ℕ) : ad (t * a) (t * b) = t * ad a b := by
  simp only [ad, ← Nat.mul_sub, ← mul_add]

lemma C_Dt (t : ℕ) : ∑ i, tri (Dt t i) =
    tri (t * 315) + tri (t * 116) + tri (t * 25) + 2 * tri (t * 21) + 8 * tri t := by
  simp [Dt, Dl, Fin.sum_univ_succ]; ring

lemma tri_431 (t : ℕ) : tri (t * 431) = tri (t * 315) + tri (t * 116) + t * 315 * (t * 116) := by
  rw [← tri_add]; ring_nf

/-- **Upper bound.** `σ_max(T*_t) ≤ C(t · D) + 58048 t²`. -/
theorem Tstar_upper (t : ℕ) : maxTrans (Tstar t) ≤ ∑ i, tri (Dt t i) + 58048 * (t * t) := by
  have hC := C_Dt t
  have h431 := tri_431 t
  have h116 : t * 431 - t * 315 = t * 116 := by omega
  rw [hC]
  apply maxTrans_le
  · rw [trans_inl]
    simp [Fin.sum_univ_succ, starLen, starPos, Plen, Ppos, ad]
    nlinarith
  · rw [trans_inl]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, starLen, starPos, Fin.val_last, ad_mul]
    simp [Plen, Ppos, ad]
    nlinarith
  · intro q hq
    have h := trans_leaf (starLen t) (starPos t) q hq
    generalize trans (cat (starLen t) (starPos t)) _ = X at h ⊢
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, starLen, starPos, ad_mul] at h
    fin_cases q <;> simp [Plen, Ppos, ad, h116] at h <;> ring_nf at h h431 ⊢ <;> omega

/-- The farthest leaf of `T*_t` (end of the first `21`-segment). -/
theorem Tstar_leaf (t : ℕ) (ht : 0 < t) :
    trans (Tstar t) (.inr ⟨0, ⟨starLen t 0 - 1, by simp [starLen, Plen]; omega⟩⟩) =
      ∑ i, tri (Dt t i) + 58048 * (t * t) := by
  have hC := C_Dt t
  have h431 := tri_431 t
  have h := trans_leaf (starLen t) (starPos t) 0 (by simp [starLen, Plen]; omega)
  unfold Tstar
  generalize trans (cat (starLen t) (starPos t)) _ = X at h ⊢
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, starLen, starPos, ad_mul] at h
  simp [Plen, Ppos, ad] at h
  rw [hC]
  linarith

theorem Tstar_maxTrans (t : ℕ) (ht : 0 < t) :
    maxTrans (Tstar t) = ∑ i, tri (Dt t i) + 58048 * (t * t) :=
  le_antisymm (Tstar_upper t) (Tstar_leaf t ht ▸ le_sup (mem_univ _))

/-! ## Main results -/

lemma card_CV {L m : ℕ} (len : Fin m → ℕ) : Fintype.card (CV L m len) = L + 1 + ∑ p, len p := by
  simp [Fintype.card_sigma]

lemma card_Tstar (t : ℕ) : Fintype.card (CV (t * 431) 11 (starLen t)) = t * 506 + 1 := by
  rw [card_CV]; simp [starLen, Plen, ← mul_sum, Fin.sum_univ_succ]; ring

lemma card_h2 (t : ℕ) (j : Option (Fin 13)) :
    Fintype.card (CV (spineLen (Dt t) j) 13 (h2len (Dt t) j)) = t * 506 + 1 := by
  have := h2_sum (Dt t) j id rfl
  simp only [id] at this
  rw [card_CV, ← sum_Dt, ← this]; ring

theorem Tstar_isTree (t : ℕ) : (Tstar t).IsTree := cat_isTree _ _

theorem h2tree_isTree {k : ℕ} (ℓ : Fin k → ℕ) (j : Option (Fin k)) (side : Fin k → Bool) :
    (h2tree ℓ j side).IsTree := cat_isTree _ _

/-- `σ_max(T*) = 115399` for `D = (315, 116, 25, 21, 21, 1⁸)`. -/
theorem Tstar_one : maxTrans (Tstar 1) = 115399 := by
  rw [Tstar_maxTrans 1 one_pos, C_Dt]; norm_num [tri]

/-- Every `D`-tree with at most two branch vertices has `σ_max ≥ 115501`. -/
theorem h2_one (j : Option (Fin 13)) (side : Fin 13 → Bool) :
    115501 ≤ maxTrans (h2tree (Dt 1) j side) := by
  have := h2_lower 1 one_pos j side
  rw [C_Dt] at this; norm_num [tri] at this; omega

/-- **Infinite family.** For every `t ≥ 1`, the `(9, 3)`-`(t · D)`-tree beats every
`(t · D)`-tree with at most two branch vertices by at least `102 t²` in maximum transmission. -/
theorem family_gap (t : ℕ) (ht : 0 < t) (j : Option (Fin 13)) (side : Fin 13 → Bool) :
    maxTrans (Tstar t) + 102 * (t * t) ≤ maxTrans (h2tree (Dt t) j side) := by
  rw [Tstar_maxTrans t ht]; have := h2_lower t ht j side; omega

theorem family_remoteness (t : ℕ) (ht : 0 < t) (j : Option (Fin 13)) (side : Fin 13 → Bool) :
    remoteness (Tstar t) < remoteness (h2tree (Dt t) j side) := by
  have hgap := family_gap t ht j side
  have hlt : (maxTrans (Tstar t) : ℚ) < maxTrans (h2tree (Dt t) j side) := by
    exact_mod_cast (show maxTrans (Tstar t) < maxTrans (h2tree (Dt t) j side) by
      have : 0 < t * t := Nat.mul_pos ht ht
      omega)
  unfold remoteness
  rw [card_Tstar, card_h2]
  have hpos : (0 : ℚ) < ((t * 506 + 1 : ℕ) : ℚ) - 1 := by
    have : (0 : ℚ) < t := by exact_mod_cast ht
    push_cast; linarith
  exact div_lt_div_of_pos_right hlt hpos

/-- **Conjecture 4.4 of arXiv:2611.27685 is false.** For `D = (315, 116, 25, 21, 21, 1⁸)`
(`n = 507`), the `(9, 3)`-`D`-tree `T*` is a tree with `σ_max(T*) = 115399`, while every
`D`-tree with at most two branch vertices (starlike or `(Δ, 2)`) has `σ_max ≥ 115501`, hence
strictly larger remoteness. -/
theorem conjecture_4_4_false :
    (Tstar 1).IsTree ∧ Fintype.card (CV (1 * 431) 11 (starLen 1)) = 507 ∧
      maxTrans (Tstar 1) = 115399 ∧
      ∀ (j : Option (Fin 13)) (side : Fin 13 → Bool),
        (h2tree (Dt 1) j side).IsTree ∧
        Fintype.card (CV (spineLen (Dt 1) j) 13 (h2len (Dt 1) j)) = 507 ∧
        115501 ≤ maxTrans (h2tree (Dt 1) j side) ∧
        remoteness (Tstar 1) < remoteness (h2tree (Dt 1) j side) :=
  ⟨Tstar_isTree 1, card_Tstar 1, Tstar_one, fun j side =>
    ⟨h2tree_isTree _ _ _, card_h2 1 j, h2_one j side, family_remoteness 1 one_pos j side⟩⟩

end AllieRemoteness

#print axioms AllieRemoteness.conjecture_4_4_false
#print axioms AllieRemoteness.family_gap
#print axioms AllieRemoteness.family_remoteness
