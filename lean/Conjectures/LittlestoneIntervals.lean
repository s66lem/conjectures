import Mathlib.Data.List.OfFn
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Odd switch budgets and optimal greedy cuts

The first part identifies every first-query branch with the fixed-end gap class.
The second part bounds each legal cut at every dyadic scale, then sums these
bounds and solves the Bellman recurrence by induction on the remaining cuts.

Reference: M. Daga and S. P. Ramu, arXiv:2611.28727.
-/

namespace LittlestoneIntervals

def slice {X : Type*} (H : Set (X → Bool)) (x : X) (b : Bool) :=
  {f ∈ H | f x = b}

def ShatteredTree (X : Type*) (H : Set (X → Bool)) : ℕ → Prop
  | 0 => H.Nonempty
  | d + 1 => ∃ x, ShatteredTree X (slice H x false) d ∧ ShatteredTree X (slice H x true) d

noncomputable def ldim (X : Type*) (H : Set (X → Bool)) : ℕ :=
  sSup {d | ShatteredTree X H d}

private theorem inhabited_tree {X : Type*} {H : Set (X → Bool)} {d}
    (h : ShatteredTree X H d) : H.Nonempty := by
  induction d generalizing H with
  | zero => exact h
  | succ d ih =>
    obtain ⟨_, h, _⟩ := h
    obtain ⟨f, hf⟩ := ih h
    exact ⟨f, hf.1⟩

/-- Transfer a tree by matching each query up to a fixed flip. A query constant on
the class cannot occur at the root of a positive-depth tree. -/
private theorem transfer {X Y : Type*} {H : Set (X → Bool)} {K : Set (Y → Bool)}
    (e : (X → Bool) → (Y → Bool)) (he : ∀ f ∈ H, e f ∈ K)
    (hq : ∀ x, (∃ b, ∀ f ∈ H, f x = b) ∨
      ∃ y s, ∀ f ∈ H, e f y = (if s = true then !(f x) else f x))
    {d} (h : ShatteredTree X H d) : ShatteredTree Y K d := by
  induction d generalizing H K with
  | zero =>
    obtain ⟨f, hf⟩ := h
    exact ⟨e f, he f hf⟩
  | succ d ih =>
    obtain ⟨x, hl, hr⟩ := h
    rcases hq x with ⟨b, hb⟩ | ⟨y, s, hy⟩
    · obtain ⟨f, hf⟩ := inhabited_tree hl
      obtain ⟨g, hg⟩ := inhabited_tree hr
      have := (hb f hf.1).symm.trans hf.2
      have := (hb g hg.1).symm.trans hg.2
      grind
    · have branch (b : Bool) (hb : ShatteredTree X (slice H x b) d) :
          ShatteredTree Y (slice K y (if s = true then !b else b)) d := by
        apply ih _ _ hb
        · intro f hf
          exact ⟨he f hf.1, by rw [hy f hf.1, hf.2]⟩
        · intro z
          rcases hq z with ⟨c, hc⟩ | ⟨w, c, hc⟩
          · exact Or.inl ⟨c, fun f hf => hc f hf.1⟩
          · exact Or.inr ⟨w, c, fun f hf => hc f hf.1⟩
      exact ⟨y, by cases s <;> first | exact ⟨branch false hl, branch true hr⟩
                                     | exact ⟨branch true hr, branch false hl⟩⟩

private def edge (a b : Bool) : ℕ := if a = b then 0 else 1

private def free (a : Bool) : List Bool → ℕ
  | [] => 0
  | b :: l => edge a b + free b l

private def walk (a : Bool) : List Bool → Bool → ℕ
  | [], b => edge a b
  | x :: l, b => edge a x + walk x l b

private theorem walk_free (a b : Bool) (l : List Bool) :
    walk a l b = free a l + (if free a l % 2 = edge a b then 0 else 1) := by
  induction l generalizing a with
  | nil => cases a <;> cases b <;> decide
  | cons x l ih =>
    simp only [free, walk, ih x]
    cases a <;> cases x <;> cases b <;> simp [edge] <;> split_ifs <;> omega

private theorem walk_flip (a b : Bool) (l : List Bool) :
    walk (!a) (l.map Bool.not) (!b) = walk a l b := by
  induction l generalizing a with
  | nil => cases a <;> cases b <;> rfl
  | cons x l ih =>
    simp only [List.map_cons, walk, ih]
    cases a <;> cases x <;> rfl

private theorem walk_snoc (a b c : Bool) (l : List Bool) :
    walk a (l ++ [b]) c = walk a l b + edge b c := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => simp [walk, ih, Nat.add_assoc]

def switches : {n : ℕ} → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | _ + 1, f => free (f 0) (List.ofFn (fun i => f i.succ))

def C (n k : ℕ) := {f : Fin n → Bool | switches f ≤ k}

def gapSwitches {m : ℕ} (g : Fin m → Bool) := walk false (List.ofFn g) true

def G (k n : ℕ) := {g : Fin (n - 1) → Bool | gapSwitches g ≤ k}

private def aug {n : ℕ} (f : Fin (n+1) → Bool) :=
  walk (f 0) (List.ofFn (fun i => f i.succ)) (!(f 0))

private theorem mem_aug {n k : ℕ} (hk : Odd k) (f : Fin (n+1) → Bool) :
    f ∈ C (n+1) k ↔ aug f ≤ k := by
  obtain ⟨t, ht⟩ := hk
  have hn (a : Bool) : edge a (!a) = 1 := by cases a <;> rfl
  change free _ _ ≤ k ↔ walk _ _ _ ≤ k
  rw [walk_free, hn]
  split_ifs <;> omega

def signedRotation {n : ℕ} (f : Fin (n+1) → Bool) : Fin (n+1) → Bool :=
  Fin.snoc (fun i => f i.succ) (!(f 0))

private def unrotate {n : ℕ} (g : Fin (n+1) → Bool) : Fin (n+1) → Bool :=
  Fin.cons (!(g (Fin.last n))) (fun i => g i.castSucc)

private theorem rotate_unrotate {n} (g : Fin (n+1) → Bool) :
    signedRotation (unrotate g) = g := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [signedRotation, unrotate]

private theorem unrotate_rotate {n} (f : Fin (n+1) → Bool) :
    unrotate (signedRotation f) = f := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [signedRotation, unrotate]

def rotationEquiv (n : ℕ) : (Fin (n+1) → Bool) ≃ (Fin (n+1) → Bool) :=
  ⟨signedRotation, unrotate, unrotate_rotate, rotate_unrotate⟩

private theorem ofFn_snoc {n} (f : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc f b) = List.ofFn f ++ [b] := by
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

private theorem aug_rotate {n} (f : Fin (n+1) → Bool) :
    aug (signedRotation f) = aug f := by
  cases n with
  | zero => simp [aug, signedRotation, walk, edge]
  | succ n =>
    let g : Fin n → Bool := fun i => f i.succ.succ
    have tail_eq : (fun i : Fin (n+1) => signedRotation f i.succ) =
        Fin.snoc g (!(f 0)) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [signedRotation]
      · change signedRotation f j.succ.castSucc = _
        exact (Fin.snoc_castSucc _ _ j.succ).trans (Fin.snoc_castSucc (α := fun _ : Fin (n+1) => Bool) (!(f 0)) g j).symm
    unfold aug
    rw [tail_eq, ofFn_snoc, walk_snoc]
    rw [List.ofFn_succ (f := fun i : Fin (n+1) => f i.succ)]
    simp only [walk, signedRotation, Fin.snoc_apply_zero]
    change _ + edge (!(f 0)) (!(f 1)) = edge (f 0) (f 1) + _
    have h (a b : Bool) : edge (!a) (!b) = edge a b := by cases a <;> cases b <;> rfl
    rw [h, Nat.add_comm]

theorem signedRotation_mem {n k} (hk : Odd k) (f : Fin (n+1) → Bool) :
    signedRotation f ∈ C (n+1) k ↔ f ∈ C (n+1) k := by
  rw [mem_aug hk, mem_aug hk, aug_rotate]

private theorem flip_mem {n k} (hk : Odd k) (f : Fin (n+1) → Bool) :
    (fun i => !(f i)) ∈ C (n+1) k ↔ f ∈ C (n+1) k := by
  rw [mem_aug hk, mem_aug hk]
  unfold aug
  simpa only [List.map_ofFn, Function.comp_def] using
    (congrArg (· ≤ k) (walk_flip (f 0) (!(f 0)) (List.ofFn (fun i => f i.succ)))).to_iff

theorem signedRotation_query {n : ℕ} (f : Fin (n+1) → Bool) (i : Fin (n+1)) :
    signedRotation f i = if i = Fin.last n then !(f (finRotate _ i)) else f (finRotate _ i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [signedRotation]
  · simp only [signedRotation, Fin.snoc_castSucc, Fin.castSucc_ne_last, if_false]
    exact congrArg f (finRotate_of_lt j.isLt).symm

theorem signedRotation_shattered {n d} (H : Set (Fin (n+1) → Bool)) :
    ShatteredTree _ H d ↔ ShatteredTree _ (signedRotation '' H) d := by
  constructor
  · apply transfer (K := signedRotation '' H) signedRotation (fun f hf => ⟨f, hf, rfl⟩)
    intro x
    right
    refine Fin.cases ⟨Fin.last n, true, ?_⟩ (fun i => ⟨i.castSucc, false, ?_⟩) x
    · simp [signedRotation]
    · simp [signedRotation]
  · apply transfer unrotate
    · rintro _ ⟨f, hf, rfl⟩
      simpa only [unrotate_rotate] using hf
    · intro y
      right
      refine Fin.lastCases ⟨0, true, ?_⟩ (fun i => ⟨i.succ, false, ?_⟩) y
      · simp [unrotate]
      · simp [unrotate]

theorem rotation_slice {n k} (hk : Odd k) (i : Fin n) (b : Bool) :
    signedRotation '' slice (C (n+1) k) i.succ b = slice (C (n+1) k) i.castSucc b := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨(signedRotation_mem hk _).2 hf.1, by simpa [signedRotation] using hf.2⟩
  · intro hg
    refine ⟨unrotate g, ⟨(signedRotation_mem hk _).1 ?_, ?_⟩, rotate_unrotate g⟩
    · simpa [rotate_unrotate] using hg.1
    · simpa [unrotate] using hg.2

/-- Iterated signed rotation moves the queried coordinate to zero. Complementing
the word when necessary also normalizes its queried label. -/
theorem slice_isomorphism {n k} (hk : Odd k) (x : Fin (n+1)) (b : Bool) :
    ∃ e : Equiv.Perm (Fin (n+1) → Bool),
      e '' slice (C (n+1) k) x b = slice (C (n+1) k) 0 false ∧
      ∀ H d, ShatteredTree _ H d ↔ ShatteredTree _ (e '' H) d := by
  induction x using Fin.induction with
  | zero =>
    cases b with
    | false => exact ⟨Equiv.refl _, by simp, by simp⟩
    | true =>
      let flip (f : Fin (n+1) → Bool) := fun i => !(f i)
      have hinv (f) : flip (flip f) = f := by funext i; simp [flip]
      let e : Equiv.Perm (Fin (n+1) → Bool) := ⟨flip, flip, hinv, hinv⟩
      refine ⟨e, ?_, ?_⟩
      · ext f
        constructor
        · rintro ⟨g,hg,rfl⟩
          exact ⟨(flip_mem hk _).2 hg.1, congrArg Bool.not hg.2⟩
        · intro hf
          exact ⟨flip f, ⟨(flip_mem hk _).2 hf.1, congrArg Bool.not hf.2⟩, hinv f⟩
      · intro H d
        have tr (K J : Set (Fin (n+1) → Bool)) (hj : ∀ f ∈ K, flip f ∈ J) :
            ShatteredTree _ K d → ShatteredTree _ J d :=
          transfer flip hj (fun i => Or.inr ⟨i, true, fun _ _ => rfl⟩)
        exact ⟨tr _ _ (fun f hf => ⟨f,hf,rfl⟩),
          tr _ _ (by rintro _ ⟨f,hf,rfl⟩; change flip (flip f) ∈ H; rwa [hinv])⟩
  | succ i ih =>
    obtain ⟨e,hs,he⟩ := ih
    refine ⟨(rotationEquiv n).trans e, ?_, ?_⟩
    · change (e ∘ signedRotation) '' _ = _
      rw [Set.image_comp, rotation_slice hk, hs]
    · intro H d
      change ShatteredTree _ H d ↔ ShatteredTree _ ((e ∘ signedRotation) '' H) d
      rw [Set.image_comp]
      exact (signedRotation_shattered H).trans (he _ d)

private theorem fixed_gap {n k d} (hk : Odd k) :
    ShatteredTree _ (slice (C (n+1) k) 0 false) d ↔ ShatteredTree _ (G k (n+1)) d := by
  constructor
  · apply transfer (fun f i => f (Fin.succ i))
    · intro f hf
      have h := (mem_aug hk f).1 hf.1
      simpa [aug, hf.2, G, gapSwitches] using h
    · intro x
      refine Fin.cases (Or.inl ⟨false, fun f hf => hf.2⟩) (fun i => ?_) x
      exact Or.inr ⟨i, false, fun _ _ => rfl⟩
  · apply transfer (fun (g : Fin n → Bool) => Fin.cons (α := fun _ : Fin (n+1) => Bool) false g)
    · intro g hg
      refine ⟨(mem_aug hk _).2 ?_, by simp⟩
      simpa [aug, G, gapSwitches] using hg
    · exact fun i => Or.inr ⟨i.succ, false, fun _ _ => Fin.cons_succ ..⟩

theorem odd_switch_shattered_iff {n k : ℕ} (hn : 1 ≤ n) (hk : Odd k) (d : ℕ) :
    ShatteredTree _ (C n k) (d+1) ↔ ShatteredTree _ (G k n) d := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h (x : Fin (n+1)) (b : Bool) :
      ShatteredTree _ (slice (C (n+1) k) x b) d ↔ ShatteredTree _ (G k (n+1)) d := by
    obtain ⟨_, hs, he⟩ := slice_isomorphism hk x b
    exact (he _ d).trans (hs.symm ▸ fixed_gap hk)
  exact ⟨fun ⟨x, hl, _⟩ => (h x false).1 hl,
    fun hg => ⟨0, (h 0 false).2 hg, (h 0 true).2 hg⟩⟩

private theorem tree_bound {X : Type*} [Finite X] {H : Set (X → Bool)} {d}
    (h : ShatteredTree X H d) : d ≤ H.ncard := by
  induction d generalizing H with
  | zero => omega
  | succ d ih =>
    obtain ⟨x, hl, hr⟩ := h
    obtain ⟨f, hf, ht⟩ := inhabited_tree hr
    have hlt : slice H x false ⊂ H := by
      refine ⟨fun _ hx => hx.1, fun he => ?_⟩
      have := (he hf).2
      simp_all
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hl) (Set.ncard_lt_ncard hlt))

theorem ldim_C_odd {n k : ℕ} (hn : 1 ≤ n) (hk : Odd k) :
    ldim _ (C n k) = 1 + ldim _ (G k n) := by
  have bdd {X : Type} [Finite X] (H : Set (X → Bool)) :
      BddAbove {d | ShatteredTree _ H d} := ⟨H.ncard, fun _ => tree_bound⟩
  have free_false (l : List Bool) (h : ∀ x ∈ l, x = false) : free false l = 0 := by
    induction l with
    | nil => rfl
    | cons x l ih =>
      have hx := h x (by simp)
      subst x
      simpa [free, edge] using ih (fun y hy => h y (by simp [hy]))
  have g0 : ShatteredTree _ (G k n) 0 := by
    refine ⟨fun _ => false, ?_⟩
    change walk false _ true ≤ k
    rw [walk_free, free_false _ (by simp)]
    obtain ⟨t, ht⟩ := hk
    simp [edge]; omega
  have topG : ShatteredTree _ (G k n) (ldim _ (G k n)) :=
    Nat.sSup_mem ⟨0, g0⟩ (bdd _)
  have hc := (odd_switch_shattered_iff hn hk _).2 topG
  apply le_antisymm
  · apply csSup_le (s := {d | ShatteredTree _ (C n k) d}) ⟨ldim _ (G k n) + 1, hc⟩
    intro d hd
    cases d with
    | zero => omega
    | succ d =>
      have hle : d ≤ ldim _ (G k n) := le_csSup (bdd _) ((odd_switch_shattered_iff hn hk d).1 hd)
      omega
  · rw [Nat.add_comm]
    exact le_csSup (bdd _) hc

/-- Linear interpolation of the dyadic logarithm on positive measures. -/
noncomputable def L_tilde (p : ℕ) : ℝ :=
  if p = 0 then 0 else (Nat.log 2 p : ℝ) + p / (2:ℝ)^(Nat.log 2 p) - 1

noncomputable def cutReward (u v : ℕ) : ℝ := 1 + (L_tilde u + L_tilde v) / 2

def greedySplit (p : ℕ) : ℕ × ℕ :=
  let t := Nat.log 2 p
  let a := max (2^(t-1)) (p - 2^t)
  (a, p-a)

private theorem split_shape {p : ℕ} (hp : 2 ≤ p) :
    ∃ m, let q := 2^m
         let (a,b) := greedySplit p
         a+b = p ∧ q ≤ a ∧ a ≤ 2*q ∧ q ≤ b ∧ b ≤ 2*q ∧ (a=q ∨ b=2*q) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (Nat.log_pos (by decide : 1 < 2) hp))
  have hlo := Nat.pow_log_le_self 2 (by omega : p ≠ 0)
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) p
  rw [hm, pow_succ] at hlo
  rw [hm, pow_succ, pow_succ] at hhi
  refine ⟨m, ?_⟩
  simp only [greedySplit, hm, Nat.add_one_sub_one, pow_succ]
  omega

private theorem split_valid {p : ℕ} (hp : 2 ≤ p) :
    let (a,b) := greedySplit p
    0 < a ∧ 0 < b ∧ a+b=p ∧ a<p ∧ b<p := by
  obtain ⟨m, hm⟩ := split_shape hp
  dsimp only at hm ⊢
  have := Nat.two_pow_pos m
  omega

def rodCuts (p : ℕ) : Multiset ℕ :=
  if _hp : 2 ≤ p then p ::ₘ (rodCuts (greedySplit p).1 + rodCuts (greedySplit p).2) else 0
termination_by p
decreasing_by all_goals have := split_valid _hp; decreasing_tactic

def greedyCuts (S : Multiset ℕ) := S.bind rodCuts

def sortedDesc (S : Multiset ℕ) := S.sort (· ≥ ·)

private noncomputable def discount (w : ℕ → ℝ) : List ℕ → ℝ
  | [] => 0
  | x :: l => (w x + discount w l) / 2

noncomputable def greedyVal (S : Multiset ℕ) : ℝ :=
  discount L_tilde (sortedDesc (greedyCuts S))

theorem discounted_sum (w : ℕ → ℝ) (l : List ℕ) :
    discount w l = ∑ i : Fin l.length, (1/2 : ℝ)^(i.val+1) * w l[i.val] := by
  induction l with
  | nil => simp [discount]
  | cons x l ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [discount, ih, Fin.val_zero, zero_add, pow_one, List.getElem_cons_zero,
      Fin.val_succ, List.getElem_cons_succ]
    simp_rw [pow_succ (1/2:ℝ) (_+1)]
    have scale (a b : ℝ) : a * (1 / 2) * b = (a*b)/2 := by ring
    simp_rw [scale]
    rw [← Finset.sum_div]
    ring

theorem greedyVal_eq_sum (S : Multiset ℕ) :
    let l := sortedDesc (greedyCuts S)
    greedyVal S = ∑ i : Fin l.length, (1/2 : ℝ)^(i.val+1) * L_tilde l[i.val] :=
  discounted_sum L_tilde _

-- At scale h the mass and the capped root contribution both have denominator h.
private def mass (h p : ℕ) := p-h
private def chip (h p : ℕ) := min h (mass h p)

/-- Sum of the excesses above threshold c in a packing of x into slots of size h. -/
private def packed (h c x : ℕ) := x/h * (h-c) + (x%h-c)

private theorem packed_repr {h c q r : ℕ} (hh : 0 < h) (hr : r < h) :
    packed h c (r + h*q) = q*(h-c)+(r-c) := by
  simp [packed, Nat.add_mul_div_left, Nat.add_mul_mod_self_left, Nat.div_eq_of_lt hr,
    Nat.mod_eq_of_lt hr, hh]

private theorem packed_small {h c x : ℕ} (hh : 0<h) (hx : x≤h) :
    packed h c x = x-c := by
  rcases lt_or_eq_of_le hx with hx | rfl
  · simp [packed, Nat.div_eq_of_lt hx, Nat.mod_eq_of_lt hx]
  · simp [packed, hh]

private theorem packed_shift {h : ℕ} (hh : 0<h) (c x q : ℕ) :
    packed h c (x+h*q) = packed h c x + q*(h-c) := by
  simp [packed, Nat.add_mul_div_left, hh, Nat.add_mul, Nat.add_assoc, Nat.add_comm]

private theorem packed_super {h : ℕ} (hh : 0<h) (c x y : ℕ) :
    packed h c x + packed h c y ≤ packed h c (x+y) := by
  let r := x%h
  let s := y%h
  have hr : r<h := Nat.mod_lt x hh
  have hs : s<h := Nat.mod_lt y hh
  have he : x+y = r+s + h*(x/h+y/h) := by
    dsimp [r,s]
    rw [Nat.mul_add]
    have := Nat.mod_add_div x h
    have := Nat.mod_add_div y h
    omega
  rw [he, packed_shift hh, Nat.add_mul]
  change _ * _ + (r-c) + (_ * _ + (s-c)) ≤ _
  by_cases hlt : r+s<h
  · rw [packed_small hh (Nat.le_of_lt hlt)]
    omega
  · have he' : r+s = (r+s-h)+h*1 := by omega
    rw [he', packed_repr hh (by omega), Nat.one_mul]
    omega

private theorem packed_lip {h : ℕ} (hh : 0<h) (c x z : ℕ) :
    packed h c (x+z) ≤ packed h c x + z := by
  induction z with
  | zero => simp
  | succ z ih =>
    let w := x+z
    have hw : w = w%h + h*(w/h) := (Nat.mod_add_div w h).symm
    have hr := Nat.mod_lt w hh
    have he : w+1 = (w%h+1)+h*(w/h) := by omega
    change packed h c (w+1) ≤ _
    rw [he, packed_shift hh, packed_small hh (by omega)]
    change w/h*(h-c)+(w%h-c) ≤ packed h c x + z at ih
    omega

private def losses (h c : ℕ) (s : Multiset ℕ) :=
  (s.map (fun p => chip h p - c)).sum

private theorem dyadic_separation {i m : ℕ} (hi : ¬ i ≤ m) :
    2*2^m ≤ 2^i := by
  have := Nat.pow_le_pow_right (by decide : 0 < 2) (show m+1 ≤ i by omega)
  simpa [pow_succ, Nat.mul_comm] using this

/-- At every dyadic scale, the greedy descendants have the same threshold
excesses as the fully packed list. One greedy child is dyadically aligned. -/
private theorem losses_rod (i c p : ℕ) :
    losses (2^i) c (rodCuts p) = packed (2^i) c (mass (2^i) p) := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    let h := 2^i
    have hh : 0 < h := Nat.two_pow_pos i
    change losses h c _ = packed h c (mass h p)
    rw [rodCuts]
    split_ifs with hp
    · obtain ⟨m, hm⟩ := split_shape hp
      let q := 2^m
      let a := (greedySplit p).1
      let b := (greedySplit p).2
      obtain ⟨hab, hqa, haq, hqb, hbq, he⟩ :
          a+b=p ∧ q≤a ∧ a≤2*q ∧ q≤b ∧ b≤2*q ∧ (a=q ∨ b=2*q) := hm
      have hv := split_valid hp
      have ha := ih a hv.2.2.2.1
      have hb := ih b hv.2.2.2.2
      change losses h c (p ::ₘ (rodCuts a + rodCuts b)) = _
      simp only [losses, Multiset.map_cons, Multiset.map_add, Multiset.sum_cons,
        Multiset.sum_add] at ha hb ⊢
      rw [ha, hb]
      change chip h p - c + (packed h c (mass h a) + packed h c (mass h b)) = _
      by_cases hi : i ≤ m
      · have hq : h ≤ q := Nat.pow_le_pow_right (by decide) hi
        have hd : h ∣ q := pow_dvd_pow 2 hi
        have hroot : chip h p = h := by unfold chip mass; omega
        have hmass : mass h p = (mass h a + mass h b) + h*1 := by unfold mass; omega
        have aligned (x y : ℕ) (hx : h ∣ x) :
            packed h c (mass h x + mass h y) =
              packed h c (mass h x) + packed h c (mass h y) := by
          obtain ⟨k, hk⟩ : h ∣ mass h x := Nat.dvd_sub hx (dvd_refl h)
          rw [hk, Nat.add_comm (h*k), packed_shift hh]
          simp [packed, hh, Nat.mul_comm, Nat.add_comm]
        have hpacks : packed h c (mass h a + mass h b) =
            packed h c (mass h a) + packed h c (mass h b) := by
          rcases he with he | he
          · exact aligned a b (he ▸ hd)
          · rw [Nat.add_comm (mass h a), Nat.add_comm (packed h c (mass h a))]
            exact aligned b a (he ▸ dvd_mul_of_dvd_right hd 2)
        rw [hroot, hmass, packed_shift hh, hpacks, Nat.one_mul, Nat.add_comm]
      · have hqh : 2*q ≤ h := dyadic_separation hi
        have hma : mass h a = 0 := by unfold mass; omega
        have hmb : mass h b = 0 := by unfold mass; omega
        have hmp : mass h p ≤ h := by unfold mass; omega
        rw [hma,hmb, packed_small hh hmp]
        simp [chip, min_eq_right hmp, packed]
    · have hmp : mass h p = 0 := by unfold mass; omega
      simp [losses, hmp, packed]

private def prefixSum (j : ℕ) (l : List ℕ) := (l.take j).sum
private def excess (c : ℕ) (l : List ℕ) := (l.map (· - c)).sum

private theorem prefixSum_upper (c j : ℕ) (l : List ℕ) :
    prefixSum j l ≤ j*c + excess c l := by
  induction j generalizing l with
  | zero => simp [prefixSum]
  | succ j ih =>
    cases l with
    | nil => simp [prefixSum]
    | cons a l =>
      have := ih l
      simp only [prefixSum, excess, List.take_succ_cons, List.sum_cons, Nat.succ_mul,
        List.map_cons] at *
      omega

/-- On a descending list a threshold between the included and excluded
entries makes the prefix bound exact, including when the prefix is padded. -/
private theorem prefixSum_threshold (j M : ℕ) (l : List ℕ) (hs : l.Pairwise (· ≥ ·))
    (hM : ∀ x ∈ l, x ≤ M) : ∃ c ≤ M, prefixSum j l = j*c + excess c l := by
  induction j generalizing M l with
  | zero =>
    refine ⟨M, le_rfl, ?_⟩
    have hl : (l.map (· - M)).sum = 0 := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [Nat.sub_eq_zero_of_le (hM a (by simp)), zero_add]
        exact ih hs.tail (fun x hx => hM x (by simp [hx]))
    simp [prefixSum, excess, hl]
  | succ j ih =>
    cases l with
    | nil => exact ⟨0, Nat.zero_le _, by simp [prefixSum, excess]⟩
    | cons a l =>
      obtain ⟨c, hc, he⟩ := ih a l hs.tail (List.pairwise_cons.mp hs).1
      refine ⟨c, hc.trans (hM a (by simp)), ?_⟩
      simp only [prefixSum, excess, List.take_succ_cons, List.sum_cons, List.map_cons,
        Nat.succ_mul] at *
      omega

private theorem prefixSum_of_excess {l r : List ℕ} {e : ℕ} (hs : r.Pairwise (· ≥ ·))
    (he : ∀ c, excess c l ≤ excess c r + e) (j : ℕ) :
    prefixSum j l ≤ prefixSum j r + e := by
  obtain ⟨c, _, hc⟩ := prefixSum_threshold j r.sum r hs
    (fun x hx => List.single_le_sum (fun _ _ => Nat.zero_le _) x hx)
  have := prefixSum_upper c j l
  have := he c
  omega

private noncomputable def discNat := discount (fun p => (p : ℝ))

private theorem disc_nonneg (l : List ℕ) : 0 ≤ discNat l := by
  induction l with
  | nil => rfl
  | cons a l ih => change 0 ≤ ((a:ℝ) + discNat l)/2; positivity

/-- Uniform slack in all prefix sums costs at most half as much after discounting. -/
private theorem disc_prefixSum {l r : List ℕ} {e : ℕ}
    (he : ∀ j, prefixSum j l ≤ prefixSum j r + e) :
    discNat l ≤ discNat r + e/2 := by
  induction l generalizing r e with
  | nil => change 0 ≤ _; have := disc_nonneg r; positivity
  | cons a l ih =>
    let b := r.headD 0
    have hr : discNat r = ((b:ℝ) + discNat r.tail)/2 := by
      cases r <;> simp [discNat, discount, b]
    have hp (j : ℕ) : prefixSum (j+1) r = b + prefixSum j r.tail := by
      cases r <;> simp [prefixSum, b]
    have ht (j : ℕ) := he (j+1)
    simp only [prefixSum, List.take_succ_cons, List.sum_cons] at ht
    have bound (j : ℕ) : a+prefixSum j l ≤ b+prefixSum j r.tail+e := by
      rw [← hp]; exact ht j
    have hab := bound 0
    simp [prefixSum] at hab
    have hrec := ih (r := r.tail) (e := b+e-a) (fun j => by have := bound j; omega)
    rw [hr]
    change ((a:ℝ) + discNat l)/2 ≤ _
    rw [Nat.cast_sub hab, Nat.cast_add] at hrec
    have hrab : (a:ℝ) ≤ b+e := by exact_mod_cast hab
    linarith

private def chips (h : ℕ) (s : Multiset ℕ) := (sortedDesc s).map (chip h)

private theorem chips_sorted (h : ℕ) (s : Multiset ℕ) : (chips h s).Pairwise (· ≥ ·) := by
  exact (Multiset.pairwise_sort s (· ≥ ·)).map (chip h)
    (fun _ _ hxy => min_le_min_left _ (Nat.sub_le_sub_right hxy _))

private theorem chips_excess (h c : ℕ) (s : Multiset ℕ) :
    excess c (chips h s) = losses h c s := by
  unfold excess chips losses sortedDesc
  rw [List.map_map]
  have e := congrArg (fun t : Multiset ℕ => (t.map (fun p => chip h p - c)).sum)
    (Multiset.sort_eq s (· ≥ ·))
  exact e

private theorem losses_add (h c : ℕ) (s t : Multiset ℕ) :
    losses h c (s+t) = losses h c s + losses h c t := by simp [losses]

private noncomputable def scaleVal (h : ℕ) (s : Multiset ℕ) := discNat (chips h s)

private theorem scale_first (h p : ℕ) (s : Multiset ℕ) :
    (chip h p : ℝ) + scaleVal h s ≤ 2*scaleVal h (p ::ₘ s) := by
  have he (c : ℕ) : excess c (chip h p :: chips h s) ≤ excess c (chips h (p ::ₘ s)) + 0 := by
    change chip h p-c + excess c (chips h s) ≤ _
    simp [chips_excess, losses]
  have hb := disc_prefixSum (fun j => prefixSum_of_excess (chips_sorted _ _) he j)
  change ((chip h p : ℝ) + scaleVal h s)/2 ≤ scaleVal h (p ::ₘ s) + (0:ℕ)/2 at hb
  linarith

/-- Play the parent's capped contribution first, and bound the replacement
children by packing their combined mass above every threshold. -/
private theorem scale_cut (i p u v : ℕ) (huv : u+v=p) (hp : 2≤p) (A : Multiset ℕ) :
    let h := 2^i
    (chip h p : ℝ) + (mass h p : ℝ) - mass h u - mass h v ≤
      2*(2*scaleVal h (A+rodCuts p) - scaleVal h (A+(rodCuts u+rodCuts v))) := by
  let h := 2^i
  let B := rodCuts (greedySplit p).1 + rodCuts (greedySplit p).2
  have hh : 0<h := Nat.two_pow_pos i
  have hroot : rodCuts p = p ::ₘ B := by rw [rodCuts, dif_pos hp]
  have hres (c : ℕ) : losses h c B = packed h c (mass h p-chip h p) := by
    have he := losses_rod i c p
    rw [hroot] at he
    simp only [losses, Multiset.map_cons, Multiset.sum_cons] at he
    change chip h p-c+losses h c B = packed h c (mass h p) at he
    by_cases hx : mass h p ≤ h
    · rw [packed_small hh hx] at he
      simp only [chip, min_eq_right hx, Nat.sub_self] at he ⊢
      simp [packed]; omega
    · have hx' : chip h p = h := min_eq_left (by omega)
      have hx'' : mass h p = (mass h p-h)+h*1 := by omega
      conv_rhs at he => rw [hx'', packed_shift hh, Nat.one_mul]
      rw [hx'] at he ⊢
      omega
  let e := mass h u + mass h v - (mass h p - chip h p)
  have hmass : mass h p-chip h p ≤ mass h u+mass h v := by unfold mass chip; unfold mass; omega
  have he (c : ℕ) : excess c (chips h (A+(rodCuts u+rodCuts v))) ≤
      excess c (chips h (A+B)) + e := by
    simp only [chips_excess, losses_add, hres]
    have hu := losses_rod i c u
    have hv := losses_rod i c v
    change losses h c _ = packed h c (mass h u) at hu
    change losses h c _ = packed h c (mass h v) at hv
    rw [hu,hv]
    have hsum := packed_super hh c (mass h u) (mass h v)
    have hbound := packed_lip hh c (mass h p-chip h p) e
    have hx : mass h p-chip h p + e = mass h u+mass h v := by dsimp [e]; omega
    rw [hx] at hbound
    omega
  have hchild := disc_prefixSum (fun j => prefixSum_of_excess (chips_sorted _ _) he j)
  change scaleVal h _ ≤ scaleVal h (A+B) + (e:ℝ)/2 at hchild
  have hf := scale_first h p (A+B)
  rw [hroot, Multiset.add_cons]
  change (chip h p : ℝ) + (mass h p : ℝ) - mass h u - mass h v ≤ _
  have hb : chip h p ≤ mass h p := min_le_right .. 
  dsimp only [e] at hchild
  rw [Nat.cast_sub hmass, Nat.cast_sub hb, Nat.cast_add] at hchild
  linarith

private theorem scale_sums {p N : ℕ} (hp : 0<p) (hN : p≤N) :
    (∑ i ∈ Finset.range N, (chip (2^i) p : ℝ) / (2:ℝ)^i) = L_tilde p ∧
    (∑ i ∈ Finset.range N, (mass (2^i) p : ℝ) / (2:ℝ)^i) = 2*p-2-L_tilde p := by
  have low (t : ℕ) (ht : 2^t ≤ p) :
      (∑ i ∈ Finset.range t, (chip (2^i) p : ℝ) / (2:ℝ)^i) = t ∧
      (∑ i ∈ Finset.range t, (mass (2^i) p : ℝ) / (2:ℝ)^i) =
        2*p-2*p/(2:ℝ)^t-t := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ] at ht
      obtain ⟨ha,hb⟩ := ih (by omega)
      have hchip : chip (2^t) p = 2^t := by unfold chip mass; omega
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ha, hb, hchip]
      simp only [mass, Nat.cast_sub (show 2^t ≤ p by omega), Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_succ, pow_succ]
      constructor <;> (field_simp; try ring)
  let t := Nat.log 2 p
  have hlo : 2^t ≤ p := Nat.pow_log_le_self 2 hp.ne'
  have hhi : p < 2^(t+1) := Nat.lt_pow_succ_log_self (by decide) p
  have hbase : t+1 ≤ N := by have := Nat.log_lt_self 2 hp.ne'; dsimp [t]; omega
  clear hN
  induction N, hbase using Nat.le_induction with
  | base =>
    obtain ⟨ha,hb⟩ := low t hlo
    have hchip : chip (2^t) p = p-2^t := by unfold chip mass; rw [pow_succ] at hhi; omega
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ha, hb, hchip]
    simp only [mass, Nat.cast_sub hlo, Nat.cast_pow, Nat.cast_ofNat, L_tilde,
      if_neg hp.ne']
    change _ = (t:ℝ) + p/(2:ℝ)^t - 1 ∧ _ = 2*p-2-((t:ℝ)+p/(2:ℝ)^t-1)
    constructor <;> field_simp <;> ring
  | succ N hN ih =>
    have hn : p ≤ 2^N := hhi.le.trans (Nat.pow_le_pow_right (by decide) hN)
    have h0 : mass (2^N) p = 0 := Nat.sub_eq_zero_of_le hn
    simp only [Finset.sum_range_succ, chip, h0, Nat.min_zero, Nat.cast_zero, zero_div, add_zero]
    exact ih

private theorem rod_bounds {p z : ℕ} (hz : z ∈ rodCuts p) : 2≤z ∧ z≤p := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    rw [rodCuts] at hz
    split_ifs at hz with hp
    · obtain ⟨_, _, _, ha, hb⟩ := split_valid hp
      simp only [Multiset.mem_cons, Multiset.mem_add] at hz
      rcases hz with rfl | hz | hz
      · exact ⟨hp, le_rfl⟩
      · obtain ⟨hlo,hhi⟩ := ih _ ha hz
        exact ⟨hlo, hhi.trans ha.le⟩
      · obtain ⟨hlo,hhi⟩ := ih _ hb hz
        exact ⟨hlo, hhi.trans hb.le⟩
    · simp at hz

private theorem discount_scales {N : ℕ} (l : List ℕ) (hl : ∀ p ∈ l, 0<p ∧ p≤N) :
    discount L_tilde l =
      ∑ i ∈ Finset.range N, discNat (l.map (chip (2^i))) / (2:ℝ)^i := by
  induction l with
  | nil => simp [discNat, discount]
  | cons p l ih =>
    obtain ⟨hp, hN⟩ := hl p (by simp)
    have ht := ih (fun z hz => hl z (by simp [hz]))
    rw [discount, ht, ← (scale_sums hp hN).1]
    simp only [List.map_cons]
    change _ = ∑ i ∈ Finset.range N, (((chip (2^i) p:ℝ)+discNat (l.map (chip (2^i))))/2) / _
    have hd (a b t : ℝ) : ((a+b)/2)/t = (a/t+b/t)/2 := by ring
    simp_rw [hd]
    rw [← Finset.sum_div, Finset.sum_add_distrib]

private theorem val_scales {N : ℕ} (s : Multiset ℕ) (hs : ∀ p ∈ s, p ≤ N) :
    greedyVal s = ∑ i ∈ Finset.range N, scaleVal (2^i) (greedyCuts s) / (2:ℝ)^i := by
  apply discount_scales
  intro z hz
  obtain ⟨p,hp,hz⟩ := Multiset.mem_bind.mp ((Multiset.mem_sort _).mp hz)
  obtain ⟨hlo,hhi⟩ := rod_bounds hz
  exact ⟨by omega, hhi.trans (hs _ hp)⟩

def afterCut (S : Multiset ℕ) (p u v : ℕ) := (S.erase p) + {u,v}

private theorem mem_after {S : Multiset ℕ} {p u v x : ℕ} :
    x ∈ afterCut S p u v ↔ x ∈ S.erase p ∨ x = u ∨ x = v := by
  change x ∈ S.erase p + (u ::ₘ v ::ₘ 0) ↔ _
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.notMem_zero, or_false]

private theorem cuts_after {S : Multiset ℕ} {p : ℕ} (hp : p ∈ S) (u v : ℕ) :
    greedyCuts S = greedyCuts (S.erase p) + rodCuts p ∧
    greedyCuts (afterCut S p u v) = greedyCuts (S.erase p) + (rodCuts u+rodCuts v) := by
  constructor
  · conv_lhs => rw [← Multiset.cons_erase hp]
    simp [greedyCuts, add_comm]
  · simp [afterCut, greedyCuts, add_comm, add_assoc]

theorem greedy_supersolution (S : Multiset ℕ) (_hS : ∀ x ∈ S, 1 ≤ x)
    {p u v : ℕ} (hp : p ∈ S) (hu : 1≤u) (hv : 1≤v) (huv : u+v=p) :
    cutReward u v ≤ 2*greedyVal S - greedyVal (afterCut S p u v) := by
  let N := S.sum
  have hN (x : ℕ) (hx : x∈S) : x≤N := Multiset.le_sum_of_mem hx
  have hpN := hN p hp
  have hsN (x : ℕ) (hx : x ∈ afterCut S p u v) : x≤N := by
    rw [mem_after] at hx
    rcases hx with hx | rfl | rfl
    · exact hN x (Multiset.mem_of_mem_erase hx)
    · omega
    · omega
  obtain ⟨h1,h2⟩ := cuts_after hp u v
  have hi (i : ℕ) (hi : i∈Finset.range N) := div_le_div_of_nonneg_right
    (scale_cut i p u v huv (by omega) (greedyCuts (S.erase p))) (by positivity : 0 ≤ (2:ℝ)^i)
  simp only [← h1, ← h2] at hi
  have hb := Finset.sum_le_sum hi
  simp only [sub_div, add_div, mul_div_assoc, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hb
  obtain ⟨hchip, hmass⟩ := scale_sums (by omega : 0<p) hpN
  rw [hchip, hmass, (scale_sums hu (show u≤N by omega)).2, (scale_sums hv (show v≤N by omega)).2,
    ← val_scales S hN, ← val_scales _ hsN] at hb
  have hreal : (u:ℝ)+v=p := by exact_mod_cast huv
  unfold cutReward
  linarith

def cutsLeft (S : Multiset ℕ) := (S.map (· - 1)).sum

structure Cut (S : Multiset ℕ) where
  p : ℕ
  u : ℕ
  v : ℕ
  mem : p ∈ S
  left_pos : 1≤u
  right_pos : 1≤v
  total : u+v=p

def Cut.next {S : Multiset ℕ} (a : Cut S) := afterCut S a.p a.u a.v

private theorem Cut.decreases {S : Multiset ℕ} (a : Cut S) : cutsLeft a.next < cutsLeft S := by
  conv_rhs => rw [← Multiset.cons_erase a.mem]
  simp [Cut.next, afterCut, cutsLeft]
  have := a.total
  have := a.left_pos
  have := a.right_pos
  omega

private theorem Cut.positive {S : Multiset ℕ} (a : Cut S) (hs : ∀ x ∈ S, 1 ≤ x) :
    ∀ x ∈ a.next, 1 ≤ x := by
  intro x hx
  rw [Cut.next, mem_after] at hx
  rcases hx with hx | rfl | rfl
  · exact hs _ (Multiset.mem_of_mem_erase hx)
  · exact a.left_pos
  · exact a.right_pos

/-- Stopping earns zero. Every other option discounts the immediate reward and
continuation together. Each legal cut removes exactly one remaining cut. -/
noncomputable def bellmanOpt (S : Multiset ℕ) : ℝ :=
  sSup (insert 0 (Set.range (fun a : Cut S =>
    (cutReward a.u a.v + bellmanOpt a.next)/2)))
termination_by cutsLeft S
decreasing_by exact a.decreases

theorem bellmanOpt_terminal {S : Multiset ℕ} (hS : ∀ p ∈ S, p ≤ 1) : bellmanOpt S = 0 := by
  have noCut (a : Cut S) : False := by
    have := hS a.p a.mem
    have := a.total
    have := a.left_pos
    have := a.right_pos
    omega
  rw [bellmanOpt]
  have he (f : Cut S → ℝ) : Set.range f = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨a, rfl⟩
    exact noCut a
  rw [he]
  simp

private theorem L_band {p m : ℕ} (hlo : 2^m≤p) (hhi : p≤2^(m+1)) :
    L_tilde p = (m:ℝ)+p/(2:ℝ)^m-1 := by
  have hp : p ≠ 0 := by have := Nat.two_pow_pos m; omega
  unfold L_tilde
  rw [if_neg hp]
  rcases lt_or_eq_of_le hhi with ht | rfl
  · rw [Nat.log_eq_of_pow_le_of_lt_pow hlo ht]
  · rw [Nat.log_pow (by decide : 1<2)]
    push_cast
    rw [pow_succ]
    field_simp
    ring

private theorem greedy_reward {p : ℕ} (hp : 2≤p) :
    cutReward (greedySplit p).1 (greedySplit p).2 = L_tilde p := by
  obtain ⟨m, hm⟩ := split_shape hp
  change (greedySplit p).1 + (greedySplit p).2 = p ∧ 2^m ≤ (greedySplit p).1 ∧
    (greedySplit p).1 ≤ 2*2^m ∧ 2^m ≤ (greedySplit p).2 ∧
    (greedySplit p).2 ≤ 2*2^m ∧ _ at hm
  obtain ⟨hab, ha, ha', hb, hb', _⟩ := hm
  have hpow : 2^(m+1) = 2*2^m := by rw [pow_succ, Nat.mul_comm]
  have hpow' : 2^(m+1+1) = 2*(2*2^m) := by rw [pow_succ, hpow, Nat.mul_comm]
  unfold cutReward
  rw [L_band (m := m) ha (by omega), L_band (m := m) hb (by omega),
    L_band (m := m+1) (by omega) (by omega)]
  have he : ((greedySplit p).1:ℝ)+(greedySplit p).2=p := by exact_mod_cast hab
  rw [← he, pow_succ, Nat.cast_succ]
  ring

private theorem greedy_nonneg (S : Multiset ℕ) : 0 ≤ greedyVal S := by
  rw [val_scales (N := S.sum) S (fun _ hx => Multiset.le_sum_of_mem hx)]
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (disc_nonneg _) (by positivity)

private theorem greedy_terminal {S : Multiset ℕ} (hS : ∀ p ∈ S, p≤1) : greedyVal S = 0 := by
  have h0 : greedyCuts S = 0 := by
    unfold greedyCuts
    rw [← Multiset.bind_zero (s := S) (β := ℕ)]
    apply Multiset.bind_congr
    intro p hp
    rw [rodCuts, dif_neg (by have := hS p hp; omega)]
  simp [greedyVal, h0, sortedDesc, discount]

def Cut.IsGreedy {S : Multiset ℕ} (a : Cut S) : Prop :=
  (∀ z ∈ S, z ≤ a.p) ∧ (a.u, a.v) = greedySplit a.p

/-- The greedy schedule cuts a largest active rod and repeats on the new forest. -/
private theorem greedy_step {S : Multiset ℕ} (hS : ∃ p ∈ S, 2≤p) :
    ∃ a : Cut S, a.IsGreedy ∧ greedyVal S = (cutReward a.u a.v + greedyVal a.next)/2 := by
  obtain ⟨p,hp,hp2⟩ := hS
  have hne : S.toFinset.Nonempty := ⟨p, by simpa using hp⟩
  let m := S.toFinset.max' hne
  have hm : m ∈ S := Multiset.mem_toFinset.mp (Finset.max'_mem _ hne)
  have hmax (z : ℕ) (hz : z∈S) : z≤m := Finset.le_max' _ _ (by simpa using hz)
  have hm2 : 2≤m := hp2.trans (hmax p hp)
  obtain ⟨ha, hb, hab, hlt, hlt'⟩ := split_valid hm2
  let a : Cut S := ⟨m, (greedySplit m).1, (greedySplit m).2, hm, ha, hb, hab⟩
  refine ⟨a, ⟨hmax, rfl⟩, ?_⟩
  have hcuts : greedyCuts S = m ::ₘ greedyCuts a.next := by
    obtain ⟨h1,h2⟩ := cuts_after hm a.u a.v
    rw [h1, rodCuts, dif_pos hm2, Multiset.add_cons, ← h2]
    rfl
  have hmax' (z : ℕ) (hz : z ∈ greedyCuts a.next) : z ≤ m := by
    obtain ⟨q,hq,hz⟩ := Multiset.mem_bind.mp hz
    apply (rod_bounds hz).2.trans
    change q ∈ afterCut S m _ _ at hq
    rw [mem_after] at hq
    rcases hq with hq | rfl | rfl
    · exact hmax _ (Multiset.mem_of_mem_erase hq)
    · exact hlt.le
    · exact hlt'.le
  change discount L_tilde (sortedDesc (greedyCuts S)) = _
  rw [hcuts, sortedDesc, Multiset.sort_cons _ _ _ hmax']
  change (L_tilde m + greedyVal a.next)/2 = _
  rw [← greedy_reward hm2]

theorem conjecture_31_bellman_eq_greedy (S : Multiset ℕ) (hs : ∀ x ∈ S, 1≤x) :
    bellmanOpt S = greedyVal S := by
  rw [bellmanOpt]
  have hrec (a : Cut S) := conjecture_31_bellman_eq_greedy a.next (a.positive hs)
  have hupper : ∀ r ∈ insert 0 (Set.range (fun a : Cut S =>
      (cutReward a.u a.v + bellmanOpt a.next)/2)), r ≤ greedyVal S := by
    rintro r (rfl | ⟨a,rfl⟩)
    · exact greedy_nonneg _
    · change (cutReward a.u a.v + bellmanOpt a.next)/2 ≤ _
      rw [hrec]
      have := greedy_supersolution S hs a.mem a.left_pos a.right_pos a.total
      change _ ≤ 2*greedyVal S - greedyVal a.next at this
      linarith
  apply le_antisymm (csSup_le (s := insert (0:ℝ) (Set.range (fun a : Cut S =>
    (cutReward a.u a.v + bellmanOpt a.next)/2))) ⟨0, Or.inl rfl⟩ hupper)
  apply le_csSup ⟨_, hupper⟩
  by_cases h : ∃ p∈S, 2≤p
  · obtain ⟨a,_,ha⟩ := greedy_step h
    exact Or.inr ⟨a, (congrArg (fun v => (cutReward a.u a.v + v)/2) (hrec a)).trans ha.symm⟩
  · exact Or.inl (greedy_terminal (fun p hp => by by_contra! hn; exact h ⟨p,hp,hn⟩))
termination_by cutsLeft S
decreasing_by exact a.decreases

inductive Strategy : Multiset ℕ → Type
  | stop (S) : Strategy S
  | cut {S} (a : Cut S) (next : Strategy a.next) : Strategy S

noncomputable def Strategy.value {S : Multiset ℕ} : Strategy S → ℝ
  | .stop _ => 0
  | .cut a t => (cutReward a.u a.v + t.value)/2

theorem strategy_le_greedy {S} (s : Strategy S) (hs : ∀ x ∈ S, 1≤x) :
    s.value ≤ greedyVal S := by
  induction s with
  | stop => exact greedy_nonneg _
  | cut a t ih =>
    have h := ih (a.positive hs)
    have h' := greedy_supersolution _ hs a.mem a.left_pos a.right_pos a.total
    change _ ≤ 2*greedyVal _ - greedyVal a.next at h'
    change (_ + t.value)/2 ≤ _
    linarith

def Strategy.IsGreedy {S : Multiset ℕ} : Strategy S → Prop
  | .stop s => ∀ p ∈ s, p ≤ 1
  | .cut a t => a.IsGreedy ∧ t.IsGreedy

theorem greedy_attained (S : Multiset ℕ) :
    ∃ t : Strategy S, t.IsGreedy ∧ t.value = greedyVal S := by
  by_cases h : ∃ p ∈ S, 2≤p
  · obtain ⟨a,hg,ha⟩ := greedy_step h
    obtain ⟨t, htg, ht⟩ := greedy_attained a.next
    exact ⟨.cut a t, ⟨hg,htg⟩, by change (_+t.value)/2 = _; rw [ht, ha]⟩
  · have hstop (p) (hp : p ∈ S) : p ≤ 1 := by by_contra! hn; exact h ⟨p,hp,hn⟩
    exact ⟨.stop _, hstop, (greedy_terminal hstop).symm⟩
termination_by cutsLeft S
decreasing_by exact a.decreases

#print axioms ldim_C_odd
#print axioms odd_switch_shattered_iff
#print axioms greedy_supersolution
#print axioms conjecture_31_bellman_eq_greedy

end LittlestoneIntervals

