import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic

/-!
# Tree stacking in graph pebbling

Csernák and Soukup, arXiv:2610.09650, Definitions 2.1, 3.1 and 5.1.
A move spends two pebbles and delivers one across an edge. Both thresholds
take the least qualifying size at least two.

* `conjecture_5_6` identifies the stacking number of a finite tree.
* `P4.literal_ASH_fails` separates the two thresholds on the four-vertex path.
* `G5.clearing_witness` certifies the size-sixteen obstruction to clearing.
-/

namespace CsernakSoukup

open Finset Relation SimpleGraph

variable {V : Type*}

abbrev Config (V : Type*) := V → ℕ

def size [Fintype V] (c : Config V) : ℕ := ∑ v, c v

def transfer [DecidableEq V] (c : Config V) (u v : V) : Config V :=
  fun x ↦ if x = u then c x - 2 else if x = v then c x + 1 else c x

def Move [DecidableEq V] (G : SimpleGraph V) (c d : Config V) : Prop :=
  ∃ u v, G.Adj u v ∧ 2 ≤ c u ∧ d = transfer c u v

def Stacked (c : Config V) : Prop := ∃ v, 0 < c v ∧ ∀ u, u ≠ v → c u = 0

def AlmostStacked (c : Config V) : Prop := ∃ v, ∀ u, u ≠ v → c u ≤ 1

def Stackable [DecidableEq V] (G : SimpleGraph V) (c : Config V) : Prop :=
  ∃ d, ReflTransGen (Move G) c d ∧ Stacked d

def Good [Fintype V] [DecidableEq V] (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ c, size c = n → Stackable G c

def AlmostGood [Fintype V] [DecidableEq V] (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ c, size c = n → AlmostStacked c → Stackable G c

noncomputable def stack [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sInf {n | 2 ≤ n ∧ Good G n}

noncomputable def almostStack [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sInf {n | 2 ≤ n ∧ AlmostGood G n}

noncomputable def rootEstimate [Fintype V] (G : SimpleGraph V) (r : V) : ℕ := by
  classical
  exact (∑ v, if v = r ∨ 1 < G.degree v then G.degree v * 2 ^ G.dist r v else 0) +
    (univ.filter fun v ↦ v ≠ r ∧ G.degree v = 1).card

noncomputable def estim [Fintype V] (G : SimpleGraph V) : ℕ :=
  max 2 (1 + univ.sup (rootEstimate G))

theorem stackable_iff [DecidableEq V] {G : SimpleGraph V} {c : Config V} :
    Stackable G c ↔ Stacked c ∨ ∃ d, Move G c d ∧ Stackable G d := by
  constructor
  · rintro ⟨d, h, hd⟩
    obtain rfl | ⟨e, he, hed⟩ := h.cases_head
    · exact Or.inl hd
    · exact Or.inr ⟨e, he, d, hed, hd⟩
  · rintro (h | ⟨d, h, e, he, hs⟩)
    · exact ⟨c, .refl, h⟩
    · exact ⟨e, he.head h, hs⟩

section Moves

variable [DecidableEq V] {G : SimpleGraph V}

def pile (u : V) (k : ℕ) : Config V := fun v ↦ if v = u then k else 0

@[simp] theorem pile_zero (u : V) : pile u 0 = 0 := by ext; simp [pile]

theorem pile_add (u : V) (a b : ℕ) : pile u (a+b) = pile u a + pile u b := by
  ext v; by_cases h : v = u <;> simp [pile, h]

abbrev Reach (G : SimpleGraph V) := ReflTransGen (Move G)

private theorem frame {c d : Config V} (h : Reach G c d) (b : Config V) :
    Reach G (c + b) (d + b) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih =>
    obtain ⟨u,v,he,hn,rfl⟩ := h
    apply ih.tail
    refine ⟨u,v,he,by simp; omega, ?_⟩
    ext x
    by_cases hx : x = u
    · subst x; simp [transfer]; omega
    · by_cases hy : x = v <;> simp [transfer,hx,hy,he.ne.symm, Nat.add_right_comm]

private theorem batch {u v : V} (h : G.Adj u v) (n : ℕ) :
    Reach G (pile u (2*n)) (pile v n) := by
  induction n with
  | zero => simp; exact .refl
  | succ n ih =>
    have one : Reach G (pile u 2) (pile v 1) := by
      apply ReflTransGen.single
      refine ⟨u,v,h,by simp [pile],?_⟩
      ext x
      by_cases hu : x = u <;> by_cases hv : x = v <;> simp_all [transfer,pile]
    rw [Nat.mul_succ, pile_add, pile_add]
    exact (frame ih _).trans (by simpa [add_comm] using frame one (pile v n))

private theorem absorb {u v : V} (he : G.Adj u v) (n : ℕ) (hn : 0 < n) :
    Reach G (pile u (n+1) + pile v 1) (pile u n) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h₁ := frame (batch he 1) (pile u k + pile v 1)
  have h₂ := frame (batch he.symm 1) (pile u k)
  simp only [Nat.mul_one] at h₁ h₂
  rw [show pile v 2 = pile v 1 + pile v 1 from pile_add v 1 1] at h₂
  rw [show k+1+1 = k+2 by omega, pile_add, pile_add u k 1]
  apply ReflTransGen.trans (b := pile v 1 + (pile u k + pile v 1))
  · convert h₁ using 1; abel
  · convert h₂ using 1 <;> abel

/-- A subtree can accept an external supply at its root and deliver its computed balance. -/
def Solves (G : SimpleGraph V) (c : Config V) (u : V) (z : ℤ) : Prop :=
  ∀ d : ℕ, 1 ≤ z + d → Reach G (c + pile u d) (pile u (z + d).toNat)

theorem solves_pile (u : V) (n : ℕ) : Solves G (pile u n) u n := by
  intro d _
  rw [← pile_add, ← Nat.cast_add, Int.toNat_natCast]

def tau (z : ℤ) : ℤ := if z ≤ 1 then 2*z-3 else z/2 - z%2

theorem solves_merge {u v : V} {a b : Config V} {x y : ℤ} (he : G.Adj u v)
    (ha : Solves G a u x) (hb : Solves G b v y) :
    Solves G (a+b) u (x + tau y) := by
  intro d hd
  -- A solvent child pays first. For a deficient child the parent first sends
  -- enough pebbles for balance one, then absorbs that last pebble in two moves.
  by_cases hy : 1 ≤ y
  · let k := y.toNat / 2
    let j := y.toNat % 2
    have hj : j = 0 ∨ j = 1 := by dsimp [j]; omega
    have hτ : tau y = (k : ℤ) - j := by unfold tau k j; split <;> omega
    have hy' : y.toNat = 2*k+j := by dsimp [k,j]; omega
    have h₁ := frame (hb 0 (by omega)) (a + pile u d)
    simp only [Nat.cast_zero, add_zero, pile_zero] at h₁
    have h₂ := frame (batch he.symm k) (pile v j + (a + pile u d))
    have h₃ := frame (ha (d+k) (by omega)) (pile v j)
    have hr : Reach G ((a+b)+pile u d) (pile u (x+(d+k : ℕ)).toNat + pile v j) := by
      apply ReflTransGen.trans (b := pile v y.toNat + (a + pile u d))
      · convert h₁ using 1; abel
      apply ReflTransGen.trans (b := pile u k + (pile v j + (a+pile u d)))
      · convert h₂ using 1
        rw [hy',pile_add]; abel
      · convert h₃ using 1
        rw [pile_add]; abel
    obtain hj | hj := hj
    · rw [hj,pile_zero,add_zero] at hr
      convert hr using 2
      push_cast; omega
    · rw [hj] at hr
      let n := (x + tau y + d).toNat
      have hh : (x+(d+k : ℕ)).toNat = n+1 := by dsimp [n]; omega
      rw [hh] at hr
      exact hr.trans (absorb he n (by dsimp [n]; omega))
  · let k := (1-y).toNat
    let n := (x + tau y + d).toNat
    have ht : tau y = -(2*(k : ℤ))-1 := by simp [tau, show y ≤ 1 by omega,k]; omega
    have h₁ := frame (ha d (by omega)) b
    have h₂ := frame (batch he k) (pile u (n+1) + b)
    have h₃ := frame (hb k (by dsimp [k]; omega)) (pile u (n+1))
    have hh : (x+d).toNat = 2*k + (n+1) := by dsimp [n]; omega
    have hk : (y+k).toNat = 1 := by dsimp [k]; omega
    rw [hh,pile_add] at h₁
    rw [hk] at h₃
    apply ReflTransGen.trans (b := (pile u (2*k)+pile u (n+1))+b)
    · convert h₁ using 1; abel
    apply ReflTransGen.trans (b := pile v k + (pile u (n+1)+b))
    · convert h₂ using 1; abel
    apply ReflTransGen.trans (b := pile u (n+1) + pile v 1)
    · convert h₃ using 1 <;> abel
    exact absorb he n (by dsimp [n]; omega)

end Moves

section Rooting

variable {G : SimpleGraph V}

private def Before (G : SimpleGraph V) (w x p : V) : Prop :=
  G.Adj x p ∧ G.dist p w + 1 = G.dist x w

private theorem before_exists (hT : G.IsTree) {w x : V} (hne : x ≠ w) :
    ∃ p, Before G w x p := by
  obtain ⟨q,hq⟩ := hT.connected.exists_walk_length_eq_dist x w
  cases q with
  | nil => exact (hne rfl).elim
  | @cons _ p _ e q =>
    refine ⟨p,e,?_⟩
    have h₁ := G.dist_le q
    have h₂ := e.diff_dist_adj (u := w)
    simp only [SimpleGraph.dist_comm (u := w)] at h₂
    simp only [Walk.length_cons] at hq
    omega

private theorem before_unique (hT : G.IsTree) {w x p z : V}
    (hp : Before G w x p) (hz : Before G w x z) : p = z := by
  obtain ⟨a,ha⟩ := hT.connected.exists_walk_length_eq_dist p w
  obtain ⟨b,hb⟩ := hT.connected.exists_walk_length_eq_dist z w
  have h := (hT.existsUnique_path x w).unique
    ((a.cons hp.1).isPath_of_length_eq_dist (by simpa [ha] using hp.2))
    ((b.cons hz.1).isPath_of_length_eq_dist (by simpa [hb] using hz.2))
  simpa using congrArg Walk.snd h

private def Closed (G : SimpleGraph V) (w : V) (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ p, Before G w x p → p ∈ s

private theorem peel [DecidableEq V] (hT : G.IsTree) {w : V} {s : Finset V}
    (hw : w ∈ s) (hc : Closed G w s) (hmore : s ≠ {w}) :
    ∃ x ∈ s, x ≠ w ∧ ∃ p ∈ s.erase x, G.Adj x p ∧ Closed G w (s.erase x) ∧
      ∀ z ∈ s, G.Adj x z → z = p := by
  obtain ⟨x,hx,hm⟩ := s.exists_max_image (fun a ↦ G.dist a w) ⟨w,hw⟩
  have hne : x ≠ w := by
    rintro rfl
    apply hmore
    ext z
    constructor
    · intro hz
      have hh := hm z hz
      rw [dist_self] at hh
      exact mem_singleton.mpr ((hT.connected z x).dist_eq_zero_iff.mp (by omega))
    · simpa using fun (h : z = x) ↦ h ▸ hw
  obtain ⟨p,hp⟩ := before_exists hT hne
  refine ⟨x,hx,hne,p,mem_erase.mpr ⟨hp.1.ne.symm,hc x hx p hp⟩,hp.1,?_,?_⟩
  · intro a ha b hb
    have ha' := mem_of_mem_erase ha
    have := hm a ha'
    have := hb.2
    exact mem_erase.mpr ⟨by rintro rfl; omega,hc a ha' b hb⟩
  · intro z hz he
    apply before_unique hT (p := z) (z := p) _ hp
    have hh := hT.dist_eq_dist_add_one_of_adj w he
    simp only [SimpleGraph.dist_comm (u := w)] at hh
    have := hm z hz
    exact ⟨he, by omega⟩

end Rooting

section Budget
variable [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private def degreeIn (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (u : V) : ℕ :=
  (s.filter (G.Adj u)).card

private theorem degreeIn_erase (s : Finset V) {x : V} (hx : x ∈ s) (v : V) :
    degreeIn G s v = degreeIn G (s.erase x) v + (if G.Adj v x then 1 else 0) := by
  unfold degreeIn
  rw [filter_erase]
  split_ifs with h
  · exact (card_erase_add_one (mem_filter.mpr ⟨hx,h⟩)).symm
  · simp [erase_eq_of_notMem (show x ∉ s.filter (G.Adj v) by simp [h])]

private theorem sum_merge {A : Type*} [AddCommMonoid A] {s : Finset V} {x p : V}
    (_hx : x ∈ s) (hp : p ∈ s.erase x) (f : V → A) (g : A) :
    ∑ v ∈ s.erase x, Function.update f p (f p + g) v =
      ∑ v ∈ s.erase x, f v + g := by
  rw [← sum_erase_add _ _ hp, ← sum_erase_add _ f hp]
  simp only [Function.update_self]
  rw [add_assoc]
  congr 1
  apply sum_congr rfl
  intro v hv
  exact Function.update_of_ne (ne_of_mem_erase hv) ..

private theorem slope (y : ℤ) : ∃ t : ℚ, (t = 2 ∨ t = 1/2) ∧
    t * y - (1+t) ≤ tau y := by
  by_cases h : y ≤ 1
  · exact ⟨2,Or.inl rfl,by simp [tau,h]; linarith⟩
  · refine ⟨1/2,Or.inr rfl,?_⟩
    simp only [tau, if_neg h]
    have h₁ : y = 2*(y/2) + y%2 := by omega
    have h₂ : y%2 ≤ 1 := by omega
    push_cast
    linarith [show (y : ℚ) = 2*((y/2 : ℤ) : ℚ) + ((y%2 : ℤ) : ℚ) by exact_mod_cast h₁,
      show ((y%2 : ℤ) : ℚ) ≤ 1 by exact_mod_cast h₂]

/-- Each peeled edge contributes the sum of the weights at its endpoints to the
fractional bound, since its two possible slopes are 2 and 1/2. -/
private theorem budget (hT : G.IsTree) (w : V) (s : Finset V) (hw : w ∈ s)
    (hc : Closed G w s) (D : V → Config V) (z : V → ℤ) (b : V → ℚ)
    (hs : ∀ v ∈ s, Solves G (D v) v (z v))
    (hb : ∀ v ∈ s, b v ≤ (z v : ℚ) - degreeIn G s v) :
    ∃ (Z : ℤ) (a : V → ℚ), Solves G (∑ v ∈ s, D v) w Z ∧
      (∀ v ∈ s, 0 < a v) ∧ a w = 1 ∧
      (∀ u ∈ s, ∀ v ∈ s, G.Adj u v → a v ≤ 2*a u) ∧
      ∑ v ∈ s, a v*b v ≤ Z := by
  by_cases h : s = {w}
  · subst s
    refine ⟨z w,fun _ ↦ 1,by simpa using hs w (by simp),by simp,rfl,by simp,?_⟩
    simp only [sum_singleton,one_mul]
    exact (hb w (by simp)).trans (sub_le_self _ (by positivity))
  obtain ⟨x,hx,hxw,p,hp,he,hclosed,hu⟩ := peel hT hw hc h
  let S := s.erase x
  have hw' : w ∈ S := mem_erase.mpr ⟨hxw.symm,hw⟩
  have hp' := mem_of_mem_erase hp
  obtain ⟨t,ht,htau⟩ := slope (z x)
  have htpos : 0 < t := by rcases ht with rfl|rfl <;> norm_num
  have hdx : degreeIn G s x = 1 := by
    have hset : s.filter (G.Adj x) = {p} := by
      ext v
      simp only [mem_filter,mem_singleton]
      exact ⟨fun ⟨hv,hadj⟩ ↦ hu v hv hadj,by rintro rfl; exact ⟨hp',he⟩⟩
    simp [degreeIn,hset]
  let D' := Function.update D p (D p + D x)
  let z' := Function.update z p (z p + tau (z x))
  let b' := Function.update b p (b p + t*b x)
  have hs' (v) (hv : v ∈ S) : Solves G (D' v) v (z' v) := by
    by_cases hh : v = p
    · subst v
      simpa [D',z'] using solves_merge he.symm (hs p hp') (hs x hx)
    · simpa [D',z',hh] using hs v (mem_of_mem_erase hv)
  have hb' (v) (hv : v ∈ S) : b' v ≤ (z' v : ℚ) - degreeIn G S v := by
    have h₁ := hb v (mem_of_mem_erase hv)
    have h₂ := hb x hx
    rw [hdx] at h₂
    rw [degreeIn_erase s hx v] at h₁
    by_cases hh : v = p
    · subst v
      simp [b',z',he.symm, ← show s.erase x = S from rfl] at *
      nlinarith [mul_le_mul_of_nonneg_left h₂ htpos.le]
    · have hn : ¬G.Adj v x := fun h ↦ hh (hu v (mem_of_mem_erase hv) h.symm)
      simpa [b',z',hh,hn,S] using h₁
  obtain ⟨Z,a,hsol,hpos,hroot,hadj,hsum⟩ := budget hT w S hw' hclosed D' z' b' hs' hb'
  let a' := Function.update a x (a p * t)
  have ha (v) (hv : v ∈ S) : a' v = a v := Function.update_of_ne (ne_of_mem_erase hv) ..
  have hax : a' x = a p*t := Function.update_self ..
  refine ⟨Z,a',?_,?_,(ha w hw').trans hroot,?_,?_⟩
  · simpa [D',S,sum_merge hx hp, sum_erase_add _ _ hx] using hsol
  · intro v hv
    by_cases hh : v = x
    · subst v; rw [hax]; exact mul_pos (hpos _ hp) htpos
    · have hh' := mem_erase.mpr ⟨hh,hv⟩
      rw [ha _ hh']; exact hpos _ hh'
  · intro u hu' v hv he'
    by_cases hux : u = x
    · subst u
      have h := hu v hv he'
      subst v; rw [ha _ hp,hax]
      rcases ht with rfl|rfl <;> linarith [hpos _ hp]
    by_cases hvx : v = x
    · subst v
      have h := hu u hu' he'.symm
      subst u; rw [ha _ hp,hax]
      rcases ht with rfl|rfl <;> linarith [hpos _ hp]
    have h₁ : u ∈ S := mem_erase.mpr ⟨hux,hu'⟩
    have h₂ : v ∈ S := mem_erase.mpr ⟨hvx,hv⟩
    rw [ha _ h₁,ha _ h₂]
    exact hadj u h₁ v h₂ he'
  · have hid (v) : a v * b' v =
        Function.update (fun i ↦ a i * b i) p (a p*b p + (a p*t)*b x) v := by
      by_cases h : v = p <;> simp [b',h,mul_add,mul_assoc]
    simp_rw [hid] at hsum
    rw [sum_merge hx hp] at hsum
    rw [← sum_erase_add _ _ hx,hax]
    convert hsum using 2
    apply sum_congr rfl
    intro v hv
    rw [ha v hv]
termination_by s.card
decreasing_by exact card_erase_lt_of_mem hx

private noncomputable def extend (hT : G.IsTree) (w : V) (s : Finset V) (a : V → ℚ)
    (x : V) : ℚ := if x ∈ s then a x else if hx : x = w then a w else
  extend hT w s a (before_exists hT hx).choose
termination_by G.dist x w
decreasing_by have := (before_exists hT hx).choose_spec.2; omega

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem along {a : V → ℚ} (ha : ∀ x y, G.Adj x y → a y ≤ 2*a x)
    {x y : V} (q : G.Walk x y) : a y ≤ a x * 2^q.length := by
  induction q with
  | nil => simp
  | @cons x p v e q ih =>
    have h := mul_le_mul_of_nonneg_right (ha x p e) (show 0 ≤ (2:ℚ)^q.length by positivity)
    rw [Walk.length_cons,pow_succ]
    linarith

omit [DecidableRel G.Adj] in
private theorem ratio_bound (hT : G.IsTree) {w : V} {s : Finset V} (hw : w ∈ s)
    (hc : Closed G w s) {a : V → ℚ} (hpos : ∀ x ∈ s, 0 < a x)
    (ha : ∀ x ∈ s, ∀ y ∈ s, G.Adj x y → a y ≤ 2*a x)
    {r v : V} (hr : r ∈ s) (hv : v ∈ s) : a v ≤ a r * 2^G.dist r v := by
  let A := extend hT w s a
  have hin (x) (hx : x ∈ s) : A x = a x := by unfold A; rw [extend,if_pos hx]
  have hout (x p) (hx : x ∉ s) (hp : Before G w x p) : A x = A p := by
    have hn : x ≠ w := fun h ↦ hx (h ▸ hw)
    unfold A
    rw [extend,if_neg hx,dif_neg hn, before_unique hT (before_exists hT hn).choose_spec hp]
  let rec pos (x : V) : 0 < A x := by
    by_cases h : x ∈ s
    · rw [hin _ h]; exact hpos _ h
    · have hn : x ≠ w := fun he ↦ h (he ▸ hw)
      obtain ⟨p,hp⟩ := before_exists hT hn
      rw [hout x p h hp]
      exact pos p
  termination_by G.dist x w
  decreasing_by have := hp.2; omega
  have pair (x p) (he : Before G w x p) : A x ≤ 2*A p ∧ A p ≤ 2*A x := by
    by_cases hx : x ∈ s
    · have hp := hc x hx p he
      rw [hin _ hx,hin _ hp]
      exact ⟨ha p hp x hx he.1.symm,ha x hx p hp he.1⟩
    · rw [hout x p hx he]; constructor <;> linarith [pos p]
  have adj (x y) (e : G.Adj x y) : A y ≤ 2*A x := by
    have h := hT.dist_eq_dist_add_one_of_adj w e
    simp only [SimpleGraph.dist_comm (u := w)] at h
    rcases h with h|h
    · exact (pair x y ⟨e,h.symm⟩).2
    · exact (pair y x ⟨e.symm,h.symm⟩).1
  obtain ⟨q,hq⟩ := hT.connected.exists_walk_length_eq_dist r v
  simpa [hq, hin _ hr,hin _ hv] using along adj q

end Budget

section Thresholds
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private noncomputable def charge (G : SimpleGraph V) (r v : V) : ℕ := by
  classical
  exact (if v = r ∨ 1 < G.degree v then G.degree v * 2^G.dist r v else 0) +
    (if v ≠ r ∧ G.degree v = 1 then 1 else 0)

private theorem sum_charge (r : V) : ∑ v, charge G r v = rootEstimate G r := by
  classical
  simp only [charge,rootEstimate,sum_add_distrib,card_filter]
  congr 1 <;> apply sum_congr rfl <;> intro v _ <;> split_ifs <;> rfl

/-- Every configuration of at least the estimate stacks at any occupied vertex. -/
theorem upper_at (hT : G.IsTree) (c : Config V) (w : V) (hw : 0 < c w)
    (hsize : estim G ≤ size c) :
    ∃ n, 0 < n ∧ Reach G c (pile w n) := by
  classical
  let s := univ.filter fun v ↦ G.degree v ≠ 1 ∨ 0 < c v
  have mem (v) : v ∈ s ↔ G.degree v ≠ 1 ∨ 0 < c v := by simp [s]
  have hw' := (mem w).mpr (Or.inr hw)
  have closed : Closed G w s := by
    intro x _ p hp
    by_cases hh : p = w
    · exact hh ▸ hw'
    apply (mem p).mpr
    left
    intro hd
    obtain ⟨q,hq⟩ := before_exists hT hh
    have e := (degree_eq_one_iff_existsUnique_adj.mp hd).unique hp.1.symm hq.1
    have h₁ := hp.2
    have h₂ := hq.2
    subst q; omega
  let b (v : V) : ℚ := (c v : ℚ) - degreeIn G s v
  obtain ⟨Z,a,hsol,hpos,_,hadj,hsum⟩ := budget hT w s hw' closed
    (fun v ↦ pile v (c v)) (fun v ↦ (c v : ℤ)) b
    (fun v _ ↦ solves_pile v (c v)) (by intro v _; simp [b])
  have hD : ∑ v ∈ s, pile v (c v) = c := by
    ext v
    simp only [Finset.sum_apply,pile]
    by_cases hv : v ∈ s
    · simp [eq_comm (a := v),hv]
    · have hzero : c v = 0 := by have := (mem v).not.mp hv; omega
      simp [eq_comm (a := v),hv,hzero]
  by_cases hz : 1 ≤ Z
  · refine ⟨Z.toNat,by omega,?_⟩
    simpa [hD] using hsol 0 (by simpa using hz)
  let support := univ.filter fun v ↦ 0 < c v
  obtain ⟨r,hr,hmin⟩ := support.exists_min_image a ⟨w,by simpa [support] using hw⟩
  have hrc : 0 < c r := by simpa [support] using hr
  have hrs := (mem r).mpr (Or.inr hrc)
  have hα := hpos r hrs
  -- Normalize at the lightest occupied vertex. At an occupied leaf its first
  -- pebble pays for its one incident edge, leaving just one unit of charge.
  have term (v : V) (hv : v ∈ s) :
      a r*(c v) - a v*b v ≤ a r*(charge G r v) := by
    have hd : degreeIn G s v ≤ G.degree v := by
      rw [← G.card_neighborFinset_eq_degree, neighborFinset_eq_filter]
      exact card_le_card (filter_subset_filter _ (subset_univ _))
    have hav := hpos v hv
    have hpow := ratio_bound hT hw' closed hpos hadj hrs hv
    have hmin' (hc : 0 < c v) : a r ≤ a v := hmin v (by simpa [support] using hc)
    have hc : a r*(c v) ≤ a v*(c v) := by
      by_cases h : 0 < c v
      · exact mul_le_mul_of_nonneg_right (hmin' h) (by positivity)
      · simp [show c v = 0 by omega]
    have hdeg : (degreeIn G s v : ℚ) ≤ G.degree v := by exact_mod_cast hd
    have hd' := mul_le_mul_of_nonneg_left hdeg hav.le
    unfold b charge
    by_cases h : v = r ∨ 1 < G.degree v
    · have hn : ¬(v ≠ r ∧ G.degree v = 1) := by rcases h with h|h <;> grind
      simp only [if_pos h,if_neg hn,add_zero,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      nlinarith [mul_le_mul_of_nonneg_right hpow (show 0 ≤ (G.degree v : ℚ) by positivity)]
    · by_cases hleaf : G.degree v = 1
      · have hv' : 0 < c v := (mem v).mp hv |>.resolve_left (not_not.mpr hleaf)
        have hv1 : (1:ℚ) ≤ c v := by exact_mod_cast hv'
        have hdiff := mul_nonneg (sub_nonneg.mpr (hmin' hv')) (sub_nonneg.mpr hv1)
        simp only [if_neg h,if_pos (show v ≠ r ∧ G.degree v = 1 by tauto),zero_add,
          Nat.cast_one]
        rw [hleaf] at hd'; push_cast at hd'; linarith
      · have hd0 : degreeIn G s v = 0 := by have := not_or.mp h |>.2; omega
        simp [h,hleaf,hd0]; linarith
  have hcomp := sum_le_sum term
  simp only [sum_sub_distrib,← mul_sum] at hcomp
  have hcs : ∑ v ∈ s, c v = size c := by
    apply sum_subset_zero_on_sdiff (subset_univ _) _ (by simp)
    intro i hi
    have := (mem i).not.mp (mem_sdiff.mp hi).2
    omega
  have hch : ∑ v ∈ s, charge G r v ≤ rootEstimate G r := by
    rw [← sum_charge]; exact sum_le_univ_sum_of_nonneg (by simp)
  have hbound : size c ≤ rootEstimate G r := by
    have hZ : (Z : ℚ) ≤ 0 := by exact_mod_cast (show Z ≤ 0 by omega)
    simp only [← Nat.cast_sum,hcs] at hcomp
    have hh : a r*(size c) ≤ a r*(rootEstimate G r) := by
      have := mul_le_mul_of_nonneg_left (show (∑ v ∈ s, charge G r v : ℕ) ≤
        (rootEstimate G r : ℚ) by exact_mod_cast hch) hα.le
      linarith
    exact_mod_cast (le_of_mul_le_mul_left hh hα)
  have hrmax : rootEstimate G r ≤ univ.sup (rootEstimate G) := le_sup (mem_univ r)
  unfold estim at hsize
  omega

theorem tree_upper (hT : G.IsTree) (c : Config V) (hsize : estim G ≤ size c) :
    Stackable G c := by
  classical
  have hc : ∃ w, 0 < c w := by
    by_contra! h
    have hz : size c = 0 := by simp [size, fun v ↦ Nat.eq_zero_of_le_zero (h v)]
    unfold estim at hsize; omega
  obtain ⟨w,hw⟩ := hc
  obtain ⟨n,hn,hr⟩ := upper_at hT c w hw hsize
  exact ⟨_,hr,w,by simpa [pile] using hn,fun v hv ↦ by simp [pile,hv]⟩

theorem stack_le_estim (hT : G.IsTree) : stack G ≤ estim G :=
  Nat.sInf_le ⟨le_max_left .., fun c h ↦ tree_upper hT c h.ge⟩

#print axioms tree_upper
#print axioms stack_le_estim

end Thresholds

section Obstruction
open scoped Classical
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private noncomputable def radial (G : SimpleGraph V) (r v : V) : ℕ := 2^G.dist v r

private noncomputable def toll (G : SimpleGraph V) (r v : V) : ℕ := by
  classical
  exact if v = r then 0 else 3 * 2^(G.dist v r - 1)

omit [Fintype V] in
private theorem radial_parent {r x p : V} (hp : Before G r x p) :
    radial G r x = 2*radial G r p ∧ toll G r x = 3*radial G r p := by
  have hx : x ≠ r := by rintro rfl; have := hp.2; simp at this
  simp [radial,toll,hx,← hp.2,pow_succ,Nat.mul_comm]

omit [Fintype V] [DecidableEq V] in
private theorem radial_zero {r : V} : radial G r r = 1 := by simp [radial]

omit [Fintype V] [DecidableEq V] in
private theorem before_or (hT : G.IsTree) (r : V) {x y : V} (he : G.Adj x y) :
    Before G r x y ∨ Before G r y x := by
  have h := hT.dist_eq_dist_add_one_of_adj r he
  simp only [SimpleGraph.dist_comm (u := r)] at h
  exact h.imp (fun h ↦ ⟨he,h.symm⟩) (fun h ↦ ⟨he.symm,h.symm⟩)

private theorem sum_toll (hT : G.IsTree) (r : V) :
    ∑ v, toll G r v = ∑ v, G.degree v * radial G r v := by
  classical
  let K (v p : V) := if Before G r v p then radial G r v + radial G r p else 0
  have ht (v) : toll G r v = ∑ p, K v p := by
    by_cases h : v = r
    · subst v
      have hn (p) : ¬ Before G r r p := by rintro ⟨_,hh⟩; simp at hh
      simp [K,toll,hn]
    · obtain ⟨p,hp⟩ := before_exists hT h
      rw [sum_eq_single p]
      · simp [K,hp,(radial_parent hp).1,(radial_parent hp).2]; omega
      · intro z _ hz
        simp [K,show ¬Before G r v z from fun hh ↦ hz (before_unique hT hh hp)]
      · simp
  let L (v p : V) := if Before G r v p then radial G r v else 0
  let M (v p : V) := if Before G r v p then radial G r p else 0
  have hK (v p) : K v p = L v p + M v p := by by_cases h : Before G r v p <;> simp [K,L,M,h]
  simp_rw [ht,hK,sum_add_distrib]
  rw [sum_comm (f := M), ← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  rw [← sum_add_distrib]
  have hv (p) : L v p + M p v = if G.Adj v p then radial G r v else 0 := by
    by_cases he : G.Adj v p
    · rcases before_or hT r he with hp|hp
      · have hn : ¬Before G r p v := by rintro ⟨_,hh⟩; have := hp.2; omega
        simp [L,M,hp,hn,he]
      · have hn : ¬Before G r v p := by rintro ⟨_,hh⟩; have := hp.2; omega
        simp [L,M,hp,hn,he]
    · have h₁ : ¬ Before G r v p := fun h ↦ he h.1
      have h₂ : ¬ Before G r p v := fun h ↦ he h.1.symm
      simp [L,M,h₁,h₂,he]
  simp_rw [hv]
  rw [← sum_filter]
  simp [← neighborFinset_eq_filter]

private theorem leaf_hull (hT : G.IsTree) (r : V) (s : Finset V) (hr : r ∈ s)
    (hs : Closed G r s) (hleaf : ∀ v, G.degree v = 1 → v ∈ s) : s = univ := by
  classical
  by_contra h
  have hne : (univ \ s).Nonempty := by
    obtain ⟨v,hv⟩ : ∃ v, v ∉ s := by simpa [eq_univ_iff_forall] using h
    exact ⟨v,by simpa using hv⟩
  obtain ⟨v,hv,hmax⟩ := (univ \ s).exists_max_image (fun i ↦ G.dist i r) hne
  have hn : v ∉ s := (mem_sdiff.mp hv).2
  have hvr : v ≠ r := fun hh ↦ hn (hh ▸ hr)
  obtain ⟨p,hp⟩ := before_exists hT hvr
  refine hn (hleaf v (degree_eq_one_iff_existsUnique_adj.mpr ⟨p,hp.1,?_⟩))
  intro x hx
  rcases before_or hT r hx with hh|hh
  · exact before_unique hT hh hp
  · have hx' : x ∉ s := fun h ↦ hn (hs x h v hh)
    have := hmax x (by simpa using hx')
    have := hh.2
    omega

omit [Fintype V] in
private theorem path_budget (hT : G.IsTree) (r v : V) :
    ∃ s : Finset V, r ∈ s ∧ v ∈ s ∧ Closed G r s ∧
      (∑ u ∈ s, toll G r u) + 3 ≤ 3*radial G r v := by
  classical
  by_cases h : v = r
  · subst v
    refine ⟨{r},by simp,by simp,?_,by simp [toll,radial]⟩
    rintro x hx p hp
    have := mem_singleton.mp hx
    subst x; have := hp.2; simp at this
  obtain ⟨p,hp⟩ := before_exists hT h
  obtain ⟨s,hr,hs,hc,hh⟩ := path_budget hT r p
  refine ⟨insert v s,mem_insert_of_mem hr,mem_insert_self ..,?_,?_⟩
  · intro x hx y he
    rcases mem_insert.mp hx with rfl|hx
    · exact mem_insert_of_mem ((before_unique hT he hp) ▸ hs)
    · exact mem_insert_of_mem (hc x hx y he)
  · have hle : ∑ u ∈ insert v s, toll G r u ≤ toll G r v + ∑ u ∈ s, toll G r u :=
      by by_cases hh : v ∈ s <;> simp [hh] 
    rw [(radial_parent hp).1]
    rw [(radial_parent hp).2] at hle
    omega
termination_by G.dist v r
decreasing_by have := hp.2; omega

private def weight (R : V → ℕ) (c : Config V) := ∑ v, c v * R v

private theorem weight_pile (R : V → ℕ) (x : V) (n : ℕ) :
    weight R (pile x n) = n*R x := by classical simp [weight,pile,ite_mul]

omit [DecidableEq V] in
private theorem weight_add (R : V → ℕ) (c d : Config V) :
    weight R (c+d) = weight R c + weight R d := by simp [weight,add_mul,sum_add_distrib]

private theorem weight_step (R : V → ℕ) (c : Config V) {u v : V}
    (he : G.Adj u v) (hn : 2 ≤ c u) :
    weight R (transfer c u v) + 2*R u = weight R c + R v := by
  have h : transfer c u v + pile u 2 = c + pile v 1 := by
    ext x
    by_cases hu : x = u
    · subst x; simp [transfer,pile, he.ne]; omega
    · by_cases hv : x = v <;> simp [transfer,pile,hu,hv,he.ne.symm]
  have := congrArg (weight R) h
  simpa only [weight_add,weight_pile,one_mul] using this

/-- Test every parent-closed set containing the support and the root. An inward
move can remove its source from such a set, and its weight loss pays that toll. -/
private def BoundedWeight (G : SimpleGraph V) (r : V) (c : Config V) : Prop :=
  3 ∣ weight (radial G r) c ∧
    ∀ s : Finset V, r ∈ s → Closed G r s → (∀ x, 0 < c x → x ∈ s) →
      weight (radial G r) c ≤ ∑ x ∈ s, toll G r x

private theorem bounded_step (hT : G.IsTree) {r : V} {c d : Config V}
    (h : BoundedWeight G r c) (hm : Move G c d) : BoundedWeight G r d := by
  classical
  obtain ⟨u,v,he,hn,rfl⟩ := hm
  let R := radial G r
  let d := transfer c u v
  have hw := weight_step R c he hn
  change weight R d + 2*R u = weight R c + R v at hw
  have hv : 0 < d v := by simp [d,transfer,he.ne.symm]
  have cover (s : Finset V) (hd : ∀ x, 0 < d x → x ∈ s) (x) (hx : 0 < c x) :
      x = u ∨ x ∈ s := by
    by_cases hh : x = u
    · exact Or.inl hh
    · right; apply hd; by_cases h' : x = v <;> simp_all [d,transfer,he.ne.symm]
  obtain hin|hout := before_or hT r he
  · have hu : R u = 2*R v := (radial_parent hin).1
    obtain ⟨k,hk⟩ := h.1
    change weight R c = 3*k at hk
    constructor
    · change 3 ∣ weight R d
      omega
    · intro s hr hc hs
      have hc' : Closed G r (insert u s) := by
        intro x hx p hp
        rcases mem_insert.mp hx with rfl|hx
        · exact mem_insert_of_mem ((before_unique hT hp hin) ▸ hs v hv)
        · exact mem_insert_of_mem (hc x hx p hp)
      have hh := h.2 (insert u s) (mem_insert_of_mem hr) hc'
        (fun x hx ↦ mem_insert.mpr (cover s hs x hx))
      have ht := (radial_parent hin).2
      change toll G r u = 3*R v at ht
      have hi : ∑ x ∈ insert u s, toll G r x ≤ toll G r u + ∑ x ∈ s, toll G r x :=
        by by_cases hh : u ∈ s <;> simp [hh]
      change weight R c ≤ _ at hh
      change weight R d ≤ _
      omega
  · have hr' : R v = 2*R u := (radial_parent hout).1
    have eqn : weight R d = weight R c := by omega
    constructor
    · exact eqn ▸ h.1
    · intro s hr hc hs
      rw [show weight (radial G r) (transfer c u v) = _ from eqn]
      apply h.2 s hr hc
      intro x hx
      exact (cover s hs x hx).elim (fun hh ↦ hh ▸ hc v (hs v hv) u hout) id

private theorem bounded_not_stackable (hT : G.IsTree) {r : V} {c : Config V}
    (hb : BoundedWeight G r c) : ¬Stackable G c := by
  rintro ⟨d,hreach,v,hv,hs⟩
  have hd : BoundedWeight G r d := by
    clear hv hs
    induction hreach with
    | refl => exact hb
    | tail _ h ih => exact bounded_step hT ih h
  have eqn : d = pile v (d v) := by
    ext x; by_cases hh : x = v <;> simp [pile,hh,hs]
  have hw : weight (radial G r) d = d v * radial G r v := by
    conv_lhs => rw [eqn,weight_pile]
  obtain ⟨s,hr,hv',hc,htoll⟩ := path_budget hT r v
  have hle := hd.2 s hr hc (by
    intro x hx
    by_contra hn
    have hh : x ≠ v := fun he ↦ hn (he ▸ hv')
    exact (hs x hh).not_gt hx)
  have hdiv := hd.1
  rw [hw] at hle hdiv
  have hprime : Nat.Prime 3 := by decide
  have hn : ¬ 3 ∣ radial G r v := fun hh ↦
    (by decide : ¬3 ∣ 2) (hprime.dvd_of_dvd_pow hh)
  have hthree : 3 ≤ d v := Nat.le_of_dvd hv ((hprime.dvd_mul.mp hdiv).resolve_right hn)
  have := Nat.mul_le_mul_right (radial G r v) hthree
  omega

private noncomputable def rho (G : SimpleGraph V) (r : V) : ℕ := by
  classical
  exact ∑ v, if v = r ∨ 1 < G.degree v then G.degree v * radial G r v else 0

private noncomputable def leaves (G : SimpleGraph V) (r : V) : Config V := by
  classical
  exact fun v ↦ if v ≠ r ∧ G.degree v = 1 then 1 else 0

/-- The root holds its degree-weight sum, and every other leaf holds one pebble. -/
private noncomputable def obstruction (G : SimpleGraph V) (r : V) : Config V :=
  pile r (rho G r) + leaves G r

private theorem obstruction_size (r : V) : size (obstruction G r) = rootEstimate G r := by
  classical
  have hh : size (pile r (rho G r)) = rho G r := by simp [size,pile]
  rw [obstruction,size,Pi.add_def,sum_add_distrib,← size,hh]
  unfold rho radial rootEstimate leaves
  simp only [card_filter,SimpleGraph.dist_comm (v := r)]
  congr 1 <;> apply sum_congr rfl <;> intro v _ <;> split_ifs <;> rfl

private theorem obstruction_weight (hT : G.IsTree) (r : V) :
    weight (radial G r) (obstruction G r) = ∑ v, toll G r v := by
  classical
  rw [obstruction,weight_add,weight_pile,radial_zero,mul_one,sum_toll hT]
  unfold rho weight
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  by_cases h : v = r ∨ 1 < G.degree v
  · have hn : ¬(v ≠ r ∧ G.degree v = 1) := by rcases h with h|h <;> grind
    simp [leaves,h,hn]
  · by_cases hd : G.degree v = 1
    · simp [leaves,hd,not_or.mp h |>.1]
    · have hd0 : G.degree v = 0 := by have := (not_or.mp h).2; omega
      simp [leaves,hd0]

private theorem obstruction_bad (hT : G.IsTree) (r : V) : ¬Stackable G (obstruction G r) := by
  classical
  apply bounded_not_stackable hT (r := r)
  constructor
  · rw [obstruction_weight hT]
    apply Finset.dvd_sum
    intro v _
    unfold toll; split <;> simp
  · intro s hr hc hs
    have hfull := leaf_hull hT r s hr hc (by
      intro v hv
      by_cases hh : v = r
      · exact hh ▸ hr
      · apply hs
        simp [obstruction,leaves,hh,hv])
    rw [hfull,obstruction_weight hT]

theorem tree_lower_witness [Nontrivial V] (hT : G.IsTree) :
    ∃ c : Config V, size c = estim G - 1 ∧ AlmostStacked c ∧ ¬Stackable G c := by
  classical
  obtain ⟨r,_,hr⟩ := univ.exists_mem_eq_sup univ_nonempty (rootEstimate G)
  have hdeg := hT.connected.preconnected.degree_pos_of_nontrivial r
  have hρ : G.degree r ≤ rootEstimate G r := by
    rw [← sum_charge]
    have h := single_le_sum (f := charge G r) (fun _ _ ↦ Nat.zero_le _) (mem_univ r)
    simpa [charge] using h
  refine ⟨obstruction G r,?_,⟨r,?_⟩,obstruction_bad hT r⟩
  · rw [obstruction_size,estim,hr]; omega
  · intro v hv
    simp [obstruction,pile,leaves,hv]
    split <;> decide

private theorem card_lt_of_good {n : ℕ} (hn : 2 ≤ n) (hg : Good G n) :
    Fintype.card V < n := by
  classical
  by_contra! h
  obtain ⟨s,_,hs⟩ := exists_subset_card_eq (s := (univ : Finset V)) (by simpa using h)
  let c (v : V) : ℕ := if v ∈ s then 1 else 0
  have hsize : size c = n := by simpa [size,c] using hs
  rcases stackable_iff.mp (hg c hsize) with ⟨v,_,hv⟩|⟨d,⟨u,_,_,h,_⟩,_⟩
  · have hh : size c = c v := by
      unfold size
      apply sum_eq_single v (fun x _ hx ↦ hv x hx) (by simp)
    have hle : c v ≤ 1 := by unfold c; split <;> decide
    omega
  · unfold c at h; split at h <;> omega

private theorem good_succ [Nontrivial V] (hT : G.IsTree) {n : ℕ}
    (hcard : Fintype.card V ≤ n) (hg : Good G n) : Good G (n+1) := by
  classical
  intro c hsize
  have high : ∃ u, 2 ≤ c u := by
    by_contra! hh
    have hle : size c ≤ ∑ _ : V, 1 := sum_le_sum fun x _ ↦ by have := hh x; omega
    simp at hle
    omega
  obtain ⟨u,hn⟩ := high
  obtain ⟨v,he⟩ := hT.connected.preconnected.exists_adj_of_nontrivial u
  have h := weight_step (fun _ ↦ 1) c he hn
  simp only [weight, mul_one] at h
  change size (transfer c u v) + 2 = size c + 1 at h
  exact stackable_iff.mpr (.inr ⟨_,⟨u,v,he,hn,rfl⟩,hg _ (by omega)⟩)

theorem estim_le_stack (hT : G.IsTree) : estim G ≤ stack G := by
  classical
  have hmem : 2 ≤ stack G ∧ Good G (stack G) :=
    Nat.sInf_mem (s := {n | 2 ≤ n ∧ Good G n})
      ⟨estim G,le_max_left ..,fun c h ↦ tree_upper hT c h.ge⟩
  rcases subsingleton_or_nontrivial V with ht|ht
  · have hr (r : V) : rootEstimate G r = 0 := by simp [rootEstimate]
    have hsup : univ.sup (rootEstimate G) ≤ 0 := Finset.sup_le (fun v _ ↦ (hr v).le)
    unfold estim; omega
  · obtain ⟨c,hc,_,hn⟩ := tree_lower_witness hT
    by_contra! hlt
    have hcard := card_lt_of_good hmem.1 hmem.2
    have good (n : ℕ) (h : stack G ≤ n) : Good G n := by
      induction n, h using Nat.le_induction with
      | base => exact hmem.2
      | succ n h ih => exact good_succ hT (by omega) ih
    exact hn (good _ (show stack G ≤ size c by omega) c rfl)

/-- Csernák and Soukup's Conjecture 5.6, with the literal least-size threshold. -/
theorem conjecture_5_6 (hT : G.IsTree) : stack G = estim G :=
  le_antisymm (stack_le_estim hT) (estim_le_stack hT)

#print axioms upper_at
#print axioms tree_lower_witness
#print axioms estim_le_stack
#print axioms conjecture_5_6

end Obstruction

namespace P4

abbrev graph := pathGraph 4

private abbrev Row := ℕ × ℕ × ℕ × ℕ

private def config : Row → Config (Fin 4)
  | (a,b,c,d) => ![a,b,c,d]

private def total : Row → ℕ
  | (a,b,c,d) => a+b+c+d

private theorem size_config (p : Row) : size (config p) = total p := by
  obtain ⟨a,b,c,d⟩ := p
  simp [size, config, total, Fin.sum_univ_succ, Nat.add_assoc]

private theorem config_surj (f : Config (Fin 4)) : ∃ p, config p = f :=
  ⟨(f 0, f 1, f 2, f 3), by funext i; fin_cases i <;> rfl⟩

private def settled : Row → Prop
  | (a,b,c,d) => (0 < a ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨
    (0 < b ∧ a = 0 ∧ c = 0 ∧ d = 0) ∨ (0 < c ∧ a = 0 ∧ b = 0 ∧ d = 0) ∨
    (0 < d ∧ a = 0 ∧ b = 0 ∧ c = 0)

private instance (p : Row) : Decidable (settled p) := by unfold settled; split; infer_instance

private def almost : Row → Prop
  | (a,b,c,d) => (b ≤ 1 ∧ c ≤ 1 ∧ d ≤ 1) ∨ (a ≤ 1 ∧ c ≤ 1 ∧ d ≤ 1) ∨
    (a ≤ 1 ∧ b ≤ 1 ∧ d ≤ 1) ∨ (a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1)

private instance (p : Row) : Decidable (almost p) := by unfold almost; split; infer_instance

private theorem settled_iff (p : Row) : settled p ↔ Stacked (config p) := by
  obtain ⟨a,b,c,d⟩ := p
  simp [settled, Stacked, config, Fin.exists_fin_succ,
    Fin.forall_fin_succ]

private theorem almost_iff (p : Row) : almost p ↔ AlmostStacked (config p) := by
  obtain ⟨a,b,c,d⟩ := p
  simp [almost, AlmostStacked, config, Fin.exists_fin_succ, Fin.forall_fin_succ]

private def destinations : Row → List Row
  | (a,b,c,d) =>
    (if 2 ≤ a then [(a-2,b+1,c,d)] else []) ++
    (if 2 ≤ b then [(a+1,b-2,c,d), (a,b-2,c+1,d)] else []) ++
    (if 2 ≤ c then [(a,b+1,c-2,d), (a,b,c-2,d+1)] else []) ++
    (if 2 ≤ d then [(a,b,c+1,d-2)] else [])

private theorem path_edges (u v : Fin 4) : graph.Adj u v ↔
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨
    (u = 2 ∧ v = 1) ∨ (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) := by
  rw [pathGraph_adj]
  revert u v; decide

private theorem destinations_spec (p : Row) (f : Config (Fin 4)) :
    Move graph (config p) f ↔ ∃ q ∈ destinations p, f = config q := by
  obtain ⟨a,b,c,d⟩ := p
  have app (l k : List Row) : (∃ q ∈ l ++ k, f = config q) ↔
      (∃ q ∈ l, f = config q) ∨ (∃ q ∈ k, f = config q) := by simp [or_and_right, exists_or]
  have guard (P : Prop) [Decidable P] (l : List Row) :
      (∃ q ∈ (if P then l else []), f = config q) ↔ P ∧ ∃ q ∈ l, f = config q := by
    by_cases h : P <;> simp [h]
  simp only [destinations, app, guard, List.mem_cons, List.not_mem_nil, or_false,
    or_and_right, exists_or, exists_eq_left]
  have h0 : transfer (config (a,b,c,d)) 0 1 = config (a-2,b+1,c,d) := by
    funext i; fin_cases i <;> rfl
  have h1 : transfer (config (a,b,c,d)) 1 0 = config (a+1,b-2,c,d) := by
    funext i; fin_cases i <;> rfl
  have h2 : transfer (config (a,b,c,d)) 1 2 = config (a,b-2,c+1,d) := by
    funext i; fin_cases i <;> rfl
  have h3 : transfer (config (a,b,c,d)) 2 1 = config (a,b+1,c-2,d) := by
    funext i; fin_cases i <;> rfl
  have h4 : transfer (config (a,b,c,d)) 2 3 = config (a,b,c-2,d+1) := by
    funext i; fin_cases i <;> rfl
  have h5 : transfer (config (a,b,c,d)) 3 2 = config (a,b,c+1,d-2) := by
    funext i; fin_cases i <;> rfl
  constructor
  · rintro ⟨u,v,he,hn,hf⟩
    rcases (path_edges u v).mp he with h|h|h|h|h|h <;> obtain ⟨rfl,rfl⟩ := h
    all_goals simp only [h0,h1,h2,h3,h4,h5] at hf
    all_goals first | exact .inl (.inl (.inl ⟨hn,hf⟩)) | exact .inl (.inl (.inr ⟨hn,.inl hf⟩)) |
      exact .inl (.inl (.inr ⟨hn,.inr hf⟩)) | exact .inl (.inr ⟨hn,.inl hf⟩) |
      exact .inl (.inr ⟨hn,.inr hf⟩) | exact .inr ⟨hn,hf⟩
  · rintro (((h|⟨hn,h|h⟩)|⟨hn,h|h⟩)|h)
    · exact ⟨0,1, (path_edges _ _).mpr (by decide), h.1, h.2 |>.trans h0.symm⟩
    · exact ⟨1,0, (path_edges _ _).mpr (by decide), hn, h |>.trans h1.symm⟩
    · exact ⟨1,2, (path_edges _ _).mpr (by decide), hn, h |>.trans h2.symm⟩
    · exact ⟨2,1, (path_edges _ _).mpr (by decide), hn, h |>.trans h3.symm⟩
    · exact ⟨2,3, (path_edges _ _).mpr (by decide), hn, h |>.trans h4.symm⟩
    · exact ⟨3,2, (path_edges _ _).mpr (by decide), h.1, h.2 |>.trans h5.symm⟩

private theorem total_destination {p q : Row} (h : q ∈ destinations p) :
    total q + 1 = total p := by
  obtain ⟨a,b,c,d⟩ := p
  simp [destinations] at h
  grind [total]

private def rows (n : ℕ) : List Row := do
  let a ← List.range (n+1)
  let b ← List.range (n-a+1)
  let c ← List.range (n-a-b+1)
  return (a,b,c,n-a-b-c)

private theorem mem_rows (p : Row) (n : ℕ) : p ∈ rows n ↔ total p = n := by
  obtain ⟨a,b,c,d⟩ := p
  simp [rows, total, List.mem_flatMap]
  omega

/-- The preceding layer suffices because each move consumes one pebble. -/
private def bad : ℕ → List Row
  | 0 => rows 0
  | n+1 =>
    let prev := bad n
    (rows (n+1)).filter fun p ↦ !decide (settled p) && (destinations p).all (· ∈ prev)

private theorem bad_iff (n : ℕ) (p : Row) : p ∈ bad n ↔
    total p = n ∧ ¬Stackable graph (config p) := by
  induction n generalizing p with
  | zero =>
    rw [bad, mem_rows]
    refine ⟨fun h ↦ ⟨h, ?_⟩, And.left⟩
    obtain ⟨a,b,c,d⟩ := p
    simp [total] at h
    obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩ := h
    rw [stackable_iff, ← settled_iff]
    simp [settled, destinations_spec, destinations]
  | succ n ih =>
    simp only [bad, List.mem_filter, mem_rows, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, List.all_eq_true, decide_eq_true_eq, ih, settled_iff]
    constructor
    · rintro ⟨hp, hs, hd⟩
      refine ⟨hp, ?_⟩
      rw [stackable_iff]
      rintro (h | ⟨f, hf, h⟩)
      · exact hs h
      · obtain ⟨q,hq,rfl⟩ := (destinations_spec p f).mp hf
        exact (hd q hq).2 h
    · rintro ⟨hp, h⟩
      rw [stackable_iff] at h
      refine ⟨hp, fun hs ↦ h (.inl hs), fun q hq ↦ ⟨by have := total_destination hq; omega, ?_⟩⟩
      exact fun hs ↦ h (.inr ⟨_, (destinations_spec p _).mpr ⟨q,hq,rfl⟩, hs⟩)

private theorem good_iff (n : ℕ) : Good graph n ↔ bad n = [] := by
  constructor
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hp
    obtain ⟨ht,hn⟩ := (bad_iff n p).mp hp
    exact hn (h _ ((size_config p).trans ht))
  · intro h f hf
    obtain ⟨p,rfl⟩ := config_surj f
    by_contra hn
    have hp := (bad_iff n p).mpr ⟨(size_config p).symm.trans hf, hn⟩
    simp [h] at hp

private theorem almostGood_iff (n : ℕ) :
    AlmostGood graph n ↔ (bad n).any (fun p ↦ decide (almost p)) = false := by
  simp only [List.any_eq_false, decide_eq_true_eq]
  constructor
  · intro h p hp ha
    obtain ⟨ht,hn⟩ := (bad_iff n p).mp hp
    exact hn (h _ ((size_config p).trans ht) ((almost_iff p).mp ha))
  · intro h f hf ha
    obtain ⟨p,rfl⟩ := config_surj f
    by_contra hn
    exact h _ ((bad_iff n p).mpr ⟨(size_config p).symm.trans hf,hn⟩) ((almost_iff p).mpr ha)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem layers :
    (bad 15 = []) ∧
    (∀ n : Fin 15, 2 ≤ n.val → (bad n.val).isEmpty = false) ∧
    ((bad 12).any (fun p ↦ decide (almost p)) = false) ∧
    (∀ n : Fin 12, 2 ≤ n.val → (bad n.val).any (fun p ↦ decide (almost p)) = true) ∧
    ((9,0,0,3) : Row) ∈ bad 12 := by decide

theorem witness : size (![9,0,0,3] : Config (Fin 4)) = 12 ∧
    ¬ Stackable graph ![9,0,0,3] := by
  have h := (bad_iff 12 (9,0,0,3)).mp layers.2.2.2.2
  exact ⟨(size_config _).trans h.1, h.2⟩

theorem almostGood_twelve : AlmostGood graph 12 := (almostGood_iff _).mpr layers.2.2.1

theorem stack_eq_fifteen : stack graph = 15 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨by decide, (good_iff _).mpr layers.1⟩
  · unfold stack
    refine le_csInf ⟨15, by decide, (good_iff _).mpr layers.1⟩ ?_
    intro n ⟨hn,h⟩
    by_contra! hlt
    have hb := layers.2.1 ⟨n,hlt⟩ hn
    simp [(good_iff _).mp h] at hb

theorem almostStack_eq_twelve : almostStack graph = 12 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨by decide, almostGood_twelve⟩
  · unfold almostStack
    refine le_csInf ⟨12, by decide, almostGood_twelve⟩ ?_
    intro n ⟨hn,h⟩
    by_contra! hlt
    have hb := layers.2.2.2.1 ⟨n,hlt⟩ hn
    simp [(almostGood_iff _).mp h] at hb

theorem literal_ASH_fails : stack graph ≠ almostStack graph := by
  rw [stack_eq_fifteen, almostStack_eq_twelve]
  decide

#print axioms witness
#print axioms almostGood_twelve
#print axioms stack_eq_fifteen
#print axioms almostStack_eq_twelve
#print axioms literal_ASH_fails

end P4

def Clearable [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Config V) : Prop :=
  ∃ d, Reach G c d ∧ size d = 1

namespace G5

private def edges : List (Fin 5 × Fin 5) :=
  [(0,1),(1,0),(1,2),(2,1),(0,2),(2,0),(2,3),(3,2),(3,4),(4,3)]

def graph : SimpleGraph (Fin 5) where
  Adj u v := (u,v) ∈ edges
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

abbrev start : Config (Fin 5) := ![0,0,0,2,14]

private def next (c : Config (Fin 5)) : List (Config (Fin 5)) :=
  edges.flatMap fun (u,v) ↦ if 2 ≤ c u then [transfer c u v] else []

private theorem mem_next {c d : Config (Fin 5)} : d ∈ next c ↔ Move graph c d := by
  simp only [next,List.mem_flatMap,Prod.exists]
  constructor
  · rintro ⟨u,v,he,hm⟩
    by_cases hn : 2 ≤ c u
    · exact ⟨u,v,he,hn,by simpa [hn] using hm⟩
    · simp [hn] at hm
  · rintro ⟨u,v,he,hn,rfl⟩
    exact ⟨u,v,he,by simp [hn]⟩

private def layer : ℕ → List (Config (Fin 5))
  | 0 => [start]
  | n+1 => ((layer n).flatMap next).eraseDups

private theorem next_layer {n : ℕ} {c d : Config (Fin 5)} (hc : c ∈ layer n)
    (hm : Move graph c d) : d ∈ layer (n+1) := by
  simpa [layer] using (List.mem_flatMap.mpr ⟨c,hc,mem_next.mpr hm⟩ :
    d ∈ (layer n).flatMap next)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem exhaustion : layer 16 = [] ∧
    ∀ n : Fin 16, ((layer n).all (fun c ↦ decide (size c ≠ 1))) = true := by decide

theorem clearing_witness : size start = 16 ∧ ¬Clearable graph start := by
  refine ⟨by decide,?_⟩
  rintro ⟨d,hr,hd⟩
  have found : ∃ n : Fin 16, d ∈ layer n := by
    clear hd
    induction hr with
    | refl => exact ⟨0,by simp [layer]⟩
    | tail _ hm ih =>
      obtain ⟨n,hn⟩ := ih
      have h := next_layer hn hm
      by_cases hlt : n.val+1 < 16
      · exact ⟨⟨_,hlt⟩,h⟩
      · rw [show n.val+1 = 16 by omega,exhaustion.1] at h
        simp at h
  obtain ⟨n,hn⟩ := found
  exact (of_decide_eq_true (List.all_eq_true.mp (exhaustion.2 n) d hn)) hd

#print axioms clearing_witness

end G5

end CsernakSoukup
