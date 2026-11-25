import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# Zero-rotatability of regular spiders

Path positions start at zero. A permutation of the indices `0,…,n−1` whose adjacent
sums are `1,3,…,2n−3` becomes an alpha-labeling under the Walecki map
`2u ↦ u`, `2u+1 ↦ n−1−u`. An adjacent sum `2r+1` gives edge weight `n−1−r`.

Two index permutations of lengths `p,s` concatenate after shifting the second
by `p` when their adjoining endpoint indices sum to `p−1`. The bridge then has
sum `2p−1`, between the two disjoint intervals of old edge sums.
-/

namespace SpiderRotatability

abbrev SpiderV (k l : ℕ) := Unit ⊕ (Fin k × Fin l)
abbrev SpiderE (k l : ℕ) := Fin k × Fin l

def edgeEndpoints {k l : ℕ} (e : SpiderE k l) : SpiderV k l × SpiderV k l :=
  (if h : e.2.val = 0 then .inl () else .inr (e.1, ⟨e.2.val - 1, by omega⟩), .inr e)

def weight (x y : ℕ) := ((x : ℤ) - y).natAbs

def edgeWeight {k l : ℕ} (f : SpiderV k l → ℕ) (e : SpiderE k l) :=
  weight (f (edgeEndpoints e).1) (f (edgeEndpoints e).2)

def IsGraceful (k l : ℕ) (f : SpiderV k l → ℕ) : Prop :=
  (∀ v, f v ≤ k*l) ∧ Function.Injective f ∧
  (∀ e, 1 ≤ edgeWeight f e ∧ edgeWeight f e ≤ k*l) ∧ Function.Injective (edgeWeight f)

private theorem image_iff {α : Type*} [Fintype α] (f : α → ℕ) (s : Finset ℕ)
    (h : s.card = Fintype.card α) :
    Finset.univ.image f = s ↔ (∀ i, f i ∈ s) ∧ Function.Injective f := by
  classical
  constructor
  · intro he
    refine ⟨fun i ↦ he ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i), ?_⟩
    have hi : Set.InjOn f (Finset.univ : Finset α) := Finset.card_image_iff.mp (by simp [he,h])
    exact fun _ _ ↦ hi (Finset.mem_univ _) (Finset.mem_univ _)
  · rintro ⟨hm, hi⟩
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hm i
    · simp [Finset.card_image_of_injective _ hi,h]

theorem isGraceful_iff_images {k l : ℕ} (f : SpiderV k l → ℕ) :
    IsGraceful k l f ↔ Finset.univ.image f = Finset.range (k*l+1) ∧
      Finset.univ.image (edgeWeight f) = Finset.Icc 1 (k*l) := by
  rw [image_iff, image_iff]
  · simp [IsGraceful, Nat.lt_succ_iff, and_assoc]
  · simp [SpiderE]
  · simp [SpiderV, Nat.add_comm]

/-- Every label in the zero-based interval is attained. -/
private def Covers (n : ℕ) (f : ℕ → ℕ) := ∀ x < n, ∃ i < n, f i = x

/-- The adjacent sums of this permutation are the odd numbers from 1 to 2n−3. -/
private structure SumPath (n : ℕ) (f : ℕ → ℕ) : Prop where
  labels : Covers n f
  sums : ∀ r, r+1 < n → ∃ i, i+1 < n ∧ f i + f (i+1) = 2*r+1

private def splice (p : ℕ) (f g : ℕ → ℕ) (i : ℕ) :=
  if i < p then f i else p + g (i-p)

private theorem splice_path {p s : ℕ} {f g : ℕ → ℕ} (hp : 0 < p) (hs : 0 < s)
    (hf : SumPath p f) (hg : SumPath s g) (bridge : f (p-1) + g 0 = p-1) :
    SumPath (p+s) (splice p f g) := by
  constructor
  · intro x hx
    by_cases h : x < p
    · obtain ⟨i,hi,he⟩ := hf.labels x h
      exact ⟨i,by omega,by simp [splice,hi,he]⟩
    · obtain ⟨i,hi,he⟩ := hg.labels (x-p) (by omega)
      exact ⟨p+i,by omega,by simp [splice,he]; omega⟩
  · intro r hr
    by_cases h : r+1 < p
    · obtain ⟨i,hi,he⟩ := hf.sums r h
      exact ⟨i,by omega,by simpa [splice,hi,show i<p by omega] using he⟩
    by_cases h' : r < p
    · refine ⟨p-1,by omega,?_⟩
      simp [splice,show p-1<p by omega,show p-1+1=p by omega]
      omega
    · obtain ⟨i,hi,he⟩ := hg.sums (r-p) (by omega)
      refine ⟨p+i,by omega,?_⟩
      simp [splice,show ¬p+i+1<p by omega,show p+i+1-p=i+1 by omega]
      omega

private def rev (n : ℕ) (f : ℕ → ℕ) (i : ℕ) := f (n-1-i)

private theorem rev_path {n : ℕ} {f : ℕ → ℕ} (hf : SumPath n f) : SumPath n (rev n f) := by
  constructor
  · intro x hx
    obtain ⟨i,hi,he⟩ := hf.labels x hx
    exact ⟨n-1-i,by omega,by simpa [rev,show n-1-(n-1-i)=i by omega] using he⟩
  · intro r hr
    obtain ⟨i,hi,he⟩ := hf.sums r hr
    refine ⟨n-2-i,by omega,?_⟩
    simp only [rev,show n-1-(n-2-i)=i+1 by omega,show n-1-(n-2-i+1)=i by omega]
    omega

private theorem id_path (n : ℕ) : SumPath n id :=
  ⟨fun x hx ↦ ⟨x,hx,rfl⟩, fun r hr ↦ ⟨r,hr,by simp; omega⟩⟩

private def flipPair (x : ℕ) := 2*(x/2) + (1-x%2)

private theorem flip_path {n : ℕ} {f : ℕ → ℕ} (hn : n%2=0) (hf : SumPath n f) :
    SumPath n (fun i ↦ flipPair (f i)) := by
  constructor
  · intro x hx
    obtain ⟨i,hi,he⟩ := hf.labels (flipPair x) (by unfold flipPair; omega)
    exact ⟨i,hi,by change flipPair (f i) = x; rw [he]; unfold flipPair; omega⟩
  · intro r hr
    obtain ⟨i,hi,he⟩ := hf.sums r hr
    exact ⟨i,hi,by unfold flipPair; omega⟩


private theorem full_image {α : Type*} [Fintype α] {f : α → ℕ} {s : Finset ℕ}
    (hc : s.card = Fintype.card α) (hits : ∀ x ∈ s, ∃ i, f i = x) :
    Finset.univ.image f = s := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨i,hi⟩ := hits _ hx
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
  · exact Finset.card_image_le.trans (by simp [hc])

private theorem covers_spec {n : ℕ} {f : ℕ → ℕ} (h : Covers n f) :
    (∀ i < n, f i < n) ∧ Function.Injective (fun i : Fin n ↦ f i) := by
  have hi := full_image (f := fun i : Fin n ↦ f i) (s := Finset.range n) (by simp) (by
    intro x hx
    obtain ⟨i,hi,he⟩ := h x (Finset.mem_range.mp hx)
    exact ⟨⟨i,hi⟩,he⟩)
  have hm := (image_iff _ _ (by simp)).mp hi
  exact ⟨fun i hi ↦ Finset.mem_range.mp (hm.1 ⟨i,hi⟩), hm.2⟩

private theorem mirror_path {n : ℕ} {f : ℕ → ℕ} (hf : SumPath n f) :
    SumPath n (fun i ↦ n-1-f i) := by
  constructor
  · intro x hx
    obtain ⟨i,hi,he⟩ := hf.labels (n-1-x) (by omega)
    exact ⟨i,hi,by change n-1-f i=x; omega⟩
  · intro r hr
    obtain ⟨i,hi,he⟩ := hf.sums (n-2-r) (by omega)
    have ha := (covers_spec hf.labels).1 i (by omega)
    have hb := (covers_spec hf.labels).1 (i+1) hi
    exact ⟨i,hi,by omega⟩

private def Allowed (n i : ℕ) := i<n ∧ (n%2=0 ∨ (i%2=0 ∧ (n≠2*i+1 ∨ n=1)))

/-- Reflect a far starting index about n−1, or swap adjacent label pairs to turn
an odd start into an even one when n is even. For the resulting even index i,
prepend the reversed identity block of length i+1. When n is even and 2i+2<n,
use length i+2 and swap adjacent labels in that block. Both choices require
the smaller permutation to start at i. -/
private theorem block_start (n i : ℕ) (h : Allowed n i) :
    ∃ f, SumPath n f ∧ f 0 = i := by
  unfold Allowed at h
  by_cases hn : n=1
  · exact ⟨id,id_path n,by simp; omega⟩
  by_cases hfar : 2*i ≥ n
  · obtain ⟨f,hf,hi⟩ := block_start n (n-1-i) (by unfold Allowed; omega)
    exact ⟨_,mirror_path hf,by simp [hi]; omega⟩
  by_cases hodd : i%2=1
  · obtain ⟨f,hf,hi⟩ := block_start n (i-1) (by unfold Allowed; omega)
    exact ⟨_,flip_path (by omega) hf,by simp [hi,flipPair]; omega⟩
  by_cases hwide : n%2=0 ∧ 2*i+2<n
  · let p := i+2
    let a := fun j ↦ flipPair (rev p id j)
    have ha : SumPath p a := flip_path (by dsimp [p]; omega) (rev_path (id_path p))
    obtain ⟨g,hg,h0⟩ := block_start (n-p) i (by unfold Allowed p; omega)
    have hj := splice_path (p := p) (s := n-p) (by unfold p; omega) (by unfold p; omega)
      ha hg (by simp [a,rev,p,flipPair,h0]; omega)
    exact ⟨_,by simpa [Nat.add_sub_of_le (show p≤n by unfold p; omega)] using hj,
      by simp [splice,p,a,rev,flipPair]; omega⟩
  · let p := i+1
    obtain ⟨g,hg,h0⟩ := block_start (n-p) i (by unfold Allowed p; omega)
    have hj := splice_path (p := p) (s := n-p) (by unfold p; omega) (by unfold p; omega)
      (rev_path (id_path p)) hg (by simp [rev,p,h0])
    exact ⟨_,by simpa [Nat.add_sub_of_le (show p≤n by unfold p; omega)] using hj,
      by simp [splice,rev,p]⟩
termination_by (n,i)
decreasing_by
  all_goals simp only [Allowed] at *
  all_goals have hi : i<n := h.1
  all_goals first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega)


private def AtExtreme (n d : ℕ) := ∃ f, SumPath n f ∧ f d ≤ 1

private theorem prefix_extreme {n d p : ℕ} (hp : 0<p) (hp' : p<n)
    (hd : p=d+1 ∨ p=d+2) (h : Allowed (n-p) (p-1) ∨
      (p%2=0 ∧ Allowed (n-p) (p-2))) : AtExtreme n d := by
  have assemble (a : ℕ → ℕ) (ha : SumPath p a) (hx : a d ≤ 1)
      (hbound : a (p-1) ≤ p-1) (hb : Allowed (n-p) (p-1-a (p-1))) : AtExtreme n d := by
    obtain ⟨g,hg,h0⟩ := block_start _ _ hb
    have hj := splice_path hp (s := n-p) (by omega) ha hg (by omega)
    exact ⟨_,by simpa [Nat.add_sub_of_le hp'.le] using hj,
      by simpa [splice,show d<p by omega] using hx⟩
  rcases h with h | ⟨he,h⟩
  · apply assemble (rev p id) (rev_path (id_path p)) <;> simp [rev] at * <;> omega
  · apply assemble _ (flip_path he (rev_path (id_path p))) <;>
      simp [flipPair,rev] at * <;> omega

private theorem finite_sum_path {n : ℕ} {f : ℕ → ℕ}
    (hv : ∀ x : Fin n, ∃ i : Fin n, f i=x.val)
    (he : ∀ r : Fin (n-1), ∃ i : Fin (n-1), f i+f (i.val+1)=2*r.val+1) :
    SumPath n f := by
  constructor
  · intro x hx
    obtain ⟨i,hi⟩ := hv ⟨x,hx⟩
    exact ⟨i,i.isLt,hi⟩
  · intro r hr
    obtain ⟨i,hi⟩ := he ⟨r,by omega⟩
    exact ⟨i,by have := i.isLt; omega,hi⟩

private def seedSix (i : ℕ) : ℕ := [3,0,1,4,5,2][i]!

private theorem seedSix_path : SumPath 6 seedSix := finite_sum_path (by decide) (by decide)

private def seedNine (i : ℕ) : ℕ := [2,5,4,1,0,3,8,7,6][i]!

private theorem seedNine_path : SumPath 9 seedNine := finite_sum_path (by decide) (by decide)

private def seedThirteen (i : ℕ) : ℕ := [2,5,8,7,4,1,0,3,6,11,12,9,10][i]!

private theorem seedThirteen_path : SumPath 13 seedThirteen := finite_sum_path (by decide) (by decide)


/-- For n=2d+1 with d even and d≥8, put p=d+2. Extend the six-entry seed with a
block of length p−6 starting at 3, reverse the result, then append a block of
length n−p starting at p−4. The seed's second entry is now at position d. -/
private theorem center_extreme {n d : ℕ} (hn : n=2*d+1) (hd : d%2=0)
    (hs : 8≤d) : AtExtreme n d := by
  let p := d+2
  obtain ⟨g,hg,hg0⟩ := block_start (p-6) 3 (by unfold Allowed p; omega)
  let a := splice 6 seedSix g
  have ha : SumPath p a := by
    have hj := splice_path (p := 6) (s := p-6) (by decide) (by unfold p; omega)
      seedSix_path hg (by rw [hg0]; decide)
    simpa [a,Nat.add_sub_of_le (show 6≤p by unfold p; omega)] using hj
  obtain ⟨b,hb,hb0⟩ := block_start (n-p) (p-4) (by unfold Allowed p; omega)
  have hj := splice_path (p := p) (s := n-p) (by unfold p; omega) (by unfold p; omega)
    (rev_path ha) hb (by simp [rev,a,splice,hb0]; change 3+(p-4)=p-1; unfold p; omega)
  exact ⟨_,by simpa [Nat.add_sub_of_le (show p≤n by unfold p; omega)] using hj,
    by simp [splice,show d<p by unfold p; omega,rev,show p-1-d=1 by unfold p; omega,a]; decide⟩

/-- For a position in the first half, lengths d+1 and d+2 put one of the extreme
indices 0,1 at d in a reversed prefix. Try either prefix, optionally swapping
pairs when its length is even. The admissibility inequalities leave the centered
case and the listed small seeds. Reversing the path covers the second half. -/
private theorem near_extreme {n d : ℕ} (hn : 1<n) (hd : 2*d<n)
    (hex : ¬ (n=5 ∧ d=2)) : AtExtreme n d := by
  by_cases h0 : d≤1
  · exact ⟨id,id_path n,h0⟩
  by_cases h9 : n=9 ∧ (d=3 ∨ d=4)
  · obtain ⟨rfl,rfl|rfl⟩ := h9 <;> exact ⟨seedNine,seedNine_path,by decide⟩
  by_cases hc : n=2*d+1 ∧ d%2=0
  · by_cases h8 : 8≤d
    · exact center_extreme hc.1 hc.2 h8
    · obtain ⟨rfl,he⟩ := hc
      have : d=4 ∨ d=6 := by omega
      rcases this with rfl|rfl
      · exact ⟨seedNine,seedNine_path,by decide⟩
      · exact ⟨seedThirteen,seedThirteen_path,by decide⟩
  let usable := fun p ↦ Allowed (n-p) (p-1) ∨ (p%2=0 ∧ Allowed (n-p) (p-2))
  have : usable (d+1) ∨ usable (d+2) := by unfold usable Allowed; omega
  rcases this with h|h
  · exact prefix_extreme (p := d+1) (by omega) (by omega) (Or.inl rfl) h
  · exact prefix_extreme (p := d+2) (by omega) (by omega) (Or.inr rfl) h

private theorem sum_extreme {n d : ℕ} (hn : 1<n) (hd : d<n) (hex : ¬(n=5 ∧ d=2)) :
    AtExtreme n d := by
  by_cases h : 2*d<n
  · exact near_extreme hn h hex
  · obtain ⟨f,hf,hx⟩ := near_extreme (d := n-1-d) hn (by omega) (by omega)
    exact ⟨_,rev_path hf,hx⟩


/-- Vertex labels cover 0 through n−1 and adjacent differences cover 1 through n−1.
Both covers are bijective by their finite cardinalities. -/
def GracefulPath (n : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ x < n, ∃ i < n, f i = x) ∧
    ∀ w, 1 ≤ w → w < n → ∃ i, i+1 < n ∧ weight (f i) (f (i+1)) = w

def Crosses (a x y : ℕ) : Prop := (x ≤ a ∧ a < y) ∨ (y ≤ a ∧ a < x)

def AlphaPath (n : ℕ) (f : ℕ → ℕ) : Prop :=
  GracefulPath n f ∧ ∃ a < n-1, ∀ i, i+1<n → Crosses a (f i) (f (i+1))

private def walecki (n x : ℕ) := if x%2=0 then x/2 else n-1-x/2

private theorem walecki_bound {n x : ℕ} (hx : x<n) : walecki n x < n := by
  unfold walecki; split <;> omega

private theorem walecki_hits (n : ℕ) : Covers n (walecki n) := by
  intro x hx
  by_cases h : 2*x<n
  · exact ⟨2*x,h,by simp [walecki]⟩
  · exact ⟨2*(n-1-x)+1,by omega,by unfold walecki; split <;> omega⟩

private theorem walecki_diff {n x y r : ℕ} (hx : x<n) (hy : y<n) (he : x+y=2*r+1) :
    weight (walecki n x) (walecki n y) = n-1-r := by
  unfold walecki weight
  split <;> split <;> omega

private theorem sums_odd {n : ℕ} {f : ℕ → ℕ} (hf : SumPath n f) {i : ℕ} (hi : i+1<n) :
    ∃ r, f i + f (i+1) = 2*r+1 := by
  let odd := fun r : ℕ ↦ 2*r+1
  let s := (Finset.range (n-1)).image odd
  let v := fun j : Fin (n-1) ↦ f j + f (j+1 : ℕ)
  have hcard : s.card = Fintype.card (Fin (n-1)) := by
    simp [s,Finset.card_image_of_injective _ (show Function.Injective odd from
      fun _ _ h ↦ by dsimp [odd] at h; omega)]
  have he := full_image (f := v) hcard (by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx
    have := Finset.mem_range.mp hr
    obtain ⟨j,hj,he⟩ := hf.sums r (by omega)
    exact ⟨⟨j,by omega⟩,he⟩)
  obtain ⟨r,_,hr⟩ := Finset.mem_image.mp ((image_iff v s hcard).mp he |>.1 ⟨i,by omega⟩)
  exact ⟨r,hr.symm⟩

private theorem walecki_graceful {n : ℕ} {f : ℕ → ℕ} (hf : SumPath n f) :
    GracefulPath n (fun i ↦ walecki n (f i)) := by
  constructor
  · intro x hx
    obtain ⟨j,hj,he⟩ := walecki_hits n x hx
    obtain ⟨i,hi,hi'⟩ := hf.labels j hj
    exact ⟨i,hi,by simpa [hi'] using he⟩
  · intro w hw hn
    obtain ⟨i,hi,he⟩ := hf.sums (n-1-w) (by omega)
    have ha := (covers_spec hf.labels).1
    exact ⟨i,hi,(walecki_diff (ha _ (by omega)) (ha _ hi) he).trans (by omega)⟩

private theorem walecki_alpha {n : ℕ} {f : ℕ → ℕ} (hn : 1<n) (hf : SumPath n f) :
    AlphaPath n (fun i ↦ walecki n (f i)) := by
  refine ⟨walecki_graceful hf,(n-1)/2,by omega,?_⟩
  intro i hi
  obtain ⟨r,hr⟩ := sums_odd hf hi
  have ha := (covers_spec hf.labels).1 i (by omega)
  have hb := (covers_spec hf.labels).1 (i+1) hi
  dsimp [Crosses,walecki]; split <;> split <;> omega

private theorem complement_path {n : ℕ} {f : ℕ → ℕ} (hf : GracefulPath n f) :
    GracefulPath n (fun i ↦ n-1-f i) := by
  constructor
  · intro x hx
    obtain ⟨i,hi,he⟩ := hf.1 (n-1-x) (by omega)
    exact ⟨i,hi,by dsimp; omega⟩
  · intro w hw hn
    obtain ⟨i,hi,he⟩ := hf.2 w hw hn
    have ha := (covers_spec hf.1).1 i (by omega)
    have hb := (covers_spec hf.1).1 (i+1) hi
    exact ⟨i,hi,by dsimp [weight] at *; omega⟩

private theorem complement_alpha {n : ℕ} {f : ℕ → ℕ} (hf : AlphaPath n f) :
    AlphaPath n (fun i ↦ n-1-f i) := by
  obtain ⟨hg,a,ha,hc⟩ := hf
  refine ⟨complement_path hg,n-2-a,by omega,?_⟩
  intro i hi
  have h := hc i hi
  have hx := (covers_spec hg.1).1 i (by omega)
  have hy := (covers_spec hg.1).1 (i+1) hi
  unfold Crosses at *; dsimp; omega

theorem rosa_path_alpha (l d : ℕ) (hl : 1≤l) (hd : d≤l) (hex : (l,d)≠(4,2)) :
    ∃ f : ℕ → ℕ, AlphaPath (l+1) f ∧ f d=0 := by
  obtain ⟨g,hg,hd'⟩ := sum_extreme (n := l+1) (d := d) (by omega) (by omega)
    (by rintro ⟨h,rfl⟩; exact hex (by congr 1; omega))
  have h := walecki_alpha (by omega : 1<l+1) hg
  by_cases h0 : g d=0
  · exact ⟨_,h,by simp [walecki,h0]⟩
  · have h1 : g d=1 := by omega
    exact ⟨_,complement_alpha h,by simp [walecki,h1]⟩


/-- The exceptional starting label for the alpha construction occurs at n=4b+1.
Reverse the first 2b+1 Walecki entries and append a graceful path of length 2b
starting at b−1, shifted up by b+1. The bridge from 0 has weight 2b. -/
private theorem middle_start (b : ℕ) (hb : 0<b) :
    ∃ f, GracefulPath (4*b+1) f ∧ f 0=b := by
  let n := 4*b+1
  let p := 2*b+1
  let s := 2*b
  obtain ⟨u,hu,hu0⟩ := block_start s (2*(b-1)) (by unfold Allowed s; omega)
  let g := fun j ↦ walecki s (u j)
  have hg : GracefulPath s g := walecki_graceful hu
  have hg0 : g 0=b-1 := by simp [g,hu0,walecki]
  let f := fun i ↦ if i<p then walecki n (p-1-i) else b+1+g (i-p)
  refine ⟨f,⟨?_,?_⟩,?_⟩
  · intro x hx
    by_cases h : x≤b
    · refine ⟨p-1-2*x,by unfold p; omega,?_⟩
      simp [f,show p-1-2*x<p by unfold p; omega,show p-1-(p-1-2*x)=2*x by unfold p; omega,walecki]
    by_cases h' : x<n-b
    · obtain ⟨j,hj,he⟩ := hg.1 (x-(b+1)) (by unfold n at h'; unfold s; omega)
      exact ⟨p+j,by unfold p s at *; omega,by simp [f,he]; omega⟩
    · let y := 2*(n-1-x)+1
      have hy : y<p := by unfold y p n at *; omega
      refine ⟨p-1-y,by unfold p n y at *; omega,?_⟩
      simp only [f,if_pos (show p-1-y<p by omega),show p-1-(p-1-y)=y by omega]
      unfold walecki y n; split <;> omega
  · intro w hw hw'
    by_cases h : w<s
    · obtain ⟨j,hj,he⟩ := hg.2 w hw h
      refine ⟨p+j,by unfold p s at *; omega,?_⟩
      simp [f,show ¬p+j+1<p by omega,show p+j+1-p=j+1 by omega,weight] at *
      omega
    by_cases he : w=s
    · refine ⟨p-1,by unfold p; omega,?_⟩
      simp [f,show p-1<p by unfold p; omega,show p-1+1=p by unfold p; omega,walecki,hg0,weight]
      unfold s at he; omega
    · let j := n-1-w
      have hj : j+1<p := by unfold j n p s at *; omega
      refine ⟨p-2-j,by unfold p; omega,?_⟩
      simp only [f,if_pos (show p-2-j<p by omega),if_pos (show p-2-j+1<p by omega),
        show p-1-(p-2-j)=j+1 by omega,show p-1-(p-2-j+1)=j by omega]
      apply (walecki_diff (by unfold n p at *; omega) (by unfold n p at *; omega)
        (show j+1+j=2*j+1 by omega)).trans
      unfold j n; omega
  · simp [f,p,walecki]

private theorem low_start {n b : ℕ} (hb : 2*b<n) : ∃ f, GracefulPath n f ∧ f 0=b := by
  by_cases h : Allowed n (2*b)
  · obtain ⟨g,hg,he⟩ := block_start n _ h
    exact ⟨_,walecki_graceful hg,by simp [he,walecki]⟩
  · unfold Allowed at h
    obtain rfl : n=4*b+1 := by omega
    exact middle_start b (by omega)

/-- A permutation of 1 through l, starting at b, with each difference 1 through l−1. -/
theorem graceful_path_start (l b : ℕ) (hb : 1≤b) (hbl : b≤l) :
    ∃ f : ℕ → ℕ, f 0=b ∧ (∀ x, 1≤x → x≤l → ∃ i<l, f i=x) ∧
      ∀ w, 1≤w → w<l → ∃ i, i+1<l ∧ weight (f i) (f (i+1))=w := by
  suffices h : ∃ f, GracefulPath l f ∧ f 0=b-1 by
    obtain ⟨f,hf,he⟩ := h
    refine ⟨fun i ↦ f i+1,by dsimp; omega,?_,?_⟩
    · intro x hx hx'
      obtain ⟨i,hi,he'⟩ := hf.1 (x-1) (by omega)
      exact ⟨i,hi,by dsimp; omega⟩
    · intro w hw hw'
      obtain ⟨i,hi,he'⟩ := hf.2 w hw hw'
      exact ⟨i,hi,by simpa [weight] using he'⟩
  by_cases h : 2*(b-1)<l
  · exact low_start h
  · obtain ⟨g,hg,he⟩ := low_start (n := l) (b := l-b) (by omega)
    exact ⟨_,complement_path hg,by omega⟩


/-- The same root occurs at depth zero on every leg. Depths 1 through l are
the vertices on an individual leg. -/
def rowLabel {k l : ℕ} (F : ℕ → ℕ → ℕ) : SpiderV k l → ℕ
  | .inl _ => F 0 0
  | .inr (i,j) => F i (j+1)

structure GracefulRows (k l : ℕ) (F : ℕ → ℕ → ℕ) : Prop where
  root : ∀ i, F i 0 = F 0 0
  vertices : ∀ x, x ≤ k*l → ∃ i<k, ∃ d≤l, F i d=x
  edges : ∀ w, 1≤w → w≤k*l → ∃ i<k, ∃ d<l, weight (F i d) (F i (d+1))=w

private theorem rows_graceful {k l : ℕ} {F : ℕ → ℕ → ℕ} (h : GracefulRows k l F) :
    IsGraceful k l (rowLabel F) := by
  rw [isGraceful_iff_images]
  constructor
  · apply full_image (by simp [SpiderV,Nat.add_comm])
    intro x hx
    obtain ⟨i,hi,d,hd,he⟩ := h.vertices x (by have := Finset.mem_range.mp hx; omega)
    cases d with
    | zero => exact ⟨.inl (), (h.root i).symm.trans he⟩
    | succ j => exact ⟨.inr (⟨i,hi⟩,⟨j,by omega⟩),he⟩
  · apply full_image (by simp [SpiderE])
    intro w hw
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hw
    obtain ⟨i,hi,d,hd,he⟩ := h.edges w hl hu
    refine ⟨(⟨i,hi⟩,⟨d,hd⟩),?_⟩
    cases d with
    | zero => simpa [edgeWeight,edgeEndpoints,rowLabel,h.root i] using he
    | succ j => simpa [edgeWeight,edgeEndpoints,rowLabel] using he

def liftLabel (a M x : ℕ) := if x≤a then x else x+M

private theorem lift_weight {a M x y : ℕ} (h : Crosses a x y) :
    weight (liftLabel a M x) (liftLabel a M y) = M+weight x y := by
  unfold Crosses at h; unfold liftLabel weight; split <;> split <;> omega

private def stripe (m i j : ℕ) := if j%2=0 then m-1-i else i

private def legLabel (a m l : ℕ) (b : ℕ → ℕ) (i j : ℕ) :=
  a+b j+stripe m i j*l

private theorem stripe_hits {m q : ℕ} (hq : q<m) (j : ℕ) :
    ∃ i<m, stripe m i j=q := by
  by_cases h : j%2=0
  · exact ⟨m-1-q,by omega,by simp [stripe,h]; omega⟩
  · exact ⟨q,hq,by simp [stripe,h]⟩

private theorem stripe_delta {m : ℕ} {t : ℤ} (hl : 1-(m:ℤ)≤t) (hu : t≤(m:ℤ)-1)
    (hp : (t+m-1)%2=0) (j : ℕ) :
    ∃ i<m, (stripe m i j : ℤ)-stripe m i (j+1)=t := by
  let q := ((t+m-1)/2).toNat
  have hq : q<m := by unfold q; omega
  obtain ⟨i,hi,he⟩ := stripe_hits hq j
  refine ⟨i,hi,?_⟩
  unfold stripe at *; split at he <;> split <;> split <;> unfold q at * <;> omega

private theorem leg_internal {m l : ℕ} {b : ℕ → ℕ}
    (hb : ∀ w, 1≤w → w<l → ∃ j, j+1<l ∧ weight (b j) (b (j+1))=w)
    (a : ℕ) {r : ℕ} (hr : 1≤r) (hr' : r<l) {t : ℤ}
    (ht : 1-(m:ℤ)≤t) (ht' : t≤(m:ℤ)-1) (hp : (t+m-1)%2=0) :
    ∃ i<m, ∃ j, j+1<l ∧ weight (legLabel a m l b i j) (legLabel a m l b i (j+1)) =
      (t*(l:ℤ)+r).natAbs := by
  obtain ⟨j,hj,he⟩ := hb r hr hr'
  unfold weight at he
  have realize (s : ℤ) (h₁ : 1-(m:ℤ)≤s) (h₂ : s≤(m:ℤ)-1) (h₃ : (s+m-1)%2=0) :
      ∃ i<m, (legLabel a m l b i j : ℤ)-legLabel a m l b i (j+1) =
        s*(l:ℤ)+((b j : ℤ)-b (j+1)) := by
    obtain ⟨i,hi,hΔ⟩ := stripe_delta h₁ h₂ h₃ j
    refine ⟨i,hi,?_⟩
    rw [← hΔ]
    simp only [legLabel,Nat.cast_add,Nat.cast_mul]
    ring
  by_cases h : (b j : ℤ) - b (j+1) = r
  · obtain ⟨i,hi,hd⟩ := realize t ht ht' hp
    exact ⟨i,hi,j,hj,by simp [weight,hd,h]⟩
  · have h' : (b j : ℤ)-b (j+1) = -(r:ℤ) := by omega
    obtain ⟨i,hi,hd⟩ := realize (-t) (by omega) (by omega) (by omega)
    refine ⟨i,hi,j,hj,?_⟩
    simp only [weight,hd,h',neg_mul,← neg_add,Int.natAbs_neg]

/-- Write w=q*l+r with 1≤r≤l. The root edges supply r=l. For r<l the
signed block offset is q or −(q+1), according to parity, and the required
difference of consecutive permutation entries is respectively r or l−r. -/
private theorem leg_weight_hits {m l a c : ℕ} {b : ℕ → ℕ} (hl : 0<l)
    (hb0 : a+b 0=c+l)
    (hb : ∀ w, 1≤w → w<l → ∃ j, j+1<l ∧ weight (b j) (b (j+1))=w)
    (w : ℕ) (hw : 1≤w) (hw' : w≤m*l) :
    (∃ i<m, weight c (legLabel a m l b i 0)=w) ∨
    ∃ i<m, ∃ j, j+1<l ∧ weight (legLabel a m l b i j) (legLabel a m l b i (j+1))=w := by
  let q := (w-1)/l
  let r := (w-1)%l+1
  have hq : q<m := (Nat.div_lt_iff_lt_mul hl).mpr (by omega)
  have hr : r≤l := by have := Nat.mod_lt (w-1) hl; unfold r; omega
  have he : w=q*l+r := by have := Nat.div_add_mod (w-1) l; unfold q r; rw [Nat.mul_comm] at this; omega
  by_cases h : r=l
  · left
    obtain ⟨i,hi,hs⟩ := stripe_hits hq 0
    exact ⟨i,hi,by unfold legLabel weight; rw [hs,hb0]; omega⟩
  right
  have hc : (w:ℤ)=(q:ℤ)*l+r := by exact_mod_cast he
  have hr0 : 0<r := Nat.zero_lt_succ _
  have hqi : (q:ℤ)<m := by exact_mod_cast hq
  have hq0 : 0≤(q:ℤ) := Int.natCast_nonneg _
  by_cases hp : ((q:ℤ)+m-1)%2=0
  · obtain ⟨i,hi,j,hj,hd⟩ := leg_internal (m := m) hb a hr0 (by omega) (t := q) (by omega) (by omega) hp
    exact ⟨i,hi,j,hj,by rw [hd,← hc,Int.natAbs_natCast]⟩
  · obtain ⟨i,hi,j,hj,hd⟩ := leg_internal (m := m) hb a (r := l-r) (by omega) (by omega)
      (t := -((q:ℤ)+1)) (by omega) (by omega) (by omega)
    have e : -((q:ℤ)+1)*l+((l-r:ℕ):ℤ) = -(w:ℤ) := by
      rw [Nat.cast_sub hr,hc]; ring
    exact ⟨i,hi,j,hj,by rw [hd,e,Int.natAbs_neg,Int.natAbs_natCast]⟩


private def extendRows (h m l a : ℕ) (F : ℕ → ℕ → ℕ) (b : ℕ → ℕ) (i d : ℕ) :=
  if i<h then liftLabel a (m*l) (F i d) else
    if d=0 then F 0 0 else legLabel a m l b (i-h) (d-1)

/-- The endpoints after attaching m legs at root. Each old vertex keeps its own
copy in the left summand. The right summand indexes the new leg vertices. -/
def attachedEndpoints {V E : Type*} (ends : E → V × V) (root : V) {m l : ℕ} :
    E ⊕ SpiderE m l → (V ⊕ SpiderE m l) × (V ⊕ SpiderE m l)
  | .inl e => (.inl (ends e).1, .inl (ends e).2)
  | .inr (i,j) =>
    (if j.val=0 then .inl root else .inr (i,⟨j.val-1,by omega⟩), .inr (i,j))

private def absEdge {V E : Type*} (ends : E → V × V) (f : V → ℕ) (e : E) :=
  weight (f (ends e).1) (f (ends e).2)

/-- Exact vertex and edge images on a finite graph given by its endpoints. -/
def GracefulImages {V E : Type*} [Fintype V] [Fintype E]
    (s : ℕ) (ends : E → V × V) (f : V → ℕ) : Prop :=
  Finset.univ.image f = Finset.range (s+1) ∧
    Finset.univ.image (fun e ↦ weight (f (ends e).1) (f (ends e).2)) = Finset.Icc 1 s

private structure LegCompletion (s m l a c : ℕ) (b : ℕ → ℕ) : Prop where
  vertices : ∀ x≤s+m*l, (∃ y≤s, liftLabel a (m*l) y=x) ∨
    ∃ i<m, ∃ j<l, legLabel a m l b i j=x
  edges : ∀ w, 1≤w → w≤s+m*l → (∃ u, 1≤u ∧ u≤s ∧ m*l+u=w) ∨
    (∃ i<m, weight c (legLabel a m l b i 0)=w) ∨
    ∃ i<m, ∃ j, j+1<l ∧ weight (legLabel a m l b i j) (legLabel a m l b i (j+1))=w

private theorem complete_legs (s m l a c : ℕ) (hl : 0<l) (ha : a≤s)
    (hc : c≤a) (hd : a-c<l) : ∃ b, LegCompletion s m l a c b := by
  obtain ⟨b,hb0,hbv,hbe⟩ := graceful_path_start l (l-(a-c)) (by omega) (by omega)
  refine ⟨b,?_,?_⟩
  · intro x hx
    by_cases hsmall : x≤a
    · exact Or.inl ⟨x,by omega,by simp [liftLabel,hsmall]⟩
    by_cases hbig : a+m*l<x
    · exact Or.inl ⟨x-m*l,by omega,by simp [liftLabel,show ¬x-m*l≤a by omega]; omega⟩
    · let q := (x-a-1)/l
      let r := (x-a-1)%l+1
      have hq : q<m := (Nat.div_lt_iff_lt_mul hl).mpr (by omega)
      have hr : r≤l := by have := Nat.mod_lt (x-a-1) hl; unfold r; omega
      obtain ⟨j,hj,he⟩ := hbv r (Nat.zero_lt_succ _) hr
      obtain ⟨i,hi,hs⟩ := stripe_hits hq j
      refine Or.inr ⟨i,hi,j,hj,?_⟩
      rw [legLabel,he,hs]
      have hx' := Nat.div_add_mod (x-a-1) l
      rw [Nat.mul_comm] at hx'; unfold r q; omega
  · intro w hw hw'
    by_cases hbig : m*l<w
    · exact Or.inl ⟨w-m*l,by omega,by omega,by omega⟩
    · exact Or.inr (leg_weight_hits hl (by omega : a+b 0=c+l) hbe w hw (by omega))

/-- Attach any number of equal legs at a low-labeled vertex of an alpha-labeled
finite graph. Low labels stay fixed and high labels increase by m*l. -/
theorem attach_legs_graceful {V E : Type*} [Fintype V] [Fintype E] {s l a : ℕ}
    (m : ℕ) (ends : E → V × V) (root : V) {f : V → ℕ}
    (nv : Fintype.card V=s+1) (ne : Fintype.card E=s) (hg : GracefulImages s ends f)
    (hl : 0<l) (ha : a<s) (hc : f root≤a) (hd : a-f root<l)
    (cross : ∀ e, Crosses a (f (ends e).1) (f (ends e).2)) :
    ∃ g : V ⊕ SpiderE m l → ℕ, GracefulImages (s+m*l) (attachedEndpoints ends root) g ∧
      ∀ v, g (.inl v)=liftLabel a (m*l) (f v) := by
  obtain ⟨b,hb⟩ := complete_legs s m l a _ hl ha.le hc hd
  let g : V ⊕ SpiderE m l → ℕ := Sum.elim (fun v ↦ liftLabel a (m*l) (f v))
    (fun p ↦ legLabel a m l b p.1 p.2)
  refine ⟨g,⟨?_,?_⟩,fun _ ↦ rfl⟩
  · apply full_image (by simp [SpiderE,nv]; omega)
    intro x hx
    rcases hb.vertices x (by have := Finset.mem_range.mp hx; omega) with ⟨y,hy,he⟩ | ⟨i,hi,j,hj,he⟩
    · have hym : y ∈ Finset.univ.image f := hg.1 ▸ Finset.mem_range.mpr (by omega)
      obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hym
      exact ⟨.inl v,by simpa [g,hv] using he⟩
    · exact ⟨.inr (⟨i,hi⟩,⟨j,hj⟩),he⟩
  · apply full_image (by simp [SpiderE,ne])
    intro w hw
    obtain ⟨h₁,h₂⟩ := Finset.mem_Icc.mp hw
    rcases hb.edges w h₁ h₂ with ⟨u,hu,hu',he⟩ | ⟨i,hi,he⟩ | ⟨i,hi,j,hj,he⟩
    · have hum : u ∈ Finset.univ.image (absEdge ends f) := hg.2 ▸ Finset.mem_Icc.mpr ⟨hu,hu'⟩
      obtain ⟨e,_,hw'⟩ := Finset.mem_image.mp hum
      exact ⟨.inl e, (lift_weight (M := m*l) (cross e)).trans (by change m*l+absEdge ends f e=w; omega)⟩
    · refine ⟨.inr (⟨i,hi⟩,⟨0,hl⟩),?_⟩
      simpa [attachedEndpoints,g,liftLabel,hc] using he
    · refine ⟨.inr (⟨i,hi⟩,⟨j+1,hj⟩),?_⟩
      simpa [attachedEndpoints,g] using he

private theorem attach_rows {h l a : ℕ} (m : ℕ) {F : ℕ → ℕ → ℕ}
    (hl : 0<l) (hg : GracefulRows h l F) (ha : a≤h*l)
    (hc : F 0 0≤a) (hd : a-F 0 0<l)
    (cross : ∀ i<h, ∀ d<l, Crosses a (F i d) (F i (d+1))) :
    ∃ G, GracefulRows (h+m) l G ∧ ∀ i<h, ∀ d, G i d=liftLabel a (m*l) (F i d) := by
  obtain ⟨b,hb⟩ := complete_legs (h*l) m l a _ hl ha hc hd
  let G := extendRows h m l a F b
  have old (i : ℕ) (hi : i<h) (d : ℕ) : G i d=liftLabel a (m*l) (F i d) := by
    simp [G,extendRows,hi]
  have root (i : ℕ) : G i 0=F 0 0 := by simp [G,extendRows,hg.root i,liftLabel,hc]
  have fresh (i j : ℕ) : G (h+i) (j+1)=legLabel a m l b i j := by simp [G,extendRows]
  refine ⟨G,⟨fun i ↦ (root i).trans (root 0).symm,?_,?_⟩,old⟩
  · intro x hx
    rw [Nat.add_mul] at hx
    rcases hb.vertices x hx with ⟨y,hy,he⟩ | ⟨i,hi,j,hj,he⟩
    · obtain ⟨i,hi,d,hd',h'⟩ := hg.vertices y hy
      exact ⟨i,by omega,d,hd',by simp [old i hi,h',he]⟩
    · exact ⟨h+i,by omega,j+1,by omega,(fresh i j).trans he⟩
  · intro w hw hw'
    rw [Nat.add_mul] at hw'
    rcases hb.edges w hw hw' with ⟨u,hu,hu',he⟩ | ⟨i,hi,he⟩ | ⟨i,hi,j,hj,he⟩
    · obtain ⟨i,hi,d,hd',h'⟩ := hg.edges u hu hu'
      exact ⟨i,by omega,d,hd',by rw [old i hi,old i hi,lift_weight (cross i hi d hd'),h',he]⟩
    · exact ⟨h+i,by omega,0,hl,by rw [root,fresh]; exact he⟩
    · exact ⟨h+i,by omega,j+1,hj,by rw [fresh,fresh]; exact he⟩

private theorem one_row {l : ℕ} {f : ℕ → ℕ} (h : GracefulPath (l+1) f) :
    GracefulRows 1 l (fun _ d ↦ f d) := by
  constructor
  · intro i; rfl
  · intro x hx
    obtain ⟨d,hd,he⟩ := h.1 x (by omega)
    exact ⟨0,by decide,d,by omega,he⟩
  · intro w hw hw'
    obtain ⟨d,hd,he⟩ := h.2 w hw (by omega)
    exact ⟨0,by decide,d,by omega,he⟩

private theorem normalized_seed {l d : ℕ} (hl : 1≤l) (hd : d≤l) (hex : (l,d)≠(4,2)) :
    ∃ f a, GracefulPath (l+1) f ∧ f 0≤a ∧ a<l ∧
      (∀ j<l, Crosses a (f j) (f (j+1))) ∧ (f d=0 ∨ f d=l) := by
  obtain ⟨f,⟨hg,a,ha,hc⟩,he⟩ := rosa_path_alpha l d hl hd hex
  by_cases h : f 0≤a
  · exact ⟨f,a,hg,h,by omega,fun j hj ↦ hc j (by omega),Or.inl he⟩
  · let g := fun i ↦ l-f i
    refine ⟨g,l-1-a,by simpa [g] using complement_path hg,by unfold g; omega,by omega,?_,?_⟩
    · intro j hj
      have hx := hc j (by omega)
      have h₁ := (covers_spec hg.1).1 j (by omega)
      have h₂ := (covers_spec hg.1).1 (j+1) (by omega)
      unfold g Crosses at *; omega
    · exact Or.inr (by simp [g,he])

private def fourSeed (i d : ℕ) : ℕ :=
  if i=0 then [2,6,0,8,1][d]! else [2,7,4,5,3][d]!

private theorem fourSeed_rows : GracefulRows 2 4 fourSeed := by
  constructor
  · intro i; unfold fourSeed; split <;> decide
  · intro x hx
    have : x≤8 := hx
    interval_cases x <;> first
      | exact ⟨0,by decide,0,by decide,by decide⟩
      | exact ⟨0,by decide,1,by decide,by decide⟩
      | exact ⟨0,by decide,2,by decide,by decide⟩
      | exact ⟨0,by decide,3,by decide,by decide⟩
      | exact ⟨0,by decide,4,by decide,by decide⟩
      | exact ⟨1,by decide,0,by decide,by decide⟩
      | exact ⟨1,by decide,1,by decide,by decide⟩
      | exact ⟨1,by decide,2,by decide,by decide⟩
      | exact ⟨1,by decide,3,by decide,by decide⟩
      | exact ⟨1,by decide,4,by decide,by decide⟩
  · intro w hw hw'
    have : w≤8 := hw'
    interval_cases w <;> first
      | exact ⟨0,by decide,0,by decide,by decide⟩
      | exact ⟨0,by decide,1,by decide,by decide⟩
      | exact ⟨0,by decide,2,by decide,by decide⟩
      | exact ⟨0,by decide,3,by decide,by decide⟩
      | exact ⟨1,by decide,0,by decide,by decide⟩
      | exact ⟨1,by decide,1,by decide,by decide⟩
      | exact ⟨1,by decide,2,by decide,by decide⟩
      | exact ⟨1,by decide,3,by decide,by decide⟩

private theorem fourSeed_cross : ∀ i<2, ∀ d<4, Crosses 4 (fourSeed i d) (fourSeed i (d+1)) := by
  intro i hi d hd
  interval_cases i <;> interval_cases d <;> unfold Crosses <;> decide

private def fourSingle (d : ℕ) : ℕ := [1,4,0,2,3][d]!

private theorem fourSingle_path : GracefulPath 5 fourSingle := by
  constructor
  · intro x hx
    interval_cases x <;> first
      | exact ⟨0,by decide,by decide⟩
      | exact ⟨1,by decide,by decide⟩
      | exact ⟨2,by decide,by decide⟩
      | exact ⟨3,by decide,by decide⟩
      | exact ⟨4,by decide,by decide⟩
  · intro w hw hw'
    interval_cases w <;> first
      | exact ⟨0,by decide,by decide⟩
      | exact ⟨1,by decide,by decide⟩
      | exact ⟨2,by decide,by decide⟩
      | exact ⟨3,by decide,by decide⟩

private theorem extreme_rows {k l d : ℕ} (hk : 1≤k) (hl : 1≤l) (hd : d≤l) :
    ∃ G, GracefulRows k l G ∧ (G 0 d=0 ∨ G 0 d=k*l) := by
  by_cases hex : (l,d)=(4,2)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hex
    by_cases hk' : k=1
    · subst k
      exact ⟨_,one_row (l := 4) fourSingle_path,Or.inl (by decide)⟩
    let m := k-2
    have hm : 2+m=k := by unfold m; omega
    obtain ⟨G,hG,ho⟩ := attach_rows (a := 4) m (by decide)
      fourSeed_rows (by decide) (by decide) (by decide) fourSeed_cross
    refine ⟨G,hm ▸ hG,Or.inl ?_⟩
    rw [ho 0 (by decide)]; rfl
  · obtain ⟨f,a,hf,h0,ha,hc,he⟩ := normalized_seed hl hd hex
    let m := k-1
    have hm : 1+m=k := by unfold m; omega
    obtain ⟨G,hG,ho⟩ := attach_rows (a := a) m hl (one_row hf)
      (by simpa using ha.le) h0 (by omega) (fun _ _ j hj ↦ hc j hj)
    refine ⟨G,hm ▸ hG,?_⟩
    rw [ho 0 (by decide)]
    rw [← hm,Nat.add_mul,Nat.one_mul]
    rcases he with he|he <;> simp [he,liftLabel,show ¬l≤a by omega]

private def swapLeg (t i : ℕ) := if i=0 then t else if i=t then 0 else i

private theorem swap_twice (t i : ℕ) : swapLeg t (swapLeg t i)=i := by
  by_cases h : i=0 <;> by_cases h' : i=t <;> simp_all [swapLeg]

private theorem swap_rows {k l t : ℕ} {G : ℕ → ℕ → ℕ} (ht : t<k)
    (h : GracefulRows k l G) : GracefulRows k l (fun i ↦ G (swapLeg t i)) := by
  have hb (i : ℕ) (hi : i<k) : swapLeg t i<k := by unfold swapLeg; split <;> (try split) <;> omega
  constructor
  · intro i; exact (h.root _).trans (h.root _).symm
  · intro x hx
    obtain ⟨i,hi,d,hd,he⟩ := h.vertices x hx
    exact ⟨swapLeg t i,hb _ hi,d,hd,by simpa [swap_twice] using he⟩
  · intro w hw hw'
    obtain ⟨i,hi,d,hd,he⟩ := h.edges w hw hw'
    exact ⟨swapLeg t i,hb _ hi,d,hd,by simpa [swap_twice] using he⟩

private theorem complement_graceful {k l : ℕ} {f : SpiderV k l → ℕ} (hg : IsGraceful k l f) :
    IsGraceful k l (fun v ↦ k*l-f v) := by
  obtain ⟨hb,hi,hw,hinj⟩ := hg
  have he (e : SpiderE k l) : edgeWeight (fun v ↦ k*l-f v) e=edgeWeight f e := by
    have := hb (edgeEndpoints e).1
    have := hb (edgeEndpoints e).2
    unfold edgeWeight weight; dsimp only; omega
  refine ⟨fun _ ↦ Nat.sub_le ..,?_,fun e ↦ (he e).symm ▸ hw e,?_⟩
  · intro x y h
    apply hi
    have := hb x
    have := hb y
    dsimp at h; omega
  · intro e e' h
    exact hinj (by simpa only [he] using h)

theorem regular_spider_zero_rotatable (k l : ℕ) (hk : 1≤k) (hl : 1≤l) (v : SpiderV k l) :
    ∃ f : SpiderV k l → ℕ, IsGraceful k l f ∧ f v=0 := by
  suffices h : ∃ f : SpiderV k l → ℕ, IsGraceful k l f ∧ (f v=0 ∨ f v=k*l) by
    obtain ⟨f,hg,he|he⟩ := h
    · exact ⟨f,hg,he⟩
    · exact ⟨_,complement_graceful hg,by simp [he]⟩
  rcases v with u | ⟨i,j⟩
  · obtain ⟨G,hG,hx⟩ := extreme_rows (d := 0) hk hl (Nat.zero_le _)
    exact ⟨_,rows_graceful hG,hx⟩
  · obtain ⟨G,hG,hx⟩ := extreme_rows (d := j.val+1) hk hl j.isLt
    refine ⟨_,rows_graceful (swap_rows i.isLt hG),?_⟩
    by_cases h : i.val=0 <;> simpa [rowLabel,swapLeg,h] using hx

#print axioms rosa_path_alpha
#print axioms graceful_path_start
#print axioms attach_legs_graceful
#print axioms regular_spider_zero_rotatable

end SpiderRotatability

