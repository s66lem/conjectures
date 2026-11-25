import Conjectures.StableKneserK3.DigitSum
import Conjectures.StableKneserK3.MaskCertificate
import Mathlib.Algebra.BigOperators.Fin

namespace StableKneserK3.DualCover

open Finset DigitSum MaskCertificate

def mask {n : ℕ} : List (Fin n) → ℕ
  | [] => 0
  | x :: xs => 2^x.val ||| mask xs

private theorem mem_mask {n : ℕ} (i : Fin n) (l : List (Fin n)) :
    (mask l).testBit i.val = true ↔ i ∈ l := by
  induction l with
  | nil => simp [mask]
  | cons a l ih =>
    simp only [mask, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq,
      ih, List.mem_cons]
    grind [Fin.ext_iff]

def readPoints (n : ℕ) [NeZero n] : ℕ → ℕ → List (Fin n)
  | 0, _ => []
  | len+1, data => Fin.ofNat n (data % 256) :: readPoints n len (data >>> 8)

private theorem list_digits {n bits dims B : ℕ} (p : Fin n → ℕ) (l : List (Fin n))
    (h : ∀ i, ∀ d < dims, digit (2^bits) d (p i) ≤ B) (hlen : l.length*(B+1) ≤ 2^bits)
    {d : ℕ} (hd : d < dims) :
    digit (2^bits) d (l.map p).sum = (l.map (fun x => digit (2^bits) d (p x))).sum := by
  have he (f : Fin n → ℕ) : (∑ i : Fin l.length, f l[i]) = (l.map f).sum := by
    rw [← Fin.sum_ofFn]
    exact congrArg List.sum (List.ofFn_getElem_eq_map l f)
  have hz := digit_sum (univ : Finset (Fin l.length)) (fun i => p l[i]) (M := B)
    (B := 2^bits) (Nat.two_pow_pos _) (fun i _ j hj => h l[i] j hj) (by simpa using hlen) hd
  rwa [he p, he (fun i => digit (2^bits) d (p i))] at hz

structure Data (n : ℕ) where
  bits : ℕ
  dims : ℕ
  bound : ℕ
  allowed : ℕ
  total : ℕ
  column : Fin n → ℕ

structure Valid {n : ℕ} (d : Data n) : Prop where
  positive : 0 < d.dims
  room : n*(d.bound+1) ≤ 2^d.bits
  digits : ∀ i : Fin d.dims, digit (2^d.bits) i d.allowed = d.bound
  columns : ∀ i, d.column i &&& d.allowed = d.column i
  total : ∑ i, d.column i = d.total

private theorem Valid.member {n : ℕ} {d : Data n} (h : Valid d) (i : Fin n) {k : ℕ} (hk : k < d.dims) :
    digit (2^d.bits) k (d.column i) ≤ d.bound :=
  (digit_le_of_mask (j := k) (h.columns i)).trans_eq (h.digits ⟨k,hk⟩)

def checkRow {n : ℕ} (d : Data n) (q bits witness : ℕ) (l : List (Fin n)) : Bool :=
  let s := (l.map d.column).sum
  (l.length ≤ n) && mask l == bits && (s &&& d.allowed) == s &&
    (q * digit (2^d.bits) 0 s < digit (2^d.bits) 0 d.total ||
      witness < d.dims && (q-1)*d.bound + digit (2^d.bits) witness s < digit (2^d.bits) witness d.total)

def rowWeight {n : ℕ} (d : Data n) (S : Finset (Fin n)) (k : ℕ) :=
  ∑ i ∈ S, digit (2^d.bits) k (d.column i)

private theorem sum_distinct_le {n} (f : Fin n → ℕ) (l : List (Fin n)) :
    (∑ i ∈ l.toFinset, f i) ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : a ∈ l
    · simpa [ha] using (ih.trans (Nat.le_add_left _ (f a)))
    · simpa [ha] using Nat.add_le_add_left ih (f a)

def Good {n : ℕ} (d : Data n) (q bits : ℕ) : Prop :=
  ∀ S : Finset (Fin n), (∀ i ∈ S, bits.testBit i.val) →
    (∀ k < d.dims, rowWeight d S k ≤ d.bound) ∧
    (q * rowWeight d S 0 < digit (2^d.bits) 0 d.total ∨
      ∃ k < d.dims, (q-1)*d.bound + rowWeight d S k < digit (2^d.bits) k d.total)

theorem row_sound {n q bits w : ℕ} {d : Data n} (h : Valid d) (l : List (Fin n))
    (hc : checkRow d q bits w l) : Good d q bits := by
  simp only [checkRow, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hlen,rfl⟩,hmask⟩,cases⟩ := hc
  intro S hs
  have hsub : S ⊆ l.toFinset := fun i hi => List.mem_toFinset.mpr ((mem_mask i l).mp (hs i hi))
  have le (k) (hk : k < d.dims) : rowWeight d S k ≤ digit (2^d.bits) k (l.map d.column).sum := by
    rw [list_digits d.column l (fun i _ => h.member i) ((Nat.mul_le_mul_right _ hlen).trans h.room) hk]
    apply (sum_le_sum_of_subset hsub).trans
    exact sum_distinct_le _ _
  refine ⟨fun k hk => ((le k hk).trans (digit_le_of_mask hmask)).trans_eq (h.digits ⟨k,hk⟩), ?_⟩
  rcases cases with hsmall | ⟨hw,hover⟩
  · exact Or.inl ((Nat.mul_le_mul_left _ (le 0 h.positive)).trans_lt hsmall)
  · exact Or.inr ⟨w,hw,(Nat.add_le_add_left (le w hw) _).trans_lt hover⟩

def RowsGood {n : ℕ} (d : Data n) (q : ℕ) (t : Table) (offset len : ℕ) :=
  ∀ i : Fin len, Good d q (t.get (offset+i.val))

theorem rows_block {n : ℕ} [NeZero n] {q off len stride : ℕ} {d : Data n} (h : Valid d)
    (t lengths witnesses : Table) (bytes : ℕ) (test : ∀ i : Fin len,
      checkRow d q (t.get (off+i.val)) (witnesses.get i.val)
        (readPoints n (lengths.get i.val) (bytes >>> (stride*i.val)))) : RowsGood d q t off len :=
  fun i => row_sound h _ (test i)

theorem RowsGood.join {n q a b off : ℕ} {d : Data n} {t : Table}
    (hl : RowsGood d q t off a) (hr : RowsGood d q t (off+a) b) : RowsGood d q t off (a+b) := by
  intro i
  by_cases hi : i.val < a
  · exact hl ⟨i.val,hi⟩
  · have h := hr ⟨i.val-a,by have := i.isLt; omega⟩
    simpa only [show off+a+(i.val-a) = off+i.val by omega] using h

theorem RowsGood.all {n q : ℕ} {d : Data n} {t : Table} (h : RowsGood d q t 0 t.size) :
    ∀ i : Fin t.size, Good d q (t.get i) := fun i => by simpa using h i

theorem triple_surjective {n : ℕ} {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (s : Fin n → Triple G) (h : ∀ a b c : V, a ≠ b → a ≠ c → b ≠ c →
      ¬G.Adj a b → ¬G.Adj a c → ¬G.Adj b c → ∃ i, (s i).val = {a,b,c}) :
    Function.Surjective s := by
  rintro ⟨t,ht⟩
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := card_eq_three.mp ht.1
  obtain ⟨i,he⟩ := h a b c hab hac hbc (ht.2 _ (by simp) _ (by simp))
    (ht.2 _ (by simp) _ (by simp)) (ht.2 _ (by simp) _ (by simp))
  exact ⟨i,Subtype.ext he⟩

/-- The first coordinate chooses a class of at least average weight. The chosen row
supplies a second coordinate on which the other colors have insufficient capacity. -/
theorem no_cover {n q : ℕ} {d : Data n} (h : Valid d) (hq : 0 < q) (col : Fin n → Fin q)
    (hrow : ∀ i : Fin q, ∃ b, Good d q b ∧ ∀ j, col j = i → b.testBit j.val) : False := by
  let S (i : Fin q) := univ.filter (fun j => col j = i)
  have hr (i : Fin q) : (∀ k < d.dims, rowWeight d (S i) k ≤ d.bound) ∧
      (q*rowWeight d (S i) 0 < digit (2^d.bits) 0 d.total ∨
      ∃ k < d.dims, (q-1)*d.bound + rowWeight d (S i) k < digit (2^d.bits) k d.total) := by
    obtain ⟨b,hb,hs⟩ := hrow i
    exact hb (S i) (fun j hj => hs j (mem_filter.mp hj).2)
  have total (k) (hk : k < d.dims) :
      (∑ i, rowWeight d (S i) k) = digit (2^d.bits) k d.total := by
    rw [← h.total, digit_sum _ _ (Nat.two_pow_pos _) (fun i _ j hj => h.member i hj)
      (by simpa using h.room) hk]
    simp only [rowWeight, S, sum_fiberwise_of_maps_to (fun _ _ => mem_univ _)]
  have large : ∃ i, digit (2^d.bits) 0 d.total ≤ q * rowWeight d (S i) 0 := by
    by_contra! hh
    have ne : (univ : Finset (Fin q)).Nonempty := ⟨⟨0,by omega⟩,mem_univ _⟩
    have hh' := sum_lt_sum_of_nonempty ne (fun i _ => hh i)
    rw [← Finset.mul_sum, total 0 h.positive] at hh'
    simp at hh'
  obtain ⟨i,hi⟩ := large
  obtain ⟨k,hk,hover⟩ := (hr i).2.resolve_left (by omega)
  have cap := sum_le_sum (s := (univ : Finset (Fin q)).erase i) (fun j _ => (hr j).1 k hk)
  have he := sum_erase_add (univ : Finset (Fin q)) (fun j => rowWeight d (S j) k) (mem_univ i)
  rw [total k hk] at he
  simp at cap
  omega

/-- A color family inside the candidate set is contained in a star or satisfies
the weighted bounds. The two branches distinguish membership of a pivot. -/
def Covered {n : ℕ} (d : Data n) (q : ℕ) (g : Fin n → ℕ) (stars : ℕ → ℕ) (u : ℕ) : Prop :=
  ∀ S : Finset (Fin n), (∀ i ∈ S, u.testBit i.val) →
    (∀ i ∈ S, ∀ j ∈ S, (g i).testBit j.val = false) →
    (∃ x, ∀ i ∈ S, (stars x).testBit i.val) ∨ ∃ b, Good d q b ∧ ∀ i ∈ S, b.testBit i.val

private theorem bit_diff {a b j : ℕ} (ha : a.testBit j) (hb : b.testBit j = false) :
    (difference a b).testBit j := by simp [difference, Nat.testBit_xor, Nat.testBit_and, ha, hb]

private theorem bit_sub {a b j : ℕ} (h : a &&& b = a) (ha : a.testBit j) : b.testBit j := by
  have ht := congrArg (fun x : ℕ => x.testBit j) h
  simpa [Nat.testBit_and,ha] using ht

/-- Preorder instructions encode a star, a row, or a pivot with right-subtree address. -/
def checkTree {n : ℕ} [NeZero n] (g : Fin n → ℕ) (stars : ℕ → ℕ) (rows words : Table) :
    ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | k+1, addr, u =>
    let code := words.get addr
    let v := code / 4
    if code%4 = 0 then (u &&& stars v) == u else
    if code%4 = 1 then v < rows.size && (u &&& rows.get v) == u else
    let i := Fin.ofNat n (v%n)
    checkTree g stars rows words k (addr+1) (difference u (2^i.val)) &&
      checkTree g stars rows words k (v/n) (difference u (g i))

theorem tree_sound {n q : ℕ} [NeZero n] {d : Data n} {g : Fin n → ℕ} {stars : ℕ → ℕ}
    {rows words : Table} (hr : ∀ i : Fin rows.size, Good d q (rows.get i))
    (k addr u : ℕ) (h : checkTree g stars rows words k addr u) : Covered d q g stars u := by
  induction k generalizing addr u with
  | zero => contradiction
  | succ k ih =>
    intro S hS hi
    simp only [checkTree] at h
    split at h
    · exact Or.inl ⟨_,fun i hm => bit_sub (beq_iff_eq.mp h) (hS i hm)⟩
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact Or.inr ⟨_,hr ⟨_,h.1⟩, fun i hm => bit_sub h.2 (hS i hm)⟩
    simp only [Bool.and_eq_true] at h
    let i := Fin.ofNat n (words.get addr / 4 % n)
    by_cases hm : i ∈ S
    · exact ih _ _ h.2 S (fun j hj => bit_diff (hS j hj) (hi i hm j hj)) hi
    · apply ih _ _ h.1 S _ hi
      intro j hj
      apply bit_diff (hS j hj)
      exact Nat.testBit_two_pow_of_ne (by
        intro eq
        have he : i = j := Fin.ext eq
        exact hm (he.symm ▸ hj))

theorem covered_join {n q : ℕ} {d : Data n} {g : Fin n → ℕ} {stars : ℕ → ℕ}
    {u : ℕ} (i : Fin n)
    (l : Covered d q g stars (difference u (2^i.val)))
    (r : Covered d q g stars (difference u (g i))) : Covered d q g stars u := by
  intro S hS hi
  by_cases hm : i ∈ S
  · exact r S (fun j hj => bit_diff (hS j hj) (hi i hm j hj)) hi
  · apply l S _ hi
    intro j hj
    apply bit_diff (hS j hj)
    exact Nat.testBit_two_pow_of_ne (by intro e; exact hm ((show j = i from (Fin.ext e).symm) ▸ hj))

theorem forces_star {n q : ℕ} {V : Type*} {G : SimpleGraph V}
    {d : Data n} (hd : Valid d) (hq : 0 < q) {g : Fin n → ℕ} {stars : ℕ → ℕ} {u : ℕ}
    (cov : Covered d q g stars u) (hu : ∀ i : Fin n, u.testBit i.val) (s : Fin n → Triple G)
    (surj : Function.Surjective s) (center : ℕ → V)
    (hstar : ∀ x (j : Fin n), (stars x).testBit j.val → center x ∈ (s j).val)
    (hedge : ∀ i j : Fin n, (g i).testBit j.val → Disjoint (s i).val (s j).val)
    (c : Triple G → Fin q) (hc : IsProperColoring G q c) : ∃ i x, ∀ t, c t = i → x ∈ t.val := by
  by_contra! bad
  apply no_cover hd hq (fun j => c (s j))
  intro i
  let S := univ.filter (fun j => c (s j) = i)
  have hs {j} : j ∈ S ↔ c (s j) = i := by simp [S]
  rcases cov S (fun j _ => hu j) (by
    intro a ha b hb
    cases h : (g a).testBit b.val
    · rfl
    · exact False.elim (hc _ _ (hedge a b h) ((hs.mp ha).trans (hs.mp hb).symm))) with
    ⟨x,hx⟩ | ⟨b,hb,hsub⟩
  · obtain ⟨t,ht,miss⟩ := bad i (center x)
    obtain ⟨j,rfl⟩ := surj t
    exact (miss (hstar x j (hx _ (hs.mpr ht)))).elim
  · exact ⟨b,hb,fun j hj => hsub j (hs.mpr hj)⟩

end StableKneserK3.DualCover
