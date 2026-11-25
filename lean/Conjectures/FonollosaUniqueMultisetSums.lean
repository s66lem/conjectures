import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Resolution of Fonollosa's Problem 4 on Unique Multiset Sums in Finite Abelian Groups

In `arXiv:2607.08366v2` (§8, Problem 4) and its companion `arXiv:2607.09949v2` (Remark 1),
Fonollosa asked for the minimum order of a finite abelian group `G` admitting a size-`n`
family `a : ι → G` with unique multiset sums: the only multiplicity vector `m : ι → ℕ` with
`∑ i, m i = n` and `∑ i, m i • a i = ∑ i, a i` is `m ≡ 1`.

We completely resolve Problem 4 for every `n ≥ 1`:
1. `order_lower_bound`: `2 ^ (Fintype.card ι - 1) ≤ Fintype.card G`.
2. `valid_at_lower_bound`: achieved at `2 ^ (n - 1)` by `(Fin (n - 1) → ZMod 2)` with `0`
   and the standard basis.
3. `equality_classification`: equality `Fintype.card G = 2 ^ (Fintype.card ι - 1)` holds
   if and only if `G` is isomorphic as an additive group to `(Subtype (· ≠ anchor) → ZMod 2)`
   via an isomorphism mapping `Pi.single j 1` to `a j - a anchor` (so `G` is an elementary
   abelian 2-group of rank `n - 1` and `a` is an affine basis).
4. `cyclic_modulus_lower_bound`: for cyclic groups `ZMod N` (`N > 0`), the disjointness of
   nonzero doubles `2 • (a i - a anchor)` from all subset sums strengthens the bound to
   `2 ^ (A.card - 1) + (A.card - 1) / Nat.gcd 2 N ≤ N`.
-/

open scoped BigOperators

namespace FonollosaUniqueMultisetSums

variable {ι G : Type*} [Fintype ι] [AddCommGroup G]

/-- A family `a : ι → G` has unique multiset sums if the all-ones vector is the unique
multiplicity vector `m : ι → ℕ` with total multiplicity `|ι|` and sum `∑ i, a i`. -/
def Valid (a : ι → G) : Prop :=
  ∀ m : ι → ℕ, (∑ i, m i) = Fintype.card ι →
    (∑ i, m i • a i) = ∑ i, a i → ∀ i, m i = 1

theorem valid_translate {a : ι → G} (h : Valid a) (c : G) :
    Valid (fun i => a i - c) := by
  intro m hm hsum
  apply h m hm
  simp only [nsmul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hm,
    Finset.sum_const, Finset.card_univ] at hsum
  exact sub_left_injective hsum

open Finset in
private theorem sum_indicator [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    (s : Finset ι) (f : ι → M) :
    (∑ i, if i ∈ s then f i else 0) = ∑ i ∈ s, f i := by
  rw [← sum_filter, filter_mem_eq_inter, univ_inter]

open Finset in
theorem subset_subsum_unique [DecidableEq ι] {a : ι → G} (h : Valid a)
    (s : Finset ι) (m : ι → ℕ) (hm : (∑ i, m i) = s.card)
    (hs : (∑ i, m i • a i) = ∑ i ∈ s, a i) (i : ι) :
    m i = if i ∈ s then 1 else 0 := by
  let c : ι → ℕ := fun j => if j ∈ s then 0 else 1
  have hc : (∑ j, c j) = (univ \ s).card := by
    rw [card_eq_sum_ones, ← sum_indicator (univ \ s)]
    apply sum_congr rfl
    intro j _
    by_cases hjs : j ∈ s <;> simp [c, hjs]
  have hc' : (∑ j, c j • a j) = ∑ j ∈ univ \ s, a j := by
    rw [← sum_indicator (univ \ s)]
    apply sum_congr rfl
    intro j _
    by_cases hjs : j ∈ s <;> simp [c, hjs]
  have hsize : (∑ j, (m j + c j)) = Fintype.card ι := by
    rw [sum_add_distrib, hm, hc, card_sdiff_of_subset (subset_univ s), card_univ]
    have := card_le_univ s
    omega
  have hsum : (∑ j, (m j + c j) • a j) = ∑ j, a j := by
    simp only [add_nsmul, sum_add_distrib, hs, hc']
    rw [add_comm, sum_sdiff (subset_univ s)]
  have hi := h _ hsize hsum i
  by_cases his : i ∈ s <;> simp [c, his] at hi ⊢ <;> omega

open Finset in
theorem valid_injective [DecidableEq ι] {a : ι → G} (h : Valid a) : Function.Injective a := by
  intro i j hij
  let m : ι → ℕ := fun k => if k = i then 1 else 0
  have hm : (∑ k, m k) = ({j} : Finset ι).card := by simp [m]
  have hsum : (∑ k, m k • a k) = ∑ k ∈ ({j} : Finset ι), a k := by
    simp [m, hij]
  have hi := subset_subsum_unique h {j} m hm hsum i
  by_contra hne
  simp [m, hne] at hi

open Finset in
theorem subset_sum_injective_of_valid [DecidableEq ι] {a : ι → G} (h : Valid a)
    {anchor : ι} (hanchor : a anchor = 0) :
    Set.InjOn (fun s : Finset ι => ∑ i ∈ s, a i)
      (↑((univ.erase anchor).powerset) : Set (Finset ι)) := by
  intro s hs t ht heq
  have hs' := mem_powerset.mp (mem_coe.mp hs)
  have ht' := mem_powerset.mp (mem_coe.mp ht)
  have hnots : anchor ∉ s := fun hh => (notMem_erase anchor univ) (hs' hh)
  have hnott : anchor ∉ t := fun hh => (notMem_erase anchor univ) (ht' hh)
  suffices local_inj : ∀ (u v : Finset ι), anchor ∉ u → anchor ∉ v →
      u.card ≤ v.card → (∑ i ∈ u, a i) = (∑ i ∈ v, a i) → u = v by
    rcases le_total s.card t.card with hle | hle
    · exact local_inj s t hnots hnott hle heq
    · exact (local_inj t s hnott hnots hle heq.symm).symm
  intro u v hnu hnv hle huv
  let m : ι → ℕ :=
    fun i => (if i ∈ u then 1 else 0) + (if i = anchor then v.card - u.card else 0)
  have hm : (∑ i, m i) = v.card := by
    simp only [m, sum_add_distrib, sum_indicator, sum_ite_eq', mem_univ, ↓reduceIte,
      sum_const, Nat.nsmul_eq_mul, mul_one, Nat.add_sub_of_le hle]
  have hms : (∑ i, m i • a i) = ∑ i ∈ v, a i := by
    rw [← huv]
    simp only [m, add_nsmul, sum_add_distrib, ite_smul, one_nsmul, zero_nsmul,
      sum_indicator, sum_ite_eq', mem_univ, ↓reduceIte, hanchor, smul_zero, add_zero]
  ext i
  have hi := subset_subsum_unique h v m hm hms i
  by_cases hia : i = anchor
  · subst i
    simp [hnu, hnv]
  · by_cases hiu : i ∈ u <;> by_cases hiv : i ∈ v <;> simp_all [m]

open Finset in
/-- Main lower bound: any finite abelian group admitting a valid size-`n` family has
order at least `2 ^ (n - 1)`. -/
theorem order_lower_bound [DecidableEq ι] [Fintype G] {a : ι → G}
    (h : Valid a) (anchor : ι) :
    2 ^ (Fintype.card ι - 1) ≤ Fintype.card G := by
  classical
  let f : Finset ι → G := fun s => ∑ i ∈ s, (a i - a anchor)
  have hf : Set.InjOn f (↑((univ.erase anchor).powerset) : Set (Finset ι)) :=
    subset_sum_injective_of_valid (valid_translate h (a anchor)) (sub_self _)
  have hc := card_le_univ (((univ.erase anchor).powerset).image f)
  rwa [card_image_of_injOn hf, card_powerset, card_erase_of_mem (mem_univ anchor), card_univ] at hc

theorem two_nsmul_eq_zero_of_subsum [DecidableEq ι] {a : ι → G} (h : Valid a)
    {anchor : ι} (hanchor : a anchor = 0)
    (i : ι) (s : Finset ι) (hns : anchor ∉ s) (hs : (∑ j ∈ s, a j) = 2 • a i) :
    2 • a i = (0 : G) := by
  by_contra hne
  have hna : i ≠ anchor := by
    intro hi
    subst i
    simp [hanchor] at hne
  have hpos : 0 < s.card := by
    by_contra! hnpos
    have hempty : s = ∅ := Finset.card_eq_zero.mp (by omega)
    exact hne (by simpa [hempty] using hs.symm)
  let m : ι → ℕ :=
    fun j => (if j = i then 2 else 0) + (if j = anchor then s.card - 1 else 0)
  have hm : (∑ j, m j) = (insert anchor s).card := by
    simp only [m, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, Finset.card_insert_of_notMem hns]
    omega
  have hsum : (∑ j, m j • a j) = ∑ j ∈ insert anchor s, a j := by
    simp only [m, add_nsmul, Finset.sum_add_distrib, ite_smul, zero_nsmul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hanchor, smul_zero, add_zero,
      Finset.sum_insert hns, zero_add, hs]
  have hi := subset_subsum_unique h (insert anchor s) m hm hsum i
  by_cases his : i ∈ insert anchor s <;> simp [m, hna, his] at hi

open Finset in
theorem order_lower_bound_with_doubles [DecidableEq ι] [DecidableEq G] [Fintype G] {a : ι → G}
    (h : Valid a) (anchor : ι) :
    2 ^ (Fintype.card ι - 1) +
      ((univ.image fun i => 2 • (a i - a anchor)).erase 0).card ≤ Fintype.card G := by
  classical
  let b : ι → G := fun i => a i - a anchor
  have hb : Valid b := valid_translate h (a anchor)
  have hzero : b anchor = 0 := sub_self _
  let p := (univ.erase anchor).powerset
  let f : Finset ι → G := fun s => ∑ i ∈ s, b i
  let d := (univ.image fun i => 2 • b i).erase 0
  have hdis : Disjoint (p.image f) d := by
    rw [Finset.disjoint_left]
    intro x hx hd
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hx
    obtain ⟨hne, hd⟩ := mem_erase.mp hd
    obtain ⟨i, _, hi⟩ := mem_image.mp hd
    have hns : anchor ∉ s := fun hm => (notMem_erase anchor univ) (mem_powerset.mp hs hm)
    exact hne (hi.symm.trans (two_nsmul_eq_zero_of_subsum hb hzero i s hns hi.symm))
  have hf : Set.InjOn f (↑p : Set (Finset ι)) :=
    subset_sum_injective_of_valid hb hzero
  have hc := card_le_univ (disjUnion (p.image f) d hdis)
  rw [card_disjUnion, card_image_of_injOn hf] at hc
  simpa [p, d, b, card_powerset, card_erase_of_mem (mem_univ anchor)] using hc

open Finset in
theorem two_nsmul_eq_zero_of_minimum [DecidableEq ι] [Fintype G] {a : ι → G}
    (h : Valid a) (anchor : ι) (heq : Fintype.card G = 2 ^ (Fintype.card ι - 1))
    (g : G) : 2 • g = (0 : G) := by
  classical
  let b : ι → G := fun i => a i - a anchor
  have hb : Valid b := valid_translate h (a anchor)
  have hzero : b anchor = 0 := sub_self _
  let p := (univ.erase anchor).powerset
  let f : Finset ι → G := fun s => ∑ i ∈ s, b i
  have hf : Set.InjOn f (↑p : Set (Finset ι)) :=
    subset_sum_injective_of_valid hb hzero
  have hcard : (p.image f).card = Fintype.card G := by
    rw [card_image_of_injOn hf, heq]
    simp [p, card_powerset, card_erase_of_mem (mem_univ anchor)]
  have hall : p.image f = univ := eq_univ_of_card _ hcard
  have hcover : ∀ x : G, ∃ s : Finset ι, anchor ∉ s ∧ (∑ j ∈ s, b j) = x := by
    intro x
    have hx : x ∈ p.image f := by simp [hall]
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hx
    exact ⟨s, fun hm => (notMem_erase anchor univ) (mem_powerset.mp hs hm), rfl⟩
  obtain ⟨s, _, rfl⟩ := hcover g
  rw [Finset.smul_sum]
  apply sum_eq_zero
  intro i _
  obtain ⟨t, hnt, ht⟩ := hcover (2 • b i)
  exact two_nsmul_eq_zero_of_subsum hb hzero i t hnt ht

/-! ### Complete equality classification: elementary abelian 2-group + affine basis -/

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hlt : x.val < 2 := x.val_lt
  rcases (by omega : x.val = 0 ∨ x.val = 1) with h0 | h1
  · left
    rw [← ZMod.natCast_zmod_val x, h0]
    simp
  · right
    rw [← ZMod.natCast_zmod_val x, h1]
    simp

open Finset in
/-- Equality classification: if `|G| = 2 ^ (|ι| - 1)` admits a valid family `a : ι → G`,
then `G` is isomorphic as an additive group to `({i : ι // i ≠ anchor} → ZMod 2)` via
the isomorphism sending each standard basis vector `Pi.single j 1` to `a j - a anchor`. -/
theorem equality_classification [DecidableEq ι] [Fintype G] {a : ι → G}
    (h : Valid a) (anchor : ι) (heq : Fintype.card G = 2 ^ (Fintype.card ι - 1)) :
    ∃ e : ({i : ι // i ≠ anchor} → ZMod 2) ≃+ G,
      ∀ j : {i : ι // i ≠ anchor}, e (Pi.single j 1) = a j.1 - a anchor := by
  classical
  let b : ι → G := fun i => a i - a anchor
  have hb : Valid b := valid_translate h (a anchor)
  have hzero : b anchor = 0 := sub_self _
  have h2g : ∀ g : G, 2 • g = 0 := two_nsmul_eq_zero_of_minimum h anchor heq
  let φ_fun : ({i : ι // i ≠ anchor} → ZMod 2) → G :=
    fun v => ∑ j : {i : ι // i ≠ anchor}, (v j).val • b j.1
  have h_add_coeff : ∀ (x y : ZMod 2) (g : G), ((x + y).val • g) = x.val • g + y.val • g := by
    intro x y g
    rcases zmod2_eq_zero_or_one x with rfl | rfl <;> rcases zmod2_eq_zero_or_one y with rfl | rfl
    · simp
    · simp
    · simp
    · have h0 : ((1 : ZMod 2) + 1).val = 0 := by decide
      have h1 : (1 : ZMod 2).val = 1 := by decide
      rw [h0, zero_nsmul, h1, one_nsmul, ← two_nsmul]
      exact (h2g g).symm
  let φ : ({i : ι // i ≠ anchor} → ZMod 2) →+ G :=
    { toFun := φ_fun
      map_zero' := by simp [φ_fun]
      map_add' := fun v w => by
        simp only [φ_fun, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => h_add_coeff (v j) (w j) (b j.1) }
  have h_single : ∀ j : {i : ι // i ≠ anchor}, φ (Pi.single j 1) = b j.1 := by
    intro j
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, φ_fun]
    rw [Finset.sum_eq_single j]
    · simp [ZMod.val_one]
    · intro k _ hkj
      simp [Pi.single_eq_of_ne hkj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have h_inj : Function.Injective φ := by
    intro v w hvw
    let supp : ({i : ι // i ≠ anchor} → ZMod 2) → Finset ι :=
      fun u => (univ.filter fun j : {i : ι // i ≠ anchor} => u j = 1).map
        ⟨Subtype.val, Subtype.val_injective⟩
    have h_val_eq : ∀ u : {i : ι // i ≠ anchor} → ZMod 2, φ u = ∑ i ∈ supp u, b i := by
      intro u
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, φ_fun, supp, Finset.sum_map,
        Function.Embedding.coeFn_mk]
      rw [← Finset.sum_filter_add_sum_filter_not univ (fun j : {i : ι // i ≠ anchor} => u j = 1)]
      have h0 : (∑ j ∈ univ.filter (fun j => ¬ u j = 1), (u j).val • b j.1) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hne : u j ≠ 1 := (Finset.mem_filter.mp hj).2
        have hzj : u j = 0 := (zmod2_eq_zero_or_one (u j)).resolve_right hne
        simp [hzj]
      rw [h0, add_zero]
      apply Finset.sum_congr rfl
      intro j hj
      have h1 : u j = 1 := (Finset.mem_filter.mp hj).2
      simp [h1, ZMod.val_one]
    have h_mem : ∀ u, supp u ∈ (univ.erase anchor).powerset := by
      intro u
      rw [mem_powerset]
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact mem_erase.mpr ⟨j.2, mem_univ _⟩
    have h_sub_inj := subset_sum_injective_of_valid hb hzero
    have h_supp_eq : supp v = supp w :=
      h_sub_inj (mem_coe.mpr (h_mem v)) (mem_coe.mpr (h_mem w))
        (by dsimp only; rw [← h_val_eq v, ← h_val_eq w]; exact hvw)
    funext j
    have hiff : v j = 1 ↔ w j = 1 := by
      have hv : j.1 ∈ supp v ↔ v j = 1 := by
        simp [supp]
      have hw : j.1 ∈ supp w ↔ w j = 1 := by
        simp [supp]
      rw [← hv, ← hw, h_supp_eq]
    rcases zmod2_eq_zero_or_one (v j) with hv0 | hv1 <;>
      rcases zmod2_eq_zero_or_one (w j) with hw0 | hw1 <;> simp_all
  have h_card_dom : Fintype.card ({i : ι // i ≠ anchor} → ZMod 2) = Fintype.card G := by
    rw [heq, Fintype.card_fun, ZMod.card, Fintype.card_subtype_compl,
      show Fintype.card {i : ι // i = anchor} = 1 from Fintype.card_unique]
  have h_bij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨h_inj, h_card_dom⟩
  exact ⟨AddEquiv.ofBijective φ h_bij, h_single⟩

/-! ### Sharpness construction at `|G| = 2 ^ (n - 1)` -/

def zeroAndBasis (n : ℕ) (i : Fin (n + 1)) (j : Fin n) : ZMod 2 :=
  if i = j.castSucc then 1 else 0

theorem valid_zeroAndBasis (n : ℕ) : Valid (zeroAndBasis n) := by
  classical
  intro m hm hsum
  have hun : ∀ j : Fin n, m j.castSucc % 2 = 1 := by
    intro j
    have hh := congrFun hsum j
    simp only [Finset.sum_apply, Pi.smul_apply, zeroAndBasis, smul_ite,
      smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hh
    have hh' : (m j.castSucc : ZMod 2) = 1 := by
      simpa only [nsmul_eq_mul, mul_one] using hh
    simpa using (ZMod.natCast_eq_natCast_iff' (m j.castSucc) 1 2).mp hh'
  have hpos : ∀ j : Fin n, 1 ≤ m j.castSucc := by
    intro j
    have := hun j
    omega
  have hrest : ∀ j : Fin n, m j.castSucc = 1 := by
    intro j
    have hlow : n ≤ ∑ k : Fin n, m k.castSucc := by
      calc
        n = ∑ _k : Fin n, (1 : ℕ) := by simp
        _ ≤ ∑ k : Fin n, m k.castSucc := Finset.sum_le_sum fun k _ => hpos k
    have hupper : ∑ k : Fin n, m k.castSucc ≤ n + 1 := by
      rw [Fin.sum_univ_castSucc, Fintype.card_fin] at hm
      omega
    have hle : (∑ k : Fin n, (1 + if k = j then m j.castSucc - 1 else 0)) ≤
        ∑ k : Fin n, m k.castSucc := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hkj : k = j
      · subst k
        simp only [↓reduceIte]
        exact (Nat.add_sub_of_le (hpos j)).le
      · simpa [hkj] using hpos k
    simp [Finset.sum_add_distrib] at hle
    have := hun j
    omega
  have hlast : m (Fin.last n) = 1 := by
    rw [Fin.sum_univ_castSucc, Fintype.card_fin] at hm
    simpa [hrest] using hm
  exact Fin.lastCases hlast hrest

theorem valid_at_lower_bound (n : ℕ) :
    ∃ a : Fin (n + 1) → (Fin n → ZMod 2),
      Valid a ∧ Fintype.card (Fin n → ZMod 2) = 2 ^ n :=
  ⟨zeroAndBasis n, valid_zeroAndBasis n, by simp [ZMod.card]⟩

/-! ### Sharpened cyclic lower bound matching `FormalConjectures/Arxiv/2607.08366/MinModulus.lean` -/

open Finset in
/-- Standalone cyclic residue-set validity predicate corresponding to
`FormalConjectures/Arxiv/2607.08366/MinModulus.lean`. -/
def IsValidMod {N : ℕ} (A : Finset (ZMod N)) : Prop :=
  ∀ m : ZMod N → ℕ, ∑ a ∈ A, m a = A.card →
    ∑ a ∈ A, (m a : ZMod N) * a = ∑ a ∈ A, a → ∀ a ∈ A, m a = 1

open Finset in
theorem valid_of_isValidMod {N : ℕ} {A : Finset (ZMod N)} (h : IsValidMod A) :
    Valid (fun x : A => (x : ZMod N)) := by
  intro m hm hsum x
  let M : ZMod N → ℕ := fun z => if hz : z ∈ A then m ⟨z, hz⟩ else 0
  have hM (z : A) : M z = m z := by simp [M, z.property]
  have hsize : ∑ z ∈ A, M z = A.card := by
    rw [← sum_coe_sort, ← Fintype.card_coe]
    simpa only [hM] using hm
  have hval : (∑ z ∈ A, (M z : ZMod N) * z) = ∑ z ∈ A, z := by
    rw [← sum_coe_sort A (fun z : ZMod N => (M z : ZMod N) * z),
      ← sum_coe_sort A (fun z : ZMod N => z)]
    simpa only [nsmul_eq_mul, hM] using hsum
  simpa only [hM] using h M hsize hval x x.property

private theorem card_zmod_two_mul_fiber {N : ℕ} [NeZero N] (y : ZMod N) :
    (Finset.univ.filter fun x : ZMod N => 2 • x = y).card ≤ Nat.gcd 2 N := by
  by_cases hne : (Finset.univ.filter fun x : ZMod N => 2 • x = y).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    have hx₀' : 2 • x₀ = y := (Finset.mem_filter.mp hx₀).2
    have hsub : (Finset.univ.filter fun x : ZMod N => 2 • x = y) ⊆
        (Finset.univ.filter fun d : ZMod N => 2 • d = 0).image (fun d => x₀ + d) := by
      intro x hx
      have hx' : 2 • x = y := (Finset.mem_filter.mp hx).2
      refine Finset.mem_image.mpr ⟨x - x₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by abel⟩
      rw [smul_sub, hx', hx₀', sub_self]
    have hcard_le := (Finset.card_le_card hsub).trans Finset.card_image_le
    refine hcard_le.trans ?_
    -- Count solutions to `2 • d = 0` in `ZMod N`: at most `gcd 2 N`
    have hg : Nat.gcd 2 N = 1 ∨ Nat.gcd 2 N = 2 := by
      have hd : Nat.gcd 2 N ∣ 2 := Nat.gcd_dvd_left 2 N
      have hpos : 0 < Nat.gcd 2 N := Nat.gcd_pos_of_pos_left N (by decide)
      have hle : Nat.gcd 2 N ≤ 2 := Nat.le_of_dvd (by decide) hd
      omega
    rcases hg with h1 | h2
    · rw [h1]
      have hsub1 : (Finset.univ.filter fun d : ZMod N => 2 • d = 0) ⊆ {0} := by
        intro d hd
        have hd0 : 2 • d = 0 := (Finset.mem_filter.mp hd).2
        have hodd : ¬ 2 ∣ N := by
          intro h2n
          have : 2 ∣ Nat.gcd 2 N := Nat.dvd_gcd dvd_rfl h2n
          omega
        have hdv : N ∣ 2 * d.val := by
          have : ((2 * d.val : ℕ) : ZMod N) = 0 := by simpa [two_nsmul, two_mul] using hd0
          exact (ZMod.natCast_eq_zero_iff _ _).mp this
        have hcop : Nat.Coprime N 2 := by
          rw [Nat.coprime_comm]
          exact h1
        have hdn : N ∣ d.val := hcop.dvd_of_dvd_mul_left hdv
        have hlt : d.val < N := d.val_lt
        have hv0 : d.val = 0 := Nat.eq_zero_of_dvd_of_lt hdn hlt
        apply Finset.mem_singleton.mpr
        rw [← ZMod.natCast_zmod_val d, hv0]
        simp
      exact (Finset.card_le_card hsub1).trans (by simp)
    · rw [h2]
      have h2dvd : 2 ∣ N := h2 ▸ Nat.gcd_dvd_right 2 N
      obtain ⟨k, hk⟩ := h2dvd
      have hsub2 : (Finset.univ.filter fun d : ZMod N => 2 • d = 0) ⊆ {0, (k : ZMod N)} := by
        intro d hd
        have hd0 : 2 • d = 0 := (Finset.mem_filter.mp hd).2
        have hdv : N ∣ 2 * d.val := by
          have : ((2 * d.val : ℕ) : ZMod N) = 0 := by simpa [two_nsmul, two_mul] using hd0
          exact (ZMod.natCast_eq_zero_iff _ _).mp this
        have hkd : k ∣ d.val := by
          obtain ⟨t, ht⟩ := hdv
          exact ⟨t, by nlinarith⟩
        have hlt : d.val < 2 * k := by
          have := d.val_lt
          omega
        obtain ⟨t, ht⟩ := hkd
        have ht_le : t = 0 ∨ t = 1 := by
          have hkpos : 0 < k := by
            have := NeZero.pos N
            omega
          have ht2 : t < 2 := by nlinarith
          omega
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases ht_le with rfl | rfl
        · left
          have hv0 : d.val = 0 := by omega
          rw [← ZMod.natCast_zmod_val d, hv0]
          simp
        · right
          have hv : d.val = k := by omega
          rw [← ZMod.natCast_zmod_val d, hv]
      exact (Finset.card_le_card hsub2).trans Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

open Finset in
/-- Sharpened cyclic lower bound: for any valid residue set `A ⊆ ZMod N` (`N > 0`, `A` nonempty),
`2 ^ (A.card - 1) + (A.card - 1) / Nat.gcd 2 N ≤ N`
(equivalently `2 ^ (n - 1) + ⌈n / gcd(2, N)⌉ - 1 ≤ N`). -/
theorem cyclic_modulus_lower_bound {N : ℕ} [NeZero N] {A : Finset (ZMod N)}
    (h : IsValidMod A) (hne : A.Nonempty) :
    2 ^ (A.card - 1) + (A.card - 1) / Nat.gcd 2 N ≤ N := by
  classical
  obtain ⟨a₀, ha₀⟩ := hne
  let anchor : A := ⟨a₀, ha₀⟩
  have hval := valid_of_isValidMod h
  have hbound := order_lower_bound_with_doubles hval anchor
  rw [Fintype.card_coe, ZMod.card] at hbound
  -- Lower bound the number of distinct nonzero doubles `2 • (x - a₀)`
  let img := (univ : Finset A).image (fun x : A => 2 • ((x : ZMod N) - a₀))
  have h0mem : (0 : ZMod N) ∈ img :=
    mem_image.mpr ⟨anchor, mem_univ _, by simp [anchor]⟩
  have hfib : A.card ≤ img.card * Nat.gcd 2 N := by
    have hsum : (univ : Finset A).card =
        ∑ y ∈ img, ((univ : Finset A).filter fun x : A => 2 • ((x : ZMod N) - a₀) = y).card :=
      Finset.card_eq_sum_card_image (fun x : A => 2 • ((x : ZMod N) - a₀)) univ
    rw [Finset.card_univ, Fintype.card_coe] at hsum
    rw [hsum]
    calc
      ∑ y ∈ img, ((univ : Finset A).filter fun x : A => 2 • ((x : ZMod N) - a₀) = y).card
          ≤ ∑ _y ∈ img, Nat.gcd 2 N := by
            apply Finset.sum_le_sum
            intro y _
            let emb : A → ZMod N := fun x => (x : ZMod N) - a₀
            have hemb : Function.Injective emb := by
              intro x₁ x₂ hx
              exact Subtype.ext (sub_left_injective hx)
            have hsub : ((univ : Finset A).filter fun x : A => 2 • ((x : ZMod N) - a₀) = y).image emb ⊆
                (univ : Finset (ZMod N)).filter fun z : ZMod N => 2 • z = y := by
              intro z hz
              obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
              exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩
            calc
              ((univ : Finset A).filter fun x : A => 2 • ((x : ZMod N) - a₀) = y).card
                  = (((univ : Finset A).filter fun x : A => 2 • ((x : ZMod N) - a₀) = y).image emb).card :=
                    (card_image_of_injective _ hemb).symm
              _ ≤ ((univ : Finset (ZMod N)).filter fun z : ZMod N => 2 • z = y).card :=
                    card_le_card hsub
              _ ≤ Nat.gcd 2 N := card_zmod_two_mul_fiber y
      _ = img.card * Nat.gcd 2 N := by simp
  have hg : Nat.gcd 2 N = 1 ∨ Nat.gcd 2 N = 2 := by
    have hd : Nat.gcd 2 N ∣ 2 := Nat.gcd_dvd_left 2 N
    have hpos : 0 < Nat.gcd 2 N := Nat.gcd_pos_of_pos_left N (by decide)
    have hle : Nat.gcd 2 N ≤ 2 := Nat.le_of_dvd (by decide) hd
    omega
  have hcard_erase : (A.card - 1) / Nat.gcd 2 N ≤ (img.erase 0).card := by
    rw [card_erase_of_mem h0mem]
    have hpos : 1 ≤ img.card := card_pos.mpr ⟨0, h0mem⟩
    have hApos : 1 ≤ A.card := card_pos.mpr ⟨a₀, ha₀⟩
    rcases hg with hg1 | hg2
    · rw [hg1] at hfib ⊢; omega
    · rw [hg2] at hfib ⊢; omega
  have himg_eq : img = (univ : Finset A).image (fun i : A => 2 • ((i : ZMod N) - (anchor : ZMod N))) := rfl
  rw [← himg_eq] at hbound
  omega

end FonollosaUniqueMultisetSums
