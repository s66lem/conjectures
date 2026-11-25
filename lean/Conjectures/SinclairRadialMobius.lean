import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Field.Rat

/-!
# Disproof of Sinclair's Conjecture C (arXiv:2608.18519)

Conjecture C asserts `h_k^β(M) ≥ h_{r-k}^β(M)` for every simple matroid `M` of rank `r` and
every `k ≤ r/2`, where `h_k^β = dim C_k` is the Hilbert function of the cyclic module generated
from `v_r = β_E e_E` by the radial derivative `D_β = S⁻¹ U^β K` and the coordinate lowering
operators `L_a^β` (§2, Propositions 2.2–2.3).

For the cycle matroid of `G₄ = K_{1,1,4} + {2,3}` (rank 5, 10 edges) we prove `h_2 = 31` and
`h_3 = 32`, so the conjecture fails at `k = 2`.

Method. The rescaling `f ↦ (X ↦ f X / β_X)` is a linear equivalence that turns `L_a^β` into a
0/1 matrix and `D_β` into a matrix with entries `rk Y / (n - |X|)`, independent of `β`.
All counting is done on natural-number vectors (`D_β` scaled by `2520 = lcm(1..9)`):
* upper bounds: the cyclic module lies in the common kernel of explicit integer relations whose
  pivot structure makes a coordinate projection injective;
* lower bounds: explicit words whose value matrix on selected columns is invertible mod 1009.
Kernel checks use `decide +kernel` over packed natural-number tables.
-/

namespace SinclairRadialMobius

open Finset

/-! ## Simple matroids, flats and the operators of §2 -/

/-- A simple matroid on `Fin n`, axiomatized by its rank function. -/
structure SimpleMatroid (n : ℕ) where
  rk : Finset (Fin n) → ℕ
  rk_empty : rk ∅ = 0
  rk_le_card : ∀ S, rk S ≤ S.card
  rk_mono : ∀ {S T}, S ⊆ T → rk S ≤ rk T
  rk_submod : ∀ S T, rk (S ∪ T) + rk (S ∩ T) ≤ rk S + rk T
  simple_singleton : ∀ a : Fin n, rk {a} = 1
  simple_pair : ∀ a b : Fin n, a ≠ b → rk {a, b} = 2

namespace SimpleMatroid
variable {n : ℕ} (M : SimpleMatroid n)
def rank : ℕ := M.rk univ
end SimpleMatroid

variable {n : ℕ}

def IsFlat (M : SimpleMatroid n) (F : Finset (Fin n)) : Prop :=
  ∀ e, M.rk (insert e F) = M.rk F → e ∈ F

def Flat (M : SimpleMatroid n) := {F : Finset (Fin n) // IsFlat M F}

noncomputable instance (M : SimpleMatroid n) : Fintype (Flat M) := by
  classical
  unfold Flat
  infer_instance

def cl (M : SimpleMatroid n) (S : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun e => M.rk (insert e S) = M.rk S)

/-- `β_F`: number of ordered bases of `M|F`. -/
def beta (M : SimpleMatroid n) (F : Finset (Fin n)) : ℕ :=
  (M.rk F).factorial * ((F.powersetCard (M.rk F)).filter (fun B => M.rk B = M.rk F)).card

def Covers (M : SimpleMatroid n) (X Y : Finset (Fin n)) (a : Fin n) : Prop :=
  M.rk Y = M.rk X + 1 ∧ X ⊆ Y ∧ a ∉ X ∧ cl M (insert a X) = Y

open Classical in
/-- Coordinate lowering operator `L_a^β` (Prop. 2.2). -/
noncomputable def L_beta (M : SimpleMatroid n) (a : Fin n) :
    (Flat M → ℚ) →ₗ[ℚ] (Flat M → ℚ) where
  toFun f X := ∑ Y : Flat M,
    if Covers M X.1 Y.1 a then ((beta M X.1 : ℚ) / (beta M Y.1 : ℚ)) * f Y else 0
  map_add' f g := by
    ext X; simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Y _ => ?_
    split_ifs <;> ring
  map_smul' c f := by
    ext X; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    split_ifs <;> ring

def K_op (M : SimpleMatroid n) : (Flat M → ℚ) →ₗ[ℚ] (Flat M → ℚ) where
  toFun f Y := (M.rk Y.1 : ℚ) * f Y
  map_add' f g := by ext; simp [mul_add]
  map_smul' c f := by ext; simp; ring

noncomputable def U_beta (M : SimpleMatroid n) : (Flat M → ℚ) →ₗ[ℚ] (Flat M → ℚ) :=
  ∑ a : Fin n, L_beta M a

def S_inv (M : SimpleMatroid n) : (Flat M → ℚ) →ₗ[ℚ] (Flat M → ℚ) where
  toFun f X := if X.1.card < n then (1 / ((n - X.1.card : ℕ) : ℚ)) * f X else 0
  map_add' f g := by ext; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c f := by
    ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Radial derivative `D_β = S⁻¹ U^β K` (Prop. 2.3). -/
noncomputable def D_beta (M : SimpleMatroid n) : (Flat M → ℚ) →ₗ[ℚ] (Flat M → ℚ) :=
  (S_inv M).comp ((U_beta M).comp (K_op M))

/-- `v_r = β_E e_E`. -/
def v_top (M : SimpleMatroid n) : Flat M → ℚ :=
  fun X => if X.1 = univ then (beta M univ : ℚ) else 0

/-- The graded cyclic module `C_k`. -/
noncomputable def C_mod (M : SimpleMatroid n) : ℕ → Submodule ℚ (Flat M → ℚ)
  | 0 => Submodule.span ℚ {v_top M}
  | k + 1 => (C_mod M k).map (D_beta M) ⊔ ⨆ a : Fin n, (C_mod M k).map (L_beta M a)

noncomputable def h_beta (M : SimpleMatroid n) (k : ℕ) : ℕ := Module.finrank ℚ (C_mod M k)

/-! ## Generic rank-function lemmas -/

lemma mono_of_insert {α : Type*} [DecidableEq α] {f : Finset α → ℕ}
    (h : ∀ S e, f S ≤ f (insert e S)) {S T : Finset α} (hST : S ⊆ T) : f S ≤ f T := by
  have key : ∀ D : Finset α, f S ≤ f (D ∪ S) := by
    intro D
    induction D using Finset.induction_on with
    | empty => simp
    | insert a D _ ih => rw [Finset.insert_union]; exact ih.trans (h _ _)
  simpa [Finset.sdiff_union_of_subset hST] using key (T \ S)

/-- Local submodularity on single insertions implies submodularity. -/
lemma submod_of_local {α : Type*} [DecidableEq α] {f : Finset α → ℕ}
    (h : ∀ S a b, f (insert a (insert b S)) + f S ≤ f (insert a S) + f (insert b S))
    (S T : Finset α) : f (S ∪ T) + f (S ∩ T) ≤ f S + f T := by
  have step1 : ∀ A C e, f (insert e (C ∪ A)) + f A ≤ f (insert e A) + f (C ∪ A) := by
    intro A C e
    induction C using Finset.induction_on with
    | empty => simp
    | insert c C _ ih =>
      rw [Finset.insert_union]
      have := h (C ∪ A) e c
      omega
  have step2 : ∀ I D, I ⊆ S → f (D ∪ S) + f I ≤ f S + f (D ∪ I) := by
    intro I D hI
    induction D using Finset.induction_on with
    | empty => simp
    | insert d D _ ih =>
      rw [Finset.insert_union, Finset.insert_union]
      have h1 := step1 (D ∪ I) S d
      have e1 : S ∪ (D ∪ I) = D ∪ S := by
        ext x; simp only [Finset.mem_union]; have := @hI x; tauto
      rw [e1] at h1
      omega
  have := step2 (S ∩ T) (T \ S) Finset.inter_subset_left
  rwa [Finset.sdiff_union_self_eq_union, Finset.union_comm T S, Finset.inter_comm,
    Finset.sdiff_union_inter, Finset.inter_comm] at this

/-! ## Bitmask encoding of subsets of `Fin 10` -/

def mask (S : Finset (Fin 10)) : ℕ := ∑ i ∈ S, 2 ^ (i : ℕ)

def ofMask (m : ℕ) : Finset (Fin 10) := univ.filter (fun i => m.testBit i)

lemma testBit_mask (S : Finset (Fin 10)) (j : ℕ) :
    (mask S).testBit j = true ↔ ∃ h : j < 10, (⟨j, h⟩ : Fin 10) ∈ S := by
  induction S using Finset.induction_on_max generalizing j with
  | empty => simp [mask]
  | insert a s ha ih =>
    have hlt : mask s < 2 ^ (a : ℕ) := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      by_contra hc
      obtain ⟨h10, hm⟩ := (ih i).1 (by simpa using hc)
      have := ha _ hm
      rw [Fin.lt_def] at this
      simp at this
      omega
    have has : a ∉ s := fun h => lt_irrefl _ (ha a h)
    have heq : mask (insert a s) = mask s ||| 2 ^ (a : ℕ) := by
      rw [Nat.or_two_pow_eq_add_of_lt hlt, mask, Finset.sum_insert has, add_comm]; rfl
    rw [heq, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨h, hm⟩ | h)
      · exact ⟨h, Finset.mem_insert_of_mem hm⟩
      · simp only [decide_eq_true_eq] at h; subst h; exact ⟨a.2, by simp⟩
    · rintro ⟨h, hm⟩
      rcases Finset.mem_insert.1 hm with h' | h'
      · right; simp [← h']
      · left; exact ⟨h, h'⟩

lemma mem_iff_testBit {S : Finset (Fin 10)} {i : Fin 10} :
    i ∈ S ↔ (mask S).testBit i = true := by
  rw [testBit_mask]; exact ⟨fun h => ⟨i.2, h⟩, fun ⟨_, h⟩ => h⟩

lemma mask_lt (S : Finset (Fin 10)) : mask S < 1024 := by
  apply Nat.lt_pow_two_of_testBit (n := 10)
  intro i hi
  by_contra hc
  obtain ⟨h, _⟩ := (testBit_mask S i).1 (by simpa using hc)
  omega

lemma ofMask_mask (S : Finset (Fin 10)) : ofMask (mask S) = S := by
  ext i; simp [ofMask, ← mem_iff_testBit]

lemma mask_ofMask {m : ℕ} (hm : m < 1024) : mask (ofMask m) = m := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 10
  · rw [Bool.eq_iff_iff, testBit_mask]
    simp [ofMask, hj]
  · have h1 : m.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm
        (show (1024 : ℕ) ≤ 2 ^ j from (show (1024 : ℕ) = 2 ^ 10 by norm_num) ▸
          Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [h1, Bool.eq_false_iff]
    intro h; obtain ⟨h, _⟩ := (testBit_mask _ j).1 h; exact hj h

lemma mem_ofMask {m : ℕ} {i : Fin 10} : i ∈ ofMask m ↔ m.testBit i = true := by simp [ofMask]

lemma mask_insert (a : Fin 10) (S : Finset (Fin 10)) :
    mask (insert a S) = mask S ||| 2 ^ (a : ℕ) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Bool.eq_iff_iff, testBit_mask, Nat.testBit_or, Bool.or_eq_true, testBit_mask,
    Nat.testBit_two_pow, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hm⟩
    rcases Finset.mem_insert.1 hm with h' | h'
    · right; rw [← h']
    · left; exact ⟨h, h'⟩
  · rintro (⟨h, hm⟩ | h)
    · exact ⟨h, Finset.mem_insert_of_mem hm⟩
    · subst h; exact ⟨a.2, by simp⟩

lemma mask_empty : mask ∅ = 0 := by simp [mask]

lemma forall_finset {P : Finset (Fin 10) → Prop} (h : ∀ m < 1024, P (ofMask m))
    (S : Finset (Fin 10)) : P S := ofMask_mask S ▸ h _ (mask_lt S)

lemma ofMask_inj {m m' : ℕ} (hm : m < 1024) (hm' : m' < 1024) (h : ofMask m = ofMask m') :
    m = m' := by
  rw [← mask_ofMask hm, ← mask_ofMask hm', h]

/-! ## The cycle matroid of `G₄ = K_{1,1,4} + {2,3}` -/

/-- Edges of `G₄` on vertices `0..5`. -/
def G4edges : List (ℕ × ℕ) :=
  [(0,1), (0,2), (0,3), (0,4), (0,5), (1,2), (1,3), (1,4), (1,5), (2,3)]

/-- `𝔽₂`-incidence vector of edge `e`, as a bitmask over the 6 vertices. -/
def incid (e : ℕ) : ℕ := match G4edges.getD e (0, 0) with | (u, v) => 2 ^ u ||| 2 ^ v

/-- Insert a vector into an `𝔽₂` echelon basis (vectors as bitmasks). -/
def gf2Insert (B : List ℕ) (v : ℕ) : List ℕ :=
  let c := B.foldl (fun c b => min c (c ^^^ b)) v
  if c = 0 then B else B ++ [c]

/-- `𝔽₂`-rank of the incidence vectors of the edges in the bitmask `m`
(Gaussian elimination). -/
def gf2Rank (m : ℕ) : ℕ :=
  ((List.range 10).foldl (fun B e => if m.testBit e then gf2Insert B (incid e) else B) []).length

/-! ## Packed tables (generated; every entry used is checked by `decide +kernel` below)

* `RT`: rank of each edge bitmask (3 bits per mask); `INCT`: elements raising the rank.
* `FLT`: the 110 flats as bitmasks, sorted by rank (rank-3 flats are indices `44..87`,
  rank-2 flats `11..43`, the top flat is `109`).
* `CLT`: index of `cl(X_i ∪ a)` (7 bits, entry `10 i + a`); `IDXT`: inverse of `FLT`.
* `BAST`: a basis of each flat; `CDT`: cardinality of each flat.
* `REL k`: integer relations `(column, coefficient)` satisfied by all words of length `k`, pivot
  first; `AF k`: the remaining (free) columns.
* `WD k`, `SEL k`: words and columns for the lower bound; `WT k`: their values mod 1009,
  `NT k`: the inverse matrix mod 1009 (10 bits per entry).
-/

def RT : ℕ := 0xb6db6db6db6db6db6db6db6cb6db6db6db6db6db6db6db6cb6db6db6db6db6db6db6db6cb6db64b6db64b6db64b2cb23b6db6d924924b6db6c924923b6db6d924924b6db6c924923b6db6d924924b6db6c924923b6db6492491bb2cb238e38dab6db6db6db6c924924924923b6db6db6db6c924924924923b6db6db6db6c924924924923b6db64b2cb2392491b8e38dab6db6c9249239249236db6dab6db6c9249239249236db6dab6db6c9249239249236db6dab2cb238e38da8e38da69a691b6db6db6db6db6db6db6db6cb64b64b64b64b64b64b64b23b6d924b6d924b6d924b6c923b6491bb6491bb6491bb238dab6db6d924924b6db6c924923b64b6491b91bb64b2391b8dab6d9249246dbb6c9239236dab6491b91b6d2b238da8da691b6db6db6db6c924924924923b64b64b64b2391b91b91b8dab6d924b6c9239246db9236dab6491bb238da91b6d28da691b6db6c9249239249236db6dab64b2391b8da91b8da6d2691b6c9239236da9236da6da491b238da8da6918da691691448

def INCT : ℕ := 0x1f0000000000000000000000000000000000000000000000000000000000000000000000000000001f0000000000000000000000000000000000000000000000000000000000000000000000000000001f0000000000000001986600000000000000019866000000000000000198660007900079000791987f0000000000000000000022088220882208822088000000000000000000972208822088220882209f0000000000000000000022088220882208822088000000000000000000972208822088220882209f0000000000000000000022088220882208822088000000000000000000972208822088220882209f000000000000000198662208822088220883b8ee000f1000f1000f1198f7220f9220f9220f93b8ff000000000000000000000000000000000000010f441104411044110441104411044110441104411f000000000000000000000000000000000000010f441104411044110441104411044110441104411f000000000000000000000000000000000000010f441104411044110441104411044110441104411f000000000000000198660016900169001691996f4411044110441105d9764417944179441795d97f000000000000000001872208822088220882218f441104411044110441976619866198661986619f000000000000000001872208822088220882218f441104411044110441976619866198661986619f000000000000000001872208822088220882218f441104411044110441976619866198661986619f001e1001e1001e1199e7221e9221e9221e93b9ef441f1441f1441f15d9f7661f9661f9661f97f9ff0000000000000000000000000000000000000000000000000000000000000000000000000000001f0000088a220000088a220000088a220000088a220000088a220000088a220000088a220023d88a3f000000000091244912440000000000912449124400000000009124491244000000025b912449125f0000088a229124499a660000088a229124499a660000088a229124499a660007988a7b9127d99a7f0000000000000000000022088220882208822088000000000000000000972208822088220882209f0000088a220000088a2222088aaaaa22088aaaaa0000088a22002b588ab722088aaaaa222bdaaabf000000000091244912442208822088b32ccb32cc00000002d391244912d722088222dbb32ccb32df0000088a229124499a6622088aaaaab32ccbbaee000f188af3912f599af7220f9aaafbb32fdbbaff000000000000000000000000000000000000010f441104411044110441104411044110441104411f0000088a220000088a220000088a220032d88b2f44110ccb3244110ccb3244110ccb324433dccb3f00000000009124491244000000034b912449134f4411044110d5354d5354441104435bd5354d535f0000088a229124499a660016988b6b9136d99b6f44110ccb32d5354ddb7644179ccb7bd537dddb7f000000000000000001872208822088220882218f441104411044110441976619866198661986619f0000088a22003a588ba722088aaaaa223adaabaf44110ccb32443b5ccbb766198eebba663bdeebbf00000003c391244913c722088223cbb32ccb33cf44110443d3d5354d53d766198663dbf73dcf73df001e188be3913e599be7221e9aabebb33edbbbef441f1ccbf3d53f5ddbf7661f9eebfbf73fdffbff

def FLT : ℕ := 0xfffe0e6786ddf68c3af0bbe969e21e775c26eda45292c348b41683ce0360c4708c1ae0a4289a1a709a26786216839c0681996118255548509334a1244310a340cd308b02aca42509216052128380d02c0701ac0280982108220680580501204450841102300a0240892108214048114420c02809023060140480c02a004008010020040080100200400

def CLT : ℕ := 0x6ddbb76ed000006dda0006dda0000001b76edda0006d000368000036800000000da0006d01b76ed00036eddbb400001b406d0000000dbb76ed01b400001b4000000006d01b7680da0006d01b7680000006ddbb406ddbb7680000006dda00000da00000da0368000036eddbb406dda0006d000006d000368001b406dda036edda03680dbb406d01b7680dbb406d00036eddbb4000da036ed01b76ed01b4000da036eddbb7680da0006d01b76eddbb400000036ed000006cd9af5ead5ac000d800069d1a74e900035e9d2035e9d200000d7a346b019f3eb0003569d3a738001a406c0000066cb972e501ac066cc035e4c9ac06b01972eb019728001a8065cb932800194069cc00000c7a74e901a3280018c065cb94069ca00069ca0000001af5e3c600062c5ac069c9a7480c400069019f2e5cb8800001976000003661c387061d80006c017efdebf7f5800186f800186f80d400061bd87080d5875000182fdfbfa805fd203080d203080d203400c2034610186ee1d203000d3a6ee901a7480bfa4000bfa4000d002fe8017c05cbf7f480bda4069b8034e9ce030e1b984000cf87380bf76fdf019c05fcd84000cc030e1b7872e100032e10003280cb80000cb6f2e5019735f0198000bf6afdfcb7c065017c06500032de019405aca032e5c984061b403080c98725f016ef80bf9005fc787080c600061b3874e9b603480b3a4069cb77280cb6406501971dfbf8c0000162fdfd3a6d690002c00d3a72dccb9405800032e5c5870e1b000000c58715fbf66f80018805f0002bd6ad56a53a754057014a951a13e7d0015a900013a6cc9930055a33a700972a555015284d9b2c04993400539f3264a920004c015684c995684c9802b8001223c68d16246ac02400ad0e143830eb008f580407efa040aa0234380023438002a008d09fc600f5e46a6022c37d0de80a70e9808906040794c040a520000a4edd3a72ea94701480386ed9bb7a31803b7002335691a84600e9bc600e9b809f1403a6cd5d009eea7c400e5bb46f3c0379d0dd809c019c3650e6c274026b300e98ba990dd00990dd0098026417202632633004c9d01c4e000182f81026bf6f3403000b9bb798f9b4c00bd70099326406f300406f30000971a333600002d591a5436b0d7805a025439501a32800164a01024bd74e972d00024ba92f1bb16eb004900dc02b54a54a84e993255601223448501f3c855240074e1b3464c1a528ce80525cb1528554a238a401324448105084d97260078e1a853a0345890f003059a4c7cc9522386004c5531e305080d16980104a84d152084d152000509101c305080c101

def IDXT : ℕ := 0xdbffffffffffffffffffffffffffffffffffffffffffffffffffffecfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5ffffffffffffffffffffffffffffffffabffffffffd7ffffffffffffffd3ffffffffffffffffffffffffe8ffffffffffffd6ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaffff9fffffffffd4ff4fffffffffabffffffffffffffffffffffffffe6cbffffffffffffffffffffffffd2ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff93ffffffffd1ffffffffffe87fff3fffffffffaaffffffffffffe3ffffffffffffceffffffffffffcd99ffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8bffffffffcbff2bffffffffa8ff27ffffffffa7fe9bffffffd28affffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0ffffffffffffffffffffffffffffffffffffffffffffff83fc8fffffffbfffffffffffffffffffffffffffffffffffffffdefffffc7ffffffffffe37ffffffffffffffffffffffffffffffffffc5ff13fa4fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1ffffffffffffffffff77fc2fffffffff07fa3fffffffffffffffffffff81ffffffffffdcfffffbffffffbefffffa2ffffffffffffffffffffffffd0fffffffbdfef3fa0fffff9ffe7bf89fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6ffbbfffdd7ffffffffffffffffee7f9dfffffffffffffffffffdafffffb8fffffff6fffffffffffb6fffff9cfffffffffffffffffffb5fed3f9bffffffffffcd7ffffff99fe63f88fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff67fb3ffffffffecbf97ffffffffec7f96fffcafffe53f87fffffd8fffffb0fffffaffffff93fffffaefffff92fffff9121fff86fffffadfeb3f8ffffff8efe37f85fffff8cfe2ff84fffff83fe08080

def BAST : ℕ := 0x7de08658605d68438f003c961e01e075c206da45292c348b41683ce016084708418e0a4209218701a00786016039c0680196118205548508134a1244310a3400d308b002ca42509216052128380d02c0701ac0280182108200680580501200450841102300a0240092108214048014420c02809003060140480c02a004008010020040080100200400

def CDT : ℕ := 0xa5658555855574744444443443443444463443353353353333353353333333333322322322223222222322223222232222211111111110

def REL2 : List (List (ℕ × ℤ)) := [[(12, 1), (0, 1), (4, -1), (8, -1)], [(13, 1), (2, 1), (5, -1), (10, -1)], [(15, 1), (1, 1), (7, -1), (9, -1)], [(19, 1), (0, 1), (4, -1), (16, -1)], [(21, 1), (3, 1), (6, -1), (18, -1)], [(22, 1), (1, 1), (7, -1), (17, -1)], [(24, 1), (0, 1), (8, -1), (16, -1)], [(25, 1), (1, 1), (9, -1), (17, -1)], [(27, 1), (0, 2), (4, -1), (8, -1), (16, -1)], [(28, 1), (1, 2), (7, -1), (9, -1), (17, -1)], [(38, 1), (29, 1), (33, -1), (35, -1)], [(42, 1), (30, 1), (34, -1), (39, -1)], [(43, 1), (31, 1), (37, -1), (40, -1)]]

def AF2 : List ℕ := [1, 0, 3, 2, 31, 4, 6, 5, 7, 9, 17, 8, 11, 26, 20, 16, 10, 23, 30, 18, 34, 14, 29, 32, 33, 37, 40, 41, 36, 35, 39]

def WD2 : List (List ℕ) := [[0, 1], [0, 2], [0, 3], [0, 4], [0, 9], [1, 2], [1, 3], [1, 4], [1, 6], [1, 7], [1, 8], [2, 3], [2, 4], [2, 5], [2, 7], [2, 8], [3, 4], [3, 5], [3, 6], [3, 8], [3, 9], [4, 5], [4, 6], [4, 7], [4, 9], [7, 9], [8, 9], [3, 10], [4, 10], [10, 3], [10, 4]]

def SEL2 : List ℕ := [44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 58, 60, 61, 62, 64, 67, 70, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85]

def WT2 : ℕ := 0xb2d4d0029a52000523ec000005200000000d791c473ebfae3800000000008e0000023800000a6800522cb0014d52000fb00052000003ebfae380000000000d791c470008e0000023800000000007b1ec001ec7b0007b1ec000007b000000007b1ec7b1ec7b1ec00000000007b000001ec000007b0007b1ec001ec7b0007b0007b000001ec7b1ec00000000007b1ec7b0007b000001ec000000000000000000000000000000000000000000000000000000100401004010040000401000010040100000000000000000000000000000000001004010040100000000000000100400004010000100400000000000000000000000000000000000000000100401004010000000000004000000100000000000040000000000010040000001000000000100000000000000000000000010000000400000000040000001004000000000000004000000000000004000040100000000000000000001000000000100000004010000000000000010000000000004000040000000000000000100000000000000000000000000000000000000000000000401004000000000000004010000100000004000000000000000000000100400004000040000000000000000000000004000000000400000010000000001000010040000000000000000100000000010040000000000000000100000000000040000000004000040100000000000000000400000010000000000000000000100000004000000000000000000000100000004000000100000000000000000400000000000100000000000000000000000000000000001004000000100001000000000000000000000000100000004000000100400000000040100400000000000100000004000000000001000000040000000000000000100001000000000100001000010000000000000010000000400000000000100000000000040100000000000000000400004000000100000004000000000000000000000000400004000000000000004000000000000004000000100000004000000000000000000040000000000000000000400004000000000000000000000000401000000040000400000000000000000000010000100400004000000000001004000040100000000000040000001000000000100001004000000000000000010000000001000010000000400004000000000000004000000100000000010000000000004000000000001000000040000001000000040000001000000000000000000000040000400004000000000000000000040000001000000040000001000000000000000004000040000000000000040000000000000040000000000000000000000000000000000000004000000000000000000000000001000000040000000000000000000000000000000000000000000000000001004000000000401004000000100000004010000000000000010000100000000010000000000000000000000400000000000100000004000000000001000000000100000000010000000000004000000000000000000000100000004000000000001000010000000000000010000000000000000000100000000000040000000004000000000400004000040000000000000040000000000000000100000000000040000400000000000000400

def NT2 : ℕ := 0xde0003f00000000002f57e5f97e5f9002f500000bd400bd400002f5002f5001f83f0fc0000000000bd4003f000000000000000000000fc00000bd4003f000002f5000003f000002f5bd78a00246002c1003285862a8a8003e800000677e00000032001f8000000c800001303def77e5f90000000000002f500000000003f00000000000003f000002f5000fc00000bd4003f000002f5bd40000378000fc002f57e5f97e40000000001f9bd400002f5002f500000bd400002f57e0003f0fc0038a00246002c1000fa00000ca1618aa2a19c007e00000032001f8000000c8004c2f73ddf97e400000001e4000000000000001f87e1f87e1f8000000000000000000000000000000001f900000000001e400000007e1f87e1f800000000007e0000000000000000000000000000001f900000000000000000000000007e400000007e400000000000000000000000000000000000007e1f80000000000000003f0fcbd40000000bd40000000002f5bd4003f0fcbd6f5000fc3f000000000000000067001ab1e530000c9a41c771df83f800001917e400003bf7e1f900000efdf8002c1beaf37e1f8000671e5ab001307e0fe000003269071dc7644007e4007e3bf001f9001f8efc00b06f3be9f87e00000000000000000000000000000000000000000007e40000000001f90000000000000007e1f80000000079002f500000000003f1f87e0007e0003f000000fc002f5000003f0003f000002f53f000000001e400bd40000000000fc7e0007e1f8002f5000003f0003f000000fc000fc000003f2f519c006ac004c0003269071dc7000fe00000649f900000efc007e400003bf00000b06fabcdf87e00000000000fc002f500000000000000000000bd400000fc000fc00000bd400002f5000003f2f500000000003f000bd400000000000000000000fc00000bd400bd400000fc00000bd400002f53f00000079002f5000fc7e1f80000000000001f83f000000fc002f5000003f000000fc00000bd4fc000001e400bd4003f1f8001f800000000007e2f5000003f0003f000000fc000003f000000fcbd40019c006ac004c0003f800000c9a41c771d92001f900000efc007e400003bf002c1bcefa7e1f80000000000000fc0000000000bd4000000000000bd400000fc000fc00000bd400bd400000fcbd40000000000003f00000000002f50000000000000fc00000bd400bd400000fc002f500000bd4fc00000000000000000000000000000000000000000000000000000007e000001f900000000007e40000000de0000000000000001f97e4007e5f900000000007e400000000000000000000000000000000de000000007e5f9001f900000000007e400000007e40000000000000000000000000000000000000000000000000000000000000000000000007e0000000000000000007e400000007e400e280091b78b0400ca1618aa2a7e4fb7e40019df8000000c8007e000000327e4004c0f73f9f97e400e2b7891800b05f93edf9003285862a8a867001f8000000c8007e0007e432001303f8f77e5f90000000000bd6f53f000000003f00000000000fc3f000bd6f5bd6f57e4fc3f1f800000000007e00000000002f5bd4fc00000000fc0000000000bd6f57e4fc3f0fc3f000bd6f57e000000007e000

def REL3 : List (List (ℕ × ℤ)) := [[(25, 1), (4, 1), (16, -1), (21, -1)]]

def AF3 : List ℕ := [4, 3, 1, 2, 0, 6, 29, 28, 8, 7, 16, 21, 9, 12, 20, 11, 14, 5, 22, 19, 15, 13, 10, 27, 26, 32, 31, 18, 24, 17, 23, 30]

def WD3 : List (List ℕ) := [[0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 2, 4], [0, 3, 4], [0, 3, 9], [0, 4, 9], [1, 2, 3], [1, 2, 4], [1, 2, 7], [1, 2, 8], [1, 3, 4], [1, 3, 6], [1, 3, 8], [1, 4, 6], [1, 4, 7], [2, 3, 4], [2, 3, 5], [2, 3, 8], [2, 4, 5], [2, 4, 7], [3, 4, 5], [3, 4, 6], [3, 4, 9], [3, 8, 9], [4, 7, 9], [1, 10, 3], [1, 10, 4], [2, 10, 3], [2, 10, 4], [3, 4, 10]]

def SEL3 : List ℕ := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 38, 39, 40, 41, 42, 43]

def WT3 : ℕ := 0x7b1ec7b000001ec7b1ec7b000001ec7b1ec7b000001ec7b000001ec7b000001ec7b000000000000053548fb00052000fb000d780047000537eb8e000fac0052000fac00fb0008e000fb00000000001485214dfb14800000fb3eb8e3eb0000052000d791c00000537eb00000fb23800000fb000001480000053548fb00052000fb35e000004714d00238fac00fad48000008e3ec00000fafec0000000000520005214dfb14800000fb238fafeb001480035e0011c0014d00238003ec003eb003ec000005200000000000000000000000000010040000001004000000000000000000040100400004010040000000004010000000000000000000000000000000000100400000010040100001004010000100400004010000000000000000000000001004000000100401004000000100400000010040000001004000000000000004010000000001004000040000000004000040000000004000000000000000010040000000000000040100000000010040100000000010000100000000010000000001004000000000000000000000000400004000040000400004000000000400000000000000000000000040000400004000000000001000010000000400000000000000400000010000000400004000040000000000000000000000000010000100401000000040000000000000000000400000000040000000004010000000400000010000000400000010000000001000010000000400000010000000001000000000000000000000000100000004010040000000004000040000000004000040000000004000000000400000000040000000000000040000400004000040100000000010000000000000000000000401000000000100000000000040000001000000040000000000000040000000004000040100000000000000000400000000000000400000010040100000004000000000000000010000000001000010000100000000010000000400000000040000001000000000000401000010000000001000000000000000000010000000000004000000000401004000000000401000000000100001000000000100000000010000000001000000000000000000000000000000000000000000000000010040100400000000040000000004000000100000000000000000000000000000100401004000000000000000000000100000000010000000001000000000000000000000000000000000000040000001004000040000000004000000000400000000000000000000000000000000000010040100000000000000100000000010000000001000000000000000000000000000000000000000000000000000000100400000010040000400000000040000000000000040100000000000000000001004000000100400000000000000001000000000100000000000040100000000000040000001000000000000000000000000000000000000000000400000010000000000000000000100000004000000000000000000000000400000000040000000000000040000000000000000100400000010000000000004000000000400000000000000000000000000100000000000000100000000010000000400000000000000000000010000000001000000040000000000000000000000004000040000001000000000100000000010000000000000000000100000000000000000000004000000000000000000000000000000000040000000000010000000000000000000000000000010000000000

def NT3 : ℕ := 0xbd4fc00000000003f000bd400000fc002f50000000000000fc00000bd400bd4000000000000002f5000fc000003f00000000bd4fc00000002f500000000003f000002f5002f5000001e4000000000000001f87e1f800000000000000000000000000000000000000000000000000000000000000000000003f2f50000000000bd4003f000002f5000fc0000000000000fc00000bd400bd4000000000000000fc002f500000bd400000003f2f500000000fc00000000003f000002f5002f5000001e4000000000000001f80000000000000007e00000000001f8000000000000000000000000000000de00000000000fc3f1f97e5f9bd400bd400002f5002f5000000000000000bd6f5000fc3f0fc3f00000000000670000000000000000000000000002fa8c4fe001fcca400404000000000000000d0bccc80006700000000000000000000bea313f8007f0000000000000ca4004040000000000d0bcc00000c8000000000000000000000000000000001f900000000007e400001f9001f800000000007e0007e1f8000000000000000000000000000000000000000000000000007e0007e400000000000000000001f9000000038a000003f2f50000000000bd4003f0f7703ef000f932000bc000002f5000003f32100b290038a00000000003f2f5000003ddc0fbc003e400002f5000fc32000bc000002f500321008003f329000000000019c0000000000000000000000000fe002fa8c5fc00329001010000000000002f3340c80000019c000000000000000003f800bea317f0000000000000003290010100000002f334000000c800000000000000000000000000000000000000000000000000001f8001f9000000000000000001f90000000000000000000000000001f900000000007e400000007e4007e00000000001f8001f8001f80000000000e28fc002f500000bd400000003f3ef000f7700f9000c8002f0bd400000fc00002c872900000e2800000fc002f500000fbc003ddc03e6f500000000fc000c8002f0bd40000002c84fc00329000000038a0000000000000000000000000000f7702f37e1f532000bc1f9000000000000321bdf290000000000e280000000000000000000000002f37e0f7701f5000c87e6f00000000000002f7c87291e40000000002f5bd5f87e0003f0003f000002f5002f5001f800000000003f0fc7e2f5bd4fc3f000de0000000000000001f9001f900000000007e40000000000000000000000000007e40000000000000038a000000000000000000003ddc0bcdf87d400000000000032000bc1f90000000321bdc000032900000e2800000000000000000bcdf83ddc07d4000000000000000c87e6f000000002f7c840000329de0000000000000001f97e40000000000000000000000001f90000000000000007e40000000000001e40000000002f5bd5f8001f8bd400bd4007e0fc000fc0000000000000003f0fc7e0fc3f2f5bd400000000000000000000000000000000000000000000000000007e5f97e1f800000000000000000000000000006700000bd4fc00000000003f000bd6fa8c4027e6f8ca400405f8002f5000003f0d0fbcc8000670000000000bd4fc00000bea31009f9be000000fc002f5ca400405f8002f5000d0fbc003f0c8000000000019ef5000fc000003f00000000bd4027e6fa8c6f8003297e101bd400000fc003ef340c80000019c00002f5000fc00000009f9bea31be0fc00000002f5003297e101bd400003ef340fc000c8

def rkM (m : ℕ) : ℕ := (RT >>> (3 * m)) % 8
def INC (m : ℕ) : ℕ := (INCT >>> (10 * m)) % 1024
def FL (i : ℕ) : ℕ := (FLT >>> (10 * i)) % 1024
def CL (i a : ℕ) : ℕ := (CLT >>> (7 * (10 * i + a))) % 128
def IDX (m : ℕ) : ℕ := (IDXT >>> (7 * m)) % 128
def BAS (i : ℕ) : ℕ := (BAST >>> (10 * i)) % 1024
def CD (i : ℕ) : ℕ := (CDT >>> (4 * i)) % 16

/-! ### Kernel-checked facts about the tables -/

theorem gf2Rank_eq_rkM : ∀ m < 1024, gf2Rank m = rkM m := by decide +kernel

/-- `INC m` is the set of elements whose insertion raises the rank; increments are `0` or `1`. -/
theorem inc_spec : ∀ m < 1024, ∀ e < 10,
    (rkM (m ||| 2 ^ e) = rkM m + 1 ∧ (INC m).testBit e = true) ∨
    (rkM (m ||| 2 ^ e) = rkM m ∧ (INC m).testBit e = false) := by decide +kernel

theorem inc_anti : ∀ m < 1024, ∀ a < 10, INC (m ||| 2 ^ a) &&& INC m = INC (m ||| 2 ^ a) := by
  decide +kernel

theorem rk_small : rkM 0 = 0 ∧ (∀ a < 10, rkM (2 ^ a) = 1) ∧
    ∀ a < 10, ∀ b < 10, a ≠ b → rkM (2 ^ b ||| 2 ^ a) = 2 := by decide +kernel

theorem flat_tbl : ∀ i < 110, INC (FL i) ||| FL i = 1023 ∧ IDX (FL i) = i ∧
    (ofMask (FL i)).card = CD i ∧ BAS i &&& FL i = BAS i ∧
    (ofMask (BAS i)).card = rkM (FL i) ∧ rkM (BAS i) = rkM (FL i) := by decide +kernel

theorem surj_tbl : ∀ m < 1024, INC m ||| m = 1023 → IDX m < 110 ∧ FL (IDX m) = m := by
  decide +kernel

theorem cov_tbl : ∀ i < 110, ∀ a < 10, CL i a < 110 ∧ ((FL i).testBit a = false →
    rkM (FL (CL i a)) = rkM (FL i) + 1 ∧ FL i &&& FL (CL i a) = FL i ∧
    FL (CL i a) = 1023 ^^^ INC (FL i ||| 2 ^ a)) := by decide +kernel

theorem misc_tbl : FL 109 = 1023 ∧ IDX 1023 = 109 ∧ rkM 1023 = 5 ∧ ofMask 1023 = univ ∧
    (∀ e < 10, (1023 : ℕ).testBit e = true) ∧ (∀ c < 10, (10 - c) ∣ 2520) := by decide +kernel

lemma lt1024_or {m e : ℕ} (hm : m < 1024) (he : e < 10) : m ||| 2 ^ e < 1024 :=
  Nat.or_lt_two_pow (n := 10) hm (Nat.pow_lt_pow_right (by norm_num) he)

lemma testBit_ge10 {m j : ℕ} (hm : m < 1024) (hj : 10 ≤ j) : m.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hm
    (show (1024 : ℕ) ≤ 2 ^ j from (show (1024 : ℕ) = 2 ^ 10 by norm_num) ▸
      Nat.pow_le_pow_right (by norm_num) hj))

lemma FL_lt (i : ℕ) : FL i < 1024 := Nat.mod_lt _ (by norm_num)
lemma INC_lt (m : ℕ) : INC m < 1024 := Nat.mod_lt _ (by norm_num)
lemma BAS_lt (i : ℕ) : BAS i < 1024 := Nat.mod_lt _ (by norm_num)

/-! ### The matroid -/

/-- Rank of an edge set: `𝔽₂`-rank of its incidence vectors. -/
def rkG (S : Finset (Fin 10)) : ℕ := gf2Rank (mask S)

lemma rkG_eq (S : Finset (Fin 10)) : rkG S = rkM (mask S) := gf2Rank_eq_rkM _ (mask_lt S)

lemma rkG_insert (S : Finset (Fin 10)) (e : Fin 10) :
    rkG (insert e S) = rkM (mask S ||| 2 ^ (e : ℕ)) := by rw [rkG_eq, mask_insert]

lemma inc_cases (S : Finset (Fin 10)) (e : Fin 10) :
    (rkG (insert e S) = rkG S + 1 ∧ (INC (mask S)).testBit e = true) ∨
    (rkG (insert e S) = rkG S ∧ (INC (mask S)).testBit e = false) := by
  rw [rkG_insert, rkG_eq]; exact inc_spec _ (mask_lt S) _ e.2

lemma rk_local (m : ℕ) (hm : m < 1024) (a b : ℕ) (ha : a < 10) (hb : b < 10) :
    rkM (m ||| 2 ^ b ||| 2 ^ a) + rkM m ≤ rkM (m ||| 2 ^ a) + rkM (m ||| 2 ^ b) := by
  have hcomm : m ||| 2 ^ b ||| 2 ^ a = m ||| 2 ^ a ||| 2 ^ b := by
    rw [Nat.or_assoc, Nat.or_comm (2 ^ b), ← Nat.or_assoc]
  rw [hcomm]
  have hma := lt1024_or hm ha
  rcases inc_spec _ hma _ hb with h1 | h1 <;> rcases inc_spec _ hm _ hb with h2 | h2
  · omega
  · have h3 := congrArg (fun x => x.testBit b) (inc_anti _ hm _ ha)
    simp only [Nat.testBit_and, h1.2, h2.2] at h3
    simp at h3
  · omega
  · omega

/-- The cycle matroid of `G₄`, as the `𝔽₂`-linear matroid of its vertex–edge incidence
vectors. -/
def M_G4 : SimpleMatroid 10 where
  rk := rkG
  rk_empty := by rw [rkG_eq, mask_empty]; exact rk_small.1
  rk_le_card S := by
    induction S using Finset.induction_on with
    | empty => rw [rkG_eq, mask_empty, rk_small.1]; simp
    | insert e S he ih =>
      rw [Finset.card_insert_of_notMem he]
      rcases inc_cases S e with h | h <;> omega
  rk_mono := by
    intro S T hST
    exact mono_of_insert (f := rkG) (fun S e => by rcases inc_cases S e with h | h <;> omega) hST
  rk_submod := by
    apply submod_of_local
    intro S a b
    rw [rkG_insert, rkG_insert, rkG_insert, rkG_eq, mask_insert]
    exact rk_local _ (mask_lt S) _ _ a.2 b.2
  simple_singleton a := by
    rw [rkG_eq]; simp only [mask, Finset.sum_singleton]; exact rk_small.2.1 _ a.2
  simple_pair a b hab := by
    rw [rkG_eq, mask_insert]; simp only [mask, Finset.sum_singleton]
    exact rk_small.2.2 _ a.2 _ b.2 (fun h => hab (Fin.ext h))

lemma rk_eq (S : Finset (Fin 10)) : M_G4.rk S = rkM (mask S) := rkG_eq S

theorem M_G4_rank : M_G4.rank = 5 := by
  show rkG univ = 5
  rw [rkG_eq, ← misc_tbl.2.2.2.1, mask_ofMask (by norm_num)]; exact misc_tbl.2.2.1

/-- `M_G4` is the cycle matroid of `G₄`: its rank is the `𝔽₂`-rank of incidence vectors. -/
theorem M_G4_rk_eq_gf2Rank (S : Finset (Fin 10)) : M_G4.rk S = gf2Rank (mask S) := rfl

/-! ### Flats of `M_G4` -/

lemma rk_ofMask {m : ℕ} (hm : m < 1024) : M_G4.rk (ofMask m) = rkM m := by
  rw [rk_eq, mask_ofMask hm]

lemma rk_insert_ofMask {m : ℕ} (hm : m < 1024) (e : Fin 10) :
    M_G4.rk (insert e (ofMask m)) = rkM (m ||| 2 ^ (e : ℕ)) := by
  rw [rk_eq, mask_insert, mask_ofMask hm]

lemma cl_eq (S : Finset (Fin 10)) : cl M_G4 S = ofMask (1023 ^^^ INC (mask S)) := by
  ext e
  simp only [cl, Finset.mem_filter, Finset.mem_univ, true_and, mem_ofMask, Nat.testBit_xor,
    misc_tbl.2.2.2.2.1 _ e.2, Bool.true_xor, Bool.not_eq_true']
  show rkG (insert e S) = rkG S ↔ _
  rcases inc_cases S e with h | h <;> simp [h]

lemma isFlat_FL (i : Fin 110) : IsFlat M_G4 (ofMask (FL i)) := by
  intro e he
  rw [rk_insert_ofMask (FL_lt _), rk_ofMask (FL_lt _)] at he
  rw [mem_ofMask]
  have h1 := (flat_tbl i i.2).1
  have h2 := congrArg (fun x => x.testBit e) h1
  simp only [Nat.testBit_or, misc_tbl.2.2.2.2.1 _ e.2] at h2
  rcases inc_spec _ (FL_lt i) _ e.2 with h | h
  · omega
  · rw [h.2] at h2; simpa using h2

def flatG (i : Fin 110) : Flat M_G4 := ⟨ofMask (FL i), isFlat_FL i⟩

lemma flatG_injective : Function.Injective flatG := by
  intro i j h
  have h1 : FL i = FL j := ofMask_inj (FL_lt _) (FL_lt _) (congrArg Subtype.val h)
  apply Fin.ext
  rw [← (flat_tbl i i.2).2.1, ← (flat_tbl j j.2).2.1, h1]

lemma flatG_surjective : Function.Surjective flatG := by
  intro F
  set m := mask F.1
  have hm : m < 1024 := mask_lt _
  have hflat : INC m ||| m = 1023 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 10
    · rw [misc_tbl.2.2.2.2.1 _ hj, Nat.testBit_or]
      rcases inc_spec _ hm _ hj with h | h
      · rw [h.2]; rfl
      · have := F.2 ⟨j, hj⟩ (by rw [rk_eq, rk_eq, mask_insert]; exact h.1)
        rw [mem_iff_testBit] at this
        rw [this]; simp
    · rw [Nat.testBit_or, testBit_ge10 (INC_lt m) (by omega), testBit_ge10 hm (by omega),
        testBit_ge10 (by norm_num : (1023 : ℕ) < 1024) (by omega)]; rfl
  obtain ⟨hi, hFL⟩ := surj_tbl m hm hflat
  refine ⟨⟨IDX m, hi⟩, Subtype.ext ?_⟩
  show ofMask (FL (IDX m)) = F.1
  rw [hFL, ofMask_mask]

noncomputable def flatEquiv : Fin 110 ≃ Flat M_G4 :=
  Equiv.ofBijective flatG ⟨flatG_injective, flatG_surjective⟩

lemma flatEquiv_apply (i : Fin 110) : flatEquiv i = flatG i := rfl

/-- Index of `cl(X_i ∪ a)`. -/
def cli (i : Fin 110) (a : Fin 10) : Fin 110 := ⟨CL i a, (cov_tbl i i.2 a a.2).1⟩

lemma covers_iff (i j : Fin 110) (a : Fin 10) :
    Covers M_G4 (flatG i).1 (flatG j).1 a ↔ (FL i).testBit a = false ∧ j = cli i a := by
  have hcl : cl M_G4 (insert a (ofMask (FL i))) = ofMask (1023 ^^^ INC (FL i ||| 2 ^ (a : ℕ))) := by
    rw [cl_eq, mask_insert, mask_ofMask (FL_lt _)]
  show Covers M_G4 (ofMask (FL i)) (ofMask (FL j)) a ↔ _
  constructor
  · rintro ⟨-, -, ha, hc⟩
    rw [mem_ofMask, Bool.not_eq_true] at ha
    refine ⟨ha, ?_⟩
    obtain ⟨-, -, h3⟩ := (cov_tbl i i.2 a a.2).2 ha
    rw [hcl, ← h3] at hc
    have h4 := ofMask_inj (FL_lt _) (FL_lt _) hc
    apply Fin.ext
    show (j : ℕ) = CL i a
    rw [← (flat_tbl j j.2).2.1, ← h4, (flat_tbl _ (cov_tbl i i.2 a a.2).1).2.1]
  · rintro ⟨ha, rfl⟩
    obtain ⟨h1, h2, h3⟩ := (cov_tbl i i.2 a a.2).2 ha
    refine ⟨?_, ?_, ?_, ?_⟩
    · show M_G4.rk (ofMask (FL (CL i a))) = M_G4.rk (ofMask (FL i)) + 1
      rw [rk_ofMask (FL_lt _), rk_ofMask (FL_lt _), h1]
    · intro e he
      show e ∈ ofMask (FL (CL i a))
      rw [mem_ofMask] at he ⊢
      have := congrArg (fun x => x.testBit e) h2
      simp only [Nat.testBit_and, he, Bool.true_and] at this
      exact this
    · rw [mem_ofMask, ha]; simp
    · rw [hcl]; show _ = ofMask (FL (CL i a)); rw [h3]

/-! ### `β` is positive on flats -/

def betaG (i : Fin 110) : ℕ := beta M_G4 (ofMask (FL i))

lemma betaG_pos (i : Fin 110) : 0 < betaG i := by
  obtain ⟨-, -, -, h1, h2, h3⟩ := flat_tbl i i.2
  unfold betaG beta
  rw [rk_ofMask (FL_lt _)]
  refine Nat.mul_pos (Nat.factorial_pos _) (Finset.card_pos.2 ⟨ofMask (BAS i), ?_⟩)
  rw [Finset.mem_filter, Finset.mem_powersetCard, rk_ofMask (BAS_lt _)]
  refine ⟨⟨?_, h2⟩, h3⟩
  intro e he
  rw [mem_ofMask] at he ⊢
  have := congrArg (fun x => x.testBit e) h1
  simp only [Nat.testBit_and, he, Bool.true_and] at this
  exact this

lemma betaG_ne (i : Fin 110) : (betaG i : ℚ) ≠ 0 := by
  exact_mod_cast (betaG_pos i).ne'

/-! ### Rescaled coordinates -/

/-- `f ↦ (i ↦ f(X_i) / β_{X_i})`. -/
noncomputable def ψ : (Flat M_G4 → ℚ) ≃ₗ[ℚ] (Fin 110 → ℚ) where
  toFun f i := f (flatG i) / (betaG i : ℚ)
  invFun g X := g (flatEquiv.symm X) * (betaG (flatEquiv.symm X) : ℚ)
  map_add' f g := by ext i; simp [add_div]
  map_smul' c f := by ext i; simp [mul_div_assoc]
  left_inv f := by
    funext X
    have h : flatG (flatEquiv.symm X) = X := flatEquiv.apply_symm_apply X
    simp only [h]
    exact div_mul_cancel₀ _ (betaG_ne _)
  right_inv g := by
    funext i
    have h : flatEquiv.symm (flatG i) = i := flatEquiv.symm_apply_apply i
    simp only [h]
    exact mul_div_cancel_right₀ _ (betaG_ne _)

lemma ψ_apply (f : Flat M_G4 → ℚ) (i : Fin 110) : ψ f i = f (flatG i) / (betaG i : ℚ) := rfl

def Lq (a : Fin 10) : (Fin 110 → ℚ) →ₗ[ℚ] (Fin 110 → ℚ) where
  toFun g i := if (FL i).testBit a then 0 else g (cli i a)
  map_add' f g := by ext i; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

def Kq : (Fin 110 → ℚ) →ₗ[ℚ] (Fin 110 → ℚ) where
  toFun g i := (rkM (FL i) : ℚ) * g i
  map_add' f g := by ext; simp [mul_add]
  map_smul' c f := by ext; simp; ring

def Sq : (Fin 110 → ℚ) →ₗ[ℚ] (Fin 110 → ℚ) where
  toFun g i := if CD i < 10 then (1 / ((10 - CD i : ℕ) : ℚ)) * g i else 0
  map_add' f g := by ext; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c f := by
    ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

def Uq : (Fin 110 → ℚ) →ₗ[ℚ] (Fin 110 → ℚ) := ∑ a : Fin 10, Lq a

def Dq : (Fin 110 → ℚ) →ₗ[ℚ] (Fin 110 → ℚ) := Sq.comp (Uq.comp Kq)

lemma ψ_L (a : Fin 10) (f : Flat M_G4 → ℚ) : ψ (L_beta M_G4 a f) = Lq a (ψ f) := by
  classical
  funext i
  rw [ψ_apply]
  simp only [L_beta, LinearMap.coe_mk, AddHom.coe_mk, Lq]
  rw [← flatEquiv.sum_comp]
  simp only [flatEquiv_apply, covers_iff]
  by_cases hb : (FL i).testBit a = true
  · simp [hb]
  · rw [Bool.not_eq_true] at hb
    simp only [hb, true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true, ψ_apply]
    simp only [Bool.false_eq_true, if_false]
    have h1 := betaG_ne i
    have h2 := betaG_ne (cli i a)
    unfold betaG at h1 h2
    show (beta M_G4 (ofMask (FL i)) : ℚ) / (beta M_G4 (ofMask (FL (cli i a))) : ℚ) *
        f (flatG (cli i a)) / (beta M_G4 (ofMask (FL i)) : ℚ) =
      f (flatG (cli i a)) / (beta M_G4 (ofMask (FL (cli i a))) : ℚ)
    field_simp

lemma ψ_K (f : Flat M_G4 → ℚ) : ψ (K_op M_G4 f) = Kq (ψ f) := by
  funext i
  simp only [ψ_apply, K_op, Kq, LinearMap.coe_mk, AddHom.coe_mk]
  show (M_G4.rk (ofMask (FL i)) : ℚ) * _ / _ = _
  rw [rk_ofMask (FL_lt _), mul_div_assoc]

lemma ψ_S (f : Flat M_G4 → ℚ) : ψ (S_inv M_G4 f) = Sq (ψ f) := by
  funext i
  simp only [ψ_apply, S_inv, Sq, LinearMap.coe_mk, AddHom.coe_mk]
  have hc : (flatG i).1.card = CD i := (flat_tbl i i.2).2.2.1
  simp only [hc]
  split_ifs <;> ring

lemma ψ_U (f : Flat M_G4 → ℚ) : ψ (U_beta M_G4 f) = Uq (ψ f) := by
  simp only [U_beta, Uq, LinearMap.sum_apply, map_sum, ψ_L]

lemma ψ_D (f : Flat M_G4 → ℚ) : ψ (D_beta M_G4 f) = Dq (ψ f) := by
  simp only [D_beta, Dq, LinearMap.comp_apply, ψ_S, ψ_U, ψ_K]

/-! ### Natural-number vectors and words -/

def castv (g : ℕ → ℕ) : Fin 110 → ℚ := fun i => (g i : ℚ)

def eZ (i : ℕ) : ℕ := if i = 109 then 1 else 0
def LZ (a : ℕ) (g : ℕ → ℕ) (i : ℕ) : ℕ := if (FL i).testBit a then 0 else g (CL i a)
def KZ (g : ℕ → ℕ) (i : ℕ) : ℕ := rkM (FL i) * g i
/-- `2520 · D` in rescaled coordinates. -/
def DZ (g : ℕ → ℕ) (i : ℕ) : ℕ :=
  if CD i < 10 then (2520 / (10 - CD i)) * ∑ a : Fin 10, LZ a (KZ g) i else 0
/-- Operator code: `o < 10` is `L_o`, otherwise `D`. -/
def opZ (o : ℕ) (g : ℕ → ℕ) : ℕ → ℕ := if o < 10 then LZ o g else DZ g
def evZ : List ℕ → ℕ → ℕ
  | [] => eZ
  | o :: w => opZ o (evZ w)

lemma ψ_vtop : ψ (v_top M_G4) = castv eZ := by
  funext i
  rw [ψ_apply]
  simp only [v_top, castv, eZ]
  show (if ofMask (FL i) = univ then _ else _) / _ = _
  by_cases hi : (i : ℕ) = 109
  · have h109 : ofMask (FL i) = univ := by rw [hi, misc_tbl.1]; exact misc_tbl.2.2.2.1
    rw [if_pos h109, if_pos hi]
    have h := betaG_ne i
    unfold betaG at h ⊢
    rw [h109] at h ⊢
    simp [div_self h]
  · rw [if_neg hi]
    have : ofMask (FL i) ≠ univ := by
      intro h
      rw [← misc_tbl.2.2.2.1] at h
      have h1 := ofMask_inj (FL_lt _) (by norm_num) h
      apply hi
      rw [← (flat_tbl i i.2).2.1, h1, misc_tbl.2.1]
    rw [if_neg this]; simp

lemma Lq_castv (a : Fin 10) (g : ℕ → ℕ) : Lq a (castv g) = castv (LZ a g) := by
  funext i
  simp only [Lq, LinearMap.coe_mk, AddHom.coe_mk, castv, LZ, cli]
  split_ifs <;> simp

lemma Kq_castv (g : ℕ → ℕ) : Kq (castv g) = castv (KZ g) := by
  funext i; simp [Kq, castv, KZ]

lemma Uq_castv (g : ℕ → ℕ) : Uq (castv g) = castv (fun i => ∑ a : Fin 10, LZ a g i) := by
  funext i
  simp only [Uq, LinearMap.sum_apply, Finset.sum_apply, Lq_castv, castv]
  push_cast; rfl

lemma Dq_castv (g : ℕ → ℕ) : Dq (castv g) = (1 / 2520 : ℚ) • castv (DZ g) := by
  funext i
  simp only [Dq, LinearMap.comp_apply, Kq_castv, Uq_castv]
  simp only [Sq, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, castv, DZ]
  split_ifs with h
  · have hd := misc_tbl.2.2.2.2.2 _ h
    have hne : ((10 - CD i : ℕ) : ℚ) ≠ 0 := by
      have : 0 < 10 - CD i := by omega
      exact_mod_cast this.ne'
    push_cast
    rw [Nat.cast_div hd hne]
    field_simp
    norm_num
  · simp

def opQ (o : ℕ) : (Fin 110 → ℚ) →ₗ[ℚ] (Fin 110 → ℚ) := if h : o < 10 then Lq ⟨o, h⟩ else Dq

def scl : List ℕ → ℚ
  | [] => 1
  | o :: w => (if o < 10 then 1 else 1 / 2520) * scl w

def evQ : List ℕ → Fin 110 → ℚ
  | [] => castv eZ
  | o :: w => opQ o (evQ w)

lemma opQ_castv (o : ℕ) (g : ℕ → ℕ) :
    opQ o (castv g) = (if o < 10 then 1 else 1 / 2520 : ℚ) • castv (opZ o g) := by
  unfold opQ opZ
  by_cases h : o < 10
  · simp only [dif_pos h, if_pos h, one_smul]; exact Lq_castv ⟨o, h⟩ g
  · simp only [dif_neg h, if_neg h]; exact Dq_castv g

lemma evQ_eq (w : List ℕ) : evQ w = scl w • castv (evZ w) := by
  induction w with
  | nil => simp [evQ, scl, evZ]
  | cons o w ih =>
    simp only [evQ, scl, evZ, ih, map_smul, opQ_castv, smul_smul, mul_comm]

lemma scl_ne (w : List ℕ) : scl w ≠ 0 := by
  induction w with
  | nil => simp [scl]
  | cons o w ih => simp only [scl]; split_ifs <;> simp [ih]

/-! ### The cyclic module in rescaled coordinates -/

noncomputable def C' (k : ℕ) : Submodule ℚ (Fin 110 → ℚ) :=
  (C_mod M_G4 k).map (ψ : (Flat M_G4 → ℚ) →ₗ[ℚ] (Fin 110 → ℚ))

lemma h_beta_eq (k : ℕ) : h_beta M_G4 k = Module.finrank ℚ (C' k) :=
  (LinearEquiv.finrank_map_eq ψ _).symm

lemma C'_zero : C' 0 = Submodule.span ℚ {castv eZ} := by
  simp only [C', C_mod, Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, ψ_vtop]

lemma C'_succ (k : ℕ) : C' (k + 1) = (C' k).map Dq ⊔ ⨆ a : Fin 10, (C' k).map (Lq a) := by
  have hD : (ψ : (Flat M_G4 → ℚ) →ₗ[ℚ] (Fin 110 → ℚ)).comp (D_beta M_G4) =
      Dq.comp (ψ : (Flat M_G4 → ℚ) →ₗ[ℚ] (Fin 110 → ℚ)) := LinearMap.ext ψ_D
  have hL : ∀ a, (ψ : (Flat M_G4 → ℚ) →ₗ[ℚ] (Fin 110 → ℚ)).comp (L_beta M_G4 a) =
      (Lq a).comp (ψ : (Flat M_G4 → ℚ) →ₗ[ℚ] (Fin 110 → ℚ)) := fun a => LinearMap.ext (ψ_L a)
  simp only [C', C_mod, Submodule.map_sup, Submodule.map_iSup, ← Submodule.map_comp, hD, hL]

lemma evQ_mem (w : List ℕ) : evQ w ∈ C' w.length := by
  induction w with
  | nil => show evQ [] ∈ C' 0; rw [C'_zero]; exact Submodule.subset_span rfl
  | cons o w ih =>
    rw [List.length_cons, C'_succ]
    simp only [evQ, opQ]
    split_ifs with h
    · exact Submodule.mem_sup_right
        (Submodule.mem_iSup_of_mem (⟨o, h⟩ : Fin 10) (Submodule.mem_map_of_mem ih))
    · exact Submodule.mem_sup_left (Submodule.mem_map_of_mem ih)

lemma castv_mem (w : List ℕ) : castv (evZ w) ∈ C' w.length := by
  have h := Submodule.smul_mem _ (scl w)⁻¹ (evQ_mem w)
  rwa [evQ_eq, inv_smul_smul₀ (scl_ne w)] at h

/-- Words of length `k` over the 11 operator codes. -/
def allWords : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (List.range 11).flatMap fun o => (allWords k).map (o :: ·)

lemma mem_allWords : ∀ (w : List ℕ), (∀ o ∈ w, o ≤ 10) → w ∈ allWords w.length
  | [], _ => by simp [allWords]
  | o :: w, h => by
    simp only [allWords, List.length_cons, List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨o, by have := h o (by simp); omega, w,
      mem_allWords w (fun x hx => h x (by simp [hx])), rfl⟩

lemma length_of_mem_allWords : ∀ {k : ℕ} {w : List ℕ}, w ∈ allWords k → w.length = k
  | 0, w, hw => by simp [allWords] at hw; simp [hw]
  | k + 1, w, hw => by
    simp only [allWords, List.mem_flatMap, List.mem_map] at hw
    obtain ⟨o, -, w', hw', rfl⟩ := hw
    simp [length_of_mem_allWords hw']

def wordSet (k : ℕ) : Set (Fin 110 → ℚ) := {x | ∃ w ∈ allWords k, x = castv (evZ w)}

lemma C'_le (k : ℕ) : C' k ≤ Submodule.span ℚ (wordSet k) := by
  induction k with
  | zero =>
    rw [C'_zero]
    exact Submodule.span_mono (by
      rintro x rfl; exact ⟨[], by simp [allWords], rfl⟩)
  | succ k ih =>
    rw [C'_succ]
    refine sup_le ?_ (iSup_le fun a => ?_)
    · refine (Submodule.map_mono ih).trans ((Submodule.map_span_le _ _ _).2 ?_)
      rintro x ⟨w, hw, rfl⟩
      rw [Dq_castv]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨10 :: w, ?_, ?_⟩)
      · simp only [allWords, List.mem_flatMap, List.mem_range, List.mem_map]
        exact ⟨10, by norm_num, w, hw, rfl⟩
      · simp [evZ, opZ]
    · refine (Submodule.map_mono ih).trans ((Submodule.map_span_le _ _ _).2 ?_)
      rintro x ⟨w, hw, rfl⟩
      rw [Lq_castv]
      refine Submodule.subset_span ⟨a.val :: w, ?_, ?_⟩
      · simp only [allWords, List.mem_flatMap, List.mem_range, List.mem_map]
        exact ⟨a.val, by omega, w, hw, rfl⟩
      · simp [evZ, opZ, a.2]

/-! ### Support: words of length `k` live on rank-`(5 - k)` flats -/

def SuppZ (ρ : ℕ) (g : ℕ → ℕ) : Prop := ∀ i < 110, rkM (FL i) ≠ ρ → g i = 0

lemma LZ_supp {ρ : ℕ} {g : ℕ → ℕ} (hg : SuppZ (ρ + 1) g) {a : ℕ} (ha : a < 10) :
    SuppZ ρ (LZ a g) := by
  intro i hi hr
  unfold LZ
  split_ifs with hb
  · rfl
  · rw [Bool.not_eq_true] at hb
    obtain ⟨h0, h1⟩ := cov_tbl i hi a ha
    exact hg _ h0 (by rw [(h1 hb).1]; omega)

lemma opZ_supp {ρ : ℕ} {g : ℕ → ℕ} (hg : SuppZ (ρ + 1) g) (o : ℕ) : SuppZ ρ (opZ o g) := by
  unfold opZ
  split_ifs with ho
  · exact LZ_supp hg ho
  · intro i hi hr
    have hK : SuppZ (ρ + 1) (KZ g) := fun j hj hr' => by simp [KZ, hg j hj hr']
    unfold DZ
    split_ifs
    · rw [Finset.sum_eq_zero fun a _ => LZ_supp hK a.2 i hi hr, mul_zero]
    · rfl

lemma evZ_supp : ∀ w : List ℕ, w.length ≤ 5 → SuppZ (5 - w.length) (evZ w)
  | [], _ => by
    intro i hi hr
    simp only [evZ, eZ]
    split_ifs with h
    · subst h; exact absurd misc_tbl.2.2.1 (by rw [misc_tbl.1] at hr; simpa using hr)
    · rfl
  | o :: w, h => by
    simp only [List.length_cons] at h ⊢
    have := evZ_supp w (by omega)
    rw [show 5 - w.length = (5 - (w.length + 1)) + 1 by omega] at this
    exact opZ_supp this o

/-! ### Upper bounds from relations -/

def xN (x : Fin 110 → ℚ) (i : ℕ) : ℚ := if h : i < 110 then x ⟨i, h⟩ else 0

def relQ (off : ℕ) (rel : List (ℕ × ℤ)) (x : Fin 110 → ℚ) : ℚ :=
  (rel.map fun p => (p.2 : ℚ) * xN x (off + p.1)).sum

def relZ (off : ℕ) (rel : List (ℕ × ℤ)) (g : ℕ → ℕ) : ℤ :=
  (rel.map fun p => p.2 * (g (off + p.1) : ℤ)).sum

lemma relQ_add (off : ℕ) (rel : List (ℕ × ℤ)) (x y : Fin 110 → ℚ) :
    relQ off rel (x + y) = relQ off rel x + relQ off rel y := by
  induction rel with
  | nil => simp [relQ]
  | cons p rel ih =>
    simp only [relQ, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; simp only [xN]; split_ifs <;> simp
    ring

lemma relQ_smul (off : ℕ) (rel : List (ℕ × ℤ)) (c : ℚ) (x : Fin 110 → ℚ) :
    relQ off rel (c • x) = c * relQ off rel x := by
  induction rel with
  | nil => simp [relQ]
  | cons p rel ih =>
    simp only [relQ, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; simp only [xN]; split_ifs <;> simp
    ring

lemma relQ_castv (off : ℕ) (rel : List (ℕ × ℤ)) (g : ℕ → ℕ)
    (h : ∀ p ∈ rel, off + p.1 < 110) : relQ off rel (castv g) = (relZ off rel g : ℚ) := by
  induction rel with
  | nil => simp [relQ, relZ]
  | cons p rel ih =>
    simp only [relQ, relZ, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih (fun q hq => h q (by simp [hq]))]
    simp only [xN, dif_pos (h p (by simp)), castv]
    push_cast; ring

def Pq (ρ off : ℕ) (REL : List (List (ℕ × ℤ))) : Submodule ℚ (Fin 110 → ℚ) where
  carrier := {x | (∀ i : Fin 110, rkM (FL i) ≠ ρ → x i = 0) ∧ ∀ rel ∈ REL, relQ off rel x = 0}
  add_mem' {x y} hx hy :=
    ⟨fun i hi => by simp [hx.1 i hi, hy.1 i hi],
     fun rel hr => by rw [relQ_add, hx.2 rel hr, hy.2 rel hr, add_zero]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun rel _ => by
    simpa using relQ_smul off rel 0 0⟩
  smul_mem' c x hx :=
    ⟨fun i hi => by simp [hx.1 i hi], fun rel hr => by rw [relQ_smul, hx.2 rel hr, mul_zero]⟩

/-- Pivot structure: the head coefficient is nonzero and the tail lies in the free columns. -/
def pivOK (AF : List ℕ) : List (ℕ × ℤ) → Bool
  | [] => false
  | p :: t => p.2 != 0 && t.all fun q => AF.contains q.1

theorem upper_bound (k ρ off W : ℕ) (REL : List (List (ℕ × ℤ))) (AF : List ℕ)
    (hk : k ≤ 5) (hρ : ρ = 5 - k)
    (hlay : ∀ i < 110, rkM (FL i) = ρ → off ≤ i ∧ i < off + W)
    (hcov : ∀ j < W, AF.contains j = true ∨
      ∃ rel ∈ REL, (rel.head?.map Prod.fst) = some j)
    (hpiv : REL.all (pivOK AF) = true)
    (hbd : ∀ rel ∈ REL, ∀ p ∈ rel, off + p.1 < 110)
    (hrel : (allWords k).all (fun w => REL.all fun rel => relZ off rel (evZ w) == 0) = true) :
    Module.finrank ℚ (C' k) ≤ AF.length := by
  have hle : C' k ≤ Pq ρ off REL := by
    refine (C'_le k).trans (Submodule.span_le.2 ?_)
    rintro x ⟨w, hw, rfl⟩
    have hwl : w.length = k := length_of_mem_allWords hw
    refine ⟨fun i hi => ?_, fun rel hr => ?_⟩
    · show ((evZ w i : ℕ) : ℚ) = 0
      rw [evZ_supp w (by omega) i i.2 (by rw [hwl, ← hρ]; exact hi)]; simp
    · rw [relQ_castv off rel _ (hbd rel hr)]
      have := List.all_eq_true.1 hrel w hw
      have := List.all_eq_true.1 this rel hr
      rw [beq_iff_eq] at this
      rw [this]; simp
  let π : (Fin 110 → ℚ) →ₗ[ℚ] (Fin AF.length → ℚ) :=
    { toFun := fun x t => xN x (off + AF[t])
      map_add' := fun x y => by ext t; simp only [xN, Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by
        ext t; simp only [xN, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp }
  have hinj : Function.Injective (π.comp (C' k).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ h0
    have hP := hle hx
    have hfree : ∀ j ∈ AF, xN x (off + j) = 0 := by
      intro j hj
      obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hj
      exact congrFun h0 ⟨t, ht⟩
    have hpivz : ∀ rel ∈ REL, ∀ j c, rel.head? = some (j, c) → xN x (off + j) = 0 := by
      intro rel hr j c hh
      have hok := List.all_eq_true.1 hpiv rel hr
      cases rel with
      | nil => simp at hh
      | cons p t =>
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst hh
        simp only [pivOK, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
          List.contains_iff_mem] at hok
        have hz := hP.2 _ hr
        simp only [relQ, List.map_cons, List.sum_cons] at hz
        rw [List.sum_eq_zero (fun y hy => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
          rw [hfree _ (hok.2 q hq), mul_zero]), add_zero] at hz
        rcases mul_eq_zero.1 hz with h | h
        · exact absurd (by exact_mod_cast h) hok.1
        · exact h
    apply Subtype.ext
    funext i
    show x i = 0
    by_cases hr : rkM (FL i) = ρ
    · obtain ⟨h1, h2⟩ := hlay i i.2 hr
      have hxi : x i = xN x (off + (i - off)) := by
        simp only [xN, show off + (i - off) = i by omega, dif_pos i.2]
      rw [hxi]
      rcases hcov (i - off) (by omega) with h | ⟨rel, hrel', hh⟩
      · exact hfree _ (List.contains_iff_mem.1 h)
      · obtain ⟨⟨j, c⟩, hh', hj⟩ := Option.map_eq_some_iff.1 hh
        simp only at hj
        rw [← hj]
        exact hpivz rel hrel' j c hh'
    · exact hP.1 i hr
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

/-! ### Lower bounds from words invertible mod 1009 -/

def P : ℕ := 1009

instance : Fact (1 < P) := ⟨by norm_num [P]⟩

def ent (T N t m : ℕ) : ℕ := (T >>> (10 * (N * t + m))) % 1024

theorem lower_bound (k N : ℕ) (WD : List (List ℕ)) (SEL : List ℕ) (WT NT : ℕ)
    (hlen : WD.length = N ∧ SEL.length = N ∧ WD.all (fun w => w.length == k) = true ∧
      SEL.all (· < 110) = true)
    (hW : ∀ t < N, ∀ m < N, evZ (WD.getD t []) (SEL.getD m 0) % P = ent WT N t m)
    (hinv : ∀ t < N, ∀ l < N,
      (∑ m ∈ range N, ent WT N t m * ent NT N m l) % P = if t = l then 1 else 0) :
    N ≤ Module.finrank ℚ (C' k) := by
  obtain ⟨hWD, hSEL, hk, hs⟩ := hlen
  have hselF : ∀ m : Fin N, SEL.getD m 0 < 110 := fun m => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact of_decide_eq_true (List.all_eq_true.1 hs _ (List.getElem_mem _))
  have hwk : ∀ t : Fin N, (WD.getD t []).length = k := fun t => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact beq_iff_eq.1 (List.all_eq_true.1 hk _ (List.getElem_mem _))
  let u : Fin N → Fin 110 → ℚ := fun t => castv (evZ (WD.getD t []))
  let sel : Fin N → Fin 110 := fun m => ⟨SEL.getD m 0, hselF m⟩
  let Wz : Matrix (Fin N) (Fin N) ℤ :=
    Matrix.of fun t m => (evZ (WD.getD t []) (SEL.getD m 0) : ℤ)
  -- `Wz` is invertible mod `P`
  have hmodP : (Wz.map (Int.cast : ℤ → ZMod P)) *
      Matrix.of (fun m l : Fin N => (ent NT N m l : ZMod P)) = 1 := by
    ext t l
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    have h1 : ∀ m : Fin N, (Wz.map (Int.cast : ℤ → ZMod P)) t m = (ent WT N t m : ZMod P) := by
      intro m
      simp only [Matrix.map_apply, Wz, Matrix.of_apply, Int.cast_natCast]
      rw [← hW t t.2 m m.2, ZMod.natCast_mod]
    simp only [h1]
    have h2 := hinv t t.2 l l.2
    have h3 : (∑ m : Fin N, (ent WT N t m : ZMod P) * (ent NT N m l : ZMod P)) =
        ((∑ m ∈ range N, ent WT N t m * ent NT N m l : ℕ) : ZMod P) := by
      push_cast
      exact (Finset.sum_range (fun m => (ent WT N t m : ZMod P) * (ent NT N m l : ZMod P))).symm
    rw [h3, ← ZMod.natCast_mod, h2]
    by_cases htl : t = l
    · subst htl; simp
    · rw [if_neg (fun h => htl (Fin.ext h)), if_neg htl]; simp
  have hdetP : ((Wz.det : ℤ) : ZMod P) ≠ 0 := by
    have := congrArg Matrix.det hmodP
    rw [Matrix.det_mul, Matrix.det_one] at this
    have hm : (Int.castRingHom (ZMod P)).mapMatrix Wz = Wz.map (Int.cast : ℤ → ZMod P) := rfl
    rw [← hm, ← RingHom.map_det] at this
    intro h0
    rw [eq_intCast, h0, zero_mul] at this
    exact zero_ne_one this
  have hdetQ : (Wz.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    have hm : (Int.castRingHom ℚ).mapMatrix Wz = Wz.map (Int.cast : ℤ → ℚ) := rfl
    rw [← hm, ← RingHom.map_det, eq_intCast, Int.cast_ne_zero]
    intro h0; apply hdetP; rw [h0, Int.cast_zero]
  have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hdetQ
  have hu : LinearIndependent ℚ u := by
    have hcomp : (LinearMap.funLeft ℚ ℚ sel) ∘ u = fun t => (Wz.map (Int.cast : ℤ → ℚ)) t := by
      funext t m
      simp [u, sel, Wz, castv, LinearMap.funLeft_apply, Matrix.map_apply, Matrix.of_apply]
    have h' : LinearIndependent ℚ ((LinearMap.funLeft ℚ ℚ sel) ∘ u) := by rw [hcomp]; exact hrows
    exact LinearIndependent.of_comp _ h'
  have hspan : Submodule.span ℚ (Set.range u) ≤ C' k := by
    rw [Submodule.span_le]
    rintro x ⟨t, rfl⟩
    have := castv_mem (WD.getD t [])
    rwa [hwk t] at this
  have := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hu, Fintype.card_fin] at this
  exact this

/-! ### The four Hilbert-function values and the disproof -/

theorem M_G4_h2_le : h_beta M_G4 2 ≤ 31 := by
  rw [h_beta_eq]
  have := upper_bound 2 3 44 44 REL2 AF2 (by norm_num) rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa [AF2] using this

theorem M_G4_h3_le : h_beta M_G4 3 ≤ 32 := by
  rw [h_beta_eq]
  have := upper_bound 3 2 11 33 REL3 AF3 (by norm_num) rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa [AF3] using this

theorem M_G4_h2_ge : 31 ≤ h_beta M_G4 2 := by
  rw [h_beta_eq]
  exact lower_bound 2 31 WD2 SEL2 WT2 NT2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem M_G4_h3_ge : 32 ≤ h_beta M_G4 3 := by
  rw [h_beta_eq]
  exact lower_bound 3 32 WD3 SEL3 WT3 NT3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem M_G4_h2 : h_beta M_G4 2 = 31 := le_antisymm M_G4_h2_le M_G4_h2_ge

theorem M_G4_h3 : h_beta M_G4 3 = 32 := le_antisymm M_G4_h3_le M_G4_h3_ge

/-- Conjecture C (`h_k ≥ h_{r-k}` for `k ≤ r/2`) is false. -/
theorem not_sinclair_conjecture_C :
    ¬ (∀ (n : ℕ) (M : SimpleMatroid n) (k : ℕ), 2 * k ≤ M.rank →
      h_beta M (M.rank - k) ≤ h_beta M k) := by
  intro h
  have := h 10 M_G4 2 (by rw [M_G4_rank]; norm_num)
  rw [M_G4_rank] at this
  have h3 := M_G4_h3_ge
  have h2 := M_G4_h2_le
  norm_num at this
  omega

end SinclairRadialMobius

#print axioms SinclairRadialMobius.M_G4_rank
#print axioms SinclairRadialMobius.M_G4_h2_le
#print axioms SinclairRadialMobius.M_G4_h3_ge
#print axioms SinclairRadialMobius.M_G4_h2
#print axioms SinclairRadialMobius.M_G4_h3
#print axioms SinclairRadialMobius.not_sinclair_conjecture_C
