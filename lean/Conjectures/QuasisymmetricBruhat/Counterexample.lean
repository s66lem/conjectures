import Conjectures.QuasisymmetricBruhat.Raise
import Conjectures.QuasisymmetricBruhat.Shellability
import Mathlib.Tactic.IntervalCases

/-!
# Conjecture C / 6.11 of arXiv:2611.02210 is false

For the zigzag forest `Z = F(1, 2, 4)` and `x = F(0, 1, 0, 1, 1, 0, 1)`, the open interval
`(x, Z)` consists of six forests of rank 5 and six of rank 6 joined by twelve covers forming two
disjoint hexagons.  A shelling of `[∅, Z]` would restrict (Fact 6.1) to a shelling of `[x, Z]`,
whose order complex is a disconnected graph; so `[∅, Z]` is not shellable.  The zigzag forests
`Z_m = F(m - 6, 2, 4)` lie above `Z` by covers `x₁ P_{Z_m} = P_{Z_{m+1}}`, so Fact 6.1 rules out
shellability of `[∅, Z_m]` for every `m ≥ 7`.

Completeness of `(x, Z)`: every lower cover `z ⋖ Z` has its index `k ≤ |code Z| + |Z| = 10`
and lies in the candidate list `lowL Z k`; likewise below each such `z`.  The resulting finite
search, with exact coefficients `coefL`, is checked by `decide +kernel`.
-/

namespace QuasisymmetricBruhat

open Forest

/-- The forest with a given code (trailing zeros allowed). -/
def mkF (l : List ℕ) : Forest := ⟨trim l, noTrail_trim l⟩

/-- `F(a, 2, 4)`. -/
def zig (a : ℕ) : Forest := ⟨[a, 2, 4], by simp [NoTrail]⟩

/-- The zigzag counterexample `Z = F(1, 2, 4)`. -/
def Zc : Forest := zig 1

/-- The bottom `x = F(0, 1, 0, 1, 1, 0, 1)` of the bad interval. -/
def xc : Forest := mkF [0, 1, 0, 1, 1, 0, 1]

/-- The rank-5 elements of `(x, Z)`. -/
def ys : List Forest :=
  [mkF [0, 1, 0, 2, 2], mkF [0, 1, 1, 2, 0, 0, 1], mkF [0, 1, 2, 0, 1, 0, 1],
   mkF [0, 1, 0, 1, 3], mkF [0, 2, 0, 2, 0, 0, 1], mkF [0, 2, 1, 0, 1, 0, 1]]

/-- The rank-6 elements of `(x, Z)`. -/
def zs : List Forest :=
  [mkF [0, 1, 2, 3], mkF [0, 1, 3, 0, 2], mkF [1, 1, 3, 0, 0, 0, 1],
   mkF [0, 2, 0, 4], mkF [0, 2, 1, 0, 3], mkF [0, 2, 3, 0, 0, 0, 1]]

/-- The first hexagon. -/
def hexA : List Forest :=
  [mkF [0, 1, 0, 2, 2], mkF [0, 1, 1, 2, 0, 0, 1], mkF [0, 1, 2, 0, 1, 0, 1],
   mkF [0, 1, 2, 3], mkF [0, 1, 3, 0, 2], mkF [1, 1, 3, 0, 0, 0, 1]]

/-- The second hexagon. -/
def hexB : List Forest :=
  [mkF [0, 1, 0, 1, 3], mkF [0, 2, 0, 2, 0, 0, 1], mkF [0, 2, 1, 0, 1, 0, 1],
   mkF [0, 2, 0, 4], mkF [0, 2, 1, 0, 3], mkF [0, 2, 3, 0, 0, 0, 1]]

/-- The twelve covers inside `(x, Z)`. -/
def edges : List (Forest × Forest) :=
  [(mkF [0, 1, 0, 1, 3], mkF [0, 2, 0, 4]), (mkF [0, 1, 0, 1, 3], mkF [0, 2, 1, 0, 3]),
   (mkF [0, 1, 0, 2, 2], mkF [0, 1, 2, 3]), (mkF [0, 1, 0, 2, 2], mkF [0, 1, 3, 0, 2]),
   (mkF [0, 1, 1, 2, 0, 0, 1], mkF [0, 1, 2, 3]),
   (mkF [0, 1, 1, 2, 0, 0, 1], mkF [1, 1, 3, 0, 0, 0, 1]),
   (mkF [0, 1, 2, 0, 1, 0, 1], mkF [0, 1, 3, 0, 2]),
   (mkF [0, 1, 2, 0, 1, 0, 1], mkF [1, 1, 3, 0, 0, 0, 1]),
   (mkF [0, 2, 0, 2, 0, 0, 1], mkF [0, 2, 0, 4]),
   (mkF [0, 2, 0, 2, 0, 0, 1], mkF [0, 2, 3, 0, 0, 0, 1]),
   (mkF [0, 2, 1, 0, 1, 0, 1], mkF [0, 2, 1, 0, 3]),
   (mkF [0, 2, 1, 0, 1, 0, 1], mkF [0, 2, 3, 0, 0, 0, 1])]

/-- A maximal chain `∅ < x₁ < x₂ < x₃ < x`. -/
def x1 : Forest := mkF [0, 1]
def x2 : Forest := mkF [0, 1, 0, 1]
def x3 : Forest := mkF [0, 1, 0, 1, 1]

/-- Cover certificates `(F, k, G)`: `P_G` occurs in `L_k P_F`. -/
def certs : List (Forest × ℕ × Forest) :=
  [(empty, 2, x1), (x1, 4, x2), (x2, 5, x3), (x3, 7, xc),
   (xc, 5, mkF [0, 1, 0, 2, 2]), (xc, 4, mkF [0, 1, 1, 2, 0, 0, 1]),
   (xc, 3, mkF [0, 1, 2, 0, 1, 0, 1]), (xc, 5, mkF [0, 1, 0, 1, 3]),
   (xc, 4, mkF [0, 2, 0, 2, 0, 0, 1]), (xc, 3, mkF [0, 2, 1, 0, 1, 0, 1]),
   (mkF [0, 1, 0, 1, 3], 4, mkF [0, 2, 0, 4]), (mkF [0, 1, 0, 1, 3], 3, mkF [0, 2, 1, 0, 3]),
   (mkF [0, 1, 0, 2, 2], 4, mkF [0, 1, 2, 3]), (mkF [0, 1, 0, 2, 2], 3, mkF [0, 1, 3, 0, 2]),
   (mkF [0, 1, 1, 2, 0, 0, 1], 4, mkF [0, 1, 2, 3]),
   (mkF [0, 1, 1, 2, 0, 0, 1], 3, mkF [1, 1, 3, 0, 0, 0, 1]),
   (mkF [0, 1, 2, 0, 1, 0, 1], 5, mkF [0, 1, 3, 0, 2]),
   (mkF [0, 1, 2, 0, 1, 0, 1], 3, mkF [1, 1, 3, 0, 0, 0, 1]),
   (mkF [0, 2, 0, 2, 0, 0, 1], 4, mkF [0, 2, 0, 4]),
   (mkF [0, 2, 0, 2, 0, 0, 1], 3, mkF [0, 2, 3, 0, 0, 0, 1]),
   (mkF [0, 2, 1, 0, 1, 0, 1], 5, mkF [0, 2, 1, 0, 3]),
   (mkF [0, 2, 1, 0, 1, 0, 1], 3, mkF [0, 2, 3, 0, 0, 0, 1]),
   (mkF [0, 1, 2, 3], 3, Zc), (mkF [0, 1, 3, 0, 2], 3, Zc), (mkF [1, 1, 3, 0, 0, 0, 1], 3, Zc),
   (mkF [0, 2, 0, 4], 3, Zc), (mkF [0, 2, 1, 0, 3], 3, Zc), (mkF [0, 2, 3, 0, 0, 0, 1], 3, Zc)]

theorem certs_ok : ∀ c ∈ certs, 1 ≤ c.2.1 ∧
    (∀ G ∈ upL c.2.1 c.1, coefL G c.2.1 c.1 = 0 ∨ coefL G c.2.1 c.1 = 1) ∧
    coefL c.2.2 c.2.1 c.1 = 1 := by
  decide +kernel

/-- The certified covers. -/
def coverPairs : List (Forest × Forest) := certs.map (fun c => (c.1, c.2.2))

lemma cover_of_mem {F G : Forest} (h : (F, G) ∈ coverPairs) : MonkCover F G := by
  obtain ⟨⟨F', k, G'⟩, hc, he⟩ := List.mem_map.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨hk, hchk, hG⟩ := certs_ok _ hc
  exact monkCover_of_check hk hchk hG

/-! ### Finite facts -/

theorem facts_sizes : xc.size = 4 ∧ Zc.size = 7 ∧ (∀ y ∈ ys, y.size = 5) ∧
    (∀ z ∈ zs, z.size = 6) ∧ Zc.len + Zc.size = 10 ∧ x1.size = 1 ∧ x2.size = 2 ∧ x3.size = 3 := by
  decide +kernel

theorem facts_edges : (∀ e ∈ edges, e.1 ∈ ys ∧ e.2 ∈ zs ∧ e ∈ coverPairs) ∧
    (∀ y ∈ ys, (xc, y) ∈ coverPairs ∧ ∃ z ∈ zs, (y, z) ∈ edges) ∧
    (∀ z ∈ zs, (z, Zc) ∈ coverPairs ∧ ∃ y ∈ ys, (y, z) ∈ edges) := by
  decide +kernel

theorem facts_hex : (∀ e ∈ edges, (e.1 ∈ hexA ∧ e.2 ∈ hexA) ∨ (e.1 ∈ hexB ∧ e.2 ∈ hexB)) ∧
    (∀ w ∈ hexA, w ∉ hexB) ∧ (∀ w ∈ ys ++ zs, w ∈ hexA ∨ w ∈ hexB) ∧
    (∀ w ∈ hexA ++ hexB, w ∈ ys ∨ w ∈ zs) ∧
    (mkF [0, 1, 0, 2, 2], mkF [0, 1, 2, 3]) ∈ edges ∧ mkF [0, 1, 0, 2, 2] ∈ hexA ∧
    mkF [0, 1, 2, 3] ∈ hexA ∧
    (mkF [0, 1, 0, 1, 3], mkF [0, 2, 0, 4]) ∈ edges ∧ mkF [0, 1, 0, 1, 3] ∈ hexB ∧
    mkF [0, 2, 0, 4] ∈ hexB := by
  decide +kernel

theorem facts_chain : (empty, x1) ∈ coverPairs ∧ (x1, x2) ∈ coverPairs ∧ (x2, x3) ∈ coverPairs ∧
    (x3, xc) ∈ coverPairs ∧ (xc, mkF [0, 1, 0, 2, 2]) ∈ coverPairs ∧
    (mkF [0, 1, 0, 2, 2], mkF [0, 1, 2, 3]) ∈ coverPairs ∧ (mkF [0, 1, 2, 3], Zc) ∈ coverPairs := by
  decide +kernel

/-! ### Completeness of `(x, Z)` -/

/-- The finite completeness check for lower covers `z ⋖ Z` through index `k`. -/
abbrev ComplK (k : ℕ) : Prop :=
  ∀ z ∈ lowL Zc k, coefL Zc k z = 1 → ∀ k₂ ∈ List.range' 1 (z.len + z.size),
    ∀ y ∈ lowL z k₂, coefL z k₂ y = 1 →
      (∃ k₁ ∈ List.range' 1 (y.len + y.size), coefL y k₁ xc = 1) → (y, z) ∈ edges

theorem compl_1 : ComplK 1 := by decide +kernel
theorem compl_2 : ComplK 2 := by decide +kernel
theorem compl_3 : ComplK 3 := by decide +kernel
theorem compl_4 : ComplK 4 := by decide +kernel
theorem compl_5 : ComplK 5 := by decide +kernel
theorem compl_6 : ComplK 6 := by decide +kernel
theorem compl_7 : ComplK 7 := by decide +kernel
theorem compl_8 : ComplK 8 := by decide +kernel
theorem compl_9 : ComplK 9 := by decide +kernel
theorem compl_10 : ComplK 10 := by decide +kernel

lemma complK {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 10) : ComplK k := by
  interval_cases k
  exacts [compl_1, compl_2, compl_3, compl_4, compl_5, compl_6, compl_7, compl_8, compl_9,
    compl_10]

/-- Every chain `x ⋖ y ⋖ z ⋖ Z` is one of the twelve edges. -/
theorem complete {y z : Forest} (h1 : MonkCover xc y) (h2 : MonkCover y z) (h3 : MonkCover z Zc) :
    (y, z) ∈ edges := by
  obtain ⟨k₃, hk₃, hb₃, hz, hc₃⟩ := cover_lowL h3
  obtain ⟨k₂, hk₂, hb₂, hy, hc₂⟩ := cover_lowL h2
  obtain ⟨k₁, hk₁, hb₁, -, hc₁⟩ := cover_lowL h1
  rw [facts_sizes.2.2.2.2.1] at hb₃
  exact complK hk₃ hb₃ z hz hc₃ k₂ (List.mem_range'_1.2 ⟨hk₂, by omega⟩) y hy hc₂
    ⟨k₁, List.mem_range'_1.2 ⟨hk₁, by omega⟩, hc₁⟩

/-! ### The open interval `(x, Z)` -/

local notation "LE" => QBruhatLE

lemma hpo : IsPartialOrderRel QBruhatLE :=
  ⟨QBruhatLE.refl, fun _ _ _ => QBruhatLE.trans, fun _ _ => QBruhatLE.antisymm⟩

lemma le_of_pair {F G : Forest} (h : (F, G) ∈ coverPairs) : LE F G :=
  QBruhatLE.of_cover (cover_of_mem h)

lemma ne_of_size {F G : Forest} (h : F.size ≠ G.size) : F ≠ G := fun e => h (e ▸ rfl)

lemma y_mem {y : Forest} (hy : y ∈ ys) : MonkCover xc y ∧ ∃ z ∈ zs, (y, z) ∈ edges ∧
    MonkCover y z ∧ MonkCover z Zc := by
  obtain ⟨hxy, z, hz, he⟩ := facts_edges.2.1 y hy
  exact ⟨cover_of_mem hxy, z, hz, he, cover_of_mem (facts_edges.1 _ he).2.2,
    cover_of_mem (facts_edges.2.2 z hz).1⟩

lemma z_mem {z : Forest} (hz : z ∈ zs) : MonkCover z Zc ∧ ∃ y ∈ ys, (y, z) ∈ edges ∧
    MonkCover xc y ∧ MonkCover y z := by
  obtain ⟨hzZ, y, hy, he⟩ := facts_edges.2.2 z hz
  exact ⟨cover_of_mem hzZ, y, hy, he, cover_of_mem (facts_edges.2.1 y hy).1,
    cover_of_mem (facts_edges.1 _ he).2.2⟩

theorem mem_OI {w : Forest} : w ∈ openInt QBruhatLE xc Zc ↔ w ∈ ys ∨ w ∈ zs := by
  obtain ⟨sx, sZ, sy, sz, -⟩ := facts_sizes
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have a1 := size_lt_of_le_ne h1 (Ne.symm h2)
    have a2 := size_lt_of_le_ne h3 h4
    rw [sx] at a1; rw [sZ] at a2
    by_cases h5 : w.size = 5
    · left
      have hxw := cover_of_le h1 (by omega)
      obtain ⟨M, hwM, hMZ⟩ := exists_cover_of_le h3 h4
      have := cover_size hMZ
      have hwM' := cover_of_le hwM (by omega)
      exact (facts_edges.1 _ (complete hxw hwM' hMZ)).1
    · right
      have hwZ := cover_of_le h3 (by omega)
      obtain ⟨M, hxM, hMw⟩ := exists_cover_of_le h1 (Ne.symm h2)
      have := cover_size hMw
      have hxM' := cover_of_le hxM (by omega)
      exact (facts_edges.1 _ (complete hxM' hMw hwZ)).2.1
  · rintro (hy | hz)
    · obtain ⟨hxy, z, hz, -, hyz, hzZ⟩ := y_mem hy
      have := sy _ hy; have := sz _ hz
      exact ⟨QBruhatLE.of_cover hxy, ne_of_size (by omega),
        (QBruhatLE.of_cover hyz).trans (QBruhatLE.of_cover hzZ), ne_of_size (by omega)⟩
    · obtain ⟨hzZ, y, hy, -, hxy, hyz⟩ := z_mem hz
      have := sy _ hy; have := sz _ hz
      exact ⟨(QBruhatLE.of_cover hxy).trans (QBruhatLE.of_cover hyz), ne_of_size (by omega),
        QBruhatLE.of_cover hzZ, ne_of_size (by omega)⟩

lemma size_OI {w : Forest} (hw : w ∈ openInt QBruhatLE xc Zc) :
    (w ∈ ys ∧ w.size = 5) ∨ (w ∈ zs ∧ w.size = 6) := by
  rcases mem_OI.1 hw with h | h
  · exact Or.inl ⟨h, facts_sizes.2.2.1 w h⟩
  · exact Or.inr ⟨h, facts_sizes.2.2.2.1 w h⟩

/-- Comparable distinct elements of `(x, Z)` form an edge. -/
lemma edge_of_le {u v : Forest} (hu : u ∈ openInt QBruhatLE xc Zc)
    (hv : v ∈ openInt QBruhatLE xc Zc) (h : LE u v) (hne : u ≠ v) : (u, v) ∈ edges := by
  have hlt := size_lt_of_le_ne h hne
  rcases size_OI hu with ⟨huy, hus⟩ | ⟨-, hus⟩ <;> rcases size_OI hv with ⟨-, hvs⟩ | ⟨hvz, hvs⟩
  · omega
  · exact complete (y_mem huy).1 (cover_of_le h (by omega)) (z_mem hvz).1
  · omega
  · omega

lemma eq_of_comp {u v : Forest} (h : LE u v ∨ LE v u) (hs : u.size = v.size) : u = v := by
  rcases h with h | h
  · exact eq_of_le_of_size h hs.ge
  · exact (eq_of_le_of_size h hs.le).symm

lemma edge_le {e : Forest × Forest} (he : e ∈ edges) : LE e.1 e.2 :=
  le_of_pair (facts_edges.1 e he).2.2

lemma edge_mem {e : Forest × Forest} (he : e ∈ edges) :
    e.1 ∈ openInt QBruhatLE xc Zc ∧ e.2 ∈ openInt QBruhatLE xc Zc :=
  ⟨mem_OI.2 (Or.inl (facts_edges.1 e he).1), mem_OI.2 (Or.inr (facts_edges.1 e he).2.1)⟩

/-- The maximal chains of `(x, Z)` are exactly the twelve edges. -/
theorem maxChain_iff {C : Finset Forest} :
    IsMaxChainIn QBruhatLE (openInt QBruhatLE xc Zc) C ↔ ∃ e ∈ edges, C = {e.1, e.2} := by
  constructor
  · rintro ⟨⟨hCI, hCc⟩, hmax⟩
    -- inserting a comparable element would enlarge `C`
    have grow : ∀ w ∈ openInt QBruhatLE xc Zc, (∀ u ∈ C, LE u w ∨ LE w u) → w ∈ C := by
      intro w hw hcomp
      refine hmax (insert w C) ⟨fun u hu => ?_, fun u hu v hv => ?_⟩
        (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)
      · rcases Finset.mem_insert.1 hu with rfl | hu
        · exact hw
        · exact hCI u hu
      · by_cases huw : u = w
        · rw [huw]
          by_cases hvw : v = w
          · rw [hvw]; exact Or.inl (QBruhatLE.refl _)
          · exact (hcomp v (Finset.mem_of_mem_insert_of_ne hv hvw)).symm
        · have hu' := Finset.mem_of_mem_insert_of_ne hu huw
          by_cases hvw : v = w
          · rw [hvw]; exact hcomp u hu'
          · exact hCc u hu' v (Finset.mem_of_mem_insert_of_ne hv hvw)
    have rank5 : ∀ a ∈ C, ∀ b ∈ C, a ∈ ys → b ∈ ys → a = b := fun a ha b hb hay hby =>
      eq_of_comp (hCc a ha b hb) (by rw [facts_sizes.2.2.1 a hay, facts_sizes.2.2.1 b hby])
    have rank6 : ∀ a ∈ C, ∀ b ∈ C, a ∈ zs → b ∈ zs → a = b := fun a ha b hb haz hbz =>
      eq_of_comp (hCc a ha b hb) (by rw [facts_sizes.2.2.2.1 a haz, facts_sizes.2.2.2.1 b hbz])
    by_cases hY : ∃ a ∈ C, a ∈ ys
    · obtain ⟨a, haC, hay⟩ := hY
      by_cases hZ : ∃ b ∈ C, b ∈ zs
      · obtain ⟨b, hbC, hbz⟩ := hZ
        have hab : (a, b) ∈ edges := by
          have hsa := facts_sizes.2.2.1 a hay
          have hsb := facts_sizes.2.2.2.1 b hbz
          rcases hCc a haC b hbC with h | h
          · exact edge_of_le (hCI a haC) (hCI b hbC) h (ne_of_size (by omega))
          · have := le_size h; omega
        refine ⟨(a, b), hab, ?_⟩
        ext u
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hu
          rcases mem_OI.1 (hCI u hu) with h | h
          · exact Or.inl (rank5 u hu a haC h hay)
          · exact Or.inr (rank6 u hu b hbC h hbz)
        · rintro (rfl | rfl)
          · exact haC
          · exact hbC
      · exfalso
        obtain ⟨-, z, hz, he, -, -⟩ := y_mem hay
        apply hZ
        refine ⟨z, grow z (edge_mem he).2 fun u hu => ?_, hz⟩
        rcases mem_OI.1 (hCI u hu) with h | h
        · rw [rank5 u hu a haC h hay]; exact Or.inl (edge_le he)
        · exact absurd ⟨u, hu, h⟩ hZ
    · exfalso
      by_cases hZ : ∃ b ∈ C, b ∈ zs
      · obtain ⟨b, hbC, hbz⟩ := hZ
        obtain ⟨-, y, hy, he, -, -⟩ := z_mem hbz
        apply hY
        refine ⟨y, grow y (edge_mem he).1 fun u hu => ?_, hy⟩
        rcases mem_OI.1 (hCI u hu) with h | h
        · exact absurd ⟨u, hu, h⟩ hY
        · rw [rank6 u hu b hbC h hbz]; exact Or.inr (edge_le he)
      · have hy0 : mkF [0, 1, 0, 2, 2] ∈ ys := by decide +kernel
        apply hY
        refine ⟨_, grow _ (mem_OI.2 (Or.inl hy0)) fun u hu => ?_, hy0⟩
        rcases mem_OI.1 (hCI u hu) with h | h
        · exact absurd ⟨u, hu, h⟩ hY
        · exact absurd ⟨u, hu, h⟩ hZ
  · rintro ⟨e, he, rfl⟩
    obtain ⟨h1, h2⟩ := edge_mem he
    have hle := edge_le he
    refine ⟨⟨fun u hu => ?_, fun u hu v hv => ?_⟩, fun D hD hsub w hw => ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact h1
      · exact h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact Or.inl (QBruhatLE.refl _)
      · exact Or.inl hle
      · exact Or.inr hle
      · exact Or.inl (QBruhatLE.refl _)
    · have hs1 := facts_sizes.2.2.1 _ (facts_edges.1 e he).1
      have hs2 := facts_sizes.2.2.2.1 _ (facts_edges.1 e he).2.1
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases size_OI (hD.1 w hw) with ⟨-, hws⟩ | ⟨-, hws⟩
      · left
        exact eq_of_comp (hD.2 w hw e.1 (hsub (by simp))) (by omega)
      · right
        exact eq_of_comp (hD.2 w hw e.2 (hsub (by simp))) (by omega)

/-- The open interval `(x, Z)` is the disjoint union of two nonempty parts (the two hexagons)
with no comparable pair across the parts; in particular `Δ((x, Z))` is disconnected. -/
theorem open_interval_x_Z_disconnected :
    ∃ A B : Set Forest, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      openInt QBruhatLE xc Zc = A ∪ B ∧
      ∀ a ∈ A, ∀ b ∈ B, ¬ QBruhatLE a b ∧ ¬ QBruhatLE b a := by
  obtain ⟨hE, hAB, hcov, hsub, -, hA1, -, -, hB1, -⟩ := facts_hex
  refine ⟨{w | w ∈ hexA}, {w | w ∈ hexB}, ⟨_, hA1⟩, ⟨_, hB1⟩, ?_, ?_, ?_⟩
  · exact Set.disjoint_left.2 fun w hA hB => hAB w hA hB
  · ext w
    constructor
    · intro h; exact hcov w (List.mem_append.2 (mem_OI.1 h))
    · intro h; exact mem_OI.2 (hsub w (List.mem_append.2 h))
  · have hmem : ∀ w, w ∈ hexA ∨ w ∈ hexB → w ∈ openInt QBruhatLE xc Zc := fun w h =>
      mem_OI.2 (hsub w (List.mem_append.2 h))
    have key : ∀ a b, a ∈ hexA → b ∈ hexB → ¬ QBruhatLE a b ∧ ¬ QBruhatLE b a := by
      intro a b ha hb
      have hne : a ≠ b := fun h => hAB a ha (h ▸ hb)
      constructor
      · intro h
        rcases hE _ (edge_of_le (hmem a (Or.inl ha)) (hmem b (Or.inr hb)) h hne) with
          ⟨-, h'⟩ | ⟨h', -⟩
        · exact hAB b h' hb
        · exact hAB a ha h'
      · intro h
        rcases hE _ (edge_of_le (hmem b (Or.inr hb)) (hmem a (Or.inl ha)) h (Ne.symm hne)) with
          ⟨h', -⟩ | ⟨-, h'⟩
        · exact hAB b h' hb
        · exact hAB a ha h'
    exact fun a ha b hb => key a b ha hb

/-- The order complex of `(x, Z)` is not shellable. -/
theorem not_shellable_x_Z : ¬ ShellableProper QBruhatLE (openInt QBruhatLE xc Zc) := by
  classical
  intro hS
  obtain ⟨hE, hAB, -, -, hA0, hA1, hA2, hB0, hB1, hB2⟩ := facts_hex
  have hcard : ∀ C, IsMaxChainIn QBruhatLE (openInt QBruhatLE xc Zc) C → 2 ≤ C.card := by
    intro C hC
    obtain ⟨e, he, rfl⟩ := maxChain_iff.1 hC
    have hs1 := facts_sizes.2.2.1 _ (facts_edges.1 e he).1
    have hs2 := facts_sizes.2.2.2.1 _ (facts_edges.1 e he).2.1
    rw [Finset.card_pair (ne_of_size (by omega))]
  refine not_shellable_of_split hS hcard (fun C => ∀ w ∈ C, w ∈ hexA)
    ⟨_, maxChain_iff.2 ⟨_, hA0, rfl⟩, ?_⟩ ⟨_, maxChain_iff.2 ⟨_, hB0, rfl⟩, ?_⟩ ?_
  · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hA1
    · exact hA2
  · intro h; exact hAB _ (h _ (by simp)) hB1
  · intro C D hC hD hpC hpD
    obtain ⟨e, he, rfl⟩ := maxChain_iff.1 hD
    have hDB : e.1 ∈ hexB ∧ e.2 ∈ hexB := by
      rcases hE e he with h | h
      · exact absurd (fun w hw => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact h.1
          · exact h.2) hpD
      · exact h
    refine Finset.disjoint_left.2 fun w hwC hwD => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwD
    rcases hwD with rfl | rfl
    · exact hAB _ (hpC _ hwC) hDB.1
    · exact hAB _ (hpC _ hwC) hDB.2

/-! ### From the lower interval to the open interval -/

lemma shellable_lower_to_open {G : Forest} (hG : QBruhatLE empty G)
    (h : IsShellable QBruhatLE (lowerInterval G)) :
    ShellableProper QBruhatLE (openInt QBruhatLE empty G) := by
  obtain ⟨bot, hbotP, top, htopP, hall, hS⟩ := h
  have hbot : bot = empty := eq_of_le_of_size (hall empty hG).1 (by simp [size_empty])
  have htop : top = G := QBruhatLE.antisymm htopP (hall G (QBruhatLE.refl G)).2
  rw [hbot, htop] at hS
  have : lowerInterval G \ {empty, G} = openInt QBruhatLE empty G := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      have h2' : w ≠ empty ∧ w ≠ G := ⟨fun h => h2 (Or.inl h), fun h => h2 (Or.inr h)⟩
      exact ⟨hbot ▸ (hall w h1).1, h2'.1, h1, h2'.2⟩
    · rintro ⟨-, h2, h3, h4⟩
      exact ⟨h3, fun h => h.elim h2 h4⟩
  rw [← this]; exact hS

/-- A chain containing an element of every intermediate rank is maximal. -/
lemma maxChain_of_graded {a b : Forest} {c : Finset Forest}
    (hc : IsChainIn QBruhatLE (openInt QBruhatLE a b) c)
    (hg : ∀ w ∈ openInt QBruhatLE a b, ∃ e ∈ c, e.size = w.size) :
    IsMaxChainIn QBruhatLE (openInt QBruhatLE a b) c := by
  refine ⟨hc, fun D hD hsub w hw => ?_⟩
  obtain ⟨e, he, hs⟩ := hg w (hD.1 w hw)
  rw [eq_of_comp (hD.2 w hw e (hsub he)) hs.symm]; exact he

lemma le_chain : LE empty x1 ∧ LE x1 x2 ∧ LE x2 x3 ∧ LE x3 xc ∧ LE xc Zc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := facts_chain
  exact ⟨le_of_pair h1, le_of_pair h2, le_of_pair h3, le_of_pair h4,
    (le_of_pair h5).trans ((le_of_pair h6).trans (le_of_pair h7))⟩

lemma c0_max : IsMaxChainIn QBruhatLE (openInt QBruhatLE empty xc) {x1, x2, x3} := by
  obtain ⟨l1, l2, l3, l4, -⟩ := le_chain
  obtain ⟨sx, -, -, -, -, s1, s2, s3⟩ := facts_sizes
  have mem : ∀ w ∈ ({x1, x2, x3} : Finset Forest), w ∈ openInt QBruhatLE empty xc := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨l1, ne_of_size (by rw [s1, size_empty]; omega), l2.trans (l3.trans l4),
        ne_of_size (by omega)⟩
    · exact ⟨l1.trans l2, ne_of_size (by rw [s2, size_empty]; omega), l3.trans l4,
        ne_of_size (by omega)⟩
    · exact ⟨l1.trans (l2.trans l3), ne_of_size (by rw [s3, size_empty]; omega), l4,
        ne_of_size (by omega)⟩
  apply maxChain_of_graded ⟨mem, fun u hu v hv => ?_⟩
  · intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    have a1 := size_lt_of_le_ne h1 (Ne.symm h2)
    have a2 := size_lt_of_le_ne h3 h4
    rw [size_empty] at a1; rw [sx] at a2
    by_cases w1 : w.size = 1
    · exact ⟨x1, by simp, by omega⟩
    by_cases w2 : w.size = 2
    · exact ⟨x2, by simp, by omega⟩
    · exact ⟨x3, by simp, by omega⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals first
      | exact Or.inl (QBruhatLE.refl _)
      | exact Or.inl l2 | exact Or.inr l2
      | exact Or.inl l3 | exact Or.inr l3
      | exact Or.inl (l2.trans l3) | exact Or.inr (l2.trans l3)

/-- `(∅, Z)` is not shellable: Fact 6.1 would restrict a shelling to `(x, Z)`. -/
theorem not_shellable_empty_Z : ¬ ShellableProper QBruhatLE (openInt QBruhatLE empty Zc) := by
  intro hS
  obtain ⟨l1, l2, l3, l4, l5⟩ := le_chain
  obtain ⟨sx, sZ, -⟩ := facts_sizes
  exact not_shellable_x_Z (fact61_left hpo c0_max (l1.trans (l2.trans (l3.trans l4)))
    (ne_of_size (by rw [sx, size_empty]; omega)) l5 (ne_of_size (by omega)) hS)

lemma empty_le_Z : QBruhatLE empty Zc := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := le_chain
  exact l1.trans (l2.trans (l3.trans (l4.trans l5)))

/-! ### Exported results -/

/-- `Z = (1, 2, 4)` is a zigzag forest (Definition 6.8). -/
theorem Z_is_zigzag : IsZigzag Zc := by
  intro a ha; simp [Zc, zig] at ha; omega

/-- The lower interval `[∅, Z]` of the zigzag forest `Z = (1, 2, 4)` is not shellable. -/
theorem lowerInterval_Z_not_shellable : ¬ IsShellable QBruhatLE (lowerInterval Zc) :=
  fun h => not_shellable_empty_Z (shellable_lower_to_open empty_le_Z h)

/-! ### The family `Z_m = (m - 6, 2, 4)` -/

lemma zig_size (a : ℕ) : (zig a).size = a + 6 := by simp [zig, size]

lemma Zc_size : Zc.size = 7 := zig_size 1

lemma zig_zigzag {a : ℕ} (ha : 1 ≤ a) : IsZigzag (zig a) := by
  intro b hb; simp [zig] at hb; omega

lemma endAt_one_le (F : Forest) (p : ℕ) : ∀ s, F.endAt p 1 ≤ F.endAt p (s + 1) := by
  intro s
  induction s with
  | zero => exact le_rfl
  | succ s ih =>
    rw [endAt_succ F p (s + 1)]
    have := F.le_E (F.endAt p (s + 1) + 1); omega

lemma zig_cover {a : ℕ} (ha : 1 ≤ a) : MonkCover (zig a) (zig (a + 1)) := by
  apply monkCover_raise rfl
  · intro i hi
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
    rfl
  · apply c_eq_zero_of_lt
    have hE1 : (zig a).E 1 = (zig a).endAt 1 a := (zig a).E_eq le_rfl
    have hE2 : (zig a).E 2 = (zig a).endAt 2 2 := (zig a).E_eq (by omega)
    have h22 := (zig a).le_endAt 2 2
    obtain ⟨s, rfl⟩ : ∃ s, a = s + 1 := ⟨a - 1, by omega⟩
    have hm := endAt_one_le (zig (s + 1)) 1 s
    have h1 : (zig (s + 1)).endAt 1 1 = (zig (s + 1)).E 2 := by
      rw [endAt_succ]; rfl
    show 3 < _ + 1
    omega

lemma zig_le {a : ℕ} (ha : 1 ≤ a) : ∀ n, QBruhatLE (zig a) (zig (a + n)) := by
  intro n
  induction n with
  | zero => exact QBruhatLE.refl _
  | succ n ih => exact ih.trans (QBruhatLE.of_cover (zig_cover (by omega)))

lemma zig_le' {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : QBruhatLE (zig a) (zig b) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab; exact zig_le ha n

/-- Conjecture C / 6.11 fails for every rank `m ≥ 7`: the zigzag forest `Z_m = (m - 6, 2, 4)`
of rank `m` has a non-shellable lower interval. -/
theorem not_bansal_conjecture_C :
    ∀ m, 7 ≤ m → ∃ Zm : Forest, IsZigzag Zm ∧ Zm.size = m ∧
      ¬ IsShellable QBruhatLE (lowerInterval Zm) := by
  intro m hm
  refine ⟨zig (m - 6), zig_zigzag (by omega), by rw [zig_size]; omega, fun h => ?_⟩
  have hZm : QBruhatLE Zc (zig (m - 6)) := zig_le' le_rfl (by omega)
  have hS := shellable_lower_to_open (empty_le_Z.trans hZm) h
  by_cases h7 : m = 7
  · subst h7; exact not_shellable_empty_Z hS
  · apply not_shellable_empty_Z
    have hc1 : IsMaxChainIn QBruhatLE (openInt QBruhatLE Zc (zig (m - 6)))
        ((Finset.Icc 2 (m - 7)).image zig) := by
      apply maxChain_of_graded ⟨fun w hw => ?_, fun u hu v hv => ?_⟩
      · intro w hw
        obtain ⟨h1, h2, h3, h4⟩ := hw
        have a1 := size_lt_of_le_ne h1 (Ne.symm h2)
        have a2 := size_lt_of_le_ne h3 h4
        rw [Zc_size] at a1; rw [zig_size] at a2
        exact ⟨zig (w.size - 6), Finset.mem_image_of_mem _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩),
          by rw [zig_size]; omega⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw
        obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.1 ha
        exact ⟨zig_le' le_rfl (by omega), ne_of_size (by rw [zig_size, Zc_size]; omega),
          zig_le' (by omega) (by omega), ne_of_size (by rw [zig_size, zig_size]; omega)⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
        have := (Finset.mem_Icc.1 ha).1; have := (Finset.mem_Icc.1 hb).1
        rcases le_total a b with hab | hab
        · exact Or.inl (zig_le' (by omega) hab)
        · exact Or.inr (zig_le' (by omega) hab)
    exact fact61_right hpo hc1 empty_le_Z (ne_of_size (by rw [Zc_size, size_empty]; omega))
      hZm (ne_of_size (by rw [Zc_size, zig_size]; omega)) hS

/-- Conjecture C (Conjecture 6.11) of arXiv:2611.02210 is false. -/
theorem bansal_conjecture_C_false :
    ¬ ∀ Z : Forest, IsZigzag Z → IsShellable QBruhatLE (lowerInterval Z) :=
  fun h => lowerInterval_Z_not_shellable (h Zc Z_is_zigzag)

end QuasisymmetricBruhat
