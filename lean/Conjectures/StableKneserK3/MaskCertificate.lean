import Conjectures.StableKneserK3.Basic
import Mathlib.Data.Nat.Bitwise

namespace StableKneserK3.MaskCertificate

/-- Rows of the adjacency matrix and subsets of its vertices are bit masks. -/
abbrev Rows := ℕ → ℕ

def difference (u v : ℕ) := u ^^^ (u &&& v)

private theorem bit_difference {u v x : ℕ} :
    (difference u v).testBit x = true ↔ u.testBit x = true ∧ v.testBit x = false := by
  simp only [difference, Nat.testBit_xor, Nat.testBit_and]
  cases u.testBit x <;> cases v.testBit x <;> decide

private theorem bit_subset {u v : ℕ} (h : u &&& v = u) {x : ℕ} (hx : u.testBit x = true) :
    v.testBit x = true := by
  have he := congrArg (fun n : ℕ => n.testBit x) h
  simpa [Nat.testBit_and, hx] using he

structure Coloring (g : Rows) (k u : ℕ) (c : ℕ → ℕ) : Prop where
  bound : ∀ x, u.testBit x → c x < k
  proper : ∀ a b, u.testBit a → u.testBit b → (g a).testBit b → c a ≠ c b

def Obstruction (g : Rows) (k u : ℕ) : Prop := ∀ c, ¬ Coloring g k u c

inductive Branch where
  | leaf (prior : ℕ)
  | split (vertex : ℕ) (absent present : Branch)
  deriving Inhabited

/-- Fixed-width rows of bits packed into a single natural number. -/
structure Table where
  size : ℕ
  width : ℕ
  data : ℕ

def Table.get (t : Table) (i : ℕ) := (t.data >>> (i * t.width)) % 2^t.width

/-- A leaf reuses a lower bound with one fewer color on a subset of the residual graph. -/
def checkBranch (g : Rows) (prior : Table) (u a : ℕ) : Branch → Bool
  | .leaf j => j < prior.size && (prior.get j &&& difference u a) == prior.get j
  | .split v l r =>
    checkBranch g prior u (difference a (2^v)) l && checkBranch g prior u (difference a (g v)) r

private theorem branch_sound {g : Rows} {prior : Table} {u k : ℕ}
    (old : ∀ j : Fin prior.size, Obstruction g k (prior.get j)) (t : Branch) (a : ℕ)
    (h : checkBranch g prior u a t) {c : ℕ → ℕ} (hc : Coloring g (k+1) u c)
    {i : ℕ} (hi : i < k+1) (ha : ∀ x, u.testBit x → c x = i → a.testBit x) : False := by
  induction t generalizing a with
  | leaf j =>
    simp only [checkBranch, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hj, hs⟩ := h
    have sub {x} (hx : (prior.get j).testBit x) := bit_difference.mp (bit_subset hs hx)
    have miss {x} (hx : (prior.get j).testBit x) : c x ≠ i := fun he => by
      have hh := ha x (sub hx).1 he
      simp [(sub hx).2] at hh
    let d (x : ℕ) := if c x < i then c x else c x - 1
    apply old ⟨j,hj⟩ d
    constructor
    · intro x hx
      have := miss hx
      have := hc.bound x (sub hx).1
      dsimp [d]
      split <;> omega
    · intro x y hx hy he
      have := miss hx
      have := miss hy
      have := hc.proper x y (sub hx).1 (sub hy).1 he
      dsimp [d]
      split <;> split <;> omega
  | split v l r hl hr =>
    simp only [checkBranch, Bool.and_eq_true] at h
    obtain ⟨h₁,h₂⟩ := h
    by_cases hv : u.testBit v = true ∧ c v = i
    · apply hr _ h₂
      intro x hx he
      apply bit_difference.mpr ⟨ha x hx he, ?_⟩
      cases hvx : (g v).testBit x
      · rfl
      · exact False.elim (hc.proper _ _ hv.1 hx hvx (hv.2.trans he.symm))
    · apply hl _ h₁
      intro x hx he
      have hne : v ≠ x := by rintro rfl; exact hv ⟨hx, he⟩
      exact bit_difference.mpr ⟨ha x hx he, Nat.testBit_two_pow_of_ne (by grind)⟩

structure Step where
  vertices : ℕ
  pivot : ℕ
  branches : Branch

def checkStep (g : Rows) (prior : Table) (s : Step) : Bool :=
  s.vertices.testBit s.pivot &&
    checkBranch g prior s.vertices (difference s.vertices (g s.pivot)) s.branches

theorem step_sound {g : Rows} {prior : Table} {k : ℕ}
    (old : ∀ j : Fin prior.size, Obstruction g k (prior.get j)) (s : Step) (h : checkStep g prior s) :
    Obstruction g (k+1) s.vertices := by
  simp only [checkStep, Bool.and_eq_true] at h
  obtain ⟨hv, hb⟩ := h
  intro c hc
  apply branch_sound old _ _ hb hc (hc.bound _ hv)
  intro x hx he
  apply bit_difference.mpr ⟨hx,?_⟩
  cases hh : (g s.pivot).testBit x
  · rfl
  · exact False.elim (hc.proper _ _ hv hx hh he.symm)

/-- The walk checker tests each edge and requires the last vertex to equal the endpoint. -/
def walk (g : Rows) (u b : ℕ) (a : ℕ) : List ℕ → Bool
  | [] => a == b
  | x :: xs => u.testBit x && (g a).testBit x && walk g u b x xs

private theorem parity {g : Rows} {u b : ℕ} {c : ℕ → ℕ} (hc : Coloring g 2 u c)
    (hb : u.testBit b) (xs : List ℕ) (a : ℕ) (ha : u.testBit a) (h : walk g u b a xs) :
    c a = c b ↔ xs.length % 2 = 0 := by
  induction xs generalizing a with
  | nil => have he : a = b := beq_iff_eq.mp h; simp [he]
  | cons x xs ih =>
    simp only [walk, Bool.and_eq_true] at h
    obtain ⟨⟨hx, he⟩, ht⟩ := h
    have := ih x hx ht
    have := hc.proper a x ha hx he
    have := hc.bound a ha
    have := hc.bound x hx
    have := hc.bound b hb
    simp only [List.length_cons]
    omega

structure OddWalk where
  vertices : ℕ
  start : ℕ
  rest : List ℕ

def checkOdd (g : Rows) (s : OddWalk) : Bool :=
  s.vertices.testBit s.start && s.rest.length % 2 == 1 && walk g s.vertices s.start s.start s.rest

theorem odd_sound {g : Rows} (s : OddWalk) (h : checkOdd g s) : Obstruction g 2 s.vertices := by
  simp only [checkOdd, Bool.and_eq_true, beq_iff_eq] at h
  intro c hc
  have := (parity hc h.1.1 _ _ h.1.1 h.2).mp rfl
  omega

/-- A split stores its vertex and the index of its right subtree. Its left subtree follows it. -/
def decode (words : Table) (vertices : ℕ) : ℕ → ℕ → Branch
  | 0, _ => .leaf 0
  | depth+1, index =>
    let word := words.get index
    if word % 2 = 0 then .leaf (word / 2) else
      .split ((word / 2) % vertices) (decode words vertices depth (index+1))
        (decode words vertices depth (word / 2 / vertices))

def Segment (g : Rows) (k : ℕ) (t : Table) (offset len : ℕ) : Prop :=
  ∀ i : Fin len, Obstruction g k (t.get (offset + i.val))

theorem Segment.join {g : Rows} {k : ℕ} {t : Table} {offset a b : ℕ}
    (l : Segment g k t offset a) (r : Segment g k t (offset+a) b) : Segment g k t offset (a+b) := by
  intro i
  by_cases hi : i.val < a
  · exact l ⟨i.val,hi⟩
  · have h := r ⟨i.val-a, by have := i.isLt; omega⟩
    simpa only [show offset+a+(i.val-a) = offset+i.val by omega] using h

theorem Segment.all {g : Rows} {k : ℕ} {t : Table} (h : Segment g k t 0 t.size) :
    ∀ j : Fin t.size, Obstruction g k (t.get j) := fun j => by simpa using h j

theorem not_colorable {V : Type*} {G : SimpleGraph V} {g : Rows} {k u n : ℕ}
    (s : Fin n → Triple G) (he : ∀ a b : Fin n, (g a).testBit b → Disjoint (s a).val (s b).val)
    (hu : u < 2^n) (h : Obstruction g k u) : ¬ Colorable G k := by
  rintro ⟨c, hc⟩
  let d (i : ℕ) := if hi : i < n then (c (s ⟨i,hi⟩)).val else 0
  have index {i : ℕ} (hi : u.testBit i) : i < n := by
    by_contra! hle
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hle
    have := Nat.ge_two_pow_of_testBit hi
    omega
  apply h d
  constructor
  · intro i hi
    simp [d, index hi]
  · intro i j hi hj hij eq
    apply hc _ _ (he ⟨i,index hi⟩ ⟨j,index hj⟩ hij)
    exact Fin.ext (by simpa [d, index hi, index hj] using eq)

end StableKneserK3.MaskCertificate

