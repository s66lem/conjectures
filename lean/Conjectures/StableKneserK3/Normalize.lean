import Conjectures.StableKneserK3.Layouts
import Conjectures.StableKneserK3.Components

namespace StableKneserK3

open SimpleGraph

def cycles : List Block → List ℕ
  | [] => []
  | b :: bs => if b.closed then b.size :: cycles bs else cycles bs

def paths : List Block → ℕ
  | [] => 0
  | b :: bs => if b.closed then paths bs else b.size + paths bs

private theorem lengths (bs : List Block) : (cycles bs).sum + paths bs = blockOrder bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases h : b.closed <;> simp [cycles,paths,blockOrder,h] <;> omega

def CanonAdj : List ℕ → ℕ → ℕ → ℕ → Prop
  | [], r, a, b => a < r ∧ b < r ∧ (a+1=b ∨ b+1=a)
  | m :: ms, r, a, b =>
    a < m ∧ b < m ∧ (a+1=b ∨ b+1=a ∨ a=0 ∧ b+1=m ∨ b=0 ∧ a+1=m) ∨
    m ≤ a ∧ m ≤ b ∧ CanonAdj ms r (a-m) (b-m)

private def shiftPath (s t a : ℕ) := if a < s then a else t+a

private theorem shift_path_edges (ms : List ℕ) (r t a b : ℕ) (h : CanonAdj ms r a b) :
    CanonAdj ms (t+r) (shiftPath ms.sum t a) (shiftPath ms.sum t b) := by
  induction ms generalizing a b with
  | nil => simp only [CanonAdj,List.sum_nil,shiftPath,Nat.not_lt_zero,if_false] at *; omega
  | cons m ms ih =>
    simp only [CanonAdj, List.sum_cons] at h ⊢
    rcases h with h | ⟨ha,hb,h⟩
    · simpa [shiftPath,show a < m+ms.sum by omega,show b < m+ms.sum by omega] using Or.inl h
    · have eq (x : ℕ) (hx : m ≤ x) :
          shiftPath (m+ms.sum) t x-m = shiftPath ms.sum t (x-m) := by
        simp only [shiftPath]; split <;> split <;> omega
      refine Or.inr ⟨?_,?_,?_⟩
      · simp only [shiftPath]; split <;> omega
      · simp only [shiftPath]; split <;> omega
      · rw [eq a ha,eq b hb]
        exact ih _ _ h

private theorem path_edges (ms : List ℕ) (r a b : ℕ) (ha : a < r) (hb : b < r)
    (he : a+1=b ∨ b+1=a) : CanonAdj ms r (ms.sum+a) (ms.sum+b) := by
  induction ms with
  | nil => simpa [CanonAdj] using And.intro ha (And.intro hb he)
  | cons m ms ih =>
    simp only [CanonAdj,List.sum_cons]
    refine Or.inr ⟨by omega,by omega,?_⟩
    simpa [Nat.add_assoc] using ih

def normalize : List Block → ℕ → ℕ
  | [], i => i
  | b :: bs, i =>
    if i < b.size then if b.closed then i else (cycles bs).sum+i else
      let j := normalize bs (i-b.size)
      if b.closed then b.size+j else shiftPath (cycles bs).sum b.size j

private theorem normalize_lt (bs : List Block) {i : ℕ} (hi : i < blockOrder bs) :
    normalize bs i < blockOrder bs := by
  induction bs generalizing i with
  | nil => exact hi
  | cons b bs ih =>
    simp only [blockOrder,normalize] at *
    have hl := lengths bs
    split
    · split <;> omega
    · rename_i outside
      have := ih (i := i-b.size) (by omega)
      split
      · omega
      · unfold shiftPath; split <;> omega

private theorem normalize_inj (bs : List Block) {i j : ℕ} (hi : i < blockOrder bs)
    (hj : j < blockOrder bs) (he : normalize bs i = normalize bs j) : i=j := by
  induction bs generalizing i j with
  | nil => exact he
  | cons b bs ih =>
    simp only [normalize,blockOrder] at hi hj he
    have subeq {i j} (hi : ¬i < b.size) (hj : ¬j < b.size) (h₁ : i-b.size < blockOrder bs)
        (h₂ : j-b.size < blockOrder bs) (eq : normalize bs (i-b.size) = normalize bs (j-b.size)) : i=j := by
      have := ih h₁ h₂ eq; omega
    cases hc : b.closed <;> simp [hc,shiftPath] at he <;>
      split_ifs at he <;> first | omega | exact subeq (by omega) (by omega) (by omega) (by omega) (by omega)

private theorem normalize_edges (bs : List Block) {i j : ℕ} (he : LayoutAdj bs i j) :
    CanonAdj (cycles bs) (paths bs) (normalize bs i) (normalize bs j) := by
  induction bs generalizing i j with
  | nil => contradiction
  | cons b bs ih =>
    rcases he with ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩
    · cases hc : b.closed
      · simp only [normalize,cycles,paths,hc,hi,hj,if_true,Bool.false_eq_true,if_false]
        apply path_edges (ha := by omega) (hb := by omega)
        simpa [hc] using he
      · simp only [normalize,cycles,paths,hc,hi,hj,if_true,CanonAdj]
        exact Or.inl ⟨trivial,trivial,by simpa [hc] using he⟩
    · have h := ih he
      cases hc : b.closed <;> simp only [normalize,cycles,paths,hc,if_true,Bool.false_eq_true,
        if_false,Nat.not_lt.mpr hi,Nat.not_lt.mpr hj,CanonAdj]
      · exact shift_path_edges _ _ _ _ _ h
      · exact Or.inr ⟨by omega,by omega,by simpa using h⟩

theorem canonical_layout {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hg : Qualifies G) {n : ℕ} (hn : Fintype.card V = n) :
    ∃ ms r, ms.sum+r=n ∧ (∀ m ∈ ms, 3 ≤ m ∧ (9 ≤ m ∨ m = n)) ∧
      ∃ f : V ↪ Fin n, ∀ x y, G.Adj x y → CanonAdj ms r (f x).val (f y).val := by
  obtain ⟨bs,hb,hl,g,he⟩ := exists_layout G hn hg.1 n le_rfl (by simpa [hn] using hg.2)
  refine ⟨cycles bs,paths bs,(lengths bs).trans hb,?_,?_,?_⟩
  · intro m hm
    have hmem : ∃ b ∈ bs, b.closed = true ∧ b.size=m := by
      clear hl hb g he
      induction bs with
      | nil => contradiction
      | cons b bs ih =>
        cases hc : b.closed <;> simp only [cycles,hc,if_true,Bool.false_eq_true,if_false,List.mem_cons] at hm
        · obtain ⟨a,ha,h⟩ := ih hm
          exact ⟨a,List.mem_cons_of_mem _ ha,h⟩
        · rcases hm with rfl | hm
          · exact ⟨b,List.mem_cons_self,hc,rfl⟩
          · obtain ⟨a,ha,h⟩ := ih hm
            exact ⟨a,List.mem_cons_of_mem _ ha,h⟩
    obtain ⟨b,hb,hc,rfl⟩ := hmem
    exact ⟨b.cycle_size hc, hl b hb hc⟩
  · exact ⟨fun v => ⟨normalize bs (g v).val,(normalize_lt bs (by simp [hb])).trans_eq hb⟩,
      fun x y eq => g.injective (Fin.ext (normalize_inj _ (by simp [hb]) (by simp [hb]) (congrArg Fin.val eq)))⟩
  · exact fun x y h => normalize_edges bs (he x y h)

end StableKneserK3
