import Conjectures.StableKneserK3.Cycles
import Conjectures.StableKneserK3.FiniteReduction

namespace StableKneserK3

open SimpleGraph Finset

structure Block where
  size : ℕ
  closed : Bool
  positive : 0 < size
  cycle_size : closed = true → 3 ≤ size

def blockOrder : List Block → ℕ
  | [] => 0
  | b :: bs => b.size + blockOrder bs

def LayoutAdj : List Block → ℕ → ℕ → Prop
  | [], _, _ => False
  | b :: bs, a, c =>
    a < b.size ∧ c < b.size ∧
      (a+1=c ∨ c+1=a ∨ b.closed ∧ (a=0 ∧ c+1=b.size ∨ c=0 ∧ a+1=b.size)) ∨
    b.size ≤ a ∧ b.size ≤ c ∧ LayoutAdj bs (a-b.size) (c-b.size)

def LongBlocks (n : ℕ) (bs : List Block) :=
  ∀ b ∈ bs, b.closed = true → 9 ≤ b.size ∨ b.size = n

private theorem saturated {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {x a b y : V} (hdeg : G.degree x ≤ 2) (ha : G.Adj x a) (hb : G.Adj x b) (hab : a ≠ b)
    (hy : G.Adj x y) : y = a ∨ y = b := by
  classical
  by_contra! h
  have sub : {y,a,b} ⊆ G.neighborFinset x := by
    simp [Finset.insert_subset_iff, ha, hb, hy]
  have hh := Finset.card_le_card sub
  simp [h.1,h.2,hab] at hh
  omega

private theorem block_step {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hg : Qualifies G) [Nonempty V] : ∃ b : Block, ∃ f : Fin b.size ↪ V,
    (b.closed = true → Nonempty (Copy (cycleGraph b.size) G)) ∧
    (∀ i j : Fin b.size, G.Adj (f i) (f j) →
      i.val+1=j.val ∨ j.val+1=i.val ∨ b.closed ∧
        (i.val=0 ∧ j.val+1=b.size ∨ j.val=0 ∧ i.val+1=b.size)) ∧
    ∀ i y, G.Adj (f i) y → y ∈ Set.range f := by
  classical
  obtain ⟨a,z,p,hp,maximal⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  let L := p.length+1
  let f : Fin L ↪ V := ⟨fun i => p.getVert i.val, fun i j h => Fin.ext
    (hp.getVert_injOn (show i.val ≤ p.length by have := i.isLt; dsimp [L] at this; omega)
      (show j.val ≤ p.length by have := j.isLt; dsimp [L] at this; omega) h)⟩
  let first : Fin L := ⟨0,by simp [L]⟩
  let last : Fin L := ⟨p.length,by simp [L]⟩
  have hfirst : f first = a := p.getVert_zero
  have hlast : f last = z := p.getVert_length
  have in_range (y) (hy : y ∈ p.support) : y ∈ Set.range f := by
    obtain ⟨i,hi,hlen⟩ := Walk.mem_support_iff_exists_getVert.mp hy
    exact ⟨⟨i,by dsimp [L]; omega⟩,hi⟩
  have consecutive {i j : Fin L} (he : i.val+1 = j.val) : G.Adj (f i) (f j) := by
    change G.Adj (p.getVert i.val) (p.getVert j.val)
    rw [← he]
    apply p.adj_getVert_succ
    have := j.isLt
    dsimp [L] at this; omega
  have middle {i : Fin L} (h₁ : 0 < i.val) (h₂ : i.val < p.length) {y : V} (hy : G.Adj (f i) y) :
      ∃ j, y = f j ∧ (j.val+1=i.val ∨ i.val+1=j.val) := by
    let l : Fin L := ⟨i.val-1,by omega⟩
    let r : Fin L := ⟨i.val+1,by dsimp [L]; omega⟩
    have hl : l.val+1=i.val := by dsimp [l]; omega
    have hr : i.val+1=r.val := rfl
    have hne : f l ≠ f r := fun e => by have := congrArg Fin.val (f.injective e); dsimp [l,r] at this; omega
    rcases saturated G (hg.1 _) (consecutive hl).symm (consecutive hr) hne hy with h | h
    · exact ⟨l,h,Or.inl hl⟩
    · exact ⟨r,h,Or.inr hr⟩
  let b : Block := ⟨L,decide (3 ≤ L ∧ G.Adj a z),by simp [L],fun h => (of_decide_eq_true h).1⟩
  have indices (i j : Fin L) (h : G.Adj (f i) (f j)) :
      i.val+1=j.val ∨ j.val+1=i.val ∨ b.closed ∧
        (i.val=0 ∧ j.val+1=L ∨ j.val=0 ∧ i.val+1=L) := by
    have mid {x y : Fin L} (hx : 0 < x.val ∧ x.val < p.length) (he : G.Adj (f x) (f y)) :
        y.val+1=x.val ∨ x.val+1=y.val := by
      obtain ⟨j,eq,hj⟩ := middle hx.1 hx.2 he
      rwa [← f.injective eq] at hj
    by_cases hi : 0 < i.val ∧ i.val < p.length
    · exact (mid hi h).symm.imp_right Or.inl
    by_cases hj : 0 < j.val ∧ j.val < p.length
    · exact (mid hj h.symm).imp_right Or.inl
    have hne : i.val ≠ j.val := fun e => h.ne (congrArg f (Fin.ext e))
    have ii := i.isLt
    have jj := j.isLt
    change i.val < p.length+1 at ii
    change j.val < p.length+1 at jj
    by_cases hs : 3 ≤ L
    · have endpoints : i = first ∧ j = last ∨ j = first ∧ i = last := by
        have eqs : i.val = 0 ∧ j.val = p.length ∨ j.val = 0 ∧ i.val = p.length := by omega
        rcases eqs with h | h <;> exact (by first | exact Or.inl ⟨Fin.ext h.1,Fin.ext h.2⟩ | exact Or.inr ⟨Fin.ext h.1,Fin.ext h.2⟩)
      rcases endpoints with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rw [hfirst,hlast] at h
        exact Or.inr (Or.inr ⟨by simp [b,hs,h], Or.inl ⟨rfl,rfl⟩⟩)
      · rw [hfirst,hlast] at h
        exact Or.inr (Or.inr ⟨by simp [b,hs,h.symm], Or.inr ⟨rfl,rfl⟩⟩)
    · dsimp [L] at hs; omega
  refine ⟨b,f,?_,indices,?_⟩
  · intro hb
    have hc : 3 ≤ L ∧ G.Adj a z := by simpa [b] using hb
    refine ⟨⟨⟨f,?_⟩,f.injective⟩⟩
    intro i j he
    rcases (cycle_adj_values (by omega : 2 ≤ L)).mp he with h | h | ⟨hi,hj⟩ | ⟨hj,hi⟩
    · exact consecutive h
    · exact (consecutive h).symm
    · have hd : i = last := Fin.ext (by change i.val=p.length; dsimp [L] at hi; omega)
      have hz : j = first := Fin.ext hj
      simpa [hd,hz,hfirst,hlast] using hc.2.symm
    · have hd : j = last := Fin.ext (by change j.val=p.length; dsimp [L] at hj; omega)
      have hz : i = first := Fin.ext hi
      simpa [hd,hz,hfirst,hlast] using hc.2
  · intro i y hy
    by_cases h0 : i.val = 0
    · rw [show i = first from Fin.ext h0,hfirst] at hy
      apply in_range
      by_contra hbad
      have h := maximal _ _ (.cons hy.symm p) (hp.cons hbad)
      simp at h
    by_cases hl : i.val = p.length
    · rw [show i = last from Fin.ext hl,hlast] at hy
      apply in_range
      by_contra hbad
      have h := maximal _ _ (p.concat hy) (hp.concat hbad hy)
      simp at h
    have hi : i.val < p.length+1 := i.isLt
    obtain ⟨j,hj,_⟩ := middle (i := i) (by omega) (by omega) hy
    exact ⟨j,hj.symm⟩

theorem exists_layout {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ}
    (hn : Fintype.card V = n)
    (hdeg : ∀ x, G.degree x ≤ 2) (ambient : ℕ) (hle : n ≤ ambient)
    (hcycles : ∀ m, 3 ≤ m → m ≤ 8 → m < ambient → IsEmpty (Copy (cycleGraph m) G)) :
    ∃ bs, blockOrder bs = n ∧ LongBlocks ambient bs ∧
      ∃ f : V ↪ Fin n, ∀ x y, G.Adj x y → LayoutAdj bs (f x).val (f y).val := by
  classical
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases he : n=0
    · have hV : IsEmpty V := Fintype.card_eq_zero_iff.mp (hn.trans he)
      exact ⟨[],he.symm,by simp [LongBlocks],Function.Embedding.ofIsEmpty,fun x => isEmptyElim x⟩
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have hg : Qualifies G := ⟨hdeg,fun m hm hs hlt => hcycles m hm hs (by omega)⟩
    obtain ⟨b,f,hb,hadj,closed⟩ := block_step G hg
    let W := {v : V // v ∉ Set.range f}
    let H := G.induce {v | v ∉ Set.range f}
    have hw : Fintype.card W = n-b.size := by
      change Fintype.card {v : V // v ∉ Set.range f} = _
      rw [Fintype.card_subtype_compl, Fintype.card_range f, Fintype.card_fin, hn]
    have hbsize : b.size ≤ n := by simpa [hn] using Fintype.card_le_of_embedding f
    have hpos := b.positive
    let copyH : Copy H G := Copy.induce G _
    obtain ⟨bs,hs,good,g,edges⟩ := ih (n-b.size) (by omega) H hw
      (fun x => (copyH.degree_le x).trans (hdeg _)) (by omega)
      (fun m hm hshort hlt => ⟨fun copy => (hcycles m hm hshort hlt).false (copyH.comp copy)⟩)
    have hlong (hc : b.closed = true) : 9 ≤ b.size ∨ b.size = ambient := by
      by_contra! hh
      exact (hcycles _ (b.cycle_size hc) (by omega) (by omega)).false (hb hc).some
    let inv (v : V) (hv : v ∈ Set.range f) : Fin b.size := Classical.choose hv
    have right (v) (hv : v ∈ Set.range f) : f (inv v hv) = v := Classical.choose_spec hv
    let label (v : V) : Fin n := if hv : v ∈ Set.range f then ⟨(inv v hv).val,by
      have := (inv v hv).isLt; omega⟩ else ⟨b.size+(g ⟨v,hv⟩).val,by have := (g ⟨v,hv⟩).isLt; omega⟩
    have inj : Function.Injective label := by
      intro x y eq
      have ee := congrArg Fin.val eq
      dsimp only [label] at ee
      split at ee <;> split at ee
      · rename_i hx hy
        exact (right x hx).symm.trans ((congrArg f (Fin.ext ee)).trans (right y hy))
      · rename_i hx hy
        change (inv x hx).val = b.size+(g ⟨y,hy⟩).val at ee
        have := (inv x hx).isLt
        omega
      · rename_i hx hy
        change b.size+(g ⟨x,hx⟩).val = (inv y hy).val at ee
        have := (inv y hy).isLt
        omega
      · exact congrArg Subtype.val (g.injective (Fin.ext (Nat.add_left_cancel ee)))
    refine ⟨b::bs,by simp [blockOrder,hs,Nat.add_sub_of_le hbsize],?_,⟨label,inj⟩,?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hm
      · exact hlong
      · exact good u hm
    · intro x y hxy
      change LayoutAdj (b::bs) (label x).val (label y).val
      dsimp only [label, LayoutAdj]
      split <;> split
      · rename_i hx hy
        exact Or.inl ⟨(inv x hx).isLt,(inv y hy).isLt,hadj (inv x hx) (inv y hy)
          (by rw [right, right]; exact hxy)⟩
      · rename_i hx hy
        exact (hy (closed (inv x hx) y (by simpa [right] using hxy))).elim
      · rename_i hx hy
        exact (hx (closed (inv y hy) x (by simpa [right] using hxy.symm))).elim
      · rename_i hx hy
        exact Or.inr ⟨Nat.le_add_right ..,Nat.le_add_right ..,by simpa using edges ⟨x,hx⟩ ⟨y,hy⟩ hxy⟩

end StableKneserK3
