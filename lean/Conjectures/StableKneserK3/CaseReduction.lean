import Conjectures.StableKneserK3.Normalize

namespace StableKneserK3

open SimpleGraph

abbrev StarForced {V : Type*} (G : SimpleGraph V) (q : ℕ) :=
  ∀ c : Triple G → Fin q, IsProperColoring G q c → ∃ i x, ∀ s, c s = i → x ∈ s.val

/-- If every deletion is tight, a star class precludes a deficient coloring. -/
theorem tight_of_forced_star {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hn : 6 ≤ Fintype.card V) (hf : StarForced G (Fintype.card V-5))
    (hd : ∀ v, K3Tight (G.induce {x | x ≠ v})) : K3Tight G := by
  refine ⟨?_,upper_bound G (by omega)⟩
  rintro ⟨c,hc⟩
  obtain ⟨i,x,hx⟩ := hf c hc
  apply (hd x).1
  have h := delete_star_color c hc i x hx
  convert h using 1
  change Fintype.card {v : V // v ≠ x}-5 = Fintype.card V-5-1
  simp
  omega

private theorem cycle_image {n : ℕ} (hn : 3 ≤ n) {a b : Fin n}
    (h : a.val+1=b.val ∨ b.val+1=a.val ∨ a.val=0 ∧ b.val+1=n ∨ b.val=0 ∧ a.val+1=n) :
    (cycleGraph n).Adj a b := (cycle_adj_values (by omega)).mpr (by omega)

theorem tight_canonical {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (hn : Fintype.card V = n) (horder : 7 ≤ n) (hsmall : n ≤ 19)
    (cyclesTight : ∀ k ≥ 6, K3Tight (cycleGraph k))
    (one : ∀ m r, 9 ≤ m → 1 ≤ r → m+r=n → K3Tight (componentGraph n m r false))
    (two : ∀ m r, 9 ≤ m → 9 ≤ r → m+r≤n → K3Tight (componentGraph n m r true))
    (ms : List ℕ) (r : ℕ) (lengths : ms.sum+r=n)
    (long : ∀ m ∈ ms, 3 ≤ m ∧ (9 ≤ m ∨ m=n))
    (f : V ↪ Fin n) (edges : ∀ a b, G.Adj a b → CanonAdj ms r (f a).val (f b).val) :
    K3Tight G := by
  have transfer {H : SimpleGraph (Fin n)} (ht : K3Tight H)
      (h : ∀ a b, G.Adj a b → H.Adj (f a) (f b)) :=
    tight_of_subgraph (G := H) (H := G) f (fun _ _ he => h _ _ he) (by omega) ht
  cases ms with
  | nil =>
    apply transfer (cyclesTight n (by omega))
    intro a b h
    have := (edges a b h).2.2
    apply cycle_image (by omega)
    tauto
  | cons m ms =>
    have hm := long m List.mem_cons_self
    cases ms with
    | nil =>
      simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at lengths
      by_cases hz : r=0
      · apply transfer (cyclesTight n (by omega))
        intro a b h
        rcases edges a b h with ⟨_,_,he⟩ | ⟨_,_,he⟩
        · exact cycle_image (by omega) (by omega)
        · have := he.1; omega
      · apply transfer (one m r (by omega) (by omega) lengths)
        intro a b h
        refine ⟨fun eq => h.ne (f.injective eq),?_⟩
        rcases edges a b h with ⟨ha,hb,he⟩ | ⟨ha,hb,ha',hb',he⟩
        · exact Or.inl ⟨ha,hb,he⟩
        · right; refine ⟨ha,hb,?_,?_,?_⟩ <;> omega
    | cons k ks =>
      have hk := long k (by simp)
      have empty : ks = [] := by
        cases ks with
        | nil => rfl
        | cons j js =>
          have hj := long j (by simp)
          simp only [List.sum_cons] at lengths
          omega
      subst ks
      simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at lengths
      apply transfer (two m k (by omega) (by omega) (by omega))
      intro a b h
      refine ⟨fun eq => h.ne (f.injective eq),?_⟩
      rcases edges a b h with ⟨ha,hb,he⟩ | ⟨ha,hb,hrest⟩
      · exact Or.inl ⟨ha,hb,he⟩
      rcases hrest with ⟨ha',hb',he⟩ | ⟨ha',hb',ha'',hb'',he⟩
      · right
        refine ⟨ha,hb,by omega,by omega,?_⟩
        rcases he with he | he | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨by omega,by omega⟩⟩)
        · exact Or.inr (Or.inr ⟨rfl, Or.inr ⟨by omega,by omega⟩⟩)
      · omega

end StableKneserK3
