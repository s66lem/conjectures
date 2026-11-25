import Conjectures.StableKneserK3.Reduction
import Conjectures.StableKneserK3.Obstructions
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace StableKneserK3

open SimpleGraph

/-- The forbidden-subgraph formulation of the condition in Conjecture 1.3. -/
def Qualifies {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ x, G.degree x ≤ 2) ∧ ∀ m, 3 ≤ m → m ≤ 8 → m < Fintype.card V → IsEmpty (Copy (cycleGraph m) G)

theorem qualifies_subgraph {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : Qualifies G) (f : Copy H G) : Qualifies H := by
  refine ⟨fun x => (f.degree_le x).trans (h.1 _), fun m hm hshort hout =>
    ⟨fun t => (h.2 m hm hshort (hout.trans_le (Fintype.card_le_of_embedding f.toEmbedding))).false (f.comp t)⟩⟩

/-- Necessity at every order covered by the conjecture. -/
theorem qualifies_of_tight {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 7 ≤ Fintype.card V) (ht : K3Tight G) : Qualifies G := by
  constructor
  · intro x
    by_contra! h
    exact ht.1 (colorable_of_degree_ge_three G hn x h)
  · intro m hm hshort hout
    exact ⟨fun f => ht.1 (colorable_of_short_cycle G hn hm hshort hout f.toEmbedding
      (fun _ _ h => f.toHom.map_rel' h))⟩

private theorem triangle_free_of_qualifies {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hg : Qualifies G) (hn : 3 < Fintype.card V) :
    ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj a c := by
  intro a b c hab hbc hac
  apply (hg.2 3 (by decide) (by decide) hn).false
  let f : Fin 3 → V := ![a,b,c]
  have inj : Function.Injective f := by
    intro x y he
    fin_cases x <;> fin_cases y <;> simp_all [f,hab.ne,hac.ne,hbc.ne,Ne.symm hab.ne,Ne.symm hac.ne,Ne.symm hbc.ne]
  refine ⟨⟨f,?_⟩,inj⟩
  intro x y h
  rw [cycleGraph_three_eq_top] at h
  fin_cases x <;> fin_cases y <;>
    first | exact hab | exact hbc | exact hac | exact hab.symm | exact hbc.symm | exact hac.symm | exact (h rfl).elim

/-- The full equivalence follows from sufficiency on labelled graphs of orders seven to nineteen. -/
theorem tight_iff_qualifies_of_finite
    (hbase : ∀ n, 7 ≤ n → n ≤ 19 → ∀ H : SimpleGraph (Fin n), ∀ [DecidableRel H.Adj],
      Qualifies H → K3Tight H)
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 7 ≤ Fintype.card V) :
    K3Tight G ↔ Qualifies G := by
  classical
  refine ⟨qualifies_of_tight G hn, ?_⟩
  intro hg
  induction he : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hsmall : n ≤ 19
    · let e := Fintype.equivFinOfCardEq he
      let H := G.comap e.symm
      let f : Copy H G := ⟨⟨e.symm,fun h => h⟩,e.symm.injective⟩
      have hH := hbase n (by omega) hsmall H (qualifies_subgraph hg f)
      exact tight_of_subgraph e.toEmbedding (G := H) (H := G) (fun x y h => by
        change G.Adj (e.symm (e x)) (e.symm (e y)); simpa using h) (by omega) hH
    by_contra hbad
    have hdel (x : V) : K3Tight (G.induce {v | v ≠ x}) := by
      let W := {v : V // v ≠ x}
      have hw : Fintype.card W = n-1 := by simp [W,he]
      apply ih (n-1) (by omega) (G.induce {v | v ≠ x}) (by change 7 ≤ Fintype.card W; omega)
        (qualifies_subgraph hg (Copy.induce G _)) hw
    have := minimal_failure_order_le_nineteen hg.1 (triangle_free_of_qualifies G hg (by omega)) hbad hdel
    omega

end StableKneserK3

