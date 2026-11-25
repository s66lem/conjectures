import Conjectures.StableKneserK3.PackedWeights

namespace StableKneserK3.WeightCertificate

open Finset PackedWeights

def both (a b : ℕ) := a &&& b
def three (a b c : ℕ) := (a &&& b) &&& c
def majority (a b c : ℕ) := (a &&& b) ||| ((a &&& c) ||| (b &&& c))
def fork (a b c : ℕ) := b &&& (a ||| c)
def exceptional (a b c x : ℕ) := three a b c ||| (x &&& (a ||| (b ||| c)))

variable {V : Type*} [DecidableEq V] [Fintype V]

instance (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Decidable (StableTriple G s) := by
  unfold StableTriple
  infer_instance

/-- Numerical conditions on the packed columns for the four possible links. -/
structure Tests (G : SimpleGraph V) (star : V → ℕ) (D M B : ℕ) : Prop where
  small : 10*M ≤ B
  pair : ∀ a b, a ≠ b → both (star a) (star b) % D + 6*M ≤ B
  member : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → three (star a) (star b) (star c) % D ≤ M
  majority : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → majority (star a) (star b) (star c) % D ≤ B
  fork : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → fork (star a) (star b) (star c) % D + 3*M ≤ B
  exceptional : ∀ a b c x, a ≠ b → a ≠ c → b ≠ c → x ≠ a → x ≠ b → x ≠ c →
    ¬G.Adj a b → ¬G.Adj a c → ¬G.Adj b c → exceptional (star a) (star b) (star c) (star x) % D ≤ B

omit [Fintype V] in
private theorem triple_equiv {s : Finset V} (hs : s.card = 3) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a ∈ s ∧ b ∈ s) ∧ c ∈ s ↔ s = {a,b,c} := by
  constructor
  · rintro ⟨⟨ha,hb⟩,hc⟩
    have hsub : {a,b,c} ⊆ s := by simp [insert_subset_iff, ha, hb, hc]
    exact (eq_of_subset_of_card_le hsub (by simp [hs, hab, hac, hbc])).symm
  · rintro rfl; simp

theorem has_star {G : SimpleGraph V} [DecidableRel G.Adj] {q width M B : ℕ}
    {samples : List (Finset V × ℕ)} {star : V → ℕ}
    (hn : 4 ≤ Fintype.card V) (ht : ∀ e ∈ samples, StableTriple G e.1)
    (digit : ∀ e ∈ samples, e.2 < 2^width)
    (col : ∀ x, pack width (fun s : Finset V => decide (x ∈ s)) samples = star x)
    (hmass : mass (fun _ => true) samples < 2^width-1)
    (over : q*B < mass (fun _ => true) samples) (test : Tests G star (2^width-1) M B)
    (c : Triple G → Fin q) (hc : IsProperColoring G q c) :
    ∃ i x, ∀ s, c s = i → x ∈ s.val := by
  classical
  let T := stableTriples G
  let w := assign samples
  have hT (e) (he : e ∈ samples) : e.1 ∈ T := (mem_stableTriples G).mpr (ht e he)
  let R := Represents width samples
  have point (x : V) : R (fun s => x ∈ s) (star x) :=
    ⟨_,col x, fun _ _ => by simp⟩
  have triple (a b d : V) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
      R (fun s => s = {a,b,d}) (three (star a) (star b) (star d)) :=
    (((point a).and (point b) digit).and (point d) digit).congr
      (fun e he => triple_equiv (ht e he).1 hab had hbd)
  have calcWeight (p : Finset V → Prop) [DecidablePred p] (v : ℕ) (hp : R p v) :
      weight w (T.filter p) = v % (2^width-1) := hp.weight_filter T hT hmass
  have everything : weight w T = mass (fun _ => true) samples := by
    have rep : R (fun _ => True) (pack width (fun _ => true) samples) :=
      ⟨_,rfl,fun _ _ => by simp⟩
    simpa [eval _ _ _ hmass] using calcWeight _ _ rep
  apply weighted_coloring_has_star hn (w := w) (M := M) (B := B) ?_ (everything.symm ▸ over) c hc
  constructor
  · intro t h
    obtain ⟨a,b,d,hab,had,hbd,rfl⟩ := card_eq_three.mp ((mem_stableTriples G).mp h).1
    have hh := calcWeight _ _ (triple a b d hab had hbd)
    have heq : T.filter (fun s => s = {a,b,d}) = {{a,b,d}} := by
      ext s
      simp only [mem_filter, mem_singleton]
      exact ⟨And.right, fun eq => ⟨eq ▸ h, eq⟩⟩
    rw [heq] at hh
    simpa [weight] using hh.trans_le (test.member a b d hab had hbd)
  · exact test.small
  · intro t h x hx
    obtain ⟨a,b,d,hab,had,hbd,rfl⟩ := card_eq_three.mp ((mem_stableTriples G).mp h).1
    have hst := ((mem_stableTriples G).mp h).2
    have meet := (point a).or ((point b).or (point d) digit) digit
    have meet' : R (fun s => ¬Disjoint s {a,b,d}) (star a ||| (star b ||| star d)) := by
      apply meet.congr
      intro e _
      simp only [disjoint_insert_right, disjoint_singleton_right]
      tauto
    have hh := calcWeight _ _ ((triple a b d hab had hbd).or ((point x).and meet' digit) digit)
    simp only [mem_insert, mem_singleton, not_or] at hx
    exact hh.trans_le (test.exceptional a b d x hab had hbd hx.1 hx.2.1 hx.2.2
      (hst _ (by simp) _ (by simp)) (hst _ (by simp) _ (by simp)) (hst _ (by simp) _ (by simp)))
  · intro a b d hab had hbd
    exact (calcWeight _ _ (((point a).and (point b) digit).or
      (((point a).and (point d) digit).or ((point b).and (point d) digit) digit) digit)).trans_le
      (test.majority a b d hab had hbd)
  · intro a b d hab had hbd
    rw [calcWeight _ _ ((point b).and ((point a).or (point d) digit) digit)]
    exact test.fork a b d hab had hbd
  · intro a b hab
    rw [calcWeight _ _ ((point a).and (point b) digit)]
    exact test.pair a b hab

end StableKneserK3.WeightCertificate
