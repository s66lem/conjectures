import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Basic

/-!
# Disproof of Talmage's Monotonicity Conjecture for Muñiz's List Reversal (`arXiv:2611.25115v1`)

Reference: Alan Talmage, "A Density Bound for Muñiz's List Reversal",
arXiv:2611.25115v1 [math.CO] (18 Nov 2026), Section "Discussion" (third bullet of open problems)
and Appendix A ("Known Irreversible Lists").

Verbatim conjecture (Discussion):
> "The irreversible lists found by computer search in [Appendix A] suggest a conjecture that
> reversibility is monotonic in `n`, in the sense that replacing the maximum value `n` in an
> irreversible list with `n + 1` (leaving the rest of the list unchanged) must yield an
> irreversible list. No counterexamples to the conjecture are presently known, but it is not clear
> if that is an artifact of only having data on short lists."

We disprove **both** readings of monotonicity in `n`:
1. **As stated** (`¬ Reversible L → ¬ Reversible (bumpMax L)`):
   `[2, 6]` is irreversible (its entire reachable component has 7 states and omits `[6, 2]`),
   whereas `[2, 7]` reverses in 4 legal moves.
2. **Converse reading** (`Reversible L → Reversible (bumpMax L)`):
   `[1, 3, 7, 4]` reverses in 18 legal moves, whereas `[1, 3, 8, 4]` is irreversible
   (its entire reachable component has 5 states and omits `[4, 8, 3, 1]`).
-/

namespace TalmageListReversal

/-- A list state is legal with upper bound `n` if its entries are pairwise distinct
and lie in `{1, ..., n}`. -/
def LegalState (n : ℕ) (L : List ℕ) : Prop :=
  L.Nodup ∧ ∀ x ∈ L, 1 ≤ x ∧ x ≤ n

instance (n : ℕ) (L : List ℕ) : Decidable (LegalState n L) :=
  inferInstanceAs (Decidable (L.Nodup ∧ ∀ x ∈ L, 1 ≤ x ∧ x ≤ n))

/-- Maximum entry of a list of natural numbers (`0` if empty). -/
def listMax (L : List ℕ) : ℕ := L.foldr max 0

/-- Replace every occurrence of the maximum value `n` in `L` with `n + 1`. -/
def bumpMax (L : List ℕ) : List ℕ :=
  let n := listMax L
  L.map fun x => if x = n then n + 1 else x

/-- One legal move in Muñiz's list reversal game with upper bound `n`:
either merge two adjacent entries into their sum, or split one entry into two adjacent
positive integers with the same sum, maintaining `LegalState n` at every step. -/
inductive Step (n : ℕ) : List ℕ → List ℕ → Prop
  | combine (p q : List ℕ) (a b : ℕ) :
      LegalState n (p ++ (a + b) :: q) →
      Step n (p ++ a :: b :: q) (p ++ (a + b) :: q)
  | split (p q : List ℕ) (a b : ℕ) :
      1 ≤ a → 1 ≤ b →
      LegalState n (p ++ a :: b :: q) →
      Step n (p ++ (a + b) :: q) (p ++ a :: b :: q)

/-- Multi-step reachability under `Step n`. -/
def Reachable (n : ℕ) : List ℕ → List ℕ → Prop :=
  Relation.ReflTransGen (Step n)

/-- A list `L` is reversible if `L.reverse` is reachable from `L` with upper bound `max L`. -/
def Reversible (L : List ℕ) : Prop :=
  Reachable (listMax L) L L.reverse

/-! ### Section 1: Sound & complete computable move enumerator -/

/-- Enumerate all legal single-step combine moves starting from `p ++ suffix`. -/
def combineAux (n : ℕ) : List ℕ → List ℕ → List (List ℕ)
  | p, a :: b :: rest =>
      (if decide (LegalState n (p ++ (a + b) :: rest)) then [p ++ (a + b) :: rest] else []) ++
        combineAux n (p ++ [a]) (b :: rest)
  | _, _ => []

/-- Enumerate all legal single-step split moves starting from `p ++ suffix`. -/
def splitAux (n : ℕ) : List ℕ → List ℕ → List (List ℕ)
  | p, x :: rest =>
      ((List.range x).filterMap fun a =>
        if 1 ≤ a ∧ a < x ∧ decide (LegalState n (p ++ a :: (x - a) :: rest)) then
          some (p ++ a :: (x - a) :: rest)
        else none) ++
      splitAux n (p ++ [x]) rest
  | _, [] => []

/-- All lists reachable in one legal move from `s` with bound `n`. -/
def nextStates (n : ℕ) (s : List ℕ) : List (List ℕ) :=
  combineAux n [] s ++ splitAux n [] s

private lemma mem_combineAux {n : ℕ} :
    ∀ (p' p q : List ℕ) (a b : ℕ),
      LegalState n (p ++ p' ++ (a + b) :: q) →
      (p ++ p' ++ (a + b) :: q) ∈ combineAux n p (p' ++ a :: b :: q)
  | [], p, q, a, b, hleg => by
      simp only [List.append_nil, List.nil_append] at hleg ⊢
      simp only [combineAux, List.mem_append]
      left
      simp [hleg]
  | c :: rest, p, q, a, b, hleg => by
      have hsub := mem_combineAux rest (p ++ [c]) q a b (by simpa [List.append_assoc] using hleg)
      cases hrest : rest ++ a :: b :: q with
      | nil =>
          exfalso
          have := congrArg List.length hrest
          simp at this
      | cons d tail =>
          simp only [List.cons_append]
          rw [hrest, combineAux, List.mem_append]
          right
          rw [← hrest]
          simpa [List.append_assoc] using hsub

private lemma mem_splitAux {n : ℕ} :
    ∀ (p' p q : List ℕ) (a b : ℕ),
      1 ≤ a → 1 ≤ b →
      LegalState n (p ++ p' ++ a :: b :: q) →
      (p ++ p' ++ a :: b :: q) ∈ splitAux n p (p' ++ (a + b) :: q)
  | [], p, q, a, b, ha, hb, hleg => by
      simp only [List.append_nil, List.nil_append] at hleg ⊢
      simp only [splitAux, List.mem_append, List.mem_filterMap]
      left
      refine ⟨a, List.mem_range.mpr (by omega), ?_⟩
      have hsub : a + b - a = b := by omega
      have hlt : a < a + b := by omega
      simp [ha, hlt, hsub, hleg]
  | c :: rest, p, q, a, b, ha, hb, hleg => by
      simp only [List.cons_append, splitAux, List.mem_append]
      right
      have hsub := mem_splitAux rest (p ++ [c]) q a b ha hb (by simpa [List.append_assoc] using hleg)
      simpa [List.append_assoc] using hsub

/-- Completeness of `nextStates`: every legal `Step n s t` appears in `nextStates n s`. -/
lemma mem_nextStates_of_step {n : ℕ} {s t : List ℕ} (h : Step n s t) :
    t ∈ nextStates n s := by
  cases h with
  | combine p q a b hleg =>
      unfold nextStates
      rw [List.mem_append]
      left
      simpa using mem_combineAux p [] q a b (by simpa using hleg)
  | split p q a b ha hb hleg =>
      unfold nextStates
      rw [List.mem_append]
      right
      simpa using mem_splitAux p [] q a b ha hb (by simpa using hleg)

/-- If a finite list `S` of states is closed under `nextStates n`, then every state
reachable from an element of `S` stays inside `S`. -/
lemma reachable_mem_of_closed {n : ℕ} {S : List (List ℕ)}
    (hclosed : ∀ s ∈ S, ∀ t ∈ nextStates n s, t ∈ S)
    {s t : List ℕ} (hs : s ∈ S) (hr : Reachable n s t) : t ∈ S := by
  induction hr with
  | refl => exact hs
  | tail _ hstep ih => exact hclosed _ ih _ (mem_nextStates_of_step hstep)

/-- Helper to verify a single combine move in a reversibility certificate. -/
private lemma step_combine {n : ℕ} (p q : List ℕ) (a b : ℕ)
    (hleg : LegalState n (p ++ (a + b) :: q) := by decide) :
    Step n (p ++ a :: b :: q) (p ++ (a + b) :: q) :=
  Step.combine p q a b hleg

/-- Helper to verify a single split move in a reversibility certificate. -/
private lemma step_split {n : ℕ} (p q : List ℕ) (a b : ℕ)
    (ha : 1 ≤ a := by decide) (hb : 1 ≤ b := by decide)
    (hleg : LegalState n (p ++ a :: b :: q) := by decide) :
    Step n (p ++ (a + b) :: q) (p ++ a :: b :: q) :=
  Step.split p q a b ha hb hleg

/-! ### Section 2: Counterexample 1 (stated direction: `[2, 6]` irreversible, `[2, 7]` reversible) -/

/-- The exact 7-state reachable component of `[2, 6]` under bound `6`. -/
def comp26 : List (List ℕ) :=
  [[2, 6], [2, 1, 5], [2, 5, 1], [3, 5], [1, 2, 5], [3, 1, 4], [3, 4, 1]]

private lemma comp26_closed : ∀ s ∈ comp26, ∀ t ∈ nextStates 6 s, t ∈ comp26 := by
  decide

/-- `[2, 6]` is irreversible (`n = 6`): its entire reachable component is `comp26`,
which does not contain `[6, 2]`. -/
theorem not_reversible_2_6 : ¬ Reversible [2, 6] := by
  intro hr
  have hmem : [6, 2] ∈ comp26 :=
    reachable_mem_of_closed comp26_closed (by decide : [2, 6] ∈ comp26) hr
  exact absurd hmem (by decide)

/-- `[2, 7] = bumpMax [2, 6]` is reversible in 4 legal moves (`n = 7`). -/
theorem reversible_2_7 : Reversible [2, 7] := by
  change Reachable 7 [2, 7] [7, 2]
  exact Relation.ReflTransGen.head (step_split [2] [] 1 6) <|
    Relation.ReflTransGen.head (step_combine [] [6] 2 1) <|
    Relation.ReflTransGen.head (step_split [3] [] 4 2) <|
    Relation.ReflTransGen.head (step_combine [] [2] 3 4) <|
    Relation.ReflTransGen.refl

/-! ### Section 3: Counterexample 2 (converse direction: `[1, 3, 7, 4]` reversible, `[1, 3, 8, 4]` irreversible) -/

/-- The exact 5-state reachable component of `[1, 3, 8, 4]` under bound `8`. -/
def comp1384 : List (List ℕ) :=
  [[1, 3, 8, 4], [1, 3, 2, 6, 4], [1, 3, 6, 2, 4], [1, 5, 6, 4], [1, 2, 3, 6, 4]]

private lemma comp1384_closed : ∀ s ∈ comp1384, ∀ t ∈ nextStates 8 s, t ∈ comp1384 := by
  decide

/-- `[1, 3, 8, 4]` is irreversible (`n = 8`): its entire reachable component is `comp1384`,
which does not contain `[4, 8, 3, 1]`. -/
theorem not_reversible_1_3_8_4 : ¬ Reversible [1, 3, 8, 4] := by
  intro hr
  have hmem : [4, 8, 3, 1] ∈ comp1384 :=
    reachable_mem_of_closed comp1384_closed (by decide : [1, 3, 8, 4] ∈ comp1384) hr
  exact absurd hmem (by decide)

/-- `[1, 3, 7, 4]` is reversible in 18 legal moves (`n = 7`). -/
theorem reversible_1_3_7_4 : Reversible [1, 3, 7, 4] := by
  change Reachable 7 [1, 3, 7, 4] [4, 7, 3, 1]
  exact Relation.ReflTransGen.head (step_split [1, 3] [4] 5 2) <|
    Relation.ReflTransGen.head (step_combine [1, 3, 5] [] 2 4) <|
    Relation.ReflTransGen.head (step_combine [] [5, 6] 1 3) <|
    Relation.ReflTransGen.head (step_split [] [5, 6] 3 1) <|
    Relation.ReflTransGen.head (step_split [3, 1, 5] [] 2 4) <|
    Relation.ReflTransGen.head (step_combine [3] [2, 4] 1 5) <|
    Relation.ReflTransGen.head (step_split [3] [2, 4] 5 1) <|
    Relation.ReflTransGen.head (step_combine [3, 5, 1] [] 2 4) <|
    Relation.ReflTransGen.head (step_combine [3, 5] [] 1 6) <|
    Relation.ReflTransGen.head (step_split [] [5, 7] 1 2) <|
    Relation.ReflTransGen.head (step_split [1, 2, 5] [] 3 4) <|
    Relation.ReflTransGen.head (step_combine [1] [3, 4] 2 5) <|
    Relation.ReflTransGen.head (step_split [1] [3, 4] 5 2) <|
    Relation.ReflTransGen.head (step_combine [] [2, 3, 4] 1 5) <|
    Relation.ReflTransGen.head (step_combine [6] [4] 2 3) <|
    Relation.ReflTransGen.head (step_split [6, 5] [] 3 1) <|
    Relation.ReflTransGen.head (step_split [] [5, 3, 1] 4 2) <|
    Relation.ReflTransGen.head (step_combine [4] [3, 1] 2 5) <|
    Relation.ReflTransGen.refl

/-! ### Section 4: Main Disproof Theorem -/

/-- **Main Theorem (Disproof of Talmage's monotonicity conjecture, arXiv:2611.25115v1):**
Reversibility under Muñiz's list reversal game is not monotonic in the maximum `n` in either direction:
1. There exists a legal list `L = [2, 6]` that is irreversible while `bumpMax L = [2, 7]` is reversible.
2. There exists a legal list `L = [1, 3, 7, 4]` that is reversible while `bumpMax L = [1, 3, 8, 4]` is irreversible. -/
theorem talmage_monotonicity_disproof :
    (∃ L : List ℕ, LegalState (listMax L) L ∧ ¬ Reversible L ∧ Reversible (bumpMax L)) ∧
    (∃ L : List ℕ, LegalState (listMax L) L ∧ Reversible L ∧ ¬ Reversible (bumpMax L)) := by
  refine ⟨⟨[2, 6], by decide, not_reversible_2_6, ?_⟩,
          ⟨[1, 3, 7, 4], by decide, reversible_1_3_7_4, ?_⟩⟩
  · exact reversible_2_7
  · exact not_reversible_1_3_8_4

end TalmageListReversal
