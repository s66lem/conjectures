import Conjectures.QuasisymmetricBruhat.Code
import Mathlib.Logic.Function.Iterate

/-!
# Reconstruction of an indexed forest from its code (Definition 2.4)

The forest with code `c` is built from right to left [NST, Prop. 4.2]: start from the bare
number line; for `i = n, n-1, …, 1`, join `cᵢ` times the piece whose leftmost leaf is `i` with
the piece immediately to its right.  `E F p` is the rightmost leaf of the final piece whose
leftmost leaf is `p`, and `endAt F i t` is the rightmost leaf of the piece at `i` after its
first `t` joins.

The vertex `(i, t)` (the `t`-th join at `i`) has leftmost leaf `ρ(i,t) = i`, left child `(i, t-1)`
(the leaf `i` if `t = 1`) and right child the final piece at `q = endAt F i (t-1) + 1`, whose
root is `(q, c_q)` (the leaf `q` if `c_q = 0`).
-/

namespace QuasisymmetricBruhat

open Function

lemma iterate_semiconj_on {f g φ : ℕ → ℕ} {a : ℕ} (h : ∀ e, a ≤ e → f (φ e) = φ (g e))
    (hg : ∀ e, a ≤ e → a ≤ g e) : ∀ n e, a ≤ e → f^[n] (φ e) = φ (g^[n] e) := by
  intro n
  induction n with
  | zero => intro e _; rfl
  | succ n ih =>
    intro e he
    rw [iterate_succ_apply, iterate_succ_apply, h e he, ih _ (hg e he)]

lemma iterate_congr_on {f g : ℕ → ℕ} {a : ℕ} (h : ∀ e, a ≤ e → f e = g e)
    (hg : ∀ e, a ≤ e → a ≤ g e) : ∀ n e, a ≤ e → f^[n] e = g^[n] e :=
  iterate_semiconj_on (φ := id) h hg

lemma le_iterate_of {g : ℕ → ℕ} (hg : ∀ e, e < g e) : ∀ n e, e + n ≤ g^[n] e := by
  intro n; induction n with
  | zero => intro e; simp
  | succ n ih => intro e; rw [iterate_succ_apply']; have := ih e; have := hg (g^[n] e); omega

/-- Right-to-left reconstruction on a raw code list. -/
def Eaux : List ℕ → ℕ → ℕ
  | [], p => p
  | a :: l, p => if p ≤ 1 then (fun e => Eaux l e + 1)^[a] 1 else Eaux l (p - 1) + 1

lemma le_Eaux (l : List ℕ) (p : ℕ) : p ≤ Eaux l p := by
  induction l generalizing p with
  | nil => simp [Eaux]
  | cons a l ih =>
    simp only [Eaux]
    split_ifs with h
    · have := le_iterate_of (g := fun e => Eaux l e + 1) (fun e => by have := ih e; omega) a 1
      omega
    · have := ih (p - 1); omega

lemma Eaux_char (l : List ℕ) (p : ℕ) (hp : 1 ≤ p) :
    Eaux l p = (fun e => Eaux l (e + 1))^[l.getD (p - 1) 0] p := by
  induction l generalizing p with
  | nil => simp [Eaux]
  | cons a l ih =>
    rcases Nat.lt_or_ge p 2 with h | h
    · obtain rfl : p = 1 := by omega
      have h1 : Eaux (a :: l) 1 = (fun e => Eaux l e + 1)^[a] 1 := by simp [Eaux]
      rw [h1]
      simp only [Nat.sub_self, List.getD_cons_zero]
      refine iterate_congr_on (a := 1) (fun e he => ?_)
        (fun e _ => le_trans (by omega) (le_Eaux _ _)) a 1 le_rfl
      show Eaux l e + 1 = Eaux (a :: l) (e + 1)
      simp only [Eaux, show ¬ e + 1 ≤ 1 by omega, if_false, Nat.add_sub_cancel]
    · have hp1 : p = (p - 1) + 1 := by omega
      simp only [Eaux, show ¬ p ≤ 1 by omega, if_false]
      rw [ih (p - 1) (by omega)]
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
      simp only [show m + 2 - 1 = m + 1 by omega, List.getD_cons_succ]
      symm
      refine iterate_semiconj_on (φ := fun e => e + 1) (a := 0) (fun e _ => ?_)
        (fun e _ => by omega) _ (m + 1) (by omega)
      simp only [show ¬ e + 1 + 1 ≤ 1 by omega, if_false, show e + 1 + 1 - 1 = e + 1 by omega]

namespace Forest

/-- Rightmost leaf of the final piece with leftmost leaf `p`. -/
def E (F : Forest) (p : ℕ) : ℕ := Eaux F.code p

/-- Rightmost leaf of the piece at `p` after `t` joins. -/
def endAt (F : Forest) (p t : ℕ) : ℕ := (fun e => F.E (e + 1))^[t] p

lemma le_E (F : Forest) (p : ℕ) : p ≤ F.E p := le_Eaux _ _

lemma le_endAt (F : Forest) (p t : ℕ) : p + t ≤ F.endAt p t :=
  le_iterate_of (fun e => by have := F.le_E (e + 1); omega) t p

lemma endAt_succ (F : Forest) (p t : ℕ) : F.endAt p (t + 1) = F.E (F.endAt p t + 1) := by
  simp only [endAt, iterate_succ_apply']

lemma E_eq (F : Forest) {p : ℕ} (hp : 1 ≤ p) : F.E p = F.endAt p (F.c p) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  simp only [E, endAt, c_succ]; rw [Eaux_char _ _ hp]; rfl

/-- `E` is the unique solution of its recursion above any threshold `a ≥ 1`. -/
lemma E_unique (F : Forest) (f : ℕ → ℕ) {a : ℕ} (ha : 1 ≤ a)
    (hf : ∀ p, a ≤ p → f p = (fun e => f (e + 1))^[F.c p] p) : ∀ p, a ≤ p → f p = F.E p := by
  have key : ∀ m p, F.len + 1 - p = m → a ≤ p → f p = F.E p := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro p hm hp
      rw [hf p hp, F.E_eq (by omega), endAt]
      refine iterate_congr_on (a := p) (fun e he => ?_) (fun e he => ?_) _ p le_rfl
      · by_cases hlt : F.len < e + 1
        · have h1 := hf (e + 1) (by omega)
          rw [F.c_eq_zero_of_lt hlt] at h1
          have h2 := F.E_eq (p := e + 1) (by omega)
          rw [F.c_eq_zero_of_lt hlt] at h2
          rw [h1, h2]; rfl
        · exact ih (F.len + 1 - (e + 1)) (by omega) (e + 1) rfl (by omega)
      · have := F.le_E (e + 1); omega
  exact fun p hp => key _ p rfl hp

lemma E_eq_self_of_c (F : Forest) {p : ℕ} (hp : 1 ≤ p) (h : F.c p = 0) : F.E p = p := by
  rw [F.E_eq hp, h]; rfl

/-! ### Relations between `G` and `ins j G` -/

section ins
variable {j : ℕ} (hj : 1 ≤ j) (G : Forest)
include hj

lemma E_ins_high : ∀ p, j + 2 ≤ p → (ins j G).E p = G.E (p - 1) + 1 := by
  have := (ins j G).E_unique (fun p => if j + 2 ≤ p then G.E (p - 1) + 1 else (ins j G).E p)
    (a := j + 2) (by omega) ?_
  · intro p hp; have := this p hp; simp only [hp, if_true] at this; exact this.symm
  intro p hp
  simp only [hp, if_true]
  rw [c_ins _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    G.E_eq (show 1 ≤ p - 1 by omega), endAt]
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  symm
  refine iterate_semiconj_on (φ := fun e => e + 1) (a := m) (fun e he => ?_)
    (fun e he => by have := G.le_E (e + 1); omega) _ m le_rfl
  simp only [show j + 2 ≤ e + 1 + 1 by omega, if_true]

lemma endAt_ins_high (p t : ℕ) (hp : j + 2 ≤ p) :
    (ins j G).endAt p t = G.endAt (p - 1) t + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  simp only [endAt, Nat.add_sub_cancel]
  refine iterate_semiconj_on (φ := fun e => e + 1) (a := m) (fun e he => ?_)
    (fun e he => by have := G.le_E (e + 1); omega) _ m le_rfl
  show (ins j G).E (e + 1 + 1) = G.E (e + 1) + 1
  rw [E_ins_high hj G _ (by omega)]; rfl

lemma E_ins_succ : (ins j G).E (j + 1) = j + 1 := by
  apply E_eq_self_of_c _ (by omega)
  rw [c_ins _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

lemma endAt_ins_mid (t : ℕ) : (ins j G).endAt j (t + 1) = G.endAt j t + 1 := by
  induction t with
  | zero => rw [endAt_succ]; simp only [endAt, iterate_zero, id]; exact E_ins_succ hj G
  | succ t ih =>
    rw [endAt_succ, ih, endAt_succ, E_ins_high hj G _ (by have := G.le_endAt j t; omega)]
    rfl

/-- The leaf map for positions below the inserted cherry. -/
def iota (j e : ℕ) : ℕ := if j ≤ e then e + 1 else e

omit hj in
lemma iota_of_lt {e : ℕ} (h : e < j) : iota j e = e := if_neg (by omega)

omit hj in
lemma iota_of_ge {e : ℕ} (h : j ≤ e) : iota j e = e + 1 := if_pos h

lemma E_ins_E (p : ℕ) (hp : 1 ≤ p) (hpj : p < j) : (ins j G).E p = iota j (G.E p) := by
  set f : ℕ → ℕ := fun p => if p < j then iota j (G.E p) else (ins j G).E p with hfdef
  have semi : ∀ e, 1 ≤ e → f (iota j e + 1) = iota j (G.E (e + 1)) := by
    intro e he
    rcases lt_trichotomy (e + 1) j with h | h | h
    · rw [iota_of_lt (by omega)]; simp only [hfdef, h, if_true]
    · rw [iota_of_lt (by omega)]; simp only [hfdef, h, lt_irrefl, if_false]
      subst h
      rw [(ins _ G).E_eq (by omega), c_ins _ _ _ (by omega), if_neg (by omega), if_pos rfl,
        endAt_ins_mid hj, ← G.E_eq (by omega), iota_of_ge (G.le_E _)]
    · rw [iota_of_ge (by omega)]; simp only [hfdef, show ¬ e + 1 + 1 < j by omega, if_false]
      rw [E_ins_high hj G _ (by omega), Nat.add_sub_cancel,
        iota_of_ge (by have := G.le_E (e + 1); omega)]
  have hf := (ins j G).E_unique f (a := 1) le_rfl ?_ p hp
  · simp only [hfdef, hpj, if_true] at hf; exact hf.symm
  intro p hp
  by_cases hpj : p < j
  · have hfp : f p = iota j (G.E p) := if_pos hpj
    rw [hfp, c_ins _ _ _ hp, if_pos hpj, G.E_eq hp, endAt]
    have key := iterate_semiconj_on (f := fun e => f (e + 1)) (g := fun e => G.E (e + 1))
      (φ := iota j) (a := 1) semi (fun e he => by have := G.le_E (e + 1); omega) (G.c p) p hp
    rw [iota_of_lt hpj] at key
    exact key.symm
  · have hfp : f p = (ins j G).E p := if_neg hpj
    rw [hfp, (ins j G).E_eq hp, endAt]
    refine iterate_congr_on (a := p) (fun e he => ?_) (fun e he => ?_) _ p le_rfl
    · show (ins j G).E (e + 1) = f (e + 1)
      exact (if_neg (by omega)).symm
    · show p ≤ f (e + 1)
      rw [show f (e + 1) = (ins j G).E (e + 1) from if_neg (by omega)]
      have := (ins j G).le_E (e + 1); omega

lemma endAt_ins_low (p t : ℕ) (hp : 1 ≤ p) (hpj : p < j) :
    (ins j G).endAt p t = iota j (G.endAt p t) := by
  have semi : ∀ e, 1 ≤ e → (ins j G).E (iota j e + 1) = iota j (G.E (e + 1)) := by
    intro e he
    rcases lt_trichotomy (e + 1) j with h | h | h
    · rw [iota_of_lt (by omega)]; exact E_ins_E hj G _ (by omega) h
    · rw [iota_of_lt (by omega)]; subst h
      rw [(ins _ G).E_eq (by omega), c_ins _ _ _ (by omega), if_neg (by omega), if_pos rfl,
        endAt_ins_mid hj, ← G.E_eq (by omega), iota_of_ge (G.le_E _)]
    · rw [iota_of_ge (by omega), E_ins_high hj G _ (by omega), Nat.add_sub_cancel,
        iota_of_ge (by have := G.le_E (e + 1); omega)]
  simp only [endAt]
  conv_lhs => rw [show p = iota j p from (iota_of_lt hpj).symm]
  exact iterate_semiconj_on (φ := iota j) (a := 1) semi
    (fun e he => by have := G.le_E (e + 1); omega) _ p hp

end ins

/-! ### Children -/

/-- Leftmost leaf `ρ(v)` of the vertex `v = (i, t)`. -/
def rho (v : ℕ × ℕ) : ℕ := v.1

/-- Left child of `v` if it is internal. -/
def lc (v : ℕ × ℕ) : Option (ℕ × ℕ) := if 2 ≤ v.2 then some (v.1, v.2 - 1) else none

/-- Right child of `v` if it is internal: the root of the final piece at
`q = endAt F i (t-1) + 1`. -/
def rc (F : Forest) (v : ℕ × ℕ) : Option (ℕ × ℕ) :=
  if 1 ≤ F.c (F.endAt v.1 (v.2 - 1) + 1) then
    some (F.endAt v.1 (v.2 - 1) + 1, F.c (F.endAt v.1 (v.2 - 1) + 1)) else none

lemma lc_mem {F : Forest} {v u : ℕ × ℕ} (hv : v ∈ F.IN) (h : lc v = some u) :
    u ∈ F.IN ∧ u.1 = v.1 := by
  unfold lc at h; split_ifs at h with h2
  cases h; rw [mem_IN] at hv ⊢
  refine ⟨⟨hv.1, by omega, ?_⟩, rfl⟩
  show v.2 - 1 ≤ F.c v.1; omega

lemma rc_mem {F : Forest} {v u : ℕ × ℕ} (h : F.rc v = some u) :
    u ∈ F.IN ∧ v.1 < u.1 := by
  unfold rc at h; split_ifs at h with h2
  cases h; rw [mem_IN]
  have := F.le_endAt v.1 (v.2 - 1)
  exact ⟨⟨by omega, h2, le_rfl⟩, by simp; omega⟩

/-- Common shape of `rc` after the right-child position is known. -/
lemma rc_of_endAt {F : Forest} {v : ℕ × ℕ} {e : ℕ} (h : F.endAt v.1 (v.2 - 1) = e) :
    F.rc v = if 1 ≤ F.c (e + 1) then some (e + 1, F.c (e + 1)) else none := by
  simp only [rc, h]

section ins
variable {j : ℕ} (hj : 1 ≤ j) (G : Forest)
include hj

lemma lc_ins (v : ℕ × ℕ) (hv : v ∈ G.IN) :
    lc (psi j v) = if v.1 = j ∧ v.2 = 1 then some (j, 1) else (lc v).map (psi j) := by
  obtain ⟨a, b⟩ := v
  obtain ⟨ha, hb, -⟩ := mem_IN.1 hv
  simp only at ha hb ⊢
  rcases lt_trichotomy a j with h | rfl | h
  · rw [show psi j (a, b) = (a, b) by simp [psi, h], if_neg (by omega)]
    unfold lc; split_ifs <;> simp [psi, h]
  · rw [show psi a (a, b) = (a, b + 1) by simp [psi]]
    by_cases hb1 : b = 1
    · subst hb1; rw [if_pos ⟨rfl, rfl⟩]; simp [lc]
    · rw [if_neg (by tauto)]; simp only [lc]
      rw [if_pos (by omega), if_pos (by omega)]; simp [psi]; omega
  · rw [show psi j (a, b) = (a + 1, b) by simp [psi, show ¬ a < j by omega,
      show a ≠ j by omega], if_neg (by omega)]
    unfold lc; split_ifs <;> simp [psi, show ¬ a < j by omega, show a ≠ j by omega]

lemma rc_ins_new : (ins j G).rc (j, 1) = none := by
  simp only [rc, Nat.sub_self, endAt, iterate_zero, id]
  rw [if_neg]; rw [c_ins _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  omega

lemma rc_ins (v : ℕ × ℕ) (hv : v ∈ G.IN) :
    (ins j G).rc (psi j v) =
      if v.1 < j ∧ G.endAt v.1 (v.2 - 1) + 1 = j ∧ G.c j = 0 then some (j, 1)
      else (G.rc v).map (psi j) := by
  obtain ⟨i, t⟩ := v
  obtain ⟨hi, ht, -⟩ := mem_IN.1 hv
  simp only at hi ht ⊢
  have hge := G.le_endAt i (t - 1)
  have hG := rc_of_endAt (F := G) (v := (i, t)) rfl
  simp only at hG
  set e' := G.endAt i (t - 1) with he'
  rw [hG]
  -- the case where the right child lies beyond the inserted cherry
  have high : ∀ e, j ≤ e → (ins j G).rc (psi j (i, t)) =
      (if 1 ≤ (ins j G).c (e + 1 + 1) then some (e + 1 + 1, (ins j G).c (e + 1 + 1)) else none) →
      e' = e →
      (ins j G).rc (psi j (i, t)) = Option.map (psi j)
        (if 1 ≤ G.c (e' + 1) then some (e' + 1, G.c (e' + 1)) else none) := by
    intro e hje hrc hee
    have hc : (ins j G).c (e + 1 + 1) = G.c (e + 1) := by
      rw [c_ins _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rfl
    rw [hrc, hc, hee]
    split_ifs <;> simp [psi, show ¬ e + 1 < j by omega, show e + 1 ≠ j by omega]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hpsi : psi j (i, t) = (i, t) := by simp [psi, hij]
    have hH := rc_of_endAt (F := ins j G) (v := (i, t))
      (endAt_ins_low hj G i (t - 1) hi hij)
    rw [← he'] at hH
    rcases lt_trichotomy (e' + 1) j with h | h | h
    · rw [if_neg (by omega), hpsi, hH, iota_of_lt (by omega), c_ins _ _ _ (by omega), if_pos h]
      split_ifs <;> simp [psi, h]
    · have hc : (ins j G).c j = G.c j + 1 := by
        rw [c_ins _ _ _ hj, if_neg (by omega), if_pos rfl]
      rw [hpsi, hH, iota_of_lt (by omega), h, hc, if_pos (by omega)]
      by_cases hc0 : G.c j = 0
      · rw [if_pos ⟨hij, rfl, hc0⟩, hc0]
      · rw [if_neg (by tauto), if_pos (show 1 ≤ G.c j by omega)]; simp [psi]
    · rw [if_neg (by omega)]
      refine high e' (by omega) ?_ rfl
      rw [hpsi, hH, iota_of_ge (by omega)]
  · have hpsi : psi i (i, t) = (i, t + 1) := by simp [psi]
    rw [if_neg (by omega)]
    refine high e' (by omega) ?_ rfl
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hH := rc_of_endAt (F := ins i G) (v := (i, s + 1 + 1)) (e := e' + 1)
      (by simp only [Nat.add_sub_cancel]; rw [endAt_ins_mid hj]; simp [he'])
    rw [hpsi, hH]
  · have hpsi : psi j (i, t) = (i + 1, t) := by
      simp [psi, show ¬ i < j by omega, show i ≠ j by omega]
    rw [if_neg (by omega)]
    refine high e' (by omega) ?_ rfl
    have hH := rc_of_endAt (F := ins j G) (v := (i + 1, t)) (e := e' + 1)
      (by simp only; rw [endAt_ins_high hj G _ _ (by omega), Nat.add_sub_cancel])
    rw [hpsi, hH]

end ins

end Forest

end QuasisymmetricBruhat
