# Audit Log — Proof of Easlick's Conjecture 1 (`arXiv:2610.40321v2`)

## 1. Source & Openness Verification (2026-11-25)

- **Primary source:** Terry Easlick, *Computer-assisted results for $n$-sided non-transitive dice taking face values in $[n]$*, `arXiv:2610.40321v2` (`math.CO`, updated 2026-11-19).
- **Statement check:** Definitions 1–2, Equations (1)–(5), Theorem 1 ($n \le 6$), Examplemmas 1–2 ($7 \le n \le 12$), and Conjecture 1 were inspected directly in the primary arXiv v2 HTML/PDF source.
- **Openness check:** Verified via arXiv API and web search on 2026-11-25 that no later version or follow-up paper resolves Conjecture 1.

## 2. Independent Cross-Model Adversarial Audit

- **Auditor:** Claude Sonnet 5.5 (`claude-sonnet-5-5`, read-only audit of `EaslickNontransitiveDice.lean`, `PROOF.md`, `README.md`, `verify.py`, `paper.tex`, and primary arXiv v2 PDF text).
- **Verdict:** **PASS** (zero mathematical or Lean soundness issues).
- **Checks independently confirmed by auditor:**
  - `Die n`, `wins` (`wins_eq_card_pairs`), `minAdvTarget n = n^2 / 2 + 1`, `MinAdvEdge`, and `IsMinAdvCycle` match Easlick's Definitions 1–2 and Equations (1)–(5).
  - Hand-recomputed all win-count formulas for the odd family ($T = 2k^2 + 2k + 1$), even family ($T = 2k^2 + 1$), and $n = 14$ 7-base zipper ($T = 99$), plus distinctness, range bounds, and length inequalities $3(n-7) \ge n+1$ ($n \ge 11$) and $3(n-10) \ge n+1$ ($n \ge 16$).
  - Confirmed zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `unsafe`/`implemented_by`/`opaque` in Lean code.
  - Confirmed `python -O -W error results/easlick-nontransitive-dice/verify.py` exits 0 with all 4 checks passing (no `assert` statements).
- **Polish items addressed post-audit:**
  1. Rewrote the $W(C(z), A(x))$ decomposition in `PROOF.md` and `paper.tex` row-by-row as $1\cdot(k-1) + (k-2)(k-1) + k\cdot k + (2k-1) = 2k^2$.
  2. Tightened scope statements in `EaslickNontransitiveDice.lean`, `PROOF.md`, `README.md`, and `paper.tex` to state explicitly that Lean 4 proves the full $n \ge 7$ theorem, `n6_has_cycle_6`, and `flipDie_antiautomorphism`, while the $n \le 6$ upper bounds are Easlick's Theorem 1 (re-verified exhaustively in `verify.py`).
  3. Replaced "Equivalently" in `PROOF.md` with the implication from $n \ge 7$ cycles of length $\ge n + 1$ to Conjecture 1, and removed an informal factoring remark in the $n = 14$ paragraph.

## 3. Lean 4 Build & Axiom Verification (`v4.33.1` + Mathlib `v4.33.1`)

- `lake build Conjectures.EaslickNontransitiveDice` — **PASSED** (zero warnings, zero errors).
- `lake env lean Conjectures.lean` — **PASSED** (`ALL24=0`).
- `#print axioms` output:
  - `EaslickNontransitiveDice.wins_eq_card_pairs` : `[propext, Classical.choice, Quot.sound]`
  - `EaslickNontransitiveDice.minAdvTarget_gt_half` : `[propext, Quot.sound]`
  - `EaslickNontransitiveDice.minAdvTarget_le_of_gt_half` : `[propext, Quot.sound]`
  - `EaslickNontransitiveDice.flipDie_involutive` : `[propext, Classical.choice, Quot.sound]`
  - `EaslickNontransitiveDice.flipDie_antiautomorphism` : `[propext, Classical.choice, Quot.sound]`
  - `EaslickNontransitiveDice.odd_cycle_exists` : `[propext, Classical.choice, Quot.sound]`
  - `EaslickNontransitiveDice.even_cycle_exists` : `[propext, Classical.choice, Quot.sound]`
  - `EaslickNontransitiveDice.n6_has_cycle_6` : `[propext, Classical.choice, Quot.sound]`
  - `EaslickNontransitiveDice.easlick_conjecture1` : `[propext, Classical.choice, Quot.sound]`

## 4. Python Reproduction

- `python -O -W error results/easlick-nontransitive-dice/verify.py`:
  - Check 1: Exhaustive $G_3$–$G_6$ (10/3, 35/67, 126/620, 462/5491; two 7-vertex, 10-edge SCCs in $G_6$ with max cycle length 6; global antiautomorphism).
  - Check 2: Explicit simple cycles of length $n + 1$ for $n \in \{7, 8, 9, 10, 12, 14\}$.
  - Check 3: Odd 3-die zipper family for all 46 odd $n \in [11, 101]$ (length $3(n - 7)$).
  - Check 4: Even 3-die zipper family for all 43 even $n \in [16, 100]$ (length $3(n - 10)$).
  - Exited 0 in `1.723s`.
