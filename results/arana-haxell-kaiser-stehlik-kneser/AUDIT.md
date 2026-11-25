# Verification & Audit Log — Arana–Haxell–Kaiser–Stehlík Conjecture 1.3 ($k = 3$)

## Source & Definition Audit

Checked verbatim against Carmen Arana, Penny Haxell, Tomáš Kaiser, and Matěj Stehlík, *The chromatic number of $G$-stable Kneser graphs* (`arXiv:2610.17884`, §§1–4):

- **$G$-stable Kneser graph $\mathrm{KG}(G, k)$:** Vertices are independent $k$-subsets of $V(G)$; two vertices are adjacent iff they are disjoint.
- **Upper bound and $k$-tightness (§1):** Every graph $G$ on $n \ge 2k - 1$ vertices satisfies $\chi(\mathrm{KG}(G, k)) \le n - 2k + 2$ (`upper_bound`); $G$ is *$k$-tight* when equality holds (at $k = 3$: `K3Tight G ↔ ¬ Colorable G (n - 5) ∧ Colorable G (n - 4)`).
- **Conjecture 1.3 (§1):** At $k = 3$ ($n \ge 7$), a simple graph $G$ is $3$-tight if and only if $G$ is a single cycle $C_n$ or a disjoint union of paths and cycles of length at least $9$ — equivalently (`Qualifies G`), $\Delta(G) \le 2$ and $G$ contains no proper cycle of length $3 \le m \le 8$.
- **Section 2 star coloring threshold:** Arana–Haxell–Kaiser–Stehlík construct a $(m - 2k + 2)$-coloring of $\mathrm{KG}(C_m \sqcup K_1, k)$ for $m \le 4k - 4$; `section_two_obstruction` proves that no $(m - 2k + 2)$-coloring extending a star coloring on $C_m$ exists for any $m \ge 4k - 3$.

## Cross-Model Adversarial Referee Audit

- **Prover:** GPT-6.2 Astra.
- **Independent Adversarial Referee:** Claude Opus 5.5 (`Verdict: ACCEPT` across all three results: complete Conjecture 1.3 at $k = 3$, all-$k$ Section 2 star-class obstruction at $m \ge 4k - 3$, and $C_m \sqcup K_1$ $4$-tightness for $m \ge 39$).
- Referee flagged three minor exposition/verifier issues during review — all repaired prior to publication:
  1. Corrected the $k = 4$ Hilton–Milner cutoff from $n \le 51$ to $n \le 52$ (with $m \ge 39$ unaffected).
  2. Made the $k = 4$ base-case appeal to Corollary 2.2 of `arXiv:2610.17884` explicit.
  3. Replaced `assert` statements in `verify.py` with explicit `-O`-safe `require()` checks.
- Independently checked the Hilton–Milner threshold $n \le 19$, the four-case nonstar triple classification, the anchor + Mantel reduction for $C_m \sqcup K_1$ ($m \ge 15$), and the finite weight / branch-and-bound certificates on orders $n = 7 \dots 19$.

## Independent Python 3 Verification

`python3 -O results/arana-haxell-kaiser-stehlik-kneser/verify.py base` and `verify.py 13 14 15 16 17 18 19` (stdlib only, `-O`-safe):

- Independently verifies all finite base cases, component weight certificates, and arithmetic cutoffs used in the proof.

## Lean 4 Formal Verification

Files: [`lean/Conjectures/StableKneserK3.lean`](../../lean/Conjectures/StableKneserK3.lean) and [`lean/Conjectures/StableKneserK3/`](../../lean/Conjectures/StableKneserK3/) (57 files, 37,351 lines, Lean `v4.33.1` + Mathlib).

- Formally verifies **Conjecture 1.3 for all simple graphs at $k = 3$** (`conjecture_1_3_k3 : 7 ≤ Fintype.card V → (K3Tight G ↔ Qualifies G)`).
- Formally proves **Schrijver's $k = 3$ theorem** for every cycle length $m \ge 6$ inside Lean without external axioms (`schrijver_k3`), **$C_m \sqcup K_1$ tightness** for all $m \ge 9$ (`isolate_k3`, `large_isolate_k3`), and the **all-$k$ Section 2 star-class obstruction** for all $k \ge 2, m \ge 4k - 3$ (`section_two_obstruction`).
- Zero `sorry`, zero custom `axiom`, zero `native_decide`.
- `lake build Conjectures.StableKneserK3` succeeded cleanly; `#print axioms` across all 147 exported theorems reports only standard axioms `[propext, Classical.choice, Quot.sound]`.
