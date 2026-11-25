# Verification & Audit Log — Rofa's Regular Spider 0-Rotatability Conjecture

## Source & Definition Audit

Checked verbatim against R. I. Rofa, *0-rotatability of classes of rooted symmetric trees. Are rooted symmetric trees 0-rotatable?* (`arXiv:2312.16235`, 2023) and *On the 0-Rotatability of Regular Spider Trees of Leg Length 4* (`arXiv:2611.29448`, Nov 22, 2026):

- **Regular (symmetric) spider tree $T(k, \ell)$:** Central root $v_0$ with $k \ge 1$ pairwise internally disjoint paths (legs) of uniform length $\ell \ge 1$ attached ($k\ell + 1$ vertices, $k\ell$ edges).
- **Graceful labeling:** Bijection $f : V(T) \to \{0, \dots, |E|\}$ whose induced edge weights $|f(u) - f(v)|$ form a bijection onto $\{1, \dots, |E|\}$.
- **0-rotatable tree:** For every vertex $v \in V(T)$, there exists a graceful labeling $f$ with $f(v) = 0$.
- **Conjecture scope:** Rofa (§1 item 2 and Summary) conjectured that all *symmetric* (regular) spiders $T(k, \ell)$ are 0-rotatable, proving $\ell \le 3$; `arXiv:2611.29448` proved $\ell = 4$ and left all $\ell \ge 5$ open. (Rofa's abstract also poses the broader conjecture for arbitrary irregular spiders; our theorem completely settles the regular/symmetric spider conjecture.)

## Cross-Model Adversarial Referee Audit

- **Prover:** GPT-6.2 Astra.
- **Independent Adversarial Referee:** Claude Opus 5.5 (`Verdict: ACCEPT, with minor wording fixes`).
- Independently verified all definitions, the leg-attachment lemma line-by-line (including $m = 0$, $m$ odd/even, $\ell = 1$, extreme-label preservation, and $a = \lfloor \ell/2 \rfloor$), the $(\ell, d) = (4, 2)$ construction, and both path theorems (brute-forcing all paths up to $\ell = 11$ and checking 847 spider cases up to $k, \ell \le 11$).
- Incorporated both referee wording clarifications into `PROOF.md` and `paper.tex` (explicitly distinguishing symmetric vs. general spiders, stating $s > a$, and stating that the low labels are $\{0, \dots, a\}$).

## Independent Python 3 Verification

`python3 results/rofa-spider-rotatability/verify.py` (stdlib only, directly implementing the exact recursive odd-sum / Walecki / leg-attachment construction from `SpiderRotatability.lean` with no search tables):

- Verifies all $14{,}850$ triples $(k, \ell, d)$ with $1 \le k \le 30$, $1 \le \ell \le 30$, $0 \le d \le \ell$.
- Verifies all $333$ larger stress-test triples up to $(k, \ell) = (256, 17)$ and $(73, 64)$.
- Verifies both path constructions exhaustively through $\ell \le 64$.

## Lean 4 Formal Verification

File: [`lean/Conjectures/SpiderRotatability.lean`](../../lean/Conjectures/SpiderRotatability.lean) (835 lines, Lean `v4.33.1` + Mathlib).

- Completely self-contained: proves Rosa's 1977 path $\alpha$-labeling theorem (`rosa_path_alpha`), the arbitrary-start graceful path theorem (`graceful_path_start`), the general finite-graph leg-attachment theorem (`attach_legs_graceful`), the `Finset.image` characterization (`isGraceful_iff_images`), and the main theorem (`regular_spider_zero_rotatable`).
- Zero `sorry`, zero custom `axiom`, zero `native_decide`.
- `lake build Conjectures.SpiderRotatability` succeeded cleanly (932 jobs, 17s); `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for all four exported theorems.
