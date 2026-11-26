# Disproof of Talmage's Monotonicity Conjecture for Muñiz's List Reversal

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24565022.svg)](https://doi.org/10.5281/zenodo.24565022)

**Status:** Disproved (both directions of monotonicity fail; **Lean 4 verified** & independently cross-model audited — [AUDIT.md](AUDIT.md))

## Source

- **Paper:** Alan Talmage, *A Density Bound for Muñiz's List Reversal*, [`arXiv:2611.25115v1`](https://arxiv.org/abs/2611.25115) [math.CO], 18 November 2026.
- **Location:** Section *Discussion* (third open-problem bullet, preceding Appendix A).
- **Conjecture (verbatim):**
  > "The irreversible lists found by computer search in [Appendix A] suggest a conjecture that reversibility is monotonic in $n$, in the sense that replacing the maximum value $n$ in an irreversible list with $n+1$ (leaving the rest of the list unchanged) must yield an irreversible list. No counterexamples to the conjecture are presently known, but it is not clear if that is an artifact of only having data on short lists."

## Main Result

Under Muñiz's list reversal rules (replace two adjacent entries by their sum, or split one entry into two adjacent positive integers with the same sum, maintaining distinct entries in $\{1, \dots, n\}$ where $n$ is the maximum of the initial list), reversibility is **not** monotonic in $n$ in either direction:

1. **As stated (irreversible at $n \implies$ irreversible at $n + 1$): False.**
   The list $(2, 6)$ is irreversible (its entire reachable component has $7$ states and omits $(6, 2)$), whereas $(2, 7)$ reverses in $4$ legal moves:
   $$(2, 7) \to (2, 1, 6) \to (3, 6) \to (3, 4, 2) \to (7, 2).$$
   (Moreover, the stated direction contradicts the paper's own Corollary that there are only finitely many irreversible lists of each length.)

2. **Converse reading (reversible at $n \implies$ reversible at $n + 1$): False.**
   The list $(1, 3, 7, 4)$ reverses in $18$ legal moves, whereas $(1, 3, 8, 4)$ (listed in Appendix A of Talmage's paper) is irreversible (its entire reachable component has $5$ states and omits $(4, 8, 3, 1)$).

## Files

- [PROOF.md](PROOF.md) — Complete hand-checkable proof with full transition tables for both closed components and both explicit reversal sequences.
- [AUDIT.md](AUDIT.md) — Independent cross-model adversarial audit (`claude-sonnet-5-5`, PASS).
- [verify.py](verify.py) — Standalone stdlib-only verification script (`python -O -W error verify.py`, optional `--l4` for the 307 length-4 recount).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Standalone preprint ([DOI: 10.5281/zenodo.24565022](https://doi.org/10.5281/zenodo.24565022)).
- [`lean/Conjectures/TalmageListReversal.lean`](../../lean/Conjectures/TalmageListReversal.lean) — Lean 4 formalization proving `talmage_monotonicity_disproof`, `not_reversible_2_6`, `reversible_2_7`, `reversible_1_3_7_4`, and `not_reversible_1_3_8_4`.
