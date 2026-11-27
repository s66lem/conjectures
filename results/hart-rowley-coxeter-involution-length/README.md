# Disproof of Hart–Rowley Conjecture 1.3 on Involution Length in Coxeter Groups (`arXiv:2502.00777v1`)

## Status

- **Conjecture:** Conjecture 1.3 of S. B. Hart and P. J. Rowley, *A note on involution prefixes in Coxeter groups*, `arXiv:2502.00777v1` (*Archiv der Mathematik* 2026): assuming Conjecture 1.2 (proved in general by Gaetz–Gao, `arXiv:2610.22857`), every element $w$ of a finite Coxeter group $W$ satisfies $\ell_{\mathrm{inv}}(w) \le \mathrm{rank}(W)$.
- **Outcome:** **Disproved** in $H_3$ ($\ell_{\mathrm{inv}}(w) = 4 > 3$), $F_4$ ($5 > 4$), $E_6$ ($8 > 6$), and $E_7$ ($\ge 8 > 7$ by parabolic inheritance from $E_6$).
- **Lean 4 formalization:** [`lean/Conjectures/HartRowleyCoxeterInvolutionLength.lean`](../../lean/Conjectures/HartRowleyCoxeterInvolutionLength.lean) (complete, standard axioms only).
- **Preprint:** [`paper.pdf`](paper.pdf) (compiled from [`paper.tex`](paper.tex)) · Zenodo DOI [`10.5281/zenodo.24581942`](https://doi.org/10.5281/zenodo.24581942).
- **Audit:** [`AUDIT.md`](AUDIT.md) (independent read-only Sonnet audit: `PASS`).

## Counterexample Summary

In the finite Coxeter group $H_3$ (rank $3$, order $120$, $m(r_1, r_2) = 3$, $m(r_2, r_3) = 5$, $m(r_1, r_3) = 2$):
- The length-$7$ element $w_1 = r_2 r_3 r_1 r_2 r_3 r_2 r_1$ has unique ancestor decomposition $(r_2 r_3 r_1 r_2)(r_3)(r_2)(r_1)$, giving $\ell_{\mathrm{inv}}(w_1) = 4 > 3 = \mathrm{rank}(H_3)$.
- A second witness $w_2 = r_2 r_3 r_2 r_3 r_1 r_2 r_3 = (r_2 r_3 r_2)(r_3 r_1)(r_2)(r_3)$ also has $\ell_{\mathrm{inv}}(w_2) = 4 > 3$.
- In crystallographic types, $F_4$ already violates the bound via $w = r_3 r_4 r_1 r_2 r_3 r_2 r_1 = (r_3 r_1)(r_4 r_2)(r_3)(r_2)(r_1)$ ($\ell_{\mathrm{inv}} = 5 > 4$), and $E_6$ reaches $\ell_{\mathrm{inv}} = 8 > 6$.

## Files

- [`PROOF.md`](PROOF.md): Complete disproof in $H_3$, $F_4$, $E_6$, parabolic inheritance to $E_7$, and Lean 4 formalization architecture.
- [`AUDIT.md`](AUDIT.md): Independent adversarial audit record.
- [`verify.py`](verify.py): Standalone verification script building $H_3$ (exact over $\mathbb{Q}(\sqrt{5})$), $F_4$, and $E_6$, verifying Conjecture 1.2 on all elements and checking explicit witnesses and exact maxima.
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf): Self-contained preprint.
