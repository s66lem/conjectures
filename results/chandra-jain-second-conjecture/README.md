# Proof of the Second Chandra--Jain Conjecture and Exact Degree Criterion (`arXiv:2608.11372v3`)

## Status

- **Conjecture:** Second Chandra--Jain Conjecture (Chandra & Jain, *On The Spectral Properties of Discrete Landscape Functions*, `arXiv:2608.11372v3`, Section 5, `conj:chandra-jain-second`) and accompanying open arithmetic criterion.
- **Outcome:** **Proved** (both the dichotomy and the exact arithmetic criterion for all odd $1 \le k < N$, generalizing the coprime case $d = 1$).
- **Lean 4 formalization:** [`lean/Conjectures/ChandraJainSecondConjecture.lean`](../../lean/Conjectures/ChandraJainSecondConjecture.lean) (complete, zero axioms beyond the standard three `[propext, Classical.choice, Quot.sound]`, zero warnings, independent cross-model audit `PASS` in [`AUDIT.md`](AUDIT.md)).
- **Preprint:** [DOI `10.5281/zenodo.24578327`](https://doi.org/10.5281/zenodo.24578327) · [`paper.pdf`](paper.pdf) (compiled from [`paper.tex`](paper.tex)).

## Summary

For integers $N \ge 3$ and odd $k$ with $1 \le k < N$, set $d = \gcd(N, k)$ and $N_0 = N / d$. The discrete landscape expansion coefficient is

$$c_k(N) = \frac{1}{4}\sqrt{\frac{2}{N}}\cot\left(\frac{k\pi}{2N}\right)\csc^2\left(\frac{k\pi}{2N}\right).$$

We prove:
1. If $N_0$ is odd, then $[\mathbb{Q}(c_k(N)) : \mathbb{Q}] = \varphi(N_0)$.
2. If $N_0$ is even, then $[\mathbb{Q}(c_k(N)) : \mathbb{Q}] = \varphi(N_0)$ if every prime $p$ with odd valuation $v_p(d)$ divides $N_0$, and $2\varphi(N_0)$ otherwise.

In particular, whenever $d > 1$, $[\mathbb{Q}(c_k(N)) : \mathbb{Q}] \in \{\varphi(N_0), 2\varphi(N_0)\}$, proving the Second Chandra--Jain Conjecture; when $d = 1$, the degree is $\varphi(N)$ for all odd $k$ coprime to $N$.

## Files

- [`PROOF.md`](PROOF.md): Complete self-contained proof inside $\mathbb{Q}(\zeta_{8N})$.
- [`AUDIT.md`](AUDIT.md): Independent cross-model adversarial audit report (`claude-sonnet-5-5`).
- [`verify.py`](verify.py): Standalone verification script checking 3,599 odd pairs ($3 \le N \le 120$), the $c_1(N)$ degree table, the $59/48$ non-coprime split for $N \le 50$, and explicit CRT sign-flip witnesses.
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf): Self-contained preprint.
