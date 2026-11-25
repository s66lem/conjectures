# Proof of Benedetti–Menara Conjecture 7.1 for $r = 2$ (Flag $1$-Layered Families)

Complete proof and Lean 4 formal verification settling the **$r = 2$ (triangle-free graph) case of Conjecture 7.1** of Bruno Benedetti and Giuliamaria Menara, *Diameter bounds for complexes that are close to flag or close to normal* (`arXiv:2611.08071`, §7), together with two unconditional higher-rank consequences.

## Main Results

1. **Conjecture 7.1 for $r = 2$ (sharp bound $m - 1$):** Every flag $1$-layered family of $2$-subsets of an $m$-element set ($m \ge 2$) has at most $m - 1$ layers, improving the Larman–Barnette bound $2m - 3$ (`arXiv:2611.08071`, Theorem 2.1) to the exact optimum attained by the path on $m$ vertices.
2. **Halved Larman–Barnette bound for all flag $1$-layered $r$-set families ($r \ge 2$):** Every flag $1$-layered family of $r$-subsets of an $m$-set has at most $2^{r-2}(m - r) + 1$ layers.
3. **Unconditional Lemma 7.2 and Main Theorem E(a) at $p = r - 2$ / $p = d - 2$:** Carrying the upper bound $p = r - 2$ through the link recursion of Lemma 7.2 invokes only the proved $r = 2$ flag base case, making Main Theorem E(a) of `arXiv:2611.08071` unconditional at parameter $p = d - 2$ for every pure normal $(d - 1)$-complex with $\mathrm{fd}(\Delta) \le d - 2$.

## Files

- [`PROOF.md`](PROOF.md) — Self-contained proof of the $r = 2$ theorem (monotone-path counting lemma for non-proper interval labelings + downward-reachability induction) and both higher-rank consequences.
- [`AUDIT.md`](AUDIT.md) — Cross-model adversarial referee audit and Lean 4 verification log.
- [`verify.py`](verify.py) — Standalone Python 3 verifier (stdlib only: exhaustive $m = 5$ enumeration of all $13{,}017$ families, tight paths, $K_4$ non-flag control, $c \ge 1$ witnesses, and $10{,}000$ random families).
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Self-contained LaTeX manuscript and compiled PDF.
- [`../../lean/Conjectures/FlagLayeredR2.lean`](../../lean/Conjectures/FlagLayeredR2.lean) — Lean 4 formalization (`flag_one_layered_r2_le`, `path_attains_bound`, `triangle_free_interval_layers_le`, `monotone_path_vertex_bound`).

## Reproduction

```bash
python3 results/benedetti-menara-flag-layered/verify.py
cd lean && lake build Conjectures.FlagLayeredR2
```
