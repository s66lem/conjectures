# Disproof of Runbo Li's Twin-Practical Conjecture 1.1 (`NNTDM` 32(3), 2026)

## Status

- **Conjecture:** Conjecture 1.1 of Runbo Li, *On a conjecture involving twin practical numbers*, *Notes on Number Theory and Discrete Mathematics* 32(3) (2026), 544–555, DOI `10.7546/nntdm.2026.32.3.544-555`: for any positive integer $C$, there are infinitely many practical numbers $q$ such that $q^C$ and $q^C + 2$ are also practical numbers.
- **Outcome:** **Disproved** at $C = 30$ and for every positive multiple $C = 30 t$ ($t \ge 1$): there are **zero** positive integers $q$ for which $q^C + 2$ is practical. Moreover, $30 \mid C$ is the exact characterization of the local small-divisor obstruction modulo $\{4, 9, 5, 7, 11, 13\}$.
- **Lean 4 formalization:** [`lean/Conjectures/LiTwinPractical.lean`](../../lean/Conjectures/LiTwinPractical.lean) (complete, standard axioms only).
- **Preprint:** [`paper.pdf`](paper.pdf) (compiled from [`paper.tex`](paper.tex)) · Zenodo DOI [`10.5281/zenodo.24585372`](https://doi.org/10.5281/zenodo.24585372).
- **Audit:** [`AUDIT.md`](AUDIT.md) (independent read-only Sonnet audit: `PASS`).

## Summary of Proof

Let $n = q^{30} + 2$ for a positive integer $q$:
- If $q$ is odd, then $n \ge 3$ is odd, so its only divisor $\le 2$ is $1$, and $2$ is not a sum of distinct divisors of $n$.
- If $q$ is even, then $4 \nmid n$ ($n \equiv 2 \pmod{4}$), $9 \nmid n$ ($q^{30} \equiv 0, 1 \pmod{9}$), $5 \nmid n$ ($q^{30} \equiv 0, 1, 4 \pmod{5}$), $7 \nmid n$ ($q^{30} \equiv 0, 1 \pmod{7}$), $11 \nmid n$ ($q^{30} \equiv 0, 1 \pmod{11}$), and $13 \nmid n$ ($q^{30} \equiv 0, 1, 12 \pmod{13}$). Thus every divisor $d \mid n$ with $d \le 13$ belongs to $\{1, 2, 3, 6\}$, whose sum is $12 < 13 \le n$. Hence $13$ cannot be represented as a sum of distinct divisors of $n$, so $n$ is not practical.
- For any $C = 30 t$ ($t \ge 1$), $q^{30t} + 2 = (q^t)^{30} + 2$ is never practical.

## Files

- [`PROOF.md`](PROOF.md): Complete disproof, exact sharpness theorem (`30 ∣ C`), and positive small-$C$ contrast.
- [`verify.py`](verify.py): Standalone verification script checking all residue classes, the modulo-$360360$ divisor lemma, direct checks for $q \le 400$, brute-force cross-checks for $n < 3000$, and small-$C$ positive examples.
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf): Self-contained preprint.
