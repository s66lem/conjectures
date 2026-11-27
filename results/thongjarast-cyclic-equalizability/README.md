# Disproof of Thongjarast's Discard-Letter Conjecture on Cyclic Equalizability (`arXiv:2607.18452v1`, Problem 2)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24573606.svg)](https://doi.org/10.5281/zenodo.24573606)

**Problem:** Problem 2 (`prob:discard`) of S. Thongjarast, *0-Cyclic Equalizability of Binary Words Characterized by Hamming Weight*, [arXiv:2607.18452v1](https://arxiv.org/abs/2607.18452) (20 July 2026).

**Status:** **DISPROVED** (answer is **NO**, formally verified in **Lean 4**):
- For every finite alphabet $\Sigma = \{x_0, \dots, x_{m-1}\}$ of size $m \ge 3$ (indices modulo $m$), the length-$3m$ words
  $$u_m = \prod_{i=0}^{m-1} x_i x_i x_{i+1}, \qquad v_m = \prod_{i=0}^{m-1} x_{i+1} x_i x_{i+1}$$
  are permutations of each other, use every letter of $\Sigma$, and are **not** $(\Sigma \setminus \{c\})$-cyclically equalizable for **any** letter $c \in \Sigma$.
- Smallest instance ($m = 3$, $\Sigma = \{a, b, c\}$, length $n = 9$):
  $$u_3 = \texttt{aabbbccca}, \qquad v_3 = \texttt{babcbcaca}.$$
  With the full alphabet $\Sigma$, $(u_3, v_3)$ is cyclically equalizable (explicit length-$15$ witness with cyclic shift $d = 10$: $\texttt{aabcababcacabca}$ vs $\texttt{babcacabcaaabca}$).

## Statement (Verbatim)

> **Problem 2 (`prob:discard`).** Let $\Sigma$ be an alphabet of size at least $3$. Let $u$ and $v$ be words over $\Sigma$ that are permutations of each other. Must there exist a letter $c \in \Sigma$ such that $u$ and $v$ are $(\Sigma \setminus \{c\})$-equalizable?

Here a $\sigma$-simultaneous insertion inserts identical words $w_0, \dots, w_n \in \sigma^*$ into identical slots of both $u$ and $v$, and two words $u', v'$ of length $L$ are cyclically equivalent iff $u'[t] = v'[(t + d) \bmod L]$ for some integer $d$ and all $0 \le t < L$.

## Summary of Disproof

For each block $i \in \{0, \dots, m - 1\}$, the pair $(u_m, v_m)$ at positions $(3i, 3i + 1, 3i + 2)$ is $(x_i, x_{i+1}), (x_i, x_i), (x_{i+1}, x_{i+1})$.

Suppose $c = x_i$ is discarded ($\sigma = \Sigma \setminus \{c\}$) and some $\sigma$-simultaneous insertion produces cyclically equivalent words $u', v'$ of length $L$ with shift $d$ and original letter positions $P(0) < \dots < P(3m - 1) < L$:

1. **Nonzero shift:** $d \not\equiv 0 \pmod{L}$, else $u' = v'$ forces $u_m = v_m$.
2. **Rigidity of $c$:** Whenever $u_m[j] = c$, we have $v'[P(j) + d \bmod L] = c \notin \sigma$, so $P(j) + d \bmod L = P(\varphi(j))$ for a fixed-point-free bijection $\varphi : U_c \to V_c$ between the $c$-positions of $u_m$ and $v_m$.
3. **Half-turn forcing ($2d \equiv 0 \pmod{L}$):** The four $c$-positions $\beta = 3i \in U_c \setminus V_c$, $\gamma = 3i + 1 \in U_c \cap V_c$, $\delta = 3(i - 1) \bmod 3m \in V_c \setminus U_c$, and $\alpha = (3i - 1) \bmod 3m \in U_c \cap V_c$ lie in cyclic order $\beta \prec \gamma \prec \delta \prec \alpha$, which is preserved by the strictly increasing map $P$. Exactly three fixed-point-free bijections $U_c \to V_c$ exist: the two 4-step chains force $0 < [2e]_L < [3e]_L < e$ or $0 < e < [3e]_L < [2e]_L$ (both arithmetically impossible for $0 < e < L$), leaving the transposition $\alpha \leftrightarrow \gamma, \beta \mapsto \delta$, which forces $2e = L$.
4. **Antipodal-swap contradiction:** With $2d \equiv 0 \pmod{L}$, the mismatch position $j = 0$ of type $(x_0, x_1)$ forces the antipodal position $P(0) + L/2 \bmod L$ to be an original position $P(j')$ of swapped mismatch type $(x_1, x_0)$. However, the mismatch types of $(u_m, v_m)$ form the directed $m$-cycle $(x_0, x_1), \dots, (x_{m-1}, x_0)$, which contains no reversed pair for $m \ge 3$.

## Files

- [PROOF.md](PROOF.md) — Complete self-contained mathematical disproof.
- [AUDIT.md](AUDIT.md) — Independent cross-model adversarial audit (`claude-sonnet-5-5`, PASS).
- [verify.py](verify.py) — Standalone stdlib-only verifier (`python -O -W error verify.py`).
- [paper.tex](paper.tex) / [paper.pdf](paper.pdf) — Formatted preprint ([DOI: 10.5281/zenodo.24573606](https://doi.org/10.5281/zenodo.24573606)).
- [ThongjarastCyclicEqualizability.lean](../../lean/Conjectures/ThongjarastCyclicEqualizability.lean) — Complete Lean 4 formalization.
