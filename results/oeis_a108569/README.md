# OEIS A108569 Parity Conjecture (Firoozbakht 2005) — Disproved

- **Source:** F. Firoozbakht, comment on [OEIS A108569](https://oeis.org/A108569) (Jul 5, 2005); `google-deepmind/formal-conjectures` (`FormalConjectures/OEIS/108569.lean`).
- **Conjecture:** Except for $n = 1$, every positive integer solution to $\varphi(n) = \varphi(n + \varphi(n))$ is even.
- **Result:** **Disproved.** The odd integer
  $$n = 5{,}095{,}354{,}107 = 3 \times 1{,}033 \times 1{,}644{,}193$$
  satisfies $\varphi(n) = 3{,}393{,}612{,}288$ and
  $$n + \varphi(n) = 8{,}488{,}966{,}395 = 3 \times 5 \times 7 \times 13 \times 19 \times 327{,}317, \qquad \varphi(n + \varphi(n)) = 3{,}393{,}612{,}288 = \varphi(n).$$
  Because $3 \mid \gcd(n, \varphi(n))$, $n_j = 3^j \cdot 5{,}095{,}354{,}107$ ($j \ge 0$) gives an infinite family of odd counterexamples.

## Files

- [DISPROOF.md](DISPROOF.md) — full factorizations and proof of the infinite odd family.
- [verify.py](verify.py) — standalone Python 3 verifier using deterministic trial division for primality and checking $j = 0 \dots 5$.

## Verify

```bash
python verify.py
```
