# Audit Log: Disproof of Firoozbakht's OEIS A086766 Conjecture

## 1. Source & Live OEIS Audit

- **Source:** [OEIS A086766](https://oeis.org/A086766) (Farideh Firoozbakht, Jan 7, 2015) and `google-deepmind/formal-conjectures` (`FormalConjectures/OEIS/86766.lean`, `OeisA86766.conjecture2`, tagged `@[category research open, AMS 11]`).
- **Verbatim conjecture:** If $n > 0$ is not of the form $10^m$, then $a(n) \ne 0$, where $a(n)$ is the least $r \ge 1$ such that $(n \sum_{i=0}^{r-1} 10^{di}) \cdot 10 + 1$ is prime ($d = \lfloor \log_{10} n \rfloor + 1$), or $0$ if none exists.
- **Live OEIS check (2026-11-25):** Confirmed that Firoozbakht's 2015 conjecture remains listed as open on live `oeis.org/A086766` with no counterexample noted.

## 2. Computational Verification (`verify.py`)

- Ran `python -O results/firoozbakht-oeis-a086766/verify.py` (Python 3 stdlib only, `-O`-safe `require()` checks):
  - Verified the infinite family $n_k = 10(10^{2k} - 1)/99$ for $k = 2, \dots, 12$ ($r = 1, \dots, 6$), including minimal $4$-digit $n_2 = 1010$.
  - Verified the difference-of-squares algebraic hypotheses and explicit factorizations ($r = 1, \dots, 6$) for the minimal $6$-digit primitive (non-periodic) witness $n = 104040$ and the $78$-digit primitive witness $n = 100558839880907801793259217884670002826017800775406752876641328923179557019040$.
  - Result: `PASS` (exit 0).

## 3. Lean 4 Formalization Audit (`lean/Conjectures/FiroozbakhtA086766.lean`)

- **Toolchain:** Lean `v4.33.1` + Mathlib `v4.33.1`.
- **Definition match:** `primeCandidate` and `a` match `FormalConjectures/OEIS/86766.lean` verbatim (`(Nat.digits 10 n).length`, `sInf {r : ℕ | 0 < r ∧ (primeCandidate n r).Prime}`).
- **Hygiene audit:** Zero occurrences of `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, or `implemented_by`.
- **Verified exports under `FiroozbakhtA086766`:**
  - `disproof_minimal_1010` ($n = 1010$, $a(1010) = 0$)
  - `disproof_infinite_family` ($\forall k \ge 2$, $n_k = 10(10^{2k}-1)/99 \ne 10^m$ and $a(n_k) = 0$)
  - `a_eq_zero_of_diff_squares` (general even-length algebraic difference-of-squares criterion)
  - `disproof_primitive_104040` ($n = 104040$, $a(104040) = 0$)
  - `disproof_giant78` ($78$-digit primitive witness `giant78`, $a(\mathrm{giant78}) = 0$)
- **Axiom check (`#print axioms`):** All four main theorems depend only on `[propext, Classical.choice, Quot.sound]`.
- **Build check:** `lake env lean Conjectures\FiroozbakhtA086766.lean` exited with code 0 and zero warnings.
