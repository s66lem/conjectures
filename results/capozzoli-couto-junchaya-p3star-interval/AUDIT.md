# Audit Log: Disproof of Capozzoli–Couto–Junchaya Conjecture 1 under ETH (`arXiv:2609.22640v1`)

## 1. Source & Definition Audit

- **Source:** Idian C. Capozzoli, Yan S. Couto, and Enrique Junchaya, *Interval number for tournaments in $P_3$-convexity*, `arXiv:2609.22640v1` (Sep 2026).
- **Target (Section 5, Conjecture 1):** *$P_3^*$-interval on Tournaments* — given a tournament $T$ and positive integer $k$, decide whether $\mathrm{in}_{P_3^*}(T) \le k$ — is **NP-complete**.
- **Definition match:** Verified verbatim against Section 1.1 and Lemma 4 of `arXiv:2609.22640v1`: in a tournament $T$, a directed path $u \to v \to w$ is shortest iff $w \to u \in A(T)$, so $I_{P_3^*}(S) = S \cup \{v : \exists u, w \in S,\, u \to v \to w \to u\}$.

## 2. Cross-Model Adversarial Audit (`gpt-6.2-sol`)

An independent adversarial review audited Lemmas A–E, the recursive algorithm, correctness, running time, ETH/Sparsification implication, and Theorem 4.1 strong connectivity. Verdict: **PASS WITH MINOR FIXES**, all of which were folded into the final proof, manuscript, verifier, and Lean 4 formalization:

1. **Greedy loop termination guard:** Added explicit $U \ne \emptyset$ guard to the greedy loop (preventing $0 \ge 0$ nontermination when $U = \emptyset$) and upfront $k \ge n \implies \textsc{Yes}$ exit.
2. **Lemma D proof order:** Proved the interior gap bound for occupied endpoints first, then deduced the 4-band non-emptiness property from the endpoint band bounds $U \cap (C_1 \cup C_2) \ne \emptyset$ and $U \cap (C_{r-1} \cup C_r) \ne \emptyset$.
3. **Integer-exact parameterization:** Parameterized $K_0 = 8000\ell$ and $r = \lfloor k / (40\ell) \rfloor$ with $\ell = \lfloor \log_2 n \rfloor + 1$ and cross-multiplied integer comparisons, eliminating real logarithms in the executable algorithm and Lean proof.
4. **Runtime recurrence & ETH citation:** Defined $\tau(k)$ as the maximum over budgets $\le k$, charged polynomial per-branch overhead explicitly, and cited the Impagliazzo–Paturi–Zane Sparsification Lemma for variable-count ETH.
5. **Verifier coverage:** Added a constrained subproblem test with $F \ne \emptyset$ (including a vertex in $R_t$) whose recursive band-splitting actively fires (`YES splits=1, NO splits=1`).

## 3. Computational Verification (`verify.py`)

- Ran `python -O results/capozzoli-couto-junchaya-p3star-interval/verify.py` (Python 3 stdlib only, `-O`-safe `require()` checks):
  - Verified Lemmas A, B, C, D, and E across 14 diverse tournament families ($n = 32$ to $60$).
  - Verified strong connectivity of Theorem 4.1 constructions.
  - Verified exact equivalence against an independent branch-and-bound solver on 4 full tournaments (strong and non-strong, YES and NO, `splits >= 1` on all) and on a constrained $F \ne \emptyset$ subproblem (`YES splits=1, NO splits=1`).
  - Result: `PASS` in 7.24s (exit 0).

## 4. Lean 4 Formalization Audit (`lean/Conjectures/TournamentP3StarQP.lean`)

- **Toolchain:** Lean `v4.33.1` + Mathlib `v4.33.1` (1,723 lines).
- **Hygiene audit:** Zero occurrences of `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, or `implemented_by`.
- **Verified exports under `TournamentP3StarQP`:**
  - Structural lemmas: `lemmaA_lipschitz`, `lemmaB_forward`, `lemmaE_triangle_radius`, `lemmaC_decoupling`, `lemmaD_empty_gap`.
  - Executable solver & correctness: `solve_sound`, `solve_complete`, `solve_iff_full`, `solveWithCost_eq_solve`.
  - Unit-cost quasi-polynomial work bound: `solveWithCost_quasipolynomial` and `solveCost_quasipolynomial` (proving `solveCost T D F k ≤ 2 ^ (20000000 * (Nat.log 2 (Fintype.card V) + 1) ^ 4)`).
  - Strong tournament reduction: `thm41_strongly_connected`.
- **Axiom check (`#print axioms`):** All 12 exported theorems depend strictly on `[propext, Classical.choice, Quot.sound]`.
- **Scope note:** The unit-cost quasi-polynomial work bound and solver correctness are machine-checked in Lean 4; the conditional ETH implication (via Sparsification and Corollary 3 of `arXiv:2609.22640v1`) is a standard paper-level corollary.
- **Build check:** `lake build Conjectures.TournamentP3StarQP` and `lake env lean Conjectures\TournamentP3StarQP.lean` passed with exit code 0 and zero warnings.
