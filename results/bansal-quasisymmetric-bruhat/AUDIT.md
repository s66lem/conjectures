# Audit Log — Bansal Conjecture C / 6.11 (`arXiv:2611.02210`)

## 1. Source & Definition Verification

All definitions were checked verbatim against `arXiv:2611.02210v1` (*A Quasisymmetric Analogue of the Bruhat Order*, Ryan Bansal, November 2026):

- **Indexed forests and codes (Definitions 2.1 & 2.4):** Binary forests on $\mathbb{Z}_{>0}$ with $\rho(v)$ = leftmost leaf label in the subtree rooted at $v$ and code $c_i(F) = \#\{v \in \mathrm{IN}(F) : \rho(v) = i\}$.
- **Forest polynomials (Definition 2.3 & Fact 2.5):** Valid labelings $\lambda : \mathrm{IN}(F) \to \mathbb{Z}_{>0}$ satisfy $1 \le \lambda(v) \le \rho(v)$, $\lambda(v) \le \lambda(\text{left child})$, and $\lambda(v) < \lambda(\text{right child})$; $P_F = \sum_\lambda \prod_v x_{\lambda(v)}$ has lexicographically smallest monomial $x^{\mathbf{c}(F)}$ with coefficient $1$.
- **Quasisymmetric Bruhat order (Definition 2.7):** Cover relation $F \lessdot G$ iff $P_G$ appears in the forest-basis expansion of $(x_1 + \cdots + x_i) P_F$ for some $i \ge 1$.
- **Zigzag forest (Definition 6.8):** $Z = F(a_1, \dots, a_k)$ with $a_j > 0$ for all $1 \le j \le k$.
- **Conjecture C / Conjecture 6.11:** Every zigzag lower interval $[\varnothing, Z]$ is shellable.

## 2. Independent Cross-Model & Computational Verification

- **Independent Python 3 audit (`verify.py`, stdlib only, `-O`-safe):** Independently reconstructed indexed forests, valid labelings, and exact forest polynomials directly from Definitions 2.1, 2.3, 2.4, and 2.7; calibrated against Figure 3 and Figure 5 of `arXiv:2611.02210`; verified that for $Z = F(1, 2, 4)$ and $x = F(0, 1, 0, 1, 1, 0, 1)$ the open interval $(x, Z)$ has exact order complex $C_6 \sqcup C_6$ (6 rank-5 elements, 6 rank-6 elements, 12 cover edges, 2 vertex-disjoint 6-cycles); and confirmed all four failing rank-7 zigzags and the infinite code-raising chains.
- **Result of `python3 -O results/bansal-quasisymmetric-bruhat/verify.py`:** `PASS`.

## 3. Formal Verification in Lean 4

- **Entry point:** `lean/Conjectures/QuasisymmetricBruhat.lean` (12 modules under `lean/Conjectures/QuasisymmetricBruhat/`, 3,460 lines total).
- **Build & hygiene:** `cd lean && lake build Conjectures.QuasisymmetricBruhat` succeeds with 0 errors and 0 warnings; zero `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or `implemented_by` tokens across all 12 files.
- **Definition fidelity:** `Forest.Valid`, `forestPoly`, `MonkCover`, `QBruhatLE`, `IsZigzag`, and `IsShellable` formalize Definitions 2.1, 2.3, 2.4, 2.7, 6.8, and Section 6.1 verbatim without external axioms. The divided-difference identity `D_j P_F = [j terminal] · x_j · P_{F/j}`, unique forest-basis expansion, Fact 6.1 at both endpoints, completeness of the open interval $(x, Z) \cong C_6 \sqcup C_6$, and the first-coordinate raising identity `x_1 P_F = P_{F + e_1}` are all proved from first principles.
- **Axiom check (`#print axioms`):**
  - `QuasisymmetricBruhat.Z_is_zigzag`: `[propext, Quot.sound]`
  - `QuasisymmetricBruhat.open_interval_x_Z_disconnected`: `[propext, Classical.choice, Quot.sound]`
  - `QuasisymmetricBruhat.lowerInterval_Z_not_shellable`: `[propext, Classical.choice, Quot.sound]`
  - `QuasisymmetricBruhat.not_bansal_conjecture_C`: `[propext, Classical.choice, Quot.sound]`
  - `QuasisymmetricBruhat.bansal_conjecture_C_false`: `[propext, Classical.choice, Quot.sound]`
