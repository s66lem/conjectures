# Verification & Audit Log — Manabe Conjecture 57 (`arXiv:2609.05358v2`)

## Source & Definition Audit

Checked verbatim against Hikaru Manabe, *Purely Periodic Three-move Subtraction Games* (`arXiv:2609.05358v2`, §§1–3, 6):

- **Three-move subtraction game $S = \{a, b, c\}$ ($1 \le a < b < c$):** Sprague–Grundy sequence $\mathcal{G}_S(x) = \mathrm{mex}\{\mathcal{G}_S(x - s) : s \in S,\, s \le x\}$, $\mathrm{P}$-position set $W = \mathcal{W}_0(S) = \{x \in \mathbb{N} : \mathcal{G}_S(x) = 0\}$, base game $B = \{a, b\}$ with $\mathcal{Z} = W_B \cap [0, a + b)$, gap set $D = [a, b) \setminus \mathcal{Z}$, $\delta = b - a = \eta a + \varepsilon$ ($0 \le \varepsilon < a$), and angle $\rho = c \bmod (a + b)$.
- **Arc $\Lambda$ (formula (4)):** $[(\eta + 1)a, (\eta + 1)a + \varepsilon)$ if $\eta$ is even, and $[\eta a + \varepsilon, (\eta + 1)a)$ if $\eta$ is odd.
- **Admissible angle sets (Definition 19):**
  - **(T0)** $\rho \in \Theta_{a+b} \iff \mathcal{Z} \cap (\mathcal{Z} + \rho) = \emptyset \pmod{a + b}$.
  - **(T1)** $\rho \in \Theta_{c+a} \iff \mathcal{Z} \cap [0, \delta) \cap (\mathcal{Z} + (\delta - \rho)) = \emptyset \pmod{a + b}$.
  - **(T2)** $\rho \in \Theta_{c+b} \iff (\rho + \Lambda) \cap \mathcal{Z} = \emptyset$ and $(\rho + D) \cap \Lambda = \emptyset \pmod{a + b}$.
- **Conjecture 57 (§6):** Under $a \ge 2$, $\gcd(a,b,c) = 1$, $c \neq a + b$, if $\mathcal{G}_S$ is purely periodic with least period $p$, then $p = c + a \implies \rho \in \Theta_{c+a}$ and $p = c + b \implies \rho \in \Theta_{c+b}$. Our Theorems 3.2–3.4 prove the strictly stronger equivalence at the $\mathrm{P}$-position level for *all* $1 \le a < b < c$ and *any* pure period $P \in \{a + b, c + a, c + b\}$.

## Cross-Model Adversarial Audit

- **Prover:** Claude Opus 5.5 (discovered the proof of Theorems A0, A1, A2, the cyclic-interval characterization of $\Theta_{c+b}$, the equivalence Conjecture 52 $\iff$ Conjecture 56 for all $c > b$, the partial period exclusions, and ran the $100{,}946{,}926$-triple exact cycle-detection search).
- **Independent Cross-Model Auditor:** Gemini 4 Neon (independently checked every lemma and edge case against `arXiv:2609.05358v2`, including $a = 1$, $b = a + 1$, $b < 2a$, $b = ka$ for even and odd $k$, $\Lambda = \emptyset$, $b < c < a + b$, $c = a + b$, and non-primitive triples).
- **Review catch fixed prior to publication:** In the Fine–Wilf partial period exclusion (`c ≥ p + n - gcd(p, n)`), the initial prose echoed Manabe's Lemma 54 condition `c ≥ p + g`, which fails when `g = n` (`n ∣ p`). Corrected in both prose (`PROOF.md`, `paper.tex`) and Lean 4 (`fine_wilf_period_implies_Theta_ab`) to use only `p ≤ c` and `g ∣ p`, covering all `g = n` cases cleanly.

## Independent Python 3 Verification

`python3 -O results/manabe-subtraction-games/verify.py` (stdlib only, `-O`-safe):

- Matches Manabe's Example 1 ($(a, b) = (3, 8)$: $\mathcal{Z} = \{0, 1, 2, 6, 7\}$, $\Theta_{a+b} = \{3, 8\}$, $\Theta_{c+a} = \{2, 8\}$, $\Theta_{c+b} = \{3, 4, 5, 9, 10\}$) and Manabe's exact census on $2 \le a \le 8, b \le 40, c \le 100$ ($7{,}557$ admissible / $7{,}828$ non-admissible).
- Independently verifies F1–F4, L1–L2, Theorems A0/A1/A2, the explicit cyclic-interval form of $\Theta_{c+b}$, and both partial period exclusions on all $16{,}755$ unrestricted triples $1 \le a \le 18, a < b \le 30, b < c \le 65$ (including $9{,}994$ extended Fine–Wilf hits, of which $5{,}562$ have $(a + b) \mid p$).

## Lean 4 Formal Verification

File: [`lean/Conjectures/ManabeSubtraction.lean`](../../lean/Conjectures/ManabeSubtraction.lean) (1,121 lines, Lean `v4.33.1` + Mathlib).

- Formalizes exact `isP`, `isPB`, `grundy` (with `grundy_eq_zero_iff_isP`), verbatim `Z`, `D`, `Lambda`, `Theta_ab`, `Theta_ca`, `Theta_cb`, `ExplicitTheta_cb`, `PurelyPeriodicP`, and `PurelyPeriodicG`.
- Exports `period_ab_iff`, `period_ca_iff`, `period_cb_iff`, `Theta_cb_iff_explicit`, `manabe_conjecture_57`, `no_period_in_open_interval`, and `fine_wilf_period_implies_Theta_ab`.
- Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero warnings.
- `lake build Conjectures.ManabeSubtraction` succeeded cleanly (11s); `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for all seven exported theorems.
