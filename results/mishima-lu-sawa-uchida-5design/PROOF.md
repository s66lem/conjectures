# Proof: Odd-Size Antipodal Rational 5-Designs for the Chebyshev Measure

**Target:** Problem 8.3 (and the odd-size existence spectrum) of T. Mishima, X.-N. Lu, M. Sawa, and Y. Uchida, *Geometric designs and Hilbert–Kamke equations of degree five for classical orthogonal polynomials*, [arXiv:2503.21151v4](https://arxiv.org/abs/2503.21151) (2 Apr 2026); *Research in Number Theory* **12** (2026), Paper No. 39, Section 8.

> **Verbatim (Section 8, Problem 8.3):** "Find an antipodal $5$-design with $37$ rational points, as the smallest open case."

---

## Main Results

An $n$-point antipodal rational $5$-design for the Chebyshev measure $d\mu(t) = \frac{dt}{\pi\sqrt{1 - t^2}}$ on $(-1, 1)$ is a finite set $X = -X \subset (-1, 1) \cap \mathbb{Q}$ of size $n$ satisfying
$$\frac{1}{n}\sum_{x \in X} x^k = \int_{-1}^{1} t^k\, d\mu(t) \qquad (0 \le k \le 5),$$
i.e. odd moments vanish by antipodality, $\sum_{x \in X} x^2 = n/2$, and $\sum_{x \in X} x^4 = 3n/8$. For odd $n = 2N + 1$, writing $X = \{0\} \cup \{\pm x_1, \dots, \pm x_N\}$ with distinct $x_i \in (0, 1) \cap \mathbb{Q}$, this is equivalent to
$$\sum_{i=1}^{N} x_i^2 = \frac{2N + 1}{4}, \qquad \sum_{i=1}^{N} x_i^4 = \frac{3(2N + 1)}{16}.$$

**Theorem 1 (Resolution of Problem 8.3).** The 37-point set
$$X_{37} = \{0\} \cup \left\{\pm \frac{a}{240} : a \in \{15, 57, 61, 69, 93, 129, 141, 147, 151, 183, 199, 209, 211, 215, 234, 235, 238, 239\}\right\}$$
is an antipodal rational $5$-design for the Chebyshev measure.

**Theorem 2 (Complete odd-size spectrum).** An antipodal rational $5$-design for the Chebyshev measure with an odd number of points $n = 2N + 1$ exists **if and only if $n \ge 35$ ($N \ge 17$)**.

*(Combined with Mishima–Lu–Sawa–Uchida's Theorem 1.1 for even sizes, this completely determines all attainable sizes of antipodal rational $5$-designs for the Chebyshev measure.)*

---

## 1. Proof of Existence for Every $N \ge 17$

### Step 1: Three Base Designs Covering All Residues Modulo $3$
Direct rational arithmetic verifies the following three positive half-sets $S_{N_0} \subset (0, 1) \cap \mathbb{Q}$ of sizes $N_0 \in \{17, 18, 19\}$:
- **$N = 17$ ($n = 35$, denominator $D = 1092$):**
  $$\{55, 87, 171, 305, 533, 575, 733, 753, 765, 881, 905, 966, 981, 985, 1083, 1085, 1089\} / 1092$$
  ($\sum a_i^2 = 10{,}433{,}934 = \frac{35}{4}\cdot 1092^2$, $\sum a_i^4 = 9{,}332{,}453{,}208{,}666 = \frac{105}{16}\cdot 1092^4$).
- **$N = 18$ ($n = 37$, denominator $D = 240$, Problem 8.3):**
  $$\{15, 57, 61, 69, 93, 129, 141, 147, 151, 183, 199, 209, 211, 215, 234, 235, 238, 239\} / 240$$
  ($\sum a_i^2 = 532{,}800 = \frac{37}{4}\cdot 240^2$, $\sum a_i^4 = 23{,}016{,}960{,}000 = \frac{111}{16}\cdot 240^4$).
- **$N = 19$ ($n = 39$, denominator $D = 420$):**
  $$\{47, 93, 108, 113, 129, 153, 161, 305, 309, 343, 353, 357, 365, 366, 369, 395, 405, 408, 413\} / 420$$
  ($\sum a_i^2 = 1{,}719{,}900 = \frac{39}{4}\cdot 420^2$, $\sum a_i^4 = 227{,}542{,}770{,}000 = \frac{117}{16}\cdot 420^4$).

### Step 2: Monotone Disjoint 6-Point Blocks
For $t \in \mathbb{N}$ with $t \ge 20$, define the three rational functions (from the parametrization in Lemma 3.2 of `arXiv:2503.21151v4`):
$$a(t) = \frac{2t^2 - 22t - 13}{14(t^2 + t + 1)}, \qquad b(t) = \frac{13t^2 + 4t - 11}{14(t^2 + t + 1)}, \qquad c(t) = \frac{11t^2 + 26t + 2}{14(t^2 + t + 1)}.$$
Direct polynomial expansion gives $a(t) - b(t) + c(t) = 0$ and
$$a(t)^2 + b(t)^2 + c(t)^2 = \frac{3}{2}, \qquad a(t)^4 + b(t)^4 + c(t)^4 = \frac{9}{8}.$$
Moreover, for every $t \ge 20$:
1. **Disjoint open intervals:**
   $$0 < a(t) < \frac{2}{14} < \frac{11}{14} < c(t) < \frac{12}{14} < b(t) < \frac{13}{14} < 1,$$
   so $a(t), b(t), c(t)$ are pairwise distinct and lie in $(0, 1)$.
2. **Strict monotonicity:** For all $20 \le t_1 < t_2$,
   $$a(t_2) - a(t_1) = \frac{(t_2 - t_1)(24 t_1 t_2 + 15(t_1 + t_2) - 9)}{14(t_1^2+t_1+1)(t_2^2+t_2+1)} > 0,$$
   $$b(t_2) - b(t_1) = \frac{(t_2 - t_1)(9 t_1 t_2 + 24(t_1 + t_2) + 15)}{14(t_1^2+t_1+1)(t_2^2+t_2+1)} > 0,$$
   $$c(t_1) - c(t_2) = \frac{(t_2 - t_1)(15 t_1 t_2 - 9(t_1 + t_2) - 24)}{14(t_1^2+t_1+1)(t_2^2+t_2+1)} > 0.$$
   Hence $a, b, c$ are each injective on $\{t \in \mathbb{N} : t \ge 20\}$.

### Step 3: Pigeonhole Extension
Given any finite set $S \subset (0, 1) \cap \mathbb{Q}$, among the $3|S| + 1$ integers $t \in [20,\; 20 + 3|S|]$, each of $a(t), b(t), c(t)$ hits $S$ for at most $|S|$ values of $t$ (by injectivity). Thus at least one $t \ge 20$ satisfies $\{a(t), b(t), c(t)\} \cap S = \emptyset$. Adjoining $\{a(t), b(t), c(t)\}$ increases $|S|$ by $3$, adds $3/2$ to $\sum x^2$, and adds $9/8$ to $\sum x^4$, preserving the design equations. Starting from $S_{17}$, $S_{18}$, or $S_{19}$ according to $N \bmod 3$ yields a $(2N + 1)$-point design for every $N \ge 17$.

---

## 2. Self-Contained 2-Adic Proof of Non-Existence for $N \le 16$

Write $M = 2N + 1$ (odd) and clear denominators: $x_i = y_i / D$ with $D \ge 1$, $y_i \in \mathbb{Z}$, minimal so that if $2 \mid D$ then at least one $y_i$ is odd. The equations become
$$4\sum_{i=1}^N y_i^2 = M D^2, \qquad 16\sum_{i=1}^N y_i^4 = 3 M D^4.$$
Let $r = \#\{i : y_i \text{ odd}\}$. Since $y^4 \equiv 1 \pmod{16}$ for odd $y$ and $y^4 \equiv 0 \pmod{16}$ for even $y$, we have $\sum y_i^4 \equiv r \pmod{16}$.
- **Case $2 \nmid D$ ($e = 0$):** $M D^2$ is odd, contradicting $4 \mid M D^2$.
- **Case $D = 2 D_1$ with $D_1$ odd ($e = 1$):** Dividing by $4$ and $16$ gives $\sum y_i^2 = M D_1^2$ and $\sum y_i^4 = 3 M D_1^4$. Since $D_1^2 \equiv D_1^4 \equiv 1 \pmod 8$, reducing mod $8$ yields $r \equiv 3M \pmod 8$ and $r + 4j \equiv M \pmod 8$ (where $j = \#\{i : y_i \equiv 2 \pmod 4\}$), hence $2M + 4j \equiv 0 \pmod 8$, contradicting $M$ odd.
- **Case $4 \mid D$ ($e \ge 2$, $D = 4 D_2$):** Now $\sum y_i^4 = 48 M D_2^4 \equiv 0 \pmod{16}$, so $16 \mid r$. Since $1 \le r \le N \le 16$, we must have $r = N = 16$ (so $M = 33$ and every $y_i$ is odd). Write $y_i^2 = 1 + 8 t_i$ ($t_i \in \mathbb{Z}$), $T_1 = \sum t_i$, $T_2 = \sum t_i^2$. Then
  $$16 + 8 T_1 = 4 M D_2^2, \qquad 16 + 16 T_1 + 64 T_2 = 48 M D_2^4.$$
  - If $D_2$ is odd ($e = 2$), then $4 M D_2^2 \equiv 4 \pmod 8$, contradicting $16 + 8 T_1 \equiv 0 \pmod 8$.
  - If $D_2$ is even ($e \ge 3$), then $16 \mid 16 + 8 T_1$ forces $T_1$ even, whereas $256 \mid 16 + 16 T_1 + 64 T_2$ gives $1 + T_1 + 4 T_2 \equiv 0 \pmod{16}$, forcing $T_1$ odd — contradiction. $\square$

---

## 3. Machine Verification

- **Lean 4:** [MishimaLuSawaUchida5Design.lean](../../lean/Conjectures/MishimaLuSawaUchida5Design.lean) formally verifies `mishima_problem_8_3_37_design`, `exists_odd_5design_of_ge_17`, `not_exists_odd_5design_of_le_16`, and `mishima_odd_5design_iff` from first principles with zero `sorry` and standard axioms only.
- **Python:** `python -O -W error results/mishima-lu-sawa-uchida-5design/verify.py` verifies all base designs, exact quadrature moments $k = 0,\dots,5$, polynomial block identities, explicit designs for all $17 \le N \le 80$, and all 2-adic residue claims.
