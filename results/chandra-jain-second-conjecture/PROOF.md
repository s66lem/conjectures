# Proof of the Second Chandra--Jain Conjecture and Exact Degree Criterion

**Target:** A. Chandra and S. R. Jain, *On The Spectral Properties of Discrete Landscape Functions*, `arXiv:2608.11372v3` (Section 5, `\label{conj:chandra-jain-second}`).

## 1. Statement

For integers $N \ge 3$ and odd $k$ with $1 \le k < N$, the discrete landscape expansion coefficient is

$$c_k(N) = \langle u_N, \psi_{N,k} \rangle = \frac{1}{4}\sqrt{\frac{2}{N}}\cot\left(\frac{k\pi}{2N}\right)\csc^2\left(\frac{k\pi}{2N}\right),$$

where $u_N(j) = j(N-j)/2$ and $\psi_{N,k}(j) = \sqrt{2/N}\sin(k\pi j/N)$. Let $d = \gcd(N, k)$ and $N_0 = N / d$.

- **Conjecture (Second Chandra--Jain Dichotomy):** Whenever $d > 1$,
  $$[\mathbb{Q}(c_k(N)) : \mathbb{Q}] \in \{\varphi(N_0),\, 2\varphi(N_0)\}.$$
- **Open Question (Arithmetic Criterion):** Determine which of $\varphi(N_0)$ or $2\varphi(N_0)$ occurs.

## 2. Main Theorems

**Theorem A (Second Chandra--Jain Dichotomy).** For every $N \ge 3$ and every odd $k$ with $1 \le k < N$ and $d = \gcd(N, k) > 1$, writing $N_0 = N/d$,
$$[\mathbb{Q}(c_k(N)) : \mathbb{Q}] \in \{\varphi(N_0),\, 2\varphi(N_0)\}.$$

**Theorem B (Exact Criterion for All Odd $1 \le k < N$).** For every $N \ge 3$ and every odd $k$ with $1 \le k < N$, let $d = \gcd(N,k)$ and $N_0 = N/d$. Then:
1. If $N_0$ is odd, then $[\mathbb{Q}(c_k(N)) : \mathbb{Q}] = \varphi(N_0)$.
2. If $N_0$ is even, then
   $$[\mathbb{Q}(c_k(N)) : \mathbb{Q}] = \begin{cases} \varphi(N_0) & \text{if every prime } p \text{ with } v_p(d) \text{ odd divides } N_0, \\ 2\varphi(N_0) & \text{otherwise.} \end{cases}$$

When $d = 1$, every prime has $v_p(d) = 0$ (even), so Theorem B recovers $[\mathbb{Q}(c_k(N)) : \mathbb{Q}] = \varphi(N)$ for all odd $k$ coprime to $N$, reproving and generalizing Q. Zhou's resolution of the first conjecture ($k = 1$).

## 3. Proof

Set $k' = k / d$. Since $k$ is odd and $1 \le k < N$, both $d$ and $k'$ are odd, $\gcd(k', N_0) = 1$, $1 \le k' < N_0$, and $N_0 \ge 2$. Define

$$f(\theta) = \frac{\cos\theta}{\sin^3\theta}.$$

Then $c := c_k(N) = \frac{1}{4}\sqrt{\frac{2}{N}}\,f\left(\frac{k'\pi}{2N_0}\right)$. Note three elementary properties of $f$:
- (F1) $f(\theta + \pi) = f(\theta)$;
- (F2) $f(-\theta) = -f(\theta)$;
- (F3) $f$ is positive and strictly decreasing on $(0, \pi/2)$.

Let $M = 8N$, $\zeta_M = e^{2\pi i / M}$, and $K = \mathbb{Q}(\zeta_M) \subset \mathbb{C}$. The extension $K/\mathbb{Q}$ is Galois with $\mathrm{Gal}(K/\mathbb{Q}) = \{\sigma_a : a \in (\mathbb{Z}/M\mathbb{Z})^\times\}$, where $\sigma_a(\zeta_M) = \zeta_M^a$.

### Step 1: Membership in $K$ and Galois Action

Set $z = \zeta_M^{2k} = e^{i k\pi / (2N)}$ and $i = \zeta_M^{2N}$. Since $\cos y = (z + z^{-1})/2$ and $\sin y = (z - z^{-1})/(2i)$, we have

$$f\left(\frac{k\pi}{2N}\right) = -4i\,\frac{z + z^{-1}}{(z - z^{-1})^3}, \qquad g := \frac{f(k\pi/(2N))}{i} = -4\,\frac{z + z^{-1}}{(z - z^{-1})^3} \in K.$$

For any $a \in (\mathbb{Z}/M\mathbb{Z})^\times$, $\sigma_a(z) = e^{i a k\pi / (2N)}$, so $\sigma_a(g) = f(a k\pi / (2N)) / i = f(a k'\pi / (2N_0)) / i$.

Next, factor $2N = m^2 \cdot 2^\epsilon \cdot \prod_{p \in S} p$, where $m \ge 1$, $\epsilon \in \{0, 1\}$, and $S$ is the finite set of odd primes with $v_p(N)$ odd. Inside $K$:
- $\sqrt{2} = \zeta_M^{N} + \zeta_M^{-N} = \zeta_8 + \zeta_8^{-1} \in K$ (since $8 \mid M$), and $\sigma_a(\sqrt{2}) = \chi_2(a)\sqrt{2}$ where $\chi_2(a) = 1$ if $a \equiv \pm 1 \pmod 8$ and $-1$ if $a \equiv \pm 3 \pmod 8$;
- $i = \zeta_M^{2N} \in K$ (since $4 \mid M$), and $\sigma_a(i) = (-1)^{(a-1)/2} i$;
- for each $p \in S$, letting $\zeta_p = \zeta_M^{M/p}$, the quadratic Gauss sum
  $$g_p = \sum_{x \in (\mathbb{Z}/p\mathbb{Z})^\times} \left(\frac{x}{p}\right)\zeta_p^x \in K$$
  satisfies $g_p^2 = (-1)^{(p-1)/2} p$ and $\sigma_a(g_p) = \left(\frac{a}{p}\right) g_p$ (by shifting the summation index $x \mapsto a^{-1}x$).

Let $r = |\{p \in S : p \equiv 3 \pmod 4\}|$. Then the product

$$\alpha := m \cdot (\sqrt{2})^\epsilon \cdot i^{1 - r} \cdot \prod_{p \in S} g_p \in K$$

satisfies $\alpha^2 = -2N$, so $\alpha = \pm i\sqrt{2N}$ (switching sign if necessary, we take $\alpha = i\sqrt{2N}$). Hence $\sigma_a(\alpha) = \chi(a)\alpha$ where the character $\chi : (\mathbb{Z}/M\mathbb{Z})^\times \to \{\pm 1\}$ is explicitly

$$\chi(a) = \chi_2(a)^\epsilon \cdot \left((-1)^{(a-1)/2}\right)^{1-r} \cdot \prod_{p \in S} \left(\frac{a}{p}\right).$$

In particular, since $c = \frac{1}{4N} \cdot \alpha \cdot g \in K$, every conjugate of $c$ is real and equals

$$\sigma_a(c) = \chi(a) \cdot \frac{1}{4}\sqrt{\frac{2}{N}}\,f\left(\frac{a k'\pi}{2N_0}\right). \tag{1}$$

Because $K/\mathbb{Q}$ is Galois, $[\mathbb{Q}(c) : \mathbb{Q}] = |\mathcal{O}|$, where $\mathcal{O} = \{\sigma_a(c) : a \in (\mathbb{Z}/M\mathbb{Z})^\times\}$.

### Step 2: Absolute Values of Conjugates and Fibre Size

Let $J' = \{j \in \mathbb{Z} : 0 < j < N_0,\; j \text{ odd},\; \gcd(j, N_0) = 1\}$.

**Claim 1.** For every $a \in (\mathbb{Z}/M\mathbb{Z})^\times$, there is a unique $j(a) \in J'$ with $a k' \equiv \pm j(a) \pmod{2N_0}$, and $|\sigma_a(c)| = c_{d j(a)}(N)$. Moreover, $a \mapsto j(a)$ maps $(\mathbb{Z}/M\mathbb{Z})^\times$ onto $J'$, and the positive numbers $c_{d j}(N)$ ($j \in J'$) are pairwise distinct.

*Proof.* Since $a$ and $k'$ are odd and $\gcd(a k', N_0) = 1$, the unique residue $r \in \{1, \dots, 2N_0 - 1\}$ with $r \equiv a k' \pmod{2N_0}$ is odd and coprime to $N_0$. Also $r \ne N_0$ (if $N_0$ is even, $r$ is odd; if $N_0 \ge 3$ is odd, $\gcd(N_0, N_0) = N_0 > 1$). If $r < N_0$, set $j = r \in J'$; then $f(a k'\pi/(2N_0)) = f(j\pi/(2N_0))$ by (F1). If $r > N_0$, set $j = 2N_0 - r \in J'$; then $f(a k'\pi/(2N_0)) = f(r\pi/(2N_0) - \pi) = -f(j\pi/(2N_0))$ by (F1)–(F2). Uniqueness holds because the residues $\pm j \pmod{2N_0}$ are distinct for $0 < j < N_0$. Distinctness and positivity of $c_{dj}(N)$ follow from (F3) since $j\pi/(2N_0) \in (0, \pi/2)$. Surjectivity follows because any $j \in J'$ is a unit mod $2N_0$, so $j (k')^{-1} \in (\mathbb{Z}/2N_0\mathbb{Z})^\times$ lifts to $(\mathbb{Z}/M\mathbb{Z})^\times$ (every prime dividing $M = 8N$ divides $2N_0$ or is coprime to $2N_0$, so $(\mathbb{Z}/M\mathbb{Z})^\times \to (\mathbb{Z}/2N_0\mathbb{Z})^\times$ is surjective by CRT). $\square$

**Claim 2.** Either $-c \in \mathcal{O}$ and $|\mathcal{O}| = 2|J'|$, or $-c \notin \mathcal{O}$ and $|\mathcal{O}| = |J'|$.

*Proof.* The absolute value map $x \mapsto |x|$ surjects $\mathcal{O}$ onto $\{c_{dj}(N) : j \in J'\}$ with each fibre contained in $\{v, -v\}$. Because $\mathrm{Gal}(K/\mathbb{Q})$ acts transitively on $\mathcal{O}$ by $\mathbb{Q}$-linear automorphisms, if some $x = \sigma(c) \in \mathcal{O}$ has $-x = \tau(c) \in \mathcal{O}$, then $-c = \sigma^{-1}\tau(c) \in \mathcal{O}$, and conversely if $-c = \rho(c) \in \mathcal{O}$ then $-\sigma(c) = \sigma\rho(c) \in \mathcal{O}$ for every $\sigma$. Thus every fibre has size $2$ if $-c \in \mathcal{O}$, and size $1$ otherwise. $\square$

**Claim 3 (Size of $J'$).** If $N_0$ is even, then $|J'| = \varphi(N_0)$. If $N_0$ is odd, then $|J'| = \varphi(N_0)/2$.

*Proof.* When $N_0$ is even, every integer coprime to $N_0$ is odd, so $J' = \{j \in (0, N_0) : \gcd(j, N_0) = 1\}$ has cardinality $\varphi(N_0)$. When $N_0 \ge 3$ is odd, $j \mapsto N_0 - j$ is an involution on $\{j \in (0, N_0) : \gcd(j, N_0) = 1\}$ swapping odd and even residues, so $|J'| = \varphi(N_0)/2$. $\square$

### Step 3: Sign-Flip Characterization

Let $U = \{a \in (\mathbb{Z}/M\mathbb{Z})^\times : a \equiv 1 \pmod{2N_0}\}$.

**Claim 4.** $-c \in \mathcal{O}$ if and only if there exists $u \in U$ with $\chi(u) = -1$.

*Proof.* By Claim 1, $\sigma_a(c) = \pm c$ forces $a k' \equiv \pm k' \pmod{2N_0}$, hence $a \equiv \pm 1 \pmod{2N_0}$ since $\gcd(k', 2N_0) = 1$.
- If $a \in U$, then $a k' - k'$ is a multiple of $2N_0$, so (1) and (F1) give $\sigma_a(c) = \chi(a) c$.
- If $a \equiv -1 \pmod{2N_0}$, write $a = -u$ with $u \in U$. By (1), (F1), and (F2), $\sigma_a(c) = -\chi(a) c = -\chi(-1)\chi(u) c$. Because $\sigma_{-1}$ is complex conjugation and $\alpha = i\sqrt{2N}$ is purely imaginary, $\chi(-1) = -1$, whence $\sigma_a(c) = \chi(u) c$.

Therefore $\sigma_a(c) = -c$ occurs if and only if $\chi(u) = -1$ for some $u \in U$. $\square$

### Step 4: Evaluating $\chi$ on $U$ (Proof of Theorems A and B)

Write $N_0 = 2^e u_0$ with $u_0$ odd and $e \ge 0$. Recall $d$ is odd, so $N = 2^e u_0 d$ and $2N = 2^{e+1} u_0 d$.

**Case 1: $N_0$ is odd ($e = 0$).**
Then $N = u_0 d$ is odd, $\gcd(8, N) = 1$, and $\epsilon = 1$ (since $v_2(2N) = 1$). By the Chinese Remainder Theorem, choose $a \in (\mathbb{Z}/M\mathbb{Z})^\times$ with $a \equiv 1 \pmod N$ and $a \equiv 5 \pmod 8$.
- Since $a \equiv 1 \pmod{N_0}$ and $a$ is odd, $a \equiv 1 \pmod{2N_0}$, so $a \in U$.
- Since $a \equiv 5 \pmod 8$, $\chi_2(a) = -1$ and $(-1)^{(a-1)/2} = (-1)^2 = 1$.
- For every odd prime $p \in S$, $p \mid N$, so $a \equiv 1 \pmod p$ and $\left(\frac{a}{p}\right) = 1$.

Hence $\chi(a) = -1$. By Claims 2, 3, and 4, $[\mathbb{Q}(c) : \mathbb{Q}] = 2 \cdot (\varphi(N_0)/2) = \varphi(N_0)$.

**Case 2: $N_0$ is even ($e \ge 1$).**
First, Claims 2 and 3 already give $[\mathbb{Q}(c) : \mathbb{Q}] \in \{\varphi(N_0), 2\varphi(N_0)\}$, establishing Theorem A.

For Theorem B, consider any $a \in U$, so $a \equiv 1 \pmod{2^{e+1} u_0}$:
- If $e$ is odd, then $e + 1$ is even, so $\epsilon = 0$ (no $\sqrt{2}$ factor) and $4 \mid 2^{e+1}$, so $a \equiv 1 \pmod 4$, giving $(-1)^{(a-1)/2} = 1$.
- If $e$ is even, then $e \ge 2$, so $8 \mid 2^{e+1}$, hence $a \equiv 1 \pmod 8$, giving both $\chi_2(a) = 1$ and $(-1)^{(a-1)/2} = 1$.

In both subcases, every $a \in U$ satisfies

$$\chi(a) = \prod_{p \in S} \left(\frac{a}{p}\right).$$

For every $p \in S$ that divides $N_0$ (equivalently $p \mid u_0$), $a \equiv 1 \pmod p$, so $\left(\frac{a}{p}\right) = 1$. The remaining primes in $S$ are precisely the primes $p$ with $p \nmid N_0$ and $v_p(N) = v_p(d)$ odd. Let $S_{\mathrm{ext}} = \{p \in S : p \nmid N_0\}$. Then for all $a \in U$,

$$\chi(a) = \prod_{p \in S_{\mathrm{ext}}} \left(\frac{a}{p}\right).$$

- If $S_{\mathrm{ext}} = \emptyset$ (every prime $p$ with $v_p(d)$ odd divides $N_0$), then $\chi(a) = 1$ for all $a \in U$, so $-c \notin \mathcal{O}$ and $[\mathbb{Q}(c) : \mathbb{Q}] = \varphi(N_0)$.
- If there exists $p_0 \in S_{\mathrm{ext}}$, then $p_0$ is an odd prime not dividing $2N_0$. Let $r$ be a quadratic non-residue modulo $p_0$, and let $M = p_0^t M'$ with $\gcd(p_0, M') = 1$. Note $2N_0 \mid M'$ since $p_0 \nmid 2N_0$, and every $p \in S_{\mathrm{ext}} \setminus \{p_0\}$ divides $M'$. By CRT, choose $a \in (\mathbb{Z}/M\mathbb{Z})^\times$ with $a \equiv r \pmod{p_0^t}$ and $a \equiv 1 \pmod{M'}$. Then $a \in U$, $\left(\frac{a}{p_0}\right) = -1$, and $\left(\frac{a}{p}\right) = 1$ for all other $p \in S_{\mathrm{ext}}$, so $\chi(a) = -1$. Hence $-c \in \mathcal{O}$ and $[\mathbb{Q}(c) : \mathbb{Q}] = 2\varphi(N_0)$. $\square$
