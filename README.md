# Solved conjectures in combinatorics, graph theory, and number theory

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24519466.svg)](https://doi.org/10.5281/zenodo.24519466)

Mathematical proofs, counterexamples, and reproducible verification code for open conjectures in combinatorics, algorithmic game theory, graph theory, and number theory.

Each result directory contains a self-contained proof (`PROOF.md`), an internal mathematical and source audit (`AUDIT.md`), an independent Python 3 verifier (`verify.py`), and (where applicable) an arXiv-ready LaTeX manuscript (`paper.tex`).

## Results

| Problem | Outcome | Preprint | Verification |
| :--- | :--- | :---: | :---: |
| **1.** [Fanelli–Moscardelli stability threshold conjecture](results/fanelli-moscardelli/) | Disproved for all odd $N \ge 7$ | [DOI](https://doi.org/10.5281/zenodo.24519727) | **Lean 4** · Audit · Python · DRAT SAT |
| **2.** [Csernák–Soukup tree stacking conjecture & literal ASH](results/csernak-soukup-tree-stacking/) | Conj. 5.6 proved; literal Hyp. 3.2 disproved | [DOI](https://doi.org/10.5281/zenodo.24519728) | **Lean 4** · Audit · Python BFS |
| **3.** [Allie–Du Preez–Hefty–Mafunda tree remoteness conjecture](results/allie-dupreez-hefty-mafunda-remoteness/) | Disproved (infinite family + $k=8$ minimizer) | [DOI](https://doi.org/10.5281/zenodo.24519729) | **Lean 4** · Audit · Python BFS |
| **4.** [Firoozbakht’s OEIS A108569 parity conjecture](results/firoozbakht-oeis-a108569/) | Disproved (infinite odd family) | [DOI](https://doi.org/10.5281/zenodo.24536214) | **Lean 4** · Audit · Python |
| **5.** [Rossi rank score veto core distortion conjecture](results/rossi-veto-core-distortion/) | Proved (exact distortion $1 + 2(\|\mathbf{s}\|_1 - s_m)$) | [DOI](https://doi.org/10.5281/zenodo.24536065) | **Lean 4** · Cross-Model Audit · Python |
| **6.** [Togni multi-label radio labeling conjectures](results/togni-multilabel-radio/) | Conj. 2 proved (all $k, m$); Conj. 1 upper bound & exact $k=3$ | [DOI](https://doi.org/10.5281/zenodo.24536068) | **Lean 4** · Cross-Model Audit · Python |
| **7.** [Maharaj 1D discrete Voronoi game conjecture](results/maharaj-voronoi-game/) | Disproved for all $\ell \ge 3$; exact $k^*(\ell) = 2\ell - 1$ | [DOI](https://doi.org/10.5281/zenodo.24536074) | **Lean 4** · Cross-Model Audit · Python |
| **8.** [Daga–Ramu exact Littlestone dimensions of intervals](results/daga-ramu-littlestone/) | Both conjectures proved (Conj. 31 & odd-$k$ unions) | [DOI](https://doi.org/10.5281/zenodo.24536080) | **Lean 4** · Cross-Model Audit · Python |
| **9.** [Kalmanovich–Nivasch Conjecture 9.1 on planar all-even sets](results/kalmanovich-nivasch-alleven/) | Disproved (36-point counterexample + unbounded seed family) | [DOI](https://doi.org/10.5281/zenodo.24536092) | **Lean 4** · Cross-Model Audit · Python |
| **10.** [Notik Singer Golomb ruler chamber-uniqueness conjecture](results/notik-singer-golomb/) | Proved for all prime powers (every cyclic PDS) | [DOI](https://doi.org/10.5281/zenodo.24536094) | **Lean 4** · Cross-Model Audit · Python |
| **11.** [Rofa regular spider 0-rotatability conjecture](results/rofa-spider-rotatability/) | Proved for all $k \ge 1, \ell \ge 1$ | [DOI](https://doi.org/10.5281/zenodo.24536097) | **Lean 4** · Cross-Model Audit · Python |
| **12.** [Benedetti–Menara Conjecture 7.1 ($r = 2$, flag $1$-layered families)](results/benedetti-menara-flag-layered/) | Proved $r = 2$ sharp bound $m - 1$ + halved Larman–Barnette + unconditional Thm. E(a) at $p = d - 2$ | [DOI](https://doi.org/10.5281/zenodo.24536099) | **Lean 4** · Cross-Model Audit · Python |
| **13.** [Sinclair Conjecture C (radial-derivative Hilbert series front-loading)](results/sinclair-radial-mobius/) | Disproved ($M(K_{1,1,4}+e)$: $h_2^\beta = 31 < 32 = h_3^\beta$, family $m=4..7$ + binary example) | [DOI](https://doi.org/10.5281/zenodo.24536118) | **Lean 4** · Cross-Model Audit · Python |
| **14.** [Arana–Haxell–Kaiser–Stehlík Conjecture 1.3 ($k = 3$, $G$-stable Kneser graphs)](results/arana-haxell-kaiser-stehlik-kneser/) | Proved completely for $k = 3$ (+ Schrijver $k = 3$, all-$k$ star obstruction at $4k-3$, $k = 4$ $C_m \sqcup K_1$ for $m \ge 39$) | [DOI](https://doi.org/10.5281/zenodo.24536120) | **Lean 4** · Cross-Model Audit · Python |
| **15.** [Manabe Conjecture 57 (purely periodic three-move subtraction games)](results/manabe-subtraction-games/) | Proved in full (strengthened to all $1 \le a < b < c$ at $\mathrm{P}$-position level + Conj. 52 $\iff$ Conj. 56 for all $c > b$ + $100.9\text{M}$ census) | [DOI](https://doi.org/10.5281/zenodo.24536124) | **Lean 4** · Cross-Model Audit · Python |
| **16.** [Chen–Zwicker Conjecture 1 ($\mathrm{EF1}_{\mathrm{outer}}$ spectrum of connected graphs)](results/chen-zwicker-ef1-outer/) | Disproved (minimal $8$-vertex graph $H$: `NO` at $k=2$, `YES` at $k=3$, `NO` at $k=4$ from common binary up to heterogeneous monotone) | [DOI](https://doi.org/10.5281/zenodo.24536131) | **Lean 4** · Cross-Model Audit · Python |
| **17.** [Bansal Conjecture C / 6.11 (quasisymmetric Bruhat zigzag shellability)](results/bansal-quasisymmetric-bruhat/) | Disproved for all $m \ge 7$ (minimal $Z = F(1,2,4)$, $(x,Z) \cong C_6 \sqcup C_6$, non-shellable & non-Cohen–Macaulay) | [DOI](https://doi.org/10.5281/zenodo.24536751) | **Lean 4** · Cross-Model Audit · Python |
| **18.** [González D'León–Wachs Conjecture 4.13(2) (weighted bond Möbius real-rootedness)](results/gonzalez-dleon-wachs-weighted-bond/) | Disproved (minimal $n = 8, k = 2$: $G = K_3 \sqcup \mathrm{House}$, $H = P_3 \sqcup C_5$, $\Delta = -22{,}364 < 0$ + infinite families) | [DOI](https://doi.org/10.5281/zenodo.24540271) | **Lean 4** · Audit · Python |
| **19.** [Firoozbakht’s OEIS A086766 conjecture](results/firoozbakht-oeis-a086766/) | Disproved (infinite family $n_k = 10(10^{2k}-1)/99$, minimal $1010$, primitive $104040$, and $78$-digit primitive witness) | [DOI](https://doi.org/10.5281/zenodo.24540581) | **Lean 4** · Audit · Python |
| **20.** [Capozzoli–Couto–Junchaya Conjecture 1 ($P_3^*$-interval on tournaments)](results/capozzoli-couto-junchaya-p3star-interval/) | Disproved under ETH ($2^{O(\log^4 n)}$ deterministic QP algorithm $\implies$ NP-intermediate on general & strong tournaments) | [DOI](https://doi.org/10.5281/zenodo.24540682) | **Lean 4** · Cross-Model Audit · Python |
| **21.** [Campbell’s OEIS A189409 squarefree conjecture](results/campbell-oeis-a189409/) | Disproved (minimal counterexample $a(9) = (23\#)^2 + 1 = 29^2 \cdot 53 \cdot 1{,}116{,}604{,}864{,}937$; $a(0)\dots a(8)$ certified squarefree) | [DOI](https://doi.org/10.5281/zenodo.24543512) | **Lean 4** · Cross-Model Audit · Python |
| **22.** [Fonollosa Problem 4 (unique multiset sums in finite abelian groups)](results/fonollosa-unique-multiset-sums/) | Proved (exact minimum order $|G| = 2^{n-1}$, complete classification as $(\mathbb{Z}/2\mathbb{Z})^{n-1}$ with affine basis, cyclic bound $N \ge 2^{n-1} + \lceil n/\gcd(2,N) \rceil - 1$) | [DOI](https://doi.org/10.5281/zenodo.24544750) | **Lean 4** · Cross-Model Audit · Python |
| **23.** [Gil–Liang–Odetola–Weiner Conjecture 7.4 (antidiagonal grid traffic anomaly)](results/gil-antidiagonal-traffic/) | Proved for all $n \ge 496$ ($\rho(n) < 1$, sharp at $R_{495}(240) \approx 1.000024 > 1$; Stirling-free analytic bound $n \ge 800$ + unimodal peak certificate $496 \le n \le 799$) | [DOI](https://doi.org/10.5281/zenodo.24545619) | **Lean 4** · Cross-Model Audit · Python |
| **24.** [Easlick Conjecture 1 (minimal-advantage non-transitive $n$-sided dice)](results/easlick-nontransitive-dice/) | Proved for all $n \ge 7$ (3-die zipper cycles of length $3(n-7)$ for odd $n \ge 11$, $3(n-10)$ for even $n \ge 16$, and $n+1$ for $n \in \{7,8,9,10,12,14\}$; $n = 6$ unique with $L_{\max}(G_n) = n$) | [DOI](https://doi.org/10.5281/zenodo.24546684) | **Lean 4** · Cross-Model Audit · Python |
| **25.** [Ghafari–Wanless Conjecture 3 (Wormald's Question on Latin square transversals)](results/ghafari-wanless-latin-transversals/) | Proved for every even $n \ge 22, n \ne 24$ (settling $n = 30$ and all even $n > 10\,000$ via modular $\Delta$-sum Latin squares + 8 mod-16 parametric tail families + 42 small witnesses) | [DOI](https://doi.org/10.5281/zenodo.24548884) | **Lean 4** · Cross-Model Audit · Python |
| **26.** [Mandal–Mohan Conjecture 1.19 (harmonic-type means of Fibonacci powers)](results/mandal-mohan-fibonacci-harmonic/) | Proved completely for all $n, k \ge 1$ ($n^k / \sum_{i=1}^n F_i^{-k} \in \mathbb{N} \iff n \in \{1, 2\}$ or $(n, k) = (3, 2)$ via Bertrand's postulate + strong divisibility) | [DOI](https://doi.org/10.5281/zenodo.24549268) | **Lean 4** · Cross-Model Audit · Python |
| **27.** [Zai–Lv–Sabir / Tian–Dong Conjecture 1.14 (Hamilton-connectedness of split graphs)](results/zai-lv-sabir-split-hamilton/) | Disproved for every $r \ge 5$ (22-vertex Paley $(11, 5, 2)$ biplane split graph at $r = 5$ + $(2r + 8)$-vertex circulant split family for all $r \ge 6$) | [DOI](https://doi.org/10.5281/zenodo.24549479) | **Lean 4** · Cross-Model Audit · Python |
| **28.** [Yaqubi–Mirzavaziri Conjecture 6.2 ($2$-adic valuations of $k$-tuple $\mathrm{PDO}$ partitions)](results/yaqubi-mirzavaziri-pdo/) | Proved unconditionally for every $k \ge 1$ (all $8$ classes $\bmod 8$, including exceptional $k \equiv 1, 6 \pmod 8$ via $B_k(7)$ period certificates & self-contained Jacobi/$\psi\psi(q^3)$ dissections) | [DOI](https://doi.org/10.5281/zenodo.24552279) | **Lean 4** · Cross-Model Audit · Python |
| **29.** [Clark Kimberling’s OEIS A308355 & A025065 conjectures (lex-order partition part counts)](results/kimberling-a308355/) | Complete resolution: A025065 conjecture proved for all $n \ge 1$ ($\sum_{r=0}^{\lfloor n/2 \rfloor} p(r)$); A308355 $\mathrm{A025065}(n+1)$ formula disproved for every odd $n \ge 1$ | [DOI](https://doi.org/10.5281/zenodo.24552281) | **Lean 4** · Cross-Model Audit · Python |
| **30.** [Sajid Khan Hussain’s OEIS A402341 conjecture (central polynomial $2$-adic valuations)](results/hussain-a402341/) | Proved for every even $n \ge 0$ and generalized to every power-of-two block length $2^r$ ($a_r(2m) \equiv \binom{2N}{N} \pmod{2^{s_2(N)+1}}$, $v_2(a_r(2m)) = s_2((2^r-1)m)$) | [DOI](https://doi.org/10.5281/zenodo.24552348) | **Lean 4** · Cross-Model Audit · Python |
| **31.** [Jan Snellman’s Conjecture 21 (`arXiv:2611.26110v1`, rank-two Kozlov polytope volume monotonicity)](results/snellman-kozlov-volume/) | Proved for all $n \ge 1, d \ge 0$ (explicit lower bound $\bigl(\binom{n}{d}-1\bigr)t_d(n-d)\,\mathrm{NV}(\mathrm{Koz}(n))$, strict for $0 \le d \le n - 2$ except $(n,d)=(2,0)$) | [DOI](https://doi.org/10.5281/zenodo.24553538) | **Lean 4** · Cross-Model Audit · Python |
| **32.** [Omar E. Pol’s OEIS A400974, A280940 & A384225 conjectures (symmetric representation subparts & $2$-dense divisor blocks)](results/pol-a400974/) | All four conjectures proved for every $n \ge 1$ ($\mathrm{A280940} = \mathrm{A384225}$, $\mathrm{A384222} = \mathrm{A001511}\cdot\mathrm{A384225}$, $\mathrm{A400974} = \mathrm{A001511}\cdot\mathrm{A384230}$) | [DOI](https://doi.org/10.5281/zenodo.24556521) | **Lean 4** · Cross-Model Audit · Python |

## Reproduction

All verifiers use only the Python 3 standard library:

```bash
python3 results/fanelli-moscardelli/verify.py
python3 results/csernak-soukup-tree-stacking/verify.py
python3 results/allie-dupreez-hefty-mafunda-remoteness/verify.py
python3 results/firoozbakht-oeis-a108569/verify.py
python3 results/rossi-veto-core-distortion/verify.py
python3 results/togni-multilabel-radio/verify.py
python3 results/maharaj-voronoi-game/verify.py
python3 results/daga-ramu-littlestone/verify.py
python3 results/kalmanovich-nivasch-alleven/verify.py
python3 results/notik-singer-golomb/verify.py
python3 results/rofa-spider-rotatability/verify.py
python3 results/benedetti-menara-flag-layered/verify.py
python3 results/sinclair-radial-mobius/verify.py
python3 results/arana-haxell-kaiser-stehlik-kneser/verify.py base
python3 results/manabe-subtraction-games/verify.py
python3 results/chen-zwicker-ef1-outer/verify.py
python3 results/bansal-quasisymmetric-bruhat/verify.py
python3 results/gonzalez-dleon-wachs-weighted-bond/verify.py
python3 results/firoozbakht-oeis-a086766/verify.py
python3 results/capozzoli-couto-junchaya-p3star-interval/verify.py
python3 results/campbell-oeis-a189409/verify.py
python3 results/fonollosa-unique-multiset-sums/verify.py
python3 results/gil-antidiagonal-traffic/verify.py
python3 results/easlick-nontransitive-dice/verify.py
python3 results/ghafari-wanless-latin-transversals/verify.py
python3 results/mandal-mohan-fibonacci-harmonic/verify.py
python3 results/zai-lv-sabir-split-hamilton/verify.py
python3 results/yaqubi-mirzavaziri-pdo/verify.py
python3 results/kimberling-a308355/verify.py
python3 results/hussain-a402341/verify.py
python3 results/snellman-kozlov-volume/verify.py
python3 results/pol-a400974/verify.py
```

To check the Lean 4 formalizations (Lean `v4.33.1` + Mathlib):

```bash
cd lean && lake build
```

All results are internally audited and computationally verified, but externally unrefereed; priority is not asserted.
