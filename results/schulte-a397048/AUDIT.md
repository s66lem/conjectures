# Independent Adversarial Audit — Werner Schulte's OEIS A397048 Conjectures

- **Auditor:** Independent cross-model adversarial review (`claude-sonnet-5-5`, read-only audit, 26 Nov 2026)
- **Final Verdict:** **PASS** (all mathematical, Lean 4, OEIS-fidelity, and verification checks passed on first audit; the single documentation blocker — adding this `AUDIT.md` file referenced by `README.md` — and the Zenodo prior-art check were completed below).

## Verification Summary

1. **Lean 4 Build & Axioms (`lean/Conjectures/SchulteA397048.lean`):**
   - Built via `lake build Conjectures.SchulteA397048` under `gpu_lock --slot ram` with `LEAN_NUM_THREADS=1`: **exit 0**, 0 errors, 0 warnings.
   - `#print axioms` on all 9 exported theorems (`stirling1_falling_expansion`, `stirling2_falling_expansion`, `T_c_eq_stirling_sum`, `schulte_A397048_conj1`, `schulte_A397048_conj2`, `schulte_A397048_conj3`, and supporting shift/evaluation lemmas) uses strictly standard axioms `[propext, Classical.choice, Quot.sound]`.
   - Forbidden-token grep (`sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `admit`, `set_option`, `opaque`, `extern`, `macro`, `elab`): **0 hits**.
   - Imported in `lean/Conjectures.lean`.
2. **OEIS Definition Fidelity (Live Fetch):**
   - Verified `T_c n n k` matches OEIS A397048's live formula `T(n, k) = (∑_{i=0}^k (-1)^i C(k, i) (n + i)^n) (-1)^k / k!`.
   - Verified `stirling1` (signed A048994), `stirling2` (A048993), `bellNumber` (A000110), and `A134980` (`∑ C(n, k) n^(n - k) B_k`) match live OEIS conventions, and verified exact divisibility `(k - i)! ∣ k!` in Conjecture 3 for all `k` (including `k > n`).
3. **Independent Computation (`results/schulte-a397048/verify.py`):**
   - `python -O -W error results/schulte-a397048/verify.py` exits 0 with 0 `assert` statements, checking all 3 conjectures for `n ≤ 40` and the general base-point `c` shift theorem for `c, n ≤ 14` (4,424 exact identities).
4. **Openness & Prior Art (26 Nov 2026):**
   - Live OEIS A397048 labels all three formulas as "Conjecture".
   - `the-omega-institute/trureturing`: only a note-only triage mention (`oeis2026triage0910.md`), no proof or Lean formalization.
   - Zenodo API search (authenticated browser session, `/api/records?q=A397048`): **0 hits**.
5. **Preprint & Documentation:**
   - `paper.tex` / `paper.pdf` (`\author{Salem Levinstein}`, no `\thanks`, 0 TeX warnings), 0 `\operatorname` in `.md` files.
