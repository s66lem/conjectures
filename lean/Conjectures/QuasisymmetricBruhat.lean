import Conjectures.QuasisymmetricBruhat.Counterexample

/-!
# Disproof of Bansal's Conjecture C / 6.11 (arXiv:2611.02210)

Conjecture C: every zigzag lower interval `[∅, Z]` of the quasisymmetric Bruhat order is
shellable.  It fails for `Z = (1, 2, 4)`: the open interval `(x, Z)` with
`x = (0, 1, 0, 1, 1, 0, 1)` is the disjoint union of two hexagons, and by Fact 6.1 a shelling of
`[∅, Z]` would restrict to a shelling of `[x, Z]`.  The zigzags `(m - 6, 2, 4)` lie above `Z`,
so the conjecture fails in every rank `m ≥ 7`.

Modules:
* `Code`, `Structure`: codes (Definition 2.4) and the reconstructed indexed forests.
* `Poly`: forest polynomials from valid labelings (Definition 2.3), Fact 2.5.
* `Ops`, `DTheorem`: `Rᵢ`, `Dⱼ = R_{j+1} - Rⱼ` and `Dⱼ P_F = [j terminal] xⱼ P_{F/j}`.
* `Basis`, `Coef`: unique forest expansions and exact computable Monk coefficients.
* `Order`: Monk covers (Definition 2.7), the order, zigzag forests (Definition 6.8).
* `Shellability`: shellability, Fact 6.1, the disconnection obstruction.
* `Raise`, `Counterexample`: the counterexample and the infinite family.
-/

#print axioms QuasisymmetricBruhat.Z_is_zigzag
#print axioms QuasisymmetricBruhat.open_interval_x_Z_disconnected
#print axioms QuasisymmetricBruhat.lowerInterval_Z_not_shellable
#print axioms QuasisymmetricBruhat.not_bansal_conjecture_C
#print axioms QuasisymmetricBruhat.bansal_conjecture_C_false
#print axioms QuasisymmetricBruhat.fact61_left
#print axioms QuasisymmetricBruhat.fact61_right
#print axioms QuasisymmetricBruhat.not_shellable_of_split
#print axioms QuasisymmetricBruhat.D_forestPoly
#print axioms QuasisymmetricBruhat.expansion_unique
#print axioms QuasisymmetricBruhat.coeff_codeF
