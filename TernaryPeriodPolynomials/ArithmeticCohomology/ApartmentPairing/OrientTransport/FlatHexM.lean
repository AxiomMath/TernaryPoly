module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.Nonvanish2
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ChartChange
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.FlatChambers

@[expose] public section


/-!
# The linear parts of the six chambers of the flat in the plane coordinates

For the `k`-th chamber of the compactified diagonal flat (`hexW k`), the plane coordinates `rhoE ∘ psi` (log-pivots) of the point with
simple-root parameters `(s, t)` are `hexM k · (log s, log t)` (`FlatRho.rho_chamber`).  The matrices `hexM k` have determinant
`(-1)^k · 4`-signed: `det (hexM k) = 4 · (-1)^k`, so that the chamber sign `(-1)^k` times the orientation of `hexM k` is always
positive.  `hexLam k p = hexM k (p - (1,1))` is the affine map of the square `[0,1]²` with the centre `(1,1)` sent to the origin.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33.Locality

/-- The linear parts: `ρ (chamber k (s,t)) = hexM k (log s, log t)`. -/
def hexM : Fin 6 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![!![-2, -2; 0, -2], !![0, -2; -2, -2], !![0, 2; -2, 0], !![2, 2; 2, 0], !![2, 0; 2, 2], !![-2, 0; 0, 2]]

/-- The affine map of the `k`-th square sending the centre `(1,1)` to the origin. -/
def hexLam (k : Fin 6) (p : ℝ × ℝ) : R2 :=
  mk2 (hexM k 0 0 * (p.1 - 1) + hexM k 0 1 * (p.2 - 1)) (hexM k 1 0 * (p.1 - 1) + hexM k 1 1 * (p.2 - 1))

theorem hexM_det (k : Fin 6) : (hexM k).det = if k.val % 2 = 0 then 4 else -4 := by
  fin_cases k <;> simp [hexM, Matrix.det_fin_two] <;> norm_num

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
