module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ZeroExterior

@[expose] public section



/-! The algebraic Casimir-positivity bound for degree-0 forms (`Cas_𝔭 = Σ ρ(Xᵢ)²` positive
definite on `Sym^n`, `n > 0`), and its basepoint-level coercivity consequence. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive

/-- Finite-dimensional Casimir-positivity bound: for `p` homogeneous of degree `n`, the sum of
symmetric-frame energies is at least `(n(n+9)/6) * ‖p‖²`. From `fullCoefficientCasimir`'s exact
scalar value and the upper bound on `compactCoefficientCasimir`'s energy. -/
theorem tangentFrame_energy_lower {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n) :
    (n : ℝ) * (n + 9) / 6 * factorialPairing p p ≤
      ∑ i : Fin 5, tangentWeight i *
        factorialPairing (infinitesimal (tangentFrame i) p) (infinitesimal (tangentFrame i) p) := by
  have hadj : ∀ i : Fin 5,
      factorialPairing (infinitesimal (tangentFrame i) (infinitesimal (tangentFrame i) p)) p =
        factorialPairing (infinitesimal (tangentFrame i) p) (infinitesimal (tangentFrame i) p) :=
    fun i => infinitesimal_symmetric_adjoint _ (tangentFrame_mem i).1 _ _
  have hsplit : factorialPairing (fullCoefficientCasimir p) p =
      (∑ i : Fin 5, tangentWeight i *
        factorialPairing (infinitesimal (tangentFrame i) p) (infinitesimal (tangentFrame i) p)) +
        factorialPairing (compactCoefficientCasimir p) p := by
    unfold fullCoefficientCasimir
    simp only [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul, hadj]
  rw [fullCoefficientCasimir_homogeneous hp] at hsplit
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hsplit
  have hupper := compactCoefficientCasimir_upper hp
  nlinarith [hsplit, hupper]

/-- Basepoint-level degree-0 coercivity, with the shared-looking constant `c = n(n+9)/24`:
`c * formPairing a a ≤ formPairing (symmetricExterior a) (symmetricExterior a)` at the basepoint. -/
theorem symmetric_energy_basepoint_coercive_zero {n : ℕ} (a : FormValue n 0) :
    (n : ℝ) * (n + 9) / 24 * formPairing n 0 (coordinateChart basepoint) a a ≤
      formPairing n 1 (coordinateChart basepoint)
        (symmetricExterior n 0 (coordinateChart basepoint) a)
        (symmetricExterior n 0 (coordinateChart basepoint) a) := by
  have hp : (a ![]).val.IsHomogeneous n :=
    (MvPolynomial.mem_homogeneousSubmodule n (a ![]).val).mp (a ![]).2
  rw [formPairing_basepoint_zero, formPairing_basepoint_one]
  simp only [onePairing, baseOneCoordinates, symmetricExterior_zero_basepoint]
  have heq : ∑ i : Fin 5, tangentWeight i * (factorialPairing
      ((1 / 2 : ℝ) • infinitesimal (tangentFrame i) (a ![]).val)
      ((1 / 2 : ℝ) • infinitesimal (tangentFrame i) (a ![]).val)) =
      (1 / 4 : ℝ) * ∑ i : Fin 5, tangentWeight i * factorialPairing
        (infinitesimal (tangentFrame i) (a ![]).val) (infinitesimal (tangentFrame i) (a ![]).val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  have hlower := tangentFrame_energy_lower hp
  nlinarith [hlower]

end TernaryPeriodPolynomials.Argument.Coercivity
