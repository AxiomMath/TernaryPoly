module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BadLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ExplicitBinaryAction

@[expose] public section


/-!
# Levi equivariance of the Kostant pairing of the bad line

The Levi group `ℤˣ × Γ₁'(3)` of the bad line acts on `H¹(U, V) ≅ Sym^{n+1}` through
`binaryLeviRepresentation` (the determinant twist `0`, the unit `ℤˣ` acting trivially).  The
dual factor is the `H¹` of the upper plane radical, on which `GL₂(ℤ)` acts through
`upperRadicalH1Levi` (the twist `-1`).  The Kostant pairing `badLineKostant` of the bad line is
`1/3` of the apolar pairing of `σ (coord c)` and `coord c'`; since the exchange `σ` of the two
variables conjugates `γ` to `σ γ σ⁻¹`, the pairing is equivariant for the pair `(m, M')` with

  `σ m σ M'ᵀ = 1`,   i.e.  `M' = σ m^{-T} σ`        (`σ = [[0,1],[1,0]]`),

with the determinant character `det(M')⁻¹ = det m` (`badLineKostant_levi`).  Here `M'` is the matrix
by which the level involution `φ(ℓ) = a ℓ^{-T} a⁻¹` of the Levi element `ℓ = diag(u, m)` acts on the
dual radical in the frame `badFrame`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

/-- **Levi equivariance of the bad-line Kostant pairing, complex form.**  If
`σ γ σ M'ᵀ = 1` for `γ = binaryIntegralComplex m` then
`K(m ⋆ c, M' ⋆ c') = det(M')⁻¹ K(c, c')`. -/
theorem badLineKostant_levi_complex (n : ℕ) (positive : 0 < n)
    (m : ℤˣ × binaryArithmeticLevel) (M' : GeneralLinearGroup (Fin 2) ℤ)
    (h : swap01 * ((binaryIntegralComplex m.2.val : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) *
        swap01 * ((GeneralLinearGroup.map (Int.castRingHom ℂ) M' : Binary.GL2) :
          Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 1)
    (c : BadH1 n) (c' : groupCohomology.H1 (upperRadicalLatticeRep n)) :
    badLineKostant n positive
        (leviCrossedH1Representation integralBadLineSplitting.conjAct
          (standardBadLineRepresentation n) m c) (upperRadicalH1Levi n M' c') =
      ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) M') : ℂˣ) : ℂ) ^
          (-1 : ℤ) * badLineKostant n positive c c' := by
  have hmat : ((swapUnit * binaryIntegralComplex m.2.val * swapUnit⁻¹ : Binary.GL2) :
      Matrix (Fin 2) (Fin 2) ℂ) *
      ((GeneralLinearGroup.map (Int.castRingHom ℂ) M' : Binary.GL2) :
        Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 1 := h
  have e := binApolar_homogeneousAction (n + 1) 0 (-1) _ _ hmat
    (binarySwapVar (n + 1) (explicitRadicalBinaryEquiv n positive c))
    (upperRadicalH1Coordinate n c')
  rw [badLineKostant_apply n positive
      (leviCrossedH1Representation integralBadLineSplitting.conjAct
        (standardBadLineRepresentation n) m c) (upperRadicalH1Levi n M' c'),
    explicitRadicalBinaryEquiv_equivariant n positive m c, upperRadicalH1Coordinate_equivariant]
  change (1 / 3 : ℂ) * binApolar (n + 1) (binarySwapVar (n + 1)
    (Binary.homogeneousAction (n + 1) 0 (binaryIntegralComplex m.2.val)
      (explicitRadicalBinaryEquiv n positive c))) _ = _
  rw [binarySwapVar_action, e, zpow_zero, one_mul, badLineKostant_apply n positive c c']
  ring

/-- The matrix `[[0,1],[1,0]]` over `ℤ`. -/
def swapInt : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- The integral form of the relation `σ m σ M'ᵀ = 1` implies the complex form. -/
theorem levi_relation_complex (m M' : GeneralLinearGroup (Fin 2) ℤ)
    (h : swapInt * (m : Matrix (Fin 2) (Fin 2) ℤ) * swapInt *
      (M' : Matrix (Fin 2) (Fin 2) ℤ)ᵀ = 1) :
    swap01 * ((binaryIntegralComplex m : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) * swap01 *
      ((GeneralLinearGroup.map (Int.castRingHom ℂ) M' : Binary.GL2) :
        Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 1 := by
  have hs : swapInt.map (Int.castRingHom ℂ) = swap01 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swapInt, swap01]
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ) = 1 :=
    Matrix.map_one (Int.castRingHom ℂ) (map_zero _) (map_one _)
  have h2 : (swapInt * (m : Matrix (Fin 2) (Fin 2) ℤ) * swapInt *
      (M' : Matrix (Fin 2) (Fin 2) ℤ)ᵀ).map (Int.castRingHom ℂ) =
      (1 : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ) := by
    rw [h]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hs, h1] at h2
  rw [binaryIntegralComplex, GeneralLinearGroup.val_map_apply, GeneralLinearGroup.val_map_apply,
    ← Matrix.transpose_map]
  exact h2

/-- **Levi equivariance of the bad-line Kostant pairing, integral form.**  For `m` in the bad-line
Levi group and `M' ∈ GL₂(ℤ)` with `σ m σ M'ᵀ = 1` (that is `M' = σ m^{-T} σ`),
`K(m ⋆ c, M' ⋆ c') = det(M')⁻¹ K(c, c')`; here `det(M')⁻¹ = det m`. -/
theorem badLineKostant_levi (n : ℕ) (positive : 0 < n)
    (m : ℤˣ × binaryArithmeticLevel) (M' : GeneralLinearGroup (Fin 2) ℤ)
    (h : swapInt * ((m.2.val : GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      swapInt * (M' : Matrix (Fin 2) (Fin 2) ℤ)ᵀ = 1)
    (c : BadH1 n) (c' : groupCohomology.H1 (upperRadicalLatticeRep n)) :
    badLineKostant n positive
        (leviCrossedH1Representation integralBadLineSplitting.conjAct
          (standardBadLineRepresentation n) m c) (upperRadicalH1Levi n M' c') =
      ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) M') : ℂˣ) : ℂ) ^
          (-1 : ℤ) * badLineKostant n positive c c' :=
  badLineKostant_levi_complex n positive m M' (levi_relation_complex m.2.val M' h) c c'

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
