module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.TopCohomologyPlane

@[expose] public section


open CategoryTheory Matrix
noncomputable section
namespace TernaryPoly.RadicalTopCohomology
open LatticeTopCohomology RadicalFirstCohomologyLattice RadicalCoinvariantAlgebra
open RelativeStabilizerParameters RelativeStabilizerMatrices

/-- The actual two line-radical differences. -/
theorem lineRelations_eq (n : ℕ) : relations (lineRep n) = actualLineRelations n := by
  change LinearMap.range (PolynomialGLAction.integralAction n 0 (lineHom first) - (LinearMap.id : H n →ₗ[ℚ] H n)) ⊔
    LinearMap.range (PolynomialGLAction.integralAction n 0 (lineHom second) - (LinearMap.id : H n →ₗ[ℚ] H n)) = _
  rw [lineHom_first, lineHom_second]
  rfl

def lineQuotientCoordinates (n : ℕ) :
    ((lineRep n) ⧸ relations (lineRep n)) ≃ₗ[ℚ] (H n ⧸ actualLineRelations n) :=
  Submodule.quotEquivOfEq _ _ (lineRelations_eq n)

def lineH2Iso (n : ℕ) :
    groupCohomology (lineRep n) 2 ≅ ModuleCat.of ℚ (H n ⧸ actualLineRelations n) :=
  explicitQuotientIso (lineRep n) ≪≫ (lineQuotientCoordinates n).toModuleIso

/-- Inverse diagonal conjugation on the actual ordered line-root parameters. -/
def lineLattice (ε : ℤˣ × ℤˣ) : Lattice ≃* Lattice where
  toFun g := Multiplicative.ofAdd (rootScale ε 0 * g.toAdd.1, rootScale ε 1 * g.toAdd.2)
  invFun g := Multiplicative.ofAdd (rootScale ε 0 * g.toAdd.1, rootScale ε 1 * g.toAdd.2)
  left_inv g := by
    rcases ε with ⟨a,b⟩
    rcases Int.units_eq_one_or a with rfl | rfl <;>
      rcases Int.units_eq_one_or b with rfl | rfl <;> simp [rootScale]
  right_inv g := by
    rcases ε with ⟨a,b⟩
    rcases Int.units_eq_one_or a with rfl | rfl <;>
      rcases Int.units_eq_one_or b with rfl | rfl <;> simp [rootScale]
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    simp [mul_add]

theorem line_inverse_commute (ε : ℤˣ × ℤˣ) (g : Lattice) :
    diagonalHom ε * lineHom (lineLattice ε g) = lineHom g * diagonalHom ε := by
  rcases ε with ⟨a,b⟩
  rcases Int.units_eq_one_or a with rfl | rfl <;>
    rcases Int.units_eq_one_or b with rfl | rfl <;>
    apply Units.ext <;> rw [Units.val_mul, Units.val_mul] <;>
    ext i j <;> rw [Matrix.mul_apply, Matrix.mul_apply] <;>
    fin_cases i <;> fin_cases j <;>
    simp [diagonalHom, lineHom, lineLattice, rootScale, lineMatrix, bbMatrix,
      Fin.sum_univ_three]

def lineCoefficientHom (n : ℕ) (ε : ℤˣ × ℤˣ) :
    Rep.res (lineLattice ε).toMonoidHom (lineRep n) ⟶ lineRep n :=
  Rep.ofHom ⟨PolynomialGLAction.integralAction n 0 (diagonalHom ε), fun g => by
    change PolynomialGLAction.integralAction n 0 (diagonalHom ε) *
      PolynomialGLAction.integralAction n 0 (lineHom (lineLattice ε g)) =
      PolynomialGLAction.integralAction n 0 (lineHom g) *
        PolynomialGLAction.integralAction n 0 (diagonalHom ε)
    rw [← map_mul, ← map_mul, line_inverse_commute]⟩

/-- Actual degree-two group-cohomology action of the line diagonal normalizer. -/
def lineH2Action (n : ℕ) (ε : ℤˣ × ℤˣ) :
    groupCohomology (lineRep n) 2 ⟶ groupCohomology (lineRep n) 2 :=
  groupCohomology.map (lineLattice ε).toMonoidHom (lineCoefficientHom n ε) 2

theorem lineQuotientCoordinates_action (n : ℕ) (ε : ℤˣ × ℤˣ)
    (q : (lineRep n) ⧸ relations (lineRep n)) :
    lineQuotientCoordinates n (quotientCoefficientMap (lineLattice ε) (lineCoefficientHom n ε) q) =
      lineQuotientDiagonal n ε (lineQuotientCoordinates n q) := by
  obtain ⟨p,rfl⟩ := Submodule.Quotient.mk_surjective (relations (lineRep n)) q
  rfl

theorem line_latticeDeterminant (ε : ℤˣ × ℤˣ) :
    (latticeDeterminant (lineLattice ε) : ℚ) = lineRootDual ε := by
  rcases ε with ⟨a,b⟩
  rcases Int.units_eq_one_or a with rfl | rfl <;>
    rcases Int.units_eq_one_or b with rfl | rfl <;>
    simp [latticeDeterminant, lineLattice, first, second, rootScale,
      lineRootDual_formula, unitScalar]

/-- The actual H² action has the line root-dual character. -/
theorem lineH2Iso_action (n : ℕ) (ε : ℤˣ × ℤˣ) (v : groupCohomology (lineRep n) 2) :
    (lineH2Iso n).hom (lineH2Action n ε v) =
      lineRootDual ε • lineQuotientDiagonal n ε ((lineH2Iso n).hom v) := by
  change lineQuotientCoordinates n ((explicitQuotientIso (lineRep n)).hom
      (groupCohomology.map (lineLattice ε).toMonoidHom (lineCoefficientHom n ε) 2 v)) = _
  rw [explicitQuotientIso_natural, map_zsmul, lineQuotientCoordinates_action]
  rw [← Int.cast_smul_eq_zsmul ℚ, line_latticeDeterminant]
  rfl

/-- Every vector fixed by the actual diagonal action on line-radical H² is zero. -/
theorem lineH2_fixed_zero (n : ℕ) (v : groupCohomology (lineRep n) 2)
    (hv : ∀ ε : ℤˣ × ℤˣ, lineH2Action n ε v = v) : v = 0 := by
  apply (ModuleCat.mono_iff_injective (lineH2Iso n).hom).mp inferInstance
  rw [map_zero]
  apply lineQuotient_twisted_fixed_zero
  intro ε
  rw [← lineH2Iso_action, hv ε]

end TernaryPoly.RadicalTopCohomology
