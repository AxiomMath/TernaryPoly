module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.TopCohomologyMatrices
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLattice
public import TernaryPeriodPolynomials.GroupCohomology.Radical.Coinvariant

@[expose] public section

open CategoryTheory Matrix
noncomputable section
namespace TernaryPoly.RadicalTopCohomology
open LatticeTopCohomology RadicalFirstCohomologyLattice RadicalCoinvariantAlgebra
open RelativeStabilizerParameters RelativeStabilizerMatrices

/-- The two lattice differences are the actual integral plane-radical relations. -/
theorem planeRelations_eq (n : ℕ) : relations (planeRep n) = actualPlaneRelations n := by
  change LinearMap.range (PolynomialGLAction.integralAction n 0 (planeHom first) - (LinearMap.id : H n →ₗ[ℚ] H n)) ⊔
    LinearMap.range (PolynomialGLAction.integralAction n 0 (planeHom second) - (LinearMap.id : H n →ₗ[ℚ] H n)) = _
  rw [planeHom_first, planeHom_second]
  rfl

def planeQuotientCoordinates (n : ℕ) :
    ((planeRep n) ⧸ relations (planeRep n)) ≃ₗ[ℚ] (H n ⧸ actualPlaneRelations n) :=
  Submodule.quotEquivOfEq _ _ (planeRelations_eq n)

def planeH2Iso (n : ℕ) :
    groupCohomology (planeRep n) 2 ≅ ModuleCat.of ℚ (H n ⧸ actualPlaneRelations n) :=
  explicitQuotientIso (planeRep n) ≪≫ (planeQuotientCoordinates n).toModuleIso

/-- The inverse lattice change is exactly the one needed for normalizer pullback. -/
theorem plane_inverse_commute (M : GL2) (g : Lattice) :
    planeElement M 0 * planeHom (matrixLattice M⁻¹ g) = planeHom g * planeElement M 0 := by
  change planeElement M 0 * planeElement 1
    ![(matrixLattice M⁻¹ g).toAdd.1,(matrixLattice M⁻¹ g).toAdd.2] = _
  rw [matrixLattice_vector, planeLevi_radical_commute, Matrix.mulVec_mulVec]
  have hm : M.val * (M⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hm, Matrix.one_mulVec]
  rfl

/-- This coefficient morphism records actual conjugation, with inverse lattice pullback. -/
def planeCoefficientHom (n : ℕ) (M : GL2) :
    Rep.res (matrixLattice M⁻¹).toMonoidHom (planeRep n) ⟶ planeRep n :=
  Rep.ofHom ⟨PolynomialGLAction.integralAction n 0 (planeElement M 0), fun g => by
    change PolynomialGLAction.integralAction n 0 (planeElement M 0) *
      PolynomialGLAction.integralAction n 0 (planeHom (matrixLattice M⁻¹ g)) =
      PolynomialGLAction.integralAction n 0 (planeHom g) *
        PolynomialGLAction.integralAction n 0 (planeElement M 0)
    rw [← map_mul, ← map_mul, plane_inverse_commute]⟩

/-- The actual normalizer action on degree-two lattice group cohomology. -/
def planeH2Action (n : ℕ) (M : GL2) :
    groupCohomology (planeRep n) 2 ⟶ groupCohomology (planeRep n) 2 :=
  groupCohomology.map (matrixLattice M⁻¹).toMonoidHom (planeCoefficientHom n M) 2

theorem planeQuotientCoordinates_action (n : ℕ) (M : GL2)
    (q : (planeRep n) ⧸ relations (planeRep n)) :
    planeQuotientCoordinates n
      (quotientCoefficientMap (matrixLattice M⁻¹) (planeCoefficientHom n M) q) =
      planeQuotientLevi n M (planeQuotientCoordinates n q) := by
  obtain ⟨p,rfl⟩ := Submodule.Quotient.mk_surjective (relations (planeRep n)) q
  rfl

theorem plane_latticeDeterminant (M : GL2) :
    (latticeDeterminant (matrixLattice M⁻¹) : ℚ) = planeLeviRootDual M := by
  rw [latticeDeterminant_matrixLattice]
  change ((M⁻¹).val.det : ℚ) = (M.val.det : ℚ)⁻¹
  have h : M.val.det * (M⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hq : (M.val.det : ℚ) * ((M⁻¹).val.det : ℚ) = 1 := by exact_mod_cast h
  apply eq_inv_of_mul_eq_one_left
  simpa [mul_comm] using hq

/-- The polynomial quotient intertwines actual H² normalizer action with the root-dual twist. -/
theorem planeH2Iso_action (n : ℕ) (M : GL2) (v : groupCohomology (planeRep n) 2) :
    (planeH2Iso n).hom (planeH2Action n M v) =
      planeLeviRootDual M • planeQuotientLevi n M ((planeH2Iso n).hom v) := by
  change planeQuotientCoordinates n ((explicitQuotientIso (planeRep n)).hom
      (groupCohomology.map (matrixLattice M⁻¹).toMonoidHom (planeCoefficientHom n M) 2 v)) = _
  rw [explicitQuotientIso_natural, map_zsmul, planeQuotientCoordinates_action]
  rw [← Int.cast_smul_eq_zsmul ℚ, plane_latticeDeterminant]
  rfl

/-- Every vector fixed by the actual plane Levi action on radical H² is zero. -/
theorem planeH2_fixed_zero (n : ℕ) (v : groupCohomology (planeRep n) 2)
    (hv : ∀ M : GL2, planeH2Action n M v = v) : v = 0 := by
  apply (ModuleCat.mono_iff_injective (planeH2Iso n).hom).mp inferInstance
  rw [map_zero]
  apply planeQuotient_twisted_fixed_zero
  intro M
  rw [← planeH2Iso_action, hv M]

end TernaryPoly.RadicalTopCohomology
