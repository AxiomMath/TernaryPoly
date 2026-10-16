module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalScalingMatrices

@[expose] public section


open CategoryTheory MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice LatticeTopCohomology
open RelativeStabilizerParameters RelativeStabilizerMatrices PolynomialGLAction
open SymmetricLineCohomology RadicalTopCohomology

/-- Every actual rational coefficient action is an invertible linear substitution. -/
def homogeneousLinearEquiv (n : ℕ) (e : ℤ) (D : GL3) : H n ≃ₗ[ℚ] H n where
  toLinearMap := homogeneousAction n e D
  invFun := homogeneousAction n e D⁻¹
  left_inv v := by
    change homogeneousAction n e D⁻¹ (homogeneousAction n e D v)=v
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one]
    rfl
  right_inv v := by
    change homogeneousAction n e D (homogeneousAction n e D⁻¹ v)=v
    rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one]
    rfl

/-- Actual polynomial coefficients on the integral step-three plane lattice. -/
abbrev scaledPlaneRep (n : ℕ) : Rep ℚ Lattice := Rep.res (scaleLattice 3) (planeRep n)

/-- Actual polynomial coefficients on the integral step-three line lattice. -/
abbrev scaledLineRep (n : ℕ) : Rep ℚ Lattice := Rep.res (scaleLattice 3) (lineRep n)

theorem planeScale_intertwine (n : ℕ) (g : Lattice) :
    (homogeneousLinearEquiv n 0 planeScale).toLinearMap ∘ₗ (scaledPlaneRep n).ρ g=
      (planeRep n).ρ g ∘ₗ (homogeneousLinearEquiv n 0 planeScale).toLinearMap := by
  change homogeneousAction n 0 planeScale*
    homogeneousAction n 0 (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (planeHom (scaleLattice 3 g)))=
    homogeneousAction n 0 (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (planeHom g))*
      homogeneousAction n 0 planeScale
  rw [←map_mul,←map_mul,planeScale_radical]

theorem lineScale_intertwine (n : ℕ) (g : Lattice) :
    (homogeneousLinearEquiv n (-1) lineScale).toLinearMap ∘ₗ (scaledLineRep n).ρ g=
      (lineRep n).ρ g ∘ₗ (homogeneousLinearEquiv n (-1) lineScale).toLinearMap := by
  change homogeneousAction n (-1) lineScale*(lineRep n).ρ (scaleLattice 3 g)=
    (lineRep n).ρ g*homogeneousAction n (-1) lineScale
  rw [←lineHom_action_twist n (-1),←lineHom_action_twist n (-1)]
  change homogeneousAction n (-1) lineScale*
    homogeneousAction n (-1) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (lineHom (scaleLattice 3 g)))=
    homogeneousAction n (-1) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (lineHom g))*
      homogeneousAction n (-1) lineScale
  rw [←map_mul,←map_mul,lineScale_radical]

/-- Rational coordinate scaling is an actual group-cohomology isomorphism. -/
def scaledPlaneH1Iso (n : ℕ) :
    groupCohomology (scaledPlaneRep n) 1 ≅ groupCohomology (planeRep n) 1 :=
  groupCohomology.mapIso (MulEquiv.refl Lattice) (homogeneousLinearEquiv n 0 planeScale)
    (planeScale_intertwine n) 1

/-- Rational coordinate scaling identifies the actual step-three line H¹ with the original H¹. -/
def scaledLineH1Iso (n : ℕ) :
    groupCohomology (scaledLineRep n) 1 ≅ groupCohomology (lineRep n) 1 :=
  groupCohomology.mapIso (MulEquiv.refl Lattice) (homogeneousLinearEquiv n (-1) lineScale)
    (lineScale_intertwine n) 1

/-- The literal plane normalizer acts also on the actual scaled coefficient representation. -/
def scaledPlaneCoefficientHom (n : ℕ) (M : GL2) :
    Rep.res (matrixLattice M⁻¹).toMonoidHom (scaledPlaneRep n) ⟶ scaledPlaneRep n :=
  Rep.ofHom ⟨integralAction n 0 (planeElement M 0),by
    intro g
    change integralAction n 0 (planeElement M 0)*
        integralAction n 0 (planeHom (scaleLattice 3 (matrixLattice M⁻¹ g)))=
      integralAction n 0 (planeHom (scaleLattice 3 g))*integralAction n 0 (planeElement M 0)
    rw [scaleLattice_matrix,←map_mul,←map_mul,plane_inverse_commute]⟩

/-- The literal line normalizer acts on the actual scaled coefficient representation. -/
def scaledLineCoefficientHom (n : ℕ) (t : ℤˣ) (M : GL2) :
    Rep.res (leviLatticeChange t M) (scaledLineRep n) ⟶ scaledLineRep n :=
  Rep.ofHom ⟨integralAction n (-1) (lineElement t 0 M),by
    intro g
    change integralAction n (-1) (lineElement t 0 M)*
        (lineRep n).ρ (scaleLattice 3 (leviLatticeChange t M g))=
      (lineRep n).ρ (scaleLattice 3 g)*integralAction n (-1) (lineElement t 0 M)
    rw [scaleLattice_lineLevi,←lineHom_action_twist n (-1),←lineHom_action_twist n (-1),
      ←map_mul,←map_mul,leviLatticeChange_commute]⟩

def scaledPlaneH1Action (n : ℕ) (M : GL2) :
    groupCohomology (scaledPlaneRep n) 1 ⟶ groupCohomology (scaledPlaneRep n) 1 :=
  groupCohomology.map (matrixLattice M⁻¹).toMonoidHom (scaledPlaneCoefficientHom n M) 1

def scaledLineH1Action (n : ℕ) (t : ℤˣ) (M : GL2) :
    groupCohomology (scaledLineRep n) 1 ⟶ groupCohomology (scaledLineRep n) 1 :=
  groupCohomology.map (leviLatticeChange t M) (scaledLineCoefficientHom n t M) 1

end TernaryPoly.OrdinaryFaceRadical
