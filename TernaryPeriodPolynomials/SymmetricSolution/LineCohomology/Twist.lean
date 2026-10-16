module

public import TernaryPeriodPolynomials.SymmetricSolution.LineCohomology.Cocycles
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantLevi

@[expose] public section


open CategoryTheory MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.SymmetricLineCohomology
open RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice LatticeTopCohomology
open RelativeStabilizerParameters RelativeStabilizerMatrices groupCohomology

/-- Every actual line-radical matrix has determinant one. -/
theorem lineHom_det (g : Lattice) : (lineHom g).val.det = 1 := by
  simp [lineHom,lineElement_val,det_lineMatrix]

/-- Determinant twists coincide on the radical, for every integer exponent. -/
theorem lineHom_action_twist (n : ℕ) (e : ℤ) (g : Lattice) :
    PolynomialGLAction.integralAction n e (lineHom g) = (lineRep n).ρ g := by
  have hd : (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineHom g)).val.det = 1 := by
    calc
      _ = ((lineHom g).val.det : ℚ) := ((Int.castRingHom ℚ).map_det _).symm
      _ = 1 := by rw [lineHom_det]; rfl
  have he (k : ℤ) : PolynomialGLAction.determinantCharacter k
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineHom g)) = 1 := by
    change (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineHom g)).val.det ^ k = 1
    rw [hd,one_zpow]
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change (PolynomialGLAction.integralAction n e (lineHom g) v : Poly) =
    (PolynomialGLAction.integralAction n 0 (lineHom g) v : Poly)
  simp only [PolynomialGLAction.integralAction_coe,PolynomialGLAction.action_apply,he]

/-- The actual homogeneous coefficient representation with determinant exponent minus one. -/
abbrev twistedSubgroupRep (n : ℕ) : Rep ℚ lineRadical :=
  Rep.of ((PolynomialGLAction.integralAction n (-1)).comp lineRadical.subtype)

@[simp] theorem twistedSubgroupRep_parameter (n : ℕ) (g : Lattice) :
    (twistedSubgroupRep n).ρ (lineParamEquiv g) = (lineRep n).ρ g :=
  lineHom_action_twist n (-1) g

/-- The actual determinant-twisted radical is identified with its integral lattice coordinates. -/
def twistedParameterH1Iso (n : ℕ) :
    groupCohomology (lineRep n) 1 ≅ groupCohomology (twistedSubgroupRep n) 1 :=
  groupCohomology.mapIso lineParamEquiv (LinearEquiv.refl ℚ (H n)) (by
    intro g
    change (lineRep n).ρ g = (twistedSubgroupRep n).ρ (lineParamEquiv g)
    exact (twistedSubgroupRep_parameter n g).symm) 1

def twistedParameterCoefficient (n : ℕ) :
    Rep.res lineParamEquiv.toMonoidHom (twistedSubgroupRep n) ⟶ lineRep n :=
  Rep.ofHom ⟨(LinearMap.id : H n →ₗ[ℚ] H n), by
    intro g
    change (twistedSubgroupRep n).ρ (lineParamEquiv g) = (lineRep n).ρ g
    exact twistedSubgroupRep_parameter n g⟩

theorem twistedParameterH1Iso_inv (n : ℕ) : (twistedParameterH1Iso n).inv =
    groupCohomology.map lineParamEquiv.toMonoidHom (twistedParameterCoefficient n) 1 := rfl

/-- The complete literal scalar coordinate on the actual determinant-twisted line-radical H¹. -/
def subgroupH1ScalarEquiv (n : ℕ) :
    groupCohomology (twistedSubgroupRep n) 1 ≃ₗ[ℚ] BinaryH (n+1) :=
  (twistedParameterH1Iso n).symm.toLinearEquiv.trans (latticeH1ScalarEquiv n)

@[simp] theorem subgroupH1ScalarEquiv_H1π (n : ℕ) (c : cocycles₁ (twistedSubgroupRep n)) :
    subgroupH1ScalarEquiv n (H1π (twistedSubgroupRep n) c) =
      cocycleScalar n (mapCocycles₁ lineParamEquiv.toMonoidHom (twistedParameterCoefficient n) c) := by
  change latticeH1ScalarEquiv n ((twistedParameterH1Iso n).inv (H1π _ c)) = _
  rw [twistedParameterH1Iso_inv,H1π_comp_map_apply,latticeH1ScalarEquiv_H1π]

/-- The scalar formula uses precisely the two actual integral radical generators. -/
theorem subgroupH1ScalarEquiv_rename (n : ℕ) (c : cocycles₁ (twistedSubgroupRep n)) :
    rename Fin.succ (subgroupH1ScalarEquiv n (H1π (twistedSubgroupRep n) c) : BP) =
      X 2 * ternaryTodd (X (0 : Fin 2)) (c (lineParamEquiv first) : Poly) -
      X 1 * ternaryTodd (X (1 : Fin 2)) (c (lineParamEquiv second) : Poly) := by
  rw [subgroupH1ScalarEquiv_H1π,cocycleScalar_rename]
  rfl

end TernaryPoly.SymmetricLineCohomology
