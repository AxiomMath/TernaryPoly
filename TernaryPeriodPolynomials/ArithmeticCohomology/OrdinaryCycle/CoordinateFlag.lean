module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.IncidenceChains
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Coordinates
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantMatrices
public import TernaryPeriodPolynomials.Building.Reference.CoefficientMatrices
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyPolynomials

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryCoordinateFlag
open ModThreeGoodAction RelativeStabilizerCoordinates
open RadicalCoinvariantAlgebra RelativeStabilizerParameters RelativeStabilizerMatrices

/-- The literal coordinate line and coordinate plane in the ordinary incidence graph. -/
def line : OrdinaryIncidence.Line := ⟨L0,finrank_L0,trivial⟩
def plane : OrdinaryIncidence.Plane := ⟨P0,finrank_P0,⟨line,by
  intro v hv
  exact (mem_P0 v).mpr ((mem_L0 v).mp hv).2⟩⟩

def flag : OrdinaryIncidenceChains.Edge := ⟨(line,plane),by
  apply GoodIncidenceConnected.line_lt_plane (fun _ => True)
  intro v hv
  exact (mem_P0 v).mpr ((mem_L0 v).mp hv).2⟩

def flagChain : OrdinaryIncidenceChains.EdgeChains := Finsupp.single flag 1

/-- A genuine nontrivial root in the actual sum-covector congruence subgroup. -/
def step : K := ⟨rootElement 0 3,by
  change Matrix.vecMul fixedRow
    ((rootElement 0 3).val.map (Int.castRingHom (ZMod 3)))=fixedRow
  decide +kernel⟩

/-- The actual step-three root fixes both coordinate subspaces of this flag. -/
theorem step_flag : OrdinaryIncidenceChains.edgeAction step flag=flag := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change Stabilizes (rootElement 0 3) L0
    rw [stabilizes_L0_iff]
    constructor <;> rfl
  · apply Subtype.ext
    change Stabilizes (rootElement 0 3) P0
    rw [stabilizes_P0_iff]
    constructor <;> rfl

theorem step_flagChain : OrdinaryIncidenceChains.edgeRepresentation step flagChain=flagChain := by
  rw [flagChain,OrdinaryIncidenceChains.edgeRepresentation_single,step_flag]

private theorem step_rational_det :
    ((Matrix.GeneralLinearGroup.det (ReferenceCoefficientMatrices.rational (rootElement 0 3)) : ℚˣ) : ℚ)=1 := by
  change (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (rootElement 0 3)).val.det=1
  rw [Matrix.det_fin_three]
  norm_num [rootElement,bbMatrix,Matrix.GeneralLinearGroup.map_apply,
    Matrix.cons_val_zero',Matrix.cons_val_succ', Matrix.cons_val_two]

/-- The exact inverse substitution of this flag-fixing element, in every determinant twist. -/
theorem step_coefficient (e : ℤ) (p : TernaryPolynomial) :
    ReferenceCoefficientMatrices.coefficientAction e step.val p=
      RelativeEdgeCohomologyPolynomials.shearStep 0 1 3 p := by
  change PolynomialGLAction.action e (ReferenceCoefficientMatrices.rational (rootElement 0 3)) p=_
  rw [PolynomialGLAction.action_apply]
  change ((Matrix.GeneralLinearGroup.det
    (ReferenceCoefficientMatrices.rational (rootElement 0 3)) : ℚˣ) : ℚ)^e •
      PolynomialGLAction.substitute
        ((ReferenceCoefficientMatrices.rational (rootElement 0 3))⁻¹ : PolynomialGLAction.GL3) p=_
  rw [step_rational_det,one_zpow,one_smul]
  have he : PolynomialGLAction.substitute
      ((ReferenceCoefficientMatrices.rational (rootElement 0 3))⁻¹ : PolynomialGLAction.GL3)=
        RelativeEdgeCohomologyPolynomials.shearStep 0 1 3 := by
    rw [←map_inv,rootElement_inv]
    apply MvPolynomial.algHom_ext
    intro i
    rw [PolynomialGLAction.substitute_X]
    fin_cases i <;> norm_num [PolynomialGLAction.linearForm,rootElement,bbMatrix,
      Matrix.GeneralLinearGroup.map_apply,RelativeEdgeCohomologyPolynomials.shearStep,
      Fin.sum_univ_three,sub_eq_add_neg, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two]; rfl
  exact DFunLike.congr_fun he p

end TernaryPoly.OrdinaryCoordinateFlag
