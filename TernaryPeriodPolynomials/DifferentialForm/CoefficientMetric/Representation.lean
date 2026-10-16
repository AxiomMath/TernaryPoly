module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Positive
public import TernaryPeriodPolynomials.SymmetricSpace.Covering

@[expose] public section


/-! The literal real homogeneous polynomial representation of the covering deck group. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open SL3PolynomialCoercivity SymmetricSpaceCovering SymmetricSpacePositive
open SymmetricSpaceArithmeticProper IntegralGL3Congruence

abbrev Mat := SL3PolynomialCoercivity.Mat

abbrev Coefficients (n : ℕ) := MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n

instance coefficientNormedAddCommGroup (n : ℕ) : NormedAddCommGroup (Coefficients n) :=
  let : InnerProductSpace.Core ℝ (Coefficients n) := homogeneousInnerCore n
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

/-- Fix the coefficient topology to the factorial norm.
-/
instance coefficientTopologicalSpace (n : ℕ) : TopologicalSpace (Coefficients n) :=
  (coefficientNormedAddCommGroup n).toMetricSpace.toUniformSpace.toTopologicalSpace

instance coefficientInnerProductSpace (n : ℕ) : InnerProductSpace ℝ (Coefficients n) :=
  let : InnerProductSpace.Core ℝ (Coefficients n) := homogeneousInnerCore n
  InnerProductSpace.ofCore (homogeneousInnerCore n).toCore

@[simp] theorem coefficient_inner (n : ℕ) (p q : Coefficients n) :
    inner ℝ p q = factorialPairing p.val q.val := rfl

def realPolynomialAction : Representation ℝ RealGL Poly where
  toFun g := (realSubstitute (g⁻¹ : RealGL)).toLinearMap
  map_one' := by
    simp only [inv_one, Matrix.GeneralLinearGroup.coe_one, realSubstitute_one]
    rfl
  map_mul' g h := by
    simp only [_root_.mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul]
    exact congrArg (fun q : Poly →ₐ[ℝ] Poly => q.toLinearMap)
      (realSubstitute_comp (g⁻¹ : RealGL) (h⁻¹ : RealGL)).symm

def realHomogeneousAction (n : ℕ) : Representation ℝ RealGL (Coefficients n) :=
  realPolynomialAction.subrepresentation (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (fun g _ hp => realSubstitute_preserves_degree (g⁻¹ : RealGL) hp)

def deckMatrix : DeckGroup →* RealGL := realIntegral.comp deckInclusion

def deckRepresentation (n : ℕ) : Representation ℝ DeckGroup (Coefficients n) :=
  (realHomogeneousAction n).comp deckMatrix

@[simp] theorem deckRepresentation_apply (n : ℕ) (g : DeckGroup) (p : Coefficients n) :
    (deckRepresentation n g p).val = realSubstitute ((deckMatrix g)⁻¹ : RealGL) p.val := rfl

theorem deckInclusion_mem (g : DeckGroup) : deckInclusion g ∈ principalSix :=
  (mem_principalSixInK g.val).mp g.property

theorem deckMatrix_det_one (g : DeckGroup) : (deckMatrix g).val.det = 1 := by
  rw [deckMatrix, MonoidHom.comp_apply, realIntegral_det,
    principalSix_det_one (deckInclusion g) (deckInclusion_mem g)]
  norm_num

end TernaryPoly.PolynomialCoefficientMetric
