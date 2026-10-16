module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Equivariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SupportGeometry

@[expose] public section


open MvPolynomial Matrix
open scoped DirectSum
noncomputable section
namespace TernaryPoly.SinglePoleSupport
open SinglePole PolynomialGLAction
open ModThreeGoodAction AugmentedFrameComplex PrimitiveLineHeight
open OrdinaryResidueSupport
attribute [local instance] Classical.propDecidable

/-- The literal coefficient-extension homomorphism from integral to rational matrices. -/
abbrev integralRational : IntegralGL →* GL3 := GeneralLinearGroup.map (Int.castRingHom ℚ)

/-- The actual finite principal-part representation restricted to integral matrices. -/
def integralResidueAction (n : ℕ) (e : ℤ) : Representation ℚ IntegralGL (Residues n) :=
  (residueAction n e).comp integralRational

@[simp] theorem integralResidueAction_apply (n : ℕ) (e : ℤ) (g : IntegralGL) (r : Residues n) :
    integralResidueAction n e g r = residueAction n e (integralRational g) r := rfl

/-- Inverse substitution sends the chosen denominator at H to a scalar multiple at H*g⁻¹. -/
theorem integral_denominator_transport (g : IntegralGL) (H : SinglePole.Normal) :
    ∃ c : ℚ, c ≠ 0 ∧ substitute ((integralRational g)⁻¹ : GL3) (denominator H) =
      C c * denominator (rowAction g⁻¹ H) := by
  rw [← map_inv]
  change ∃ c : ℚ, c ≠ 0 ∧ substitute (integralRational g⁻¹).val
    (form (rationalVector (primitiveGenerator H))) = _
  rw [substitute_form,← rationalVector_vecMul]
  exact form_scalar_denominator _
    (primitive_rational_ne_zero (primitive_vecMul g⁻¹ (primitiveGenerator_primitive H)))

/-- An individual principal-part generator has exactly its transported normal as possible support. -/
theorem action_lof_component_zero (n : ℕ) (e : ℤ) (g : IntegralGL)
    (H J : SinglePole.Normal) (z : ResidueFiber n H) (h : J ≠ rowAction g⁻¹ H) :
    (integralResidueAction n e g (DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) H z)) J = 0 := by
  obtain ⟨p,rfl⟩ := (numeratorRelations n H).mkQ_surjective z
  obtain ⟨c,_,hc⟩ := integral_denominator_transport g H
  rw [integralResidueAction_apply,residueAction_lof n e (integralRational g) H
    (rowAction g⁻¹ H) c hc]
  exact DirectSum.of_eq_of_ne _ _ _ h

/-- Actual component projection; no abstract replacement of the residue fibers is used. -/
def component (n : ℕ) (H : SinglePole.Normal) : Residues n →ₗ[ℚ] ResidueFiber n H :=
  DirectSum.component ℚ SinglePole.Normal (ResidueFiber n) H

@[simp] theorem component_apply (n : ℕ) (H : SinglePole.Normal) (r : Residues n) :
    component n H r = r H := rfl

/-- The H-component of the action factors through precisely the source component at H*g. -/
theorem component_action_factor (n : ℕ) (e : ℤ) (g : IntegralGL) (H : SinglePole.Normal) :
    (component n H).comp (integralResidueAction n e g) =
    ((component n H).comp (integralResidueAction n e g)).comp
      ((DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) (rowAction g H)).comp
        (component n (rowAction g H))) := by
  apply DirectSum.linearMap_ext
  intro J
  apply LinearMap.ext
  intro z
  by_cases h : J = rowAction g H
  · subst J
    simp only [LinearMap.comp_apply,component_apply,DirectSum.lof_apply]
  · have ht : H ≠ rowAction g⁻¹ J := by
      intro he
      apply h
      rw [he,← rowAction_mul,inv_mul_cancel,rowAction_one]
    change (integralResidueAction n e g
      (DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) J z)) H =
      (integralResidueAction n e g
        (DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) (rowAction g H)
          ((DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) J z) (rowAction g H)))) H
    rw [action_lof_component_zero n e g J H z ht]
    have hz : (DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) J z) (rowAction g H) = 0 :=
      DirectSum.of_eq_of_ne J _ z (Ne.symm h)
    rw [hz,map_zero,map_zero]
    rfl

/-- Vanishing of the genuine source component implies vanishing of the target component. -/
theorem component_action_zero_of (n : ℕ) (e : ℤ) (g : IntegralGL)
    (H : SinglePole.Normal) (r : Residues n) (h : r (rowAction g H) = 0) :
    (integralResidueAction n e g r) H = 0 := by
  have he := LinearMap.congr_fun (component_action_factor n e g H) r
  change (integralResidueAction n e g r) H =
    (integralResidueAction n e g
      (DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) (rowAction g H)
        (r (rowAction g H)))) H at he
  rw [h,map_zero,map_zero] at he
  exact he

/-- Exact source-component transport under integral inverse substitution. -/
theorem component_action_zero_iff (n : ℕ) (e : ℤ) (g : IntegralGL)
    (H : SinglePole.Normal) (r : Residues n) :
    (integralResidueAction n e g r) H = 0 ↔ r (rowAction g H) = 0 := by
  constructor
  · intro h
    have hi : (integralResidueAction n e g r) (rowAction g⁻¹ (rowAction g H)) = 0 := by
      rw [← rowAction_mul,mul_inv_cancel,rowAction_one]
      exact h
    have he := component_action_zero_of n e g⁻¹ (rowAction g H)
      (integralResidueAction n e g r) hi
    rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply] at he
    exact he
  · exact component_action_zero_of n e g H r

end TernaryPoly.SinglePoleSupport
