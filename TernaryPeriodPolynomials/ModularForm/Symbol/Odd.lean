module

public import TernaryPeriodPolynomials.ModularForm.Symbol.Full
public import TernaryPeriodPolynomials.ModularForm.Symbol.ReflectionProjection
public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Matrices

@[expose] public section


noncomputable section
open MvPolynomial Matrix

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod BinaryModularSymbol

@[simp] theorem reflection_inv : reflection⁻¹ = reflection := by
  change (integral reflectionIntegral)⁻¹ = integral reflectionIntegral
  rw [←map_inv]
  apply congrArg integral
  apply Units.ext
  rfl

@[simp] theorem reflection_det : reflection.det.val = (-1 : ℚ) := by
  change reflection.val.det = _
  rw [reflection_matrix]
  norm_num [Matrix.det_fin_two]

theorem reflection_reference : action reflection reference = reference := by
  have he : reflection = integral (periodGL 0) := by
    apply congrArg integral
    apply Units.ext
    rfl
  rw [he]
  exact periodGL_reference 0

theorem complexify_reflection_matrix : (complexify reflection).val = !![(-1 : ℂ),0;0,1] := by
  change reflection.val.map (algebraMap ℚ ℂ) = _
  rw [reflection_matrix]
  ext i j
  change ((!![(-1 : ℚ),0;0,1] i j : ℚ) : ℂ) = _
  fin_cases i <;> fin_cases j <;> norm_num

theorem functionAction_reflection (F : Functions) (v : Coordinates) :
    functionAction reflection F v = -F ![-v 0,v 1] := by
  rw [functionAction_apply, reflection_det, ←map_inv, reflection_inv, complexify_reflection_matrix]
  have he : (!![(-1 : ℂ),0;0,1]).mulVec v = ![-v 0,v 1] := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct]
  rw [he]
  norm_num

/-- The actual odd cusp modular symbol, genuinely equivariant for all of GL2(Z). -/
def oddHom {d : ℕ} (f : Forms d) : FunctionHom :=
  ⟨(1/2 : ℚ) • (full f+homAction functionAction reflection (full f)), by
    intro g
    exact (homAction_fixed_iff _ _ _).1
      (reflection_average_integral_fixed (homAction functionAction) (full f) (full_fixed_sl f) g)⟩

/-- Its literal reference is exactly the odd period projection from the proved analytic period map. -/
theorem oddHom_reference {d : ℕ} (hd : Even d) (f : Forms d) :
    (oddHom f).val reference = evaluate (oddPeriod f) := by
  funext v
  change (1/2 : ℚ) • (full f reference v +
    functionAction reflection (full f (action reflection⁻¹ reference)) v) = _
  rw [reflection_inv, reflection_reference, full_reference hd, functionAction_reflection]
  change (1/2 : ℚ) • (eval v (period f)-eval ![-v 0,v 1] (period f)) = eval v (oddPeriod f)
  have h := two_mul_eval_oddPeriod f (v 0) (v 1)
  have hv : ![v 0,v 1] = v := by funext i; fin_cases i <;> rfl
  rw [hv] at h
  rw [Algebra.smul_def]
  norm_num
  linear_combination -(1/2 : ℂ)*h

end TernaryPoly.BinaryCuspSymbol
