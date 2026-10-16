module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.VectorDerivatives
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.PartialSmoothDerivatives
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.CompactReduction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem normalizedCuspVector_leftRealOrbit_smooth
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (finiteMatrix : FiniteGL) :
    Smooth (fun realElements : Fin 1 → RealGL3 =>
      (normalizedCuspVector induced parameter
        (atInfinity (realElements 0) * atFinite finiteMatrix)).val) := by
  simpa only [atInfinity_atFinite_commute] using
    normalizedCuspVector_realOrbit_smooth induced parameter (atFinite finiteMatrix)

theorem normalizedCuspVector_mixedOrbit_contDiffOn
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (finiteMatrix : FiniteGL) :
    ContDiffOn ℝ ⊤
      (fun input : (Fin 1 → Matrix (Fin 3) (Fin 3) ℝ) × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        inducingData.cusp.π (atInfinity (invertibleMatrix (input.2 0)))
          (normalizedCuspVector induced parameter
            (atInfinity (invertibleMatrix (input.1 0)) * atFinite finiteMatrix)).val)
      ({entries | ∀ index, (entries index).det ≠ 0} ×ˢ
        {entries | ∀ index, (entries index).det ≠ 0}) := by
  let domain : Set ((Fin 1 → Matrix (Fin 3) (Fin 3) ℝ) ×
      (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) :=
    {entries | ∀ index, (entries index).det ≠ 0} ×ˢ
      {entries | ∀ index, (entries index).det ≠ 0}
  let productEntries (input : (Fin 1 → Matrix (Fin 3) (Fin 3) ℝ) ×
      (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ :=
    fun _ => planeBlock (input.2 0) 1 * input.1 0
  have product_smooth : ContDiff ℝ ⊤ productEntries := by
    apply contDiff_pi.mpr
    intro index
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    fin_cases row <;> fin_cases column <;>
      simp only [productEntries, Matrix.mul_apply, Fin.sum_univ_three, planeBlock,
        Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] <;> fun_prop
  have product_value (input) (member : input ∈ domain) :
      productEntries input 0 =
        (planeLevi (invertibleMatrix (input.2 0)) 1 * invertibleMatrix (input.1 0)).val := by
    simp only [productEntries, Units.val_mul, planeLevi, Units.val_one,
      invertibleMatrix, dite_eq_left (member.1 0), dite_eq_left (member.2 0),
      GeneralLinearGroup.val_mkOfDetNeZero]
  have product_maps : Set.MapsTo productEntries domain
      {entries | ∀ index, (entries index).det ≠ 0} := by
    intro input member index
    have value : productEntries input index = productEntries input 0 := rfl
    rw [value, product_value input member]
    exact (planeLevi (invertibleMatrix (input.2 0)) 1 * invertibleMatrix (input.1 0)).det_ne_zero
  have vector_smooth :=
    (normalizedCuspVector_leftRealOrbit_smooth induced parameter finiteMatrix).comp
      product_smooth.contDiffOn product_maps
  have determinant_smooth : ContDiff ℝ ⊤
      (fun input : (Fin 1 → Matrix (Fin 3) (Fin 3) ℝ) ×
        (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) => (input.2 0).det) := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have logarithm_smooth : ContDiffOn ℝ ⊤
      (fun input => Real.log (input.2 0).det) domain :=
    determinant_smooth.contDiffOn.log (fun _ member => member.2 0)
  have scalar_smooth : ContDiffOn ℝ ⊤
      (fun input => Complex.exp ((-inductionExponent .plane parameter) *
        (Real.log (input.2 0).det : ℂ))) domain :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn logarithm_smooth)).cexp
  apply (scalar_smooth.smul vector_smooth).congr
  intro input member
  change inducingData.cusp.π (atInfinity (invertibleMatrix (input.2 0)))
      (normalizedCuspVector induced parameter
        (atInfinity (invertibleMatrix (input.1 0)) * atFinite finiteMatrix)).val =
    Complex.exp ((-inductionExponent .plane parameter) * (Real.log (input.2 0).det : ℂ)) •
      (normalizedCuspVector induced parameter
        (atInfinity (invertibleMatrix (productEntries input 0)) * atFinite finiteMatrix)).val
  have scalar_one : realAdeleUnit (1 : ℝˣ) = 1 := by
    apply Units.ext
    rfl
  rw [product_value input member, invertibleMatrix_val, atInfinity_mul,
    atInfinity_planeLevi, scalar_one, mul_assoc, normalizedCuspVector_binary]
  change inducingData.cusp.π _ _ = _ • (normPower _ _ • inducingData.cusp.π _ _)
  rw [smul_smul]
  have coefficient : Complex.exp ((-inductionExponent .plane parameter) *
      (Real.log (input.2 0).det : ℂ)) =
      normPower (GeneralLinearGroup.det (atInfinity (invertibleMatrix (input.2 0))))
        (-inductionExponent .plane parameter) := by
    rw [det_atInfinity_binary, normPower_realAdeleUnit]
    simp only [GeneralLinearGroup.val_det_apply, invertibleMatrix, dite_eq_left (member.2 0),
      GeneralLinearGroup.val_mkOfDetNeZero, Real.log_abs]
  rw [coefficient, ← normPower_add, neg_add_cancel, normPower_zero, one_smul]

theorem normalizedCuspVector_cuspDerivative_real_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (finiteMatrix : FiniteGL) (order : ℕ) :
    Continuous (fun realMatrix : RealGL3 => cuspOrbitDerivative inducingData.cusp order
      (normalizedCuspVector induced parameter (atInfinity realMatrix * atFinite finiteMatrix))) := by
  have derivatives := contDiffOn_iteratedFDeriv_parameter (𝕜 := ℝ)
    (function := fun (entries : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ)
      (binaryEntries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
      inducingData.cusp.π (atInfinity (invertibleMatrix (binaryEntries 0)))
        (normalizedCuspVector induced parameter
          (atInfinity (invertibleMatrix (entries 0)) * atFinite finiteMatrix)).val)
    (normalizedCuspVector_mixedOrbit_contDiffOn induced parameter finiteMatrix)
    (invertibleMatrixTuples_isOpen 3 1) (invertibleMatrixTuples_isOpen 2 1) order
  have composed := derivatives.continuousOn.comp_continuous
    ((continuous_pi (fun _ : Fin 1 => Units.continuous_val)).prodMk
      (continuous_const : Continuous (fun _ : RealGL3 => fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ))))
    (fun realMatrix => ⟨fun _ => GeneralLinearGroup.det_ne_zero realMatrix, fun _ => by simp⟩)
  simpa only [Function.comp_def, invertibleMatrix_val, cuspOrbitDerivative, LinearMap.coe_mk,
    AddHom.coe_mk] using composed

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
