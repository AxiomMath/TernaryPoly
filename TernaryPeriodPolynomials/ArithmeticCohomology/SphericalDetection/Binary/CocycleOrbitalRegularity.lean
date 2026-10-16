module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CocycleLocalRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryHilbertTranslation_family_contDiffOn_of_operator {degree : ℕ} {index P : Type}
    [Fintype index] [NormedAddCommGroup P] [NormedSpace ℝ P] {domain : Set P} {order : WithTop ℕ∞}
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (matrices : P → BinaryRealMatrix)
    (entries : ∀ row column, ContDiffOn ℝ order (fun point => matrices point row column) domain)
    (invertible : ∀ point ∈ domain, (matrices point).det ≠ 0)
    (vectors : P → (index → cusp.H))
    (regular : ContDiffOn ℝ order
      (fun point => binaryHilbertOperator cusp basis (invertibleMatrix (matrices point)) (vectors point)) domain) :
    ContDiffOn ℝ order (fun point => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix (matrices point))) (vectors point)) domain := by
  have inverse_regular := binaryHilbertCoefficient_contDiffOn cusp basis
    (fun point => (matrices point)⁻¹) (binary_matrix_inv_contDiffOn matrices entries invertible)
    (fun point member => by
      simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using inv_ne_zero (invertible point member))
    _ regular
  have scalar_regular := (binary_normalizingFactor_contDiffOn matrices entries invertible
    (((degree : ℂ) + 3) / 2)).inv (fun _ _ => Complex.exp_ne_zero _)
  apply (scalar_regular.smul inverse_regular).congr
  intro point member
  change binaryHilbertTranslation cusp (atInfinity (invertibleMatrix (matrices point))) (vectors point) =
    (normPower (GeneralLinearGroup.det (atInfinity (invertibleMatrix (matrices point)))) (((degree : ℂ) + 3) / 2))⁻¹ •
      binaryHilbertCoefficient cusp basis (invertibleMatrix (matrices point)⁻¹)
        (binaryHilbertOperator cusp basis (invertibleMatrix (matrices point)) (vectors point))
  rw [binaryHilbertTranslation_eq cusp basis, invertibleMatrix_inv _ (invertible point member)]

theorem binaryHilbertCocycle_orbital_smooth_of_analyticAt_one {degree : ℕ} {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (analytic : AnalyticAt ℝ (fun matrix : BinaryRealMatrix => binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix matrix))) 1) :
    Smooth (fun point : Fin 2 → BinaryRealGL => binaryHilbertEmbedding cusp basis
      (binaryRightTranslation cusp degree (atInfinity (point 1)) (cycle (point 0)))) := by
  let domain : Set (Fin 2 → BinaryRealMatrix) := {point | ∀ position, (point position).det ≠ 0}
  have regular := binaryHilbertCocycle_contDiffOn_of_analyticAt_one cusp basis cycle analytic
  have product_regular : ContDiff ℝ ⊤ (fun point : Fin 2 → BinaryRealMatrix => point 1 * point 0) := by
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    simp only [Matrix.mul_apply]
    exact ContDiff.sum (fun position _ => by fun_prop)
  have product_composed := regular.comp product_regular.contDiffOn (s := domain) (by
    intro point member
    change (point 1 * point 0).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (member 1) (member 0))
  have first_composed := regular.comp (contDiff_apply ℝ BinaryRealMatrix (1 : Fin 2)).contDiffOn
    (s := domain) (fun _ member => member 1)
  have operator_regular : ContDiffOn ℝ ⊤ (fun point : Fin 2 → BinaryRealMatrix =>
      binaryHilbertOperator cusp basis (invertibleMatrix (point 1))
        (binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix (point 0))))) domain := by
    apply (product_composed.sub first_composed).congr
    intro point member
    change binaryHilbertOperator cusp basis (invertibleMatrix (point 1))
        (binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix (point 0)))) =
      binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix (point 1 * point 0))) -
        binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix (point 1)))
    rw [invertibleMatrix_mul (point 1) (point 0) (member 1) (member 0), binaryHilbertCocycle_identity]
    abel
  have translation_regular := binaryHilbertTranslation_family_contDiffOn_of_operator (domain := domain) cusp basis
    (fun point : Fin 2 → BinaryRealMatrix => point 1) (fun row column => by fun_prop)
    (fun _ member => member 1)
    (fun point => binaryHilbertEmbedding cusp basis (cycle (invertibleMatrix (point 0)))) operator_regular
  apply translation_regular.congr
  intro point _
  exact (binaryHilbertTranslation_intertwines cusp basis (atInfinity (invertibleMatrix (point 1)))
    (cycle (invertibleMatrix (point 0)))).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
