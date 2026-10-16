module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexDual
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DetTwist

@[expose] public section


/-!
# General coercivity: the dual coefficient metric is the flat-bundle metric `‖ρ*(g)⁻¹ p‖`

The dual forms of this development pair with the standard coefficient metric at the Cartan point
`ι x` (`dualFormPairing`).  This file proves that this is exactly the metric of the paper for
the dual bundle `E*` with the dual representation `ρ*(g) = ρ(θ g)`, `θ g = (g⁻¹)ᵀ`: at a point whose
determinant-normalised matrix is `S = g gᵀ`, the dual coefficient bilinear form is
`⟨p, q⟩_{ι x} = ⟨ρ*(g)⁻¹ p, ρ*(g)⁻¹ q⟩_{Fischer}`.  It is the analogue for `E*` of
`matrixPairing_frame` (which gives `⟨p, q⟩_x = ⟨ρ(g)⁻¹ p, ρ(g)⁻¹ q⟩`).  The complex statement is the
Hermitian one, for `ρ*_ℂ` and the Hermitian Fischer norm.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.SL3PolynomialCoercivity

attribute [local instance 2000] TernaryPoly.PolynomialCoefficientMetric.coefficientTopologicalSpace

private theorem inv_smul_eq' {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : IsUnit M.det) {c : ℝ}
    (hc : c ≠ 0) : (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul,
    Matrix.mul_nonsing_inv _ hM]

/-- The determinant-normalised form of the Cartan point `ι x` is the inverse of the one at `x`. -/
theorem determinantNormalize_reconstruct_iotaC {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    determinantNormalize (reconstruct (iotaC x)) = (determinantNormalize (reconstruct x))⁻¹ := by
  have hR : (reconstruct x).PosDef := hx
  have hRi : (reconstruct x)⁻¹.PosDef := hR.inv
  have hdet : IsUnit (reconstruct x).det := (Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit
  have ha : (0 : ℝ) < (reconstruct x).det ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hR.det_pos _
  have hdetN : (determinantNormalize (reconstruct x)).det = 1 := determinantNormalize_det _ hR
  have hNinv_det : ((determinantNormalize (reconstruct x))⁻¹).det = 1 := by
    rw [Matrix.det_nonsing_inv, hdetN]; simp
  have hid : determinantNormalize (determinantNormalize (reconstruct x))⁻¹ =
      (determinantNormalize (reconstruct x))⁻¹ := by
    have key : ∀ M : Matrix (Fin 3) (Fin 3) ℝ, M.det = 1 → determinantNormalize M = M :=
      fun M h => by rw [determinantNormalize, h]; simp
    exact key _ hNinv_det
  have hNinv : (determinantNormalize (reconstruct x))⁻¹ =
      ((reconstruct x).det ^ (-(1 / 3 : ℝ)))⁻¹ • (reconstruct x)⁻¹ :=
    inv_smul_eq' hdet ha.ne'
  have h1 : determinantNormalize (((reconstruct x).det ^ (-(1 / 3 : ℝ)))⁻¹ • (reconstruct x)⁻¹) =
      determinantNormalize (reconstruct x)⁻¹ := determinantNormalize_smul _ (inv_pos.mpr ha) _ hRi
  rw [reconstruct_iotaC hx]
  unfold TernaryPoly.SymmetricSpacePositive.normalize
  rw [determinantNormalize_smul _ (inv_pos.mpr hRi.trace_pos) _ hRi, ← h1, ← hNinv, hid]

theorem inv_frame_eq (g : RealGL) :
    (((g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ).transpose))⁻¹ =
      ((thetaHom g : RealGL) : Matrix (Fin 3) (Fin 3) ℝ) *
        ((thetaHom g : RealGL) : Matrix (Fin 3) (Fin 3) ℝ).transpose := by
  change _ = (((g⁻¹ : RealGL) : Matrix (Fin 3) (Fin 3) ℝ).transpose) *
    (((g⁻¹ : RealGL) : Matrix (Fin 3) (Fin 3) ℝ).transpose).transpose
  rw [Matrix.transpose_transpose, Matrix.mul_inv_rev, Matrix.coe_units_inv,
    Matrix.transpose_nonsing_inv]

/-- **Faithfulness of the dual metric.**  At a point whose determinant-normalised form is
`S = g gᵀ`, the coefficient metric used for the dual forms (the standard metric at the Cartan point
`ι x`) is the flat-bundle metric `⟨ρ*(g)⁻¹ p, ρ*(g)⁻¹ q⟩` of the dual representation
`ρ*(g) = ρ(θ g)`, `θ g = (g⁻¹)ᵀ`, with the Fischer inner product.  (For the primal bundle the same
statement with `ρ` instead of `ρ*` is `matrixPairing_frame`.) -/
theorem coordinateCoefficientBilin_iotaC_frame {x : Coordinates} (hx : x ∈ positiveCoordinates)
    (g : RealGL)
    (hg : determinantNormalize (reconstruct x) =
      (g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ).transpose)
    {n : ℕ} (p q : Coefficients n) :
    coordinateCoefficientBilin n (iotaC x) p q =
      inner ℝ (realHomogeneousAction n (thetaHom g)⁻¹ p)
        (realHomogeneousAction n (thetaHom g)⁻¹ q) := by
  have e1 : coordinateCoefficientBilin n (iotaC x) p q =
      matrixPairing (determinantNormalize (reconstruct (iotaC x))) p.val q.val := rfl
  rw [e1, determinantNormalize_reconstruct_iotaC hx, hg, inv_frame_eq,
    matrixPairing_frame]
  change _ = factorialPairing (realSubstitute (((thetaHom g)⁻¹)⁻¹ : RealGL).val p.val)
    (realSubstitute (((thetaHom g)⁻¹)⁻¹ : RealGL).val q.val)
  rw [inv_inv]

/-- Every point has a frame: `determinantNormalize (reconstruct x) = g gᵀ` for some `g`. -/
theorem exists_frame {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    ∃ g : RealGL, determinantNormalize (reconstruct x) =
      (g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ).transpose := by
  obtain ⟨g, hg⟩ := TernaryPoly.SymmetricSpaceTraceMetric.exists_positive_frame _
    (determinantNormalize_positive _ hx)
  refine ⟨g, ?_⟩
  have hstar : star (g : Matrix (Fin 3) (Fin 3) ℝ) = (g : Matrix (Fin 3) (Fin 3) ℝ).transpose := by
    ext i j; rfl
  rw [hg, hstar]

/-- **Faithfulness of the complex dual metric.**  The Hermitian extension of the dual coefficient
metric is `⟨p, q⟩ = ⟨re ρ*_ℂ(g)⁻¹ p, re ρ*_ℂ(g)⁻¹ q⟩ + ⟨im ρ*_ℂ(g)⁻¹ p, im ρ*_ℂ(g)⁻¹ q⟩`, and on
the diagonal it is the Hermitian Fischer norm of `ρ*_ℂ(g)⁻¹ p`. -/
theorem cplxBilin_iotaC_frame {x : Coordinates} (hx : x ∈ positiveCoordinates) (g : RealGL)
    (hg : determinantNormalize (reconstruct x) =
      (g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ).transpose)
    {n : ℕ} (p q : ComplexCoefficients n) :
    cplxBilin n (coordinateCoefficientBilin n (iotaC x)) p q =
      inner ℝ (reL n (complexRepresentation n (thetaHom g)⁻¹ p))
          (reL n (complexRepresentation n (thetaHom g)⁻¹ q)) +
        inner ℝ (imL n (complexRepresentation n (thetaHom g)⁻¹ p))
          (imL n (complexRepresentation n (thetaHom g)⁻¹ q)) := by
  unfold cplxBilin
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.compl₁₂_apply,
    reL_complexRep, reL_complexRep, imL_complexRep, imL_complexRep]
  exact congrArg₂ (· + ·) (coordinateCoefficientBilin_iotaC_frame hx g hg _ _)
    (coordinateCoefficientBilin_iotaC_frame hx g hg _ _)

theorem cplxBilin_iotaC_frame_self {x : Coordinates} (hx : x ∈ positiveCoordinates) (g : RealGL)
    (hg : determinantNormalize (reconstruct x) =
      (g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ).transpose)
    {n : ℕ} (p : ComplexCoefficients n) :
    cplxBilin n (coordinateCoefficientBilin n (iotaC x)) p p =
      fischerC (complexRepresentation n (thetaHom g)⁻¹ p).1 := by
  rw [cplxBilin_iotaC_frame hx g hg, fischerC_reImEquiv, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  rfl

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
