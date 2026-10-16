module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.CohomologyCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.CoefficientDerivatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.PolynomialRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneOpenProjection

@[expose] public section


/-!
# Real Levi equivariance of the lower radical coordinate

The lower radical coordinate `Λ(α, β) = (X₁ α - X₀ β)|_{X₂ = 0}` is equivariant for the whole real
Levi `planeLevi m 1` of the plane parabolic, on *all* pairs (not only on cocycle pairs): moving a
pair by the coefficient action and recombining its entries by the rows of `m` gives
`det m · binaryCoefficient m (Λ(α, β))`. Pairs of the form `(D₀ v, D₁ v)` with
`D_i v = -X_i ∂₂ v` (the derivative of the coefficient action of the lower radical) have
coordinate zero.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The complexified plane Levi matrix. -/
abbrev complexPlaneLevi (m : BinaryRealGL) : GL3 :=
  GeneralLinearGroup.map (algebraMap ℝ ℂ) (planeLevi m 1)

theorem complexPlaneLevi_apply (m : BinaryRealGL) (i j : Fin 3) :
    (complexPlaneLevi m).val i j = ((planeLevi m 1).val i j : ℂ) := rfl

theorem substitute_inverse_substitute (M : GL3) (Q : Poly) :
    substitute (M⁻¹ : GL3).val (substitute M.val Q) = Q := by
  have composition := substitute_comp (M⁻¹ : GL3).val M.val
  have identity : M.val * (M⁻¹ : GL3).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [identity, substitute_one] at composition
  exact congrArg (fun hom : Poly →ₐ[ℂ] Poly => hom Q) composition

/-- The `3 × 3` block matrix with a `2 × 2` block and corner `1`. -/
def ternaryBlock (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

/-- The restriction to the first two coordinates intertwines block substitutions. -/
theorem binaryPolynomialRestrict_substitute (A : Matrix (Fin 2) (Fin 2) ℂ) (Q : Poly) :
    binaryPolynomialRestrict (substitute (ternaryBlock A) Q) =
      Binary.substitute A (binaryPolynomialRestrict Q) := by
  have homs : binaryPolynomialRestrict.comp (substitute (ternaryBlock A)) =
      (Binary.substitute A).comp binaryPolynomialRestrict := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [substitute_X, linearForm, Binary.substitute_X, Binary.linearForm, Fin.sum_univ_three,
        Fin.sum_univ_two, binaryPolynomialRestrict, ternaryBlock]
  exact congrArg (fun hom : Poly →ₐ[ℂ] Binary.Poly => hom Q) homs

theorem complexPlaneLevi_inv_val (m : BinaryRealGL) :
    (complexPlaneLevi m)⁻¹.val = ternaryBlock ((m⁻¹ : BinaryRealGL).val.map (algebraMap ℝ ℂ)) := by
  have inverse : (planeLevi m 1)⁻¹ = planeLevi m⁻¹ 1 := (map_inv planeLeviOneHom m).symm
  rw [complexPlaneLevi, ← map_inv, inverse]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [ternaryBlock, planeLevi, planeBlock]

theorem binaryMap_inv_val (m : BinaryRealGL) :
    (GeneralLinearGroup.map (algebraMap ℝ ℂ) m)⁻¹.val =
      (m⁻¹ : BinaryRealGL).val.map (algebraMap ℝ ℂ) := by
  rw [← map_inv]
  rfl

/-- **Real Levi equivariance of the lower radical coordinate.** -/
theorem lowerRadicalCoordinate_levi (m : BinaryRealGL) (v : Fin 2 → HomogeneousPoly n) :
    lowerRadicalCoordinate n (fun i => ∑ k, ((m.val i k : ℝ) : ℂ) •
        realCoefficientComponent n trivialCharacter (planeLevi m 1) (v k)) =
      ((m.val.det : ℝ) : ℂ) • binaryCoefficient n m (lowerRadicalCoordinate n v) := by
  set M := complexPlaneLevi m
  set S := substitute (M⁻¹ : GL3).val
  set d : ℂ := ((m.val.det : ℝ) : ℂ)
  have hd : d ≠ 0 := by
    simpa [d] using (Units.ne_zero (Matrix.GeneralLinearGroup.det m))
  have detM : ((GeneralLinearGroup.det M : ℂˣ) : ℂ) = d := by
    change (M.val).det = d
    simp [M, complexPlaneLevi, planeLevi, planeBlock, Matrix.det_fin_three, Matrix.det_fin_two, d]
  have detm : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) m) : ℂˣ) : ℂ) =
      d := by
    change (GeneralLinearGroup.map (algebraMap ℝ ℂ) m).val.det = d
    simp [d, Matrix.det_fin_two]
  have coefficient (k : Fin 2) : (realCoefficientComponent n trivialCharacter (planeLevi m 1)
      (v k)).val = d⁻¹ • S (v k).val := by
    rw [realCoefficientComponent_trivial, homogeneousAction_coe, action_apply]
    change ((GeneralLinearGroup.det M : ℂˣ) : ℂ) ^ (-1 : ℤ) • S (v k).val = _
    rw [detM, zpow_neg_one]
  have first : X 1 * C ((m.val 0 0 : ℝ) : ℂ) - X 0 * C ((m.val 1 0 : ℝ) : ℂ) =
      S (C d * X 1) := by
    rw [← substitute_inverse_substitute M (X 1 * C _ - X 0 * C _)]
    congr 1
    simp [substitute_X, linearForm, Fin.sum_univ_three, M, planeLevi, planeBlock, d,
      Matrix.det_fin_two]
    ring
  have second : X 1 * C ((m.val 0 1 : ℝ) : ℂ) - X 0 * C ((m.val 1 1 : ℝ) : ℂ) =
      S (-(C d * X 0)) := by
    rw [← substitute_inverse_substitute M (X 1 * C _ - X 0 * C _)]
    congr 1
    simp [substitute_X, linearForm, Fin.sum_univ_three, M, planeLevi, planeBlock, d,
      Matrix.det_fin_two]
    ring
  apply Subtype.ext
  change binaryPolynomialRestrict (lowerRadicalContraction _ _) =
    (d • binaryCoefficient n m (lowerRadicalCoordinate n v)).val
  have character : Binary.determinantCharacter (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) m) =
      d⁻¹ := by
    change ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) m) : ℂˣ) : ℂ) ^
      (-1 : ℤ) = d⁻¹
    rw [detm, zpow_neg_one]
  rw [Submodule.coe_smul, binaryCoefficient, Binary.homogeneousAction_coe, Binary.action_apply,
    character, binaryMap_inv_val]
  change binaryPolynomialRestrict (lowerRadicalContraction _ _) = d • d⁻¹ •
    Binary.substitute _ (binaryPolynomialRestrict (lowerRadicalContraction (v 0).val (v 1).val))
  rw [← binaryPolynomialRestrict_substitute, ← complexPlaneLevi_inv_val, smul_smul,
    mul_inv_cancel₀ hd, one_smul]
  congr 1
  simp only [lowerRadicalContraction, Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul,
    coefficient, smul_smul]
  have expand : X 1 * ((((m.val 0 0 : ℝ) : ℂ) * d⁻¹) • S (v 0).val +
        (((m.val 0 1 : ℝ) : ℂ) * d⁻¹) • S (v 1).val) -
      X 0 * ((((m.val 1 0 : ℝ) : ℂ) * d⁻¹) • S (v 0).val +
        (((m.val 1 1 : ℝ) : ℂ) * d⁻¹) • S (v 1).val) =
      C d⁻¹ * ((X 1 * C ((m.val 0 0 : ℝ) : ℂ) - X 0 * C ((m.val 1 0 : ℝ) : ℂ)) * S (v 0).val +
        (X 1 * C ((m.val 0 1 : ℝ) : ℂ) - X 0 * C ((m.val 1 1 : ℝ) : ℂ)) * S (v 1).val) := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul]
    ring
  rw [expand, first, second]
  simp only [map_mul, map_sub, map_neg, MvPolynomial.algHom_C, S]
  rw [show (algebraMap ℂ Poly) d = C d from rfl]
  have cancel : C d⁻¹ * C d = (1 : Poly) := by rw [← C_mul, inv_mul_cancel₀ hd, C_1]
  linear_combination (S (X 1) * S (v 0).val - S (X 0) * S (v 1).val) * cancel

end TernaryPeriodPolynomials.AnalyticClasses
