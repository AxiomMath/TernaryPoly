module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CohomologicalLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CoefficientRegularity

@[expose] public section


/-!
# Jointly smooth translates of a cocycle with smooth coefficient lifts

Let `α` be a cocycle `BinaryRealGL → BinaryAdelicGL → HomogeneousPoly (n + 1)` for the twisted
action `binaryCohomologicalAction`, and let `lift μ g` be smooth vectors of a cuspidal
representation realizing the coefficients of `α g`, depending smoothly on `g`.  The cocycle
identity expresses the translate `A ↦ α h (A * atInfinity g)` through the values `α (g * h)` and
`α g` alone:

  `α h (A * g) = N(g)⁻¹ • B(g⁻¹) (α (g * h) A - α g A)`,

with `N` the norm factor and `B` the coefficient representation.  Hence the vector family
`(h, g) ↦ π(g) (lift μ h)` is the finite sum
`∑ ν, w(μ, ν, g) • (lift ν (g * h) - lift ν g)` with smooth scalar weights `w`, and it is smooth
in both variables because `lift` is smooth in one.  This is the two-variable smooth lift
required by `Cohomological`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift
  (Index basisMonomial polynomial_reconstruct)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalLift
  (binaryCoefficient_one binaryCoefficient_mul)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (binaryCoefficient_functional_contDiffOn binary_normalizingFactor_contDiffOn
    binary_matrix_inv_contDiffOn invertibleMatrix_inv invertibleMatrix_mul)

namespace TernaryPeriodPolynomials.Automorphic.Constituent

/-! ### Algebra -/

/-- The coefficient of the monomial `μ`, as a linear functional on the degree-`n + 1` forms. -/
def coeffFunctional (n : ℕ) (μ : Fin 2 →₀ ℕ) : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ μ).comp (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (n + 1)).subtype

/-- The weight of the `ν`-th lifted vector in the translate by `g` of the `μ`-th coefficient:
the entry `(μ, ν)` of `N(g)⁻¹ • B(g⁻¹)`. -/
def translationWeight (n : ℕ) (μ : Fin 2 →₀ ℕ) (ν : Index (n + 1)) (g : BinaryRealGL) : ℂ :=
  (normPower (Matrix.GeneralLinearGroup.det (atInfinity g)) (((n : ℂ) + 3) / 2))⁻¹ *
    (binaryCoefficient n g⁻¹ (basisMonomial ν)).val.coeff μ

/-- **Matrix entries of an endomorphism of the degree-`n + 1` forms**: the `μ`-coefficient of
`T Q` is the sum over the monomial basis of the coefficients of `Q` times the entries of `T`. -/
theorem coeff_endo_apply {n : ℕ} (T : Module.End ℂ (Binary.HomogeneousPoly (n + 1)))
    (Q : Binary.HomogeneousPoly (n + 1)) (μ : Fin 2 →₀ ℕ) :
    (T Q).val.coeff μ =
      ∑ ν : Index (n + 1), Q.val.coeff ν.val * (T (basisMonomial ν)).val.coeff μ := by
  have hQ : Q = ∑ ν : Index (n + 1), Q.val.coeff ν.val • basisMonomial ν :=
    (polynomial_reconstruct (n + 1) Q).symm
  refine (congrArg (fun P : Binary.HomogeneousPoly (n + 1) => (T P).val.coeff μ) hQ).trans ?_
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, smul_eq_mul]

/-- The coefficient representation is inverted by the inverse matrix. -/
theorem binaryCoefficient_inv_apply (n : ℕ) (g : BinaryRealGL) (Y : Binary.HomogeneousPoly (n + 1)) :
    binaryCoefficient n g⁻¹ (binaryCoefficient n g Y) = Y := by
  have h : binaryCoefficient n g⁻¹ * binaryCoefficient n g = 1 := by
    rw [← binaryCoefficient_mul, inv_mul_cancel, binaryCoefficient_one]
  exact LinearMap.congr_fun h Y

/-- **The translation formula**: a cocycle for `binaryCohomologicalAction` is determined at the
translated point by its values at `g * h` and `g`. -/
theorem coeff_translate_formula {n : ℕ}
    (α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (cocycle : ∀ g h x, α (g * h) x = α g x + binaryCohomologicalAction n g (α h) x)
    (μ : Fin 2 →₀ ℕ) (h g : BinaryRealGL) (A : BinaryAdelicGL) :
    (α h (A * atInfinity g)).val.coeff μ =
      ∑ ν : Index (n + 1), translationWeight n μ ν g *
        ((α (g * h) A).val.coeff ν.val - (α g A).val.coeff ν.val) := by
  have hD : normPower (Matrix.GeneralLinearGroup.det (atInfinity g)) (((n : ℂ) + 3) / 2) •
      binaryCoefficient n g (α h (A * atInfinity g)) = α (g * h) A - α g A := by
    rw [cocycle g h A]
    unfold binaryCohomologicalAction
    abel
  have hN : normPower (Matrix.GeneralLinearGroup.det (atInfinity g)) (((n : ℂ) + 3) / 2) ≠ 0 :=
    Complex.exp_ne_zero _
  have hY : α h (A * atInfinity g) =
      (normPower (Matrix.GeneralLinearGroup.det (atInfinity g)) (((n : ℂ) + 3) / 2))⁻¹ •
        binaryCoefficient n g⁻¹ (α (g * h) A - α g A) := by
    rw [← hD, map_smul, binaryCoefficient_inv_apply, smul_smul, inv_mul_cancel₀ hN, one_smul]
  have h1 := congrArg (fun P : Binary.HomogeneousPoly (n + 1) => P.val.coeff μ) hY
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] at h1
  rw [h1, coeff_endo_apply (binaryCoefficient n g⁻¹) _ μ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold translationWeight
  simp only [Submodule.coe_sub, MvPolynomial.coeff_sub]
  ring

/-! ### Smoothness -/

/-- The product `A 1 * A 0` is smooth on pairs of matrices. -/
theorem matrixProduct_contDiff :
    ContDiff ℝ ⊤ (fun A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ => A 1 * A 0) := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  simp only [Matrix.mul_apply]
  apply ContDiff.sum
  intro middle _
  exact ((contDiff_apply_apply ℝ ℝ row middle).comp
      (contDiff_apply ℝ (Matrix (Fin 2) (Fin 2) ℝ) 1)).mul
    ((contDiff_apply_apply ℝ ℝ middle column).comp
      (contDiff_apply ℝ (Matrix (Fin 2) (Fin 2) ℝ) 0))

/-- A smooth function of one variable composed with the product `x 1 * x 0`. -/
theorem contDiffOn_comp_product {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : BinaryRealGL → E} (hF : Smooth (fun y : Fin 1 → BinaryRealGL => F (y 0))) :
    ContDiffOn ℝ ⊤ (fun A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ =>
      F (invertibleMatrix (A 1) * invertibleMatrix (A 0)))
      {A | ∀ i, (A i).det ≠ 0} := by
  have hφ : ContDiff ℝ ⊤
      (fun A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ => fun _ : Fin 1 => A 1 * A 0) :=
    contDiff_pi.mpr fun _ => matrixProduct_contDiff
  have composed := hF.comp hφ.contDiffOn
    (s := {A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ | ∀ i, (A i).det ≠ 0}) (by
      intro A hA i
      change (A 1 * A 0).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero (hA 1) (hA 0))
  refine composed.congr fun A hA => ?_
  change F (invertibleMatrix (A 1) * invertibleMatrix (A 0)) = F (invertibleMatrix (A 1 * A 0))
  rw [invertibleMatrix_mul _ _ (hA 1) (hA 0)]

/-- A smooth function of one variable composed with the projection `x 1`. -/
theorem contDiffOn_comp_second {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : BinaryRealGL → E} (hF : Smooth (fun y : Fin 1 → BinaryRealGL => F (y 0))) :
    ContDiffOn ℝ ⊤ (fun A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ => F (invertibleMatrix (A 1)))
      {A | ∀ i, (A i).det ≠ 0} := by
  have hφ : ContDiff ℝ ⊤
      (fun A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ => fun _ : Fin 1 => A 1) :=
    contDiff_pi.mpr fun _ => contDiff_apply ℝ (Matrix (Fin 2) (Fin 2) ℝ) 1
  exact hF.comp hφ.contDiffOn
    (s := {A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ | ∀ i, (A i).det ≠ 0}) (fun A hA _ => hA 1)

/-- **The translation weights are smooth** in the translating matrix. -/
theorem translationWeight_smooth (n : ℕ) (μ : Fin 2 →₀ ℕ) (ν : Index (n + 1)) :
    Smooth (fun x : Fin 2 → BinaryRealGL => translationWeight n μ ν (x 1)) := by
  unfold Smooth
  have entries : ∀ row column, ContDiffOn ℝ ⊤
      (fun A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ => A 1 row column)
      {A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ | ∀ i, (A i).det ≠ 0} := fun row column =>
    ((contDiff_apply_apply ℝ ℝ row column).comp
      (contDiff_apply ℝ (Matrix (Fin 2) (Fin 2) ℝ) 1)).contDiffOn
  have invertible : ∀ A ∈ {A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ | ∀ i, (A i).det ≠ 0},
      (A 1).det ≠ 0 := fun A hA => hA 1
  have inv_entries := fun row column => binary_matrix_inv_contDiffOn
    (fun A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ => A 1) entries invertible row column
  have inv_invertible : ∀ A ∈ {A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ | ∀ i, (A i).det ≠ 0},
      ((A 1)⁻¹).det ≠ 0 := by
    intro A hA
    simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using inv_ne_zero (hA 1)
  have coefficient := binaryCoefficient_functional_contDiffOn (degree := n)
    (fun A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ => (A 1)⁻¹) inv_entries inv_invertible
    (basisMonomial ν) (coeffFunctional n μ)
  have scalar := (binary_normalizingFactor_contDiffOn
    (fun A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ => A 1) entries invertible
    (((n : ℂ) + 3) / 2)).inv (fun _ _ => Complex.exp_ne_zero _)
  refine (scalar.mul coefficient).congr fun A hA => ?_
  change translationWeight n μ ν (invertibleMatrix (A 1)) = _
  unfold translationWeight
  rw [invertibleMatrix_inv (A 1) (hA 1)]
  rfl

/-! ### The translated vector family -/

/-- **The translated vector**: the vector realizing `A ↦ coeff μ (α (x 0) (A * atInfinity (x 1)))`,
assembled from the lifts at `x 1 * x 0` and `x 1`. -/
def translatedVector {σ : CuspidalRepresentation} (n : ℕ)
    (lift : (Fin 2 →₀ ℕ) → BinaryRealGL → σ.smooth) (μ : Fin 2 →₀ ℕ)
    (x : Fin 2 → BinaryRealGL) : σ.smooth :=
  ∑ ν : Index (n + 1), translationWeight n μ ν (x 1) •
    (lift ν.val (x 1 * x 0) - lift ν.val (x 1))

/-- The translated vector is smooth in both variables. -/
theorem translatedVector_smooth {σ : CuspidalRepresentation} (n : ℕ)
    (lift : (Fin 2 →₀ ℕ) → BinaryRealGL → σ.smooth)
    (lift_smooth : ∀ μ, Smooth (fun x : Fin 1 → BinaryRealGL => (lift μ (x 0)).val))
    (μ : Fin 2 →₀ ℕ) :
    Smooth (fun x : Fin 2 → BinaryRealGL => (translatedVector n lift μ x).val) := by
  unfold Smooth
  have hw : ∀ ν : Index (n + 1), ContDiffOn ℝ ⊤
      (fun A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ => translationWeight n μ ν (invertibleMatrix (A 1)))
      {A | ∀ i, (A i).det ≠ 0} := fun ν => translationWeight_smooth n μ ν
  have hsum : ContDiffOn ℝ ⊤ (fun A : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ =>
      ∑ ν : Index (n + 1), translationWeight n μ ν (invertibleMatrix (A 1)) •
        ((lift ν.val (invertibleMatrix (A 1) * invertibleMatrix (A 0))).val -
          (lift ν.val (invertibleMatrix (A 1))).val)) {A | ∀ i, (A i).det ≠ 0} :=
    ContDiffOn.sum fun ν _ => (hw ν).smul
      ((contDiffOn_comp_product (F := fun g => (lift ν.val g).val) (lift_smooth ν.val)).sub
        (contDiffOn_comp_second (F := fun g => (lift ν.val g).val) (lift_smooth ν.val)))
  refine hsum.congr fun A _ => ?_
  simp only [translatedVector, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_sub]

/-- The translated vector realizes the translate of the coefficient of the cocycle. -/
theorem translatedVector_realize {σ : CuspidalRepresentation} {n : ℕ}
    (α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (cocycle : ∀ g h x, α (g * h) x = α g x + binaryCohomologicalAction n g (α h) x)
    (lift : (Fin 2 →₀ ℕ) → BinaryRealGL → σ.smooth)
    (lift_realize : ∀ μ g A, σ.realize (lift μ g) A = (α g A).val.coeff μ)
    (μ : Fin 2 →₀ ℕ) (x : Fin 2 → BinaryRealGL) (A : BinaryAdelicGL) :
    σ.realize (translatedVector n lift μ x) A = (α (x 0) (A * atInfinity (x 1))).val.coeff μ := by
  rw [coeff_translate_formula α cocycle μ (x 0) (x 1) A]
  unfold translatedVector
  simp only [map_sum, map_smul, map_sub, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply,
    lift_realize, smul_eq_mul]

/-- **The two-variable smooth lift of a cocycle with smooth coefficient lifts.** -/
theorem exists_smooth_translate {σ : CuspidalRepresentation} {n : ℕ}
    (α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (cocycle : ∀ g h x, α (g * h) x = α g x + binaryCohomologicalAction n g (α h) x)
    (lift : (Fin 2 →₀ ℕ) → BinaryRealGL → σ.smooth)
    (lift_realize : ∀ μ g A, σ.realize (lift μ g) A = (α g A).val.coeff μ)
    (lift_smooth : ∀ μ, Smooth (fun x : Fin 1 → BinaryRealGL => (lift μ (x 0)).val))
    (μ : Fin 2 →₀ ℕ) :
    ∃ v : (Fin 2 → BinaryRealGL) → σ.smooth, Smooth (fun x => (v x).val) ∧ ∀ x A,
      σ.realize (v x) A = (α (x 0) (A * atInfinity (x 1))).val.coeff μ :=
  ⟨translatedVector n lift μ, translatedVector_smooth n lift lift_smooth μ,
    translatedVector_realize α cocycle lift lift_realize μ⟩

end TernaryPeriodPolynomials.Automorphic.Constituent

end
