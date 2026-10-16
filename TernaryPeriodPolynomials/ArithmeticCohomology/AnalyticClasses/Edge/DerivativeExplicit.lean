module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeExplicitMean

@[expose] public section


/-!
# The explicit derivative of the edge along the diagonal flow

For the pointwise Eichler normal form `N = eichlerNormal n F` of a scalar form `F` with the
analytic data `EichlerData`, the lower radical coordinate of the integrated mixed derivative of
the edge section is `2πi` times the velocity of the transported twisted normal form:
`Λ(i ↦ lineVector (edgeMixedIntegral N i) h) = 2πi · edgeNormalVelocity n F h`. The velocity is
the derivative at `s = 0` of `edgeNormal F (a(s)) h` along the diagonal flow `a(s)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

namespace EdgeExplicit

/-! ### Interchanging the lower radical coordinate with the integral -/

theorem functional_pi_expansion {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*}
    [Fintype ι] (b : Module.Basis ι ℂ M) (Θ : (Fin 2 → M) →ₗ[ℂ] ℂ) (v : Fin 2 → M) :
    Θ v = ∑ i, ∑ m, b.coord m (v i) * Θ (Pi.single i (b m)) := by
  have hv : v = ∑ i, ∑ m, b.coord m (v i) • Pi.single i (b m) := by
    funext k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same, Module.Basis.coord_apply]
      exact (b.sum_repr (v k)).symm
    · intro i _ hik
      simp [Pi.single_eq_of_ne' hik]
    · simp
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- **The lower radical coordinate commutes with the integral** of a family whose tests are all
integrable, read through the coordinates of the line vector. -/
theorem coord_lowerRadicalCoordinate_integral (W : ℝ × ℝ → Fin 2 → HomogeneousPoly n)
    (hW : ∀ i (functional : HomogeneousPoly n →ₗ[ℂ] ℂ),
      Integrable fun u => functional (W u i)) (j : Fin (n + 2)) :
    (binaryWeightBasis (n + 1)).coord j (lowerRadicalCoordinate n fun i =>
        ∑ m, (∫ u, (EdgeControl.homogeneousBasis n).coord m (W u i)) •
          EdgeControl.homogeneousBasis n m) =
      ∫ u, (binaryWeightBasis (n + 1)).coord j (lowerRadicalCoordinate n (W u)) := by
  set b := EdgeControl.homogeneousBasis n
  set Θ := (binaryWeightBasis (n + 1)).coord j ∘ₗ lowerRadicalCoordinate n
  change Θ _ = ∫ u, Θ (W u)
  rw [functional_pi_expansion b Θ, show (fun u => Θ (W u)) = fun u =>
    ∑ i, ∑ m, b.coord m (W u i) * Θ (Pi.single i (b m)) from
      funext fun u => functional_pi_expansion b Θ (W u)]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun m _ =>
    (hW i (b.coord m)).mul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun m _ => (hW i (b.coord m)).mul_const _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_const, Module.Basis.coord_apply, Module.Basis.repr_sum_self]

/-! ### The integral of the closed form -/

theorem coord_lowerRadicalCoordinate_edgeMixedVector {F : BinaryAdelicGL → ℂ → ℂ}
    (hF : EichlerData n F) (u : ℝ × ℝ) (h : BinaryAdelicGL) (j : Fin (n + 2)) :
    (binaryWeightBasis (n + 1)).coord j
        (lowerRadicalCoordinate n fun i => edgeMixedVector n F u i h) =
      edgeConstant n * holTerm n F h j u + edgeConstant n * antiTerm n F h j u := by
  rw [lowerRadicalCoordinate_edgeMixedVector_closed hF, map_add, map_smul, map_smul, holTerm,
    antiTerm, smul_eq_mul, smul_eq_mul]
  ring

theorem integral_coord_lowerRadicalCoordinate {F : BinaryAdelicGL → ℂ → ℂ}
    (hF : EichlerData n F) (large : 2 ≤ n) (h : BinaryAdelicGL) (j : Fin (n + 2)) :
    ∫ u, (binaryWeightBasis (n + 1)).coord j
        (lowerRadicalCoordinate n fun i => edgeMixedVector n F u i h) =
      edgeConstant n * ((Real.pi / (((n + 3 : ℕ) : ℝ) / 2 - 1) : ℝ) : ℂ) *
        (discForm n F h 0 * (binaryWeightBasis (n + 1)).coord j (holPsi n 0) +
          discForm n F (h * atInfinity UpperHalfPlane.J) 0 *
            (binaryWeightBasis (n + 1)).coord j (antiPsi n 0)) := by
  simp only [coord_lowerRadicalCoordinate_edgeMixedVector hF]
  rw [integral_add ((integrable_holTerm hF large h j).const_mul _)
    ((integrable_antiTerm hF large h j).const_mul _), integral_const_mul, integral_const_mul,
    integral_holTerm hF large h j, integral_antiTerm hF large h j]
  ring

/-! ### The velocity in the weight basis -/

theorem binarySwap_val (P : Binary.HomogeneousPoly (n + 1)) :
    (binarySwap n P).val = rename (Equiv.swap (0 : Fin 2) 1) P.val := rfl

theorem rename_swap_binaryLin (a b : ℂ) :
    rename (Equiv.swap (0 : Fin 2) 1) (binaryLin a b) = binaryLin b a := by
  simp only [binaryLin, map_add, map_mul, rename_C, rename_X, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  ring

theorem binaryLin_neg_I_one :
    binaryLin (-Complex.I) 1 = C (-Complex.I) * binaryPositiveCoordinate := by
  have key : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  rw [binaryLin, binaryPositiveCoordinate, mul_add, ← mul_assoc, ← map_mul, key, map_one,
    one_mul]

theorem binaryLin_neg_I_neg_one :
    binaryLin (-Complex.I) (-1) = C (-Complex.I) * binaryNegativeCoordinate := by
  have key : -Complex.I * -Complex.I = -1 := by rw [neg_mul_neg, Complex.I_mul_I]
  rw [binaryLin, binaryNegativeCoordinate, mul_sub, ← mul_assoc, ← map_mul, sub_eq_add_neg,
    ← neg_mul, ← map_neg, neg_mul, neg_neg, Complex.I_mul_I]

/-- **The velocity of the transported twisted normal form in the weight basis.** -/
theorem edgeNormalVelocity_eq (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) :
    edgeNormalVelocity n F h = (-(-Complex.I) ^ n) •
      (F h Complex.I • binaryWeightBasis (n + 1) (Fin.last (n + 1)) +
        F (h * atInfinity UpperHalfPlane.J) Complex.I • binaryWeightBasis (n + 1) 0) := by
  have unimodular : |(UpperHalfPlane.J : BinaryRealGL).val.det| = 1 := by
    rw [det_upperJ, abs_neg, abs_one]
  rw [edgeNormalVelocity, binaryAmbientRepresentation_apply_of_unimodular unimodular, map_smul]
  apply Subtype.ext
  rw [binarySwap_val]
  simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_C_mul,
    binaryCoefficient_J_binaryPointPower_I_val, binaryPointPower_I_val, binaryWeightBasis_coe,
    map_add, map_mul, map_pow, rename_C, rename_swap_binaryLin, binaryLin_neg_I_one,
    binaryLin_neg_I_neg_one, Fin.val_last, Fin.val_zero, Nat.sub_self, Nat.sub_zero, pow_zero,
    mul_one, mul_pow, map_one, one_mul]
  have square : (-Complex.I) ^ 2 = -1 := by rw [neg_sq, Complex.I_sq]
  have phase : -Complex.I * (-Complex.I) ^ (n + 1) = -(-Complex.I) ^ n := by
    calc -Complex.I * (-Complex.I) ^ (n + 1) = (-Complex.I) ^ n * (-Complex.I) ^ 2 := by ring
      _ = -(-Complex.I) ^ n := by rw [square]; ring
  have first : (C (-Complex.I) : Binary.Poly) * C (-Complex.I) ^ (n + 1) =
      C (-(-Complex.I) ^ n) := by
    rw [← map_pow, ← map_mul, phase]
  have second : (C Complex.I : Binary.Poly) * C (-1) * C (-Complex.I) ^ (n + 1) =
      C (-(-Complex.I) ^ n) := by
    rw [← map_pow, ← map_mul, ← map_mul, ← phase]
    ring_nf
  linear_combination (C (F h Complex.I) * binaryPositiveCoordinate ^ (n + 1)) * first +
    (C (F (h * atInfinity UpperHalfPlane.J) Complex.I) * binaryNegativeCoordinate ^ (n + 1)) *
      second

/-! ### The constant -/

theorem two_I_cube' : (2 * Complex.I) ^ 3 = -8 * Complex.I := by
  linear_combination (8 * Complex.I) * Complex.I_sq

theorem edge_constant_identity :
    edgeConstant n * ((Real.pi / (((n + 3 : ℕ) : ℝ) / 2 - 1) : ℝ) : ℂ) *
        (2 * Complex.I) ^ (n + 3) =
      (2 * Real.pi * Complex.I : ℂ) * (-(-Complex.I) ^ n) := by
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have phase : ((-1 / 2 : ℂ)) ^ n * (2 * Complex.I) ^ n = (-Complex.I) ^ n := by
    rw [← mul_pow]
    ring_nf
  have denominator : (((n + 3 : ℕ) : ℝ) / 2 - 1 : ℝ) = ((n : ℝ) + 1) / 2 := by
    push_cast
    ring
  rw [denominator, edgeConstant, pow_add, two_I_cube']
  push_cast
  calc ((n : ℂ) + 1) / 8 * (-1 / 2) ^ n * ((Real.pi : ℂ) / (((n : ℂ) + 1) / 2)) *
        ((2 * Complex.I) ^ n * (-8 * Complex.I)) =
      ((n : ℂ) + 1) / 8 * ((Real.pi : ℂ) / (((n : ℂ) + 1) / 2)) *
        ((-1 / 2) ^ n * (2 * Complex.I) ^ n) * (-8 * Complex.I) := by ring
    _ = _ := by
      rw [phase]
      field_simp

end EdgeExplicit

open EdgeExplicit

/-- **The explicit derivative edge.** The lower radical coordinate of the integrated mixed
derivative of the edge section of the pointwise Eichler normal form is `2πi` times the velocity
of the transported twisted normal form along the diagonal flow. -/
theorem lowerRadicalCoordinate_edgeMixedIntegral {F : BinaryAdelicGL → ℂ → ℂ} (large : 5 ≤ n)
    (hF : EichlerData n F) (h : BinaryAdelicGL) :
    lowerRadicalCoordinate n (fun i => lineVector (edgeMixedIntegral (eichlerNormal n F) i) h) =
      (2 * Real.pi * Complex.I : ℂ) • edgeNormalVelocity n F h := by
  have pointwise : ∀ i, lineVector (edgeMixedIntegral (eichlerNormal n F) i) h =
      ∑ m, (∫ u, (EdgeControl.homogeneousBasis n).coord m (edgeMixedVector n F u i h)) •
        EdgeControl.homogeneousBasis n m := by
    intro i
    unfold lineVector edgeMixedIntegral
    simp only [edgeMixed_eichlerNormal F hF.holomorphic]
    rfl
  apply (binaryWeightBasis (n + 1)).ext_elem
  intro j
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply]
  simp only [pointwise]
  rw [coord_lowerRadicalCoordinate_integral (fun u i => edgeMixedVector n F u i h)
      (fun i functional => integrable_functional_edgeMixedVector hF (by omega) i h functional) j,
    integral_coord_lowerRadicalCoordinate hF (by omega) h j, map_smul, edgeNormalVelocity_eq,
    map_smul, map_add, map_smul, map_smul, holPsi_zero, antiPsi_zero, discForm_zero,
    discForm_zero, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  linear_combination (F h Complex.I * (binaryWeightBasis (n + 1)).coord j
      (binaryWeightBasis (n + 1) (Fin.last (n + 1))) +
    F (h * atInfinity UpperHalfPlane.J) Complex.I *
      (binaryWeightBasis (n + 1)).coord j (binaryWeightBasis (n + 1) 0)) *
    edge_constant_identity

namespace EdgeExplicit

/-! ### The edge normal form along the diagonal flow -/

/-- The point `e^{-2s} i` of the upper half plane. -/
def flowPoint (s : ℝ) : ℂ := ((Real.exp (-2 * s) : ℝ) : ℂ) * Complex.I

theorem pivotConjugate_diagonalFlow_val (s : ℝ) :
    (pivotConjugate ((diagonalFlow s : unimodularLevi) : BinaryRealGL)).val =
      !![Real.exp (-s), 0; 0, Real.exp s] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [pivotConjugate, binaryPivotSwap, diagonalFlow, diagonalFlowMatrix_val, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem basePoint_pivotConjugate_diagonalFlow (s : ℝ) :
    basePoint (pivotConjugate ((diagonalFlow s : unimodularLevi) : BinaryRealGL)) =
      flowPoint s := by
  have det : 0 < (pivotConjugate ((diagonalFlow s : unimodularLevi) : BinaryRealGL)).val.det := by
    rw [det_pivotConjugate]
    change 0 < (diagonalFlowMatrix s).val.det
    rw [det_diagonalFlowMatrix]
    exact one_pos
  rw [basePoint, coe_smul_I_of_upper det (by rw [pivotConjugate_diagonalFlow_val]; simp),
    pivotConjugate_diagonalFlow_val, flowPoint]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Complex.ofReal_zero, add_zero]
  have hexp : Real.exp (-2 * s) = Real.exp (-s) / Real.exp s := by
    rw [← Real.exp_sub]
    ring_nf
  rw [hexp, Complex.ofReal_div]
  have := Real.exp_pos s
  field_simp

theorem binaryComplexReflection_flowPoint (s : ℝ) :
    binaryComplexReflection (flowPoint s) = flowPoint s := by
  rw [flowPoint, binaryComplexReflection]
  simp only [_root_.neg_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  ring

theorem flowPoint_zero : flowPoint 0 = Complex.I := by
  simp [flowPoint]

theorem hasDerivAt_flowPoint : HasDerivAt flowPoint (-2 * Complex.I) 0 := by
  have real := ((hasDerivAt_id (0 : ℝ)).const_mul (-2)).exp
  have complex := real.ofReal_comp.mul_const Complex.I
  refine complex.congr_deriv ?_
  simp

theorem edgeNormal_diagonalFlow (F : BinaryAdelicGL → ℂ → ℂ) (s : ℝ) (h : BinaryAdelicGL) :
    edgeNormal n F (diagonalFlow s) h = binarySwap n ((2 : ℂ)⁻¹ •
      eichlerPeriod n F (flowPoint s) h - (2 : ℂ)⁻¹ •
        binaryCoefficient n UpperHalfPlane.J
          (eichlerPeriod n F (flowPoint s) (h * atInfinity UpperHalfPlane.J))) := by
  have unimodular : |(UpperHalfPlane.J : BinaryRealGL).val.det| = 1 := by
    rw [det_upperJ, abs_neg, abs_one]
  rw [edgeNormal, eichlerTwisted, eichlerHolomorphic, eichlerAntiholomorphic,
    binaryAmbientRepresentation_apply_of_unimodular unimodular,
    basePoint_pivotConjugate_diagonalFlow, binaryComplexReflection_flowPoint]

theorem hasDerivAt_functional_eichlerPeriod_flow {F : BinaryAdelicGL → ℂ → ℂ}
    (hF : EichlerData n F) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ)
    (h : BinaryAdelicGL) :
    HasDerivAt (fun s => functional (eichlerPeriod n F (flowPoint s) h))
      (functional (F h Complex.I • binaryPointPower (n + 1) Complex.I) * (-2 * Complex.I)) 0 := by
  have coordinates (i : Fin (n + 2)) : HasDerivAt
      (fun s => (binaryWeightBasis (n + 1)).coord i (eichlerPeriod n F (flowPoint s) h))
      (F h Complex.I * (binaryWeightBasis (n + 1)).coord i (binaryPointPower (n + 1) Complex.I) *
        (-2 * Complex.I)) 0 :=
    (hasDerivAt_coord_eichlerPeriod F hF.holomorphic (by simp) h i).comp_of_eq 0
      hasDerivAt_flowPoint flowPoint_zero.symm
  have sum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (coordinates i).mul_const (functional (binaryWeightBasis (n + 1) i))
  have e : (fun s => functional (eichlerPeriod n F (flowPoint s) h)) = fun s =>
      ∑ i, (binaryWeightBasis (n + 1)).coord i (eichlerPeriod n F (flowPoint s) h) *
        functional (binaryWeightBasis (n + 1) i) :=
    funext fun s => functional_apply_eq_sum _ _ _
  rw [e]
  refine sum.congr_deriv ?_
  rw [functional_apply_eq_sum (binaryWeightBasis (n + 1)) functional, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  ring

end EdgeExplicit

/-- **The velocity of the transported twisted normal form.** Along the diagonal flow `a(s)`,
every weight-basis coordinate of `edgeNormal F (a(s)) h` has derivative at `s = 0` the coordinate
of `edgeNormalVelocity n F h`. -/
theorem hasDerivAt_edgeNormal_diagonal {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
    (h : BinaryAdelicGL) (j : Fin (n + 2)) :
    HasDerivAt (fun s => (binaryWeightBasis (n + 1)).coord j (edgeNormal n F (diagonalFlow s) h))
      ((binaryWeightBasis (n + 1)).coord j (edgeNormalVelocity n F h)) 0 := by
  set functional := (binaryWeightBasis (n + 1)).coord j ∘ₗ binarySwap n
  have unimodular : |(UpperHalfPlane.J : BinaryRealGL).val.det| = 1 := by
    rw [det_upperJ, abs_neg, abs_one]
  have first := hasDerivAt_functional_eichlerPeriod_flow hF functional h
  have second := hasDerivAt_functional_eichlerPeriod_flow hF
    (functional ∘ₗ binaryCoefficient n UpperHalfPlane.J) (h * atInfinity UpperHalfPlane.J)
  have e : (fun s => (binaryWeightBasis (n + 1)).coord j (edgeNormal n F (diagonalFlow s) h)) =
      fun s => (2 : ℂ)⁻¹ * functional (eichlerPeriod n F (flowPoint s) h) - (2 : ℂ)⁻¹ *
        (functional ∘ₗ binaryCoefficient n UpperHalfPlane.J)
          (eichlerPeriod n F (flowPoint s) (h * atInfinity UpperHalfPlane.J)) := by
    funext s
    rw [edgeNormal_diagonalFlow]
    simp only [functional, LinearMap.comp_apply, map_sub, map_smul, smul_eq_mul]
  rw [e]
  refine ((first.const_mul _).sub (second.const_mul _)).congr_deriv ?_
  rw [edgeNormalVelocity, binaryAmbientRepresentation_apply_of_unimodular unimodular]
  simp only [functional, LinearMap.comp_apply, map_add, map_smul, smul_eq_mul]
  ring

end TernaryPeriodPolynomials.AnalyticClasses
