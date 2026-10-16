module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EdgeControl.EdgeGeometry

@[expose] public section


/-!
# Integrability of the transported edges of the explicit total primitive

For a controlled one-cochain `K` of the real plane group, consider the edge cochain
`E(y₀, y₁) = π(y₀) · K(π(y₀)⁻¹ π(y₁))`, `π` the real-plane point of the Gram–Schmidt vertex. Moved
by the good-line argument `g(u)` and transported back, the value at an edge `(x, y)` is

`|det A|^{(n+3)/2} s^{-(n+3)} · (x κ⁻¹) · K(q(u))`,

with `s = 1 / corner` the corner scale of the Gram–Schmidt vertex of `g(u) x`, `κ` orthogonal and
`q(u)` of bounded shape. Unimodularity gives `|det A| = s³`, so every scalar test is bounded by
`C · s^{(n+3)/2} = C (1 + |v|²)^{-(n+3)/4}` with `v` the transformed radical coordinate, and is
continuous in `u`. Hence the finite good-line averages are absolutely integrable at `s = -3/2`
(`n ≥ 5`). Applied to the explicit total primitive of the chosen relative of the normalized source
this proves `EdgeIntegrable` for `totalPrimitiveEdge`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.ArchimedeanConstant

namespace TernaryPeriodPolynomials.EdgeControl

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

variable {n : ℕ}

/-- The homogeneous edge cochain of a one-cochain on the real plane group. -/
def homogeneousEdge (data : InducingData n)
    (cochain : RealPlaneGroup → realPlaneCuspidalRep n data.cusp data.chi) : EdgeCochain data :=
  fun V => homogeneousOne (realPlaneCuspidalRep n data.cusp data.chi) cochain
    (gsPlaneVertex (V 0)) (gsPlaneVertex (V 1))

theorem goodLineForm_corner_ne_zero {y : RealGL3} (form : GoodLineForm y) : y.val 2 2 ≠ 0 := by
  obtain ⟨B, w, -, rfl⟩ := form
  rw [planeLevi_standard_corner]
  exact one_ne_zero

theorem det_realPlaneMatrix (element : RealPlaneGroup) :
    (realPlaneMatrix element).val.det = element.right.val.det := by
  rw [realPlaneMatrix_apply, Units.val_mul, Matrix.det_mul]
  have unipotent : (realPlaneRadicalMatrix element.left).val.det = 1 := by
    simp [realPlaneRadicalMatrix, planeUnipotent, Matrix.det_fin_three]
  have levi : (planeLevi element.right 1).val.det = element.right.val.det := by
    simp [planeLevi, planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
  rw [unipotent, levi, one_mul]

/-- The coefficient of a monomial, as a linear functional. -/
def coeffFunctional (m : Fin 3 →₀ ℕ) : HomogeneousPoly n →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ m).comp (homogeneousSubmodule (Fin 3) ℂ n).subtype

theorem coeffFunctional_apply (m : Fin 3 →₀ ℕ) (p : HomogeneousPoly n) :
    coeffFunctional m p = p.val.coeff m := rfl

section Moving

variable (data : InducingData n)
  (cochain : RealPlaneGroup → realPlaneCuspidalRep n data.cusp data.chi) (x y : RealGL3)
  (u : ℝ × ℝ)

/-- The edge argument. -/
def edgeArgument : RealPlaneGroup :=
  (gsPlaneVertex (standardGoodLineRealArgument u * x))⁻¹ *
    gsPlaneVertex (standardGoodLineRealArgument u * y)

/-- **The transported edge, value by value.** -/
theorem edgeTransported_homogeneous_apply (trivial : data.chi = trivialCharacter)
    (form : GoodLineForm (standardGoodLineRealArgument u * x)) (argument : BinaryAdelicGL) :
    (edgeTransported data (homogeneousEdge data cochain) u x y).val argument =
      normPower (GeneralLinearGroup.det
          (atInfinity (gsPlaneVertex (standardGoodLineRealArgument u * x)).right))
          (((n : ℂ) + 3) / 2) •
        ((((cornerScale (gsVertex (standardGoodLineRealArgument u * x)) : ℝ) : ℂ)⁻¹ ^ (n + 3)) •
          realCoefficientComponent n trivialCharacter
            (x * (gsOrth (gsChart (standardGoodLineRealArgument u * x)))⁻¹)
            ((cochain (edgeArgument x y u) : cuspidalTensorValues data.cusp (HomogeneousPoly n)).val
              (argument * atInfinity (gsPlaneVertex (standardGoodLineRealArgument u *
                  x)).right))) := by
  set M := standardGoodLineRealArgument u
  set π := gsPlaneVertex (M * x)
  set κ := gsOrth (gsChart (M * x))
  set s := cornerScale (gsVertex (M * x))
  have matrix : M⁻¹ * realPlaneMatrix π = GeneralLinearGroup.scalar (Fin 3) s * (x * κ⁻¹) := by
    rw [gsPlaneVertex_matrix form, ← mul_assoc, ← GeneralLinearGroup.scalar_commute, mul_assoc]
    congr 1
    group
    rfl
  change realCoefficientComponent n data.chi M⁻¹
      (normPower (GeneralLinearGroup.det (atInfinity π.right)) (((n : ℂ) + 3) / 2) •
        realCoefficientComponent n data.chi (realPlaneMatrix π)
          ((cochain (edgeArgument x y u) : cuspidalTensorValues data.cusp (HomogeneousPoly n)).val
            (argument * atInfinity π.right))) = _
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, trivial, matrix,
    map_mul, Module.End.mul_apply, realCoefficientComponent_scalar]

theorem abs_det_gsPlaneVertex_right {X : RealGL3} (form : GoodLineForm X) :
    |(gsPlaneVertex X).right.val.det| = (cornerScale (gsVertex X) : ℝ) ^ 3 := by
  rw [← det_realPlaneMatrix, gsPlaneVertex_matrix form, ← gsVertex_eq_mul, Units.val_mul,
    scalar_val_three, Matrix.det_mul, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, abs_mul, goodLineForm_unimodular form, mul_one,
    abs_of_pos (pow_pos (cornerScale_pos _) 3)]

theorem scale_exponent (s : ℝ) (hs : 0 < s) :
    (s ^ 3) ^ (((n : ℝ) + 3) / 2) * (s⁻¹) ^ (n + 3) = s ^ (((n : ℝ) + 3) / 2) := by
  rw [← Real.rpow_natCast s 3, ← Real.rpow_mul hs.le, inv_pow, ← Real.rpow_natCast s (n + 3),
    ← Real.rpow_neg hs.le, ← Real.rpow_add hs]
  congr 1
  push_cast
  ring

/-- **Uniform bound of the transported edges.** -/
theorem edgeTransported_homogeneous_bound (trivial : data.chi = trivialCharacter)
    (controlled : OneControlled data.cusp (fun element =>
      (cochain element : cuspidalTensorValues data.cusp (HomogeneousPoly n))))
    (fx : ∀ u, GoodLineForm (standardGoodLineRealArgument u * x))
    (fy : ∀ u, GoodLineForm (standardGoodLineRealArgument u * y))
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ × ℝ) (argument : BinaryAdelicGL),
      ‖functional ((edgeTransported data (homogeneousEdge data cochain) u x y).val argument)‖ ≤
        (cornerScale (gsVertex (standardGoodLineRealArgument u * x)) : ℝ) ^ (((n : ℝ) + 3) / 2) *
          C := by
  obtain ⟨B, hB0, hB⟩ := functional_coefficient_bound (n := n) x functional
  have positive : 0 < (Real.sqrt (frobeniusSq (x⁻¹ * y)))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (frobeniusSq_pos _))
  have bounds (m : Fin 3 →₀ ℕ) := controlled.shape_bound (x⁻¹ * y)
    (b := Real.sqrt (frobeniusSq (y⁻¹ * x))) positive (coeffFunctional m)
  choose C hC0 hC using bounds
  refine ⟨∑ m ∈ degreeMonomials n, B m * C m,
    Finset.sum_nonneg (fun m _ => mul_nonneg (hB0 m) (hC0 m)), fun u argument => ?_⟩
  rw [edgeTransported_homogeneous_apply data cochain x y u trivial (fx u), map_smul, map_smul,
    smul_eq_mul, smul_eq_mul, norm_mul, norm_mul]
  set X := standardGoodLineRealArgument u * x
  set s := (cornerScale (gsVertex X) : ℝ) with hs
  have spos : 0 < s := cornerScale_pos _
  set Y := ((cochain (edgeArgument x y u) : cuspidalTensorValues data.cusp (HomogeneousPoly n)).val
    (argument * atInfinity (gsPlaneVertex X).right))
  have first : ‖normPower (GeneralLinearGroup.det (atInfinity (gsPlaneVertex X).right))
      (((n : ℂ) + 3) / 2)‖ = (s ^ 3) ^ (((n : ℝ) + 3) / 2) := by
    have exponent : ((n : ℂ) + 3) / 2 = ((((n : ℝ) + 3) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [exponent, norm_normPower_det_atInfinity, abs_det_gsPlaneVertex_right (fx u)]
  have second : ‖((s : ℂ))⁻¹ ^ (n + 3)‖ = (s⁻¹) ^ (n + 3) := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg spos.le]
  have coefficient (m : Fin 3 →₀ ℕ) : ‖Y.val.coeff m‖ ≤ C m := by
    have realize := cuspidalTensorFunctional_realize data.cusp (coeffFunctional m)
      (cochain (edgeArgument x y u)) (argument * atInfinity (gsPlaneVertex X).right)
    rw [coeffFunctional_apply] at realize
    rw [← realize]
    refine (CuspSupNorm.realize_le_cuspSupNorm _ _).trans ?_
    have member := edgeArgument_mem x y u (fx u) (fy u)
    have bound := hC m _ member
    rw [matrixPlanePoint_realPlaneMatrix] at bound
    exact bound
  have third : ‖functional (realCoefficientComponent n trivialCharacter
      (x * (gsOrth (gsChart X))⁻¹) Y)‖ ≤ ∑ m ∈ degreeMonomials n, B m * C m :=
    (hB _ (gsOrth_inv_mem _) Y).trans (Finset.sum_le_sum (fun m _ =>
      mul_le_mul_of_nonneg_left (coefficient m) (hB0 m)))
  rw [first, second, ← mul_assoc, scale_exponent s spos]
  exact mul_le_mul_of_nonneg_left third (Real.rpow_nonneg spos.le _)

/-- The real-plane point of the Gram–Schmidt vertex of a moved big-cell vertex is continuous. -/
theorem planeContinuous_gsPlaneVertex (fx : ∀ u, GoodLineForm (standardGoodLineRealArgument u * x))
    :
    PlaneContinuous (fun u => gsPlaneVertex (standardGoodLineRealArgument u * x)) :=
  planeContinuous_planeNormalize (continuous_prismVertex x (fun u => goodLineForm_corner_ne_zero
      (fx u)))
    (fun u => (fx u).gsVertex_mem) (fun u => (fx u).corner_pos)

/-- **The transported edges form a controlled family in the radical coordinate.** -/
theorem edgeTransported_homogeneous_controlled (trivial : data.chi = trivialCharacter)
    (controlled : OneControlled data.cusp (fun element =>
      (cochain element : cuspidalTensorValues data.cusp (HomogeneousPoly n))))
    (fx : ∀ u, GoodLineForm (standardGoodLineRealArgument u * x))
    (fy : ∀ u, GoodLineForm (standardGoodLineRealArgument u * y)) :
    Controlled data.cusp (fun u => edgeTransported data (homogeneousEdge data cochain) u x y) := by
  have hx := planeContinuous_gsPlaneVertex x fx
  have hy := planeContinuous_gsPlaneVertex y fy
  have argument := controlled (ℝ × ℝ) _ (hx.inv.mul hy)
  have moved := argument.plane_character trivial hx
  have result := moved.map (homogeneousBasis n)
    (linear := fun u => realCoefficientComponent n data.chi (standardGoodLineRealArgument u)⁻¹)
    (fun vector functional => by
      rw [trivial]
      exact realCoefficientComponent_functional_continuous _
        continuous_standardGoodLineRealArgument.inv vector functional)
  exact result

/-- **Absolute integrability of the transported homogeneous edges.** -/
theorem homogeneousEdge_average_integrable (large : 5 ≤ n) (trivial : data.chi = trivialCharacter)
    (controlled : OneControlled data.cusp (fun element =>
      (cochain element : cuspidalTensorValues data.cusp (HomogeneousPoly n))))
    (finite : EdgeFinite data (homogeneousEdge data cochain))
    (fx : ∀ u, GoodLineForm (standardGoodLineRealArgument u * x))
    (fy : ∀ u, GoodLineForm (standardGoodLineRealArgument u * y))
    (transform : ℝ × ℝ → ℝ × ℝ)
    (preserving : MeasurePreserving transform ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume))
    (radius : ∀ u, (gsVertex (standardGoodLineRealArgument u * x)).val 2 2 = gsRadius (transform u))
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (edgeAverage data (homogeneousEdge data cochain) functional x y)
      ((volume : Measure ℝ).prod volume) := by
  have three : 3 < n := by omega
  have convergent : 3 < (finiteExponent n cohomologicalPoint).re := by
    rw [finiteExponent_re]
    have : (3 : ℝ) < n := by exact_mod_cast three
    norm_num [cohomologicalPoint]
    linarith
  obtain ⟨C, hC0, hC⟩ := edgeTransported_homogeneous_bound data cochain x y trivial controlled fx fy
    functional
  have continuity := finiteAverage_continuous three data.cusp
    (fun u => cuspidalTensorFunctional data.cusp functional
      (edgeTransported data (homogeneousEdge data cochain) u x y))
    (fun u => edgeTransported_spherical data _ finite u x y functional)
    ((edgeTransported_homogeneous_controlled data cochain x y trivial controlled fx
        fy).continuous_one
      functional)
  have dominating : Integrable (fun u => weightMass (finiteExponent n cohomologicalPoint).re * C *
      kernelBase (transform u) ^ (-(((n : ℝ) + 3) / 4))) ((volume : Measure ℝ).prod volume) :=
    (preserving.integrable_comp_of_integrable (kernelBase_decay_integrable large)).const_mul _
  refine dominating.mono' continuity.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  have scale : (cornerScale (gsVertex (standardGoodLineRealArgument u * x)) : ℝ) ^
      (((n : ℝ) + 3) / 2) = kernelBase (transform u) ^ (-(((n : ℝ) + 3) / 4)) := by
    rw [cornerScale_gsVertex (fx u), radius u, ← abs_of_pos (inv_pos.mpr (gsRadius_pos _)),
      gsRadius_inv_rpow]
    congr 2
    ring
  have pointwise : ∀ A, ‖data.cusp.realize (cuspidalTensorFunctional data.cusp functional
      (edgeTransported data (homogeneousEdge data cochain) u x y)) A‖ ≤
      kernelBase (transform u) ^ (-(((n : ℝ) + 3) / 4)) * C := by
    intro A
    rw [cuspidalTensorFunctional_realize, ← scale]
    exact hC u A
  refine (norm_goodLineFiniteVectorIntegral_le data.cusp cohomologicalPoint convergent _
    (edgeTransported_spherical data _ finite u x y functional) _ pointwise).trans (le_of_eq ?_)
  ring

end Moving

end TernaryPeriodPolynomials.EdgeControl
