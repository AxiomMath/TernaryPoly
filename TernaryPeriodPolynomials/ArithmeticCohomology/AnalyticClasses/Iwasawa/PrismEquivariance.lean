module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Iwasawa.PrismIntegrability
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.FinAvgLeviInvariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorAnalyticMaps
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.FlatParameterScaling
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.CompactReduction

@[expose] public section


/-!
# Equivariance of the integrated Iwasawa prism cochain

Moving both vertices of a prism edge by a radical element of the good-line stabilizer translates the
radical coordinate; moving them by a Levi element applies the real Levi transform to the radical
coordinate and translates the cusp values at infinity by the conjugated `GL₂` block. The finite
good-line average ignores that translation (`goodLineFiniteVectorIntegral_realTranslate`) and Lebesgue
measure ignores both changes of variables. Hence the integrated prism scalars satisfy
`I_ℓ(q x, q y) = I_{ℓ ∘ ρ(q)}(x, y)` for both kinds of generators `q` of the good-line stabilizer.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The finite good-line average of a scalar test of a prism edge. -/
def prismEdgeAverage (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (x y : RealGL3) (u : ℝ × ℝ) : ℂ :=
  goodLineFiniteVectorIntegral n data.cusp cohomologicalPoint
    (cuspidalTensorFunctional data.cusp functional (goodLineIwasawaPrism data source cocycle u ![x, y]))

/-- The integrated prism scalar of an edge. -/
def prismEdgeIntegral (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (x y : RealGL3) : ℂ :=
  ∫ u, prismEdgeAverage data source cocycle functional x y u ∂((volume : Measure ℝ).prod volume)

theorem prism_edge_pair (M x y : RealGL3) :
    (fun index : Fin 2 => M * (![x, y] : Fin 2 → RealGL3) index) = ![M * x, M * y] := by
  funext index
  fin_cases index <;> rfl

/-- The prism at the real point `M`, with vertices moved by `M`. -/
theorem goodLineIwasawaPrism_apply' (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (u : ℝ × ℝ) (x y : RealGL3) (A : BinaryAdelicGL) :
    (goodLineIwasawaPrism data source cocycle u ![x, y]).val A =
      normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2)) •
        realCoefficientComponent n data.chi (standardGoodLineRealArgument u)⁻¹
          (homogeneousVertexPrism (fun vertices => source vertices (planeLevi A 1 * 1)) gsVertex
            ![standardGoodLineRealArgument u * x, standardGoodLineRealArgument u * y]) := by
  rw [goodLineIwasawaPrism, sourceCuspidalVertexPrism_apply]
  rw [prism_edge_pair]

theorem cuspidalTensorMap_val_apply {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (cusp : CuspidalRepresentation) (linear : V →ₗ[ℂ] W) (values : cuspidalTensorValues cusp V)
    (argument : BinaryAdelicGL) :
    (cuspidalTensorMap cusp linear values).val argument = linear (values.val argument) := rfl

/-- **Radical equivariance of the prism.** -/
theorem goodLineIwasawaPrism_radical (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (u : ℝ × ℝ) (r : RadicalLattice) (x y : RealGL3) :
    goodLineIwasawaPrism data source cocycle u
        ![GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r) * x,
          GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r) * y] =
      cuspidalTensorMap data.cusp
        (realCoefficientComponent n data.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r)))
        (goodLineIwasawaPrism data source cocycle (goodLineRadicalRealShift r u) ![x, y]) := by
  set q := GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r) with hq
  have transport := standardGoodLineRealArgument_radical u r
  rw [← hq] at transport
  have hinv : (standardGoodLineRealArgument u)⁻¹ =
      q * (standardGoodLineRealArgument (goodLineRadicalRealShift r u))⁻¹ := by
    rw [← transport, _root_.mul_inv_rev, mul_inv_cancel_left]
  apply Subtype.ext
  funext A
  rw [cuspidalTensorMap_val_apply, goodLineIwasawaPrism_apply', goodLineIwasawaPrism_apply',
    ← mul_assoc, ← mul_assoc, transport, hinv, map_mul, Module.End.mul_apply, map_smul]


/-- The conjugated integral Levi block. -/
def conjugateLeviInteger (γ : GeneralLinearGroup (Fin 2) ℤ) : GeneralLinearGroup (Fin 2) ℤ :=
  binaryPivotSwap * γ * binaryPivotSwap

theorem realLeviMatrix_conjugate (γ : GeneralLinearGroup (Fin 2) ℤ) :
    realLeviMatrix (conjugateLeviInteger γ) =
      binaryPivotSwap * GeneralLinearGroup.map (Int.castRingHom ℝ) γ * binaryPivotSwap := by
  have hswap : GeneralLinearGroup.map (Int.castRingHom ℝ) (binaryPivotSwap : GeneralLinearGroup (Fin 2) ℤ) =
      binaryPivotSwap := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [binaryPivotSwap, GeneralLinearGroup.map_apply]
  rw [realLeviMatrix, conjugateLeviInteger, map_mul, map_mul, hswap]

theorem normPower_atInfinity_unit {B : BinaryRealGL} (unit : |B.val.det| = 1) (exponent : ℂ) :
    normPower (Matrix.GeneralLinearGroup.det (atInfinity B)) exponent = 1 := by
  rw [normPower, EisensteinRegularization.Helpers.det_atInfinity_binary,
    EisensteinRegularization.Helpers.adeleNorm_realAdeleUnit]
  change Complex.exp (exponent * (Real.log |B.val.det| : ℂ)) = 1
  rw [unit, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

theorem cuspidalTensorFunctional_translation {V : Type} [AddCommGroup V] [Module ℂ V]
    (cusp : CuspidalRepresentation) (functional : V →ₗ[ℂ] ℂ) (element : BinaryAdelicGL)
    (values : cuspidalTensorValues cusp V) :
    cuspidalTensorFunctional cusp functional (cuspidalTensorTranslation cusp element values) =
      ⟨cusp.π element (cuspidalTensorFunctional cusp functional values).val,
        cusp.smooth_stable _ _ (cuspidalTensorFunctional cusp functional values).property⟩ := by
  apply cusp.injective
  funext argument
  rw [cuspidalTensorFunctional_realize, cusp.equivariant, cuspidalTensorFunctional_realize]
  rfl

/-- **Levi equivariance of the prism.** -/
theorem goodLineIwasawaPrism_levi (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (x y : RealGL3) :
    goodLineIwasawaPrism data source cocycle u
        ![GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ) * x,
          GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ) * y] =
      cuspidalTensorMap data.cusp
        (realCoefficientComponent n data.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ)))
        (cuspidalTensorTranslation data.cusp (atInfinity (realLeviMatrix (conjugateLeviInteger γ)))
          (goodLineIwasawaPrism data source cocycle (goodLineLeviRealInput γ u) ![x, y])) := by
  set q := GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ) with hq
  set B := realLeviMatrix (conjugateLeviInteger γ) with hB
  set M := standardGoodLineRealArgument u with hM
  set M' := standardGoodLineRealArgument (goodLineLeviRealInput γ u) with hM'
  have transport : M * q = planeLevi B 1 * M' := by
    rw [hM, hq, standardGoodLineRealArgument_levi, goodLineConjugateRealLevi, hB, realLeviMatrix_conjugate]
  have hC : planeLevi B 1 ∈ planeParabolic ℝ := planeLevi_mem _ _
  have hinv : M⁻¹ * planeLevi B 1 = q * M'⁻¹ := by
    have : planeLevi B 1 = M * q * M'⁻¹ := by rw [transport, mul_inv_cancel_right]
    rw [this]
    simp only [mul_assoc, inv_mul_cancel_left]
  have unit : |B.val.det| = 1 := by
    have h := abs_upperBlockDet_conjugateLevi γ
    rwa [goodLineConjugateRealLevi, upperBlockDet_planeLevi, ← realLeviMatrix_conjugate] at h
  have shift (A : BinaryAdelicGL) : planeLevi A 1 * 1 * atInfinity (planeLevi B 1) =
      planeLevi (A * atInfinity B) 1 * 1 := by
    rw [EisensteinRegularization.Helpers.atInfinity_planeLevi, mul_one, mul_one]
    have h1 : realAdeleUnit (1 : ℝˣ) = 1 := by apply Units.ext; rfl
    rw [h1]
    exact (planeLeviOneHom.map_mul A (atInfinity B)).symm
  have prism (A : BinaryAdelicGL) (y0 y1 : RealGL3) :
      homogeneousVertexPrism (fun vertices => source vertices (planeLevi A 1 * 1)) gsVertex
          ![planeLevi B 1 * y0, planeLevi B 1 * y1] =
        realCoefficientComponent n data.chi (planeLevi B 1)
          (homogeneousVertexPrism (fun vertices => source vertices (planeLevi (A * atInfinity B) 1 * 1))
            gsVertex ![y0, y1]) := by
    simp only [homogeneousVertexPrism, Matrix.cons_val_zero, Matrix.cons_val_one]
    have v1 : (![gsVertex (planeLevi B 1 * y0), planeLevi B 1 * y0, planeLevi B 1 * y1] : Fin 3 → RealGL3) =
        fun i => planeLevi B 1 * (![gsVertex y0, y0, y1] : Fin 3 → RealGL3) i := by
      funext i; fin_cases i <;> simp [gsVertex_plane_mul hC]
    have v2 : (![gsVertex (planeLevi B 1 * y0), gsVertex (planeLevi B 1 * y1), planeLevi B 1 * y1] :
        Fin 3 → RealGL3) = fun i => planeLevi B 1 * (![gsVertex y0, gsVertex y1, y1] : Fin 3 → RealGL3) i := by
      funext i; fin_cases i <;> simp [gsVertex_plane_mul hC]
    rw [v1, v2, cocycle.2.2.1, cocycle.2.2.1, shift, map_sub]
  apply Subtype.ext
  funext A
  rw [cuspidalTensorMap_val_apply]
  change _ = realCoefficientComponent n data.chi q
    ((goodLineIwasawaPrism data source cocycle (goodLineLeviRealInput γ u) ![x, y]).val (A * atInfinity B))
  rw [goodLineIwasawaPrism_apply', goodLineIwasawaPrism_apply', ← mul_assoc, ← mul_assoc, ← hM, ← hM',
    transport, mul_assoc, mul_assoc, prism, ← Module.End.mul_apply, ← map_mul, hinv, map_mul,
    Module.End.mul_apply, map_mul, normPower_mul, normPower_atInfinity_unit unit, map_smul]
  simp only [mul_one]

/-- **Levi equivariance of the prism edge averages.** -/
theorem prismEdgeAverage_levi (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (γ : GeneralLinearGroup (Fin 2) ℤ) (x y : RealGL3) (u : ℝ × ℝ) :
    prismEdgeAverage data source cocycle functional
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ) * x)
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ) * y) u =
      prismEdgeAverage data source cocycle
        (functional.comp (realCoefficientComponent n data.chi
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ)))) x y (goodLineLeviRealInput γ u) := by
  unfold prismEdgeAverage
  rw [goodLineIwasawaPrism_levi, cuspidalTensorFunctional_map, cuspidalTensorFunctional_translation]
  exact goodLineFiniteVectorIntegral_realTranslate n data.cusp cohomologicalPoint (conjugateLeviInteger γ) _
    (goodLineIwasawaPrism_spherical data source cocycle _ ![x, y] _)

/-- **Radical equivariance of the prism edge averages.** -/
theorem prismEdgeAverage_radical (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (r : RadicalLattice) (x y : RealGL3) (u : ℝ × ℝ) :
    prismEdgeAverage data source cocycle functional
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r) * x)
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r) * y) u =
      prismEdgeAverage data source cocycle
        (functional.comp (realCoefficientComponent n data.chi
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r)))) x y
        (goodLineRadicalRealShift r u) := by
  unfold prismEdgeAverage
  rw [goodLineIwasawaPrism_radical, cuspidalTensorFunctional_map]


/-- **Levi equivariance of the integrated prism scalars.** -/
theorem prismEdgeIntegral_levi (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (γ : GeneralLinearGroup (Fin 2) ℤ) (x y : RealGL3) :
    prismEdgeIntegral data source cocycle functional
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ) * x)
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ) * y) =
      prismEdgeIntegral data source cocycle
        (functional.comp (realCoefficientComponent n data.chi
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ)))) x y := by
  unfold prismEdgeIntegral
  simp_rw [prismEdgeAverage_levi]
  exact integral_goodLineLeviRealInput (fun u => prismEdgeAverage data source cocycle _ x y u) γ

theorem goodLineRadicalRealShift_eq_add (r : RadicalLattice) (u : ℝ × ℝ) :
    goodLineRadicalRealShift r u = u + (3 * (r.toAdd.2 : ℝ), 3 * (r.toAdd.1 : ℝ)) := rfl

/-- **Radical equivariance of the integrated prism scalars.** -/
theorem prismEdgeIntegral_radical (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (r : RadicalLattice) (x y : RealGL3) :
    prismEdgeIntegral data source cocycle functional
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r) * x)
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r) * y) =
      prismEdgeIntegral data source cocycle
        (functional.comp (realCoefficientComponent n data.chi
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r)))) x y := by
  unfold prismEdgeIntegral
  simp_rw [prismEdgeAverage_radical, goodLineRadicalRealShift_eq_add]
  exact integral_add_right_eq_self (fun u => prismEdgeAverage data source cocycle _ x y u) _

end TernaryPeriodPolynomials.AnalyticClasses
