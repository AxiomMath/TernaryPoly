module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Iwasawa.PrismDecay
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.FiniteFamilyBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteGlobalIntegrability

@[expose] public section


/-!
# Continuity of the Iwasawa prism values in the radical coordinate

On the big cell the Gram–Schmidt vertex map is continuous, so the bounded-shape simplices of the
prism terms move continuously with the radical coordinate `u`. With the continuity of the bounded
realizations of source-cochain cusp vectors this makes every scalar test of the prism value a
continuous map into the bounded functions, and therefore makes its finite good-line average continuous
in `u`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

theorem continuous_gsOrth : Continuous gsOrth :=
  Units.continuous_iff.mpr ⟨continuous_gsOrthMatrix, continuous_gsOrthMatrix.matrix_transpose⟩

theorem continuous_lineUnipotent_real :
    Continuous (fun u : ℝ × ℝ => (lineUnipotent u.1 u.2 : RealGL3)) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi; intro i; apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;> simp [lineUnipotent, upperUnipotent] <;> fun_prop
  · apply continuous_pi; intro i; apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;> simp [lineUnipotent, upperUnipotent] <;> fun_prop

theorem continuous_standardGoodLineRealArgument : Continuous standardGoodLineRealArgument := by
  unfold standardGoodLineRealArgument
  exact (continuous_const.mul continuous_lineUnipotent_real).mul continuous_const

theorem continuous_gsChart_comp {X : Type*} [TopologicalSpace X] (g : X → RealGL3) (hg : Continuous g)
    (corner : ∀ x, (g x).val 2 2 ≠ 0) : Continuous (fun x => gsChart (g x)) := by
  have hval : Continuous (fun x => (g x).val) := Units.continuous_val.comp hg
  have entry : ∀ i j, Continuous (fun x => (g x).val i j) := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hval)
  exact ((entry 2 1).div (entry 2 2) corner).prodMk ((entry 2 0).div (entry 2 2) corner)

/-- The orthogonal factor at `g(u) a`. -/
def prismOrth (a : RealGL3) (u : ℝ × ℝ) : RealGL3 := gsOrth (gsChart (standardGoodLineRealArgument u * a))

theorem continuous_prismOrth (a : RealGL3)
    (corner : ∀ u, (standardGoodLineRealArgument u * a).val 2 2 ≠ 0) : Continuous (prismOrth a) :=
  continuous_gsOrth.comp (continuous_gsChart_comp _ (continuous_standardGoodLineRealArgument.mul
    continuous_const) corner)

theorem continuous_prismVertex (a : RealGL3)
    (corner : ∀ u, (standardGoodLineRealArgument u * a).val 2 2 ≠ 0) :
    Continuous (fun u => gsVertex (standardGoodLineRealArgument u * a)) := by
  have e : (fun u => gsVertex (standardGoodLineRealArgument u * a)) =
      fun u => standardGoodLineRealArgument u * a * (prismOrth a u)⁻¹ := by
    funext u; rfl
  rw [e]
  exact (continuous_standardGoodLineRealArgument.mul continuous_const).mul (continuous_prismOrth a corner).inv

/-- **The bounded realization of a scalar test of the prism value, as a finite combination.** -/
theorem prism_boundedRealization_eq (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (a b : RealGL3) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (u : ℝ × ℝ) :
    CuspSupNorm.boundedRealization data.cusp
        (cuspidalTensorFunctional data.cusp functional (goodLineIwasawaPrism data source cocycle u ![a, b])) =
      ∑ m ∈ degreeMonomials n,
        functional (realCoefficientComponent n trivialCharacter (a * (prismOrth a u)⁻¹) (monomialVector n m)) •
          (CuspSupNorm.boundedRealization data.cusp (cochainCuspVector data source cocycle m
              ![1, prismOrth a u, prismOrth a u * (a⁻¹ * b)] (gsVertex (standardGoodLineRealArgument u * a))) -
            CuspSupNorm.boundedRealization data.cusp (cochainCuspVector data source cocycle m
              ![1, prismOrth a u * (a⁻¹ * b) * (prismOrth b u)⁻¹, prismOrth a u * (a⁻¹ * b)]
              (gsVertex (standardGoodLineRealArgument u * a)))) := by
  apply Subtype.ext
  funext A
  change data.cusp.realize _ A = _
  rw [cuspidalTensorFunctional_realize, goodLineIwasawaPrism_value, trivial]
  rw [show gsOrth (gsChart (standardGoodLineRealArgument u * a)) = prismOrth a u from rfl,
    show gsOrth (gsChart (standardGoodLineRealArgument u * b)) = prismOrth b u from rfl]
  set g := a * (prismOrth a u)⁻¹ with hg
  set Y : HomogeneousPoly n := normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2)) •
    (source ![1, prismOrth a u, prismOrth a u * (a⁻¹ * b)]
        (planeLevi A 1 * 1 * atInfinity (gsVertex (standardGoodLineRealArgument u * a))) -
      source ![1, prismOrth a u * (a⁻¹ * b) * (prismOrth b u)⁻¹, prismOrth a u * (a⁻¹ * b)]
        (planeLevi A 1 * 1 * atInfinity (gsVertex (standardGoodLineRealArgument u * a)))) with hY
  have key : functional (realCoefficientComponent n trivialCharacter g Y) =
      ∑ m ∈ degreeMonomials n, Y.val.coeff m *
        functional (realCoefficientComponent n trivialCharacter g (monomialVector n m)) :=
    functional_eq_sum_coeff (functional.comp (realCoefficientComponent n trivialCharacter g)) Y
  rw [key]
  simp only [AddSubgroup.val_finsetSum, lp.coeFn_smul, lp.coeFn_sub]
  change _ = (∑ m ∈ degreeMonomials n, (functional (realCoefficientComponent n trivialCharacter g
      (monomialVector n m)) • ((CuspSupNorm.boundedRealization data.cusp (cochainCuspVector data source cocycle m
          ![1, prismOrth a u, prismOrth a u * (a⁻¹ * b)] (gsVertex (standardGoodLineRealArgument u * a))) :
            BinaryAdelicGL → ℂ) -
        (CuspSupNorm.boundedRealization data.cusp (cochainCuspVector data source cocycle m
          ![1, prismOrth a u * (a⁻¹ * b) * (prismOrth b u)⁻¹, prismOrth a u * (a⁻¹ * b)]
          (gsVertex (standardGoodLineRealArgument u * a))) : BinaryAdelicGL → ℂ)) :
      BinaryAdelicGL → ℂ)) A
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro m _
  change _ = _ * (data.cusp.realize _ A - data.cusp.realize _ A)
  rw [← coeff_source_translate, ← coeff_source_translate, mul_comm]
  congr 1
  rw [hY, Submodule.coe_smul, Submodule.coe_sub, coeff_smul, coeff_sub, smul_eq_mul, mul_sub]


theorem snoc_continuous {X : Type*} [TopologicalSpace X] (V : X → Fin 3 → RealGL3) (h : X → RealGL3)
    (hV : Continuous V) (hh : Continuous h) :
    Continuous (fun x => (Fin.snoc (V x) (h x) : Fin 4 → RealGL3)) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have e : (fun x => (Fin.snoc (V x) (h x) : Fin 4 → RealGL3) (Fin.last 3)) = h := by
      funext x
      exact Fin.snoc_last (α := fun _ => RealGL3) (h x) (V x)
    rw [e]; exact hh
  · have e : (fun x => (Fin.snoc (V x) (h x) : Fin 4 → RealGL3) j.castSucc) = fun x => V x j := by
      funext x
      exact Fin.snoc_castSucc (α := fun _ => RealGL3) (h x) (V x) j
    rw [e]; exact (continuous_apply j).comp hV

theorem cochainCuspVector_comp_continuous (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ)
    {X : Type*} [TopologicalSpace X] (V : X → Fin 3 → RealGL3) (h : X → RealGL3)
    (hV : Continuous V) (hh : Continuous h) :
    Continuous (fun x => CuspSupNorm.boundedRealization data.cusp
      (cochainCuspVector data source cocycle m (V x) (h x))) := by
  have composite := (cochainCuspVector_boundedRealization_continuous data source cocycle m).comp
    (snoc_continuous V h hV hh)
  have e : (fun x => CuspSupNorm.boundedRealization data.cusp
      (cochainCuspVector data source cocycle m (V x) (h x))) =
      ((fun x : Fin 4 → RealGL3 => CuspSupNorm.boundedRealization data.cusp
        (cochainCuspVector data source cocycle m (fun i => x i.castSucc) (x (Fin.last 3)))) ∘
        fun x => (Fin.snoc (V x) (h x) : Fin 4 → RealGL3)) := by
    funext x
    simp only [Function.comp, Fin.snoc_castSucc, Fin.snoc_last]
  rw [e]
  exact composite

/-- **Continuity of the scalar tests of the prism value in the radical coordinate.** -/
theorem prism_boundedRealization_continuous (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (a b : RealGL3) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (cornerA : ∀ u, (standardGoodLineRealArgument u * a).val 2 2 ≠ 0)
    (cornerB : ∀ u, (standardGoodLineRealArgument u * b).val 2 2 ≠ 0) :
    Continuous (fun u => CuspSupNorm.boundedRealization data.cusp
      (cuspidalTensorFunctional data.cusp functional (goodLineIwasawaPrism data source cocycle u ![a, b]))) := by
  rw [funext (prism_boundedRealization_eq data trivial source cocycle a b functional)]
  have hκa := continuous_prismOrth a cornerA
  have hκb := continuous_prismOrth b cornerB
  have hh := continuous_prismVertex a cornerA
  apply continuous_finsetSum
  intro m _
  have hs : Continuous (fun u => functional (realCoefficientComponent n trivialCharacter
      (a * (prismOrth a u)⁻¹) (monomialVector n m))) :=
    realCoefficientComponent_functional_continuous (fun u => a * (prismOrth a u)⁻¹)
      (continuous_const.mul hκa.inv) _ _
  have h1 := cochainCuspVector_comp_continuous data source cocycle m
    (fun u => ![1, prismOrth a u, prismOrth a u * (a⁻¹ * b)])
    (fun u => gsVertex (standardGoodLineRealArgument u * a))
    (vector3_continuous (fun _ => 1) (prismOrth a) (fun u => prismOrth a u * (a⁻¹ * b))
      continuous_const hκa (hκa.mul continuous_const)) hh
  have h2 := cochainCuspVector_comp_continuous data source cocycle m
    (fun u => ![1, prismOrth a u * (a⁻¹ * b) * (prismOrth b u)⁻¹, prismOrth a u * (a⁻¹ * b)])
    (fun u => gsVertex (standardGoodLineRealArgument u * a))
    (vector3_continuous (fun _ => 1) (fun u => prismOrth a u * (a⁻¹ * b) * (prismOrth b u)⁻¹)
      (fun u => prismOrth a u * (a⁻¹ * b)) continuous_const
      ((hκa.mul continuous_const).mul hκb.inv) (hκa.mul continuous_const)) hh
  exact hs.smul (h1.sub h2)

/-- Linearity of the finite good-line average at the cohomological point. -/
theorem goodLineFiniteVectorIntegral_endpoint_sub (large : 3 < n) (cusp : CuspidalRepresentation)
    (v w : cusp.smooth) (hv : v.val ∈ cuspSphericalValues cusp) (hw : w.val ∈ cuspSphericalValues cusp) :
    goodLineFiniteVectorIntegral n cusp cohomologicalPoint (v - w) =
      goodLineFiniteVectorIntegral n cusp cohomologicalPoint v -
        goodLineFiniteVectorIntegral n cusp cohomologicalPoint w := by
  unfold goodLineFiniteVectorIntegral
  rw [← integral_sub (goodLineFiniteVectorIntegrand_endpoint_integrable n large cusp v hv)
    (goodLineFiniteVectorIntegrand_endpoint_integrable n large cusp w hw)]
  congr 1
  funext finite
  rw [map_sub, Pi.sub_apply, mul_sub]

/-- **Continuity of the finite average along a family with continuous bounded realization.** -/
theorem finiteAverage_continuous (large : 3 < n) (cusp : CuspidalRepresentation)
    {X : Type*} [TopologicalSpace X] (w : X → cusp.smooth)
    (spherical : ∀ x, (w x).val ∈ cuspSphericalValues cusp)
    (continuity : Continuous (fun x => CuspSupNorm.boundedRealization cusp (w x))) :
    Continuous (fun x => goodLineFiniteVectorIntegral n cusp cohomologicalPoint (w x)) := by
  have convergent : 3 < (finiteExponent n cohomologicalPoint).re := by
    rw [finiteExponent_re]
    have : (3 : ℝ) < n := by exact_mod_cast large
    norm_num [cohomologicalPoint]
    linarith
  set C := weightMass (finiteExponent n cohomologicalPoint).re
  have bound : ∀ x y, dist (goodLineFiniteVectorIntegral n cusp cohomologicalPoint (w y))
      (goodLineFiniteVectorIntegral n cusp cohomologicalPoint (w x)) ≤
      C * dist (CuspSupNorm.boundedRealization cusp (w y)) (CuspSupNorm.boundedRealization cusp (w x)) := by
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← goodLineFiniteVectorIntegral_endpoint_sub large cusp _ _
      (spherical y) (spherical x), ← map_sub]
    apply norm_goodLineFiniteVectorIntegral_le cusp cohomologicalPoint convergent (w y - w x)
      ((cuspSphericalValues cusp).sub_mem (spherical y) (spherical x))
    intro argument
    exact lp.norm_apply_le_norm (by simp) (CuspSupNorm.boundedRealization cusp (w y - w x)) argument
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have limit := (tendsto_iff_dist_tendsto_zero.mp (continuity.continuousAt (x := x))).const_mul C
  rw [mul_zero] at limit
  exact squeeze_zero (fun y => dist_nonneg) (fun y => bound x y) limit

end TernaryPeriodPolynomials.AnalyticClasses
