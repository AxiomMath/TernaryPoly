module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineIwasawaPrism
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CochainParabolicDecay
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CoefficientContinuity
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.SourceValueBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.MaximalCompact

@[expose] public section


/-!
# Decay of the Iwasawa prism terms

For the Gram–Schmidt vertex map `φ(y) = y k⁻¹`, both simplices of the prism one-cochain at an edge
`(M a, M b)` are translates by `h = φ(M a)` of simplices of bounded shape:
`(φ(Ma), Ma, Mb) = h·(1, κ, κ w)` and `(φ(Ma), φ(Mb), Mb) = h·(1, κ w κ'⁻¹, κ w)` with `w = a⁻¹ b` and
`κ, κ'` orthogonal. Hence every scalar test of the prism value is bounded by
`C · |det A_h|^{(n+3)/2}` with one constant, where `A_h` is the `GL₂` block of `h`. On the big cell
`M a = L g(v)` this is `|det A_L|^{(n+3)/2} (1 + |v|²)^{-(n+3)/4}`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The orthogonal group as a set of real invertible matrices. -/
def realOrthogonalSet : Set RealGL3 := {matrix | matrix.val.transpose * matrix.val = 1}

theorem realOrthogonalSet_isCompact : IsCompact realOrthogonalSet :=
  EisensteinRegularization.Helpers.realOrthogonal_isCompact

theorem gsOrth_mem (u : ℝ × ℝ) : gsOrth u ∈ realOrthogonalSet := gsOrth_orthogonal u

theorem gsOrth_inv_mem (u : ℝ × ℝ) : (gsOrth u)⁻¹ ∈ realOrthogonalSet := gsOrth_inv_orthogonal u

/-- A scalar test of the coefficient action of `a k` with `k` orthogonal is dominated by the
monomial coefficients, uniformly in `k`. -/
theorem functional_coefficient_bound (a : RealGL3) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ∃ B : (Fin 3 →₀ ℕ) → ℝ, (∀ m, 0 ≤ B m) ∧ ∀ k ∈ realOrthogonalSet, ∀ Y : HomogeneousPoly n,
      ‖functional (realCoefficientComponent n trivialCharacter (a * k) Y)‖ ≤
        ∑ m ∈ degreeMonomials n, B m * ‖Y.val.coeff m‖ := by
  have bound (m : Fin 3 →₀ ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ realOrthogonalSet,
      ‖functional (realCoefficientComponent n trivialCharacter (a * k) (monomialVector n m))‖ ≤ C := by
    have continuity := realCoefficientComponent_functional_continuous (fun k : RealGL3 => a * k)
      (continuous_const.mul continuous_id) (monomialVector n m) functional
    obtain ⟨C, hC⟩ := realOrthogonalSet_isCompact.exists_bound_of_continuousOn continuity.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun k hk => (hC k hk).trans (le_max_left _ _)⟩
  choose B hB0 hB using bound
  refine ⟨B, hB0, fun k hk Y => ?_⟩
  have decomposition := norm_functional_le
    (functional.comp (realCoefficientComponent n trivialCharacter (a * k))) Y
  refine decomposition.trans (Finset.sum_le_sum fun m _ => ?_)
  exact mul_le_mul_of_nonneg_right (hB m k hk) (norm_nonneg (Y.val.coeff m))

/-- The bounded-shape simplices of the first prism term. -/
def firstPrismShapes (w : RealGL3) : Set (Fin 3 → RealGL3) :=
  (fun k : RealGL3 => ![1, k, k * w]) '' realOrthogonalSet

/-- The bounded-shape simplices of the second prism term. -/
def secondPrismShapes (w : RealGL3) : Set (Fin 3 → RealGL3) :=
  (fun pair : RealGL3 × RealGL3 => ![1, pair.1 * w * pair.2, pair.1 * w]) ''
    (realOrthogonalSet ×ˢ realOrthogonalSet)

theorem vector3_continuous {X : Type*} [TopologicalSpace X] (f g h : X → RealGL3)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun x => (![f x, g x, h x] : Fin 3 → RealGL3)) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact hf
  · exact hg
  · exact hh

theorem firstPrismShapes_isCompact (w : RealGL3) : IsCompact (firstPrismShapes w) :=
  realOrthogonalSet_isCompact.image
    (vector3_continuous _ _ _ continuous_const continuous_id (continuous_id.mul continuous_const))

theorem secondPrismShapes_isCompact (w : RealGL3) : IsCompact (secondPrismShapes w) :=
  (realOrthogonalSet_isCompact.prod realOrthogonalSet_isCompact).image
    (vector3_continuous _ _ _ continuous_const ((continuous_fst.mul continuous_const).mul continuous_snd)
      (continuous_fst.mul continuous_const))

/-- One coefficient of a translated simplex is a cusp-vector value. -/
theorem coeff_source_translate (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ)
    (vertices : Fin 3 → RealGL3) (h : RealGL3) (A : BinaryAdelicGL) :
    normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2)) *
        (source vertices (planeLevi A 1 * 1 * atInfinity h)).val.coeff m =
      data.cusp.realize (cochainCuspVector data source cocycle m vertices h) A := by
  unfold cochainCuspVector
  rw [CuspVectors.realize_planeCuspVector, mul_one, binaryInductionExponent_plane_endpoint]

/-- **Uniform decay of one bounded-shape simplex value.** -/
theorem bounded_shape_value_bound (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) {K : Set (Fin 3 → RealGL3)} (hK : IsCompact K)
    (m : Fin 3 →₀ ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ h ∈ planeParabolic ℝ, ∀ A : BinaryAdelicGL,
      ‖normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2)) *
        (source x (planeLevi A 1 * 1 * atInfinity h)).val.coeff m‖ ≤
        |upperBlockDet h| ^ (((n : ℝ) + 3) / 2) * C := by
  obtain ⟨C, hC0, hC⟩ := cochainCuspVector_parabolic_bound data source cocycle m hK
    (isCompact_singleton (x := (1 : RealGL3)))
  refine ⟨C, hC0, fun x hx h hh A => ?_⟩
  rw [coeff_source_translate]
  refine (CuspSupNorm.realize_le_cuspSupNorm _ A).trans ?_
  have := hC x hx h hh 1 rfl
  rwa [mul_one] at this


theorem gsVertex_mul_gsOrth (y : RealGL3) : gsVertex y * gsOrth (gsChart y) = y := by
  rw [gsVertex_eq_mul, inv_mul_cancel_right]

/-- **The prism value as a translate of bounded-shape simplices.** -/
theorem goodLineIwasawaPrism_value (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (a b : RealGL3) (u : ℝ × ℝ) (A : BinaryAdelicGL) :
    (goodLineIwasawaPrism data source cocycle u ![a, b]).val A =
      realCoefficientComponent n data.chi
        (a * (gsOrth (gsChart (standardGoodLineRealArgument u * a)))⁻¹)
        (normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2)) •
          (source ![1, gsOrth (gsChart (standardGoodLineRealArgument u * a)),
              gsOrth (gsChart (standardGoodLineRealArgument u * a)) * (a⁻¹ * b)]
              (planeLevi A 1 * 1 * atInfinity (gsVertex (standardGoodLineRealArgument u * a))) -
            source ![1, gsOrth (gsChart (standardGoodLineRealArgument u * a)) * (a⁻¹ * b) *
                (gsOrth (gsChart (standardGoodLineRealArgument u * b)))⁻¹,
              gsOrth (gsChart (standardGoodLineRealArgument u * a)) * (a⁻¹ * b)]
              (planeLevi A 1 * 1 * atInfinity (gsVertex (standardGoodLineRealArgument u * a))))) := by
  set w := a⁻¹ * b with hw
  set M := standardGoodLineRealArgument u with hM
  set h := gsVertex (M * a) with hh
  set κ := gsOrth (gsChart (M * a)) with hκ
  set κ' := (gsOrth (gsChart (M * b)))⁻¹ with hκ'
  have hhκ : h * κ = M * a := gsVertex_mul_gsOrth (M * a)
  have hhb : h * (κ * w) = M * b := by
    rw [← mul_assoc, hhκ, hw, mul_assoc, mul_inv_cancel_left]
  have hφb : h * (κ * w * κ') = gsVertex (M * b) := by
    calc h * (κ * w * κ') = h * (κ * w) * κ' := by simp only [mul_assoc]
      _ = M * b * κ' := by rw [hhb]
      _ = gsVertex (M * b) := by rw [hκ', gsVertex_eq_mul]
  have firstShape : (fun i => h * (![1, κ, κ * w] : Fin 3 → RealGL3) i) =
      ![gsVertex (M * a), M * a, M * b] := by
    funext i
    fin_cases i
    · simp [hh]
    · exact hhκ
    · exact hhb
  have secondShape : (fun i => h * (![1, κ * w * κ', κ * w] : Fin 3 → RealGL3) i) =
      ![gsVertex (M * a), gsVertex (M * b), M * b] := by
    funext i
    fin_cases i
    · simp [hh]
    · exact hφb
    · exact hhb
  have hMh : M⁻¹ * h = a * κ⁻¹ := by
    have : h = M * a * κ⁻¹ := by rw [← hhκ, mul_inv_cancel_right]
    rw [this]
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [goodLineIwasawaPrism, sourceCuspidalVertexPrism_apply]
  have pair : (fun index : Fin 2 => M * (![a, b] : Fin 2 → RealGL3) index) = ![M * a, M * b] := by
    funext index
    fin_cases index <;> rfl
  rw [pair]
  simp only [homogeneousVertexPrism]
  change normPower _ _ • realCoefficientComponent n data.chi M⁻¹
    (source ![gsVertex (M * a), M * a, M * b] (planeLevi A 1 * 1) -
      source ![gsVertex (M * a), gsVertex (M * b), M * b] (planeLevi A 1 * 1)) = _
  rw [← firstShape, ← secondShape, cocycle.2.2.1, cocycle.2.2.1, ← map_sub, ← hMh, map_mul,
    Module.End.mul_apply, map_smul, map_smul]

/-- **Uniform decay of the Iwasawa prism values.** For real vertices `a, b` such that `g(u) a`
always lies in the big cell, every scalar test of the prism value at the edge `(a, b)` is bounded by
`C |det A_h|^{(n+3)/2}` with `h = φ(g(u) a)`. -/
theorem goodLineIwasawaPrism_bound (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (a b : RealGL3) (bigCell : ∀ u, gsVertex (standardGoodLineRealArgument u * a) ∈ planeParabolic ℝ)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ × ℝ) (A : BinaryAdelicGL),
      ‖functional ((goodLineIwasawaPrism data source cocycle u ![a, b]).val A)‖ ≤
        |upperBlockDet (gsVertex (standardGoodLineRealArgument u * a))| ^ (((n : ℝ) + 3) / 2) * C := by
  set w := a⁻¹ * b with hw
  obtain ⟨B, hB0, hB⟩ := functional_coefficient_bound (n := n) a functional
  have first (m : Fin 3 →₀ ℕ) := bounded_shape_value_bound data source cocycle (firstPrismShapes_isCompact w) m
  have second (m : Fin 3 →₀ ℕ) := bounded_shape_value_bound data source cocycle (secondPrismShapes_isCompact w) m
  choose C1 hC10 hC1 using first
  choose C2 hC20 hC2 using second
  refine ⟨∑ m ∈ degreeMonomials n, B m * (C1 m + C2 m),
    Finset.sum_nonneg fun m _ => mul_nonneg (hB0 m) (add_nonneg (hC10 m) (hC20 m)), fun u A => ?_⟩
  set M := standardGoodLineRealArgument u with hM
  set h := gsVertex (M * a) with hh
  set κ := gsOrth (gsChart (M * a)) with hκ
  set κ' := (gsOrth (gsChart (M * b)))⁻¹ with hκ'
  have hhκ : h * κ = M * a := gsVertex_mul_gsOrth (M * a)
  have hhb : h * (κ * w) = M * b := by
    rw [← mul_assoc, hhκ, hw, mul_assoc, mul_inv_cancel_left]
  have hφb : h * (κ * w * κ') = gsVertex (M * b) := by
    calc h * (κ * w * κ') = h * (κ * w) * κ' := by simp only [mul_assoc]
      _ = M * b * κ' := by rw [hhb]
      _ = gsVertex (M * b) := by rw [hκ', gsVertex_eq_mul]
  have firstShape : (fun i => h * (![1, κ, κ * w] : Fin 3 → RealGL3) i) =
      ![gsVertex (M * a), M * a, M * b] := by
    funext i
    fin_cases i
    · simp [hh]
    · exact hhκ
    · exact hhb
  have secondShape : (fun i => h * (![1, κ * w * κ', κ * w] : Fin 3 → RealGL3) i) =
      ![gsVertex (M * a), gsVertex (M * b), M * b] := by
    funext i
    fin_cases i
    · simp [hh]
    · exact hφb
    · exact hhb
  have hMh : M⁻¹ * h = a * κ⁻¹ := by
    have : h = M * a * κ⁻¹ := by rw [← hhκ, mul_inv_cancel_right]
    rw [this]
    simp only [mul_assoc, inv_mul_cancel_left]
  have hκinv : κ⁻¹ ∈ realOrthogonalSet := gsOrth_inv_mem _
  have hκ'mem : κ' ∈ realOrthogonalSet := gsOrth_inv_mem _
  have hκmem : κ ∈ realOrthogonalSet := gsOrth_mem _
  -- the prism value
  have value : (goodLineIwasawaPrism data source cocycle u ![a, b]).val A =
      realCoefficientComponent n data.chi (a * κ⁻¹)
        (normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2)) •
          (source ![1, κ, κ * w] (planeLevi A 1 * 1 * atInfinity h) -
            source ![1, κ * w * κ', κ * w] (planeLevi A 1 * 1 * atInfinity h))) := by
    rw [goodLineIwasawaPrism, sourceCuspidalVertexPrism_apply]
    have pair : (fun index : Fin 2 => M * (![a, b] : Fin 2 → RealGL3) index) = ![M * a, M * b] := by
      funext index
      fin_cases index <;> rfl
    rw [pair]
    simp only [homogeneousVertexPrism]
    change normPower _ _ • realCoefficientComponent n data.chi M⁻¹
      (source ![gsVertex (M * a), M * a, M * b] (planeLevi A 1 * 1) -
        source ![gsVertex (M * a), gsVertex (M * b), M * b] (planeLevi A 1 * 1)) = _
    rw [← firstShape, ← secondShape, cocycle.2.2.1, cocycle.2.2.1, ← map_sub, ← hMh, map_mul,
      Module.End.mul_apply, map_smul, map_smul]
  rw [value, trivial]
  refine (hB κ⁻¹ hκinv _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  have hhP := bigCell u
  have t1 := hC1 m ![1, κ, κ * w] ⟨κ, hκmem, rfl⟩ h hhP A
  have t2 := hC2 m ![1, κ * w * κ', κ * w] ⟨(κ, κ'), ⟨hκmem, hκ'mem⟩, rfl⟩ h hhP A
  have split : ‖(normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2)) •
      (source ![1, κ, κ * w] (planeLevi A 1 * 1 * atInfinity h) -
        source ![1, κ * w * κ', κ * w] (planeLevi A 1 * 1 * atInfinity h))).val.coeff m‖ ≤
      ‖normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2)) *
        (source ![1, κ, κ * w] (planeLevi A 1 * 1 * atInfinity h)).val.coeff m‖ +
      ‖normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2)) *
        (source ![1, κ * w * κ', κ * w] (planeLevi A 1 * 1 * atInfinity h)).val.coeff m‖ := by
    rw [Submodule.coe_smul, Submodule.coe_sub, coeff_smul, coeff_sub, smul_eq_mul, mul_sub]
    exact norm_sub_le _ _
  calc B m * ‖(_ : MvPolynomial (Fin 3) ℂ).coeff m‖ ≤ B m * (|upperBlockDet h| ^ (((n : ℝ) + 3) / 2) * C1 m +
        |upperBlockDet h| ^ (((n : ℝ) + 3) / 2) * C2 m) :=
      mul_le_mul_of_nonneg_left (split.trans (add_le_add t1 t2)) (hB0 m)
    _ = |upperBlockDet h| ^ (((n : ℝ) + 3) / 2) * (B m * (C1 m + C2 m)) := by ring

end TernaryPeriodPolynomials.AnalyticClasses
