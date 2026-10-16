module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.CompactDecomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ClosedCellIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.HilbertAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.Realization
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.NormPower
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ParabolicInvariance

@[expose] public section


/-!
# Transport from maximal compact arguments to all adelic arguments

Original work by Claude Sonnet 5.5.

A function `T` on `GL₃(𝔸)` that is invariant under the line radical and satisfies the rank-one law
`T(lineLevi t 1 · y) = χ(t) |t|² T(y)` is determined by its values `T(lineLevi 1 B · κ)` at
`κ` in the maximal compact: every adelic `g` is `n · lineLevi t B · κ`
(`LineCompactDecomposition.adelic_radical_lineCompact`). This file turns statements at maximal
compact arguments into the same statements at all arguments:

* `LineCovariant.eq_of_compact` : two covariant functions agreeing at `lineLevi 1 B · κ` are equal;
* `smooth_real_of_compact` : real smoothness of `x ↦ T(g · x)` for all `g`;
* `hasSmoothCuspLift_of_compact` : the smooth cusp lift `HasSmoothCuspLift data .line s₀ T` for all
  `a`, from lifts at maximal compact `a` (the vector at general `a` is a scalar multiple of the
  `π(B)`-translate of the vector at `κ`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace EdgeTransport

theorem lineLevi_mul (first second : Adelesˣ) (left right : BinaryAdelicGL) :
    lineLevi (first * second) (left * right) = lineLevi first left * lineLevi second right :=
  (lineLeviHom Adeles).map_mul (first, left) (second, right)

theorem lineLevi_mul_lineUnipotent (binary : BinaryAdelicGL) (first second : Adeles) :
    ∃ third fourth : Adeles, lineLevi 1 binary * lineUnipotent first second =
      lineUnipotent third fourth * lineLevi 1 binary := by
  have conjugate := ClosedCellIntegral.lineLevi_inverse_unipotent binary⁻¹ first second
  have inverse : (lineLevi 1 binary⁻¹)⁻¹ = lineLevi 1 binary := by
    rw [LineCompactDecomposition.lineLevi_inverse, inv_one, inv_inv]
  rw [inverse] at conjugate
  exact ⟨_, _, conjugate⟩

theorem normPower_inverse_pair (unit : Adelesˣ) (exponent : ℂ) :
    normPower unit (-exponent) * normPower unit exponent = 1 := by
  have h := ParabolicInvariance.normPower_neg_mul unit exponent 1
  simpa only [mul_one] using h

theorem normPower_cancel (unit : Adelesˣ) (exponent value : ℂ) :
    normPower unit exponent * (normPower unit (-exponent) * value) = value := by
  have h := ParabolicInvariance.normPower_neg_mul unit (-exponent) value
  rwa [neg_neg] at h

theorem smooth_const_mul {arity : ℕ} (constant : ℂ) {function : (Fin arity → RealGL3) → ℂ}
    (smooth : Smooth function) : Smooth (fun x => constant * function x) := by
  unfold Smooth at smooth ⊢
  exact contDiffOn_const.mul smooth

/-- A function on `GL₃(𝔸)` invariant under the line radical on the left, with the rank-one law
`T(lineLevi t 1 · y) = χ(t) |t|² T(y)` (the law satisfied by the standard value at the
cohomological point). -/
structure LineCovariant {degree : ℕ} (data : InducingData degree) (function : AdelicGL → ℂ) :
    Prop where
  radical : ∀ (first second : Adeles) (argument : AdelicGL),
    function (lineUnipotent first second * argument) = function argument
  rankOne : ∀ (unit : Adelesˣ) (argument : AdelicGL),
    function (lineLevi unit 1 * argument) =
      (data.chi.toMonoidHom unit * normPower unit 2) * function argument

namespace LineCovariant

variable {degree : ℕ} {data : InducingData degree} {function : AdelicGL → ℂ}

/-- Right translation preserves covariance. -/
theorem rightTranslate (covariant : LineCovariant data function) (right : AdelicGL) :
    LineCovariant data (fun argument => function (argument * right)) where
  radical first second argument := by
    have h := covariant.radical first second (argument * right)
    simpa only [mul_assoc] using h
  rankOne unit argument := by
    have h := covariant.rankOne unit (argument * right)
    simpa only [mul_assoc] using h

/-- Evaluation at `lineLevi 1 A · (n · lineLevi t B · κ · z)` in terms of the value at
`lineLevi 1 (A B) · (κ z)`. -/
theorem decompose (covariant : LineCovariant data function) (first second : Adeles)
    (unit : Adelesˣ) (binary left : BinaryAdelicGL) (compact rest : AdelicGL) :
    function (lineLevi 1 left * (lineUnipotent first second * lineLevi unit binary * compact * rest)) =
      (data.chi.toMonoidHom unit * normPower unit 2) *
        function (lineLevi 1 (left * binary) * (compact * rest)) := by
  obtain ⟨third, fourth, commute⟩ := lineLevi_mul_lineUnipotent left first second
  have product : lineLevi 1 left * lineLevi unit binary =
      lineLevi unit 1 * lineLevi 1 (left * binary) := by
    rw [← lineLevi_mul, ← lineLevi_mul]
    simp only [one_mul, mul_one]
  have step : lineLevi 1 left *
      (lineUnipotent first second * lineLevi unit binary * compact * rest) =
      lineUnipotent third fourth * (lineLevi unit 1 * (lineLevi 1 (left * binary) * (compact * rest))) := by
    calc lineLevi 1 left * (lineUnipotent first second * lineLevi unit binary * compact * rest)
        = (lineLevi 1 left * lineUnipotent first second) * (lineLevi unit binary * (compact * rest)) := by
          simp only [mul_assoc]
      _ = lineUnipotent third fourth *
            ((lineLevi 1 left * lineLevi unit binary) * (compact * rest)) := by
          rw [commute]
          simp only [mul_assoc]
      _ = lineUnipotent third fourth *
            (lineLevi unit 1 * (lineLevi 1 (left * binary) * (compact * rest))) := by
          rw [product]
          simp only [mul_assoc]
  rw [step, covariant.radical, covariant.rankOne]

/-- The case `A = 1` of `decompose`. -/
theorem decompose_one (covariant : LineCovariant data function) (first second : Adeles)
    (unit : Adelesˣ) (binary : BinaryAdelicGL) (compact rest : AdelicGL) :
    function (lineUnipotent first second * lineLevi unit binary * compact * rest) =
      (data.chi.toMonoidHom unit * normPower unit 2) *
        function (lineLevi 1 binary * (compact * rest)) := by
  have h := covariant.decompose first second unit binary 1 compact rest
  simpa only [ParabolicInvariance.lineLevi_one, one_mul] using h

/-- Two covariant functions that agree at all `lineLevi 1 B · κ`, `κ` in the maximal compact, are
equal. -/
theorem eq_of_compact {other : AdelicGL → ℂ} (covariant : LineCovariant data function)
    (otherCovariant : LineCovariant data other)
    (agree : ∀ compact : AdelicGL, inMaximalCompact compact → ∀ binary : BinaryAdelicGL,
      function (lineLevi 1 binary * compact) = other (lineLevi 1 binary * compact)) :
    function = other := by
  funext argument
  obtain ⟨first, second, unit, binary, compact, compactMembership, rfl⟩ :=
    LineCompactDecomposition.adelic_radical_lineCompact argument
  have left := covariant.decompose_one first second unit binary compact 1
  have right := otherCovariant.decompose_one first second unit binary compact 1
  simp only [mul_one] at left right
  rw [left, right, agree compact compactMembership binary]

end LineCovariant

/-- Real smoothness of the orbit maps `x ↦ T(g · x)` for all `g`, from the maximal compact. -/
theorem smooth_real_of_compact {degree : ℕ} {data : InducingData degree} {function : AdelicGL → ℂ}
    (covariant : LineCovariant data function)
    (compact : ∀ κ : AdelicGL, inMaximalCompact κ → ∀ binary : BinaryAdelicGL,
      Smooth (fun x : Fin 1 → RealGL3 => function (lineLevi 1 binary * (κ * atInfinity (x 0)))))
    (argument : AdelicGL) :
    Smooth (fun x : Fin 1 → RealGL3 => function (argument * atInfinity (x 0))) := by
  obtain ⟨first, second, unit, binary, κ, κMembership, rfl⟩ :=
    LineCompactDecomposition.adelic_radical_lineCompact argument
  have equation : (fun x : Fin 1 → RealGL3 =>
      function (lineUnipotent first second * lineLevi unit binary * κ * atInfinity (x 0))) =
      fun x => (data.chi.toMonoidHom unit * normPower unit 2) *
        function (lineLevi 1 binary * (κ * atInfinity (x 0))) := by
    funext x
    exact covariant.decompose_one first second unit binary κ (atInfinity (x 0))
  rw [equation]
  exact smooth_const_mul _ (compact κ κMembership binary)

/-- The smooth cusp lift of a family of line-covariant functions at the cohomological point, from
lifts at maximal compact arguments. -/
theorem hasSmoothCuspLift_of_compact {degree arity : ℕ} (data : InducingData degree)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (covariant : ∀ vertices, LineCovariant data (function vertices))
    (compact : ∀ κ : AdelicGL, inMaximalCompact κ →
      ∃ lift : (Fin (arity + 1) → RealGL3) → data.cusp.smooth,
        Smooth (fun x => (lift x).val) ∧
        ∀ x binary, data.cusp.realize (lift x) binary =
          normPower (GeneralLinearGroup.det binary)
              (-binaryInductionExponent degree .line cohomologicalPoint) *
            function (fun index => x index.castSucc)
              (lineLevi 1 binary * (κ * atInfinity (x (Fin.last arity))))) :
    HasSmoothCuspLift data .line cohomologicalPoint function := by
  intro argument
  obtain ⟨first, second, unit, binary, κ, κMembership, rfl⟩ :=
    LineCompactDecomposition.adelic_radical_lineCompact argument
  obtain ⟨lift, liftSmooth, liftRealize⟩ := compact κ κMembership
  set exponent := binaryInductionExponent degree .line cohomologicalPoint
  set scalar : ℂ := (data.chi.toMonoidHom unit * normPower unit 2) *
    normPower (GeneralLinearGroup.det binary) exponent with scalar_def
  refine ⟨fun x => scalar • CuspRealization.smoothAction data.cusp binary (lift x), ?_, ?_⟩
  · let continuousLinear : data.cusp.H →L[ℝ] data.cusp.H :=
      (scalar • (CuspHilbertAction.isometry data.cusp binary).toContinuousLinearMap :
        data.cusp.H →L[ℂ] data.cusp.H).restrictScalars ℝ
    have applyEquation : ∀ vector : data.cusp.smooth,
        (scalar • CuspRealization.smoothAction data.cusp binary vector).val =
          continuousLinear vector.val := fun vector => rfl
    unfold Smooth at liftSmooth ⊢
    exact (continuousLinear.contDiff.comp_contDiffOn liftSmooth).congr
      (fun matrices _ => applyEquation _)
  · intro x left
    have decomposition := (covariant (fun index => x index.castSucc)).decompose first second unit
      binary left κ (atInfinity (x (Fin.last arity)))
    have determinant : GeneralLinearGroup.det (left * binary) =
        GeneralLinearGroup.det left * GeneralLinearGroup.det binary := map_mul _ _ _
    have cancel := normPower_inverse_pair (GeneralLinearGroup.det binary) exponent
    change data.cusp.realize (scalar • CuspRealization.smoothAction data.cusp binary (lift x)) left =
      normPower (GeneralLinearGroup.det left) (-exponent) *
        function (fun index => x index.castSucc)
          (lineLevi 1 left * (lineUnipotent first second * lineLevi unit binary * κ *
            atInfinity (x (Fin.last arity))))
    rw [decomposition, map_smul, Pi.smul_apply, smul_eq_mul,
      CuspRealization.realize_equivariant, liftRealize x (left * binary), determinant,
      NormPower.normPower_mul_units, scalar_def]
    linear_combination
      ((data.chi.toMonoidHom unit * normPower unit 2) *
        normPower (GeneralLinearGroup.det left) (-exponent) *
        function (fun index => x index.castSucc)
          (lineLevi 1 (left * binary) * (κ * atInfinity (x (Fin.last arity))))) * cancel

end EdgeTransport

end TernaryPeriodPolynomials.EdgeConvergence
