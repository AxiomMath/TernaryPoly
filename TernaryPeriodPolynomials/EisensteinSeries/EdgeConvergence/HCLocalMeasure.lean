module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Coordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BinaryGaussian

@[expose] public section


/-!
# The integral binary group on the local line radical

Original work by Claude Sonnet 5.5.

An element `b` of `GL₂(ℤ̂)`, embedded at the finite places, acts on the coordinates `(ℝ × ℚ₃)²` of the
local line radical by the row action of its `3`-component on the two `ℚ₃` coordinates (and trivially
on the real coordinates). Because the `3`-component lies in `GL₂(ℤ₃)` it preserves the Haar measure
of `ℚ₃²` normalized by `ℤ₃²`, hence it preserves `localRadicalMeasure`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

local instance hcNormalizedLocalThreeMeasure_isAddHaar :
    normalizedLocalThreeMeasure.IsAddHaarMeasure :=
  normalizedLocalThreeMeasure_haar

/-- The square of the closed unit ball of `ℚ₃`, a positive compact set. -/
def threeUnitSquare : TopologicalSpace.PositiveCompacts (ℚ_[3] × ℚ_[3]) where
  toCompacts := ⟨Metric.closedBall (0 : ℚ_[3]) 1 ×ˢ Metric.closedBall (0 : ℚ_[3]) 1,
    (isCompact_closedBall (0 : ℚ_[3]) 1).prod (isCompact_closedBall (0 : ℚ_[3]) 1)⟩
  interior_nonempty' := by
    refine ⟨((0 : ℚ_[3]), (0 : ℚ_[3])), ?_⟩
    apply mem_interior_iff_mem_nhds.mpr
    exact prod_mem_nhds (Metric.closedBall_mem_nhds (0 : ℚ_[3]) one_pos)
      (Metric.closedBall_mem_nhds (0 : ℚ_[3]) one_pos)

theorem normalizedLocalThree_closedBall :
    normalizedLocalThreeMeasure (Metric.closedBall (0 : ℚ_[3]) 1) = 1 := by
  have same : Metric.closedBall (0 : ℚ_[3]) 1 = {scalar : ℚ_[3] | ‖scalar‖ ≤ 1} := by
    ext scalar
    simp
  rw [same]
  exact normalizedLocalThreeMeasure_normalized

theorem threeUnitSquare_measure :
    (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)
      (threeUnitSquare : Set (ℚ_[3] × ℚ_[3])) = 1 := by
  change (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)
    (Metric.closedBall (0 : ℚ_[3]) 1 ×ˢ Metric.closedBall (0 : ℚ_[3]) 1) = 1
  rw [Measure.prod_prod, normalizedLocalThree_closedBall, mul_one]

/-- The row action of an integral `3`-adic binary matrix preserves the square of the unit ball. -/
theorem rowAction_integral_mem (matrix : GeneralLinearGroup (Fin 2) ℤ_[3])
    (point : ℚ_[3] × ℚ_[3])
    (inside : point ∈ Metric.closedBall (0 : ℚ_[3]) 1 ×ˢ Metric.closedBall (0 : ℚ_[3]) 1) :
    BinaryGaussian.rowAction (GeneralLinearGroup.map padicThreeEmbedding matrix) point ∈
      Metric.closedBall (0 : ℚ_[3]) 1 ×ˢ Metric.closedBall (0 : ℚ_[3]) 1 := by
  have insidePair := Set.mem_prod.mp inside
  have first : ‖point.1‖ ≤ 1 := mem_closedBall_zero_iff.mp insidePair.1
  have second : ‖point.2‖ ≤ 1 := mem_closedBall_zero_iff.mp insidePair.2
  have combine : ∀ (a b : ℚ_[3]) (p q : ℤ_[3]), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖a * (p : ℚ_[3]) + b * (q : ℚ_[3])‖ ≤ 1 := by
    intro a b p q ha hb
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one p)).trans ha
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one q)).trans hb
  rw [Set.mem_prod]
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    exact combine point.1 point.2 (matrix.val 0 0) (matrix.val 1 0) first second
  · rw [mem_closedBall_zero_iff]
    exact combine point.1 point.2 (matrix.val 0 1) (matrix.val 1 1) first second

/-- The row action of an integral `3`-adic binary matrix as a topological additive equivalence. -/
def threeRowEquiv (matrix : GeneralLinearGroup (Fin 2) ℤ_[3]) :
    (ℚ_[3] × ℚ_[3]) ≃ₜ+ (ℚ_[3] × ℚ_[3]) :=
  BinaryGaussian.rowEquiv (GeneralLinearGroup.map padicThreeEmbedding matrix)

theorem threeRowEquiv_apply (matrix : GeneralLinearGroup (Fin 2) ℤ_[3]) :
    (threeRowEquiv matrix : ℚ_[3] × ℚ_[3] → ℚ_[3] × ℚ_[3]) =
      BinaryGaussian.rowAction (GeneralLinearGroup.map padicThreeEmbedding matrix) :=
  rfl

theorem threeRowEquiv_measurable (matrix : GeneralLinearGroup (Fin 2) ℤ_[3]) :
    Measurable (threeRowEquiv matrix : ℚ_[3] × ℚ_[3] → ℚ_[3] × ℚ_[3]) :=
  (threeRowEquiv matrix).continuous.measurable

theorem threeRowEquiv_preimage (matrix : GeneralLinearGroup (Fin 2) ℤ_[3]) :
    (threeRowEquiv matrix : ℚ_[3] × ℚ_[3] → ℚ_[3] × ℚ_[3]) ⁻¹'
      (threeUnitSquare : Set (ℚ_[3] × ℚ_[3])) = threeUnitSquare := by
  ext point
  constructor
  · intro membership
    have inverse := rowAction_integral_mem matrix⁻¹
      (BinaryGaussian.rowAction (GeneralLinearGroup.map padicThreeEmbedding matrix) point)
      membership
    have cancel : BinaryGaussian.rowAction (GeneralLinearGroup.map padicThreeEmbedding matrix⁻¹)
        (BinaryGaussian.rowAction (GeneralLinearGroup.map padicThreeEmbedding matrix) point) =
          point := by
      rw [map_inv, ← BinaryGaussian.rowAction_mul, mul_inv_cancel, BinaryGaussian.rowAction_one]
    rw [cancel] at inverse
    exact inverse
  · intro membership
    exact rowAction_integral_mem matrix point membership

/-- The row action of an element of `GL₂(ℤ₃)` preserves the Haar measure of `ℚ₃²` normalized by
`ℤ₃²`. -/
theorem rowAction_integral_measurePreserving (matrix : GeneralLinearGroup (Fin 2) ℤ_[3]) :
    MeasurePreserving
      (BinaryGaussian.rowAction (GeneralLinearGroup.map padicThreeEmbedding matrix))
      (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)
      (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure) := by
  rw [← threeRowEquiv_apply]
  have mappedHaar : (Measure.map (threeRowEquiv matrix)
      (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)).IsAddHaarMeasure :=
    (threeRowEquiv matrix).isAddHaarMeasure_map
      (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)
  have normalized : Measure.map (threeRowEquiv matrix)
      (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)
        (threeUnitSquare : Set (ℚ_[3] × ℚ_[3])) = 1 := by
    rw [Measure.map_apply (threeRowEquiv_measurable matrix)
      threeUnitSquare.isCompact.measurableSet, threeRowEquiv_preimage]
    exact threeUnitSquare_measure
  refine ⟨threeRowEquiv_measurable matrix, ?_⟩
  have unique := Measure.addHaarMeasure_unique
    (Measure.map (threeRowEquiv matrix)
      (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)) threeUnitSquare
  have uniqueBase := Measure.addHaarMeasure_unique
    (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure) threeUnitSquare
  rw [normalized, one_smul] at unique
  rw [threeUnitSquare_measure, one_smul] at uniqueBase
  exact unique.trans uniqueBase.symm

/-- The row action of a `3`-adic binary matrix on the `ℚ₃` coordinates of the local line radical,
trivial on the real coordinates. -/
def localMatrixAction (matrix : GeneralLinearGroup (Fin 2) ℚ_[3]) :
    LocalLine × LocalLine → LocalLine × LocalLine :=
  (fun pair : (ℝ × ℝ) × (ℚ_[3] × ℚ_[3]) => ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2))) ∘
    Prod.map (id : ℝ × ℝ → ℝ × ℝ) (BinaryGaussian.rowAction matrix) ∘
    (fun pair : LocalLine × LocalLine => ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2)))

theorem localMatrixAction_apply (matrix : GeneralLinearGroup (Fin 2) ℚ_[3])
    (coordinates : LocalLine × LocalLine) :
    localMatrixAction matrix coordinates =
      ((coordinates.1.1, (BinaryGaussian.rowAction matrix (coordinates.1.2, coordinates.2.2)).1),
        (coordinates.2.1, (BinaryGaussian.rowAction matrix (coordinates.1.2, coordinates.2.2)).2)) :=
  rfl

theorem localMatrixAction_measurePreserving (matrix : GeneralLinearGroup (Fin 2) ℤ_[3]) :
    MeasurePreserving
      (localMatrixAction (GeneralLinearGroup.map padicThreeEmbedding matrix))
      localRadicalMeasure localRadicalMeasure := by
  have forward := measurePreserving_prodTranspose (volume : Measure ℝ) normalizedLocalThreeMeasure
    (volume : Measure ℝ) normalizedLocalThreeMeasure
  have middle := (MeasurePreserving.id ((volume : Measure ℝ).prod (volume : Measure ℝ))).prod
    (rowAction_integral_measurePreserving matrix)
  have backward := measurePreserving_prodTranspose (volume : Measure ℝ) (volume : Measure ℝ)
    normalizedLocalThreeMeasure normalizedLocalThreeMeasure
  exact backward.comp (middle.comp forward)

/-- Integrating a continuous function after the integral `3`-adic row action does not change the
integral. -/
theorem integral_localMatrixAction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (matrix : GeneralLinearGroup (Fin 2) ℤ_[3]) (function : LocalLine × LocalLine → E)
    (continuous : Continuous function) :
    (∫ coordinates, function
      (localMatrixAction (GeneralLinearGroup.map padicThreeEmbedding matrix) coordinates)
        ∂localRadicalMeasure) = ∫ coordinates, function coordinates ∂localRadicalMeasure := by
  have preserving := localMatrixAction_measurePreserving matrix
  have mapped := integral_map (μ := localRadicalMeasure) preserving.measurable.aemeasurable
    (f := function) (by rw [preserving.map_eq]; exact continuous.aestronglyMeasurable)
  rw [preserving.map_eq] at mapped
  exact mapped.symm

theorem finiteAtThreeScalar_add (first second : ℚ_[3]) :
    finiteAtThreeScalar (first + second) = finiteAtThreeScalar first + finiteAtThreeScalar second :=
  finiteAtThreeAdd.map_add first second

/-- Multiplication of a finite adele by a vector supported at `3` acts through the `3`-component. -/
theorem finiteAtThreeScalar_mul (value : FiniteAdeles) (scalar : ℚ_[3]) :
    finiteAtThreeScalar scalar * value = finiteAtThreeScalar (scalar * finiteThree value) := by
  apply finiteAdeles_eq_of_three_and_away
  · rw [map_mul, finiteAtThreeScalar_three, finiteAtThreeScalar_three]
  · intro place away
    rw [map_mul, finiteAtThreeScalar_away scalar place away,
      finiteAtThreeScalar_away _ place away, zero_mul]

theorem localAdele_fst (value : LocalLine) : (localAdele value).1 = value.1 := rfl

theorem localAdele_snd (value : LocalLine) : (localAdele value).2 = finiteAtThreeScalar value.2 :=
  rfl

theorem atFinite_val_fst (unit : BinaryFiniteGL) (row column : Fin 2) :
    ((atFinite unit).val row column).1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) row column :=
  rfl

theorem atFinite_val_snd (unit : BinaryFiniteGL) (row column : Fin 2) :
    ((atFinite unit).val row column).2 = unit.val row column :=
  rfl

theorem rowAction_fst_fst (matrix : BinaryAdelicGL) (first second : Adeles) :
    ((BinaryGaussian.rowAction matrix (first, second)).1).1 =
      first.1 * (matrix.val 0 0).1 + second.1 * (matrix.val 1 0).1 :=
  rfl

theorem rowAction_fst_snd (matrix : BinaryAdelicGL) (first second : Adeles) :
    ((BinaryGaussian.rowAction matrix (first, second)).1).2 =
      first.2 * (matrix.val 0 0).2 + second.2 * (matrix.val 1 0).2 :=
  rfl

theorem rowAction_snd_fst (matrix : BinaryAdelicGL) (first second : Adeles) :
    ((BinaryGaussian.rowAction matrix (first, second)).2).1 =
      first.1 * (matrix.val 0 1).1 + second.1 * (matrix.val 1 1).1 :=
  rfl

theorem rowAction_snd_snd (matrix : BinaryAdelicGL) (first second : Adeles) :
    ((BinaryGaussian.rowAction matrix (first, second)).2).2 =
      first.2 * (matrix.val 0 1).2 + second.2 * (matrix.val 1 1).2 :=
  rfl

theorem localMatrixAction_fst_fst (matrix : GeneralLinearGroup (Fin 2) ℚ_[3])
    (coordinates : LocalLine × LocalLine) :
    ((localMatrixAction matrix coordinates).1).1 = coordinates.1.1 :=
  rfl

theorem localMatrixAction_snd_fst (matrix : GeneralLinearGroup (Fin 2) ℚ_[3])
    (coordinates : LocalLine × LocalLine) :
    ((localMatrixAction matrix coordinates).2).1 = coordinates.2.1 :=
  rfl

theorem localMatrixAction_fst_snd (matrix : GeneralLinearGroup (Fin 2) ℚ_[3])
    (coordinates : LocalLine × LocalLine) :
    ((localMatrixAction matrix coordinates).1).2 =
      coordinates.1.2 * matrix.val 0 0 + coordinates.2.2 * matrix.val 1 0 :=
  rfl

theorem localMatrixAction_snd_snd (matrix : GeneralLinearGroup (Fin 2) ℚ_[3])
    (coordinates : LocalLine × LocalLine) :
    ((localMatrixAction matrix coordinates).2).2 =
      coordinates.1.2 * matrix.val 0 1 + coordinates.2.2 * matrix.val 1 1 :=
  rfl

theorem map_finiteThree_val (unit : BinaryFiniteGL) (row column : Fin 2) :
    (GeneralLinearGroup.map finiteThree unit).val row column = finiteThree (unit.val row column) :=
  GeneralLinearGroup.map_apply finiteThree row column unit

/-- The row action of a finite binary adelic matrix on the local coordinates is the row action of
its `3`-component. -/
theorem rowAction_atFinite_local (unit : BinaryFiniteGL) (coordinates : LocalLine × LocalLine) :
    BinaryGaussian.rowAction (atFinite unit)
        (localAdele coordinates.1, localAdele coordinates.2) =
      (localAdele (localMatrixAction (GeneralLinearGroup.map finiteThree unit) coordinates).1,
        localAdele (localMatrixAction (GeneralLinearGroup.map finiteThree unit) coordinates).2) := by
  apply Prod.ext
  · apply Prod.ext
    · dsimp only
      rw [rowAction_fst_fst, atFinite_val_fst, atFinite_val_fst, localAdele_fst, localAdele_fst,
        localAdele_fst, localMatrixAction_fst_fst]
      simp
    · dsimp only
      rw [rowAction_fst_snd, atFinite_val_snd, atFinite_val_snd, localAdele_snd, localAdele_snd,
        localAdele_snd, localMatrixAction_fst_snd, map_finiteThree_val, map_finiteThree_val,
        finiteAtThreeScalar_add, finiteAtThreeScalar_mul, finiteAtThreeScalar_mul]
  · apply Prod.ext
    · dsimp only
      rw [rowAction_snd_fst, atFinite_val_fst, atFinite_val_fst, localAdele_fst, localAdele_fst,
        localAdele_fst, localMatrixAction_snd_fst]
      simp
    · dsimp only
      rw [rowAction_snd_snd, atFinite_val_snd, atFinite_val_snd, localAdele_snd, localAdele_snd,
        localAdele_snd, localMatrixAction_snd_snd, map_finiteThree_val, map_finiteThree_val,
        finiteAtThreeScalar_add, finiteAtThreeScalar_mul, finiteAtThreeScalar_mul]

/-- Compatibility of two ring homomorphisms with a square of rings, on `GL₂`. -/
theorem generalLinearGroup_map_square_two {first second third fourth : Type*}
    [CommRing first] [CommRing second] [CommRing third] [CommRing fourth]
    (left : first →+* second) (top : second →+* fourth)
    (bottom : first →+* third) (right : third →+* fourth)
    (square : ∀ value, top (left value) = right (bottom value))
    (matrix : GeneralLinearGroup (Fin 2) first) :
    GeneralLinearGroup.map top (GeneralLinearGroup.map left matrix) =
      GeneralLinearGroup.map right (GeneralLinearGroup.map bottom matrix) := by
  apply Units.ext
  funext row column
  simp only [GeneralLinearGroup.map_apply]
  exact square (matrix.val row column)

/-- The `3`-component of the finite embedding of an integral binary matrix. -/
theorem finiteThree_integralMatrix_two (integer : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    GeneralLinearGroup.map finiteThree (GeneralLinearGroup.map integralEmbedding integer) =
      GeneralLinearGroup.map padicThreeEmbedding (GeneralLinearGroup.map integralThree integer) :=
  generalLinearGroup_map_square_two integralEmbedding finiteThree integralThree
    padicThreeEmbedding
    (fun value => (finiteThree_integral value).trans (padicThreeEmbedding_apply (integralThree value)).symm)
    integer

/-- Integrating a continuous function after the row action of the finite embedding of an integral
binary matrix does not change the integral. -/
theorem integral_localMatrixAction_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (integer : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (function : LocalLine × LocalLine → E) (continuous : Continuous function) :
    (∫ coordinates, function (localMatrixAction (GeneralLinearGroup.map finiteThree
      (GeneralLinearGroup.map integralEmbedding integer)) coordinates) ∂localRadicalMeasure) =
      ∫ coordinates, function coordinates ∂localRadicalMeasure := by
  rw [finiteThree_integralMatrix_two]
  exact integral_localMatrixAction (GeneralLinearGroup.map integralThree integer) function
    continuous

end TernaryPeriodPolynomials.EdgeConvergence
