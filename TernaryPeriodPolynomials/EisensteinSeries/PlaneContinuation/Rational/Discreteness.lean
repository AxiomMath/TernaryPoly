module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.Unfolding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalDiscreteness

theorem integral_mul {first second : FiniteAdeles}
    (firstIntegral : first ∈ Set.range integralEmbedding) (secondIntegral : second ∈ Set.range integralEmbedding) :
    first * second ∈ Set.range integralEmbedding := by
  obtain ⟨firstPreimage, rfl⟩ := firstIntegral
  obtain ⟨secondPreimage, rfl⟩ := secondIntegral
  exact ⟨firstPreimage * secondPreimage, map_mul integralEmbedding _ _⟩

theorem rational_eq_zero_of_small (rational : ℚ)
    (integral : algebraMap ℚ FiniteAdeles rational ∈ Set.range integralEmbedding)
    (small : |(rational : ℝ)| < 1 / 2) : rational = 0 := by
  by_contra nonzero
  let unit : ℚˣ := Units.mk0 rational nonzero
  have measureIdentity := ProductFormula.adeleNorm_eq_measure_image (Units.map rationalAdele.toMonoidHom unit)
  rw [ProductFormula.adeleNorm_rational] at measureIdentity
  have containment : (fun value : Adeles => rationalAdele rational * value) '' additiveDomain ⊆
      Set.Icc (-|(rational : ℝ)|) |(rational : ℝ)| ×ˢ Set.range integralEmbedding := by
    rintro _ ⟨value, membership, rfl⟩
    change (0 ≤ value.1 ∧ value.1 < 1) ∧ value.2 ∈ Set.range integralEmbedding at membership
    change ((rational : ℝ) * value.1 ∈ Set.Icc (-|(rational : ℝ)|) |(rational : ℝ)|) ∧
      algebraMap ℚ FiniteAdeles rational * value.2 ∈ Set.range integralEmbedding
    refine ⟨?_, integral_mul integral membership.2⟩
    apply abs_le.mp
    rw [abs_mul, abs_of_nonneg membership.1.1]
    exact mul_le_of_le_one_right (abs_nonneg _) membership.1.2.le
  have measureBound := measure_mono (μ := adeleMeasure) containment
  change 1 = adeleMeasure ((fun value : Adeles => rationalAdele rational * value) '' additiveDomain) at measureIdentity
  rw [← measureIdentity, adeleMeasure, Measure.prod_prod, Real.volume_Icc,
    finiteMeasure_integralLattice, mul_one] at measureBound
  have realBound : 1 ≤ |(rational : ℝ)| - -|(rational : ℝ)| :=
    (ENNReal.ofReal_le_ofReal_iff (q := |(rational : ℝ)| - -|(rational : ℝ)|)
      (by linarith [abs_nonneg (rational : ℝ)])).mp (by simpa only [ENNReal.ofReal_one] using measureBound)
  linarith

def smallAdeles : Set Adeles := {value | |value.1| < 1 / 2 ∧ value.2 ∈ Set.range integralEmbedding}

theorem smallAdeles_open : IsOpen smallAdeles :=
  (isOpen_lt continuous_fst.abs continuous_const).inter (integralLattice_isOpen.preimage continuous_snd)

theorem zero_mem_smallAdeles : (0 : Adeles) ∈ smallAdeles := by
  refine ⟨by norm_num, ⟨0, map_zero integralEmbedding⟩⟩

theorem rational_mem_smallAdeles (rational : ℚ) : rationalAdele rational ∈ smallAdeles ↔ rational = 0 := by
  constructor
  · intro membership
    exact rational_eq_zero_of_small rational membership.2 membership.1
  · rintro rfl
    simpa only [map_zero] using zero_mem_smallAdeles

def matrixNeighborhood (size : ℕ) : Set (GeneralLinearGroup (Fin size) Adeles) :=
  {matrix | ∀ row column, matrix.val row column - (1 : Matrix (Fin size) (Fin size) Adeles) row column ∈ smallAdeles}

theorem matrixNeighborhood_open (size : ℕ) : IsOpen (matrixNeighborhood size) := by
  have equality : matrixNeighborhood size = ⋂ row : Fin size, ⋂ column : Fin size,
      {matrix : GeneralLinearGroup (Fin size) Adeles |
        matrix.val row column - (1 : Matrix (Fin size) (Fin size) Adeles) row column ∈ smallAdeles} := by
    ext matrix
    simp [matrixNeighborhood]
  rw [equality]
  apply isOpen_iInter_of_finite
  intro row
  apply isOpen_iInter_of_finite
  intro column
  have values : Continuous (fun matrix : GeneralLinearGroup (Fin size) Adeles => matrix.val) := Units.continuous_val
  have continuity : Continuous (fun matrix : GeneralLinearGroup (Fin size) Adeles =>
      matrix.val row column - (1 : Matrix (Fin size) (Fin size) Adeles) row column) :=
    ((continuous_apply column).comp ((continuous_apply row).comp values)).sub continuous_const
  exact smallAdeles_open.preimage continuity

theorem one_mem_matrixNeighborhood (size : ℕ) : (1 : GeneralLinearGroup (Fin size) Adeles) ∈ matrixNeighborhood size := by
  intro row column
  change (1 : Matrix (Fin size) (Fin size) Adeles) row column - (1 : Matrix (Fin size) (Fin size) Adeles) row column ∈ _
  rw [sub_self]
  exact zero_mem_smallAdeles

theorem rational_mem_matrixNeighborhood {size : ℕ} (matrix : GeneralLinearGroup (Fin size) ℚ)
    (membership : GeneralLinearGroup.map rationalAdele matrix ∈ matrixNeighborhood size) : matrix = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply sub_eq_zero.mp
  apply (rational_mem_smallAdeles (matrix.val row column - (1 : Matrix (Fin size) (Fin size) ℚ) row column)).mp
  have entry : rationalAdele (matrix.val row column) -
      (1 : Matrix (Fin size) (Fin size) Adeles) row column ∈ smallAdeles := membership row column
  simpa only [map_sub, Matrix.one_apply, apply_ite, map_one, map_zero] using entry

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalDiscreteness
