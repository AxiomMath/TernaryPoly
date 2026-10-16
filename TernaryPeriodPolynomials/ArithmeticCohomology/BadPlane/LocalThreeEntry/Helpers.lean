module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.Helpers

def entryMatrix {R : Type*} [CommRing R] (first second : R) : GL3 R :=
  ⟨!![0,1,0;1,0,0;second,first,1], !![0,1,0;1,0,0;-first,-second,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem entryMatrix_eq (first second : ℚ_[3]) :
    weyl⁻¹ * lineUnipotent first second * localGoodLine = entryMatrix first second := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [weyl, lineUnipotent, upperUnipotent, localGoodLine, entryMatrix,
      Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem reduction_zero_iff (integer : ℤ_[3]) :
    PadicInt.toZMod integer = 0 ↔ ‖integer‖ < 1 := by
  change integer ∈ RingHom.ker PadicInt.toZMod ↔ _
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
  exact PadicInt.not_isUnit_iff

theorem reduction_one_norm {integer : ℤ_[3]}
    (reduction : PadicInt.toZMod integer = 1) : ‖integer‖ = 1 := by
  apply PadicInt.isUnit_iff.mp
  apply IsLocalRing.notMem_maximalIdeal.mp
  rw [← PadicInt.ker_toZMod]
  change PadicInt.toZMod integer ≠ 0
  rw [reduction]
  exact one_ne_zero

theorem entryMatrix_in_level {first second : ℚ_[3]}
    (first_small : ‖first‖ < 1) (second_small : ‖second‖ < 1) :
    InLocalThreeLevel (entryMatrix first second) := by
  let first_integer : ℤ_[3] := ⟨first, first_small.le⟩
  let second_integer : ℤ_[3] := ⟨second, second_small.le⟩
  refine ⟨entryMatrix first_integer second_integer, ?_, ?_⟩
  · have first_zero : PadicInt.toZMod first_integer = 0 :=
      (reduction_zero_iff first_integer).mpr first_small
    have second_zero : PadicInt.toZMod second_integer = 0 :=
      (reduction_zero_iff second_integer).mpr second_small
    funext column
    fin_cases column <;>
      simp [lastRow, Matrix.vecMul, entryMatrix,
        GeneralLinearGroup.map, first_zero, second_zero]
  · apply GeneralLinearGroup.ext
    intro row column
    change ((entryMatrix first_integer second_integer).val row column : ℚ_[3]) =
      (entryMatrix first second).val row column
    fin_cases row <;> fin_cases column <;>
      simp [entryMatrix, first_integer, second_integer]

theorem entryMatrix_support_small {first second : ℚ_[3]}
    (support : ∃ parabolic : planeParabolic ℚ_[3], ∃ level : LocalThreeGL,
      InLocalThreeLevel level ∧ entryMatrix first second = parabolic.val * level) :
    ‖first‖ < 1 ∧ ‖second‖ < 1 := by
  rcases support with ⟨parabolic, level, ⟨integer, congruence, embedding⟩, equality⟩
  have parabolic_zero : InPlaneParabolic parabolic.val := parabolic.property
  have reduction (column : Fin 3) :
      PadicInt.toZMod (integer.val 2 column) = lastRow column := by
    have row := congrFun congruence column
    simpa [lastRow, Matrix.vecMul] using row
  have bottom (column : Fin 3) :
      (entryMatrix first second).val 2 column =
        parabolic.val.val 2 2 * (integer.val 2 column : ℚ_[3]) := by
    have row := congrArg (fun matrix : LocalThreeGL => matrix.val 2 column) equality
    rw [← embedding] at row
    change (entryMatrix first second).val 2 column =
      (parabolic.val.val * integer.val.map (fun value : ℤ_[3] => (value : ℚ_[3]))) 2 column at row
    simpa [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three,
      parabolic_zero.1, parabolic_zero.2] using row
  have corner_norm : ‖(integer.val 2 2 : ℚ_[3])‖ = 1 := by
    exact reduction_one_norm (by simpa [lastRow] using reduction 2)
  have scalar_norm : ‖parabolic.val.val 2 2‖ = 1 := by
    have corner := congrArg norm (bottom 2)
    simpa [entryMatrix, norm_mul, corner_norm] using corner.symm
  have entry_small (column : Fin 3) (different : column ≠ 2) :
      ‖(integer.val 2 column : ℚ_[3])‖ < 1 := by
    exact (reduction_zero_iff _).mp (by simpa [lastRow, different] using reduction column)
  constructor
  · have row : ‖first‖ = ‖(integer.val 2 1 : ℚ_[3])‖ := by
      simpa [entryMatrix, norm_mul, scalar_norm] using congrArg norm (bottom 1)
    exact row.trans_lt (entry_small 1 (by decide))
  · have row : ‖second‖ = ‖(integer.val 2 0 : ℚ_[3])‖ := by
      simpa [entryMatrix, norm_mul, scalar_norm] using congrArg norm (bottom 0)
    exact row.trans_lt (entry_small 0 (by decide))

def smallBall : Set ℚ_[3] := {coordinate | ‖coordinate‖ < 1}

theorem integrand_indicator (sectionValue : LocalThreeGL → ℂ)
    (support : LocalBadPlaneSupport sectionValue)
    (invariant : LocalRightInvariant sectionValue) :
    localBadPlaneIntegrand sectionValue =
      (smallBall ×ˢ smallBall).indicator (fun _ => sectionValue 1) := by
  funext coordinates
  rw [localBadPlaneIntegrand, entryMatrix_eq]
  by_cases small : coordinates ∈ smallBall ×ˢ smallBall
  · rw [Set.indicator_of_mem small]
    simpa using invariant 1 (entryMatrix coordinates.1 coordinates.2)
      (entryMatrix_in_level small.1 small.2)
  · rw [Set.indicator_of_notMem small]
    apply support
    intro membership
    exact small (entryMatrix_support_small membership)

def residueBall (residue : Fin 3) : Set ℚ_[3] :=
  {coordinate | ‖coordinate - residue.val‖ < 1}

theorem residueBall_measurable (residue : Fin 3) : MeasurableSet (residueBall residue) :=
  (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).measurableSet

theorem residueBall_subset (residue : Fin 3) :
    residueBall residue ⊆ {coordinate : ℚ_[3] | ‖coordinate‖ ≤ 1} := by
  intro coordinate small
  have residue_norm : ‖(residue.val : ℚ_[3])‖ ≤ 1 := by
    exact_mod_cast Padic.norm_int_le_one (p := 3) (residue.val : ℤ)
  calc
    ‖coordinate‖ = ‖(coordinate - residue.val) + residue.val‖ := by rw [sub_add_cancel]
    _ ≤ max ‖coordinate - residue.val‖ ‖(residue.val : ℚ_[3])‖ := Padic.nonarchimedean _ _
    _ ≤ 1 := max_le small.le residue_norm

theorem residueBall_cover :
    (⋃ residue : Fin 3, residueBall residue) = {coordinate : ℚ_[3] | ‖coordinate‖ ≤ 1} := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset residueBall_subset
  · intro coordinate bounded
    let integer : ℤ_[3] := ⟨coordinate, bounded⟩
    let residue : Fin 3 := ⟨integer.zmodRepr, integer.zmodRepr_lt_p⟩
    apply Set.mem_iUnion.mpr
    refine ⟨residue, ?_⟩
    have small : ‖integer - integer.zmodRepr‖ < 1 := by
      apply PadicInt.not_isUnit_iff.mp
      exact (IsLocalRing.mem_maximalIdeal _).mp integer.sub_zmodRepr_mem
    change ‖(coordinate - integer.zmodRepr : ℚ_[3])‖ < 1 at small
    exact small

theorem residueBall_disjoint : Pairwise (Function.onFun Disjoint residueBall) := by
  intro first second different
  apply Set.disjoint_left.mpr
  intro coordinate first_small second_small
  have difference_small : ‖((first.val : ℤ_[3]) - second.val)‖ < 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast, PadicInt.coe_natCast]
    calc
      ‖(first.val : ℚ_[3]) - second.val‖ =
          ‖-(coordinate - first.val) + (coordinate - second.val)‖ := by
            congr 1
            ring
      _ ≤ max ‖-(coordinate - first.val)‖ ‖coordinate - second.val‖ :=
        Padic.nonarchimedean _ _
      _ < 1 := by simpa only [norm_neg] using max_lt first_small second_small
  have reduction := (reduction_zero_iff _).mpr difference_small
  rw [map_sub, map_natCast, map_natCast, sub_eq_zero] at reduction
  have equal : first = second := by
    apply Fin.ext
    have values := congrArg ZMod.val reduction
    simpa [Nat.mod_eq_of_lt first.isLt, Nat.mod_eq_of_lt second.isLt] using values
  exact different equal

theorem residueBall_measure (measure : Measure ℚ_[3]) [measure.IsAddHaarMeasure]
    (residue : Fin 3) : measure (residueBall residue) = measure smallBall := by
  have equal : residueBall residue =
      (fun coordinate : ℚ_[3] => -(residue.val : ℚ_[3]) + coordinate) ⁻¹' smallBall := by
    ext coordinate
    simp [residueBall, smallBall, sub_eq_add_neg, add_comm]
  rw [equal]
  exact measure_preimage_add measure _ _

theorem smallBall_measure (measure : Measure ℚ_[3]) [measure.IsAddHaarMeasure]
    (normalized : measure {coordinate | ‖coordinate‖ ≤ 1} = 1) :
    measure smallBall = (1 / 3 : ENNReal) := by
  have partition := measure_iUnion residueBall_disjoint residueBall_measurable (μ := measure)
  rw [residueBall_cover, normalized] at partition
  simp only [residueBall_measure, tsum_fintype, Fin.sum_univ_three] at partition
  have finite : measure smallBall ≠ ⊤ := by
    have bounded : measure smallBall ≤ 1 := by
      rw [← normalized]
      exact measure_mono (fun _ small => (show ‖_‖ < 1 from small).le)
    exact ne_top_of_le_ne_top (by norm_num) bounded
  have real_partition := congrArg ENNReal.toReal partition
  rw [ENNReal.toReal_one, ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨finite, finite⟩)
    finite, ENNReal.toReal_add finite finite] at real_partition
  have real_value : (measure smallBall).toReal = 1 / 3 := by linarith
  rw [← ENNReal.ofReal_toReal finite, real_value]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

end TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.Helpers
