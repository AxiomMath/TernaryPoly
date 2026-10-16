module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers

variable {dimension arity : ℕ} {Vector : Type}
  [NormedAddCommGroup Vector] [NormedSpace ℝ Vector]

theorem smooth_zero : Smooth (fun _ : Fin arity → Matrix.GeneralLinearGroup (Fin dimension) ℝ =>
    (0 : Vector)) := by
  exact contDiffOn_const

theorem smooth_add
    {first second : (Fin arity → Matrix.GeneralLinearGroup (Fin dimension) ℝ) → Vector}
    (first_smooth : Smooth first) (second_smooth : Smooth second) :
    Smooth (first + second) := by
  exact first_smooth.add second_smooth

theorem smooth_smul {scalar : ℂ}
    {Vector : Type} [NormedAddCommGroup Vector] [InnerProductSpace ℂ Vector]
    {family : (Fin arity → Matrix.GeneralLinearGroup (Fin dimension) ℝ) → Vector}
    (family_smooth : Smooth family) : Smooth (scalar • family) := by
  exact family_smooth.const_smul scalar

theorem smooth_cusp_lift_zero {degree arity : ℕ} (data : InducingData degree)
    (side : Side) (parameter : ℂ) :
    HasSmoothCuspLift data side parameter
      (0 : (Fin arity → RealGL3) → AdelicGL → ℂ) := by
  intro base
  refine ⟨0, smooth_zero, ?_⟩
  intro coordinates binary
  simp

theorem smooth_cusp_lift_add {degree arity : ℕ} {data : InducingData degree}
    {side : Side} {parameter : ℂ}
    {first second : (Fin arity → RealGL3) → AdelicGL → ℂ}
    (first_lift : HasSmoothCuspLift data side parameter first)
    (second_lift : HasSmoothCuspLift data side parameter second) :
    HasSmoothCuspLift data side parameter (first + second) := by
  intro base
  obtain ⟨first_vector, first_smooth, first_evaluation⟩ := first_lift base
  obtain ⟨second_vector, second_smooth, second_evaluation⟩ := second_lift base
  refine ⟨first_vector + second_vector, smooth_add first_smooth second_smooth, ?_⟩
  intro coordinates binary
  simp only [Pi.add_apply, map_add, first_evaluation, second_evaluation, mul_add]

theorem smooth_cusp_lift_smul {degree arity : ℕ} {data : InducingData degree}
    {side : Side} {parameter scalar : ℂ}
    {family : (Fin arity → RealGL3) → AdelicGL → ℂ}
    (family_lift : HasSmoothCuspLift data side parameter family) :
    HasSmoothCuspLift data side parameter (scalar • family) := by
  intro base
  obtain ⟨vector, vector_smooth, vector_evaluation⟩ := family_lift base
  refine ⟨scalar • vector, smooth_smul vector_smooth, ?_⟩
  intro coordinates binary
  simp only [Pi.smul_apply, map_smul, vector_evaluation, smul_eq_mul]
  ring

theorem induced_zero {degree : ℕ} (data : InducingData degree)
    (side : Side) (parameter : ℂ) : IsInduced data side parameter 0 := by
  refine ⟨fun _ => smooth_zero, ?_, smooth_cusp_lift_zero data side parameter, ?_⟩
  · intro compact base
    rfl
  · cases side <;> refine ⟨?_, ?_, ?_⟩
    all_goals simp only [Pi.zero_apply, mul_zero]
    all_goals intros
    all_goals first | trivial | exact (cuspFunctions data.cusp).zero_mem

theorem induced_add {degree : ℕ} {data : InducingData degree}
    {side : Side} {parameter : ℂ} {first second : AdelicGL → ℂ}
    (first_induced : IsInduced data side parameter first)
    (second_induced : IsInduced data side parameter second) :
    IsInduced data side parameter (first + second) := by
  obtain ⟨first_smooth, first_compact, first_lift, first_covariance⟩ := first_induced
  obtain ⟨second_smooth, second_compact, second_lift, second_covariance⟩ := second_induced
  refine ⟨fun base => smooth_add (first_smooth base) (second_smooth base), ?_,
    smooth_cusp_lift_add first_lift second_lift, ?_⟩
  · intro compact base
    simp only [Pi.add_apply, first_compact, second_compact]
  · cases side
    all_goals
      obtain ⟨first_radical, first_character, first_binary⟩ := first_covariance
      obtain ⟨second_radical, second_character, second_binary⟩ := second_covariance
      refine ⟨?_, ?_, ?_⟩
      · intro coordinate_one coordinate_two base
        simp only [Pi.add_apply, first_radical, second_radical]
      · intro scalar base
        simp only [Pi.add_apply, first_character, second_character, mul_add]
      · intro base
        simpa only [Pi.add_def, mul_add] using
          (cuspFunctions data.cusp).add_mem (first_binary base) (second_binary base)

theorem induced_smul {degree : ℕ} {data : InducingData degree}
    {side : Side} {parameter scalar : ℂ} {family : AdelicGL → ℂ}
    (family_induced : IsInduced data side parameter family) :
    IsInduced data side parameter (scalar • family) := by
  obtain ⟨family_smooth, family_compact, family_lift, family_covariance⟩ := family_induced
  refine ⟨fun base => smooth_smul (family_smooth base), ?_,
    smooth_cusp_lift_smul family_lift, ?_⟩
  · intro compact base
    simp only [Pi.smul_apply, family_compact]
  · cases side
    all_goals
      obtain ⟨family_radical, family_character, family_binary⟩ := family_covariance
      refine ⟨?_, ?_, ?_⟩
      · intro coordinate_one coordinate_two base
        simp only [Pi.smul_apply, family_radical]
      · intro character base
        simp only [Pi.smul_apply, family_character, smul_eq_mul]
        ring
      · intro base
        simpa only [Pi.smul_def, smul_eq_mul, mul_left_comm] using
          (cuspFunctions data.cusp).smul_mem scalar (family_binary base)

theorem source_cocycle_zero {degree : ℕ} (data : InducingData degree) (side : Side) :
    IsSourceCocycle data side 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro coordinates monomial
    simpa only [Pi.zero_def, Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
      induced_zero data side cohomologicalPoint
  · intro monomial
    simpa only [Pi.zero_def, Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
      smooth_cusp_lift_zero (arity := 3) data side cohomologicalPoint
  · intro translate coordinates base
    simp only [Pi.zero_apply, map_zero]
  · intro coordinates base
    simp only [Pi.zero_apply, sub_zero, add_zero]

theorem source_cocycle_add {degree : ℕ} {data : InducingData degree} {side : Side}
    {first second : SourceCochain degree}
    (first_source : IsSourceCocycle data side first)
    (second_source : IsSourceCocycle data side second) :
    IsSourceCocycle data side (first + second) := by
  obtain ⟨first_induced, first_lift, first_equivariant, first_closed⟩ := first_source
  obtain ⟨second_induced, second_lift, second_equivariant, second_closed⟩ := second_source
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro coordinates monomial
    simpa only [Pi.add_def, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
      induced_add (first_induced coordinates monomial) (second_induced coordinates monomial)
  · intro monomial
    simpa only [Pi.add_def, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
      smooth_cusp_lift_add (first_lift monomial) (second_lift monomial)
  · intro translate coordinates base
    simp only [Pi.add_apply, first_equivariant, second_equivariant, map_add]
  · intro coordinates base
    simp only [Pi.add_apply]
    calc
      _ = (first ![coordinates 1, coordinates 2, coordinates 3] base -
          first ![coordinates 0, coordinates 2, coordinates 3] base +
          first ![coordinates 0, coordinates 1, coordinates 3] base -
          first ![coordinates 0, coordinates 1, coordinates 2] base) +
        (second ![coordinates 1, coordinates 2, coordinates 3] base -
          second ![coordinates 0, coordinates 2, coordinates 3] base +
          second ![coordinates 0, coordinates 1, coordinates 3] base -
          second ![coordinates 0, coordinates 1, coordinates 2] base) := by abel
      _ = 0 := by rw [first_closed, second_closed, add_zero]

theorem source_cocycle_smul {degree : ℕ} {data : InducingData degree} {side : Side}
    {scalar : ℂ} {family : SourceCochain degree}
    (family_source : IsSourceCocycle data side family) :
    IsSourceCocycle data side (scalar • family) := by
  obtain ⟨family_induced, family_lift, family_equivariant, family_closed⟩ := family_source
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro coordinates monomial
    simpa only [Pi.smul_def, Submodule.coe_smul, MvPolynomial.coeff_smul] using
      induced_smul (scalar := scalar) (family_induced coordinates monomial)
  · intro monomial
    simpa only [Pi.smul_def, Submodule.coe_smul, MvPolynomial.coeff_smul] using
      smooth_cusp_lift_smul (scalar := scalar) (family_lift monomial)
  · intro translate coordinates base
    simp only [Pi.smul_apply, family_equivariant, map_smul]
  · intro coordinates base
    have equality := congrArg (fun value : HomogeneousPoly degree => scalar • value)
      (family_closed coordinates base)
    simpa only [Pi.smul_apply, smul_sub, smul_add, smul_zero] using equality

theorem evaluates_zero {degree : ℕ} (data : InducingData degree) (side : Side) :
    Evaluates data side 0 0 := by
  intro coordinates flag
  rfl

theorem evaluates_add {degree : ℕ} {data : InducingData degree} {side : Side}
    {first second : SourceCochain degree} {first_cycle second_cycle : MaximalCycles degree data.chi side}
    (first_evaluates : Evaluates data side first first_cycle)
    (second_evaluates : Evaluates data side second second_cycle) :
    Evaluates data side (first + second) (first_cycle + second_cycle) := by
  intro coordinates flag
  exact congrArg₂ (· + ·) (first_evaluates coordinates flag) (second_evaluates coordinates flag)

theorem evaluates_smul {degree : ℕ} {data : InducingData degree} {side : Side}
    {scalar : ℂ} {family : SourceCochain degree} {cycle : MaximalCycles degree data.chi side}
    (family_evaluates : Evaluates data side family cycle) :
    Evaluates data side (scalar • family) (scalar • cycle) := by
  intro coordinates flag
  exact congrArg (scalar • ·) (family_evaluates coordinates flag)

theorem boundary_summand_has_representative {degree : ℕ} (data : InducingData degree)
    (side : Side) (boundary_class : boundarySummand data side) :
    ∃ (source : SourceCochain degree) (cycle : MaximalCycles degree data.chi side),
      IsSourceCocycle data side source ∧ Evaluates data side source cycle ∧
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree data.chi) side)
        cycle = boundary_class.val := by
  obtain ⟨value, membership⟩ := boundary_class
  induction membership using Submodule.span_induction with
  | mem value member =>
    obtain ⟨source, source_closed, cycle, evaluation, equality⟩ := member
    exact ⟨source, cycle, source_closed, evaluation, equality.symm⟩
  | zero =>
    exact ⟨0, 0, source_cocycle_zero data side, evaluates_zero data side, map_zero _⟩
  | add first second first_member second_member first_exists second_exists =>
    obtain ⟨first_source, first_cycle, first_closed, first_evaluation, first_class⟩ := first_exists
    obtain ⟨second_source, second_cycle, second_closed, second_evaluation, second_class⟩ := second_exists
    exact ⟨first_source + second_source, first_cycle + second_cycle,
      source_cocycle_add first_closed second_closed, evaluates_add first_evaluation second_evaluation,
      by rw [map_add, first_class, second_class]⟩
  | smul scalar value member representative_exists =>
    obtain ⟨source, cycle, closed, evaluation, equality⟩ := representative_exists
    exact ⟨scalar • source, scalar • cycle, source_cocycle_smul closed, evaluates_smul evaluation,
      by rw [map_smul, equality]⟩

theorem bad_plane_representative_zero {degree : ℕ} (data : InducingData degree) :
    BadPlaneRepresentative data 0 := by
  exact ⟨0, 0, source_cocycle_zero data .plane, evaluates_zero data .plane,
    map_zero _, fun _ _ _ _ => rfl⟩

end TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers
