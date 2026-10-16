module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.BoundedSchur
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CasimirIrreducibility
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCasimir TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirNorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirIrreducibility TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalHilbert

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirScalar

noncomputable def shifted (data : CuspidalRepresentation) : data.smooth →ₗ[ℂ] data.H :=
  data.smooth.subtype.comp (casimir data + Complex.I • LinearMap.id)

theorem shifted_apply (data : CuspidalRepresentation) (vector : data.smooth) :
    shifted data vector = (casimir data vector).val + Complex.I • vector.val := rfl

theorem shifted_norm_sq (data : CuspidalRepresentation) (vector : data.smooth) :
    ‖shifted data vector‖ ^ 2 = ‖(casimir data vector).val‖ ^ 2 + ‖vector.val‖ ^ 2 := by
  have symmetry := casimir_inner data vector vector
  have equality : (‖shifted data vector‖ : ℂ) ^ 2 =
      (‖(casimir data vector).val‖ : ℂ) ^ 2 + (‖vector.val‖ : ℂ) ^ 2 := by
    calc
      _ = inner ℂ (shifted data vector) (shifted data vector) :=
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (shifted data vector)).symm
      _ = _ := ?_
    change inner ℂ ((casimir data vector).val + Complex.I • vector.val)
      ((casimir data vector).val + Complex.I • vector.val) = _
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      Complex.conj_I]
    simp only [inner_self_eq_norm_sq_to_K]
    rw [← symmetry]
    linear_combination -(Complex.I_mul_I : Complex.I * Complex.I = -1) * (‖vector.val‖ : ℂ) ^ 2
  exact_mod_cast equality

theorem shifted_norm_bound (data : CuspidalRepresentation) (vector : data.smooth) :
    ‖vector.val‖ ≤ ‖shifted data vector‖ := by
  have equality := shifted_norm_sq data vector
  nlinarith [sq_nonneg ‖(casimir data vector).val‖, norm_nonneg vector.val,
    norm_nonneg (shifted data vector)]

theorem shifted_action (data : CuspidalRepresentation) (matrix : BinaryAdelicGL) (vector : data.smooth) :
    shifted data (smoothAction data matrix vector) = unitaryOperator data matrix (shifted data vector) := by
  rw [shifted_apply, casimir_action, shifted_apply, map_add, map_smul]
  rfl

theorem shifted_range_dense {degree : ℕ} (data : InducingData degree) : DenseRange (shifted data.cusp) := by
  let range := LinearMap.range (shifted data.cusp)
  have stable (matrix : BinaryAdelicGL) : Set.MapsTo (data.cusp.π matrix) (range : Set data.cusp.H) range := by
    rintro vector ⟨smoothVector, rfl⟩
    exact ⟨smoothAction data.cusp matrix smoothVector, shifted_action data.cusp matrix smoothVector⟩
  have closureStable (matrix : BinaryAdelicGL) :
      Set.MapsTo (data.cusp.π matrix) (range.topologicalClosure : Set data.cusp.H) range.topologicalClosure :=
    (stable matrix).closure (unitaryOperator data.cusp matrix).continuous
  have fullClosure : range.topologicalClosure = ⊤ := by
    rcases data.cusp.irreducible range.topologicalClosure range.isClosed_topologicalClosure
      (fun matrix _ membership => closureStable matrix membership) with zeroClosure | fullClosure
    · obtain ⟨vector, nonzero⟩ := exists_nonzero_smooth data
      have membership : shifted data.cusp vector ∈ range.topologicalClosure :=
        range.le_topologicalClosure ⟨vector, rfl⟩
      rw [zeroClosure] at membership
      have bound := shifted_norm_bound data.cusp vector
      rw [show shifted data.cusp vector = 0 from membership, norm_zero] at bound
      exact False.elim (nonzero (norm_eq_zero.mp (le_antisymm bound (norm_nonneg _))))
    · exact fullClosure
  apply dense_iff_closure_eq.mpr
  change (range.topologicalClosure : Set data.cusp.H) = Set.univ
  rw [fullClosure]
  rfl

/-- The inverse on the dense range of C+i extends to a bounded Hilbert operator. -/
noncomputable def resolvent (data : CuspidalRepresentation) : data.H →L[ℂ] data.H :=
  data.smooth.subtype.extendOfNorm (shifted data)

theorem resolvent_shifted {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth) :
    resolvent data.cusp (shifted data.cusp vector) = vector.val := by
  apply LinearMap.extendOfNorm_eq (shifted_range_dense data)
  refine ⟨1, fun vector => ?_⟩
  change ‖vector.val‖ ≤ 1 * ‖shifted data.cusp vector‖
  rw [one_mul]
  exact shifted_norm_bound data.cusp vector

theorem resolvent_commuting {degree : ℕ} (data : InducingData degree) (matrix : BinaryAdelicGL) :
    Commute (resolvent data.cusp) (unitaryOperator data.cusp matrix) := by
  have equality : Set.EqOn
      (fun vector => resolvent data.cusp (unitaryOperator data.cusp matrix vector))
      (fun vector => unitaryOperator data.cusp matrix (resolvent data.cusp vector))
      (Set.range (shifted data.cusp)) := by
    rintro vector ⟨smoothVector, rfl⟩
    dsimp only
    rw [← shifted_action, resolvent_shifted, resolvent_shifted]
    rfl
  ext vector
  exact equality.closure
    ((resolvent data.cusp).continuous.comp (unitaryOperator data.cusp matrix).continuous)
    ((unitaryOperator data.cusp matrix).continuous.comp (resolvent data.cusp).continuous)
    (shifted_range_dense data vector)

/-- Irreducibility and symmetry force the actual smooth Casimir to be scalar. -/
theorem exists_scalar {degree : ℕ} (data : InducingData degree) :
    ∃ value : ℂ, ∀ vector : data.cusp.smooth, casimir data.cusp vector = value • vector := by
  obtain ⟨scalar, scalarEquality⟩ := BoundedSchur.scalar data.cusp (resolvent data.cusp) (resolvent_commuting data)
  have nonzero : scalar ≠ 0 := by
    intro vanishing
    obtain ⟨vector, vectorNonzero⟩ := exists_nonzero_smooth data
    have equality := resolvent_shifted data vector
    rw [scalarEquality, vanishing, zero_smul, zero_apply] at equality
    exact vectorNonzero equality.symm
  refine ⟨scalar⁻¹ - Complex.I, ?_⟩
  intro vector
  apply Subtype.ext
  have equality := resolvent_shifted data vector
  rw [scalarEquality] at equality
  change scalar • shifted data.cusp vector = vector.val at equality
  have solved := congrArg (fun value : data.cusp.H => scalar⁻¹ • value) equality
  rw [smul_smul, inv_mul_cancel₀ nonzero, one_smul, shifted_apply] at solved
  change (casimir data.cusp vector).val = (scalar⁻¹ - Complex.I) • vector.val
  rw [sub_smul]
  exact eq_sub_of_add_eq solved

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirScalar
