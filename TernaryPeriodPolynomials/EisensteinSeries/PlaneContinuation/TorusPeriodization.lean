module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Schwartz.Periodization

@[expose] public section


open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzPeriodization

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TorusPeriodization

noncomputable def toTorus (vector : RealSpace) : UnitAddTorus Coordinate :=
  fun coordinate => (vector coordinate : AddCircle (1 : ℝ))

theorem integer_cast_zero (integer : ℤ) : ((integer : ℝ) : AddCircle (1 : ℝ)) = 0 :=
  (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨integer, by simp⟩

theorem toTorus_eq_iff (first second : RealSpace) :
    toTorus first = toTorus second ↔ ∃ integer : Coordinate → ℤ, first = second + integerVector integer := by
  constructor
  · intro equality
    have coordinateEquality : ∀ coordinate : Coordinate, ∃ integer : ℤ,
        (integer : ℝ) = first coordinate - second coordinate := by
      intro coordinate
      have circleEquality : ((first coordinate - second coordinate : ℝ) : AddCircle (1 : ℝ)) = 0 := by
        rw [AddCircle.coe_sub]
        exact sub_eq_zero.mpr (congrFun equality coordinate)
      simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp circleEquality
    choose integer integerEquality using coordinateEquality
    refine ⟨integer, ?_⟩
    ext coordinate
    change first coordinate = second coordinate + (integer coordinate : ℝ)
    linarith [integerEquality coordinate]
  · rintro ⟨integer, rfl⟩
    funext coordinate
    change ((second coordinate + (integer coordinate : ℝ) : ℝ) : AddCircle (1 : ℝ)) = _
    rw [AddCircle.coe_add, integer_cast_zero, add_zero]
    rfl

theorem toTorus_surjective : Function.Surjective toTorus := by
  intro point
  have existsPreimage : ∀ coordinate : Coordinate, ∃ value : ℝ, (value : AddCircle (1 : ℝ)) = point coordinate :=
    fun coordinate => QuotientAddGroup.mk_surjective (point coordinate)
  choose values equality using existsPreimage
  exact ⟨WithLp.toLp 2 values, funext equality⟩

theorem toTorus_continuous : Continuous toTorus :=
  continuous_pi (fun coordinate => (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_apply coordinate).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℝ)).continuous))

theorem toTorus_open : IsOpenMap toTorus := by
  have coordinateOpen : IsOpenMap (Pi.map (fun _ : Coordinate => (fun value : ℝ => (value : AddCircle (1 : ℝ))))) :=
    IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall (fun _ => QuotientAddGroup.mk_surjective))
  exact coordinateOpen.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℝ)).toHomeomorph.isOpenMap

theorem toTorus_quotient : Topology.IsQuotientMap toTorus :=
  toTorus_open.isQuotientMap toTorus_continuous toTorus_surjective

noncomputable def representative (point : UnitAddTorus Coordinate) : RealSpace :=
  (toTorus_surjective point).choose

theorem representative_projection (point : UnitAddTorus Coordinate) : toTorus (representative point) = point :=
  (toTorus_surjective point).choose_spec

noncomputable def torusSum (function : SchwartzMap RealSpace ℂ) (point : UnitAddTorus Coordinate) : ℂ :=
  periodization function (representative point)

theorem torusSum_apply (function : SchwartzMap RealSpace ℂ) (vector : RealSpace) :
    torusSum function (toTorus vector) = periodization function vector := by
  obtain ⟨integer, equality⟩ := (toTorus_eq_iff (representative (toTorus vector)) vector).mp
    (representative_projection (toTorus vector))
  unfold torusSum
  rw [equality, integer_invariant]

theorem torusSum_continuous (function : SchwartzMap RealSpace ℂ) : Continuous (torusSum function) := by
  apply toTorus_quotient.continuous_iff.mpr
  have equality : torusSum function ∘ toTorus = periodization function := funext (torusSum_apply function)
  rw [equality]
  exact SchwartzPeriodization.continuous function

noncomputable def continuousSum (function : SchwartzMap RealSpace ℂ) : C(UnitAddTorus Coordinate, ℂ) :=
  ⟨torusSum function, torusSum_continuous function⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TorusPeriodization
