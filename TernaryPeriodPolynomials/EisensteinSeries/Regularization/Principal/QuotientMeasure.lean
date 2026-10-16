module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.SpecialLinearVolume
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearUnimodular

@[expose] public section


open Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "PrincipalQuotient" => Quotient (MulAction.orbitRel principalRealSpecialLinear RealSL3)

noncomputable def principalSpecialLinearQuotientMeasure : Measure PrincipalQuotient :=
  Measure.map (Quotient.mk (MulAction.orbitRel principalRealSpecialLinear RealSL3))
    (realSpecialLinearHaar.restrict principalRealSpecialLinearDomain)

theorem principalSpecialLinearQuotientMeasure_eq_map {domain : Set RealSL3}
    (fundamental : IsFundamentalDomain principalRealSpecialLinear domain realSpecialLinearHaar) :
    principalSpecialLinearQuotientMeasure =
      Measure.map (Quotient.mk (MulAction.orbitRel principalRealSpecialLinear RealSL3))
        (realSpecialLinearHaar.restrict domain) :=
  principalRealSpecialLinearDomain_fundamental.quotientMeasure_eq realSpecialLinearHaar fundamental

theorem principalSpecialLinearQuotientMeasure_univ :
    principalSpecialLinearQuotientMeasure Set.univ = realSpecialLinearHaar principalRealSpecialLinearDomain := by
  rw [principalSpecialLinearQuotientMeasure, Measure.map_apply_of_aemeasurable]
  · simp only [Set.preimage_univ, Measure.restrict_apply_univ]
  · exact measurable_quotient_mk''.aemeasurable
  · exact MeasurableSet.univ

instance principalSpecialLinearQuotientMeasure_finite : IsFiniteMeasure principalSpecialLinearQuotientMeasure := by
  constructor
  rw [principalSpecialLinearQuotientMeasure_univ]
  exact principalRealSpecialLinearDomain_measure_finite

theorem principalSpecialLinearQuotientMeasure_nonzero : principalSpecialLinearQuotientMeasure Set.univ ≠ 0 := by
  rw [principalSpecialLinearQuotientMeasure_univ]
  exact principalRealSpecialLinearDomain_fundamental.measure_ne_zero (NeZero.ne realSpecialLinearHaar)

theorem principalRealSpecialLinearDomain_right_fundamental (matrix : RealSL3) :
    IsFundamentalDomain principalRealSpecialLinear
      ((fun point => point * matrix) '' principalRealSpecialLinearDomain) realSpecialLinearHaar := by
  apply principalRealSpecialLinearDomain_fundamental.image_of_equiv (Equiv.mulRight matrix)
    (realSpecialLinearHaar_right_measurePreserving matrix⁻¹).quasiMeasurePreserving
    (Equiv.refl principalRealSpecialLinear)
  intro element point
  exact mul_assoc element.val point matrix

def principalSpecialLinearQuotientTranslate (matrix : RealSL3) : PrincipalQuotient → PrincipalQuotient :=
  Quotient.map (fun point => point * matrix) (by
    intro first second relation
    obtain ⟨element, equality⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp relation)
    change element.val * second = first at equality
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨element, ?_⟩
    change element.val * (second * matrix) = first * matrix
    rw [← mul_assoc, equality])

theorem principalSpecialLinearQuotientTranslate_mk (matrix point : RealSL3) :
    principalSpecialLinearQuotientTranslate matrix (Quotient.mk'' point) = Quotient.mk'' (point * matrix) := rfl

theorem principalSpecialLinearQuotientTranslate_measurable (matrix : RealSL3) :
    Measurable (principalSpecialLinearQuotientTranslate matrix) := by
  apply measurable_from_quotient.mpr
  exact measurable_quotient_mk''.comp ((continuous_id.mul continuous_const).measurable)

theorem principalSpecialLinearQuotientTranslate_measurePreserving (matrix : RealSL3) :
    MeasurePreserving (principalSpecialLinearQuotientTranslate matrix)
      principalSpecialLinearQuotientMeasure principalSpecialLinearQuotientMeasure := by
  refine ⟨principalSpecialLinearQuotientTranslate_measurable matrix, ?_⟩
  have embedding : MeasurableEmbedding (fun point : RealSL3 => point * matrix) :=
    (Homeomorph.mulRight matrix).measurableEmbedding
  have restricted := (realSpecialLinearHaar_right_measurePreserving matrix).restrict_image_emb
    embedding principalRealSpecialLinearDomain
  calc
    _ = Measure.map ((Quotient.mk'' : RealSL3 → PrincipalQuotient) ∘ (fun point => point * matrix))
        (realSpecialLinearHaar.restrict principalRealSpecialLinearDomain) := by
      rw [principalSpecialLinearQuotientMeasure, Measure.map_map
        (principalSpecialLinearQuotientTranslate_measurable matrix) measurable_quotient_mk'']
      rfl
    _ = Measure.map (Quotient.mk'' : RealSL3 → PrincipalQuotient)
        (realSpecialLinearHaar.restrict ((fun point => point * matrix) '' principalRealSpecialLinearDomain)) := by
      rw [← restricted.map_eq, Measure.map_map measurable_quotient_mk'' embedding.measurable]
    _ = _ := (principalSpecialLinearQuotientMeasure_eq_map
      (principalRealSpecialLinearDomain_right_fundamental matrix)).symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
