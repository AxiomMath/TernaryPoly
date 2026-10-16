module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SameConstituent.LevelSupport

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers

noncomputable section
attribute [local instance] Classical.propDecidable

def badCut {Vector : Type} [Zero Vector] (family : AdelicGL → Vector) (base : AdelicGL) : Vector :=
  if AdelicGood base then 0 else family base

theorem bad_cut_infinity {Vector : Type} [Zero Vector]
    (family : AdelicGL → Vector) (base : AdelicGL) (translate : RealGL3) :
    badCut family (base * atInfinity translate) =
      if AdelicGood base then 0 else family (base * atInfinity translate) := by
  simp only [badCut, adelic_good_infinity]

theorem bad_cut_parabolic {Vector : Type} [Zero Vector]
    (family : AdelicGL → Vector) {parabolic_matrix : AdelicGL}
    (membership : InPlaneParabolic parabolic_matrix) (base : AdelicGL) :
    badCut family (parabolic_matrix * base) =
      if AdelicGood base then 0 else family (parabolic_matrix * base) := by
  simp only [badCut, adelic_good_left_parabolic membership]

theorem bad_cut_smooth_cusp_lift {degree arity : ℕ} {data : InducingData degree}
    {parameter : ℂ} {family : (Fin arity → RealGL3) → AdelicGL → ℂ}
    (family_lift : HasSmoothCuspLift data .plane parameter family) :
    HasSmoothCuspLift data .plane parameter (fun coordinates => badCut (family coordinates)) := by
  intro base
  by_cases base_good : AdelicGood base
  · refine ⟨0, smooth_zero, ?_⟩
    intro coordinates binary
    simp only [Pi.zero_apply, map_zero, adelic_good_binary, badCut,
      adelic_good_infinity, ite_eq_left base_good, mul_zero]
  · obtain ⟨vector, vector_smooth, evaluation⟩ := family_lift base
    refine ⟨vector, vector_smooth, ?_⟩
    intro coordinates binary
    simp only [badCut, adelic_good_binary, adelic_good_infinity, ite_eq_right base_good]
    exact evaluation coordinates binary

theorem bad_cut_induced {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {family : AdelicGL → ℂ} (family_induced : IsInduced data .plane parameter family) :
    IsInduced data .plane parameter (badCut family) := by
  obtain ⟨family_smooth, family_invariant, family_lift, family_radical,
    family_character, family_cusp⟩ := family_induced
  refine ⟨?_, ?_, bad_cut_smooth_cusp_lift family_lift, ?_, ?_, ?_⟩
  · intro base
    simp only [bad_cut_infinity]
    by_cases base_good : AdelicGood base
    · simp only [ite_eq_left base_good]
      exact smooth_zero
    · simpa only [ite_eq_right base_good] using family_smooth base
  · intro compact base
    simp only [badCut, adelic_good_finite, family_invariant]
  · intro first second base
    rw [bad_cut_parabolic _ (by simp [InPlaneParabolic, planeUnipotent])]
    simp only [badCut, family_radical]
  · intro scalar base
    rw [bad_cut_parabolic _ (planeLevi_mem 1 scalar)]
    simp only [badCut, family_character]
    split_ifs <;> simp
  · intro base
    by_cases base_good : AdelicGood base
    · simpa only [badCut, adelic_good_left_parabolic (planeLevi_mem _ _),
        ite_eq_left base_good, mul_zero, Pi.zero_def] using
        (cuspFunctions data.cusp).zero_mem
    · simpa only [badCut, adelic_good_left_parabolic (planeLevi_mem _ _),
        ite_eq_right base_good] using family_cusp base

def badSource {degree : ℕ} (source : SourceCochain degree) : SourceCochain degree :=
  fun coordinates => badCut (source coordinates)

theorem bad_source_cocycle {degree : ℕ} {data : InducingData degree}
    {source : SourceCochain degree} (source_closed : IsSourceCocycle data .plane source) :
    IsSourceCocycle data .plane (badSource source) := by
  obtain ⟨source_induced, source_lift, source_equivariant, source_cycle⟩ := source_closed
  have coefficient (coordinates : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ) :
      (fun base => ((badSource source) coordinates base).val.coeff monomial) =
        badCut (fun base => (source coordinates base).val.coeff monomial) := by
    funext base
    simp only [badSource, badCut]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro coordinates monomial
    rw [coefficient]
    exact bad_cut_induced (source_induced coordinates monomial)
  · intro monomial
    have family_equality :
        (fun coordinates base => ((badSource source) coordinates base).val.coeff monomial) =
          fun coordinates => badCut
            (fun base => (source coordinates base).val.coeff monomial) := by
      funext coordinates
      exact coefficient coordinates monomial
    rw [family_equality]
    exact bad_cut_smooth_cusp_lift (source_lift monomial)
  · intro translate coordinates base
    simp only [badSource, badCut, adelic_good_infinity]
    split_ifs <;> simp only [map_zero, source_equivariant]
  · intro coordinates base
    simp only [badSource, badCut]
    split_ifs
    · simp
    · exact source_cycle coordinates base

theorem bad_source_support {degree : ℕ} (source : SourceCochain degree) :
    BadPlaneSource (badSource source) := by
  intro coordinates frame frame_good translate
  simp only [badSource, badCut, adelic_good_infinity,
    adelic_good_rational, ite_eq_left frame_good]

end

end TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers
