module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Global
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SameConstituent.BoundarySupport

@[expose] public section


/-!
# Cutoff at the plane cusps

Every class of the plane boundary summand has a representative supported on the Γ-orbit of one
reference flag: the source cocycle is multiplied by the indicator of the adelic goodness at the
place three, which kills either the bad or the good flags of the rational cycle.  The Shapiro
coordinate at the kept cusp is unchanged and the one at the other cusp is zero
(`exists_cutoff_plane`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers

namespace TernaryPeriodPolynomials.Separation

variable {n : ℕ}

attribute [local instance] Classical.propDecidable

/-- Keep the values at adelically good points, kill the others. -/
def goodCut {Vector : Type} [Zero Vector] (family : AdelicGL → Vector) (base : AdelicGL) :
    Vector :=
  if AdelicGood base then family base else 0

theorem good_cut_smooth_cusp_lift {degree arity : ℕ} {data : InducingData degree}
    {parameter : ℂ} {family : (Fin arity → RealGL3) → AdelicGL → ℂ}
    (family_lift : HasSmoothCuspLift data .plane parameter family) :
    HasSmoothCuspLift data .plane parameter (fun coordinates => goodCut (family coordinates)) := by
  intro base
  by_cases base_good : AdelicGood base
  · obtain ⟨vector, vector_smooth, evaluation⟩ := family_lift base
    refine ⟨vector, vector_smooth, ?_⟩
    intro coordinates binary
    simp only [goodCut, adelic_good_binary, adelic_good_infinity, ite_eq_left base_good]
    exact evaluation coordinates binary
  · refine ⟨0, smooth_zero, ?_⟩
    intro coordinates binary
    simp only [Pi.zero_apply, map_zero, adelic_good_binary, goodCut,
      adelic_good_infinity, ite_eq_right base_good, mul_zero]

theorem good_cut_induced {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {family : AdelicGL → ℂ} (family_induced : IsInduced data .plane parameter family) :
    IsInduced data .plane parameter (goodCut family) := by
  obtain ⟨family_smooth, family_invariant, family_lift, family_radical,
    family_character, family_cusp⟩ := family_induced
  refine ⟨?_, ?_, good_cut_smooth_cusp_lift family_lift, ?_, ?_, ?_⟩
  · intro base
    simp only [goodCut, adelic_good_infinity]
    by_cases base_good : AdelicGood base
    · simpa only [ite_eq_left base_good] using family_smooth base
    · simp only [ite_eq_right base_good]
      exact smooth_zero
  · intro compact base
    simp only [goodCut, adelic_good_finite, family_invariant]
  · intro first second base
    have membership : InPlaneParabolic (planeUnipotent first second) := by
      simp [InPlaneParabolic, planeUnipotent]
    simp only [goodCut, adelic_good_left_parabolic membership, family_radical]
  · intro scalar base
    simp only [goodCut, adelic_good_left_parabolic (planeLevi_mem 1 scalar), family_character]
    split_ifs <;> simp
  · intro base
    by_cases base_good : AdelicGood base
    · simpa only [goodCut, adelic_good_left_parabolic (planeLevi_mem _ _),
        ite_eq_left base_good] using family_cusp base
    · simpa only [goodCut, adelic_good_left_parabolic (planeLevi_mem _ _),
        ite_eq_right base_good, mul_zero, Pi.zero_def] using
        (cuspFunctions data.cusp).zero_mem

/-- The source cocycle with its values at adelically bad points killed. -/
def goodSource {degree : ℕ} (source : SourceCochain degree) : SourceCochain degree :=
  fun coordinates => goodCut (source coordinates)

theorem good_source_cocycle {degree : ℕ} {data : InducingData degree}
    {source : SourceCochain degree} (source_closed : IsSourceCocycle data .plane source) :
    IsSourceCocycle data .plane (goodSource source) := by
  obtain ⟨source_induced, source_lift, source_equivariant, source_cycle⟩ := source_closed
  have coefficient (coordinates : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ) :
      (fun base => ((goodSource source) coordinates base).val.coeff monomial) =
        goodCut (fun base => (source coordinates base).val.coeff monomial) := by
    funext base
    simp only [goodSource, goodCut]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro coordinates monomial
    rw [coefficient]
    exact good_cut_induced (source_induced coordinates monomial)
  · intro monomial
    have family_equality :
        (fun coordinates base =>
          ((goodSource source) coordinates base).val.coeff monomial) =
          fun coordinates => goodCut
            (fun base => (source coordinates base).val.coeff monomial) := by
      funext coordinates
      exact coefficient coordinates monomial
    rw [family_equality]
    exact good_cut_smooth_cusp_lift (source_lift monomial)
  · intro translate coordinates base
    simp only [goodSource, goodCut, adelic_good_infinity]
    split_ifs <;> simp only [map_zero, source_equivariant]
  · intro coordinates base
    simp only [goodSource, goodCut]
    split_ifs
    · exact source_cycle coordinates base
    · simp

theorem good_source_evaluates {degree : ℕ} {data : InducingData degree}
    {source : SourceCochain degree} {cycle : MaximalCycles degree data.chi .plane}
    (evaluation : Evaluates data .plane source cycle) :
    Evaluates data .plane (goodSource source) (flagCutCycle true cycle) := by
  intro coordinates frame
  change (if GoodFlag .plane (QuotientGroup.mk frame) then
    cycle.val.val coordinates (QuotientGroup.mk frame) else 0) =
    goodSource source (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (coordinates index))
      (rationalGroup frame⁻¹)
  rw [evaluation coordinates frame]
  simp only [goodSource, goodCut, adelic_good_rational]

/-- Shapiro coordinates of a cut class: unchanged at the kept cusp, zero at the killed one. -/
theorem cuspRes_cut (D : InducingData n) (good : Bool)
    {c c' : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n}
    {z z' : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)}
    (hz : Evaluates D .plane c z) (hz' : Evaluates D .plane c' z')
    (hkeep : ∀ (q : RationalGL3), (QuotientGroup.mk q : Flags .plane) = cuspFlag .plane good →
      ∀ x : Fin 3 → RationalGL3,
        c' (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) (rationalGroup q⁻¹) =
          c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) (rationalGroup q⁻¹))
    (hkill : ∀ (q : RationalGL3),
      (QuotientGroup.mk q : Flags .plane) = cuspFlag .plane (!good) →
      ∀ x : Fin 3 → RationalGL3,
        c' (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) (rationalGroup q⁻¹) =
          0) :
    cuspRes n D.chi .plane good
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) z') =
      cuspRes n D.chi .plane good
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) z) ∧
    cuspRes n D.chi .plane (!good)
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) z') = 0 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (cuspFlag .plane good)
    rw [cuspRes_classOf, cuspRes_classOf]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rw [← hq, fixedPointCycle_evaluates D .plane hz' q x,
      fixedPointCycle_evaluates D .plane hz q x]
    exact hkeep q hq x
  · obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (cuspFlag .plane (!good))
    exact cuspRes_classOf_eq_zero_of_vanish D .plane (!good) hz' q hq (hkill q hq)

/-- **Cutoff at the plane cusps.** Every class of the plane boundary summand has a representative
in the summand with the same Shapiro coordinate at one cusp and zero coordinate at the other. -/
theorem exists_cutoff_plane (D : InducingData n) (good : Bool) {a : StratumH2 n D.chi .plane}
    (ha : a ∈ boundarySummand D .plane) :
    ∃ a' ∈ boundarySummand D .plane,
      cuspRes n D.chi .plane good a' = cuspRes n D.chi .plane good a ∧
        cuspRes n D.chi .plane (!good) a' = 0 := by
  obtain ⟨source, cycle, source_closed, evaluation, class_eq⟩ :=
    boundary_summand_has_representative D .plane ⟨a, ha⟩
  have class_eq' : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) cycle = a := class_eq
  subst class_eq'
  cases good
  · refine ⟨classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
      (flagCutCycle false cycle),
      classOf_mem_boundarySummand D .plane (bad_source_cocycle source_closed)
        (bad_source_evaluates evaluation),
      cuspRes_cut D false evaluation (bad_source_evaluates evaluation) ?_ ?_⟩
    · intro q hq x
      have not_good : ¬ GoodFlag .plane (QuotientGroup.mk q : Flags .plane) := by
        intro flag_good
        rw [hq, cuspFlag_good_iff] at flag_good
        exact Bool.false_ne_true flag_good
      have not_adelic : ¬ AdelicGood (rationalGroup q⁻¹) :=
        fun adelic => not_good ((adelic_good_rational q).mp adelic)
      simp only [badSource, badCut, ite_eq_right not_adelic]
    · intro q hq x
      have flag_good : GoodFlag .plane (QuotientGroup.mk q : Flags .plane) := by
        rw [hq]
        exact (cuspFlag_good_iff .plane _).mpr rfl
      have adelic : AdelicGood (rationalGroup q⁻¹) := (adelic_good_rational q).mpr flag_good
      simp only [badSource, badCut, ite_eq_left adelic]
  · refine ⟨classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
      (flagCutCycle true cycle),
      classOf_mem_boundarySummand D .plane (good_source_cocycle source_closed)
        (good_source_evaluates evaluation),
      cuspRes_cut D true evaluation (good_source_evaluates evaluation) ?_ ?_⟩
    · intro q hq x
      have flag_good : GoodFlag .plane (QuotientGroup.mk q : Flags .plane) := by
        rw [hq]
        exact (cuspFlag_good_iff .plane _).mpr rfl
      have adelic : AdelicGood (rationalGroup q⁻¹) := (adelic_good_rational q).mpr flag_good
      simp only [goodSource, goodCut, ite_eq_left adelic]
    · intro q hq x
      have not_good : ¬ GoodFlag .plane (QuotientGroup.mk q : Flags .plane) := by
        intro flag_good
        rw [hq, cuspFlag_good_iff] at flag_good
        exact Bool.false_ne_true flag_good
      have not_adelic : ¬ AdelicGood (rationalGroup q⁻¹) :=
        fun adelic => not_good ((adelic_good_rational q).mp adelic)
      simp only [goodSource, goodCut, ite_eq_right not_adelic]

end TernaryPeriodPolynomials.Separation
