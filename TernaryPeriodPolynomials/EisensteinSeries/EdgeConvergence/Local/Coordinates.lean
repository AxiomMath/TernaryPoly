module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.ThreeMeasure

@[expose] public section


/-!
# Coordinates of the line radical at the places `∞` and `3`

The adeles split as `(ℝ × ℚ₃) × 𝔸_f^{(3)}`, where `𝔸_f^{(3)}` is the group of finite adeles with
vanishing `3`-component. The splitting is measure preserving for the normalized Haar measures, so
an integral over the line radical `𝔸²` is an iterated integral over `(ℝ × ℚ₃)²` and
`(𝔸_f^{(3)})²`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- A coordinate at the two places `∞` and `3`. -/
abbrev LocalLine := ℝ × ℚ_[3]

/-- The adele with the given components at `∞` and `3` and zero components elsewhere. -/
def localAdele (value : LocalLine) : Adeles := (value.1, finiteAtThreeScalar value.2)

/-- A finite adele with vanishing `3`-component, viewed as an adele. -/
def awayAdele (value : FiniteAwayThree) : Adeles := (0, value.val)

local instance normalizedLocalThreeMeasure_isAddHaar :
    normalizedLocalThreeMeasure.IsAddHaarMeasure :=
  normalizedLocalThreeMeasure_haar

/-- Lebesgue measure at `∞` times the Haar measure of `ℚ₃` giving `ℤ₃` mass one. -/
def localLineMeasure : Measure LocalLine := (volume : Measure ℝ).prod normalizedLocalThreeMeasure

instance localLineMeasure_sigmaFinite : SigmaFinite localLineMeasure :=
  inferInstanceAs (SigmaFinite ((volume : Measure ℝ).prod normalizedLocalThreeMeasure))

/-- The measure on the local part of the line radical. -/
def localRadicalMeasure : Measure (LocalLine × LocalLine) := localLineMeasure.prod localLineMeasure

instance localRadicalMeasure_sigmaFinite : SigmaFinite localRadicalMeasure :=
  inferInstanceAs (SigmaFinite (localLineMeasure.prod localLineMeasure))

/-- The measure on the part of the line radical away from `∞` and `3`. -/
def awayRadicalMeasure : Measure (FiniteAwayThree × FiniteAwayThree) :=
  finiteAwayThreeMeasure.prod finiteAwayThreeMeasure

instance awayRadicalMeasure_sigmaFinite : SigmaFinite awayRadicalMeasure :=
  inferInstanceAs (SigmaFinite (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))

/-- The line radical element with local coordinates `u`. -/
def localRadical (coordinates : LocalLine × LocalLine) : AdelicGL :=
  lineUnipotent (localAdele coordinates.1) (localAdele coordinates.2)

/-- The adeles as local part plus part away from `∞` and `3`. -/
def adeleLocalAwayJoin : (LocalLine × FiniteAwayThree) ≃ₜ Adeles :=
  (Homeomorph.prodAssoc ℝ ℚ_[3] FiniteAwayThree).trans
    ((Homeomorph.refl ℝ).prodCongr finiteThreeSplit.symm.toHomeomorph)

theorem adeleLocalAwayJoin_apply (pair : LocalLine × FiniteAwayThree) :
    adeleLocalAwayJoin pair = localAdele pair.1 + awayAdele pair.2 := by
  change (pair.1.1, finiteAtThreeScalar pair.1.2 + pair.2.val) = _
  exact Prod.ext (add_zero _).symm rfl

theorem adeleLocalAwayJoin_measurePreserving :
    MeasurePreserving adeleLocalAwayJoin (localLineMeasure.prod finiteAwayThreeMeasure)
      adeleMeasure := by
  have associate := measurePreserving_prodAssoc (volume : Measure ℝ) normalizedLocalThreeMeasure
    finiteAwayThreeMeasure
  have combine := (MeasurePreserving.id (volume : Measure ℝ)).prod
    finiteThreeSplit_symm_measurePreserving
  exact combine.comp associate

/-- The line radical as local coordinates plus coordinates away from `∞` and `3`. -/
def radicalLocalAwayJoin :
    ((LocalLine × LocalLine) × (FiniteAwayThree × FiniteAwayThree)) ≃ₜ (Adeles × Adeles) :=
  (Homeomorph.prodProdProdComm LocalLine LocalLine FiniteAwayThree FiniteAwayThree).trans
    (adeleLocalAwayJoin.prodCongr adeleLocalAwayJoin)

theorem radicalLocalAwayJoin_apply
    (pair : (LocalLine × LocalLine) × (FiniteAwayThree × FiniteAwayThree)) :
    radicalLocalAwayJoin pair =
      (localAdele pair.1.1 + awayAdele pair.2.1, localAdele pair.1.2 + awayAdele pair.2.2) := by
  change (adeleLocalAwayJoin (pair.1.1, pair.2.1), adeleLocalAwayJoin (pair.1.2, pair.2.2)) = _
  rw [adeleLocalAwayJoin_apply, adeleLocalAwayJoin_apply]

theorem radicalLocalAwayJoin_measurePreserving :
    MeasurePreserving radicalLocalAwayJoin (localRadicalMeasure.prod awayRadicalMeasure)
      radicalMeasure := by
  have rearrange := measurePreserving_prodTranspose localLineMeasure localLineMeasure
    finiteAwayThreeMeasure finiteAwayThreeMeasure
  exact (adeleLocalAwayJoin_measurePreserving.prod adeleLocalAwayJoin_measurePreserving).comp
    rearrange

/-- An integral over the line radical is an iterated integral: first away from `∞` and `3`, then
over the local coordinates. -/
theorem radicalIntegral_local_fubini {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (integrand : Adeles × Adeles → E) (integrable : Integrable integrand radicalMeasure) :
    (∫ parameter, integrand parameter ∂radicalMeasure) =
      ∫ localParameter, ∫ away, integrand (radicalLocalAwayJoin (localParameter, away))
        ∂awayRadicalMeasure ∂localRadicalMeasure := by
  have lifted := radicalLocalAwayJoin_measurePreserving.integrable_comp_of_integrable integrable
  rw [← radicalLocalAwayJoin_measurePreserving.integral_comp
    radicalLocalAwayJoin.measurableEmbedding integrand]
  exact integral_prod _ lifted

/-- The integrand of an integrable function on the line radical is integrable on the local
coordinates after integrating away from `∞` and `3`, and almost every away slice is integrable. -/
theorem radicalIntegrable_local_slices {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (integrand : Adeles × Adeles → E) (integrable : Integrable integrand radicalMeasure) :
    (∀ᵐ localParameter ∂localRadicalMeasure, Integrable
      (fun away => integrand (radicalLocalAwayJoin (localParameter, away))) awayRadicalMeasure) ∧
    Integrable (fun localParameter => ∫ away,
      integrand (radicalLocalAwayJoin (localParameter, away)) ∂awayRadicalMeasure)
        localRadicalMeasure := by
  have lifted := radicalLocalAwayJoin_measurePreserving.integrable_comp_of_integrable integrable
  exact ⟨lifted.prod_right_ae, lifted.integral_prod_left⟩

end TernaryPeriodPolynomials.EdgeConvergence
