module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.LevelSpherical

@[expose] public section


/-!
# The class-level entry comparison for the bad plane and the good-line component

`classLevel_badPlane`: for the spherical section `S` (the same data as `classLevel_spherical`), the bad-plane section
`badPlaneWeight · planeSource` (the part of the plane source supported on the bad-plane orbit `P(ℚ₃)K₁` at `3`) is sent by
any `T` realizing the standard operator, after projection to the **good-line component** of the line stratum
cohomology (`goodComponent`), to `entryScalar n S.rBad · [goodLineWeight · lineSource]`, where
`S.rBad = (1/9) L^{(3)}(h,k-2)/L^{(3)}(h,k-1)` and

* `entryScalar n S.rBad = - S.printedScalar` (`entryScalar_rPrint`), i.e. **minus** the paper's printed scalar
  `-2πi/(9(n+1)) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)` (sign: the library line source is minus the paper's line section; see
  `Entry/EntryDictionary`);
* `entryScalar n S.rBad ≠ 0`.

All of R-a (`cOmega_isSourceCocycle`), R-b (`classLevel_of_Ra`), R-c (`standardEndpointIntegral`, `4 ≤ n`), R-e
(`badPlaneEntryIdentity`) and the local-global dictionary (`goodLineWeight_rational`) are discharged; the hypotheses
that remain are the identification of the Levi data with the Eichler datum (`hE`, `hE'`) and holomorphy of the datum;
`Entry/ClassLevelEichler.classLevel_badPlane_eichler` discharges them for the Levi data of an `EichlerInput`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- **The good-line component of the bad-plane comparison.** -/
theorem classLevel_badPlane (n : ℕ) (hn : 4 ≤ n) (D : InducingData n) (S : SphericalEntryData D)
    (E : LeviCocycleData D.cusp n) (E' : LineLeviCocycleData D.cusp n)
    (hE : ∀ A, E.α A = eichlerNormal n S.F A) (hE' : ∀ A, E'.α A = eichlerNormalTw n S.F A)
    (holomorphic : ∀ x, DifferentiableOn ℂ (S.F x) {z : ℂ | 0 < z.im})
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T) :
    entryScalar n S.rBad ≠ 0 ∧ entryScalar n S.rBad = -S.printedScalar ∧
      ∀ (hps : IsSourceCocycle D .plane (fun y g => badPlaneWeight g • planeSource D E y g))
        (hls : IsSourceCocycle D .line (fun y g => goodLineWeight g • lineSource D E' y g)),
        goodComponent n D.chi .line
            (T (SourceQuotient.sourceToSummand D .plane
              ⟨fun y g => badPlaneWeight g • planeSource D E y g, hps⟩)).val =
          entryScalar n S.rBad • (SourceQuotient.sourceToSummand D .line
            ⟨fun y g => goodLineWeight g • lineSource D E' y g, hls⟩).val := by
  have hc : ∀ g : RealGL3, componentCharacter D.chi g = 1 := componentCharacter_eq_one_of_integral D.chi S.hχ
  have decay : ∀ x, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im →
      ‖cuspScalarWeightedRealization D.cusp S.halfWeight S.vector x z‖ ^ 2 * z.im ^ (n + 3) ≤ M :=
    fun x => decay_of_weight D.cusp S.halfWeight S.weight S.vector x
  have hr : S.rBad ≠ 0 := by
    rw [S.rBad_eq_rPrint]
    exact S.rPrint_ne_zero
  obtain ⟨h0, H⟩ := classLevel_good_of_eichler n hn D badPlaneWeight_planeWeight goodLineWeight_lineWeight E E'
    S.halfWeight S.vector (fixed_of_spherical D.cusp S.vector S.spherical) hE hE' hc S.hχ holomorphic decay T hT
    (standardEndpointIntegral hn) S.rBad hr (badPlaneEntryIdentity S) goodLineWeight_rational
  refine ⟨h0, ?_, H⟩
  rw [S.rBad_eq_rPrint]
  exact S.entryScalar_rPrint

namespace SphericalEntryData

variable {n : ℕ} {D : InducingData n} (S : SphericalEntryData D)

/-- **The bad-plane class-level scalar is minus the paper's printed scalar, written with the ratio of
`global_entry_ne_zero`** (equation `ar:eq:globalentry`):
`entryScalar n S.rBad = -( -2πi/(9(n+1)) · L^{(3)}(h,n+1)/L^{(3)}(h,n+2) )`, with both `L`-values multiplied by their
Euler factor at `3` as in the target. -/
theorem entryScalar_rBad_frozen : entryScalar n S.rBad =
    -(-2 * Real.pi * Complex.I / (9 * ((n : ℂ) + 1)) *
      ((LSeries (fun m => fourierCoeff S.form m) ((n : ℂ) + 1) *
          (1 - fourierCoeff S.form 3 * (3 : ℂ) ^ (-((n : ℂ) + 1)) + (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 1)))) /
        (LSeries (fun m => fourierCoeff S.form m) ((n : ℂ) + 2) *
          (1 - fourierCoeff S.form 3 * (3 : ℂ) ^ (-((n : ℂ) + 2)) + (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 2)))))) := by
  rw [S.rBad_eq_rPrint, S.entryScalar_rPrint, S.printedScalar_frozen]

/-- The bad-plane class-level scalar is nonzero, by the `global_entry_ne_zero`. -/
theorem entryScalar_rBad_ne_zero_of_frozen : entryScalar n S.rBad ≠ 0 := by
  rw [S.rBad_eq_rPrint, S.entryScalar_rPrint]
  exact neg_ne_zero.mpr S.printedScalar_ne_zero_of_frozen

end SphericalEntryData

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
