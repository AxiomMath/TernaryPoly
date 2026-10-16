module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.LevelProj
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REMain
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RCEndpoint
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.GoodWeights
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REValue

@[expose] public section


/-!
# The class-level entry comparison for the spherical section

`classLevel_spherical`: R-a (`cOmega_isSourceCocycle`), R-b (`classLevel_of_Ra`), R-c (`standardEndpointIntegral`, `4 ≤ n`)
and R-e (`finiteEntryIdentity_spherical`) are all discharged for the spherical section (`ι = ιL = 1`): any `T`
realizing the standard operator sends the class of `planeSource D E` to `c · [lineSource D E']`, with
`c = entryScalar n S.rFull = (-r)(-2πi/(n+1)) ≠ 0` and `r = S.rFull` the product of all local Euler factors (the one at
`3` included; `S.rFull_ne_zero`).  The hypotheses are the compatibility of the Levi data with the Eichler
datum (`hE`, `hE'`) and the holomorphy of the datum.

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

theorem planeWeight_one : PlaneWeight (fun _ => (1 : ℂ)) := ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- A spherical vector is fixed by the finite congruence level. -/
theorem fixed_of_spherical (σ : CuspidalRepresentation) (v : σ.smooth) (h : v.val ∈ cuspSphericalValues σ) :
    v.val ∈ BinaryLevel.fixedSubspace σ BinaryLevel.finiteCongruence := by
  rintro ⟨element, compact, _, rfl⟩
  exact h compact

/-- The decay of the weighted scalar realization of a vector of weight `2k = -(n+3)`. -/
theorem decay_of_weight {n : ℕ} (σ : CuspidalRepresentation) (hw : ℤ) (weight : 2 * hw = -((n : ℤ) + 3))
    (v : σ.smooth) (x : BinaryAdelicGL) :
    ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖cuspScalarWeightedRealization σ hw v x z‖ ^ 2 * z.im ^ (n + 3) ≤ M := by
  have hobtain1 := cuspScalarWeightedRealization_bound σ hw v
  obtain ⟨bound, hb0, hb⟩ := hobtain1
  refine ⟨bound ^ 2, fun z hz => ?_⟩
  have h1 : ‖cuspScalarWeightedRealization σ hw v x z‖ ≤ z.im ^ hw * bound := hb x ⟨z, hz⟩
  have hy : z.im ≠ 0 := hz.ne'
  have hpow : z.im ^ hw * z.im ^ hw * z.im ^ (n + 3) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hy, ← zpow_add₀ hy]
    have : hw + hw + ((n + 3 : ℕ) : ℤ) = 0 := by push_cast; omega
    rw [this, zpow_zero]
  have hyn : 0 ≤ z.im ^ (n + 3) := pow_nonneg hz.le _
  calc ‖cuspScalarWeightedRealization σ hw v x z‖ ^ 2 * z.im ^ (n + 3)
      ≤ (z.im ^ hw * bound) ^ 2 * z.im ^ (n + 3) := by
        gcongr
    _ = (z.im ^ hw * z.im ^ hw * z.im ^ (n + 3)) * bound ^ 2 := by ring
    _ = bound ^ 2 := by rw [hpow, one_mul]


/-- **The class-level entry comparison for the spherical section** (all of R-a, R-b, R-c, R-e discharged).
Any `T` realizing the standard operator sends `[planeSource D E]` to `entryScalar n S.rFull · [lineSource D E']`,
with `entryScalar n S.rFull = (-r)(-2πi/(n+1)) ≠ 0` and `r = S.rFull`.  Remaining hypotheses: the Levi data match the
Eichler datum (`hE`, `hE'`) and holomorphy of the datum. -/
theorem classLevel_spherical (n : ℕ) (hn : 4 ≤ n) (D : InducingData n) (S : SphericalEntryData D)
    (E : LeviCocycleData D.cusp n) (E' : LineLeviCocycleData D.cusp n)
    (hE : ∀ A, E.α A = eichlerNormal n S.F A) (hE' : ∀ A, E'.α A = eichlerNormalTw n S.F A)
    (holomorphic : ∀ x, DifferentiableOn ℂ (S.F x) {z : ℂ | 0 < z.im})
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T) :
    entryScalar n S.rFull ≠ 0 ∧ ∀ (hps : IsSourceCocycle D .plane (planeSource D E))
      (hls : IsSourceCocycle D .line (lineSource D E')),
      T (SourceQuotient.sourceToSummand D .plane ⟨planeSource D E, hps⟩) =
        entryScalar n S.rFull • SourceQuotient.sourceToSummand D .line ⟨lineSource D E', hls⟩ := by
  have hc : ∀ g : RealGL3, componentCharacter D.chi g = 1 := componentCharacter_eq_one_of_integral D.chi S.hχ
  have decay : ∀ x, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖S.F x z‖ ^ 2 * z.im ^ (n + 3) ≤ M :=
    fun x => decay_of_weight D.cusp S.halfWeight S.weight S.vector x
  have hRa : IsSourceCocycle D .plane (fun y g => cOmega n D S.F y g) :=
    cOmega_isSourceCocycle D S.F holomorphic E hE hc S.hχ (continuousStages D) S.halfWeight S.vector
      (fixed_of_spherical D.cusp S.vector S.spherical) rfl
  have hobtain2 := classLevel_of_Ra n hn D (ι := fun _ => (1 : ℂ)) (ιL := fun _ => (1 : ℂ)) planeWeight_one
    lineWeight_one E E' S.F hE hE' hc S.hχ holomorphic decay T hT (standardEndpointIntegral hn) S.rFull
    S.rFull_ne_zero (finiteEntryIdentity_spherical S (fun _ => 1)) hRa
  obtain ⟨hc0, H⟩ := hobtain2
  refine ⟨hc0, fun hps hls => ?_⟩
  have hps' : IsSourceCocycle D .plane (fun y g => (fun _ : AdelicGL => (1 : ℂ)) g • planeSource D E y g) := by
    simpa only [one_smul] using hps
  have hls' : IsSourceCocycle D .line (fun y g => (fun _ : AdelicGL => (1 : ℂ)) g • lineSource D E' y g) := by
    simpa only [one_smul] using hls
  have hobtain3 := H hps' hls'
  obtain ⟨J, hTJ, _, hJ, hJclass⟩ := hobtain3
  have e1 : (⟨planeSource D E, hps⟩ : SourceSpace.sourceCocycles D .plane) =
      ⟨fun y g => (fun _ : AdelicGL => (1 : ℂ)) g • planeSource D E y g, hps'⟩ :=
    Subtype.ext (funext fun y => funext fun g => (one_smul ℂ _).symm)
  have e2 : (⟨fun y g => (fun _ : AdelicGL => (1 : ℂ)) g • J.val y g, hJ⟩ : SourceSpace.sourceCocycles D .line) = J :=
    Subtype.ext (funext fun y => funext fun g => one_smul ℂ _)
  have e3 : (⟨fun y g => (fun _ : AdelicGL => (1 : ℂ)) g • lineSource D E' y g, hls'⟩ :
      SourceSpace.sourceCocycles D .line) = ⟨lineSource D E', hls⟩ :=
    Subtype.ext (funext fun y => funext fun g => one_smul ℂ _)
  exact (congrArg (fun z => T (SourceQuotient.sourceToSummand D .plane z)) e1).trans
    (hTJ.trans ((congrArg (SourceQuotient.sourceToSummand D .line) e2.symm).trans
      (hJclass.trans (congrArg (fun z => entryScalar n S.rFull •
        SourceQuotient.sourceToSummand D .line z) e3))))

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
