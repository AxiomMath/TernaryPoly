module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.LevelBadPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Line
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceBridge

@[expose] public section


/-!
# The bad-plane / good-line class-level comparison for the Levi data of an Eichler input

`classLevel_badPlane_eichler`: in `classLevel_badPlane` the Levi data `E`, `E'` of the plane and line sources are
arbitrary data matching the Eichler normal forms of the scalar function `S.F` of the spherical vector.  Here they are
the actual data of the construction: given an `EichlerInput I` (the lowest-weight holomorphic vector of the
cohomological datum) with the same weight and vector as `S`,

* `E = LeviCocycleData.ofEichler (I.eichlerCocycle_spec stages)` (plane source, `α = I.eichlerCocycle`),
* `E' = LineLeviCocycleData.ofSignEichler (I.signEichlerCocycle_spec stages)` (line source, `α = I.signEichlerCocycle`),

so `hE`, `hE'` are the library identities `eichlerCocycle_eq_eichlerNormal`, `eichlerCocycleTw_eq_eichlerNormalTw`, and
holomorphy of `S.F` is `cuspScalarWeightedRealization_holomorphic` applied to `I.holomorphic`.  Nothing else is assumed.

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

namespace SphericalEntryData

variable {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) (I : EichlerInput D.cusp n)

/-- The plane Levi datum of the Eichler input. -/
def planeLevi : LeviCocycleData D.cusp n :=
  LeviCocycleData.ofEichler (I.eichlerCocycle_spec (continuousStages D))

/-- The line Levi datum of the Eichler input (sign-twisted Eichler cocycle). -/
def lineLevi : LineLeviCocycleData D.cusp n :=
  LineLeviCocycleData.ofSignEichler (I.signEichlerCocycle_spec (continuousStages D))

variable {S I}

theorem endpointScalar_eq (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) :
    endpointScalar D.cusp I.halfWeight I.vector = S.F := by
  rw [hw, hv]
  rfl

theorem planeLevi_alpha (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) (A : BinaryRealGL) :
    (planeLevi I).α A = eichlerNormal n S.F A := by
  show I.eichlerCocycle A = _
  rw [I.eichlerCocycle_eq_eichlerNormal (continuousStages D) A, endpointScalar_eq hw hv]

theorem lineLevi_alpha (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) (A : BinaryRealGL) :
    (lineLevi I).α A = eichlerNormalTw n S.F A := by
  show eichlerCocycleTw I A = _
  rw [eichlerCocycleTw_eq_eichlerNormalTw I (continuousStages D) A, endpointScalar_eq hw hv]

theorem holomorphic_F (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) (x : BinaryAdelicGL) :
    DifferentiableOn ℂ (S.F x) {z : ℂ | 0 < z.im} := by
  rw [← endpointScalar_eq hw hv]
  exact cuspScalarWeightedRealization_holomorphic D.cusp I.halfWeight I.vector I.vector_spherical
    I.rotation I.holomorphic x

end SphericalEntryData

/-- **The good-line component of the bad-plane comparison for the actual Eichler Levi data.**  `S` is the finite
spherical datum of the cusp form, `I` the Eichler input of the same weight and vector.  Any `T` realizing the standard
operator sends the class of `badPlaneWeight · planeSource D (planeLevi I)` to a class whose good-line component is
`entryScalar n S.rBad = -S.printedScalar` times that of `goodLineWeight · lineSource D (lineLevi I)`. -/
theorem classLevel_badPlane_eichler (n : ℕ) (D : InducingData n) (S : SphericalEntryData D)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T) :
    entryScalar n S.rBad ≠ 0 ∧ entryScalar n S.rBad = -S.printedScalar ∧
      ∀ (hps : IsSourceCocycle D .plane
          (fun y g => badPlaneWeight g • planeSource D (SphericalEntryData.planeLevi I) y g))
        (hls : IsSourceCocycle D .line
          (fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi I) y g)),
        goodComponent n D.chi .line
            (T (SourceQuotient.sourceToSummand D .plane
              ⟨fun y g => badPlaneWeight g • planeSource D (SphericalEntryData.planeLevi I) y g, hps⟩)).val =
          entryScalar n S.rBad • (SourceQuotient.sourceToSummand D .line
            ⟨fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi I) y g, hls⟩).val :=
  classLevel_badPlane n (by have := S.large; omega) D S (SphericalEntryData.planeLevi I) (SphericalEntryData.lineLevi I)
    (SphericalEntryData.planeLevi_alpha hw hv) (SphericalEntryData.lineLevi_alpha hw hv)
    (SphericalEntryData.holomorphic_F hw hv) T hT

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

