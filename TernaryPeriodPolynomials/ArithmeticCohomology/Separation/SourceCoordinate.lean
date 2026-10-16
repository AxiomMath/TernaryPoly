module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Global
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Coordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SameConstituent.BoundarySupport
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CochainOperations
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.GoodFlags

@[expose] public section


/-!
# Cusp coordinates of source cocycles

The cusp coordinate of the boundary summand factors through the linear space of source cocycles
(`sourceClass`, whose range is the summand). E's coordinate statement and global nonvanishing reduce
to one construction input, `SourceRealization`: a nonzero local joint eigenspace at a cusp is hit by
the coordinate of an actual source cocycle. If the associate pair is nonzero, some cusp is realized.

Ported from AxiomCode (Claude Sonnet 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.SpectralSeparation

namespace TernaryPeriodPolynomials.Separation

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- Restriction of a maximal cycle to the flags satisfying a level-invariant predicate. -/
def cutCycle {χ : RankOneCharacter} {side : Side} (S : Flags side → Prop)
    (hS : ∀ (γ : rationalLevel) (F : Flags side), S (γ.val • F) ↔ S F)
    (z : MaximalCycles n χ side) : MaximalCycles n χ side :=
  ⟨⟨fun x F => if S F then z.val.val x F else 0, by
    intro γ x
    funext F
    have h := congrFun (z.val.property γ x) F
    change z.val.val (fun i => γ.val * x i) F =
      rationalCoefficientComponent n χ γ.val (z.val.val x (γ.val⁻¹ • F)) at h
    change (if S F then z.val.val (fun i => γ.val * x i) F else 0) =
      rationalCoefficientComponent n χ γ.val
        (if S (γ.val⁻¹ • F) then z.val.val x (γ.val⁻¹ • F) else 0)
    have hinv := hS γ⁻¹ F
    rw [Subgroup.coe_inv] at hinv
    rw [hinv]
    split_ifs
    · exact h
    · simp⟩, by
    have hz : differentialTwo rationalLevel
        (flagRepresentation (rationalCoefficientComponent n χ) side) z.val = 0 := z.property
    change differentialTwo rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) side) _ = 0
    funext x F
    have h := congrFun (congrFun hz x) F
    change z.val.val ![x 1, x 2, x 3] F - z.val.val ![x 0, x 2, x 3] F +
      z.val.val ![x 0, x 1, x 3] F - z.val.val ![x 0, x 1, x 2] F = 0 at h
    change (if S F then z.val.val ![x 1, x 2, x 3] F else 0) -
      (if S F then z.val.val ![x 0, x 2, x 3] F else 0) +
      (if S F then z.val.val ![x 0, x 1, x 3] F else 0) -
      (if S F then z.val.val ![x 0, x 1, x 2] F else 0) = 0
    split_ifs
    · exact h
    · simp⟩

/-! ## The source coordinate map

Every class of the summand is the class of an evaluated source cocycle
(`sourceClass_range`), and the assignment source ↦ class is linear.  Hence the Shapiro coordinate
image of the summand at a cusp is the range of one linear map out of the space of source cocycles,
and *every* coordinate statement is a statement about this map. -/

/-- Linear Shapiro coordinate at the cusp `(side, good)` of the class of a source cocycle. -/
def sourceCoordinate (D : InducingData n) (side : Side) (good : Bool) :
    sourceCocycles D side →ₗ[ℂ] CuspH2 n D.chi side good :=
  (cuspRes n D.chi side good).comp (sourceClass D side)

theorem sourceCoordinate_apply (D : InducingData n) (side : Side) (good : Bool)
    (c : sourceCocycles D side) :
    sourceCoordinate D side good c = cuspRes n D.chi side good (sourceClass D side c) := rfl

theorem range_sourceCoordinate (D : InducingData n) (side : Side) (good : Bool) :
    LinearMap.range (sourceCoordinate D side good) = coordinateImage D side good := by
  unfold sourceCoordinate coordinateImage
  rw [LinearMap.range_comp, sourceClass_range]

theorem mem_coordinateImage_iff (D : InducingData n) (side : Side) (good : Bool)
    (y : CuspH2 n D.chi side good) :
    y ∈ coordinateImage D side good ↔ ∃ c : sourceCocycles D side,
      sourceCoordinate D side good c = y := by
  rw [← range_sourceCoordinate]
  exact LinearMap.mem_range

theorem coordinateImage_ne_bot_iff (D : InducingData n) (side : Side) (good : Bool) :
    coordinateImage D side good ≠ ⊥ ↔ ∃ c : sourceCocycles D side,
      sourceCoordinate D side good c ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    apply h
    rw [← range_sourceCoordinate, LinearMap.range_eq_bot]
    exact LinearMap.ext hc
  · rintro ⟨c, hc⟩ h
    apply hc
    have : sourceCoordinate D side good c ∈ coordinateImage D side good :=
      (mem_coordinateImage_iff D side good _).mpr ⟨c, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact this

/-- The coordinate of a source cocycle is a local joint eigenclass of the pair character. -/
theorem sourceCoordinate_mem_localJoint (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (c : sourceCocycles D side) :
    sourceCoordinate D side good c ∈
      localJoint n D.chi (pairCharacter D hecke hhecke) side good := by
  have hmem : sourceClass D side c ∈ boundarySummand D side := by
    rw [← sourceClass_range]
    exact LinearMap.mem_range_self _ c
  exact cuspRes_mem_localJoint_of_mem D hecke hhecke side good hmem

/-- The coordinate statement, phrased through source cocycles. -/
theorem coordinateStatement_iff (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) :
    CoordinateStatement D hecke hhecke side good ↔
      ∀ y ∈ localJoint n D.chi (pairCharacter D hecke hhecke) side good,
        ∃ c : sourceCocycles D side, sourceCoordinate D side good c = y := by
  constructor
  · intro h y hy
    exact (mem_coordinateImage_iff D side good y).mp (h hy)
  · intro h y hy
    exact (mem_coordinateImage_iff D side good y).mpr (h y hy)

/-- `m` source cocycles with linearly independent coordinates give the coordinate lower bound. -/
theorem coordinateLowerBound_of_sources (D : InducingData n) (side : Side) (good : Bool)
    (m : ℕ) (c : Fin m → sourceCocycles D side)
    (h : LinearIndependent ℂ fun i => sourceCoordinate D side good (c i)) :
    CoordinateLowerBound D side good m :=
  ⟨fun i => sourceCoordinate D side good (c i),
    fun i => (mem_coordinateImage_iff D side good _).mpr ⟨c i, rfl⟩, h⟩

/-! ## Realization of local eigenclasses by source cocycles -/

/-- **Source realization at a cusp (the single construction input).**  If the local joint
generalized eigenspace of the pair character is nonzero, some source cocycle has nonzero class
coordinate at the cusp.  This is the only statement requiring the construction of smooth induced
cohomological cocycles from `D.cohomological`. -/
def SourceRealization (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  localJoint n D.chi (pairCharacter D hecke hhecke) side good ≠ ⊥ →
    ∃ c : sourceCocycles D side, sourceCoordinate D side good c ≠ 0

theorem coordinateStatement_of_realization (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (side : Side) (good : Bool)
    (hloc : LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) side good)
    (hreal : SourceRealization D hecke hhecke side good) :
    CoordinateStatement D hecke hhecke side good :=
  coordinateStatement_of_multiplicityOne D hecke hhecke side good hloc fun hne =>
    (coordinateImage_ne_bot_iff D side good).mpr (hreal hne)

theorem globalNonvanishing_of_realization (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (side : Side) (good : Bool) (hcut : HasCutoff D side good)
    (hreal : SourceRealization D hecke hhecke side good) :
    GlobalNonvanishing D hecke hhecke side good := fun hne => by
  rw [← coordinateImage_eq_supportedImage D side good hcut]
  exact (coordinateImage_ne_bot_iff D side good).mpr (hreal hne)

/-! ## Some cusp is automatic -/

/-- A nonzero associate pair has a source cocycle with nonzero coordinate at some cusp. -/
theorem exists_sourceCoordinate_ne_zero (D : InducingData n) (hne : associatePair D ≠ ⊥) :
    ∃ side good, ∃ c : sourceCocycles D side, sourceCoordinate D side good c ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hne
  have hz : ∀ side, boundarySummand D side = ⊥ := by
    intro side
    rw [eq_bot_iff]
    intro a ha
    rw [← sourceClass_range D side] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [Submodule.mem_bot]
    exact (eq_zero_iff_cuspRes side _).mpr ⟨hall side true c, hall side false c⟩
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  rw [hz .plane] at ha
  rw [hz .line] at hb
  simp only [SetLike.mem_coe, Submodule.mem_bot] at ha hb ⊢
  exact Prod.ext ha hb

/-- For a nonzero associate pair there is a cusp at which the local joint eigenspace of the pair
character is nonzero and the source realization holds: the realization input is automatic at one
cusp, and what remains is the other cusps. -/
theorem exists_realized_cusp (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    ∃ side good,
      localJoint n D.chi (pairCharacter D hecke hhecke) side good ≠ ⊥ ∧
        ∃ c : sourceCocycles D side, sourceCoordinate D side good c ≠ 0 := by
  obtain ⟨side, good, c, hc⟩ := exists_sourceCoordinate_ne_zero D hne
  refine ⟨side, good, ?_, c, hc⟩
  intro hbot
  have := sourceCoordinate_mem_localJoint D hecke hhecke side good c
  rw [hbot, Submodule.mem_bot] at this
  exact hc this

/-- With local multiplicity one, the coordinate statement is automatic at the cusp provided by
`exists_realized_cusp`. -/
theorem exists_cusp_coordinateStatement (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hloc : ∀ side good,
      LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) side good) :
    ∃ side good,
      localJoint n D.chi (pairCharacter D hecke hhecke) side good ≠ ⊥ ∧
        CoordinateStatement D hecke hhecke side good := by
  obtain ⟨side, good, hj, hc⟩ := exists_realized_cusp D hecke hhecke hne
  exact ⟨side, good, hj,
    coordinateStatement_of_realization D hecke hhecke side good (hloc side good) fun _ => hc⟩

end TernaryPeriodPolynomials.Separation
