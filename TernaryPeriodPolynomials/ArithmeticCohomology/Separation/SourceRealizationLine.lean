module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceCoordinate

@[expose] public section


/-!
# Source realization at the line cusps: the exact input

`SourceRealization D hecke hhecke .line good` (see `SourceCoordinate`) asks that a nonzero local
joint generalized eigenspace of the pair character at the line cusp `(.line, good)` be hit by the
Shapiro coordinate of an actual smooth induced cohomological source cocycle.

The coordinate of a source at the line cusp only sees the values `c x (point)` of the source at the
adelic point `rationalGroup (q good)⁻¹`, where `q good` is the rational representative of the
reference line flag.  Each coefficient of such a value is a smooth section of the line
induced representation (`IsInduced`), so a source with nonzero coordinate at the cusp forces

  `LineCuspSection D good` : some induced section is nonzero at the cusp point.

This is proved below (`lineCuspSection_of_sourceCoordinate_ne_zero`, in both cases `good`), and
the converse direction is exactly the construction half.  Consequently `SourceRealization` at a
line cusp is equivalent to two statements which are *both necessary*:

* `LineSectionForcedByLocal`: a nonzero local joint eigenspace forces a nonzero induced section at
  the cusp point (strong multiplicity one: the abstract `D.cusp` has the local type of the
  classical eigenform);
* `LineSourceConstruction`: a nonzero induced section at the cusp point is the value of an actual
  source cocycle whose cohomology class has nonzero coordinate there (cup product of the
  cohomological Levi cocycle with the radical class, plus detection of the period class).

Everything else here is proved: the reduction `sourceRealization_line_of_inputs`, the
necessity theorems, the zero-coordinate criterion, and the support lemma for bad-line supported
sources.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit (referenceIntegral)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)

namespace TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-! ## The cusp point -/

/-- The rational representative of the reference flag of the line cusp `(.line, good)`:
the identity for the bad line and the reference integral frame for the good line. -/
def lineCuspElement : Bool → RationalGL3
  | true => rational referenceIntegral
  | false => 1

theorem mk_lineCuspElement (good : Bool) :
    (QuotientGroup.mk (lineCuspElement good) : Flags .line) = cuspFlag .line good := by
  cases good <;> rfl

theorem goodFlag_lineCuspElement_true :
    GoodFlag .line (QuotientGroup.mk (lineCuspElement true) : Flags .line) :=
  goodLineFrame_good

/-! ## The local type of `D` at a line cusp: a nonzero induced section at the cusp point -/

/-- **Local type at a line cusp.**  Some smooth normalized line-induced section is nonzero at the
cusp point `rationalGroup (lineCuspElement good)⁻¹`.  For the good line this is equivalent to the
`GL₂(ℤ̂)`-fixed vector condition `SphericalCusp D.cusp` (`SourceRealizationLineType`); for the bad
line it is the existence of a vector fixed by the Levi level `K₁'(3)`. -/
def LineCuspSection (D : InducingData n) (good : Bool) : Prop :=
  ∃ f : AdelicGL → ℂ, IsInduced D .line cohomologicalPoint f ∧
    f (rationalGroup (lineCuspElement good)⁻¹) ≠ 0

/-- **Support lemma.**  Without a nonzero induced section at the cusp point, every source has
zero coordinate at the line cusp. -/
theorem sourceCoordinate_eq_zero_of_not_lineCuspSection (D : InducingData n) (good : Bool)
    (hno : ¬ LineCuspSection D good) (c : sourceCocycles D .line) :
    sourceCoordinate D .line good c = 0 := by
  have hc : IsSourceCocycle D .line c.val := c.property
  have hz : Evaluates D .line c.val (evaluatedSource D .line c) :=
    evaluatedSource_realizes D .line c
  rw [sourceCoordinate_apply]
  change cuspRes n D.chi .line good (classOf rationalLevel
    (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
    (evaluatedSource D .line c)) = 0
  refine cuspRes_classOf_eq_zero_of_vanish D .line good hz (lineCuspElement good)
    (mk_lineCuspElement good) ?_
  intro x
  by_contra hne
  apply hno
  have hpoly : (c.val (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
      (rationalGroup (lineCuspElement good)⁻¹)).val ≠ 0 := fun h => hne (Subtype.ext h)
  obtain ⟨m, hm⟩ : ∃ m, (c.val (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
        (rationalGroup (lineCuspElement good)⁻¹)).val.coeff m ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hpoly (MvPolynomial.ext _ _ (by simpa using hall))
  exact ⟨fun g => (c.val (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) g).val.coeff m,
    hc.1 _ m, hm⟩

/-- **Necessity of the local type.**  A source with nonzero coordinate at a line cusp gives a
nonzero induced section at the cusp point. -/
theorem lineCuspSection_of_sourceCoordinate_ne_zero (D : InducingData n) (good : Bool)
    (c : sourceCocycles D .line) (h : sourceCoordinate D .line good c ≠ 0) :
    LineCuspSection D good :=
  Classical.byContradiction fun hno =>
    h (sourceCoordinate_eq_zero_of_not_lineCuspSection D good hno c)

theorem lineCuspSection_of_coordinateImage_ne_bot (D : InducingData n) (good : Bool)
    (h : coordinateImage D .line good ≠ ⊥) : LineCuspSection D good := by
  obtain ⟨c, hc⟩ := (coordinateImage_ne_bot_iff D .line good).mp h
  exact lineCuspSection_of_sourceCoordinate_ne_zero D good c hc

theorem coordinateImage_line_eq_bot_of_not_lineCuspSection (D : InducingData n) (good : Bool)
    (hno : ¬ LineCuspSection D good) : coordinateImage D .line good = ⊥ :=
  Classical.byContradiction fun h => hno (lineCuspSection_of_coordinateImage_ne_bot D good h)

/-! ## The two inputs and the reduction -/

/-- **Construction input.**  A nonzero induced section at the cusp point is the value of a source
cocycle whose class has nonzero Shapiro coordinate at the cusp.  This is the whole cohomological
construction: the cup product of the cohomological Levi cocycle of `D.cohomological` with the
radical class, induced to `GL₃` along the line parabolic, and the detection of its period class in
`H²(Γ_F, V)`. -/
def LineSourceConstruction (D : InducingData n) (good : Bool) : Prop :=
  LineCuspSection D good → ∃ c : sourceCocycles D .line, sourceCoordinate D .line good c ≠ 0

/-- **Matching input (strong multiplicity one).**  If the local joint generalized eigenspace of
the pair character at the line cusp is nonzero, `D` has the local type of the classical eigenform
there. -/
def LineSectionForcedByLocal (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (good : Bool) : Prop :=
  localJoint n D.chi (pairCharacter D hecke hhecke) .line good ≠ ⊥ → LineCuspSection D good

/-- **Reduction.**  Source realization at a line cusp follows from the matching input and the
construction input. -/
theorem sourceRealization_line_of_inputs (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (good : Bool)
    (hmatch : LineSectionForcedByLocal D hecke hhecke good)
    (hconstr : LineSourceConstruction D good) :
    SourceRealization D hecke hhecke .line good :=
  fun hne => hconstr (hmatch hne)

/-- The matching input is necessary for source realization. -/
theorem lineSectionForcedByLocal_of_sourceRealization (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (good : Bool)
    (hreal : SourceRealization D hecke hhecke .line good) :
    LineSectionForcedByLocal D hecke hhecke good := fun hne => by
  obtain ⟨c, hc⟩ := hreal hne
  exact lineCuspSection_of_sourceCoordinate_ne_zero D good c hc

/-- The construction input is necessary for source realization at a cusp with nonzero local
joint eigenspace. -/
theorem lineSourceConstruction_of_sourceRealization (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (good : Bool)
    (hne : localJoint n D.chi (pairCharacter D hecke hhecke) .line good ≠ ⊥)
    (hreal : SourceRealization D hecke hhecke .line good) :
    ∃ c : sourceCocycles D .line, sourceCoordinate D .line good c ≠ 0 :=
  hreal hne

/-- Given the construction input, source realization at a line cusp is exactly the matching
input: nothing else remains. -/
theorem sourceRealization_line_iff_of_construction (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (good : Bool)
    (hconstr : LineSourceConstruction D good) :
    SourceRealization D hecke hhecke .line good ↔ LineSectionForcedByLocal D hecke hhecke good :=
  ⟨lineSectionForcedByLocal_of_sourceRealization D hecke hhecke good,
    fun hmatch => sourceRealization_line_of_inputs D hecke hhecke good hmatch hconstr⟩

/-- The coordinate statement at a line cusp from local multiplicity one and the two inputs. -/
theorem coordinateStatement_line_of_inputs (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (good : Bool)
    (hloc : LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) .line good)
    (hmatch : LineSectionForcedByLocal D hecke hhecke good)
    (hconstr : LineSourceConstruction D good) :
    CoordinateStatement D hecke hhecke .line good :=
  coordinateStatement_of_realization D hecke hhecke .line good hloc
    (sourceRealization_line_of_inputs D hecke hhecke good hmatch hconstr)

/-- Global nonvanishing at a line cusp with cutoff, from the two inputs. -/
theorem globalNonvanishing_line_of_inputs (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (good : Bool)
    (hcut : HasCutoff D .line good)
    (hmatch : LineSectionForcedByLocal D hecke hhecke good)
    (hconstr : LineSourceConstruction D good) :
    GlobalNonvanishing D hecke hhecke .line good :=
  globalNonvanishing_of_realization D hecke hhecke .line good hcut
    (sourceRealization_line_of_inputs D hecke hhecke good hmatch hconstr)

/-! ## Several independent sources (the level-three line, where multiplicity is two) -/

/-- `m` source cocycles with linearly independent coordinates at the line cusp. -/
def LineSourceFamily (D : InducingData n) (good : Bool) (m : ℕ) : Prop :=
  ∃ c : Fin m → sourceCocycles D .line,
    LinearIndependent ℂ fun i => sourceCoordinate D .line good (c i)

theorem coordinateLowerBound_of_lineSourceFamily (D : InducingData n) (good : Bool) (m : ℕ)
    (h : LineSourceFamily D good m) : CoordinateLowerBound D .line good m := by
  obtain ⟨c, hc⟩ := h
  exact coordinateLowerBound_of_sources D .line good m c hc

theorem lineSourceFamily_one_iff (D : InducingData n) (good : Bool) :
    LineSourceFamily D good 1 ↔
      ∃ c : sourceCocycles D .line, sourceCoordinate D .line good c ≠ 0 := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c default, linearIndependent_unique_iff.mp hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨fun _ => c, linearIndependent_unique_iff.mpr hc⟩

theorem lineSourceFamily_zero (D : InducingData n) (good : Bool) : LineSourceFamily D good 0 :=
  ⟨Fin.elim0, linearIndependent_empty_type⟩

/-! ## Bad-line supported sources -/

/-- A source vanishing at the rational representative of every good line cusp has zero coordinate
at the good line. -/
theorem sourceCoordinate_line_true_eq_zero_of_vanishes (D : InducingData n)
    (c : sourceCocycles D .line)
    (hv : ∀ (x : Fin 3 → RealGL3) (q : RationalGL3),
      GoodFlag .line (QuotientGroup.mk q : Flags .line) → c.val x (rationalGroup q⁻¹) = 0) :
    sourceCoordinate D .line true c = 0 := by
  have hz : Evaluates D .line c.val (evaluatedSource D .line c) :=
    evaluatedSource_realizes D .line c
  rw [sourceCoordinate_apply]
  change cuspRes n D.chi .line true (classOf rationalLevel
    (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
    (evaluatedSource D .line c)) = 0
  exact cuspRes_classOf_eq_zero_of_vanish D .line true hz (lineCuspElement true)
    (mk_lineCuspElement true) fun x => hv _ _ goodFlag_lineCuspElement_true

/-- The class of a bad-line supported source is supported at the bad line: its bad-line
coordinate lies in the supported image, so no cutoff is needed for it. -/
theorem sourceCoordinate_line_false_mem_supportedImage (D : InducingData n)
    (c : sourceCocycles D .line)
    (hv : ∀ (x : Fin 3 → RealGL3) (q : RationalGL3),
      GoodFlag .line (QuotientGroup.mk q : Flags .line) → c.val x (rationalGroup q⁻¹) = 0) :
    sourceCoordinate D .line false c ∈ supportedImage D .line false := by
  have hmem : sourceClass D .line c ∈ boundarySummand D .line := by
    rw [← sourceClass_range]
    exact LinearMap.mem_range_self _ c
  exact mem_supportedImage D .line false hmem
    (sourceCoordinate_line_true_eq_zero_of_vanishes D c hv)

end TernaryPeriodPolynomials.Separation
