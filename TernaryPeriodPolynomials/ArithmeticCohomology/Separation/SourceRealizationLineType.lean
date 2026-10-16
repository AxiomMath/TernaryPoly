module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SphericalBridge

@[expose] public section


/-!
# The local type at the line cusps, and the three-stage decomposition of source realization

`LineCuspSection D good` (a nonzero induced section at the cusp point) is, at each line cusp, a
statement about the cuspidal representation `D.cusp` alone:

* good line: `D.cusp` has a nonzero `GL₂(ℤ̂)`-fixed vector (`SphericalCusp`), proved from the
  section by `spherical_of_nonzero_at_goodLine`;
* bad line: `D.cusp` has a nonzero vector fixed by every `k ∈ GL₂(ℤ̂)` whose block-diagonal
  embedding `diag(1, k)` lies in the finite level (`BadLineLevelVector`: bottom row `≡ (0, 1)`
  modulo three), proved below by the same argument with the trivial frame.

Hence source realization at a line cusp decomposes into three statements, each necessary:
`(M)` a nonzero local joint eigenspace forces the local type of `D` (strong multiplicity one),
`(S)` the local type produces an induced section nonzero at the cusp point (archimedean and
adelic induction of a vector, no cohomology), `(C)` such a section is the value of a source
cocycle with nonzero coordinate (cohomological construction).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.BadPlaneSupportSphericity.Helpers
open TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance
  (combineGL_mul rationalGroup_eq atFinite_mul)

namespace TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-! ## The bad-line Levi level -/

/-- A nonzero smooth vector fixed by every `k ∈ GL₂(ℤ̂)` for which `diag(1, k)` lies in the
finite level group (bottom row of `k` congruent to `(0, 1)` modulo three). -/
def BadLineLevelVector (σ : CuspidalRepresentation) : Prop :=
  ∃ v : σ.smooth, v ≠ 0 ∧ ∀ k : GeneralLinearGroup (Fin 2) IntegralAdeles,
    GeneralLinearGroup.map integralEmbedding (lineLevi 1 k) ∈ finiteLevel →
      σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) v.val = v.val

/-- The local type of a cuspidal representation at the line cusp `(.line, good)`. -/
def LineLocalType (σ : CuspidalRepresentation) : Bool → Prop
  | true => SphericalCusp σ
  | false => BadLineLevelVector σ

/-- A section of the line induced representation that is nonzero at the identity gives a vector
fixed by the bad-line Levi level. -/
theorem badLineLevelVector_of_lineCuspSection {degree : ℕ} (data : InducingData degree)
    (h : LineCuspSection data false) : BadLineLevelVector data.cusp := by
  obtain ⟨function, induced, nonzero⟩ := h
  have hpoint : rationalGroup (lineCuspElement false)⁻¹ = 1 := by
    simp [lineCuspElement]
  rw [hpoint] at nonzero
  obtain ⟨vectors, _, lift⟩ := induced.2.2.1 (1 : AdelicGL)
  let vector : data.cusp.smooth := vectors (fun _ => 1)
  have realization (argument : BinaryAdelicGL) :
      data.cusp.realize vector argument =
        normPower (GeneralLinearGroup.det argument)
          (-binaryInductionExponent degree .line cohomologicalPoint) *
        function (lineLevi 1 argument) := by
    simpa [vector, binaryLevi, atInfinity_one] using lift (fun _ => 1) argument
  refine ⟨vector, ?_, ?_⟩
  · intro zero
    have at_one := realization 1
    have vector_zero : data.cusp.realize vector = 0 := by rw [zero, map_zero]
    rw [vector_zero] at at_one
    apply nonzero
    have levi_one : lineLevi 1 (1 : BinaryAdelicGL) = 1 := (lineLeviHom Adeles).map_one
    simpa [normPower, levi_one] using at_one.symm
  · intro k hk
    apply realize_fixed_of_positive_eigenvalue data.cusp vector
      (atFinite (GeneralLinearGroup.map integralEmbedding k))
      (Real.exp (-((degree : ℝ) + 1) / 2 * Real.log (adeleNorm (GeneralLinearGroup.det
        (atFinite (GeneralLinearGroup.map integralEmbedding k))) : ℝ)))
      (Real.exp_pos _)
    intro argument
    rw [realization, realization, map_mul, normPower_mul, ← normPower_line_real]
    have levi_mul : lineLevi 1 (argument * atFinite (GeneralLinearGroup.map integralEmbedding
        k)) = lineLevi 1 argument * lineLevi 1 (atFinite (GeneralLinearGroup.map
          integralEmbedding k)) := by
      simpa [lineLeviHom] using (lineLeviHom Adeles).map_mul (1, argument)
        (1, atFinite (GeneralLinearGroup.map integralEmbedding k))
    have hel : lineLevi 1 (atFinite (GeneralLinearGroup.map integralEmbedding k)) =
        atFinite (GeneralLinearGroup.map integralEmbedding (lineLevi 1 k)) := by
      rw [map_lineLevi_one, atFinite_lineLevi_one]
    have hmain : function (lineLevi 1 (argument * atFinite (GeneralLinearGroup.map
        integralEmbedding k))) = function (lineLevi 1 argument) := by
      rw [levi_mul, hel]
      exact induced.2.1 ⟨_, hk⟩ _
    rw [hmain]
    ring

/-- **Necessity of the local type.**  A nonzero induced section at the cusp point forces the local
type of the cuspidal representation. -/
theorem lineLocalType_of_lineCuspSection (D : InducingData n) (good : Bool)
    (h : LineCuspSection D good) : LineLocalType D.cusp good := by
  cases good
  · exact badLineLevelVector_of_lineCuspSection D h
  · obtain ⟨f, hf, hne⟩ := h
    exact spherical_of_nonzero_at_goodLine D f hf hne

theorem lineLocalType_of_sourceCoordinate_ne_zero (D : InducingData n) (good : Bool)
    (c : sourceCocycles D .line) (h : sourceCoordinate D .line good c ≠ 0) :
    LineLocalType D.cusp good :=
  lineLocalType_of_lineCuspSection D good (lineCuspSection_of_sourceCoordinate_ne_zero D good c h)

/-! ## The three stages -/

/-- **(M) Matching (strong multiplicity one).**  A nonzero local joint generalized eigenspace of
the pair character at the line cusp forces the local type of `D.cusp`: `GL₂(ℤ̂)`-fixed vector at
the good line, bad-line Levi-fixed vector at the bad line.  This is the statement that the
abstract cuspidal representation `D` has, away from three, the Hecke eigenvalues of the classical
eigenform of the cusp, hence is its adelic representation. -/
def LineLocalTypeForcedByLocal (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (good : Bool) : Prop :=
  localJoint n D.chi (pairCharacter D hecke hhecke) .line good ≠ ⊥ → LineLocalType D.cusp good

/-- **(S) Section construction.**  The local type of `D.cusp` produces a smooth line-induced
section nonzero at the cusp point (induction of a vector of `D.cusp` through the Iwasawa
decomposition, with the smooth Hilbert-valued cusp lift of `HasSmoothCuspLift`).  No cohomology
enters. -/
def LineSectionConstruction (D : InducingData n) (good : Bool) : Prop :=
  LineLocalType D.cusp good → LineCuspSection D good

/-- At the good line, (M) is exactly the bridge statement `SphericalForcedByLocalLine`. -/
theorem lineLocalTypeForcedByLocal_true_iff (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) :
    LineLocalTypeForcedByLocal D hecke hhecke true ↔ SphericalForcedByLocalLine D hecke hhecke :=
  Iff.rfl

/-- **Decomposition.**  Source realization at a line cusp follows from matching (M), section
construction (S) and source construction (C). -/
theorem sourceRealization_line_of_decomposition (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (good : Bool)
    (hM : LineLocalTypeForcedByLocal D hecke hhecke good)
    (hS : LineSectionConstruction D good) (hC : LineSourceConstruction D good) :
    SourceRealization D hecke hhecke .line good :=
  sourceRealization_line_of_inputs D hecke hhecke good (fun hne => hS (hM hne)) hC

/-- Matching (M) is necessary for source realization. -/
theorem lineLocalTypeForcedByLocal_of_sourceRealization (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (good : Bool)
    (hreal : SourceRealization D hecke hhecke .line good) :
    LineLocalTypeForcedByLocal D hecke hhecke good := fun hne => by
  obtain ⟨c, hc⟩ := hreal hne
  exact lineLocalType_of_sourceCoordinate_ne_zero D good c hc

/-- With section construction (S), the induced-section condition and the local type agree. -/
theorem lineCuspSection_iff_lineLocalType (D : InducingData n) (good : Bool)
    (hS : LineSectionConstruction D good) : LineCuspSection D good ↔ LineLocalType D.cusp good :=
  ⟨lineLocalType_of_lineCuspSection D good, hS⟩

/-- The coordinate statement at a line cusp from local multiplicity one and the three stages. -/
theorem coordinateStatement_line_of_decomposition (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (good : Bool)
    (hloc : LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) .line good)
    (hM : LineLocalTypeForcedByLocal D hecke hhecke good)
    (hS : LineSectionConstruction D good) (hC : LineSourceConstruction D good) :
    CoordinateStatement D hecke hhecke .line good :=
  coordinateStatement_of_realization D hecke hhecke .line good hloc
    (sourceRealization_line_of_decomposition D hecke hhecke good hM hS hC)

end TernaryPeriodPolynomials.Separation
