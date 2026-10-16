module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Coordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.CutoffPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.CutoffLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SphericalBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationLineType
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEven
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalLevelOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalUniqueness
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Necessity

@[expose] public section


/-!
# Assembly of eigencharacter separation from the inputs

The common input of the three targets `associate_projector_away_three_algebra`,
`cuspidal_associate_projector` and `cuspidal_finite_spectral_recovery` (degrees `3 ≤ n`) is
`EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D)`.
`eigenSeparated_of_openInputs` proves it from the mathematical inputs only; every
piece already proved in the project is discharged inside the proof:

* the zero pair is closed by `eigenSeparated_of_eq_bot`, so every input is only asked for a nonzero
  pair (the pair character is junk on a zero pair);
* the support condition at all four cusps is removed by the cutoff theorems
  `exists_cutoff_plane` and `exists_cutoff_line` (`hasCutoff`);
* local multiplicity one at the two level-one cusps (identity plane and good line) holds for the
  trivial character (`levelOneLocalMultiplicityOne_of_trivial`);
* for the trivial character and even `n` the level-one local joint eigenspaces vanish, so the
  level-one inputs are only needed when `D.chi ≠ trivialCharacter` or `n` is odd.

The inputs are, in the notation of the theorem:

* `hloc1` (only for a nontrivial character): level-one local multiplicity one,
  `LevelOneLocalMultiplicityOne`;
* `hS1`, `hS1L`: source construction at the identity plane and at the good line,
  `SphericalSourceConstruction`, `SphericalSourceConstructionLine`;
* `hS2`, `hS2L`: the prime-three input (strong multiplicity one), `SphericalForcedByLocal`,
  `SphericalForcedByLocalLine`;
* `hfin3p`, `hfin3l`: finiteness of the local joint eigenspace at the two level-three cusps (good
  plane and bad line), `LocalJointFinite`;
* `hrank3p`, `hrank3l`: the global lower bound at the two level-three cusps, `CoordinateRankLowerBound`
  (as many linearly independent source coordinates as the dimension of the local joint eigenspace).

All inputs carry the premise `associatePair D ≠ ⊥`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction

namespace TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-! ## The cutoff at all four cusps -/

/-- Every cusp of the associate pair admits the cutoff: plane by `exists_cutoff_plane`, line by
`exists_cutoff_line`. -/
theorem hasCutoff (D : InducingData n) (side : Side) (good : Bool) : HasCutoff D side good := by
  cases side
  · intro a ha
    exact exists_cutoff_plane D good ha
  · intro a ha
    exact exists_cutoff_line D good ha

/-! ## Local multiplicity one at the level-one cusps -/

/-- Local multiplicity one of the pair character at the identity plane and at the good line, for a
nonzero pair. -/
def LevelOneLocalMultiplicityOne (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) : Prop :=
  associatePair D ≠ ⊥ →
    LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) .plane false ∧
      LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) .line true

/-- For the trivial character and `3 ≤ n` the pair character is within `3/4` of `1` at `T_2`. -/
theorem pairCharacter_two_sub_one_norm_le_of_trivial (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hn : 3 ≤ n) (hne : associatePair D ≠ ⊥) :
    ‖pairCharacter D hecke hhecke (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4 := by
  obtain ⟨cusp, chi, coh⟩ := D
  change chi = trivialCharacter at hχ
  subst hχ
  exact LocalUniqueness.pairCharacter_two_sub_one_norm_le (⟨cusp, coh⟩ : CohomologicalCuspData n)
    hecke hhecke hn hne

/-- **Level-one local multiplicity one for the trivial character**. -/
theorem levelOneLocalMultiplicityOne_of_trivial (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hn : 3 ≤ n) :
    LevelOneLocalMultiplicityOne D hecke hhecke := by
  intro hne
  have hc := pairCharacter_two_sub_one_norm_le_of_trivial D hχ hecke hhecke hn hne
  exact ⟨LocalLevelOne.identityPlane_localMultiplicityOne D.chi hχ (by omega) _ hc,
    LocalLevelOne.goodLine_localMultiplicityOne D.chi hχ (by omega) _ hc⟩

/-- For the trivial character and even `n` the identity-plane local joint eigenspace vanishes. -/
theorem localJoint_plane_false_eq_bot_of_even (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hn : 0 < n) (heven : Even n) :
    localJoint n D.chi (pairCharacter D hecke hhecke) .plane false = ⊥ := by
  obtain ⟨cusp, chi, coh⟩ := D
  change chi = trivialCharacter at hχ
  subst hχ
  exact IdentityPlaneEven.localJoint_identityPlane_eq_bot n hn heven _

/-- For the trivial character, even `n ≥ 3` and a nonzero pair the good-line local joint
eigenspace vanishes. -/
theorem localJoint_line_true_eq_bot_of_even (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hn : 3 ≤ n) (heven : Even n)
    (hne : associatePair D ≠ ⊥) :
    localJoint n D.chi (pairCharacter D hecke hhecke) .line true = ⊥ := by
  obtain ⟨cusp, chi, coh⟩ := D
  change chi = trivialCharacter at hχ
  subst hχ
  exact LocalUniqueness.localJoint_goodLine_eq_bot_of_even _ (by omega) heven
    (LocalUniqueness.pairCharacter_two_sub_one_norm_le (⟨cusp, coh⟩ : CohomologicalCuspData n)
      hecke hhecke hn hne)

/-! ## The coordinate statements at the level-one cusps -/

/-- **Coordinate statement at the identity plane** from local multiplicity one and the two bridge
statements, the latter only when the local joint eigenspace can be nonzero. -/
theorem coordinateStatement_plane_false (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hn : 3 ≤ n) (hne : associatePair D ≠ ⊥)
    (hloc1 : D.chi ≠ trivialCharacter → LevelOneLocalMultiplicityOne D hecke hhecke)
    (hS1 : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalSourceConstruction D)
    (hS2 : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalForcedByLocal D hecke hhecke) :
    CoordinateStatement D hecke hhecke .plane false := by
  by_cases hev : D.chi = trivialCharacter ∧ Even n
  · unfold CoordinateStatement
    rw [localJoint_plane_false_eq_bot_of_even D hev.1 hecke hhecke (by omega) hev.2]
    exact bot_le
  · have hcase : D.chi ≠ trivialCharacter ∨ Odd n := by
      by_cases hχ : D.chi = trivialCharacter
      · exact Or.inr ((Nat.even_or_odd n).resolve_left fun h => hev ⟨hχ, h⟩)
      · exact Or.inl hχ
    have hlmo : LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) .plane false := by
      by_cases hχ : D.chi = trivialCharacter
      · exact (levelOneLocalMultiplicityOne_of_trivial D hχ hecke hhecke hn hne).1
      · exact (hloc1 hχ hne).1
    exact coordinateStatement_of_sphericalBridge D hecke hhecke hlmo (hS1 hcase hne)
      (hS2 hcase hne)

/-- **Coordinate statement at the good line** from local multiplicity one and the two bridge
statements, the latter only when the local joint eigenspace can be nonzero. -/
theorem coordinateStatement_line_true (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hn : 3 ≤ n) (hne : associatePair D ≠ ⊥)
    (hloc1 : D.chi ≠ trivialCharacter → LevelOneLocalMultiplicityOne D hecke hhecke)
    (hS1L : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalSourceConstructionLine D)
    (hS2L : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalForcedByLocalLine D hecke hhecke) :
    CoordinateStatement D hecke hhecke .line true := by
  by_cases hev : D.chi = trivialCharacter ∧ Even n
  · unfold CoordinateStatement
    rw [localJoint_line_true_eq_bot_of_even D hev.1 hecke hhecke hn hev.2 hne]
    exact bot_le
  · have hcase : D.chi ≠ trivialCharacter ∨ Odd n := by
      by_cases hχ : D.chi = trivialCharacter
      · exact Or.inr ((Nat.even_or_odd n).resolve_left fun h => hev ⟨hχ, h⟩)
      · exact Or.inl hχ
    have hlmo : LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) .line true := by
      by_cases hχ : D.chi = trivialCharacter
      · exact (levelOneLocalMultiplicityOne_of_trivial D hχ hecke hhecke hn hne).2
      · exact (hloc1 hχ hne).2
    exact coordinateStatement_of_sphericalBridge_line D hecke hhecke hlmo (hS1L hcase hne)
      (hS2L hcase hne)

/-! ## The level-three cusps: finiteness and a global lower bound -/

/-- **Local finiteness** at a cusp: for a nonzero pair the local joint generalized eigenspace of the
pair character is finite-dimensional, with some bound `m`. -/
def LocalJointFinite (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  associatePair D ≠ ⊥ →
    ∃ m : ℕ, LocalUpperBound n D.chi (pairCharacter D hecke hhecke) side good m

/-- **Global lower bound** at a cusp: for a nonzero pair, if the local joint generalized eigenspace
of the pair character is finite-dimensional, there are as many linearly independent Shapiro
coordinates of summand classes as its dimension. -/
def CoordinateRankLowerBound (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  associatePair D ≠ ⊥ →
    FiniteDimensional ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) →
      CoordinateLowerBound D side good
        (Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good))

/-- Local finiteness and the global lower bound give the coordinate statement. -/
theorem coordinateStatement_of_finite_rank (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hne : associatePair D ≠ ⊥) (hfin : LocalJointFinite D hecke hhecke side good)
    (hrank : CoordinateRankLowerBound D hecke hhecke side good) :
    CoordinateStatement D hecke hhecke side good := by
  obtain ⟨_, hfd, -⟩ := hfin hne
  exact coordinateStatement_of_bounds D hecke hhecke side good _ ⟨hfd, le_rfl⟩
    (hrank hne hfd) (hasCutoff D side good)

theorem coordinateImage_le_localJoint (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) :
    coordinateImage D side good ≤
      localJoint n D.chi (pairCharacter D hecke hhecke) side good := by
  rintro _ ⟨a, ha, rfl⟩
  exact cuspRes_mem_localJoint_of_mem D hecke hhecke side good ha

/-- The global lower bound is necessary for the coordinate statement: it is not stronger than the
coordinate statement once the local joint eigenspace is finite-dimensional. -/
theorem coordinateRankLowerBound_of_coordinateStatement (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side)
    (good : Bool) (h : CoordinateStatement D hecke hhecke side good) :
    CoordinateRankLowerBound D hecke hhecke side good := by
  intro _ hfin
  have heq : coordinateImage D side good =
      localJoint n D.chi (pairCharacter D hecke hhecke) side good :=
    le_antisymm (coordinateImage_le_localJoint D hecke hhecke side good) h
  let b := Module.finBasis ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good)
  refine ⟨fun i => ((b i : localJoint n D.chi (pairCharacter D hecke hhecke) side good) :
    CuspH2 n D.chi side good), fun i => ?_, ?_⟩
  · rw [heq]
    exact (b i).2
  · exact b.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)

/-! ## The assembly -/

/-- **Separation from the coordinate statements at the level-three cusps** (coarse form of
`eigenSeparated_of_openInputs`): the good plane and the bad line enter through their coordinate
statements, for a nonzero pair. -/
theorem eigenSeparated_of_levelThreeCoordinate (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hloc1 : D.chi ≠ trivialCharacter → LevelOneLocalMultiplicityOne D hecke hhecke)
    (hS1 : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalSourceConstruction D)
    (hS1L : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalSourceConstructionLine D)
    (hS2 : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalForcedByLocal D hecke hhecke)
    (hS2L : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalForcedByLocalLine D hecke hhecke)
    (h3p : associatePair D ≠ ⊥ → CoordinateStatement D hecke hhecke .plane true)
    (h3l : associatePair D ≠ ⊥ → CoordinateStatement D hecke hhecke .line false) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) := by
  by_cases hbot : associatePair D = ⊥
  · exact eigenSeparated_of_eq_bot D hecke hbot
  refine eigenSeparated_of_coordinateStatements D hecke hhecke (hasCutoff D) ?_
  intro side good
  match side, good with
  | .plane, false => exact coordinateStatement_plane_false D hecke hhecke hn hbot hloc1 hS1 hS2
  | .plane, true => exact h3p hbot
  | .line, false => exact h3l hbot
  | .line, true => exact coordinateStatement_line_true D hecke hhecke hn hbot hloc1 hS1L hS2L

/-- **Eigencharacter separation of the associate pair for `3 ≤ n`, from the inputs.**

All inputs concern a nonzero associate pair.  See the module documentation for the meaning of each:
`hloc1` (level-one local multiplicity one, needed only for a nontrivial character), `hS1`/`hS1L`
(source construction at the identity plane and the good line), `hS2`/`hS2L` (the prime-three
input, strong multiplicity one), `hfin3p`/`hfin3l` (local finiteness at the good plane and the bad
line) and `hrank3p`/`hrank3l` (the global lower bound there). -/
theorem eigenSeparated_of_openInputs (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hloc1 : D.chi ≠ trivialCharacter → LevelOneLocalMultiplicityOne D hecke hhecke)
    (hS1 : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalSourceConstruction D)
    (hS1L : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalSourceConstructionLine D)
    (hS2 : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalForcedByLocal D hecke hhecke)
    (hS2L : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalForcedByLocalLine D hecke hhecke)
    (hfin3p : LocalJointFinite D hecke hhecke .plane true)
    (hfin3l : LocalJointFinite D hecke hhecke .line false)
    (hrank3p : CoordinateRankLowerBound D hecke hhecke .plane true)
    (hrank3l : CoordinateRankLowerBound D hecke hhecke .line false) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) :=
  eigenSeparated_of_levelThreeCoordinate hn D hecke hhecke hloc1 hS1 hS1L hS2 hS2L
    (fun hne => coordinateStatement_of_finite_rank D hecke hhecke .plane true hne hfin3p hrank3p)
    (fun hne => coordinateStatement_of_finite_rank D hecke hhecke .line false hne hfin3l hrank3l)

/-- The same for the trivial character: the level-one local multiplicity input is discharged. -/
theorem eigenSeparated_of_openInputs_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hS1 : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalSourceConstruction D)
    (hS1L : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalSourceConstructionLine D)
    (hS2 : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalForcedByLocal D hecke hhecke)
    (hS2L : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalForcedByLocalLine D hecke hhecke)
    (hfin3p : LocalJointFinite D hecke hhecke .plane true)
    (hfin3l : LocalJointFinite D hecke hhecke .line false)
    (hrank3p : CoordinateRankLowerBound D hecke hhecke .plane true)
    (hrank3l : CoordinateRankLowerBound D hecke hhecke .line false) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) :=
  eigenSeparated_of_openInputs hn D hecke hhecke (fun h => absurd hχ h) hS1 hS1L hS2 hS2L
    hfin3p hfin3l hrank3p hrank3l

/-! ## Finer forms of the bridge inputs -/

/-- Identity-plane source construction from plane-summand nonvanishing (N1) and the spherical
identity-plane source (N3). -/
theorem sphericalSourceConstruction_of_planeInputs (D : InducingData n)
    (hN1 : PlaneSummandNonvanishing D) (hN3 : SphericalIdentityPlaneSource D) :
    associatePair D ≠ ⊥ → SphericalSourceConstruction D :=
  fun hne hsph => hN3 hsph (hN1 hne)

/-- The prime-three input at the identity plane from strong multiplicity one for a non-spherical
`D` (N4). -/
theorem sphericalForcedByLocal_of_nonsphericalIdentityVanishing (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hN4 : NonsphericalIdentityVanishing D hecke hhecke) :
    associatePair D ≠ ⊥ → SphericalForcedByLocal D hecke hhecke :=
  fun hne hloc => Classical.byContradiction fun hns => hloc (hN4 hne hns)

/-- Good-line source construction from the section construction (no cohomology) and the source
construction (cohomological). -/
theorem sphericalSourceConstructionLine_of_decomposition (D : InducingData n)
    (hS : LineSectionConstruction D true) (hC : LineSourceConstruction D true) :
    SphericalSourceConstructionLine D :=
  fun hsph => (coordinateImage_ne_bot_iff D .line true).mpr (hC (hS hsph))

end TernaryPeriodPolynomials.Separation
