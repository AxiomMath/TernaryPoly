module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SupportSphericity.Helpers

@[expose] public section


/-!
# Source realization at the plane cusps: reduction to four named inputs

`SourceRealization D hecke hhecke .plane good` asks for a source cocycle with nonzero Shapiro
coordinate at the plane cusp `good` as soon as the local joint eigenspace of the pair character
there is nonzero.  Two facts organize the problem.

* The statement is false for the junk pair character that occurs when `associatePair D = ⊥`
  (`pairCharacter` is a `Classical.choose` of an unconstrained scalar), so every realization
  below is conditional on `associatePair D ≠ ⊥`; separation itself is trivial when
  `associatePair D = ⊥` (`eigenSeparated_of_eq_bot`).
* A source value at the identity-plane frame is a `GL₂(ℤ̂)`-fixed vector of `D.cusp`
  (`spherical_of_nonzero_at_identity`), so a non-spherical `D` has *no* identity-plane
  coordinate (`coordinateImage_plane_identity_eq_bot_of_not_spherical`).  Consequently, if the
  plane summand is nonzero, a non-spherical `D` has a nonzero coordinate at the good plane, with
  no construction and no strong multiplicity one needed
  (`coordinateImage_plane_true_ne_bot_of_nonspherical`).

Putting these together, the plane realizations follow from four precisely stated inputs:

* `PlaneSummandNonvanishing D` (N1): a nonzero associate pair has a nonzero plane summand;
* `SphericalGoodPlaneSource D` (N2) and `SphericalIdentityPlaneSource D` (N3): for a spherical
  `D` with nonzero plane summand, the plane summand has a nonzero coordinate at the good,
  respectively identity, plane cusp.  These are the *construction* inputs: the induction of the
  Eichler cocycle `D.cohomological` along the plane parabolic and the nonvanishing of the period
  class of its Shapiro coordinate (restriction of a level-one period class to `GL₂(ℤ)` and to
  `Γ₁'(3)`);
* `NonsphericalIdentityVanishing D hecke hhecke` (N4): for a non-spherical `D` with nonzero
  associate pair the identity-plane local joint eigenspace of the pair character is zero
  (strong multiplicity one for `GL₂`: the away-three eigensystem of `D` is not that of a
  level-one eigenform).

`sourceRealization_plane_true` needs only N1 and N2; `sourceRealization_plane_false` needs N1, N3
and N4.  N4 is necessary for the realization at the identity plane
(`nonsphericalIdentityVanishing_of_sourceRealization`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.BadPlaneSupportSphericity.Helpers

namespace TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-! ## The identity-plane cusp sees only spherical representations -/

/-- If `D.cusp` has no `GL₂(ℤ̂)`-fixed vector, every plane summand class has zero coordinate at
the identity-plane cusp. -/
theorem cuspRes_plane_identity_eq_zero_of_not_spherical (D : InducingData n)
    (hns : ¬ SphericalCusp D.cusp) {a : StratumH2 n D.chi .plane}
    (ha : a ∈ boundarySummand D .plane) : cuspRes n D.chi .plane false a = 0 := by
  have hle : boundarySummand D .plane ≤ LinearMap.ker (cuspRes n D.chi .plane false) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, hc, z, hz, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    refine cuspRes_classOf_eq_zero_of_vanish D .plane false hz 1 rfl ?_
    intro x
    by_contra hne
    have hpoly : ((c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
        (rationalGroup (1 : RationalGL3)⁻¹)).val) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨m, hm⟩ : ∃ m, (c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
          (rationalGroup (1 : RationalGL3)⁻¹)).val.coeff m ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hpoly (MvPolynomial.ext _ _ (by simpa using hall))
    apply hns
    refine spherical_of_nonzero_at_identity D
      (fun g => (c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) g).val.coeff m)
      (hc.1 _ m) ?_
    simpa using hm
  exact hle ha

/-- A non-spherical `D` has no identity-plane coordinate. -/
theorem coordinateImage_plane_identity_eq_bot_of_not_spherical (D : InducingData n)
    (hns : ¬ SphericalCusp D.cusp) : coordinateImage D .plane false = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨a, ha, rfl⟩
  rw [cuspRes_plane_identity_eq_zero_of_not_spherical D hns ha]
  exact Submodule.zero_mem _

/-- A nonzero identity-plane coordinate forces sphericity. -/
theorem sphericalCusp_of_coordinateImage_plane_identity_ne_bot (D : InducingData n)
    (h : coordinateImage D .plane false ≠ ⊥) : SphericalCusp D.cusp := by
  by_contra hns
  exact h (coordinateImage_plane_identity_eq_bot_of_not_spherical D hns)

/-! ## A nonzero plane summand has a nonzero coordinate at one of its two cusps -/

/-- If the plane summand is nonzero and the other plane cusp sees nothing, this one does. -/
theorem planeCoordinateImage_ne_bot_of_other_eq_bot (D : InducingData n) (good : Bool)
    (hne : boundarySummand D .plane ≠ ⊥) (hother : coordinateImage D .plane (!good) = ⊥) :
    coordinateImage D .plane good ≠ ⊥ := by
  intro hbot
  apply hne
  rw [eq_bot_iff]
  intro a ha
  rw [Submodule.mem_bot]
  have h1 : cuspRes n D.chi .plane good a = 0 := by
    have hmem : cuspRes n D.chi .plane good a ∈ coordinateImage D .plane good := ⟨a, ha, rfl⟩
    rwa [hbot, Submodule.mem_bot] at hmem
  have h2 : cuspRes n D.chi .plane (!good) a = 0 := by
    have hmem : cuspRes n D.chi .plane (!good) a ∈ coordinateImage D .plane (!good) :=
      ⟨a, ha, rfl⟩
    rwa [hother, Submodule.mem_bot] at hmem
  refine (eq_zero_iff_cuspRes .plane a).mpr ?_
  cases good
  · exact ⟨h2, h1⟩
  · exact ⟨h1, h2⟩

/-- The plane summand is nonzero iff one of its two cusp coordinate images is. -/
theorem boundarySummand_plane_ne_bot_iff (D : InducingData n) :
    boundarySummand D .plane ≠ ⊥ ↔
      coordinateImage D .plane true ≠ ⊥ ∨ coordinateImage D .plane false ≠ ⊥ := by
  constructor
  · intro h
    by_contra hall
    push Not at hall
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    apply ha0
    refine (eq_zero_iff_cuspRes .plane a).mpr ⟨?_, ?_⟩
    · have hmem : cuspRes n D.chi .plane true a ∈ coordinateImage D .plane true := ⟨a, ha, rfl⟩
      rwa [hall.1, Submodule.mem_bot] at hmem
    · have hmem : cuspRes n D.chi .plane false a ∈ coordinateImage D .plane false :=
        ⟨a, ha, rfl⟩
      rwa [hall.2, Submodule.mem_bot] at hmem
  · intro h hbot
    rcases h with h | h
    · apply h
      rw [eq_bot_iff]
      rintro _ ⟨a, ha, rfl⟩
      rw [hbot] at ha
      rw [(Submodule.mem_bot _).mp ha, map_zero]
      exact Submodule.zero_mem _
    · apply h
      rw [eq_bot_iff]
      rintro _ ⟨a, ha, rfl⟩
      rw [hbot] at ha
      rw [(Submodule.mem_bot _).mp ha, map_zero]
      exact Submodule.zero_mem _

/-- **Non-spherical `D` at the good plane (unconditional).**  If the plane summand is nonzero and
`D.cusp` has no `GL₂(ℤ̂)`-fixed vector, the plane summand has a nonzero coordinate at the good
plane cusp.  No source construction and no strong multiplicity one are needed. -/
theorem coordinateImage_plane_true_ne_bot_of_nonspherical (D : InducingData n)
    (hns : ¬ SphericalCusp D.cusp) (hS : boundarySummand D .plane ≠ ⊥) :
    coordinateImage D .plane true ≠ ⊥ :=
  planeCoordinateImage_ne_bot_of_other_eq_bot D true hS
    (coordinateImage_plane_identity_eq_bot_of_not_spherical D hns)

/-! ## The four inputs -/

/-- **(N1) Plane nonvanishing.**  A nonzero associate pair has a nonzero plane summand. -/
def PlaneSummandNonvanishing (D : InducingData n) : Prop :=
  associatePair D ≠ ⊥ → boundarySummand D .plane ≠ ⊥

/-- **(N2) Source construction at the good plane, spherical case.**  If `D.cusp` has a
`GL₂(ℤ̂)`-fixed vector and the plane summand is nonzero, some summand class has a nonzero
Shapiro coordinate at the good plane cusp. -/
def SphericalGoodPlaneSource (D : InducingData n) : Prop :=
  SphericalCusp D.cusp → boundarySummand D .plane ≠ ⊥ → coordinateImage D .plane true ≠ ⊥

/-- **(N3) Source construction at the identity plane.**  If `D.cusp` has a `GL₂(ℤ̂)`-fixed
vector and the plane summand is nonzero, some summand class has a nonzero Shapiro coordinate at
the identity-plane cusp. -/
def SphericalIdentityPlaneSource (D : InducingData n) : Prop :=
  SphericalCusp D.cusp → boundarySummand D .plane ≠ ⊥ → coordinateImage D .plane false ≠ ⊥

/-- **(N4) Strong multiplicity one at the identity plane.**  If the pair is nonzero and `D.cusp`
is not spherical, the identity-plane local joint eigenspace of the pair character is zero. -/
def NonsphericalIdentityVanishing (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) : Prop :=
  associatePair D ≠ ⊥ → ¬ SphericalCusp D.cusp →
    localJoint n D.chi (pairCharacter D hecke hhecke) .plane false = ⊥

/-! ## Realization at the plane cusps -/

/-- **Source realization at the good plane** from N1 and N2. -/
theorem sourceRealization_plane_true (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hN1 : PlaneSummandNonvanishing D) (hN2 : SphericalGoodPlaneSource D) :
    SourceRealization D hecke hhecke .plane true := fun _ => by
  have hS : boundarySummand D .plane ≠ ⊥ := hN1 hne
  refine (coordinateImage_ne_bot_iff D .plane true).mp ?_
  by_cases hsph : SphericalCusp D.cusp
  · exact hN2 hsph hS
  · exact coordinateImage_plane_true_ne_bot_of_nonspherical D hsph hS

/-- **Source realization at the identity plane** from N1, N3 and N4. -/
theorem sourceRealization_plane_false (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hN1 : PlaneSummandNonvanishing D) (hN3 : SphericalIdentityPlaneSource D)
    (hN4 : NonsphericalIdentityVanishing D hecke hhecke) :
    SourceRealization D hecke hhecke .plane false := fun hloc => by
  have hS : boundarySummand D .plane ≠ ⊥ := hN1 hne
  by_cases hsph : SphericalCusp D.cusp
  · exact (coordinateImage_ne_bot_iff D .plane false).mp (hN3 hsph hS)
  · exact absurd (hN4 hne hsph) hloc

/-- **Source realization at both plane cusps.** -/
theorem sourceRealization_plane (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hN1 : PlaneSummandNonvanishing D) (hN2 : SphericalGoodPlaneSource D)
    (hN3 : SphericalIdentityPlaneSource D)
    (hN4 : NonsphericalIdentityVanishing D hecke hhecke) (good : Bool) :
    SourceRealization D hecke hhecke .plane good := by
  cases good
  · exact sourceRealization_plane_false D hecke hhecke hne hN1 hN3 hN4
  · exact sourceRealization_plane_true D hecke hhecke hne hN1 hN2

/-- The realization statement relevant to separation: it is only asked for a nonzero pair. -/
def SourceRealizationNe (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  associatePair D ≠ ⊥ → SourceRealization D hecke hhecke side good

theorem sourceRealizationNe_plane (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hN1 : PlaneSummandNonvanishing D)
    (hN2 : SphericalGoodPlaneSource D) (hN3 : SphericalIdentityPlaneSource D)
    (hN4 : NonsphericalIdentityVanishing D hecke hhecke) (good : Bool) :
    SourceRealizationNe D hecke hhecke .plane good := fun hne =>
  sourceRealization_plane D hecke hhecke hne hN1 hN2 hN3 hN4 good

/-! ## Necessity of N4 -/

/-- N4 is necessary: it follows from the realization at the identity plane. -/
theorem nonsphericalIdentityVanishing_of_sourceRealization (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (h : SourceRealization D hecke hhecke .plane false) :
    NonsphericalIdentityVanishing D hecke hhecke := fun _ hns => by
  by_contra hne
  obtain ⟨c, hc⟩ := h hne
  apply hc
  have hmem : sourceClass D .plane c ∈ boundarySummand D .plane := by
    rw [← sourceClass_range]
    exact LinearMap.mem_range_self _ c
  exact cuspRes_plane_identity_eq_zero_of_not_spherical D hns hmem

end TernaryPeriodPolynomials.Separation
