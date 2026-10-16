module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Source
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SphericalBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelOneParity.Helpers

@[expose] public section


/-!
# The identity-plane coordinate of the plane source

For `χ = 1` and a spherical `D`, the plane source cocycle `planeSource D E` built from O(2)-normalized
Levi data `E` (`PlaneSourceFinal`) is an actual source cocycle, and its Shapiro coordinate at the
identity plane is nonzero as soon as the period class `[m ↦ E.α m 1]` in
`H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` is nonzero (`DetectSource`). This packages the two into the
construction inputs S1 (`SphericalSourceConstruction`) and N3 (`SphericalIdentityPlaneSource`) of the separation argument, conditional on the period nonvanishing (`PeriodNonvanishing`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)

namespace TernaryPeriodPolynomials.SourceConstruction

variable {n : ℕ}

theorem integral_character_trivial_of_eq (D : InducingData n) (hchi : D.chi = trivialCharacter) :
    ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1 := by
  intro u
  rw [hchi]
  rfl

/-- **The period input.** Some O(2)-normalized Levi data of `D` has nonzero period class. -/
def PeriodNonvanishing (D : InducingData n) : Prop :=
  ∃ (E : LeviCocycleData D.cusp n)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1))),
    (∀ m, cocyclePhi n φ m = E.α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1) ∧
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0

/-- With nonzero period class, the plane source has nonzero identity-plane coordinate. -/
theorem coordinateImage_plane_false_ne_bot_of_period (D : InducingData n)
    (hchi : D.chi = trivialCharacter) (pos : 0 < n) (odd : Odd n)
    (hP : PeriodNonvanishing D) : coordinateImage D .plane false ≠ ⊥ := by
  obtain ⟨E, φ, hφ, hφ0⟩ := hP
  let c : sourceCocycles D .plane :=
    ⟨planeSource D E, planeSource_isSourceCocycle D E (integral_character_trivial_of_eq D hchi)⟩
  refine (coordinateImage_ne_bot_iff D .plane false).mpr ⟨c, ?_⟩
  rw [sourceCoordinate_apply]
  exact planeSource_cuspRes_identity_ne_zero D E hchi pos odd φ hφ hφ0
    (evaluatedSource_realizes D .plane c)

/-- **S1 for `χ = 1`**, from the period input. -/
theorem sphericalSourceConstruction_of_period (D : InducingData n)
    (hchi : D.chi = trivialCharacter) (hP : SphericalCusp D.cusp → PeriodNonvanishing D) :
    SphericalSourceConstruction D := fun hsph => by
  have odd : Odd n :=
    TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers.cohomological_spherical_odd
      n D.cusp D.cohomological hsph
  have pos : 0 < n := odd.pos
  exact coordinateImage_plane_false_ne_bot_of_period D hchi pos odd (hP hsph)

/-- **N3 for `χ = 1`**, from the period input (the summand hypothesis is not needed). -/
theorem sphericalIdentityPlaneSource_of_period (D : InducingData n)
    (hchi : D.chi = trivialCharacter) (hP : SphericalCusp D.cusp → PeriodNonvanishing D) :
    SphericalIdentityPlaneSource D := fun hsph _ =>
  sphericalSourceConstruction_of_period D hchi hP hsph

end TernaryPeriodPolynomials.SourceConstruction
