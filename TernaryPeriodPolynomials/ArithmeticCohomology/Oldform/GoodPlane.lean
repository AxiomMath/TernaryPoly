module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.ClassicalPair
public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneRealization

@[expose] public section


/-!
# The oldform classes at the good plane from the level-three period

For spherical `D` (trivial character) let `v` be the spherical holomorphic vector of weight
`-(n+3)` and `v' = cuspFiniteRationalSlash σ W v` its Atkin–Lehner translate; both are classical
level-three vectors (`exists_classicalOldformPair`).  Each classical level-three vector `w` has the
level-three Eichler datum `E_w` (`levelThreeEichlerData`), whose cocycle is
linear in `w` (`lteFamilyMap`), and the good-plane cell source `goodPlaneSource D E_w` depends on
the datum only through its cocycle, linearly (`goodPlaneSource_linear`).  Hence the good-plane
coordinate `w ↦ coord(goodPlaneSource D E_w)` is linear on the span of `v, v'`.  By CRL's detection
(`goodPlaneSource_sourceCoordinate_ne_zero`) it does not vanish at a nonzero `w` whose period class
is nonzero, which CRL's `LevelThreePeriodNonvanishing n` provides.  Since `v, v'` are independent
(`linearIndependent_atkinLehner`), the two coordinates are independent.

* `goodPlaneSource_linear`, `sourceCoordinate_goodPlaneSource_linear`;
* `coordinateLowerBound_goodPlane_two_of_spherical`: two summand classes with independent
  good-plane coordinates for spherical `D`;
* `levelThreeOldformClasses_goodPlane_of_period` (trivial character) and
  `levelThreeOldformClasses_goodPlane_of_period_all` (every character).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThreeSource
open TernaryPeriodPolynomials.MultiplicityOne
  (LevelThreeCusp levelThreeClassicalVectors atkinLehnerQ)

namespace TernaryPeriodPolynomials.Oldform

variable {n : ℕ}

/-- The linear algebra behind the linearity of the cell source in the Levi cocycle. -/
theorem cell_linear_aux {Q V W : Type*} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (R : V →ₗ[ℂ] W) (L : Q →ₗ[ℂ] V)
    (c s t : ℂ) (a₁ a₀ b₁ b₀ : Q) :
    R (L (c • ((s • a₁ + t • b₁) - (s • a₀ + t • b₀)))) =
      s • R (L (c • (a₁ - a₀))) + t • R (L (c • (b₁ - b₀))) := by
  have e : c • ((s • a₁ + t • b₁) - (s • a₀ + t • b₀)) =
      s • (c • (a₁ - a₀)) + t • (c • (b₁ - b₀)) := by module
  rw [e]
  simp only [map_add, map_smul]

/-- **The good-plane cell source is linear in the Levi cocycle.** -/
theorem goodPlaneSource_linear (D : InducingData n) (E E₁ E₂ : LevelLeviCocycleData D.cusp n)
    (s t : ℂ) (hα : E.α = s • E₁.α + t • E₂.α) :
    goodPlaneSource D E = s • goodPlaneSource D E₁ + t • goodPlaneSource D E₂ := by
  funext y g
  simp only [Pi.add_apply, Pi.smul_apply]
  unfold goodPlaneSource goodPlaneSourceAt
  rw [hα]
  simp only [Pi.add_apply, Pi.smul_apply]
  exact cell_linear_aux _ _ _ _ _ _ _ _ _

/-- The good-plane coordinate of the cell source is linear in the Levi cocycle. -/
theorem sourceCoordinate_goodPlaneSource_linear (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (E E₁ E₂ : LevelLeviCocycleData D.cusp n) (s t : ℂ)
    (hα : E.α = s • E₁.α + t • E₂.α) :
    sourceCoordinate D .plane true
        ⟨goodPlaneSource D E, goodPlaneSource_isSourceCocycle_of_trivial D E hχ⟩ =
      s • sourceCoordinate D .plane true
          ⟨goodPlaneSource D E₁, goodPlaneSource_isSourceCocycle_of_trivial D E₁ hχ⟩ +
        t • sourceCoordinate D .plane true
          ⟨goodPlaneSource D E₂, goodPlaneSource_isSourceCocycle_of_trivial D E₂ hχ⟩ := by
  have hc : (⟨goodPlaneSource D E, goodPlaneSource_isSourceCocycle_of_trivial D E hχ⟩ :
      sourceCocycles D .plane) =
      s • ⟨goodPlaneSource D E₁, goodPlaneSource_isSourceCocycle_of_trivial D E₁ hχ⟩ +
        t • ⟨goodPlaneSource D E₂, goodPlaneSource_isSourceCocycle_of_trivial D E₂ hχ⟩ :=
    Subtype.ext (goodPlaneSource_linear D E E₁ E₂ s t hα)
  rw [hc, map_add, map_smul, map_smul]

/-- **Two good-plane classes for spherical `D`.**  For the trivial character and spherical
`D.cusp`, the cell sources of the spherical vector and of its Atkin–Lehner translate have
linearly independent good-plane coordinates, given the level-three period nonvanishing. -/
theorem coordinateLowerBound_goodPlane_two_of_spherical (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hsph : SphericalCusp D.cusp)
    (hper : LevelThreePeriodNonvanishing n) : CoordinateLowerBound D .plane true 2 := by
  have hodd := odd_of_sphericalCusp hsph D.cohomological
  obtain ⟨halfWeight, hweight, -, v, hv, hw, hsv, hv0, -⟩ := exists_classicalOldformPair D hsph
  have hσ : LevelThreeCusp D.cusp := levelThreeCusp_of_classical hv hv0
  have hlin : ∀ (w w₁ w₂ : levelThreeClassicalVectors D.cusp halfWeight) (s t : ℂ),
      w = s • w₁ + t • w₂ →
      sourceCoordinate D .plane true
          ⟨goodPlaneSource D (levelThreeEichlerData D.cohomological hσ halfWeight hweight w.val
            w.property), goodPlaneSource_isSourceCocycle_of_trivial D _ hχ⟩ =
        s • sourceCoordinate D .plane true
            ⟨goodPlaneSource D (levelThreeEichlerData D.cohomological hσ halfWeight hweight
              w₁.val w₁.property), goodPlaneSource_isSourceCocycle_of_trivial D _ hχ⟩ +
          t • sourceCoordinate D .plane true
            ⟨goodPlaneSource D (levelThreeEichlerData D.cohomological hσ halfWeight hweight
              w₂.val w₂.property), goodPlaneSource_isSourceCocycle_of_trivial D _ hχ⟩ := by
    intro w w₁ w₂ s t hw'
    apply sourceCoordinate_goodPlaneSource_linear D hχ
    rw [levelThreeEichlerData_α_eq_family, levelThreeEichlerData_α_eq_family,
      levelThreeEichlerData_α_eq_family, hw', map_add, map_smul, map_smul]
  have hne : ∀ w : levelThreeClassicalVectors D.cusp halfWeight, w ≠ 0 →
      sourceCoordinate D .plane true
          ⟨goodPlaneSource D (levelThreeEichlerData D.cohomological hσ halfWeight hweight w.val
            w.property), goodPlaneSource_isSourceCocycle_of_trivial D _ hχ⟩ ≠ 0 := by
    intro w hw0
    have hw0' : w.val ≠ 0 := fun h => hw0 (Subtype.ext h)
    exact goodPlaneSource_sourceCoordinate_ne_zero D hχ hodd.pos _
      (hper D.cusp D.cohomological halfWeight hweight w.val w.property hw0')
  let w₁ : levelThreeClassicalVectors D.cusp halfWeight := ⟨v, hv⟩
  let w₂ : levelThreeClassicalVectors D.cusp halfWeight :=
    ⟨cuspFiniteRationalSlash D.cusp atkinLehnerQ v, hw⟩
  let c : levelThreeClassicalVectors D.cusp halfWeight → sourceCocycles D .plane := fun w =>
    ⟨goodPlaneSource D (levelThreeEichlerData D.cohomological hσ halfWeight hweight w.val
      w.property), goodPlaneSource_isSourceCocycle_of_trivial D _ hχ⟩
  refine coordinateLowerBound_of_sources D .plane true 2 ![c w₁, c w₂] ?_
  have hfun : (fun i => sourceCoordinate D .plane true (![c w₁, c w₂] i)) =
      ![sourceCoordinate D .plane true (c w₁), sourceCoordinate D .plane true (c w₂)] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun, LinearIndependent.pair_iff]
  intro s t hst
  by_contra hnot
  have hpair : s • w₁ + t • w₂ ≠ 0 := by
    intro h0
    have hval : s • v + t • cuspFiniteRationalSlash D.cusp atkinLehnerQ v = 0 :=
      congrArg Subtype.val h0
    exact hnot ((LinearIndependent.pair_iff.mp
      (linearIndependent_atkinLehner D.cusp v hv0 hsv)) s t hval)
  exact hne _ hpair ((hlin _ w₁ w₂ s t rfl).trans hst)

/-- **The oldform classes at the good plane** (trivial character) from (R) and the level-three
period nonvanishing. -/
theorem levelThreeOldformClasses_goodPlane_of_period (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter)
    (hrank : LevelThreeRankTwoSpherical D hecke hhecke .plane true)
    (hper : LevelThreePeriodNonvanishing n) :
    LevelThreeOldformClasses D hecke hhecke .plane true := fun hne hfin h2 =>
  coordinateLowerBound_goodPlane_two_of_spherical D hχ (hrank hχ hne hfin h2) hper

/-- **The oldform classes at the good plane, every character**, from (R) and the level-three
period nonvanishing. -/
theorem levelThreeOldformClasses_goodPlane_of_period_all (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hrank : LevelThreeRankTwoSpherical D hecke hhecke .plane true)
    (hper : LevelThreePeriodNonvanishing n) :
    LevelThreeOldformClasses D hecke hhecke .plane true := by
  by_cases hχ : D.chi = trivialCharacter
  · exact levelThreeOldformClasses_goodPlane_of_period D hecke hhecke hχ hrank hper
  · exact levelThreeOldformClasses_of_localJoint_eq_bot D hecke hhecke .plane true
      (fun hne => (levelThreeVanishing_of_nontrivial D hecke hhecke hχ hne).1)

end TernaryPeriodPolynomials.Oldform
