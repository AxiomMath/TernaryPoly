module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.BadPlaneReflection

@[expose] public section


/-!
# Lemma C.3, last sentence, with the finite reflections: the bad plane with Levi `GL₂(ℤ)`

Paper: Lemma C.3 (`ar:lem:seed`).

At the identity (bad) plane of the library's level-three group, whose stabilizer is `Λ₀ = ℤ² ⋊ GL₂(ℤ)`
with the full Levi `GL₂(ℤ)` (determinant `-1` elements act antiholomorphically), and for odd
`n = 2k + 1` (trivial character):

* `badPlaneCuspidal n`: the literal mixed cuspidal group of `H¹(GL₂(ℤ), H¹(ℤ², E_n))`;
* `bad_plane_cuspidal_iff_binary`: it corresponds, under the coordinate isomorphism, to the classes of
  `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` restricting to zero at every rational cusp of `GL₂(ℤ)`;
* `cusp_GL_iff_odd_period_span`: those classes are exactly the classes whose `SL₂(ℤ)`-restriction is a
  combination of the odd period classes `[c_f] - [R c_f]` of level-one cusp forms;
* `bad_plane_cuspidal_iff_refl_seed_span`, `bad_plane_cuspidal_spanned_by_reflection_seeds`: a class of
  `H²(Λ₀, E_n)` has Hochschild--Serre edge in the mixed cuspidal group iff its restriction to
  `Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)` lies in the span of the reflection-invariant seeds `ω_f + \overline{ω_{f^*}}`;
  the restriction is injective and each reflection-invariant seed is the restriction of a class of
  `H²(Λ₀, E_n)`, so `𝒞_P(E)` is isomorphic to that span.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalReflection

open CategoryTheory
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The coordinate isomorphism identifies the literal mixed cuspidal group of the bad plane with the
cuspidal classes of `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`. -/
theorem bad_plane_cuspidal_iff_binary (n : ℕ) (x : groupCohomology.H1
    (splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRep n))) :
    x ∈ SeedC3S4c.badPlaneCuspidal n ↔
      ModuleCat.Hom.hom (identityPlaneLeviCohomologyIso n).hom x ∈
        SeedC3S4c.cuspidalFamily SeedC3S4c.cuspGL (arithmeticBinaryRep (n + 1) (-1)) :=
  SeedC3S4c.mem_badPlaneCuspidal_iff n x

/-- **Cuspidal classes of `GL₂(ℤ)` are spanned by the odd period classes** (`n` odd): a class of
`H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` restricts to zero at every rational cusp iff its restriction to
`SL₂(ℤ)` is a combination of the classes `[c_f] - [R c_f]` of level-one cusp forms of weight `n + 3`. -/
theorem cusp_GL_iff_odd_period_span (n : ℕ) (hev : Even (n + 1))
    (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2)
    (z : groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))) :
    z ∈ SeedC3S4c.cuspidalFamily SeedC3S4c.cuspGL (arithmeticBinaryRep (n + 1) (-1)) ↔
      TernaryPeriodPolynomials.Spectral.LevelOneESDimension.restriction (n + 1)
        (-1) (-1) z ∈ SeedC3S4c.oddPeriodSpan n hw :=
  SeedC3S4c.cuspGL_iff_oddPeriodSpan n hev hw z

/-- **Lemma C.3, last sentence, bad plane with finite reflections.** -/
theorem bad_plane_cuspidal_iff_refl_seed_span (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (x : groupCohomology.H2 (identityPlaneCoefficientRep n)) :
    splitCohomologyEdge identityPlaneSplitting (identityPlaneCoefficientRep n)
        (identityPlaneH2ToRestrictionKernel n hn hodd x) ∈ SeedC3S4c.badPlaneCuspidal n ↔
      SeedC3S4c.plusResH2 n x ∈ SeedC3S4c.reflSeedSpan n :=
  SeedC3S4c.badPlane_cuspidal_iff_reflSeedSpan n hn hodd x

/-- The restriction `H²(Λ₀, E_n) → H²(Λ₀⁺, E_n)` is injective in odd degree. -/
theorem plus_restriction_injective (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    Function.Injective (SeedC3S4c.plusResH2 n) :=
  SeedC3S4c.plusResH2_injective_of_odd n hn hodd

/-- **`𝒞_P(E)` of the bad plane is isomorphic to the span of the reflection-invariant seeds.** The
restriction to `Λ₀⁺` maps the classes with edge in `𝒞_P(E)` onto the span of the complexified de Rham
classes of the seeds `ω_f + \overline{ω_{f^*}}`, `f ∈ S_{2k+4}(SL₂(ℤ))`. -/
theorem bad_plane_cuspidal_spanned_by_reflection_seeds (k : ℕ) :
    Submodule.map (SeedC3S4c.plusResH2 (2 * k + 1))
        (SeedC3S4c.badPlaneCuspidalInH2 (2 * k + 1) (by omega) ⟨k, rfl⟩) =
      SeedC3S4c.reflSeedSpan (2 * k + 1) :=
  SeedC3S4c.map_plusResH2_badPlaneCuspidalInH2 k

/-- Finite-index descent along a homomorphism with finite-index range. -/
theorem cuspidal_descent_along_hom {L L' : Type} [Group L] [Group L'] {ι : Type}
    (B : ι → Subgroup L) (φ : L' →* L) [φ.range.FiniteIndex] (V : Rep ℂ L)
    (x : groupCohomology.H1 V) :
    x ∈ SeedC3S4c.cuspidalFamily B V ↔
      (groupCohomology.map φ (𝟙 (Rep.res φ V)) 1).hom x ∈
        SeedC3S4c.cuspidalFamily (fun i => (B i).comap φ) (Rep.res φ V) :=
  SeedC3S4c.mem_cuspidalFamily_iff_map B φ V x

end TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalReflection
