module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.ParabolicDimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.BoundaryPeriod

@[expose] public section


/-!
# Corollary 1.4, even side, Step (c): other-twist cusp periods

The map `g := restriction (2r) (twist+1) twist ∘ₗ per r (twist+1) : CuspForm levelOne (-2 * hw r)
→ₗ[ℂ] H1 (modularBinaryRep (2r) twist)` is injective (`per_injective`/`restriction_injective`
composed), lands in `ker (beta (2r) twist)` (`beta_restriction_levelOnePeriodMap`, instantiated at
exactly `per`'s own defining arguments, which match by `abbrev`-unfolding), and — when `twist` is
even, so the source twist `twist+1` is odd — lands in the `(-1)`-eigenspace of
`reflectionH1 (2r) twist` (`reflectionH1_restriction` at source twist `twist+1`, combined with
`Odd.neg_one_zpow`). Hence its image is a subspace of
`ker (beta (2r) twist) ⊓ eigenspace (reflectionH1 (2r) twist) (-1)` of dimension
`d := finrank (CuspForm levelOne (2r+2))` (by injectivity), giving the Step (c) lower bound
`d ≤ finrank (ker (beta n twist) ⊓ eigenspace (reflectionH1 n twist) (-1))` for `n = 2r` even and
`twist` even.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Spectral.BoundaryFunctional
open TernaryPeriodPolynomials.Spectral.BoundaryPeriod
open TernaryPeriodPolynomials.Spectral.LevelOneHecke
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ} (twist : ℤ)

/-- **Step (c), other-twist map.** The source-twist-`(twist+1)` level-one period map, restricted
to `SL₂(ℤ)`-cohomology at target twist `twist`. -/
def otherTwistMap (r : ℕ) (twist : ℤ) :
    CuspForm levelOne (-2 * hw r) →ₗ[ℂ] groupCohomology.H1 (modularBinaryRep (2 * r) twist) :=
  restriction (2 * r) (twist + 1) twist ∘ₗ per r (twist + 1)

theorem otherTwistMap_apply (r : ℕ) (twist : ℤ) (f : CuspForm levelOne (-2 * hw r)) :
    otherTwistMap r twist f = restriction (2 * r) (twist + 1) twist (per r (twist + 1) f) := rfl

/-- **Step (c), injectivity.** -/
theorem otherTwistMap_injective (r : ℕ) (twist : ℤ) :
    Function.Injective (otherTwistMap r twist) :=
  (restriction_injective (2 * r) (twist + 1) twist).comp (per_injective r (twist + 1))

/-- **Step (c), lands in `ker (beta)`.** -/
theorem otherTwistMap_mem_ker_beta (r : ℕ) (twist : ℤ) (f : CuspForm levelOne (-2 * hw r)) :
    beta (2 * r) twist (otherTwistMap r twist f) = 0 := by
  rw [otherTwistMap_apply]
  exact beta_restriction_levelOnePeriodMap (2 * r) (twist + 1) twist (hw r) (weight_eq_r r)
    (even_two_mul r) (parityOf (twist + 1)) (parityOf_sign (twist + 1)) f

/-- **Step (c), lands in the `(-1)`-eigenspace of the reflection** (needs `twist` even, so that the
source twist `twist+1` is odd). -/
theorem otherTwistMap_mem_eigenspace_neg_one (r : ℕ) {twist : ℤ} (htwist : Even twist)
    (f : CuspForm levelOne (-2 * hw r)) :
    otherTwistMap r twist f ∈ Module.End.eigenspace (reflectionH1 (2 * r) twist) (-1 : ℂ) := by
  rw [Module.End.mem_eigenspace_iff, otherTwistMap_apply,
    reflectionH1_restriction (2 * r) (twist + 1) twist (per r (twist + 1) f),
    htwist.add_one.neg_one_zpow]

/-- **Step (c), other-twist bound.** For `n = 2r` even and `twist` even, `d := finrank (CuspForm
levelOne (n+2))` embeds into `ker (beta n twist) ⊓ eigenspace (reflectionH1 n twist) (-1)`. -/
theorem finrank_cuspForm_le_ker_beta_inf_eigenspace_neg_one
    (hn : Even n) (htwist : Even twist) :
    Module.finrank ℂ (CuspForm levelOne ((n : ℤ) + 2)) ≤
      Module.finrank ℂ
        ↥(LinearMap.ker (beta n twist) ⊓ Module.End.eigenspace (reflectionH1 n twist) (-1 : ℂ)) := by
  obtain ⟨r, hr⟩ := hn
  have hr2 : n = 2 * r := by omega
  subst hr2
  have hFD : FiniteDimensional ℂ (groupCohomology.H1 (modularBinaryRep (2 * r) twist)) :=
    modularH1_finiteDimensional (2 * r) twist
  have hle : LinearMap.range (otherTwistMap r twist) ≤
      LinearMap.ker (beta (2 * r) twist) ⊓
        Module.End.eigenspace (reflectionH1 (2 * r) twist) (-1 : ℂ) := by
    intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨f, rfl⟩ := hy
    exact Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr (otherTwistMap_mem_ker_beta r twist f),
      otherTwistMap_mem_eigenspace_neg_one r htwist f⟩
  have hmono := Submodule.finrank_mono hle
  rwa [LinearMap.finrank_range_of_inj (otherTwistMap_injective r twist),
    finrank_cuspForm_congr (weight_eq_r r)] at hmono

end TernaryPeriodPolynomials.Argument.Corollary14
