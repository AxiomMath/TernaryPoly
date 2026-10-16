module

public import TernaryPeriodPolynomials.EisensteinSeries.LevelOne.EisensteinScalar
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelOne

@[expose] public section


/-!
# Parabolic classes at level one are period classes

`parabolicH1_le_range_per`: every parabolic cohomology class of `H¹(GL₂(ℤ), Sym^{2r} ⊗ det^σ)` is a
level-one cusp-form period class, i.e. `parabolicH1 (arithmeticBinaryRep (2*r) σ) ≤
range (per r σ)`.

This is the *easy* half
(`parabolicH1 (arithmeticBinaryRep (2r) σ) = range (per r σ)` as full submodule equality): a
parabolic class has, by definition (`mem_parabolicH1_iff`), a representative cocycle whose value at
`T` is a coboundary; the boundary functional `betaGL` kills every `T`-coboundary value directly (by
`T`-invariance of `ell`, `ell_rho_T`), so `betaGL` vanishes on the whole class, and
`ker_betaGL_eq_range_per` identifies `ker (betaGL)` with `range (per)` exactly. The *converse*
inclusion (needed to get full equality, and relevant instead to the companion gap
`InnerPlaneEdgeParabolic`) is **not** proved here and is not needed below; it is substantially harder (it is equivalent, via `ker_betaGL_eq_range_per`, to an unformalized exact
computation of `ker (ellRep d τ - evaluated after ρ(T)) `, i.e. a one-dimensional-fixed-space /
single-Jordan-block fact about `ρ(T)` on `Binary.HomogeneousPoly d` that is not in the library).

Consequence for `OddCase.lean`'s `PlanePeriodParabolicRealized` (Gap 2, "cuspidal supply"):
`parabolicPeriodRealized_of_cuspFormRealized` below shows that it is equivalent to prove "every level-one cusp-form period class of weight `n + 3` is realized by a

plane summand of some `D : CohomologicalCuspData n` vanishing on the good planes" — rather than the a
priori more general "every parabolic class is realized".
-/

open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.BoundaryFunctional
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.LevelOneEisenstein
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne

/-- **Every parabolic class at level one is a cusp-form period class**. -/
theorem parabolicH1_le_range_per (r : ℕ) (positive : 0 < r) (σ : ℤ) :
    parabolicH1 (arithmeticBinaryRep (2 * r) σ) ≤ LinearMap.range (per r σ) := by
  rw [← ker_betaGL_eq_range_per r positive σ]
  intro c hc
  obtain ⟨x, ⟨u, hu⟩, hxc⟩ := (mem_parabolicH1_iff (arithmeticBinaryRep (2 * r) σ) c).mp hc
  have hu' : x (SpecialLinearGroup.toGL ModularGroup.T) =
      (arithmeticBinaryRep (2 * r) σ).ρ (SpecialLinearGroup.toGL ModularGroup.T) u - u := hu
  have hcompat :
      (arithmeticBinaryRep (2 * r) σ).ρ (SpecialLinearGroup.toGL ModularGroup.T) u =
        (modularBinaryRep (2 * r) σ).ρ ModularGroup.T u := rfl
  have key : betaGL (2 * r) σ (projectH1 (arithmeticBinaryRep (2 * r) σ) x) = 0 := by
    have step1 : betaGL (2 * r) σ (projectH1 (arithmeticBinaryRep (2 * r) σ) x) =
        beta (2 * r) σ (restriction (2 * r) σ σ
          (groupCohomology.H1π (arithmeticBinaryRep (2 * r) σ) x)) := by
      simp only [betaGL, projectH1, LinearMap.comp_apply]
    have step2 : (oneCocyclePullback (arithmeticBinaryRep (2 * r) σ) (modularBinaryRep (2 * r) σ)
          SpecialLinearGroup.toGL LinearMap.id (restriction_intertwines (2 * r) σ σ) x)
        ModularGroup.T = x (SpecialLinearGroup.toGL ModularGroup.T) :=
      oneCocyclePullback_apply _ _ _ _ _ x ModularGroup.T
    have hcoboundary :
        (oneCocyclePullback (arithmeticBinaryRep (2 * r) σ) (modularBinaryRep (2 * r) σ)
            SpecialLinearGroup.toGL LinearMap.id (restriction_intertwines (2 * r) σ σ) x)
          ModularGroup.T =
          (modularBinaryRep (2 * r) σ).ρ ModularGroup.T
              (show modularBinaryRep (2 * r) σ from u) -
            show modularBinaryRep (2 * r) σ from u := by
      rw [step2]; exact hu'
    rw [step1, restriction_apply, beta_H1π, hcoboundary]
    show ellRep (2 * r) σ
        ((modularBinaryRep (2 * r) σ).ρ ModularGroup.T
            (show modularBinaryRep (2 * r) σ from u) -
          show modularBinaryRep (2 * r) σ from u) = 0
    rw [map_sub, ell_rho_T, sub_self]
  rw [LinearMap.mem_ker, ← hxc]
  exact key

end TernaryPeriodPolynomials.Argument.CuspidalSpan
