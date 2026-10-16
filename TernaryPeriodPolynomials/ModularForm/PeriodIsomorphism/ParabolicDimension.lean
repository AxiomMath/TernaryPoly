module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.ParabolicSubspace
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ParabolicES
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneESDimension

@[expose] public section


/-!
# Corollary 1.4, even side, Step (b): dim H_par ≤ 2d

`H_par n twist := LinearMap.ker (beta n twist)` is the parabolic subspace of Step (a)
(`ParabolicSubspace.lean`). This file shows, for `n ≠ 0` even,

  `finrank ℂ (LinearMap.ker (beta n twist)) ≤ 2 * finrank ℂ (CuspForm levelOne ((n:ℤ)+2))`.

Rank-nullity on `beta n twist : H1 (modularBinaryRep n twist) →ₗ[ℂ] ℂ`
(`LinearMap.finrank_range_add_finrank_ker`, using the `FiniteDimensional` instance from
`modularH1_finiteDimensional`) gives
`finrank (range (beta n twist)) + finrank H_par = finrank H1 (modularBinaryRep n twist)`.
Since `beta n twist ≠ 0` (`beta_ne_zero`), its range is a nonzero submodule of `ℂ`, hence contains
the span of a nonzero vector, so `finrank (range (beta n twist)) ≥ 1`
(`finrank_span_singleton`/`Submodule.finrank_mono`). And `finrank H1 (modularBinaryRep n twist) =
2d'+1` where `d' := finrank (CuspForm levelOne (-2 * hw r))` is `finrank_modularH1` (`n = 2r`), with
`d' = d` bridged by `finrank_cuspForm_congr`/`weight_eq_r`. Combining gives the bound.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Spectral.BoundaryFunctional
open TernaryPeriodPolynomials.Spectral.LevelOneHecke
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ} (twist : ℤ)

/-- **Step (b).** `finrank (ker (beta n twist)) ≤ 2 * finrank (CuspForm levelOne (n+2))`. -/
theorem finrank_ker_beta_le (hn0 : n ≠ 0) (hn : Even n) :
    Module.finrank ℂ (LinearMap.ker (beta n twist)) ≤
      2 * Module.finrank ℂ (CuspForm levelOne ((n : ℤ) + 2)) := by
  obtain ⟨r, hr⟩ := hn
  have hr2 : n = 2 * r := by omega
  subst hr2
  have hrpos : 0 < r := by omega
  have hbne : beta (2 * r) twist ≠ 0 := beta_ne_zero (2 * r) twist (by omega) (even_two_mul r)
  have hx : ∃ x, beta (2 * r) twist x ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hbne (LinearMap.ext hcon)
  obtain ⟨x, hx⟩ := hx
  have hmem : beta (2 * r) twist x ∈ LinearMap.range (beta (2 * r) twist) :=
    LinearMap.mem_range_self _ _
  have hspan_le : (ℂ ∙ beta (2 * r) twist x) ≤ LinearMap.range (beta (2 * r) twist) :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hmem
  have hrank1 : 1 ≤ Module.finrank ℂ (LinearMap.range (beta (2 * r) twist)) := by
    have hmono := Submodule.finrank_mono hspan_le
    rwa [finrank_span_singleton hx] at hmono
  have hFD : FiniteDimensional ℂ (groupCohomology.H1 (modularBinaryRep (2 * r) twist)) :=
    modularH1_finiteDimensional (2 * r) twist
  have hrn := LinearMap.finrank_range_add_finrank_ker (beta (2 * r) twist)
  have hdimH1 := finrank_modularH1 r hrpos twist
  have hweq := finrank_cuspForm_congr (weight_eq_r r)
  omega

end TernaryPeriodPolynomials.Argument.Corollary14
