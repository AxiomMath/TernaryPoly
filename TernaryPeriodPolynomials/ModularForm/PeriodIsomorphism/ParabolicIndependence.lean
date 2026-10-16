module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.OtherTwistPeriods
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.ReflectionEigenvalue

@[expose] public section


/-!
# Corollary 1.4, even side, Step (d): independence of the two eigenspace pieces

`H_par := ker (beta n twist)` splits by the reflection `reflectionH1 n twist` into eigenspaces
`E_{+1}`/`E_{-1}`. This file shows the two intersections `H_par ⊓ E_{+1}` and `H_par ⊓ E_{-1}` are
independent subspaces of `H_par`: the eigenspaces themselves are disjoint (an eigenvector fixed by
`reflectionH1 n twist` and sent to its own negative must vanish, since `2` is invertible in `ℂ`),
so `finrank (H_par ⊓ E_{+1}) + finrank (H_par ⊓ E_{-1}) = finrank (H_par ⊓ E_{+1} ⊔ H_par ⊓ E_{-1})
≤ finrank H_par` (`Submodule.finrank_sup_add_finrank_inf_eq`, the inf part vanishing by
disjointness). Combined with Step (b)'s `finrank H_par ≤ 2d` and Step (c)'s
`d ≤ finrank (H_par ⊓ E_{-1})`, this gives `finrank (H_par ⊓ E_{+1}) ≤ d`.
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

/-- **Step (d), eigenspace independence.** The `+1` and `-1` eigenspaces of the reflection
involution on `H1 (modularBinaryRep n twist)` are disjoint: an element fixed by the reflection and
also sent to its own negative satisfies `x = -x`, hence `(2:ℂ) • x = 0`, hence (as `2 ≠ 0` in `ℂ`)
`x = 0`. -/
theorem reflectionH1_eigenspace_disjoint :
    Disjoint (Module.End.eigenspace (reflectionH1 n twist) (1 : ℂ))
      (Module.End.eigenspace (reflectionH1 n twist) (-1 : ℂ)) := by
  rw [Submodule.disjoint_def]
  intro x hx1 hx2
  rw [Module.End.mem_eigenspace_iff, one_smul] at hx1
  rw [Module.End.mem_eigenspace_iff, neg_one_smul] at hx2
  have heq : x = -x := hx1.symm.trans hx2
  have hzero : (2 : ℂ) • x = 0 := by
    rw [two_smul, congrArg (· + x) heq]
    exact neg_add_cancel x
  rcases smul_eq_zero.mp hzero with h2 | hx
  · exact absurd h2 (by norm_num)
  · exact hx

/-- **Step (d), arithmetic bound.** `finrank (ker (beta n twist) ⊓ eigenspace (reflectionH1 n
twist) 1) ≤ d`, for `n ≠ 0` even and `twist` even. -/
theorem finrank_ker_beta_inf_eigenspace_one_le (hn0 : n ≠ 0) (hn : Even n) (htwist : Even twist) :
    Module.finrank ℂ ↥(LinearMap.ker (beta n twist) ⊓
        Module.End.eigenspace (reflectionH1 n twist) (1 : ℂ)) ≤
      Module.finrank ℂ (CuspForm levelOne ((n : ℤ) + 2)) := by
  have hFD : FiniteDimensional ℂ (groupCohomology.H1 (modularBinaryRep n twist)) :=
    modularH1_finiteDimensional n twist
  set s := LinearMap.ker (beta n twist) ⊓ Module.End.eigenspace (reflectionH1 n twist) (1 : ℂ)
    with hs_def
  set t := LinearMap.ker (beta n twist) ⊓ Module.End.eigenspace (reflectionH1 n twist) (-1 : ℂ)
    with ht_def
  have hdisj : Disjoint s t := by
    rw [Submodule.disjoint_def]
    intro x hxs hxt
    exact (Submodule.disjoint_def.mp (reflectionH1_eigenspace_disjoint twist)) x hxs.2 hxt.2
  have hst := Submodule.finrank_sup_add_finrank_inf_eq s t
  rw [hdisj.eq_bot, finrank_bot, add_zero] at hst
  have hsup_le : s ⊔ t ≤ LinearMap.ker (beta n twist) := sup_le inf_le_left inf_le_left
  have hsuprank : Module.finrank ℂ ↥(s ⊔ t) ≤ Module.finrank ℂ ↥(LinearMap.ker (beta n twist)) :=
    Submodule.finrank_mono hsup_le
  have hb : Module.finrank ℂ ↥(LinearMap.ker (beta n twist)) ≤
      2 * Module.finrank ℂ (CuspForm levelOne ((n : ℤ) + 2)) :=
    finrank_ker_beta_le twist hn0 hn
  have hc : Module.finrank ℂ (CuspForm levelOne ((n : ℤ) + 2)) ≤ Module.finrank ℂ ↥t :=
    finrank_cuspForm_le_ker_beta_inf_eigenspace_neg_one twist hn htwist
  omega

end TernaryPeriodPolynomials.Argument.Corollary14
