module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NLinear
public import TernaryPeriodPolynomials.EisensteinSeries.Class.SeedLinear

@[expose] public section


open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ)

theorem faceSeedKerClass_add (h : SL(3, ℤ)) (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    faceSeedKerClass N h n (f + g) = faceSeedKerClass N h n f + faceSeedKerClass N h n g := by
  unfold faceSeedKerClass
  rw [gammaNSeedKerClass_add, map_add]

theorem faceSeedKerClass_smul (h : SL(3, ℤ)) (c : ℂ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    faceSeedKerClass N h n (c • f) = c • faceSeedKerClass N h n f := by
  unfold faceSeedKerClass
  rw [gammaNSeedKerClass_smul, map_smul]

theorem faceSeedConjKerClass_add (h : SL(3, ℤ)) (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    faceSeedConjKerClass N h n (f + g) = faceSeedConjKerClass N h n f + faceSeedConjKerClass N h n g := by
  unfold faceSeedConjKerClass
  rw [gammaNSeedConjKerClass_add, map_add]

theorem faceSeedConjKerClass_smul (h : SL(3, ℤ)) (c : ℂ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    faceSeedConjKerClass N h n (c • f) = (starRingEnd ℂ c) • faceSeedConjKerClass N h n f := by
  unfold faceSeedConjKerClass
  rw [gammaNSeedConjKerClass_smul, map_smul]

open scoped Classical in
/-- **The seed side of `ClassicalLinearity`**: the seed vector is additive and homogeneous for the twisted scalar action of `TwTuple`
(from S6's `gammaNSeedKerClass_add/_smul` and the conjugate-linear `gammaNSeedConjKerClass_smul`). -/
theorem seedLinearity : SeedLinearity N n where
  seed_add f g := by
    unfold seedBoundary
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_add]
    refine congrArg _ ?_
    change ((faceSeedKerClass N (planeFaceRepr i) n (f i false + g i false)).1 +
      (faceSeedConjKerClass N (planeFaceRepr i) n (f i true + g i true)).1) = _
    rw [faceSeedKerClass_add, faceSeedConjKerClass_add]
    simp only [Submodule.coe_add]
    abel
  seed_smul a f := by
    unfold seedBoundary
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_smul]
    refine congrArg _ ?_
    change ((faceSeedKerClass N (planeFaceRepr i) n (a • f i false)).1 +
      (faceSeedConjKerClass N (planeFaceRepr i) n ((star a) • f i true)).1) = _
    rw [faceSeedKerClass_smul, faceSeedConjKerClass_smul]
    simp only [Submodule.coe_smul, smul_add]
    have : (starRingEnd ℂ) (star a) = a := by simp
    rw [this]

/-- **`ClassicalLinearity` (unconditional)**: S6's series linearity and the seed linearity. -/
theorem classicalLinearity (hn : 4 ≤ n) : ClassicalLinearity N n hn :=
  ClassicalLinearity.of_seed N n hn (seedLinearity N n)

end TernaryPeriodPolynomials.Argument.FormClassK
