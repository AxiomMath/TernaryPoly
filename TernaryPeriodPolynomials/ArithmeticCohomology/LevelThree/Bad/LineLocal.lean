module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.FullBound

@[expose] public section


/-!
# The Hochschild–Serre `E^{1,1}` part of the bad-line local cohomology

At the standard bad line (`cuspFlag .line false = standardBadLine`, trivial character), the local
cohomology `H²(Γ_F, V)` is, by Sol's inhomogeneous model, `H²` of the split extension
`ℤ² ⋊ (ℤˣ × Γ₁'(3))`. Its classes with zero radical restriction (the `E^{1,1} = H¹(Levi, H¹(U, V))`
part) embed into `H¹(Γ₁'(3), Sym^{degree+1})` (Sol: `standardBadLineMixedMap_injective`,
`explicitBinaryMixedH1Equiv`, `binaryLeviH1Equiv`). With `FullBound`:

* `finrank_badLineRadicalKernel_le`: `dim + 1 ≤ ⌊(degree + 3)/3⌋ + [degree even]` (`0 < degree`);
* `badLineLocalRadicalKernel`: the same subspace inside `H²(Γ_F, V)` itself, with the same bound
  (`finrank_badLineLocalRadicalKernel_le`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineLocal

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers GeneralEisenstein GeneralEisenstein.Homogeneous Module
open ParabolicBounds FullBound

/-- Classes of the split-extension model with vanishing restriction to the radical `ℤ²`. -/
abbrev badLineRadicalKernel (degree : ℕ) :=
  LinearMap.ker (radicalRestrictionH2 integralBadLineSplitting.conjAct
    (standardBadLineRepresentation degree))

/-- The embedding of the radical kernel into `H¹(Γ₁'(3), Sym^{degree+1})`. -/
def badLineLeviMap (degree : ℕ) (positive : 0 < degree) :
    badLineRadicalKernel degree →ₗ[ℂ] CrossedH1 (binaryArithmeticRepresentation degree) :=
  (binaryLeviH1Equiv degree).toLinearMap.comp
    ((explicitBinaryMixedH1Equiv degree positive).toLinearMap.comp
      (radicalKernelMixedMap integralBadLineSplitting.conjAct (standardBadLineRepresentation degree)))

theorem badLineLeviMap_injective (degree : ℕ) (positive : 0 < degree) :
    Function.Injective (badLineLeviMap degree positive) :=
  (binaryLeviH1Equiv degree).injective.comp
    ((explicitBinaryMixedH1Equiv degree positive).injective.comp
      (standardBadLineMixedMap_injective degree))

/-- **`dim E^{1,1}(bad line) + 1 ≤ ⌊(degree + 3)/3⌋ + [degree even]`**. -/
theorem finrank_badLineRadicalKernel_le (degree : ℕ) (positive : 0 < degree) :
    finrank ℂ (badLineRadicalKernel degree) + 1 ≤
      (degree + 3) / 3 + (if Even degree then 1 else 0) := by
  have : FiniteDimensional ℂ (CrossedH1 (binaryArithmeticRepresentation degree)) :=
    level_H1_finiteDimensional 0 (Nat.succ_pos degree)
  have le := LinearMap.finrank_le_finrank_of_injective (badLineLeviMap_injective degree positive)
  have bound := finrank_binaryArithmetic_H1_le degree
  omega

/-- The radical kernel inside the local cohomology `H²(Γ_F, V)` at the standard bad line. -/
def badLineLocalRadicalKernel (degree : ℕ) :
    Submodule ℂ (H2 (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter)) :=
  (badLineRadicalKernel degree).comap (standardBadLineInhomogeneousH2Equiv degree).toLinearMap

/-- The local radical kernel maps injectively onto the model radical kernel. -/
def localToModel (degree : ℕ) :
    badLineLocalRadicalKernel degree →ₗ[ℂ] badLineRadicalKernel degree :=
  let f : badLineLocalRadicalKernel degree →ₗ[ℂ]
      InhomogeneousH2 (standardBadLineRepresentation degree) :=
    (standardBadLineInhomogeneousH2Equiv degree).toLinearMap.comp
      (badLineLocalRadicalKernel degree).subtype
  LinearMap.codRestrict (badLineRadicalKernel degree) f (fun v => v.property)

theorem localToModel_injective (degree : ℕ) : Function.Injective (localToModel degree) := by
  intro v w h
  apply Subtype.ext
  exact (standardBadLineInhomogeneousH2Equiv degree).injective (congrArg Subtype.val h)

/-- **Local form**: the classes of `H²(Γ_F, V)` at the bad line with zero radical restriction
span a space of dimension `≤ ⌊(degree + 3)/3⌋ - 1 + [degree even]`. -/
theorem finrank_badLineLocalRadicalKernel_le (degree : ℕ) (positive : 0 < degree) :
    finrank ℂ (badLineLocalRadicalKernel degree) + 1 ≤
      (degree + 3) / 3 + (if Even degree then 1 else 0) := by
  have : FiniteDimensional ℂ (CrossedH1 (binaryArithmeticRepresentation degree)) :=
    level_H1_finiteDimensional 0 (Nat.succ_pos degree)
  have : FiniteDimensional ℂ (badLineRadicalKernel degree) :=
    Module.Finite.of_injective _ (badLineLeviMap_injective degree positive)
  have le := LinearMap.finrank_le_finrank_of_injective (localToModel_injective degree)
  have bound := finrank_badLineRadicalKernel_le degree positive
  omega

end TernaryPeriodPolynomials.LevelThree.BadLineLocal
