module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Relative

@[expose] public section


/-!
# The antiholomorphic line seed as a relative 2-cocycle of `Λ₁⁺` (LS13b)

Line mirror of `SeedC3S4c.SeedEdgeConj` (first half): the cochain of the antiholomorphic seed is the coefficientwise conjugate of that of the holomorphic seed
(`cuspSeedConjCochain_eq`), it is a relative 2-cocycle (`lineSeedConjRelCocycle`) and `lineComplexify_cuspSeedConjClass` identifies the complexification of its de Rham class.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1)

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

/-- The zig-zag cochain of the antiholomorphic line seed of `f`, on `Λ₁⁺`. -/
def lineSeedConjChain (g k : Lam1Plus) : Coef n :=
  cuspSeedConjCochain linePlusData linePlus_hΛ (f := f) g k

theorem lineSeedConjChain_eq (g k : Lam1Plus) :
    lineSeedConjChain f g k = Coef.conjCoef (lineSeedChain f g k) :=
  cuspSeedConjCochain_eq linePlusData linePlus_hΛ g k

theorem lineSeedConjChain_inl_inl (r r' : RadicalLattice) :
    lineSeedConjChain f (linePlusInl r) (linePlusInl r') = 0 := by
  rw [lineSeedConjChain_eq, lineSeedChain_inl_inl]
  apply Coef.toPoly_injective
  simp

/-- The antiholomorphic seed cochain as a complex 2-cocycle with coefficients in the library's representation. -/
def lineSeedConjCocycle₂ : cocycles₂ (linePlusRep n) :=
  cxCocycles n ⟨fun p => lineSeedConjChain f p.1 p.2, (mem_cocycles₂_iff _).2 (fun g h j =>
    cuspSeedConjCochain_cocycle linePlusData linePlus_hΛ g h j)⟩

/-- The relative 2-cocycle of the antiholomorphic line seed. -/
def lineSeedConjRelCocycle : relativeTwoCocycles linePlusExtensionS.inl (linePlusRep n) :=
  ⟨lineSeedConjCocycle₂ f, fun r r' => by
    change cxVec n (lineSeedConjChain f (linePlusInl r) (linePlusInl r')) = 0
    rw [lineSeedConjChain_inl_inl]
    exact map_zero _⟩

theorem lineComplexify_cuspSeedConjClass :
    lineComplexify n (cuspSeedConjClass linePlusData linePlus_hΛ (f := f)) =
      (relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n) (lineSeedConjRelCocycle f)).val := by
  change lineComplexify n (H2π (Rep.of (linePlusData.rhoR n)) (ZigZag.cochainCocycle _ _)) =
    H2π (linePlusRep n) (lineSeedConjCocycle₂ f)
  rw [lineComplexify_H2π]
  rfl

end

end TernaryPeriodPolynomials.Argument.LineSeed
