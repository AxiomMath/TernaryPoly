module

public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.ContractibleInward
public import TernaryPeriodPolynomials.Topology.ContractibleSingularHomology

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBordifiedContractible
open SymmetricSpaceRationalGluing SymmetricSpaceBordifiedPrincipalSix
open ContractibleSingularHomology CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped unitInterval

variable (H : C(I × BordifiedOrbit, BordifiedOrbit)) (hzero : ∀ x, H (0, x) = x)
variable (hpres : ∀ t x, x ∈ arithmeticInterior → H (t, x) ∈ arithmeticInterior)
variable (hend : ∀ x, H (1, x) ∈ arithmeticInterior)

include H hzero hpres hend in
/-- Given the actual quotient inward homotopy, positive-degree singular homology of the
actual rational corner gluing vanishes. -/
theorem glued_homology_isZero (n : ℕ) (hn : n ≠ 0) : IsZero ((chains Glued).homology n) := by
  let := glued_contractible_of_inward H hzero hpres hend
  exact homology_isZero n hn

include H hzero hpres hend in
/-- Actual rational singular chains of Glued are exact in every positive degree. -/
theorem glued_chains_exactAt (n : ℕ) (hn : n ≠ 0) : (chains Glued).ExactAt n := by
  let := glued_contractible_of_inward H hzero hpres hend
  exact chains_exactAt n hn

/-- The actual degree-zero singular augmentation of Glued gives the coefficient-module
isomorphism, conditional only on the specified actual downstairs homotopy. -/
def glued_homologyZeroIso : (chains Glued).homology 0 ≅ ModuleCat.of.{0} ℚ ℚ := by
  letI := glued_contractible_of_inward H hzero hpres hend
  exact homologyZeroIso

/-- This isomorphism's map is the literal Mathlib singular H0 augmentation. -/
theorem glued_homologyZeroIso_hom : (glued_homologyZeroIso H hzero hpres hend).hom =
    (TopCat.of Glued).singularHomology₀ε (ModuleCat.of.{0} ℚ ℚ) := rfl

/-- Concrete actual-space consumer under the exact outstanding local-deformation criterion.
It combines genuine Glued contractibility, the literal augmentation isomorphism, and all
positive-degree singular-homology vanishings. -/
theorem glued_singular_consumer
    (hlocal : ∀ x : BordifiedOrbit, ∃ d : InwardHomotopy.LocalDeformation arithmeticInterior,
      d.homotopy (1, x) ∈ arithmeticInterior) :
    ContractibleSpace Glued ∧
      IsIso ((TopCat.of Glued).singularHomology₀ε (ModuleCat.of.{0} ℚ ℚ)) ∧
      ∀ n : ℕ, n ≠ 0 → IsZero ((chains Glued).homology n) := by
  obtain ⟨d, hd⟩ := exists_global_inward hlocal
  refine ⟨glued_contractible_of_inward d.homotopy d.zero d.preserves hd, ?_,
    glued_homology_isZero d.homotopy d.zero d.preserves hd⟩
  rw [← glued_homologyZeroIso_hom d.homotopy d.zero d.preserves hd]
  exact (glued_homologyZeroIso d.homotopy d.zero d.preserves hd).isIso_hom

end TernaryPoly.SymmetricSpaceBordifiedContractible
