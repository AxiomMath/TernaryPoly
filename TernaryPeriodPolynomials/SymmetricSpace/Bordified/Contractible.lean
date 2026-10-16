module

public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.ContractibleHomology
public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.BoundaryInward

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBordifiedContractible
open SymmetricSpacePositive SymmetricSpaceRationalGluing SymmetricSpaceBordifiedPrincipalSix
open ContractibleSingularHomology CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped unitInterval

/-- The actual quotient's global inward homotopy, assembled from its proved local product charts. -/
def actualGlobalInward : InwardHomotopy.LocalDeformation arithmeticInterior :=
  (exists_global_inward SymmetricSpaceQuotientBoundary.exists_local).choose

/-- The actual assembled quotient homotopy ends entirely in the original arithmetic interior. -/
theorem actualGlobalInward_endpoint (x : BordifiedOrbit) :
    actualGlobalInward.homotopy (1, x) ∈ arithmeticInterior :=
  (exists_global_inward SymmetricSpaceQuotientBoundary.exists_local).choose_spec x

/-- The actual symmetric-space embedding into the full rational gluing is a genuine
homotopy equivalence, with no geometric hypotheses. -/
def actualEmbeddingHomotopyEquiv : ContinuousMap.HomotopyEquiv Space Glued :=
  homotopyEquivOfInward actualGlobalInward.homotopy actualGlobalInward.zero
    actualGlobalInward.preserves actualGlobalInward_endpoint

/-- The constructed equivalence's forward map is the literal original embedding. -/
theorem actualEmbeddingHomotopyEquiv_apply (S : Space) :
    actualEmbeddingHomotopyEquiv S = embedding S :=
  homotopyEquivOfInward_apply actualGlobalInward.homotopy actualGlobalInward.zero
    actualGlobalInward.preserves actualGlobalInward_endpoint S

/-- The actual full rational corner gluing is contractible. -/
instance actualGluedContractible : ContractibleSpace Glued :=
  actualEmbeddingHomotopyEquiv.symm.contractibleSpace

/-- The actual inclusion equivalence induces a genuine singular chain homotopy equivalence. -/
def actualEmbeddingChainHomotopyEquiv :
    _root_.HomotopyEquiv (chains Space) (chains Glued) :=
  chainHomotopyEquiv actualEmbeddingHomotopyEquiv

/-- All positive-degree rational singular homology groups of the actual Glued space vanish. -/
theorem actual_glued_homology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero ((chains Glued).homology n) := homology_isZero n hn

/-- The literal rational singular chain complex of Glued is exact in positive degrees. -/
theorem actual_glued_chains_exactAt (n : ℕ) (hn : n ≠ 0) :
    (chains Glued).ExactAt n := chains_exactAt n hn

/-- The actual singular degree-zero augmentation identifies H0 of Glued with ℚ. -/
def actual_glued_homologyZeroIso : (chains Glued).homology 0 ≅ ModuleCat.of.{0} ℚ ℚ :=
  homologyZeroIso

/-- The degree-zero isomorphism is induced by the literal Mathlib singular augmentation. -/
theorem actual_glued_homologyZeroIso_hom : actual_glued_homologyZeroIso.hom =
    (TopCat.of Glued).singularHomology₀ε (ModuleCat.of.{0} ℚ ℚ) := rfl

/-- Unconditional actual-space consumer: contractibility, actual H0 augmentation isomorphism,
and vanishing of every positive-degree rational singular homology group. -/
theorem actual_glued_singular_consumer :
    ContractibleSpace Glued ∧
      IsIso ((TopCat.of Glued).singularHomology₀ε (ModuleCat.of.{0} ℚ ℚ)) ∧
      ∀ n : ℕ, n ≠ 0 → IsZero ((chains Glued).homology n) := by
  refine ⟨inferInstance, ?_, actual_glued_homology_isZero⟩
  rw [← actual_glued_homologyZeroIso_hom]
  exact actual_glued_homologyZeroIso.isIso_hom

end TernaryPoly.SymmetricSpaceBordifiedContractible
