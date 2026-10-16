module

public import TernaryPeriodPolynomials.Topology.InwardHomotopyCovering
public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.ContractibleInterior
public import TernaryPeriodPolynomials.Analysis.Finite.InwardHomotopy

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBordifiedContractible
open SymmetricSpacePositive SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient
  SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceCompactBordification IntegralGL3Congruence
open scoped unitInterval

/-- The actual symmetric-space embedding is a homotopy equivalence whenever the specified
actual quotient homotopy preserves the interior and ends entirely in it. -/
def homotopyEquivOfInward (H : C(I × BordifiedOrbit, BordifiedOrbit))
    (hzero : ∀ x, H (0, x) = x)
    (hpres : ∀ t x, x ∈ arithmeticInterior → H (t, x) ∈ arithmeticInterior)
    (hend : ∀ x, H (1, x) ∈ arithmeticInterior) :
    ContinuousMap.HomotopyEquiv Space Glued :=
  preimageInteriorHomeomorph.symm.toHomotopyEquiv.trans
    (InwardHomotopyCovering.liftedHomotopyEquiv actual_projection_covering H hzero hpres hend)

/-- The forward map of the constructed actual equivalence is literally `embedding`. -/
theorem homotopyEquivOfInward_apply (H : C(I × BordifiedOrbit, BordifiedOrbit))
    (hzero : ∀ x, H (0, x) = x)
    (hpres : ∀ t x, x ∈ arithmeticInterior → H (t, x) ∈ arithmeticInterior)
    (hend : ∀ x, H (1, x) ∈ arithmeticInterior) (S : Space) :
    homotopyEquivOfInward H hzero hpres hend S = embedding S := by
  change (preimageInteriorHomeomorph.symm S).val = embedding S
  have h := preimageInteriorHomeomorph_embedding (preimageInteriorHomeomorph.symm S)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

/-- Conditional only on the actual downstairs inward homotopy, the full genuine gluing is
contractible. The covering, interior identification and upstairs contractibility are all proved. -/
theorem glued_contractible_of_inward (H : C(I × BordifiedOrbit, BordifiedOrbit))
    (hzero : ∀ x, H (0, x) = x)
    (hpres : ∀ t x, x ∈ arithmeticInterior → H (t, x) ∈ arithmeticInterior)
    (hend : ∀ x, H (1, x) ∈ arithmeticInterior) : ContractibleSpace Glued :=
  (homotopyEquivOfInward H hzero hpres hend).symm.contractibleSpace

/-- Root's finite local-deformation criterion, specialized to the actual compact orbit
bordification, produces the global base homotopy needed by the covering lift. -/
theorem exists_global_inward
    (hlocal : ∀ x : BordifiedOrbit, ∃ d : InwardHomotopy.LocalDeformation arithmeticInterior,
      d.homotopy (1, x) ∈ arithmeticInterior) :
    ∃ d : InwardHomotopy.LocalDeformation arithmeticInterior,
      ∀ x, d.homotopy (1, x) ∈ arithmeticInterior := by
  let := SymmetricSpaceCompactBordification.quotient_compact principalSix
  exact InwardHomotopy.exists_global arithmeticInterior_open hlocal

/-- The exact remaining local geometric criterion suffices for the actual Glued contractibility. -/
theorem glued_contractible_of_local
    (hlocal : ∀ x : BordifiedOrbit, ∃ d : InwardHomotopy.LocalDeformation arithmeticInterior,
      d.homotopy (1, x) ∈ arithmeticInterior) : ContractibleSpace Glued := by
  obtain ⟨d, hd⟩ := exists_global_inward hlocal
  exact glued_contractible_of_inward d.homotopy d.zero d.preserves hd

/-- The finite local criterion also yields an actual homotopy equivalence with literal embedding. -/
theorem exists_embedding_homotopyEquiv_of_local
    (hlocal : ∀ x : BordifiedOrbit, ∃ d : InwardHomotopy.LocalDeformation arithmeticInterior,
      d.homotopy (1, x) ∈ arithmeticInterior) :
    ∃ e : ContinuousMap.HomotopyEquiv Space Glued, ∀ S, e S = embedding S := by
  obtain ⟨d, hd⟩ := exists_global_inward hlocal
  exact ⟨homotopyEquivOfInward d.homotopy d.zero d.preserves hd,
    homotopyEquivOfInward_apply d.homotopy d.zero d.preserves hd⟩

end TernaryPoly.SymmetricSpaceBordifiedContractible
