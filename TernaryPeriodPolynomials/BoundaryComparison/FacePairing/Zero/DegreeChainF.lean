module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Zero.DegreeChainE

@[expose] public section


/-!
# Degree-zero reconstruction, part F: `phiL` and its injectivity at degree zero

Step 12 (`degree = 0` analogue of `phiL`/`phiL_injective`), completing the chain started in
`ZeroDegreeChain.lean`/`ZeroDegreeChainB.lean`-`E.lean` (Steps 1-11).
-/

noncomputable section

open GeneralEisenstein Matrix CategoryTheory
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Spectral.GoodLineLocalOp
open TernaryPeriodPolynomials.Spectral.LocalUniqueness
open TernaryPeriodPolynomials.Spectral.ModularH2

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **Step 12.** `degree = 0` analogue of `phiL` (reusing the already-unconditional `ML 0`,
`psiL 0`). See the module docstring for why the membership side-condition is discharged via the
explicit library lemma `Submodule.mem_comap` rather than the bare `fun _ hy => hy`. -/
def phiLZero : ML 0 →ₗ[ℂ] groupCohomology.H1 (arithmeticBinaryRep 1 0) :=
  edgeKZero ∘ₗ (psiL 0).restrict (fun _ hy => Submodule.mem_comap.mp hy)

/-- **Step 12, injectivity.** `degree = 0` analogue of `phiL_injective`. -/
theorem phiLZero_injective : Function.Injective phiLZero := by
  intro y y' h
  have h1 := edgeKZero_injective h
  apply Subtype.ext
  exact psiL_injective 0 (congrArg Subtype.val h1)

end TernaryPeriodPolynomials.Argument.FacePairing
