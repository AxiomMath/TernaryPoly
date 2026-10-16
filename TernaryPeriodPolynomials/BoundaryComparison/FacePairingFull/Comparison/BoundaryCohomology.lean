module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.TraceEvaluation
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.BoundaryH4

@[expose] public section


/-!
# The model boundary complex computes the cohomology of `∂M` with every local coefficient system

Worker M's homotopy equivalence `coneEquiv : coneR ≃ stabilizerFaceCone` between the model cone `coneR` (the cone of the signed
incidence of the three model resolutions `ℚ[GL₃(ℚ)^{•+1} × Z]` of the flag, line and plane labels, whose `Hom_{Γ(6)}(-, W)` cochains
are the boundary-building cochains of the project's model: a flag part of degree one less, a line part and a plane part) and
the library's stabilizer cone, and the library's quasi-isomorphism `localBoundaryToStabilizerTotal W` from the genuine singular
local-system cochains of the arithmetic boundary `∂M` to `Hom(stabilizerFaceCone, W)`, compose to a quasi-isomorphism of
cochain complexes
`localBoundaryCochains W ≃ homCochains coneR W`
for **every** rational representation `W` of `Γ(6)` and **every** degree (`modelBoundary_cohomology_iso`). With `W` the
rational coefficient system `E_n` of the geometric side (`TernaryPoly.restrictedCoefficients`) this says that the model's
boundary cohomology `H^k` of the cone with coefficients `E` is the genuine cohomology `H^k(∂M; E)` in which the restrictions `r_P`,
`r_Q`, `r_B` of the paper live; the restriction of the cone cohomology to the line and plane faces is compatible with
the geometric one (`stabilizerTotalToGeometric_restriction`).

This extends D3 (`TraceEvaluation`), which used the same two equivalences only in degree four with trivial coefficients.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex
open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.EquivariantSingularSmall

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

/-- **The model boundary complex is the genuine boundary cochain complex.** -/
def modelBoundaryQuasiIso (W : Rep.{0} ℚ principalSix) :
    localBoundaryCochains W ⟶ homCochains coneR W :=
  localBoundaryToStabilizerTotal W ≫ homPullback coneEquiv.hom W

instance modelBoundaryQuasiIso_quasiIso (W : Rep.{0} ℚ principalSix) :
    QuasiIso (modelBoundaryQuasiIso W) := by
  have h1 : QuasiIso (homPullback coneEquiv.hom W) := homPullback_quasiIso_of_homotopyEquiv coneEquiv W
  exact _root_.quasiIso_comp (localBoundaryToStabilizerTotal W) (homPullback coneEquiv.hom W)

/-- **Cohomology of the model boundary complex with coefficients `W` is `H^k(∂M; W)`**, for every
rational representation `W` of `Γ(6)` and every degree `k`. -/
def modelBoundary_cohomology_iso (W : Rep.{0} ℚ principalSix) (k : ℕ) :
    (homCochains coneR W).homology k ≅ (localBoundaryCochains W).homology k :=
  (asIso (homologyMap (modelBoundaryQuasiIso W) k)).symm

/-- The same for the geometric side's coefficient systems `Sym^n ⊗ det^e` of `Γ(6)` (`restrictedCoefficients n e`, the rational forms
of the model's `E`, `Comparison.Coefficients`): the cohomology of the model boundary complex is `H^k(∂M; E)`. -/
def modelBoundary_cohomology_iso_E (n : ℕ) (e : ℤ) (k : ℕ) :
    (homCochains coneR (SymmetricSpaceBoundaryFull.restrictedCoefficients n e)).homology k ≅
      (SymmetricSpaceBoundaryFull.coverBoundaryCochains n e).homology k :=
  modelBoundary_cohomology_iso _ k

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
