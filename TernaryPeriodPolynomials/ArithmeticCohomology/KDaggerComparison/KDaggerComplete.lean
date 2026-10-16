module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.CompleteDictionary
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.CompleteDictionaryLine

@[expose] public section


/-!
# `K†` comparison: the face dictionary is complete

At the paper's level `3 ∣ N`, `N ≥ 3`:

* `stratum_family_equiv`: `StratumH2 n trivialCharacter side ≃ₗ[ℂ] qFamilies N n side`, the stratum cohomology of `K†` is the space of `K†`-invariant
  families of classes of the groups `Γ_F ∩ (Γ ∩ Γ(N))` over all rational flags (`fam_act`: `(k • w)(F) = k_* w(k⁻¹ F)`).
* `phi_plane_equiv`, `phi_line_equiv`: the face dictionaries `phiPlane`, `phiLine` are linear isomorphisms onto the `K†`-invariant vectors
  `PlaneQInvariants`, `LineQInvariants` of `⨁_faces H²(Γ(N) ∩ face, E_n)` (`range_phi_plane`, `range_phi_line`).
* `inner_boundary_iff_phi_plane_mem_range`, `inner_boundary_iff_phi_line_mem_range`: `InnerBoundary ξ ↔ Φ ξ` lies in the image of the mixed cuspidal
  group; `phi_plane_inner_equiv`, `phi_line_inner_equiv`: the inner classes are isomorphic to the `K†`-invariant mixed cuspidal vectors.
* `vanishes_on_good_iff_phi_plane`, `vanishes_on_good_iff_phi_line` (and the flag-wise `..._at`): `VanishesOnGood ξ` iff `Φ ξ` has zero
  component at every good face of `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.KDaggerComplete

open TernaryPeriodPolynomials.Argument.KDaggerComparison

alias reconstruct_cochain := reconstructCochain
alias exists_fixed_point_h2_eq := exists_fixedPointH2_eq
alias stabilizer_transport_h2_mem_locally_inner := stabilizerTransportH2_mem_locallyInner
alias fam_act := famAct
alias q_families := qFamilies
alias stratum_family := stratumFamily
alias stratum_family_injective := stratumFamily_injective
alias range_stratum_family := range_stratumFamily
alias stratum_family_equiv := stratumFamilyEquiv
alias exists_plane_face_translate := exists_planeFace_translate
alias exists_line_face_translate := exists_lineFace_translate
alias plane_q_invariants := PlaneQInvariants
alias line_q_invariants := LineQInvariants
alias mem_plane_q_invariants_iff := mem_planeQInvariants_iff
alias mem_line_q_invariants_iff := mem_lineQInvariants_iff
alias range_phi_plane := range_phiPlane
alias range_phi_line := range_phiLine
alias phi_plane_injective := phiPlane_injective
alias phi_line_injective := phiLine_injective
alias phi_plane_equiv := phiPlaneEquiv
alias phi_line_equiv := phiLineEquiv
alias inner_boundary_iff_phi_plane_mem_range := innerBoundary_iff_phiPlane_mem_range
alias inner_boundary_iff_phi_line_mem_range := innerBoundary_iff_phiLine_mem_range
alias phi_plane_inner_equiv := phiPlaneInnerEquiv
alias phi_line_inner_equiv := phiLineInnerEquiv
alias vanishes_on_good_iff_phi_plane_at := vanishesOnGood_iff_phiPlaneAt
alias vanishes_on_good_iff_phi_line_at := vanishesOnGood_iff_phiLineAt
alias vanishes_on_good_iff_phi_plane := vanishesOnGood_iff_phiPlane
alias vanishes_on_good_iff_phi_line := vanishesOnGood_iff_phiLine

end TernaryPeriodPolynomials.Argument.Statements.KDaggerComplete
