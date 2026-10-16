module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LineEdgeAlign

@[expose] public section


/-!
# The canonical alignment of `𝒞_Q(E*)` with the cuspidal subspace of `H¹(Γ₂(N), H¹(N_{Q'}, E*))`

Formalized by Claude Sonnet 5.5.

The dual line cuspidal space `𝒞_Q(E*) ⊂ H²(Γ_{Q'}, E*)` (`dualCuspidalQLiteral`, defined by transport from the plane cusp `ȷ(h)`) is identified with
the `QDiLit` (`cuspidalSubspace (Γ(N)) (lineFaceRadH1Lit N n h)`) through the Hochschild-Serre edge of the line face of the literal dual:

* `ȷ` is a morphism of split extensions (`faceJ`, `faceJ_inl`, `faceJ_split`) over `(τ, σ)`, `σ(γ) = D γ D`, `D = diag(1,-1)`, with coefficient comparison `dualIso`; the transport of `H²` is the
  composite `toLiteral ∘ facePullC` (`h2Map_faceJ`, bijective);
* naturality of the edge: `edge_{Q'}(ȷ^* x) = H¹(σ)(edge_{P''} x)` (`edgeL_kerJ`);
* `H¹(σ)` is bijective and carries `𝒞_P(E)` onto the cuspidal subspace (`h1J_bijective`, `h1J_mem_cuspidal_iff`);
* `dualCuspidalLiteralEquiv : 𝒞_Q(E*) ≃ₗ[ℂ] QDiLit` (`edgeL` restricted), with `dualCuspidalLiteralEquiv_apply` the compatibility with the plane edge, and `𝒞_Q(E*) ⊂ ker(res_N)`
  (`dualCuspidalQLiteral_le_ker`).
-/

namespace TernaryPeriodPolynomials.Argument.Statements.EisensteinDualEdge

open TernaryPeriodPolynomials.Argument.EisensteinDual

alias line_face_j_morphism := faceJ_inl
alias line_face_j_levi := faceJ_split
alias j_transport_h2 := h2Map_faceJ
alias j_transport_h2_bijective := h2Map_faceJ_bijective
alias line_edge_natural := edgeL_kerJ
alias levi_h1_bijective := h1J_bijective
alias levi_h1_cuspidal_iff := h1J_mem_cuspidal_iff
alias dual_cuspidal_edge_characterisation := mem_dualCuspidalQLiteral_iff_edge
alias dual_cuspidal_le_radical_kernel := dualCuspidalQLiteral_le_ker
alias dual_cuspidal_literal_equiv := dualCuspidalLiteralEquiv
alias dual_cuspidal_literal_equiv_apply := dualCuspidalLiteralEquiv_apply

end TernaryPeriodPolynomials.Argument.Statements.EisensteinDualEdge
