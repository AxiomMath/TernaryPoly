module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Maps
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.LinearSelection
public import TernaryPeriodPolynomials.BoundaryComparison.ConstantTerms

@[expose] public section


/-!
# The dual constant-term identity `ar:eq:dualconstantterms`

Paper (Appendix C.4, "The dual series and the boundary relation"): for each mixed cuspidal
class `η ∈ 𝒞_Q(E*)` there is a closed global class `𝓔_Q^∨(η)` with coefficients `E*` such that
`r_Q 𝓔_Q^∨(η) = η`, `r_P 𝓔_Q^∨(η) = T^∨ η` (mixed cuspidal, the "second constant-term map") and
`r_B 𝓔_Q^∨(η) = 0`. The paper obtains it by applying the construction of `𝓔_P(ξ)` to `ȷ(Γ)`
and pulling back along `ȷ`.

In the boundary-building cochain model `E*` is `dualRep ρ = ρ ∘ φ` (`Dual/Model`), with global
cocycles `cocycles rationalLevel (dualRep ρ)`, strata `StratumH2Rep (dualRep ρ) side`, restrictions
`restrictionCocycleRep`, and inner classes `InnerBoundaryRep` (zero restriction to every complete
flag, so `r_B = 0` is encoded in the inner condition of the plane coordinate). The identity is
obtained exactly as in the paper, by transport of the (proved) constant-term target
`constant_terms` along the level-preserving involution (`Dual/Maps`).

Two forms are proved. `dual_constant_terms_pointwise` is the literal identity for each `η`.
`dual_constant_terms` packages the plane coordinates into one linear map `T^∨` (chosen on a basis
of the inner line classes; the paper assumes neither invertibility nor an adjoint
normalization of `T^∨`, and the identification of this `T^∨` with a named intertwiner such as
`ar:eq:intertwiner` is not part of the statement).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

/-- The coefficient system `E = Sym^n`. -/
abbrev ρE (n : ℕ) := rationalCoefficientComponent n trivialCharacter

variable (n : ℕ)

local notation "ρ" => ρE n
local notation "ρs" => dualRep (ρE n)

/-- **Dual constant terms, pointwise (`ar:eq:dualconstantterms`).** For `n ≥ 4`, every inner line
class `η` of `E*` is the line restriction `r_Q` of a global class of `E*` whose plane restriction
`r_P` is inner (so `r_B = 0`). -/
theorem dual_constant_terms_pointwise (hn : 4 ≤ n)
    (η : StratumH2Rep (dualRep (ρE n)) .line)
    (hη : InnerBoundaryRep (dualRep (ρE n)) .line η) :
    ∃ c' : cocycles rationalLevel (dualRep (ρE n)),
      InnerBoundaryRep (dualRep (ρE n)) .plane
        (globalCoordinatesRep (dualRep (ρE n)) c').1 ∧
      (globalCoordinatesRep (dualRep (ρE n)) c').2 = η := by
  obtain ⟨z', hz', u', hu'⟩ := hη
  have hzInner : InnerBoundary n trivialCharacter .plane
      (classOf rationalLevel (flagRepresentation ρ .plane) (fromLineStar ρ z')) :=
    ⟨fromLineStar ρ z', rfl, fromEdgeStar ρ u',
      edgeExact_transport (dualRep ρ) ρ (dualRep_dualRep_apply ρ) dualPlaneFlag dualPlaneFlag_smul
        (endpoint .line) (endpoint .plane) (fun e => (endpoint_line_dualEdge e).symm) z' u' hu'⟩
  obtain ⟨c, hc1, hc2⟩ := constant_terms n hn _ hzInner
  refine ⟨phiCocycle ρ c, ?_, ?_⟩
  · obtain ⟨z₀, hz₀, u₀, hu₀⟩ := hc2
    have hrestr : classOf rationalLevel (flagRepresentation ρ .line)
        (restrictionCocycleRep ρ .line c) = classOf rationalLevel (flagRepresentation ρ .line) z₀ :=
      hz₀.symm
    refine ⟨toPlaneStar ρ z₀, ?_, toEdgeStar ρ u₀,
      edgeExact_transport ρ (dualRep ρ) (fun _ => rfl) dualPlaneFlag dualPlaneFlag_smul
        (endpoint .line) (endpoint .plane) (fun e => (endpoint_line_dualEdge e).symm) z₀ u₀ hu₀⟩
    change classOf rationalLevel (flagRepresentation (dualRep ρ) .plane) (toPlaneStar ρ z₀) =
      classOf rationalLevel (flagRepresentation (dualRep ρ) .plane)
        (restrictionCocycleRep (dualRep ρ) .plane (phiCocycle ρ c))
    rw [← toPlaneStar_restriction]
    exact (classOf_transport ρ (dualRep ρ) (fun _ => rfl) dualPlaneFlag dualPlaneFlag_smul
      hrestr).symm
  · change classOf rationalLevel (flagRepresentation (dualRep ρ) .line)
      (restrictionCocycleRep (dualRep ρ) .line (phiCocycle ρ c)) = η
    rw [← toLineStar_restriction]
    have hplane : classOf rationalLevel (flagRepresentation ρ .plane)
        (restrictionCocycleRep ρ .plane c) =
        classOf rationalLevel (flagRepresentation ρ .plane) (fromLineStar ρ z') := hc1
    have h := classOf_transport ρ (dualRep ρ) (fun _ => rfl) dualFlag dualFlag_smul hplane
    have e : toLineStar ρ (fromLineStar ρ z') = z' := toLineStar_fromLineStar ρ z'
    exact (h.trans (congrArg (classOf rationalLevel (functionRepresentation (dualRep ρ)
      (Flags .line))) e)).trans hz'

/-- **Dual constant terms (`ar:eq:dualconstantterms`), with a linear `T^∨`.** For `n ≥ 4` there is a
linear map `T^∨` from the line stratum cohomology of `E*` to its plane stratum cohomology such that
for every inner line class `η` of `E*`, `T^∨ η` is inner and some global class of `E*` has maximal
coordinates `(r_P, r_Q) = (T^∨ η, η)`. (`T^∨` is the plane coordinate of the dual series; no
invertibility or adjoint normalization is claimed, and no identification with a named intertwiner.) -/
theorem dual_constant_terms (hn : 4 ≤ n) :
    ∃ T : StratumH2Rep (dualRep (ρE n)) .line →ₗ[ℂ] StratumH2Rep (dualRep (ρE n)) .plane,
      ∀ η, InnerBoundaryRep (dualRep (ρE n)) .line η →
        InnerBoundaryRep (dualRep (ρE n)) .plane (T η) ∧
        ∃ c' : cocycles rationalLevel (dualRep (ρE n)),
          globalCoordinatesRep (dualRep (ρE n)) c' = (T η, η) := by
  obtain ⟨T, hT⟩ := exists_linear_selection (globalCoordinatesRepLinear (dualRep (ρE n)))
    (innerClassesRep (dualRep (ρE n)) .line) (innerClassesRep (dualRep (ρE n)) .plane)
    (fun η hη => by
      obtain ⟨c, hc1, hc2⟩ := dual_constant_terms_pointwise n hn η hη
      exact ⟨c, hc1, hc2⟩)
  exact ⟨T, fun η hη => hT η hη⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
