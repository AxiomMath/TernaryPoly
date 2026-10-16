module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.DualJ.Pullback
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Graph
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.ConstantTerms

@[expose] public section


/-!
# The dual series `𝓔_Q^∨(η)` and the second constant-term map `T^∨`, through `ȷ`

Paper (Appendix C.4, "The dual series and the boundary relation", `ar:eq:dualconstantterms`): applying the
construction of `𝓔_P` to `ȷ(Γ)` and pulling back along `ȷ` gives, for `η ∈ 𝒞_Q(E*)`, a closed global class `𝓔_Q^∨(η)`
with `r_Q 𝓔_Q^∨(η) = η`, `r_P 𝓔_Q^∨(η) = T^∨ η`, `r_B 𝓔_Q^∨(η) = 0`; `T^∨` is "the second constant-term map";
neither invertibility nor an adjoint normalization is assumed.

* `jDualCocycle ρ c`: the global class of `E* = E ∘ φ` obtained from a global class `c` of `E` by `Ad_w`, the pullback along
  `ȷ` and the fixed change of coordinates by `w` (`DualJ.jDualGlobal`); it is the model's `phiCocycle`
  (`jDualCocycle_eq_phi`).
* `toLineStar_eq_jDual`, `toPlaneStar_eq_jDual`, `toEdgeStar_eq_jDual`: the transport maps to `E*` on the maximal strata
  and on complete flags, through which `Dual/ConstantTerms` constructs the dual series, are the `ȷ`-pullbacks of the
  conjugated cochains, with the `ȷ`-equivariant flag maps `jFlagLine`, `jFlagPlane`, `jEdge`.
* `jDual_edgeExact`: the dual of a class with zero flag restrictions (edge primitive `w`) has zero flag restrictions, with
  the `ȷ`-pullback of `w` as edge primitive: `r_B 𝓔_Q^∨ = 0`.
* `dual_constant_terms_jmath`: for `n ≥ 4` and every inner plane cocycle `z` of `E`, there is a global class `c = 𝓔_P(z)`
  with zero flag restrictions and inner line restriction whose `ȷ`-dual `𝓔_Q^∨ = jDualCocycle c` has
  `r_Q 𝓔_Q^∨ = [toLineStar z] = [ȷ-pullback of z]` and `r_P 𝓔_Q^∨ = [toPlaneStar (r_Q c)]`, i.e. `T^∨` of the
  `ȷ`-pullback of `ξ` is the `ȷ`-pullback of `T ξ`.
* `dual_series_coordinates_unique`: by graph containment (`Graph.graph_containment_pair`) the coordinates
  `(r_P, r_Q)` of the `ȷ`-dual class do not depend on the choice of `𝓔_P(ξ)`: the second constant-term map `T^∨` is
  well defined on the dual series.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
open TernaryPeriodPolynomials.Argument.FacePairingFull

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)

/-- **The `ȷ`-dual of a global class**: `Ad_w`, pullback along `ȷ`, change of coordinates by `w`. -/
def jDualCocycle (c : cocycles rationalLevel ρ) : cocycles rationalLevel (dualRep ρ) :=
  ⟨jDualGlobal ρ 2 c.val, by
    have h : jDualGlobal ρ 2 c.val = (phiCocycle ρ c).val :=
      Subtype.ext (funext fun x => jDualGlobal_apply ρ 2 c.val x)
    rw [h]
    exact (phiCocycle ρ c).property⟩

/-- The `ȷ`-dual of a global class is the model's `φ`-transport. -/
theorem jDualCocycle_eq_phi (c : cocycles rationalLevel ρ) : jDualCocycle ρ c = phiCocycle ρ c :=
  Subtype.ext (Subtype.ext (funext fun x => jDualGlobal_apply ρ 2 c.val x))

/-- `toLineStar` is the `ȷ`-pullback of the conjugate. -/
theorem toLineStar_eq_jDual (z : cocycles rationalLevel (flagRepresentation ρ .plane)) :
    (toLineStar ρ z).val = jDualFlag ρ 2 jFlagLine jFlagLine_smul z.val :=
  (jDualFlag_eq_transport ρ 2 jFlagLine dualFlag jFlagLine_smul dualFlag_smul
    dualFlag_eq_jFlagLine z.val).symm

/-- `toPlaneStar` is the `ȷ`-pullback of the conjugate. -/
theorem toPlaneStar_eq_jDual (z : cocycles rationalLevel (flagRepresentation ρ .line)) :
    (toPlaneStar ρ z).val = jDualFlag ρ 2 jFlagPlane jFlagPlane_smul z.val :=
  (jDualFlag_eq_transport ρ 2 jFlagPlane dualPlaneFlag jFlagPlane_smul dualPlaneFlag_smul
    dualPlaneFlag_eq_jFlagPlane z.val).symm

/-- `toEdgeStar` is the `ȷ`-pullback of the conjugate. -/
theorem toEdgeStar_eq_jDual (u : cochains rationalLevel (functionRepresentation ρ Edges) 1) :
    toEdgeStar ρ u = jDualFlag ρ 1 jEdge jEdge_smul u :=
  (jDualFlag_eq_transport ρ 1 jEdge dualEdge jEdge_smul dualEdge_smul dualEdge_eq_jEdge u).symm

/-- **`r_B = 0` for the dual series.** A global class with an edge primitive has a `ȷ`-dual with the `ȷ`-pullback of
that edge primitive as edge primitive. -/
theorem jDual_edgeExact (c : cocycles rationalLevel ρ)
    (u : cochains rationalLevel (functionRepresentation ρ Edges) 1)
    (hu : ∀ x e, c.val.val x = differentialOneRaw u.val x e) :
    ∀ x e, (jDualCocycle ρ c).val.val x =
      differentialOneRaw (jDualFlag ρ 1 jEdge jEdge_smul u).val x e := by
  intro x e
  have h0 : (jDualCocycle ρ c).val.val x = c.val.val (fun i => dualInvolution (x i)) :=
    jDualGlobal_apply ρ 2 c.val x
  rw [h0, hu (fun i => dualInvolution (x i)) (dualEdge e)]
  simp only [differentialOneRaw, Pi.add_apply, Pi.sub_apply, jDualFlag_apply, ← dualEdge_eq_jEdge,
    phi_vec2]

/-- An edge-exact global cocycle has inner maximal restrictions (`InnerBoundaryRep`), for any coefficients. -/
theorem innerBoundaryRep_of_edgeExact (σ : Representation ℂ RationalGL3 V)
    (d : cocycles rationalLevel σ) (u : cochains rationalLevel (functionRepresentation σ Edges) 1)
    (hu : ∀ x e, d.val.val x = differentialOneRaw u.val x e) (side : Side) :
    InnerBoundaryRep σ side (classOf rationalLevel (flagRepresentation σ side)
      (restrictionCocycleRep σ side d)) :=
  ⟨restrictionCocycleRep σ side d, rfl, u, fun x e => hu x e⟩

/-- The maximal coordinates of the `ȷ`-dual are the transports of the coordinates. -/
theorem jDual_coordinates (c : cocycles rationalLevel ρ) :
    globalCoordinatesRep (dualRep ρ) (jDualCocycle ρ c) =
      (classOf rationalLevel (flagRepresentation (dualRep ρ) .plane)
          (toPlaneStar ρ (restrictionCocycleRep ρ .line c)),
        classOf rationalLevel (flagRepresentation (dualRep ρ) .line)
          (toLineStar ρ (restrictionCocycleRep ρ .plane c))) := by
  rw [jDualCocycle_eq_phi, toPlaneStar_restriction, toLineStar_restriction]
  rfl

section Sym

variable {n : ℕ}

/-- **The dual series through `ȷ` (`ar:eq:dualconstantterms`).** Let `n ≥ 4` and let `z` be an inner plane cocycle of
`E`. There is a global class `c = 𝓔_P(z)` with zero flag restrictions and inner line restriction such that its `ȷ`-dual
`𝓔_Q^∨ = jDualCocycle c` has zero flag restrictions (`r_B = 0`, with the `ȷ`-pullback of an edge primitive of `c`),
`r_Q 𝓔_Q^∨ = [toLineStar z]` (the `ȷ`-pullback of `z`, `toLineStar_eq_jDual`) and inner `r_P 𝓔_Q^∨ =
[toPlaneStar (r_Q c)] = T^∨ η`. -/
theorem dual_constant_terms_jmath (hn : 4 ≤ n)
    (z : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hz : InnerBoundary n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z)) :
    ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      EdgeExactGlobal c ∧
      (globalCoordinates n trivialCharacter c).1 =
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z ∧
      InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 ∧
      (∃ u : cochains rationalLevel (functionRepresentation
          (dualRep (rationalCoefficientComponent n trivialCharacter)) Edges) 1,
        ∀ x e, (jDualCocycle _ c).val.val x = differentialOneRaw u.val x e) ∧
      (globalCoordinatesRep (dualRep (rationalCoefficientComponent n trivialCharacter))
          (jDualCocycle _ c)).2 =
        classOf rationalLevel
          (flagRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) .line)
          (toLineStar _ z) ∧
      InnerBoundaryRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .plane
        (globalCoordinatesRep (dualRep (rationalCoefficientComponent n trivialCharacter))
          (jDualCocycle _ c)).1 ∧
      InnerBoundaryRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .line
        (globalCoordinatesRep (dualRep (rationalCoefficientComponent n trivialCharacter))
          (jDualCocycle _ c)).2 := by
  obtain ⟨c, hc1, hc2⟩ := TernaryPeriodPolynomials.constant_terms n hn _ hz
  obtain ⟨w, hw⟩ := exists_edgePrimitive_of_line_inner c hc2
  have hedge := jDual_edgeExact (rationalCoefficientComponent n trivialCharacter) c w hw
  refine ⟨c, ⟨w, hw⟩, hc1, hc2, ⟨_, hedge⟩, ?_, ?_, ?_⟩
  · rw [jDual_coordinates]
    exact classOf_transport (rationalCoefficientComponent n trivialCharacter) _ (fun _ => rfl)
      dualFlag dualFlag_smul hc1
  · exact innerBoundaryRep_of_edgeExact _ _ _ hedge .plane
  · exact innerBoundaryRep_of_edgeExact _ _ _ hedge .line

/-- **The second constant-term map is well defined on the dual series.** By graph containment, the maximal
coordinates `(r_P, r_Q)` of the `ȷ`-dual of a class with zero flag restrictions depend only on the plane restriction
of the class: `T^∨` is determined by the construction, with no choice of `𝓔_P(ξ)` and no invertibility or adjoint
normalization. -/
theorem dual_series_coordinates_unique (hn : 4 ≤ n)
    (c c₁ : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : EdgeExactGlobal c) (hc₁ : EdgeExactGlobal c₁)
    (hP : (globalCoordinates n trivialCharacter c).1 = (globalCoordinates n trivialCharacter c₁).1) :
    globalCoordinatesRep (dualRep (rationalCoefficientComponent n trivialCharacter)) (jDualCocycle _ c) =
      globalCoordinatesRep (dualRep (rationalCoefficientComponent n trivialCharacter))
        (jDualCocycle _ c₁) := by
  have hQ := graph_containment_pair hn c c₁ hc hc₁ hP
  rw [jDual_coordinates, jDual_coordinates]
  exact Prod.ext
    (classOf_transport (rationalCoefficientComponent n trivialCharacter) _ (fun _ => rfl)
      dualPlaneFlag dualPlaneFlag_smul hQ)
    (classOf_transport (rationalCoefficientComponent n trivialCharacter) _ (fun _ => rfl)
      dualFlag dualFlag_smul hP)

end Sym

end TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ
