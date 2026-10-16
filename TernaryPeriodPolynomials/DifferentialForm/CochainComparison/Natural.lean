module

public import TernaryPeriodPolynomials.DifferentialForm.CochainComparison.Bridge
public import TernaryPeriodPolynomials.EisensteinSeries.Class.DeRhamNatural

@[expose] public section


/-!
# The triangle cochain of a pulled-back form represents the class of the original form

Formalized by Claude Sonnet 5.5.
Paper: Appendix C.

Let `φ : s → t` be a smooth map equivariant for the same group `G` (change of coordinates, `α = id`), with `G` acting by affine
maps on the open convex set `s` (a Gram cone) and arbitrarily on the target `t` (the symmetric space chart `Ω`).  For a closed
`G`-equivariant `2`-form `ω` on `t`, the triangle cochain of the pullback `φ^*ω` over affine triangles of `s` is a
`2`-cocycle whose class is the de Rham class of `ω` (`bridge_pullback`): the combination of the bridge
`bridge_triangleCochain_eq_deRhamClass` with the naturality `EisensteinClass.deRhamClass_natural`.
-/

open CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormCochainBridge

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.EisensteinClass

variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
  {s : Set D} {t : Set E} {G : Type} [Group G]

omit [FiniteDimensional ℝ D] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [CompleteSpace F]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `H²(id)` for the identity coefficient comparison is the identity. -/
theorem map_id_resMor (ρ : Representation ℝ G F) (x : H2 (Rep.of ρ)) :
    (map (MonoidHom.id G) (resMor (MonoidHom.id G) ρ ρ (fun _ => rfl)) 2).hom x = x := by
  induction x using H2_induction_on with
  | h z =>
    rw [H2π_comp_map_apply]
    rfl

/-- **Bridge for a pulled-back form**: the class of the triangle cochain of `φ^*ω` over affine triangles of the source is
the de Rham class of `ω`. -/
theorem bridge_pullback {hs : IsOpen s} {ht : IsOpen t} {A : ZigZag.Action G s} {B : ZigZag.Action G t}
    (𝔄 : AffineAction A) (Φ : EquivMap hs ht A B (MonoidHom.id G)) (hc : Convex ℝ s) (hne : s.Nonempty)
    (hc' : Convex ℝ t) (hne' : t.Nonempty) {ρ : Representation ℝ G F}
    (ω : ZigZag.invClosed ht B ρ) {x₀ : D} (hx₀ : x₀ ∈ s) :
    (H2π (Rep.of ρ)).hom ⟨_, isCocycle_inhomTriangle hs A ρ hc hne 𝔄 (pullInv Φ (fun _ => rfl) ω) hx₀⟩ =
      ZigZag.deRhamClass ht hc' hne' B ρ ω := by
  rw [bridge_triangleCochain_eq_deRhamClass hs hc hne A ρ 𝔄 (pullInv Φ (fun _ => rfl) ω) hx₀,
    deRhamClass_natural Φ hc hne hc' hne' (fun _ => rfl) ω, map_id_resMor]

end TernaryPeriodPolynomials.Argument.FormCochainBridge
