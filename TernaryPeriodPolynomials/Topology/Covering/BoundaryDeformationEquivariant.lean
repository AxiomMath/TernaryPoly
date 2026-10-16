module

public import TernaryPeriodPolynomials.Topology.Covering.BoundaryDeformationLift

@[expose] public section

noncomputable section
namespace TernaryPoly.CoveringBoundaryDeformation
open scoped unitInterval
variable {E B G : Type*} [TopologicalSpace E] [TopologicalSpace B] [Group G]
  [MulAction G E] [ContinuousConstSMul G E]
  {p : E → B} (hp : IsCoveringMap p) (hdeck : ∀ (g : G) x, p (g • x) = p x)
  {A W : Set B} (d : BoundaryNeighborhood.Deformation A W)

include hdeck in
/-- Uniqueness of lifted paths makes the genuine covering homotopy deck-equivariant. -/
theorem lift_equivariant (g : G) (t : I) (x : E) :
    lift hp d (t, g • x) = g • lift hp d (t, x) := by
  have he := hp.eq_of_comp_eq
    ((lift hp d).continuous.comp (continuous_id.prodMk continuous_const))
    ((continuous_const_smul g).comp
      ((lift hp d).continuous.comp (continuous_id.prodMk continuous_const)))
    (g₁ := fun s : I => lift hp d (s, g • x))
    (g₂ := fun s : I => g • lift hp d (s, x)) ?_ 0 ?_
  · exact congr_fun he t
  · funext s
    change p (lift hp d (s, g • x)) = p (g • lift hp d (s, x))
    rw [hdeck, lift_projection hp d, lift_projection hp d, hdeck]
  · rw [lift_zero, lift_zero]

/-- Every inverse-image set has its literal induced deck action. -/
abbrev preimageAction (S : Set B) : MulAction G (p ⁻¹' S) where
  smul g x := ⟨g • x.val, by change p (g • x.val) ∈ S; rw [hdeck]; exact x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

/-- Constant deck transformations are continuous on every inverse-image subspace. -/
abbrev preimageContinuous (S : Set B) :
    letI := preimageAction hdeck S
    ContinuousConstSMul G (p ⁻¹' S)  := by
  let := preimageAction hdeck S
  exact ⟨fun g => ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩

include hdeck in
/-- The package's entire lifted deformation is equivariant at every time. -/
theorem liftedDeformation_equivariant (g : G) (t : I) (x : E) :
    (liftedDeformation hp d).homotopy (t, g • x) =
      g • (liftedDeformation hp d).homotopy (t, x) :=
  lift_equivariant hp hdeck d g t x

end TernaryPoly.CoveringBoundaryDeformation
