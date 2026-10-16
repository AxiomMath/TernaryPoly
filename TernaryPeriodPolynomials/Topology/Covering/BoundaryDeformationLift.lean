module

public import TernaryPeriodPolynomials.SymmetricSpace.BoundaryNeighborhood.Homotopy
public import TernaryPeriodPolynomials.Topology.InwardHomotopyCovering

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringBoundaryDeformation
open scoped unitInterval
variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
  {p : E → B} (hp : IsCoveringMap p) {A W : Set B}
  (d : BoundaryNeighborhood.Deformation A W)

/-- The genuine covering-homotopy lift of the pulled-back deformation, starting at id_E. -/
def lift : C(I × E, E) :=
  InwardHomotopyCovering.liftedHomotopy hp d.homotopy d.zero

theorem lift_projection (t : I) (x : E) : p (lift hp d (t, x)) = d.homotopy (t, p x) :=
  InwardHomotopyCovering.liftedHomotopy_projection hp d.homotopy d.zero t x

@[simp] theorem lift_zero (x : E) : lift hp d (0, x) = x :=
  InwardHomotopyCovering.liftedHomotopy_zero hp d.homotopy d.zero x

/-- Uniqueness of path lifts forces fixation of every point lying over A. -/
theorem lift_fixed (t : I) (x : E) (hx : x ∈ p ⁻¹' A) : lift hp d (t, x) = x := by
  have he := hp.eq_of_comp_eq
    ((lift hp d).continuous.comp (continuous_id.prodMk continuous_const)) continuous_const
    (g₁ := fun s : I => lift hp d (s, x)) (g₂ := fun _ : I => x) ?_ 0 (lift_zero hp d x)
  · exact congr_fun he t
  · funext s
    exact (lift_projection hp d s x).trans (d.fixes s (p x) hx)

/-- Preservation of W downstairs is literal preservation of its inverse image upstairs. -/
theorem lift_preserves (t : I) (x : E) (hx : x ∈ p ⁻¹' W) : lift hp d (t, x) ∈ p ⁻¹' W := by
  change p (lift hp d (t, x)) ∈ W
  rw [lift_projection hp d]
  exact d.preserves t (p x) hx

/-- A time-one neighborhood collapse lifts to the exact inverse-image neighborhoods. -/
theorem lift_endpoint (N : Set B) (hNA : ∀ y ∈ N, d.homotopy (1, y) ∈ A)
    (x : E) (hx : x ∈ p ⁻¹' N) : lift hp d (1, x) ∈ p ⁻¹' A := by
  change p (lift hp d (1, x)) ∈ A
  rw [lift_projection hp d]
  exact hNA (p x) hx

/-- The lifted map is a genuine upstairs boundary-fixing, neighborhood-preserving deformation. -/
def liftedDeformation : BoundaryNeighborhood.Deformation (p ⁻¹' A) (p ⁻¹' W) where
  homotopy := lift hp d
  zero := lift_zero hp d
  fixes := lift_fixed hp d
  preserves := lift_preserves hp d

/-- The lifted endpoint is the actual continuous map to the boundary inverse image. -/
def retraction (N : Set B) (hNA : ∀ y ∈ N, d.homotopy (1, y) ∈ A) :
    C(p ⁻¹' N, p ⁻¹' A) :=
  BoundaryNeighborhood.endpointRetraction (liftedDeformation hp d) (p ⁻¹' N)
    (lift_endpoint hp d N hNA)

/-- The literal neighborhood-cover inclusion is homotopic inside the W-cover to a map
factoring through the boundary cover. -/
def neighborhoodHomotopy (N : Set B) (hNW : N ⊆ W) (hAW : A ⊆ W)
    (hNA : ∀ y ∈ N, d.homotopy (1, y) ∈ A) :
    ContinuousMap.Homotopy
      (⟨fun y : p ⁻¹' N => (⟨y.val, hNW y.property⟩ : p ⁻¹' W),
        continuous_subtype_val.subtype_mk _⟩ : C(p ⁻¹' N, p ⁻¹' W))
      ((⟨fun y : p ⁻¹' A => (⟨y.val, hAW y.property⟩ : p ⁻¹' W),
        continuous_subtype_val.subtype_mk _⟩ : C(p ⁻¹' A, p ⁻¹' W)).comp
        (retraction hp d N hNA)) :=
  BoundaryNeighborhood.endpointHomotopy (liftedDeformation hp d) (p ⁻¹' N)
    (Set.preimage_mono hNW) (Set.preimage_mono hAW) (lift_endpoint hp d N hNA)

end TernaryPoly.CoveringBoundaryDeformation
