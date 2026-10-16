module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryPairAlgebra
public import TernaryPeriodPolynomials.SymmetricSpace.BoundaryNeighborhood.Homotopy

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory HomologicalComplex EquivariantSingularSmall EquivariantSingularPairHomotopy
open scoped unitInterval
variable {G : Type} [Group G] {E : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (A W : Set E) [Fact (InvariantSet G E A)] [Fact (InvariantSet G E W)]
  (d : BoundaryNeighborhood.Deformation A W)
  (hd : ∀ (g : G) t x, d.homotopy (t,g • x) = g • d.homotopy (t,x))

/-- The actual endpoint of the equivariant ambient boundary deformation. -/
def deformationEndpoint : E ⟶ E :=
  TopCat.ofHom ⟨fun x => d.homotopy (1,x),d.homotopy.continuous.comp (continuous_const.prodMk continuous_id)⟩

omit [Fact (InvariantSet G E A)] [Fact (InvariantSet G E W)] [ContinuousConstSMul G E] in
include hd in
/-- The ambient endpoint remains equivariant under the literal deck action. -/
theorem deformationEndpoint_equivariant (g : G) (x : E) :
    deformationEndpoint A W d (g • x) = g • deformationEndpoint A W d x := hd g 1 x

/-- The supplied ambient deformation is the genuine homotopy from identity to its endpoint. -/
def deformationAmbientHomotopy : TopCat.Homotopy (𝟙 E) (deformationEndpoint A W d) :=
  ⟨d.homotopy,d.zero,fun _ => rfl⟩

variable (N : Set E) [Fact (InvariantSet G E N)] (hAN : A ⊆ N)
  (hNA : ∀ x ∈ N, d.homotopy (1,x) ∈ A) (V : Rep.{0} ℚ G)

/-- The actual relative support-enlargement map to boundary-relative Hom cochains. -/
def relativeToBoundary : relativeHomCochains G E N V ⟶ relativeHomCochains G E A V :=
  relativeHomPullback A N (𝟙 E) (fun _ _ => rfl) (fun _ hx => hAN hx) V

/-- Pullback by the actual ambient endpoint lifts a boundary-relative cochain to the
smaller-neighborhood-relative Hom complex. -/
def relativeFromBoundary : relativeHomCochains G E A V ⟶ relativeHomCochains G E N V :=
  relativeHomPullback N A (deformationEndpoint A W d) (deformationEndpoint_equivariant A W d hd) hNA V

omit [Fact (InvariantSet G E W)] in
/-- On actual relative Hom cohomology, endpoint lifting followed by boundary restriction is identity. -/
theorem relativeFromBoundary_retraction (k : ℕ) :
    homologyMap (relativeFromBoundary A W d hd N hNA V) k ≫
      homologyMap (relativeToBoundary A N hAN V) k = 𝟙 _ := by
  have hh := relativeHomCohomologyMap_eq A A (fun _ _ => rfl)
    (deformationEndpoint_equivariant A W d hd) (fun _ hx => hx)
    (fun x hx => hNA x (hAN hx)) (deformationAmbientHomotopy A W d) hd
    (fun t x hx => by change d.homotopy (t,x) ∈ A; rw [d.fixes t x hx]; exact hx) V k
  rw [relativeHomPullback_id,homologyMap_id] at hh
  unfold relativeFromBoundary relativeToBoundary
  erw [← homologyMap_comp,relativeHomPullback_comp]
  simpa only [Category.id_comp] using hh.symm

/-- The actual support-enlargement map from W-relative to N-relative Hom cochains. -/
def relativeNeighborhoodTransition (hNW : N ⊆ W) :
    relativeHomCochains G E W V ⟶ relativeHomCochains G E N V :=
  relativeHomPullback N W (𝟙 E) (fun _ _ => rfl) (fun _ hx => hNW hx) V

/-- Boundary restriction followed by the actual endpoint lift equals genuine neighborhood
restriction on cohomology. This uses preservation of W, not preservation of N. -/
theorem relativeFromBoundary_transition (hAW : A ⊆ W) (hNW : N ⊆ W) (k : ℕ) :
    homologyMap (relativeToBoundary A W hAW V) k ≫
      homologyMap (relativeFromBoundary A W d hd N hNA V) k =
        homologyMap (relativeNeighborhoodTransition W N V hNW) k := by
  have hh := relativeHomCohomologyMap_eq N W (fun _ _ => rfl)
    (deformationEndpoint_equivariant A W d hd) (fun _ hx => hNW hx)
    (fun x hx => hAW (hNA x hx)) (deformationAmbientHomotopy A W d) hd
    (fun t x hx => d.preserves t x (hNW hx)) V k
  unfold relativeFromBoundary relativeToBoundary relativeNeighborhoodTransition
  erw [← homologyMap_comp,relativeHomPullback_comp]
  simpa only [Category.comp_id] using hh.symm

end TernaryPoly.CompactInteriorRelativeBoundary
