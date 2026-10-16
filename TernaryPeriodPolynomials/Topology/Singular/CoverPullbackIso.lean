module

public import TernaryPeriodPolynomials.Topology.Singular.CoverPullbackComposition

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularCoverNaturality
open CategoryTheory SingularLocalCoefficient

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']

/-- Pullback by an equivariant homeomorphism is an actual cochain isomorphism. -/
theorem cochainPullback_isIso_of_inverse (F : E ⟶ E') (H : E' ⟶ E)
    (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
    (hH : ∀ (g : G) (x : E'), H (g • x) = g • H x)
    (hFH : F ≫ H = 𝟙 E) (hHF : H ≫ F = 𝟙 E') (V : Rep.{0} ℚ G) :
    IsIso (cochainPullback F hF V) := by
  refine ⟨cochainPullback H hH V,?_,?_⟩
  · rw [← cochainPullback_comp]
    simpa only [hHF] using cochainPullback_id (G := G) (E := E') V
  · rw [← cochainPullback_comp]
    simpa only [hFH] using cochainPullback_id (G := G) (E := E) V

/-- If the actual equivariant singular pullback is an isomorphism, so is the corresponding
geometric local-cochain map, with its literal coefficient transports. -/
theorem localPullback_isIso (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
    (hs : F ≫ p' = p ≫ f) (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
    (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G)
    [IsIso (cochainPullback F hF V)] : IsIso (localPullback p p' F f hs hp hp' hF V) := by
  have he : localPullback p p' F f hs hp hp' hF V =
      (cochainIso p' hp' V).inv ≫ cochainPullback F hF V ≫ (cochainIso p hp V).hom := by
    rw [cochainIso_pullback,Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

end TernaryPoly.SingularCoverNaturality
