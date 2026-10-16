module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.HomeomorphSupport
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMap

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCapHomeomorph
open CategoryTheory Limits HomologicalComplex
open SingularLocalConstant SingularLocalCap SingularLocalCompactCap SingularLocalSupport
open RationalLocalOrientation RationalManifoldCompact RationalHomologyCoefficients

variable {X Y : TopCat.{0}} (h : X ≃ₜ Y) (V : ModuleCat.{0} ℚ)

/-- The actual support cap commutes with genuine homeomorphism pullback and pushforward. -/
theorem supportCap_natural (K : Set Y) (a b : ℕ)
    (φ : (supportCochains (𝟙 Y) (constantRep V) K).X a)
    (c : (supportChains (h ⁻¹' K)).X (a+b)) :
    (chainPushforward h V).f b
      (supportCap (𝟙 X) (constantRep V) (h ⁻¹' K) a b ((supportCochainIso h V K).hom.f a φ) c) =
      supportCap (𝟙 Y) (constantRep V) K a b φ ((supportPullbackIso h K).hom.f (a+b) c) := by
  obtain ⟨c,rfl⟩ := RelativeAlgebra.projection_surjective
    (RationalRelativeSingular.inclusion (h ⁻¹' K)ᶜ) (a+b) c
  have hc := congrArg (fun f => f.f (a+b) c) (supportPullback_projection h K)
  change (supportPullbackIso h K).hom.f (a+b)
    ((cokernel.π (RationalRelativeSingular.inclusion (h ⁻¹' K)ᶜ)).f (a+b) c) =
      (cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f (a+b)
        ((RationalRelativeSingular.chainHomeomorphIso h).hom.f (a+b) c) at hc
  rw [hc,supportCap_projection,supportCap_projection]
  have hφ := congrArg (fun f => f.f a φ) (supportCochainIso_inclusion h V K)
  change (supportInclusion (𝟙 X) (constantRep V) (h ⁻¹' K)).f a
    ((supportCochainIso h V K).hom.f a φ) =
      (cochainPullback h V).f a ((supportInclusion (𝟙 Y) (constantRep V) K).f a φ) at hφ
  rw [hφ]
  exact cap_natural (𝟙 X) (𝟙 Y) (TopCat.ofHom ⟨h,h.continuous⟩) (TopCat.ofHom ⟨h,h.continuous⟩)
    (by simp) (identityCover X) (identityCover Y) (fun _ _ => rfl) (constantRep V) a b _ c

/-- Homeomorphism naturality descends to actual support cohomology and support homology classes. -/
theorem supportCapHomology_natural (K : Set Y) (a b : ℕ)
    (φ : (supportCochains (𝟙 Y) (constantRep V) K).homology a)
    (c : (supportChains (h ⁻¹' K)).homology (a+b)) :
    homologyMap (chainPushforward h V) b
      (supportCapHomology (𝟙 X) (constantRep V) (h ⁻¹' K) a b
        (homologyMap (supportCochainIso h V K).hom a φ) c) =
      supportCapHomology (𝟙 Y) (constantRep V) K a b φ
        (homologyMap (supportPullbackIso h K).hom (a+b) c) := by
  obtain ⟨φ,rfl⟩ := Algebra.cochainClass_surjective _ a φ
  obtain ⟨c,rfl⟩ := Algebra.chainClass_surjective _ (a+b) c
  rw [Algebra.cochainClass_natural (supportCochainIso h V K).hom a φ
    (mapComplexCycle (supportCochainIso h V K).hom (a-1) a (a+1) φ) rfl,
    Algebra.chainClass_natural (supportPullbackIso h K).hom (a+b) c
    (mapComplexCycle (supportPullbackIso h K).hom (a+b+1) (a+b) (a+b-1) c) rfl,
    supportCapHomology_representatives,supportCapHomology_representatives]
  apply Algebra.chainClass_natural
  exact (supportCap_natural h V K a b φ.val c.val).symm

end TernaryPoly.SingularLocalCapHomeomorph
