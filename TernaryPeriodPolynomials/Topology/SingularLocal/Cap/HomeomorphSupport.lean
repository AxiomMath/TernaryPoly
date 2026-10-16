module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.HomeomorphMaps

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCapHomeomorph
open CategoryTheory Limits HomologicalComplex
open SingularLocalConstant SingularLocalCap SingularLocalCapNormalization SingularLocalSupport
open EuclideanCompactCap RationalLocalOrientation RationalHomologyCoefficients

variable {X Y : TopCat.{0}} (h : X ≃ₜ Y) (V : ModuleCat.{0} ℚ)

/-- The genuine fixed-support cochain pullback isomorphism, through literal relative-chain evaluation. -/
def supportCochainIso (K : Set Y) : supportCochains (𝟙 Y) (constantRep V) K ≅
    supportCochains (𝟙 X) (constantRep V) (h ⁻¹' K) :=
  supportHomCochainIso Y V K ≪≫ homCochainsIso (supportPullbackIso h K) V ≪≫
    (supportHomCochainIso X V (h ⁻¹' K)).symm

/-- Fixed-support pullback evaluates on the actual homeomorphism image of a relative chain. -/
theorem supportEvaluation_pullback (K : Set Y) (a : ℕ)
    (φ : (supportCochains (𝟙 Y) (constantRep V) K).X a)
    (c : (RationalManifoldCompact.supportChains (h ⁻¹' K)).X a) :
    supportEvaluation X V (h ⁻¹' K) a ((supportCochainIso h V K).hom.f a φ) c =
      supportEvaluation Y V K a φ ((supportPullbackIso h K).hom.f a c) := by
  have hh : (supportCochainIso h V K).hom ≫ (supportHomCochainIso X V (h ⁻¹' K)).hom =
      (supportHomCochainIso Y V K).hom ≫ homCochainsMap (supportPullbackIso h K).hom V := by
    simp [supportCochainIso,homCochainsIso]
  exact congrArg (fun f => (f.f a φ) c) hh

/-- Relative chain transport keeps the actual homeomorphism image of every ambient representative. -/
theorem supportPullback_projection (K : Set Y) :
    cokernel.π (RationalRelativeSingular.inclusion (h ⁻¹' K)ᶜ) ≫ (supportPullbackIso h K).hom =
      (RationalRelativeSingular.chainHomeomorphIso h).hom ≫
        cokernel.π (RationalRelativeSingular.inclusion Kᶜ) := by
  simp only [supportPullbackIso,RationalRelativeSingular.relativeHomeomorphIso,
    cokernel.mapIso,cokernel.map,cokernel.π_desc]

/-- Fixed-support pullback has exactly the actual geometric pullback as its ambient cochain. -/
theorem supportCochainIso_inclusion (K : Set Y) :
    (supportCochainIso h V K).hom ≫ supportInclusion (𝟙 X) (constantRep V) (h ⁻¹' K) =
      supportInclusion (𝟙 Y) (constantRep V) K ≫ cochainPullback h V := by
  apply HomologicalComplex.hom_ext
  intro a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply (cochainHomEquiv X V a).injective
  apply LinearMap.ext
  intro c
  change evaluation X V a ((supportInclusion (𝟙 X) (constantRep V) (h ⁻¹' K)).f a
      ((supportCochainIso h V K).hom.f a φ)) c =
    evaluation X V a ((cochainPullback h V).f a ((supportInclusion (𝟙 Y) (constantRep V) K).f a φ)) c
  rw [evaluation_pullback,← supportEvaluation_projection,supportEvaluation_pullback]
  have hc := congrArg (fun f => f.f a c) (supportPullback_projection h K)
  change (supportPullbackIso h K).hom.f a
    ((cokernel.π (RationalRelativeSingular.inclusion (h ⁻¹' K)ᶜ)).f a c) =
      (cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f a
        ((RationalRelativeSingular.chainHomeomorphIso h).hom.f a c) at hc
  rw [hc,supportEvaluation_projection]

/-- Genuine support pullback commutes with the actual support-enlargement maps. -/
theorem supportCochainIso_natural (K L : Set Y) (hKL : K ⊆ L) :
    supportMap (𝟙 Y) (constantRep V) K L hKL ≫ (supportCochainIso h V L).hom =
      (supportCochainIso h V K).hom ≫
        supportMap (𝟙 X) (constantRep V) (h ⁻¹' K) (h ⁻¹' L) (Set.preimage_mono hKL) := by
  apply (cancel_mono (supportInclusion (𝟙 X) (constantRep V) (h ⁻¹' L))).mp
  rw [Category.assoc,supportCochainIso_inclusion,← Category.assoc,supportMap_inclusion,
    Category.assoc,supportMap_inclusion,supportCochainIso_inclusion]

end TernaryPoly.SingularLocalCapHomeomorph
