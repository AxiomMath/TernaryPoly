module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.HomeomorphAlgebra
public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapSupportComplex
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Naturality
public import TernaryPeriodPolynomials.Topology.Rational.Local.OrientationHomeomorph

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCapHomeomorph
open CategoryTheory Limits HomologicalComplex
open SingularLocalConstant SingularLocalCoefficient SingularLocalHomology SingularCoverNaturality
open SingularLocalCap SingularLocalCapNormalization FreeActionLinearization CoveringSingularOrbits
open EuclideanCompactCap RationalLocalOrientation

variable {X Y : TopCat.{0}} (h : X ≃ₜ Y) (V : ModuleCat.{0} ℚ)

/-- The actual local chain pushforward of the identity-cover homeomorphism square. -/
abbrev chainPushforward : chains X V ⟶ chains Y V :=
  localSpaceMap (TopCat.ofHom ⟨h,h.continuous⟩) (fun _ _ => rfl) (constantRep V)
    (𝟙 X) (𝟙 Y) (identityCover X) (identityCover Y)

/-- The actual geometric cochain pullback of the identity-cover homeomorphism square. -/
abbrev cochainPullback : cochains Y V ⟶ cochains X V :=
  localPullback (𝟙 X) (𝟙 Y) (TopCat.ofHom ⟨h,h.continuous⟩) (TopCat.ofHom ⟨h,h.continuous⟩)
    (by simp) (identityCover X) (identityCover Y) (fun _ _ => rfl) (constantRep V)

/-- Literal cochain pullback evaluates on the actual image scalar chain. -/
theorem evaluation_pullback (a : ℕ) (φ : (cochains Y V).X a) (c : (scalarChains X).X a) :
    evaluation X V a ((cochainPullback h V).f a φ) c =
      evaluation Y V a φ ((RationalRelativeSingular.chainHomeomorphIso h).hom.f a c) := by
  have hh : evaluation X V a ((cochainPullback h V).f a φ) =
      (evaluation Y V a φ).comp ((RationalRelativeSingular.chainHomeomorphIso h).hom.f a).hom := by
    apply scalarChain_ext
    intro σ
    rw [LinearMap.comp_apply]
    change evaluation X V a _ (SphereOddDegree.AffineBarycentricSubdivision.chainGenerator ℚ X a σ) =
      evaluation Y V a φ ((scalarSpaceMap (TopCat.ofHom ⟨h,h.continuous⟩)).f a _)
    rw [scalarSpaceMap_generator]
    erw [evaluation_generator,evaluation_generator]
    rfl
  exact LinearMap.congr_fun hh c

/-- The actual identity-cover chain pushforward is an isomorphism. -/
theorem chainPushforward_isIso : IsIso (chainPushforward h V) := by
  let F : X ⟶ Y := TopCat.ofHom ⟨h,h.continuous⟩
  let H : Y ⟶ X := TopCat.ofHom ⟨h.symm,h.symm.continuous⟩
  have hFH : F ≫ H = 𝟙 X := by ext x; exact h.symm_apply_apply x
  have hHF : H ≫ F = 𝟙 Y := by ext y; exact h.apply_symm_apply y
  have hi : IsIso (SingularCoverNaturality.chainMap (G := Unit) F (fun _ _ => rfl)) := by
    refine ⟨SingularCoverNaturality.chainMap H (fun _ _ => rfl),?_,?_⟩
    · rw [← SingularCoverNaturality.chainMap_comp]
      simpa only [hFH] using (SingularCoverNaturality.chainMap_id (G := Unit) (E := X))
    · rw [← SingularCoverNaturality.chainMap_comp]
      simpa only [hHF] using (SingularCoverNaturality.chainMap_id (G := Unit) (E := Y))
  change IsIso ((chainIso (𝟙 X) (identityCover X) (constantRep V)).inv ≫
    coinvariantSpaceMap F (fun _ _ => rfl) (constantRep V) ≫
      (chainIso (𝟙 Y) (identityCover Y) (constantRep V)).hom)
  unfold coinvariantSpaceMap
  infer_instance

/-- The actual homeomorphism map on local homology, with its literal forward map. -/
def homologyIso (b : ℕ) : (chains X V).homology b ≅ (chains Y V).homology b := by
  have := chainPushforward_isIso h V
  exact (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) b).mapIso (asIso (chainPushforward h V))

end TernaryPoly.SingularLocalCapHomeomorph
