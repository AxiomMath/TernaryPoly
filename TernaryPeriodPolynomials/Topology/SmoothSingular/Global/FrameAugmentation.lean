module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FrameConstants

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits HomologicalComplex
open SymmetricSpaceCovering
variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {U : Set OrbitSpace} {Y : TopCat.{0}} (T : SingularFrame DeckGroup (TopCat.of (CoverOpen U)) Y)

/-- The actual constant-frame coefficient map is an isomorphism on a connected frame. -/
instance frameConstantMap_isIso [ConnectedSpace Y] : IsIso (ModuleCat.ofHom (frameConstantMap ρ T)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (frameConstantMap_bijective ρ T)

/-- The actual constant-frame coefficient value as a genuine equivariant singular zero-cochain. -/
def frameSingularConstant : ModuleCat.of ℝ F ⟶ (coveringCochains ρ U).X 0 :=
  ModuleCat.ofHom ((coefficientSingularMap ρ U).comp (frameConstantMap ρ T))

/-- The actual constant-frame singular cochain is closed. -/
theorem frameSingularConstant_closed : frameSingularConstant ρ T ≫ (coveringCochains ρ U).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact coefficientSingularMap_closed ρ U (frameConstantMap ρ T c)

/-- The true constant-frame augmentation of the actual equivariant singular complex. -/
def frameSingularAugmentation : (CochainComplex.single₀ (ModuleCat ℝ)).obj (ModuleCat.of ℝ F) ⟶
    coveringCochains ρ U :=
  SmoothSingularComparison.augmentation (frameSingularConstant ρ T) (frameSingularConstant_closed ρ T)

/-- The actual frame isomorphism sends its true constant augmentation to ordinary singular constants. -/
theorem frameSingularAugmentation_compare :
    frameSingularAugmentation ρ T ≫ frameCochainRestriction T (Rep.of ρ) =
      SmoothSingularComparison.singularAugmentation Y (ModuleCat.of ℝ F) := by
  have hb : ModuleCat.ofHom (SmoothSingularComparison.singularConstant Y (ModuleCat.of ℝ F)) ≫
      (SmoothSingularComparison.realSingularCochains Y (ModuleCat.of ℝ F)).d 0 1 = 0 := by
    rw [SmoothSingularComparison.realHom_d]
    apply ModuleCat.hom_ext
    exact SmoothSingularComparison.singularConstant_closed Y (ModuleCat.of ℝ F)
  have h := SmoothSingularComparison.augmentation_natural
    (frameSingularConstant ρ T) (frameSingularConstant_closed ρ T)
    (ModuleCat.ofHom (SmoothSingularComparison.singularConstant Y (ModuleCat.of ℝ F))) hb
    (𝟙 (ModuleCat.of ℝ F)) (frameCochainRestriction T (Rep.of ρ)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact frameCochainRestriction_constant ρ T c)
  exact h.trans ((congrArg (fun k => k ≫ SmoothSingularComparison.augmentation _ hb)
    ((CochainComplex.single₀ (ModuleCat ℝ)).map_id (ModuleCat.of ℝ F))).trans (Category.id_comp _))

/-- The true local constant augmentation factors through the actual coefficient-sheaf sections. -/
theorem frameSingularAugmentation_factor : frameSingularAugmentation ρ T =
    (CochainComplex.single₀ (ModuleCat ℝ)).map (ModuleCat.ofHom (frameConstantMap ρ T)) ≫
      coveringSingularAugmentation ρ U := by
  have hb : ModuleCat.ofHom (coefficientSingularMap ρ U) ≫ (coveringCochains ρ U).d 0 1 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact coefficientSingularMap_closed ρ U f
  have h := SmoothSingularComparison.augmentation_natural
    (frameSingularConstant ρ T) (frameSingularConstant_closed ρ T)
    (ModuleCat.ofHom (coefficientSingularMap ρ U)) hb
    (ModuleCat.ofHom (frameConstantMap ρ T)) (𝟙 (coveringCochains ρ U)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      rfl)
  exact (Category.comp_id (frameSingularAugmentation ρ T)).symm.trans h

include T in
/-- On a contractible genuine frame, the actual local coefficient augmentation is a quasi-isomorphism. -/
theorem coveringSingularAugmentation_quasiIso [ContractibleSpace Y] :
    QuasiIso (coveringSingularAugmentation ρ U) := by
  have : QuasiIso (frameSingularAugmentation ρ T ≫ frameCochainRestriction T (Rep.of ρ)) := by
    rw [frameSingularAugmentation_compare]
    exact SmoothSingularComparison.singularAugmentation_quasiIso Y (ModuleCat.of ℝ F)
  have : QuasiIso (frameSingularAugmentation ρ T) :=
    quasiIso_of_comp_right _ (frameCochainRestriction T (Rep.of ρ))
  have : QuasiIso ((CochainComplex.single₀ (ModuleCat ℝ)).map
      (ModuleCat.ofHom (frameConstantMap ρ T)) ≫ coveringSingularAugmentation ρ U) := by
    rw [← frameSingularAugmentation_factor ρ T]
    infer_instance
  exact quasiIso_of_comp_left ((CochainComplex.single₀ (ModuleCat ℝ)).map
    (ModuleCat.ofHom (frameConstantMap ρ T))) (coveringSingularAugmentation ρ U)

end TernaryPoly.SmoothSingularGlobal
