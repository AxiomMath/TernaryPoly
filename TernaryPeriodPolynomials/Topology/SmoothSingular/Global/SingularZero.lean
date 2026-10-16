module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularLocalExactness

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Opposite TopologicalSpace Set HomologicalComplex
open SymmetricSpaceCovering FreeActionLinearization
open scoped Simplicial
variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- Actual coefficient sections are determined by their literal singular zero-cochain. -/
theorem coefficientSingularMap_injective (U : Set OrbitSpace) :
    Function.Injective (coefficientSingularMap ρ U) := by
  intro f g h
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  let σ : SingularSimplex (TopCat.of (CoverOpen U)) 0 :=
    (TopCat.toSSetObjEquiv _ (.op ⦋0⦌)).symm (ContinuousMap.const _ x)
  have he := congrArg (fun c =>
    cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen U)) (Rep.of ρ) 0 c σ) h
  rw [coefficientSingularMap_eval, coefficientSingularMap_eval] at he
  simpa only [σ, Equiv.apply_symm_apply, ContinuousMap.const_apply] using he

/-- The true coefficient-to-singular presheaf augmentation is a monomorphism. -/
instance coefficientToSingular_mono : Mono (coefficientToSingular ρ) := by
  have : ∀ U, Mono ((coefficientToSingular ρ).app U) := fun U =>
    (ModuleCat.mono_iff_injective _).mpr (coefficientSingularMap_injective ρ U.unop)
  exact NatTrans.mono_of_mono_app _

/-- On a genuine locally contractible frame, degree-zero singular cocycles are exactly
actual locally constant coefficient sections. -/
theorem coveringSingular_zero_exact {U : Set OrbitSpace}
    [QuasiIso (coveringSingularAugmentation ρ U)] :
    (ShortComplex.mk (ModuleCat.ofHom (coefficientSingularMap ρ U))
      ((coveringCochains ρ U).d 0 1) (by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        exact coefficientSingularMap_closed ρ U)).Exact := by
  have h : QuasiIsoAt (coveringSingularAugmentation ρ U) 0 := inferInstance
  rw [CochainComplex.quasiIsoAt₀_iff] at h
  rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp; rfl) (by simp; rfl) (by simp; rfl)] at h
  have ha : (coveringSingularAugmentation ρ U).f 0 =
      ModuleCat.ofHom (coefficientSingularMap ρ U) :=
    SmoothSingularComparison.augmentation_f_zero _ _
  simp only [shortComplexFunctor', ha, CochainComplex.single₀_obj_zero] at h
  exact h.1

/-- Every actual closed singular zero-cochain is locally the literal augmentation of an
actual locally constant coefficient section. -/
theorem singular_zero_local_lifting {U : Set OrbitSpace} (hU : IsOpen U) {q : OrbitSpace}
    (hq : q ∈ U) (w : (coveringCochains ρ U).X 0)
    (hw : (coveringCochains ρ U).d 0 1 w = 0) :
    ∃ V : Opens (TopCat.of OrbitSpace), q ∈ V ∧ ∃ hVU : (V : Set OrbitSpace) ⊆ U,
      ∃ z : coefficientSections ρ (V : Set OrbitSpace),
        coefficientSingularMap ρ (V : Set OrbitSpace) z =
          (coveringCochainRestriction ρ hVU).f 0 w := by
  obtain ⟨V, hqV, hVU, hQI⟩ := coveringSingularAugmentation_local_quasiIso ρ hU hq
  have : QuasiIso (coveringSingularAugmentation ρ (V : Set OrbitSpace)) := hQI
  have hc := congrArg (fun m => m.hom w) ((coveringCochainRestriction ρ hVU).comm 0 1)
  change (coveringCochains ρ (V : Set OrbitSpace)).d 0 1
    ((coveringCochainRestriction ρ hVU).f 0 w) =
    (coveringCochainRestriction ρ hVU).f 1 ((coveringCochains ρ U).d 0 1 w) at hc
  have hz := hc.trans ((congrArg ((coveringCochainRestriction ρ hVU).f 1) hw).trans (map_zero _))
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (coveringSingular_zero_exact ρ (U := V)) _ hz
  exact ⟨V, hqV, hVU, z, hz⟩

end TernaryPoly.SmoothSingularGlobal
