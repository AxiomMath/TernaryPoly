module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechZero

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory HomologicalComplex
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Topology ContDiff Manifold
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Set OrbitSpace) (n : ℕ)

/-- The actual global-to-Čech map restricts a genuine form to each cover member. -/
def formCechAugmentationMap : ModuleCat.of ℝ (EquivariantForm ρ Set.univ n) ⟶
    (formCechComplex ρ U n).X 0 :=
  ModuleCat.ofHom ((formCechD ρ U n 0).comp (formCechEmptyEmbed ρ U n))

/-- The actual global-to-Čech map is a genuine cocycle in horizontal degree zero. -/
theorem formCechAugmentationMap_closed : formCechAugmentationMap ρ U n ≫
    (formCechComplex ρ U n).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  exact (congrArg (fun f => f.hom (formCechD ρ U n 0 (formCechEmptyEmbed ρ U n w)))
    (formCechD_eq_complex ρ U n 0)).symm.trans
      (formCechD_one_zero ρ U n (formCechEmptyEmbed ρ U n w))

/-- The genuine global form space augments its actual horizontal Čech complex. -/
def formCechAugmentation :
    (CochainComplex.single₀ (ModuleCat ℝ)).obj (ModuleCat.of ℝ (EquivariantForm ρ Set.univ n)) ⟶
      formCechComplex ρ U n :=
  SmoothSingularComparison.augmentation (formCechAugmentationMap ρ U n)
    (formCechAugmentationMap_closed ρ U n)

variable (hU : ∀ i, IsOpen (U i))
  (φ : SmoothPartitionOfUnity ι 𝓘(ℝ, Coordinates) OrbitSpace Set.univ) (hφ : φ.IsSubordinate U)

include hU φ hφ in
/-- The true global form restriction into Čech degree zero is injective. -/
theorem formCechAugmentationMap_mono : Mono (formCechAugmentationMap ρ U n) :=
  (ModuleCat.mono_iff_injective _).mpr
    ((formCechD_zero_injective ρ U n hU φ hφ).comp (formCechEmptyEquiv ρ U n).injective)

include hU φ hφ in
/-- Every actual closed Čech zero-cochain is the restriction of a genuine global form. -/
theorem formCechAugmentationMap_exact :
    (ShortComplex.mk (formCechAugmentationMap ρ U n) ((formCechComplex ρ U n).d 0 1)
      (formCechAugmentationMap_closed ρ U n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro w hw
  change FormCechTerms ρ U n 1 at w
  have hw' : formCechD ρ U n 1 w = 0 :=
    (congrArg (fun f => f.hom w) (formCechD_eq_complex ρ U n 0)).trans hw
  have hc := formCech_contracting ρ U n hU φ hφ 0 w
  rw [hw', map_zero, add_zero] at hc
  refine ⟨formCechEmptyRecover ρ U n (formCechH ρ U n hU φ hφ 0 w), ?_⟩
  change formCechD ρ U n 0 (formCechEmptyEmbed ρ U n
    (formCechEmptyRecover ρ U n (formCechH ρ U n hU φ hφ 0 w))) = w
  rw [formCechEmptyEmbed_recover]
  exact hc

include hU φ hφ in
/-- The genuine horizontal Čech augmentation is a quasi-isomorphism, proved by the actual
partition-of-unity contraction and the actual global empty-tuple identification. -/
theorem formCechAugmentation_quasiIso : QuasiIso (formCechAugmentation ρ U n) := by
  have := formCechAugmentationMap_mono ρ U n hU φ hφ
  exact SmoothSingularComparison.augmentation_quasiIso (formCechAugmentationMap ρ U n)
    (formCechAugmentationMap_closed ρ U n) (formCechAugmentationMap_exact ρ U n hU φ hφ)
      (formCechComplex_exactAt ρ U n hU φ hφ)

include hU in
/-- Every actual quotient open cover computes the global form space by its genuine horizontal
Čech complex, with no unproved descent or acyclicity hypothesis. -/
theorem formCechAugmentation_quasiIso_of_cover (hcover : Set.univ ⊆ ⋃ i, U i) :
    QuasiIso (formCechAugmentation ρ U n) := by
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Coordinates)
    isClosed_univ U hU hcover
  exact formCechAugmentation_quasiIso ρ U n hU φ hφ

end TernaryPoly.SmoothSingularGlobal
