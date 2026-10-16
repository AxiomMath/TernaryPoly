module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechBicomplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory AlgebraicTopology
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Simplicial Topology ContDiff Manifold

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Set OrbitSpace)
  (hU : ∀ i, IsOpen (U i))

/-- The Čech augmentation is literally restriction to each cover component. -/
theorem formCechAugmentationMap_apply (n : ℕ) (w : EquivariantForm ρ Set.univ n)
    (t : Fin 1 → ι) :
    (formCechAugmentationMap ρ U n).hom w t = restrictEquivariant ρ (Set.subset_univ _) n w := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change ((formCechD ρ U n 0 (formCechEmptyEmbed ρ U n w) t).val : RawForm Coordinates F n) x = _
  rw [formCechD_zero_value ρ U n (formCechEmptyEmbed ρ U n w) t x hx]
  change ((restrictEquivariant ρ (Set.subset_univ _) n w).val : RawForm Coordinates F n) x = _
  have hx0 : x ∈ liftedDomain (cechDomain U (Fin.elim0 : Fin 0 → ι)) :=
    liftedDomain_mono (univ_subset_cechDomain_empty U Fin.elim0)
      (liftedDomain_mono (Set.subset_univ _) hx)
  exact (restrictEquivariant_apply ρ _ _ hx0).trans (restrictEquivariant_apply ρ _ _ hx).symm

/-- Global forms map into column zero by genuine restriction, compatibly with the de Rham differential. -/
def formCechColumnAugmentation : globalComplex ρ ⟶ (formCechBicomplex ρ U hU).X 0 :=
  CochainComplex.ofHom (fun n => formCechAugmentationMap ρ U n) (by
    intro n
    change formCechAugmentationMap ρ U n ≫ (formCechColumn ρ U hU 1).d n (n+1) =
      (globalComplex ρ).d n (n+1) ≫ formCechAugmentationMap ρ U (n+1)
    simp only [formCechColumn, globalComplex, coveringComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    funext t
    change differential ρ (cechDomain_isOpen U hU t) n
      ((formCechAugmentationMap ρ U n).hom w t) =
      (formCechAugmentationMap ρ U (n+1)).hom (differential ρ isOpen_univ n w) t
    rw [formCechAugmentationMap_apply, formCechAugmentationMap_apply]
    exact (restrictEquivariant_d ρ isOpen_univ (cechDomain_isOpen U hU t)
      (Set.subset_univ _) w).symm)

/-- The genuine global form augmentation is horizontally closed in the actual bicomplex. -/
theorem formCechColumnAugmentation_horizontal : formCechColumnAugmentation ρ U hU ≫
    (formCechBicomplex ρ U hU).d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  change horizontal (formCechBicomplex ρ U hU) 0 n ((formCechAugmentationMap ρ U n).hom w) = 0
  rw [formCechBicomplex_horizontal]
  exact formCechD_one_zero ρ U n (formCechEmptyEmbed ρ U n w)

/-- The actual augmentation of global local-coefficient forms into the Čech–de Rham bicomplex. -/
def formCechTotalAugmentation : TotalAugmentation (globalComplex ρ) (formCechBicomplex ρ U hU) where
  map := formCechColumnAugmentation ρ U hU
  horizontal_zero := formCechColumnAugmentation_horizontal ρ U hU

end TernaryPoly.SmoothSingularGlobal
