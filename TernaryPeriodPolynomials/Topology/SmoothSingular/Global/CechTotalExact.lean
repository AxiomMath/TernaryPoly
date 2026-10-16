module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechTotalAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory AlgebraicTopology
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Simplicial Topology ContDiff Manifold

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Set OrbitSpace)
  (hU : ∀ i, IsOpen (U i))
  (φ : SmoothPartitionOfUnity ι 𝓘(ℝ, Coordinates) OrbitSpace Set.univ) (hφ : φ.IsSubordinate U)

include φ hφ in
/-- Every augmented horizontal row of the actual Čech–de Rham bicomplex is exact,
proved by the actual smooth partition contraction. -/
theorem formCechTotalAugmentation_exactRows : (formCechTotalAugmentation ρ U hU).ExactRows where
  injective n := by
    change Function.Injective (formCechAugmentationMap ρ U n).hom
    exact (ModuleCat.mono_iff_injective _).mp (formCechAugmentationMap_mono ρ U n hU φ hφ)
  augmentation_exact n x hx := by
    change ∃ z, (formCechAugmentationMap ρ U n).hom z = x
    rw [formCechBicomplex_horizontal] at hx
    apply (ShortComplex.moduleCat_exact_iff _).mp (formCechAugmentationMap_exact ρ U n hU φ hφ) x
    exact (congrArg (fun f => f.hom x) (formCechD_eq_complex ρ U n 0)).symm.trans hx
  horizontal_exact p q x hx := by
    rw [formCechBicomplex_horizontal] at hx ⊢
    exact ⟨formCechH ρ U q hU φ hφ (p+1) x, formCech_primitive ρ U q hU φ hφ p x hx⟩

/-- Actual quotient open covers satisfy all row hypotheses without an assumed acyclicity condition. -/
theorem formCechTotalAugmentation_exactRows_of_cover (hcover : Set.univ ⊆ ⋃ i, U i) :
    (formCechTotalAugmentation ρ U hU).ExactRows := by
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Coordinates)
    isClosed_univ U hU hcover
  exact formCechTotalAugmentation_exactRows ρ U hU φ hφ

/-- The literal restriction map from actual global forms into the actual degree-two
Čech–de Rham total window is a quasi-isomorphism for every quotient open cover. -/
theorem formCechTotalAugmentation_quasiIso (hcover : Set.univ ⊆ ⋃ i, U i) :
    ShortComplex.QuasiIso (formCechTotalAugmentation ρ U hU).totalAugmentationMap :=
  (formCechTotalAugmentation ρ U hU).totalAugmentationMap_quasiIso
    (formCechTotalAugmentation_exactRows_of_cover ρ U hU hcover)

/-- Actual degree-two global de Rham cohomology is computed by the genuine Čech–de Rham
window of any actual quotient open cover. -/
def globalFormsCechTotalIso (hcover : Set.univ ⊆ ⋃ i, U i) :
    (globalComplex ρ).homology 2 ≅ (totalWindow (formCechBicomplex ρ U hU)).homology :=
  (globalComplex ρ).homologyIsoSc' 1 2 3 (by simp) (by simp) ≪≫
    (formCechTotalAugmentation ρ U hU).totalAugmentationHomologyIso
      (formCechTotalAugmentation_exactRows_of_cover ρ U hU hcover)

/-- This isomorphism is induced by the actual global restriction augmentation. -/
theorem globalFormsCechTotalIso_hom (hcover : Set.univ ⊆ ⋃ i, U i) :
    (globalFormsCechTotalIso ρ U hU hcover).hom =
      ((globalComplex ρ).homologyIsoSc' 1 2 3 (by simp) (by simp)).hom ≫
        ShortComplex.homologyMap (formCechTotalAugmentation ρ U hU).totalAugmentationMap := rfl

end TernaryPoly.SmoothSingularGlobal
