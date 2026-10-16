module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.Coefficients
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.Singular
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory HomologicalComplex SmoothLocalDeRham
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The common-constants comparison on a genuine nonempty convex open chart, in every degree.
The two arms are the literal augmentations, with local exactness proved on both sides. -/
def localComparison {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty) (n : ℕ) :
    (complex (F := F) hs).homology n ≅
      (realSingularCochains (TopCat.of s) (ModuleCat.of ℝ F)).homology n := by
  letI : ContractibleSpace (TopCat.of s) := hc.contractibleSpace hne
  letI : QuasiIso (deRhamAugmentation (F := F) hs) := deRhamAugmentation_quasiIso hs hc hne
  letI : QuasiIso (singularAugmentation (TopCat.of s) (ModuleCat.of ℝ F)) :=
    singularAugmentation_quasiIso _ _
  exact comparison (deRhamAugmentation hs) (singularAugmentation _ _) n

/-- The actual continuous inclusion of one chart domain into another. -/
def chartInclusion {s t : Set E} (hts : t ⊆ s) : TopCat.of t ⟶ TopCat.of s :=
  TopCat.ofHom ⟨fun x => ⟨x.val, hts x.property⟩, continuous_subtype_val.subtype_mk _⟩

/-- The canonical local comparison respects actual open-chart restrictions. -/
theorem localComparison_restrict {s t : Set E} (hs : IsOpen s) (ht : IsOpen t)
    (hcs : Convex ℝ s) (hct : Convex ℝ t) (hns : s.Nonempty) (hnt : t.Nonempty)
    (hts : t ⊆ s) (n : ℕ) :
    (localComparison (F := F) hs hcs hns n).hom ≫
        homologyMap (singularPullback (chartInclusion hts) (ModuleCat.of ℝ F)) n =
      homologyMap (deRhamRestriction (F := F) hs ht hts) n ≫
        (localComparison ht hct hnt n).hom := by
  let : ContractibleSpace (TopCat.of s) := hcs.contractibleSpace hns
  let : ContractibleSpace (TopCat.of t) := hct.contractibleSpace hnt
  let : QuasiIso (deRhamAugmentation (F := F) hs) := deRhamAugmentation_quasiIso hs hcs hns
  let : QuasiIso (deRhamAugmentation (F := F) ht) := deRhamAugmentation_quasiIso ht hct hnt
  let : QuasiIso (singularAugmentation (TopCat.of s) (ModuleCat.of ℝ F)) := singularAugmentation_quasiIso _ _
  let : QuasiIso (singularAugmentation (TopCat.of t) (ModuleCat.of ℝ F)) := singularAugmentation_quasiIso _ _
  exact comparison_natural _ _ _ _ (𝟙 _) (deRhamRestriction hs ht hts)
    (singularPullback (chartInclusion hts) (ModuleCat.of ℝ F))
    (by simpa using deRhamAugmentation_restrict (F := F) hs ht hts)
    (by simpa using singularAugmentation_pullback (chartInclusion hts) (ModuleCat.of ℝ F)) n

/-- The canonical local comparison respects all continuous real-linear coefficient maps;
in particular it respects arbitrary finite-dimensional deck coefficient transitions. -/
theorem localComparison_coefficient (L : F →L[ℝ] G) {s : Set E}
    (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty) (n : ℕ) :
    (localComparison (F := F) hs hc hne n).hom ≫
        homologyMap (realHomCoefficient (realSingularChains (TopCat.of s))
          (ModuleCat.ofHom L.toLinearMap)) n =
      homologyMap (deRhamCoefficient L hs) n ≫ (localComparison (F := G) hs hc hne n).hom := by
  let : ContractibleSpace (TopCat.of s) := hc.contractibleSpace hne
  let : QuasiIso (deRhamAugmentation (F := F) hs) := deRhamAugmentation_quasiIso hs hc hne
  let : QuasiIso (deRhamAugmentation (F := G) hs) := deRhamAugmentation_quasiIso hs hc hne
  let : QuasiIso (singularAugmentation (TopCat.of s) (ModuleCat.of ℝ F)) := singularAugmentation_quasiIso _ _
  let : QuasiIso (singularAugmentation (TopCat.of s) (ModuleCat.of ℝ G)) := singularAugmentation_quasiIso _ _
  exact comparison_natural _ _ _ _
    ((CochainComplex.single₀ (ModuleCat ℝ)).map (ModuleCat.ofHom L.toLinearMap))
    (deRhamCoefficient L hs) (realHomCoefficient _ (ModuleCat.ofHom L.toLinearMap))
    (deRhamAugmentation_coefficient L hs) (singularAugmentation_coefficient _ _) n

end TernaryPoly.SmoothSingularComparison
