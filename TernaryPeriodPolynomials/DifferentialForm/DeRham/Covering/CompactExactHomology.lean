module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CoefficientExactness
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.ChainMaps
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.HomologyZero

@[expose] public section


/-! Genuine smooth primitive existence kills the actual compact-to-ordinary homology map. -/
noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set CategoryTheory HomologicalComplex SymmetricSpaceCovering SmoothSingularGlobal
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem compactInclusion_homology_two_eq_zero
    (ρ : Representation ℝ DeckGroup F) (h : CompactExactInDegree ρ 1) :
    homologyMap (compactInclusion ρ isOpen_univ) 2 = 0 := by
  apply cochainHomologyMap_eq_zero_of_boundaries
  intro a ha
  have hc : compactDifferential ρ isOpen_univ 2 a = 0 := by
    change (CochainComplex.of.d
      (fun n => ModuleCat.of ℝ (CompactSupportForm ρ univ n))
      (fun n => ModuleCat.ofHom (compactDifferential ρ isOpen_univ n)) 2 (2 + 1)).hom a = 0 at ha
    rw [CochainComplex.of_d] at ha
    exact ha
  obtain ⟨v,hv⟩ := h a hc
  refine ⟨v,?_⟩
  change (CochainComplex.of.d
    (fun n => ModuleCat.of ℝ (EquivariantForm ρ univ n))
    (fun n => ModuleCat.ofHom (differential ρ isOpen_univ n)) 1 (1 + 1)).hom v = a.val
  rw [CochainComplex.of_d]
  exact hv

end TernaryPoly.SmoothCoveringDeRham
