module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularResolution
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoefficientFrameIso

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits HomologicalComplex
open SymmetricSpaceCovering
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- Both literal arms of the common coefficient-sheaf span are genuine quasi-isomorphisms. -/
theorem commonSheafResolutions :
    QuasiIso (formSheafAugmentation ρ) ∧ QuasiIso (singularSheafAugmentation ρ) :=
  ⟨formSheafAugmentation_quasiIso ρ, singularSheafAugmentation_quasiIso ρ⟩

/-- The actual common coefficient augmentation yields the comparison on sheaf homology.
Passing to ordinary global cohomology still requires the separate global descent theorem. -/
def sheafHomologyComparison (n : ℕ) :
    (formSheafComplex ρ).homology n ≅ (singularSheafComplex ρ).homology n := by
  have := formSheafAugmentation_quasiIso ρ
  have := singularSheafAugmentation_quasiIso ρ
  exact (isoOfQuasiIsoAt (formSheafAugmentation ρ) n).symm ≪≫
    isoOfQuasiIsoAt (singularSheafAugmentation ρ) n

/-- The sheaf-homology comparison retains both actual coefficient augmentation maps. -/
theorem sheafHomologyComparison_augmented (n : ℕ) :
    homologyMap (formSheafAugmentation ρ) n ≫ (sheafHomologyComparison ρ n).hom =
      homologyMap (singularSheafAugmentation ρ) n := by
  have := formSheafAugmentation_quasiIso ρ
  have := singularSheafAugmentation_quasiIso ρ
  simp [sheafHomologyComparison]

end TernaryPoly.SmoothSingularGlobal
