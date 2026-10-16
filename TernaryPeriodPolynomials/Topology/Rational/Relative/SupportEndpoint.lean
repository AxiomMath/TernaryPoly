module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportLES

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- The literal relative-support sequence terminates surjectively in degree zero. -/
theorem restrictionDifference_zero_surjective (U V : Opens X) :
    Function.Surjective (homologyRestrictionDifference (U : Set X) (V : Set X) 0) := by
  have : Epi (quotientChainRow (U : Set X) (V : Set X)).g :=
    (quotientChainRow_shortExact (U : Set X) (V : Set X)).epi_g
  have : Epi (homologyMap (quotientChainRow (U : Set X) (V : Set X)).g 0) :=
    epi_homologyMap_of_epi_of_not_rel _ 0 (by simp)
  have : Epi ((middleHomologyIso (U : Set X) (V : Set X) 0).hom ≫
      homologyRestrictionDifference (U : Set X) (V : Set X) 0) := by
    rw [← middleHomology_comm]
    infer_instance
  exact (ModuleCat.epi_iff_surjective _).mp
    (epi_of_epi (middleHomologyIso (U : Set X) (V : Set X) 0).hom _)

end TernaryPoly.RationalRelativeSupport
