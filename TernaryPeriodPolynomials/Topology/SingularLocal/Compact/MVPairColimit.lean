module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVColimitAlgebra
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

variable {J : Type} [SmallCategory J] (F G : J ⥤ ModuleCat.{0} ℚ)

/-- The explicit pointwise pair is the actual categorical biproduct of the two diagrams. -/
def pointwisePairIso : (pointwiseBinaryBicone F G).pt ≅ F ⊞ G :=
  biprod.uniqueUpToIso F G (pointwiseBinaryBicone.isBilimit F G)

/-- Colimits split the genuine pointwise pair of module-valued diagrams. -/
def pointwisePairColimitIso : colimit (pointwiseBinaryBicone F G).pt ≅ colimit F ⊞ colimit G :=
  (colim.mapIso (pointwisePairIso F G)) ≪≫ colim.mapBiprod F G

/-- The pair-colimit isomorphism retains the two actual diagram projections. -/
theorem pointwisePairColimitIso_hom :
    (pointwisePairColimitIso F G).hom =
      biprod.lift (colim.map (pointwiseBinaryBicone F G).fst) (colim.map (pointwiseBinaryBicone F G).snd) := by
  change colim.map (pointwisePairIso F G).hom ≫ (colim.mapBiprod F G).hom = _
  rw [Functor.mapBiprod_hom]
  apply biprod.hom_ext
  · rw [Category.assoc,biprod.lift_fst,biprod.lift_fst,← Functor.map_comp]
    rw [pointwisePairIso,biprod.uniqueUpToIso_hom,biprod.lift_fst]
  · rw [Category.assoc,biprod.lift_snd,biprod.lift_snd,← Functor.map_comp]
    rw [pointwisePairIso,biprod.uniqueUpToIso_hom,biprod.lift_snd]

/-- Every actual pair of fixed-support classes maps to the corresponding pair of colimit classes. -/
theorem pointwisePairColimitIso_ι (j : J) :
    colimit.ι (pointwiseBinaryBicone F G).pt j ≫ (pointwisePairColimitIso F G).hom =
      biprod.map (colimit.ι F j) (colimit.ι G j) := by
  rw [pointwisePairColimitIso_hom]
  apply biprod.hom_ext
  · erw [Category.assoc,biprod.lift_fst,colimit.ι_map,biprod.map_fst]
    rfl
  · erw [Category.assoc,biprod.lift_snd,colimit.ι_map,biprod.map_snd]
    rfl

end TernaryPoly.SingularLocalCompactMV
