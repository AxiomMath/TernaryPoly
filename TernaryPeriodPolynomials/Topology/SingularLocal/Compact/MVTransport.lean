module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVColimitAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits

/-- Transporting an actual colimit map through two isomorphisms retains its map on every representative. -/
theorem colimitTransport_ι {J : Type} [SmallCategory J] {F G : J ⥤ ModuleCat.{0} ℚ}
    {X Y : ModuleCat.{0} ℚ} (a : colimit F ≅ X) (b : colimit G ≅ Y) (φ : F ⟶ G) (j : J) :
    (colimit.ι F j ≫ a.hom) ≫ (a.inv ≫ colim.map φ ≫ b.hom) =
      φ.app j ≫ (colimit.ι G j ≫ b.hom) := by
  rw [Category.assoc,Iso.hom_inv_id_assoc,← Category.assoc,colimit.ι_map,Category.assoc]

end TernaryPoly.SingularLocalCompactMV
