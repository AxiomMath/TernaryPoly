module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ChartsQuadrant
public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesCorner

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryCharts
open SymmetricSpaceFlagCoordinates

abbrev BoundaryCoordinates := Fin 4 → ℝ
abbrev ProductModel := BoundaryCoordinates × HalfLine

/-- Adjoin the difference of the two roots to the three unipotent coordinates. -/
def vectorFourHomeomorph : ((Fin 3 → ℝ) × ℝ) ≃ₜ BoundaryCoordinates where
  toFun p := ![p.1 0,p.1 1,p.1 2,p.2]
  invFun v := (![v 0,v 1,v 2],v 3)
  left_inv p := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  right_inv v := by funext i; fin_cases i <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A full rank-three flag corner is literally a five-dimensional topological half-space. -/
def cornerProductHomeomorph : Corner ≃ₜ ProductModel :=
  (((Homeomorph.refl (Fin 3 → ℝ)).prodCongr quadrantHomeomorph).trans
    (Homeomorph.prodAssoc (Fin 3 → ℝ) ℝ HalfLine).symm).trans
      (vectorFourHomeomorph.prodCongr (Homeomorph.refl HalfLine))

@[simp] theorem cornerProduct_height (p : Corner) :
    (cornerProductHomeomorph p).2.val=min p.2.1.val p.2.2.val := rfl

@[simp] theorem cornerProduct_positive (p : Corner) :
    0<(cornerProductHomeomorph p).2.val ↔ p∈cornerInterior :=
  quadrantHomeomorph_positive p.2

@[simp] theorem cornerProduct_zero (p : Corner) :
    (cornerProductHomeomorph p).2.val=0 ↔ p.2.1.val=0 ∨ p.2.2.val=0 :=
  quadrantHomeomorph_zero p.2

end TernaryPoly.SymmetricSpaceBoundaryCharts
