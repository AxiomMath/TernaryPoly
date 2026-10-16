module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Orbit

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison
open CategoryTheory Representation EquivariantSingularSmall

variable (G : Type) [Group G] {A : Type} [MulAction G A] (a : A)

def orbitShapiroDegree (W : Rep.{0} ℚ G) (n : ℕ)
    (c : (orbitResolution G a).complex.X n ⟶ W) :
    (Rep.barResolution ℚ (stabilizer G a)).complex.X n ⟶ Rep.res (stabilizer G a).subtype W :=
  (orbitShapiroIso G a W).hom.f n c

def barAugmentValue (b : (Rep.barResolution ℚ (stabilizer G a)).complex.X 0) : ℚ :=
  (Rep.barResolution ℚ (stabilizer G a)).π.f 0 b

/-- Stabilizer cochain evaluation is literally evaluation at the identity induction generator. -/
theorem orbitShapiro_evaluation (W : Rep.{0} ℚ G) (n : ℕ)
    (c : (orbitResolution G a).complex.X n ⟶ W)
    (b : (Rep.barResolution ℚ (stabilizer G a)).complex.X n) :
    (orbitShapiroDegree G a W n c).hom b =
      c (IndV.mk (stabilizer G a).subtype ((Rep.barResolution ℚ (stabilizer G a)).complex.X n).ρ 1 b) := rfl

/-- The orbit-label augmentation sends an induced degree-zero bar generator to its literal label. -/
theorem orbitResolution_augmentation_mk (g : G)
    (b : (Rep.barResolution ℚ (stabilizer G a)).complex.X 0) :
    (orbitResolution G a).π.f 0
      (IndV.mk (stabilizer G a).subtype ((Rep.barResolution ℚ (stabilizer G a)).complex.X 0).ρ g b)=
        MonoidAlgebra.single (orbitPoint G a g⁻¹) (barAugmentValue G a b) := by
  change (inducedOrbitIso G a).hom ((inducedOrbitResolution G a).π.f 0
    (IndV.mk (stabilizer G a).subtype ((Rep.barResolution ℚ (stabilizer G a)).complex.X 0).ρ g b))=_
  change (inducedOrbitIso G a).hom
    ((Rep.indMap (stabilizer G a).subtype ((Rep.barResolution ℚ (stabilizer G a)).π.f 0)).hom
      (IndV.mk (stabilizer G a).subtype ((Rep.barResolution ℚ (stabilizer G a)).complex.X 0).ρ g b))=_
  exact inducedOrbitLinear_mk G a g _

end TernaryPoly.BoundaryFaceResolutionComparison
