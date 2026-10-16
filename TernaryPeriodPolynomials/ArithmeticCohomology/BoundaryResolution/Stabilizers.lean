module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.OrbitFamily
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.OrbitEvaluation
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Product

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison
open CategoryTheory Category Limits HomologicalComplex EquivariantSingularSmall

variable (G : Type) [Group G] (X : Type) [MulAction G X]

/-- The full sum of bar resolutions induced from the actual label stabilizers. -/
abbrev orbitFamilyResolution :=
  Family.sumResolution (fun o : labelOrbits G X => orbitResolution G o.out)

/-- The genuine full-family stabilizer resolution resolves the literal label module. -/
def stabilizerResolution : ProjectiveResolution (Rep.ofMulAction ℚ G X) where
  complex := (orbitFamilyResolution G X).complex
  projective := (orbitFamilyResolution G X).projective
  π := (orbitFamilyResolution G X).π ≫ (ChainComplex.single₀ (Rep ℚ G)).map (orbitFamilyIso G X).hom
  quasiIso := by infer_instance

/-- Cochains of all actual stabilizers, with the original coefficient representation restricted. -/
abbrev stabilizerCochains (W : Rep.{0} ℚ G) :=
  Family.productComplex (fun o : labelOrbits G X =>
    homCochains (Rep.barResolution ℚ (stabilizer G o.out)).complex (Rep.res (stabilizer G o.out).subtype W))

/-- The intermediate full product has the same actual differential as the product of Hom complexes. -/
def familyHomProductIso (W : Rep.{0} ℚ G) :
    Family.productCochains (fun o : labelOrbits G X => (orbitResolution G o.out).complex) W ≅
      Family.productComplex (fun o : labelOrbits G X => homCochains (orbitResolution G o.out).complex W) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    rfl)

/-- The full resolution has an actual Shapiro cochain isomorphism to all stabilizer factors. -/
def fullShapiroIso (W : Rep.{0} ℚ G) :
    homCochains (stabilizerResolution G X).complex W ≅ stabilizerCochains G X W :=
  Family.sumHomIso (fun o : labelOrbits G X => (orbitResolution G o.out).complex) W ≪≫
    familyHomProductIso G X W ≪≫
      Family.productComplexIso (fun o : labelOrbits G X => orbitShapiroIso G o.out W)

def fullShapiroDegree (W : Rep.{0} ℚ G) (n : ℕ)
    (c : (stabilizerResolution G X).complex.X n ⟶ W) (o : labelOrbits G X) :
    (Rep.barResolution ℚ (stabilizer G o.out)).complex.X n ⟶ Rep.res (stabilizer G o.out).subtype W :=
  (fullShapiroIso G X W).hom.f n c o

/-- Full-family coefficient evaluation is summand inclusion followed by evaluation at induction identity. -/
theorem fullShapiro_evaluation (W : Rep.{0} ℚ G) (n : ℕ)
    (c : (stabilizerResolution G X).complex.X n ⟶ W) (o : labelOrbits G X)
    (b : (Rep.barResolution ℚ (stabilizer G o.out)).complex.X n) :
    (fullShapiroDegree G X W n c o).hom b =
      c ((Family.inclusion (fun o : labelOrbits G X => (orbitResolution G o.out).complex) o).f n
        (Representation.IndV.mk (stabilizer G o.out).subtype
          ((Rep.barResolution ℚ (stabilizer G o.out)).complex.X n).ρ 1 b)) := rfl

end TernaryPoly.BoundaryFaceResolutionComparison
