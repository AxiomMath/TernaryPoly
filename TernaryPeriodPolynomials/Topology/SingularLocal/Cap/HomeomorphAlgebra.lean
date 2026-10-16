module

public import TernaryPeriodPolynomials.Topology.Rational.Homology.CoefficientsComplexNaturality
public import TernaryPeriodPolynomials.Topology.Singular.CoverPullbackIso

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCapHomeomorph
open CategoryTheory HomologicalComplex RationalHomologyCoefficients

/-- Literal precomposition on Hom cochains preserves identities. -/
theorem homCochainsMap_id (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (V : ModuleCat.{0} ℚ) :
    homCochainsMap (𝟙 K) V = 𝟙 _ := by
  ext a φ c
  rfl

/-- Literal precomposition on Hom cochains reverses composition. -/
theorem homCochainsMap_comp {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (f : K ⟶ L) (g : L ⟶ M) (V : ModuleCat.{0} ℚ) :
    homCochainsMap (f ≫ g) V = homCochainsMap g V ≫ homCochainsMap f V := by
  ext a φ c
  rfl

/-- A genuine chain isomorphism induces the literal contravariant Hom-cochain isomorphism. -/
def homCochainsIso {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (e : K ≅ L)
    (V : ModuleCat.{0} ℚ) : homCochains L V ≅ homCochains K V where
  hom := homCochainsMap e.hom V
  inv := homCochainsMap e.inv V
  hom_inv_id := by rw [← homCochainsMap_comp,e.inv_hom_id,homCochainsMap_id]
  inv_hom_id := by rw [← homCochainsMap_comp,e.hom_inv_id,homCochainsMap_id]

end TernaryPoly.SingularLocalCapHomeomorph
