module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.CochainDifferential

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalConstant
open CategoryTheory
open SingularLocalCoefficient SingularLocalCap
variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- The ordinary V-valued Hom differential is precomposition with the scalar singular boundary. -/
def homDifferential (n : ℕ) :
    ((scalarChains X).X n →ₗ[ℚ] V) →ₗ[ℚ] ((scalarChains X).X (n+1) →ₗ[ℚ] V) where
  toFun φ := φ.comp ((scalarChains X).d (n+1) n).hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The ordinary Hom differential squares to zero because the actual scalar singular differential does. -/
theorem homDifferential_squared (n : ℕ) :
    (homDifferential X V (n+1)).comp (homDifferential X V n) = 0 := by
  ext φ c
  have h := congrArg (fun f => f c) ((scalarChains X).d_comp_d (n+2) (n+1) n)
  change (scalarChains X).d (n+1) n ((scalarChains X).d (n+2) (n+1) c) = 0 at h
  change φ ((scalarChains X).d (n+1) n ((scalarChains X).d (n+2) (n+1) c)) = 0
  rw [h, map_zero]

/-- The actual ordinary V-valued Hom cochain complex on rational singular chains. -/
def homCochains : CochainComplex (ModuleCat.{0} ℚ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℚ ((scalarChains X).X n →ₗ[ℚ] V))
    (fun n => ModuleCat.ofHom (homDifferential X V n)) (fun n => by
      apply ModuleCat.hom_ext
      exact homDifferential_squared X V n)

/-- Canonical evaluation is a genuine cochain isomorphism from geometric constant
local cochains to V-valued Hom cochains on the actual rational singular complex. -/
def homCochainIso : cochains X V ≅ homCochains X V :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (cochainHomEquiv X V n).toModuleIso)
    (fun i j hij => by
      obtain rfl : j = i+1 := hij.symm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      simp only [homCochains, cochains, localCochains, CochainComplex.of_d]
      exact (evaluation_differential X V i φ).symm)

end TernaryPoly.SingularLocalConstant
