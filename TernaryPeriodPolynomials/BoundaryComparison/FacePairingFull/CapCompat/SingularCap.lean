module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Leibniz
public import TernaryPeriodPolynomials.Topology.TopHomology.PermutationHom

@[expose] public section


/-!
# The Alexander-Whitney cap of equivariant singular chains as a morphism of representations

For a group `G` acting on a space `E` and a cochain `f : C_a(E) ⟶ V` (a morphism of `G`-representations out of the
equivariant singular chains `chainRep G E a`), the cap `capE E V a b f : C_{a+b}(E) ⟶ V ⊗ C_b(E)` sends a singular
simplex `σ` to `f(front_a σ) ⊗ back_b σ` (front/back faces of Alexander-Whitney).  It is `G`-equivariant because the
front and back faces are natural for the action.  The bridge to the library's quotient-level cap
(`SingularLocalCap.cap`) is `CapCompat.Bridge`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory MonoidalCategory
open TernaryPoly TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalHomology
open TernaryPoly.FreeActionLinearization
open TernaryPeriodPolynomials.Argument.TopHomology
open SphereOddDegree.AlexanderWhitney

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {G : Type} [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]

theorem degreeRepIso_hom_single (n : ℕ) (σ : SingularSimplex E n) :
    (degreeRepIso G E n).hom.hom (MonoidAlgebra.single σ 1) = chainElement G E n σ := by
  change degreeLinearEquiv E n (MonoidAlgebra.single σ 1) = _
  rw [degreeLinearEquiv_single]
  rfl

noncomputable def capElem (V : Rep ℚ G) (a b : ℕ) (f : chainRep G E a ⟶ V) (σ : SingularSimplex E (a+b)) :
    (V ⊗ chainRep G E b : Rep ℚ G) :=
  (f.hom (chainElement G E a (frontSimplex E a b σ))) ⊗ₜ[ℚ] (chainElement G E b (backSimplex E a b σ))

theorem frontSimplex_smul (g : G) (a b : ℕ) (σ : SingularSimplex E (a+b)) :
    frontSimplex E a b (g • σ) = g • frontSimplex E a b σ := by
  rw [singular_smul_eq_map G E, singular_smul_eq_map G E]
  exact (frontSimplex_naturality (scalarMap G E g) a b σ).symm

theorem backSimplex_smul (g : G) (a b : ℕ) (σ : SingularSimplex E (a+b)) :
    backSimplex E a b (g • σ) = g • backSimplex E a b σ := by
  rw [singular_smul_eq_map G E, singular_smul_eq_map G E]
  exact (backSimplex_naturality (scalarMap G E g) a b σ).symm

theorem capElem_smul (V : Rep ℚ G) (a b : ℕ) (f : chainRep G E a ⟶ V) (g : G) (σ : SingularSimplex E (a+b)) :
    capElem E V a b f (g • σ) = (V ⊗ chainRep G E b).ρ g (capElem E V a b f σ) := by
  unfold capElem
  rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul, frontSimplex_smul, backSimplex_smul,
    ← chainElement_smul, ← chainElement_smul]
  congr 1
  exact Rep.hom_comm_apply f g _

noncomputable def capE (V : Rep ℚ G) (a b : ℕ) (f : chainRep G E a ⟶ V) :
    chainRep G E (a+b) ⟶ V ⊗ chainRep G E b :=
  (degreeRepIso G E (a+b)).inv ≫ ofMulActionLift (SingularSimplex E (a+b)) (V ⊗ chainRep G E b)
    (capElem E V a b f) (fun g σ => capElem_smul E V a b f g σ)

theorem capE_chainElement (V : Rep ℚ G) (a b : ℕ) (f : chainRep G E a ⟶ V) (σ : SingularSimplex E (a+b)) :
    (capE E V a b f).hom (chainElement G E (a+b) σ) = capElem E V a b f σ := by
  have h1 : (capE E V a b f).hom (chainElement G E (a+b) σ) =
      ((degreeRepIso G E (a+b)).hom ≫ capE E V a b f).hom (MonoidAlgebra.single σ 1) := by
    rw [← degreeRepIso_hom_single]; rfl
  rw [h1]
  unfold capE
  rw [Iso.hom_inv_id_assoc]
  exact ofMulActionLift_single _ _ _ _ σ

theorem chainRep_linear_ext {n : ℕ} {M : Type} [AddCommGroup M] [Module ℚ M]
    {φ ψ : chainRep G E n →ₗ[ℚ] M}
    (h : ∀ σ : SingularSimplex E n, φ (chainElement G E n σ) = ψ (chainElement G E n σ)) : φ = ψ := by
  have : φ ∘ₗ (degreeLinearEquiv E n).toLinearMap = ψ ∘ₗ (degreeLinearEquiv E n).toLinearMap := by
    apply MonoidAlgebra.lhom_ext'
    intro σ
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidAlgebra.lsingle_apply]
    rw [degreeLinearEquiv_single]
    exact h σ
  ext x
  have := LinearMap.congr_fun this ((degreeLinearEquiv E n).symm x)
  simpa using this

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
