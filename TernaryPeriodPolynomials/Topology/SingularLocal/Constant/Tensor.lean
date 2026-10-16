module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Comparison

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalConstant
open CategoryTheory Limits
open FreeActionLinearization CoveringSingularOrbits
open SingularLocalCap SphereOddDegree.AffineBarycentricSubdivision
open scoped TensorProduct Classical
variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- Coproduct coordinates of an actual ordinary singular coefficient generator. -/
theorem ordinaryFinsuppIso_hom_generator (n : ℕ) (σ : SingularSimplex X n) (v : V) :
    (ordinaryFinsuppIso X V n).hom (((TopCat.toSSet.obj X).ιChainComplex (R := V) σ) v) =
      Finsupp.single σ v := by
  apply (ordinaryFinsuppIso X V n).toLinearEquiv.symm.injective
  exact ((ordinaryFinsuppIso X V n).toLinearEquiv.symm_apply_apply _).trans
    (ordinaryFinsuppIso_inv_single X V n σ v).symm

/-- The tensor comparison sends a unit scalar simplex tensored with v to the same
ordinary singular simplex with coefficient v. -/
theorem tensorDegreeEquiv_generator (n : ℕ) (σ : SingularSimplex X n) (v : V) :
    tensorDegreeEquiv X V n (chainGenerator ℚ X n σ ⊗ₜ[ℚ] v) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := V) σ) v := by
  have h : (EquivariantSingularResolution.degreeFinsuppIso X n).hom
      (chainGenerator ℚ X n σ) = Finsupp.single σ (1 : ℚ) :=
    ordinaryFinsuppIso_hom_generator X (ModuleCat.of ℚ ℚ) n σ 1
  change (ordinaryFinsuppIso X V n).inv
    ((TensorProduct.finsuppScalarLeft ℚ V (SingularSimplex X n))
      ((EquivariantSingularResolution.degreeFinsuppIso X n).hom
        (chainGenerator ℚ X n σ) ⊗ₜ[ℚ] v)) = _
  rw [h]
  have ht : (TensorProduct.finsuppScalarLeft ℚ V (SingularSimplex X n))
      (Finsupp.single σ 1 ⊗ₜ[ℚ] v) = Finsupp.single σ v := by
    rw [← TensorProduct.finsuppScalarLeft_symm_apply_single, LinearEquiv.apply_symm_apply]
  rw [ht, ordinaryFinsuppIso_inv_single]

/-- Tensoring the actual scalar singular boundary with the identity of V. -/
def tensorDifferential (n : ℕ) :
    ((scalarChains X).X (n+1) ⊗[ℚ] V) →ₗ[ℚ] ((scalarChains X).X n ⊗[ℚ] V) :=
  TensorProduct.map ((scalarChains X).d (n+1) n).hom LinearMap.id

/-- The tensor differential squares to zero by the genuine singular chain identity. -/
theorem tensorDifferential_squared (n : ℕ) :
    (tensorDifferential X V n).comp (tensorDifferential X V (n+1)) = 0 := by
  apply TensorProduct.ext'
  intro c v
  have h := congrArg (fun f => f c) ((scalarChains X).d_comp_d (n+2) (n+1) n)
  change (scalarChains X).d (n+1) n ((scalarChains X).d (n+2) (n+1) c) = 0 at h
  change ((scalarChains X).d (n+1) n ((scalarChains X).d (n+2) (n+1) c)) ⊗ₜ[ℚ] v = 0
  rw [h, TensorProduct.zero_tmul]

/-- The actual rational singular chain complex tensored degreewise with V. -/
def tensorChains : ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℚ ((scalarChains X).X n ⊗[ℚ] V))
    (fun n => ModuleCat.ofHom (tensorDifferential X V n)) (fun n => by
      apply ModuleCat.hom_ext
      exact tensorDifferential_squared X V n)

/-- On every scalar simplex tensor, the tensor comparison intertwines the actual boundaries. -/
theorem tensorDegreeEquiv_boundary_generator (n : ℕ) (σ : SingularSimplex X (n+1)) (v : V) :
    tensorDegreeEquiv X V n (tensorDifferential X V n (chainGenerator ℚ X (n+1) σ ⊗ₜ[ℚ] v)) =
      (ordinaryChains X V).d (n+1) n
        (tensorDegreeEquiv X V (n+1) (chainGenerator ℚ X (n+1) σ ⊗ₜ[ℚ] v)) := by
  rw [tensorDegreeEquiv_generator, ordinary_boundary_generator]
  change tensorDegreeEquiv X V n
    ((singularBoundary ℚ X n).hom (chainGenerator ℚ X (n+1) σ) ⊗ₜ[ℚ] v) = _
  rw [scalarBoundary_generator, TensorProduct.sum_tmul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  erw [← TensorProduct.smul_tmul', map_zsmul, tensorDegreeEquiv_generator]
  rfl

/-- The actual tensor comparison commutes with the entire differential, by bilinearity
and the genuine scalar singular generators. -/
theorem tensorDegreeEquiv_boundary (n : ℕ) :
    (tensorDegreeEquiv X V n).toLinearMap.comp (tensorDifferential X V n) =
      ((ordinaryChains X V).d (n+1) n).hom.comp (tensorDegreeEquiv X V (n+1)).toLinearMap := by
  apply TensorProduct.ext
  apply SingularLocalCap.scalarChain_ext
  intro σ
  apply LinearMap.ext
  intro v
  exact tensorDegreeEquiv_boundary_generator X V n σ v

/-- Ordinary chains with coefficient V are canonically the actual rational singular
chain complex tensored with V, with the tensor differential. -/
def tensorChainIso : tensorChains X V ≅ ordinaryChains X V :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (tensorDegreeEquiv X V n).toModuleIso)
    (fun i j hij => by
      obtain rfl : i = j+1 := hij.symm
      apply ModuleCat.hom_ext
      simp only [tensorChains, ChainComplex.of_d]
      exact (tensorDegreeEquiv_boundary X V j).symm)

/-- Canonical identity-cover local chains are genuinely isomorphic to rational singular
chains tensored with arbitrary V. -/
def localTensorChainIso : chains X V ≅ tensorChains X V :=
  ordinaryChainIso X V ≪≫ (tensorChainIso X V).symm

end TernaryPoly.SingularLocalConstant
