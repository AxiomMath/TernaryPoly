module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Coinvariants
public import TernaryPeriodPolynomials.Topology.SingularLocal.CoefficientAction

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory EquivariantSingularResolution FreeActionLinearization
open scoped Simplicial TensorProduct

variable {G : Type} [Group G]

/-- The literal tensor-coinvariant functor sends an elementary tensor by the specified second map. -/
theorem tensorCoinvariant_map_mk (A B C : Rep ℚ G) (f : B ⟶ C) (a : A) (b : B) :
    (((Rep.coinvariantsTensor ℚ G).obj A).map f) (Rep.coinvariantsTensorMk A B a b) =
      Rep.coinvariantsTensorMk A C a (f b) := by
  rfl

variable (G) (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]

/-- The unit coefficient on one actual Mathlib singular simplex. -/
def chainElement (n : ℕ) (τ : SingularSimplex E n) : chainRep G E n :=
  ((TopCat.toSSet.obj E).ιChainComplex (R := ModuleCat.of ℚ ℚ) τ) 1

/-- A genuine elementary singular tensor-coinvariant chain with coefficient `v`. -/
def generator (V : Rep ℚ G) (n : ℕ) (τ : SingularSimplex E n) :
    V →ₗ[ℚ] (coinvariantChains G E V).X n :=
  (Rep.coinvariantsTensorMk V (chainRep G E n)).flip (chainElement G E n τ)

/-- The actual deck action carries a unit singular generator to the acted simplex. -/
theorem chainElement_smul (n : ℕ) (g : G) (τ : SingularSimplex E n) :
    (chainRep G E n).ρ g (chainElement G E n τ) = chainElement G E n (g • τ) :=
  congrArg (fun f => f (1 : ℚ)) (generator_smul G E n τ g)

/-- The coefficient and simplex transform diagonally; their actual coinvariant class is unchanged. -/
theorem generator_diagonal (V : Rep ℚ G) (n : ℕ) (g : G)
    (τ : SingularSimplex E n) (v : V) :
    generator G E V n (g • τ) (V.ρ g v) = generator G E V n τ v := by
  change Representation.Coinvariants.mk _ ((V.ρ g v) ⊗ₜ[ℚ] chainElement G E n (g • τ)) = _
  rw [← chainElement_smul G E n g τ, ← TensorProduct.map_tmul,
    ← Representation.tprod_apply]
  exact Representation.Coinvariants.mk_self_apply _ g _

/-- Unit singular generators have the literal alternating singular-face boundary. -/
theorem chainElement_d (n : ℕ) (τ : SingularSimplex E (n+1)) :
    (equivariantD G E (n+1) n) (chainElement G E (n+1) τ) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • chainElement G E n ((TopCat.toSSet.obj E).δ i τ) := by
  have h := congrArg (fun f => f.hom (1 : ℚ)) ((TopCat.toSSet.obj E).ιChainComplex_d (R := ModuleCat.of ℚ ℚ) τ)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply] at h
  convert h using 1 <;> rfl

/-- The actual coinvariant singular differential keeps the coefficient while taking alternating faces. -/
theorem generator_boundary (V : Rep ℚ G) (n : ℕ) (τ : SingularSimplex E (n+1)) (v : V) :
    (coinvariantChains G E V).d (n+1) n (generator G E V (n+1) τ v) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • generator G E V n ((TopCat.toSSet.obj E).δ i τ) v := by
  change (((Rep.coinvariantsTensor ℚ G).obj V).map (equivariantD G E (n+1) n))
    (Rep.coinvariantsTensorMk V (chainRep G E (n+1)) v (chainElement G E (n+1) τ)) = _
  rw [tensorCoinvariant_map_mk, chainElement_d]
  simp only [map_sum, map_zsmul]
  rfl

end TernaryPoly.SingularLocalHomology
