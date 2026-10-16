module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Fibers

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalConstant
open CategoryTheory Limits
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SphereOddDegree.AffineBarycentricSubdivision
open scoped Classical

variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- The pointwise rational module instance on the actual dependent coefficient sum. -/
@[reducible] instance chainModule (n : ℕ) :
    Module ℚ (VertexChain (𝟙 X) (identityCover X) (constantRep V) n) :=
  inferInstanceAs (Module ℚ (Π₀ σ : SingularSimplex X n,
    FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex σ)))

/-- The genuine local chains of the identity covering with arbitrary constant coefficients. -/
abbrev chains := localChains (𝟙 X) (identityCover X) (constantRep V)

/-- The genuine geometric local cochains of the identity covering. -/
abbrev cochains := localCochains (𝟙 X) (identityCover X) (constantRep V)

/-- Canonical coefficient evaluation identifies actual vertex cochains with V-valued simplex functions. -/
def cochainValueEquiv (n : ℕ) :
    VertexCochain (𝟙 X) (identityCover X) (constantRep V) n ≃ₗ[ℚ] (SingularSimplex X n → V) :=
  LinearEquiv.piCongrRight (fun σ => fiberEquiv X V (atVertex σ))

/-- Canonical fiber evaluation identifies actual dependent finite chains with finitely
supported V-valued functions on the same genuine singular simplices. -/
def chainValueEquiv (n : ℕ) :
    VertexChain (𝟙 X) (identityCover X) (constantRep V) n ≃ₗ[ℚ] (SingularSimplex X n →₀ V) :=
  DFinsupp.mapRange.linearEquiv (fun σ => fiberEquiv X V (atVertex σ)) ≪≫ₗ
    (finsuppLequivDFinsupp ℚ).symm

/-- A single geometric coefficient retains its actual singular simplex under trivialization. -/
theorem chainValueEquiv_single (n : ℕ) (σ : SingularSimplex X n)
    (c : FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex σ)) :
    chainValueEquiv X V n (DFinsupp.single (β := fun τ : SingularSimplex X n =>
      FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex τ)) σ c) = Finsupp.single σ (fiberEquiv X V (atVertex σ) c) := by
  classical
  change (DFinsupp.mapRange (fun τ => fiberEquiv X V (atVertex τ)) (fun τ => map_zero _)
    (DFinsupp.single (β := fun τ : SingularSimplex X n =>
      FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex τ)) σ c)).toFinsupp = _
  rw [DFinsupp.mapRange_single, DFinsupp.toFinsupp_single]

/-- The literal finite sum of the canonically identified chain coefficients. In degree
zero this is the augmentation that will descend to actual homology. -/
def coefficientSum (n : ℕ) :
    VertexChain (𝟙 X) (identityCover X) (constantRep V) n →ₗ[ℚ] V :=
  DFinsupp.lsum ℚ (fun σ => (fiberEquiv X V (atVertex σ)).toLinearMap)

/-- The coefficient sum of one simplex is its actual fiber value. -/
theorem coefficientSum_single (n : ℕ) (σ : SingularSimplex X n)
    (c : FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex σ)) :
    coefficientSum X V n (DFinsupp.single (β := fun τ : SingularSimplex X n =>
      FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex τ)) σ c) = fiberEquiv X V (atVertex σ) c := by
  classical
  exact DFinsupp.lsum_single ℚ (fun τ => (fiberEquiv X V (atVertex τ)).toLinearMap) σ c

/-- Literal V-valued evaluation of a geometric cochain on an ordinary rational chain. -/
def evaluation (n : ℕ) (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) n) :
    singularChainGroup ℚ X n →ₗ[ℚ] V :=
  (Sigma.desc fun σ : SingularSimplex X n => ModuleCat.ofHom
    (LinearMap.toSpanSingleton ℚ V (fiberEquiv X V (atVertex σ) (φ σ)))).hom

/-- Evaluation on an actual scalar singular generator is its canonical cochain value. -/
theorem evaluation_generator (n : ℕ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) n) (σ : SingularSimplex X n) :
    evaluation X V n φ (chainGenerator ℚ X n σ) = fiberEquiv X V (atVertex σ) (φ σ) := by
  have h := congrArg (fun f : ModuleCat.of ℚ ℚ ⟶ V => f.hom (1 : ℚ))
    (Sigma.ι_comp_desc (fun σ : SingularSimplex X n => ModuleCat.ofHom
      (LinearMap.toSpanSingleton ℚ V (fiberEquiv X V (atVertex σ) (φ σ)))) σ)
  exact h.trans (one_smul ℚ _)

end TernaryPoly.SingularLocalConstant
