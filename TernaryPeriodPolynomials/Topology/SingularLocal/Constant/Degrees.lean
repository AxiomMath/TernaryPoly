module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Coordinates
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalConstant
open CategoryTheory Limits AlgebraicTopology
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open scoped Classical TensorProduct

variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- Mathlib's actual singular chain complex with the arbitrary rational coefficient object. -/
abbrev ordinaryChains := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj V).obj X

/-- The genuine coproduct defining ordinary singular chains is the finitely supported module. -/
def ordinaryFinsuppIso (n : ℕ) :
    (ordinaryChains X V).X n ≅ ModuleCat.of ℚ (SingularSimplex X n →₀ V) :=
  (TopCat.toSSet.obj X).isColimitChainComplexXCofan V n |>.coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℚ V (SingularSimplex X n))

/-- The coproduct comparison sends each coefficient to the same actual singular generator. -/
theorem ordinaryFinsuppIso_inv_single (n : ℕ) (σ : SingularSimplex X n) (v : V) :
    (ordinaryFinsuppIso X V n).inv (Finsupp.single σ v) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := V) σ) v := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_inv
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan V n)
    (ModuleCat.finsuppCoconeIsColimit ℚ V (SingularSimplex X n)) ⟨σ⟩
  exact congrArg (fun f => f v) h

/-- The canonical comparison from actual local chains to ordinary V-coefficient chains. -/
def chainDegreeEquiv (n : ℕ) : (chains X V).X n ≃ₗ[ℚ] (ordinaryChains X V).X n :=
  chainValueEquiv X V n ≪≫ₗ (ordinaryFinsuppIso X V n).symm.toLinearEquiv

/-- The comparison on actual elementary geometric chains keeps the simplex and its canonical fiber value. -/
theorem chainDegreeEquiv_single (n : ℕ) (σ : SingularSimplex X n)
    (c : FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex σ)) :
    chainDegreeEquiv X V n (DFinsupp.single (β := fun τ : SingularSimplex X n =>
      FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex τ)) σ c) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := V) σ) (fiberEquiv X V (atVertex σ) c) := by
  exact (congrArg (ordinaryFinsuppIso X V n).inv (chainValueEquiv_single X V n σ c)).trans
    (ordinaryFinsuppIso_inv_single X V n σ _)

/-- Actual V-coefficient singular chains are degreewise rational singular chains tensored with V. -/
def tensorDegreeEquiv (n : ℕ) :
    ((EquivariantSingularResolution.underlyingChains X).X n ⊗[ℚ] V) ≃ₗ[ℚ]
      (ordinaryChains X V).X n :=
  TensorProduct.congr (EquivariantSingularResolution.degreeFinsuppIso X n).toLinearEquiv
      (LinearEquiv.refl ℚ V) ≪≫ₗ
    TensorProduct.finsuppScalarLeft ℚ V (SingularSimplex X n) ≪≫ₗ
    (ordinaryFinsuppIso X V n).symm.toLinearEquiv

end TernaryPoly.SingularLocalConstant
