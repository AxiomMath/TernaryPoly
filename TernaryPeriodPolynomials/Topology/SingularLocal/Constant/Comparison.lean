module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Degrees

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalConstant
open CategoryTheory Limits
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open scoped Classical Simplicial
variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- The ordinary V-coefficient differential is the literal alternating sum of the same singular faces. -/
theorem ordinary_boundary_generator (n : ℕ) (σ : SingularSimplex X (n+1)) (v : V) :
    (ordinaryChains X V).d (n+1) n (((TopCat.toSSet.obj X).ιChainComplex (R := V) σ) v) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        ((TopCat.toSSet.obj X).ιChainComplex (R := V) (pullSimplex (simplexCoface n i) σ)) v := by
  have h := congrArg (fun f : V ⟶ (ordinaryChains X V).X n => f.hom v)
    ((TopCat.toSSet.obj X).ιChainComplex_d (R := V) σ)
  erw [ModuleCat.hom_sum] at h
  simp only [LinearMap.sum_apply] at h
  exact h


/-- Canonical fiber evaluation intertwines the actual transported local boundary and
ordinary coefficient boundary on every genuine simplex coefficient. -/
theorem chainDegreeEquiv_boundary_single (n : ℕ) (σ : SingularSimplex X (n+1))
    (c : FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex σ)) :
    chainDegreeEquiv X V n (boundary (𝟙 X) (identityCover X) (constantRep V) n
      (DFinsupp.single (β := fun τ : SingularSimplex X (n+1) =>
        FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex τ)) σ c)) =
      (ordinaryChains X V).d (n+1) n (chainDegreeEquiv X V (n+1)
        (DFinsupp.single (β := fun τ : SingularSimplex X (n+1) =>
          FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex τ)) σ c)) := by
  have hb := congrArg (chainDegreeEquiv X V n)
    (boundary_single (𝟙 X) (identityCover X) (constantRep V) n σ c)
  refine hb.trans ?_
  rw [chainDegreeEquiv_single, ordinary_boundary_generator]
  refine (map_sum (chainDegreeEquiv X V n) _ _).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  refine (map_zsmul (chainDegreeEquiv X V n) _ _).trans ?_
  exact congrArg (fun v => (-1 : ℤ)^i.val • v)
    ((chainDegreeEquiv_single X V n _ _).trans
      (congrArg ((TopCat.toSSet.obj X).ιChainComplex (R := V)
        (pullSimplex (simplexCoface n i) σ)) (fiberEquiv_transport X V _ c)))

/-- The comparison intertwines the two actual linear differential maps. -/
theorem chainDegreeEquiv_boundary (n : ℕ) :
    (chainDegreeEquiv X V n).toLinearMap.comp
        (boundary (𝟙 X) (identityCover X) (constantRep V) n) =
      ((ordinaryChains X V).d (n+1) n).hom.comp (chainDegreeEquiv X V (n+1)).toLinearMap := by
  exact DFinsupp.lhom_ext (M := fun σ : SingularSimplex X (n+1) =>
    FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex σ))
      (chainDegreeEquiv_boundary_single X V n)

/-- The genuine constant local complex is isomorphic to Mathlib's ordinary singular
complex with the same arbitrary coefficient module; the maps are canonical fiber evaluations. -/
def ordinaryChainIso : chains X V ≅ ordinaryChains X V :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (chainDegreeEquiv X V n).toModuleIso)
    (fun i j hij => by
      obtain rfl : i = j+1 := hij.symm
      apply ModuleCat.hom_ext
      simp only [chains, localChains, ChainComplex.of_d]
      exact (chainDegreeEquiv_boundary X V j).symm)

end TernaryPoly.SingularLocalConstant
