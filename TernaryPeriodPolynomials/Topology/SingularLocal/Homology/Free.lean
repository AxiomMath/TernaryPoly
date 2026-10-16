module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Generators

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory EquivariantSingularResolution FreeActionLinearization
open scoped MonoidAlgebra TensorProduct

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  [IsCancelSMul G E]

/-- Actual singular chain representations are free on the literal orbit set of singular simplices. -/
def chainRepIsoFree (n : ℕ) :
    chainRep G E n ≅ Rep.free ℚ G (Orbits G (SingularSimplex E n)) :=
  (degreeRepIso G E n).symm ≪≫ singularPermutationIsoFree ℚ G E n

/-- The regular basis vector at group identity maps to the actual chosen orbit representative. -/
theorem chainRepIsoFree_inv_single (n : ℕ) (q : Orbits G (SingularSimplex E n)) :
    (chainRepIsoFree G E n).inv (Finsupp.single q (MonoidAlgebra.single (1 : G) (1 : ℚ))) =
      chainElement G E n q.out := by
  change degreeLinearEquiv E n ((permutationIsoFree ℚ G (SingularSimplex E n)).inv.hom
    (Finsupp.single q (MonoidAlgebra.single (1 : G) (1 : ℚ)))) = _
  rw [permutationIsoFree_inv_single, one_smul, degreeLinearEquiv_single]
  rfl

/-- The actual coinvariant singular degree is the finitely supported coefficient module on
actual simplex orbits, through the genuine representation isomorphism and coinvariant tensor map. -/
def orbitCoefficientEquiv (V : Rep ℚ G) (n : ℕ) :
    (coinvariantChains G E V).X n ≃ₗ[ℚ] (Orbits G (SingularSimplex E n) →₀ V) := by
  classical
  exact (((Rep.coinvariantsTensor ℚ G).obj V).mapIso (chainRepIsoFree G E n)).toLinearEquiv ≪≫ₗ
    Rep.coinvariantsTensorFreeLEquiv V (Orbits G (SingularSimplex E n))

/-- The inverse orbit-coordinate map sends a single coefficient to the literal representative tensor. -/
theorem orbitCoefficientEquiv_symm_single (V : Rep ℚ G) (n : ℕ)
    (q : Orbits G (SingularSimplex E n)) (v : V) :
    (orbitCoefficientEquiv G E V n).symm (Finsupp.single q v) = generator G E V n q.out v := by
  classical
  change (((Rep.coinvariantsTensor ℚ G).obj V).map (chainRepIsoFree G E n).inv)
    (Rep.finsuppToCoinvariantsTensorFree V (Orbits G (SingularSimplex E n)) (Finsupp.single q v)) = _
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  change (((Rep.coinvariantsTensor ℚ G).obj V).map (chainRepIsoFree G E n).inv)
    (Rep.coinvariantsTensorMk V (Rep.free ℚ G (Orbits G (SingularSimplex E n))) v
      (Finsupp.single q (MonoidAlgebra.single (1 : G) (1 : ℚ)))) = _
  rw [tensorCoinvariant_map_mk, chainRepIsoFree_inv_single]
  rfl

end TernaryPoly.SingularLocalHomology
