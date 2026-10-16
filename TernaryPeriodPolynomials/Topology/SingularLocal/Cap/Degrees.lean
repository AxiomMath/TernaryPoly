module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Homology

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCap
open CategoryTheory AlgebraicTopology
open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision

/-- The next degree of a natural-number chain complex, including degree zero. -/
theorem down_next (n : ℕ) : (ComplexShape.down ℕ).next n = n-1 := by
  cases n with
  | zero => exact (ComplexShape.down ℕ).next_eq_self' 0 (by intro k; simp)
  | succ n => exact (ComplexShape.down ℕ).next_eq' rfl

/-- The previous degree of a natural-number chain complex. -/
theorem down_prev (n : ℕ) : (ComplexShape.down ℕ).prev n = n+1 :=
  (ComplexShape.down ℕ).prev_eq' rfl

/-- The next degree of a natural-number cochain complex. -/
theorem up_next (n : ℕ) : (ComplexShape.up ℕ).next n = n+1 :=
  (ComplexShape.up ℕ).next_eq' rfl

/-- The previous degree of a natural-number cochain complex, including degree zero. -/
theorem up_prev (n : ℕ) : (ComplexShape.up ℕ).prev n = n-1 := by
  cases n with
  | zero => exact (ComplexShape.up ℕ).prev_eq_self' 0 (by intro k; simp)
  | succ n => exact (ComplexShape.up ℕ).prev_eq' rfl

/-- Scalar singular chains with their actual alternating boundary. -/
abbrev scalarChains (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).obj X

/-- The Alexander-Whitney degree relabelling is the canonical degree isomorphism. -/
theorem scalarCastLeft_eq (X : TopCat.{0}) (a b : ℕ) :
    scalarCastLeft X a b =
      ((scalarChains X).XIsoOfEq (show a+b+1 = a+1+b by omega)).hom.hom := by
  unfold scalarCastLeft
  rw [show (awCastLeft a b).op = eqToHom (by rw [aw_degree_left_succ a b]) from ?_]
  · rw [eqToHom_map]
    rfl
  · rw [awCastLeft, eqToHom_op]

/-- The inverse canonical degree relabelling, used to cap a coboundary. -/
def scalarCastRight (X : TopCat.{0}) (a b : ℕ) :
    singularChainGroup ℚ X (a+1+b) →ₗ[ℚ] singularChainGroup ℚ X (a+b+1) :=
  ((scalarChains X).XIsoOfEq (show a+b+1 = a+1+b by omega)).inv.hom

/-- The two actual degree relabellings cancel. -/
theorem scalarCastLeft_right (X : TopCat.{0}) (a b : ℕ)
    (c : singularChainGroup ℚ X (a+1+b)) :
    scalarCastLeft X a b (scalarCastRight X a b c) = c := by
  rw [scalarCastLeft_eq]
  exact congrArg (fun f => f c)
    ((scalarChains X).XIsoOfEq (show a+b+1 = a+1+b by omega)).inv_hom_id

/-- Relabelling a scalar cycle preserves its actual zero boundary. -/
theorem scalarCastRight_cycle (X : TopCat.{0}) (a b : ℕ)
    (c : singularChainGroup ℚ X (a+1+b))
    (hc : (scalarChains X).d (a+1+b) (a+1+b-1) c = 0) :
    (singularBoundary ℚ X (a+b)).hom (scalarCastRight X a b c) = 0 := by
  have h := congrArg (fun f => f c)
    ((scalarChains X).XIsoOfEq_inv_comp_d (show a+b+1 = a+1+b by omega) (a+b))
  change (singularBoundary ℚ X (a+b)).hom (scalarCastRight X a b c) =
    (scalarChains X).d (a+1+b) (a+b) c at h
  rw [h]
  have he : a+1+b-1 = a+b := by omega
  have hd := congrArg (fun f => f c) ((scalarChains X).d_comp_XIsoOfEq_hom he (a+1+b))
  rw [← hd]
  change ((scalarChains X).XIsoOfEq he).hom ((scalarChains X).d (a+1+b) (a+1+b-1) c) = 0
  rw [hc, map_zero]

end TernaryPoly.SingularLocalCap
