module

public import TernaryPeriodPolynomials.GroupCohomology.FreeAction.ActionLinearizationSingular
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Tactic.NoncommRing

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringSingularOrbits
open CategoryTheory FreeActionLinearization
open scoped Simplicial
variable {G : Type} [Group G] {E B : TopCat} [MulAction G E] [ContinuousConstSMul G E]

/-- The literal map on Mathlib singular simplices induced by the covering projection. -/
def projection (p : E ⟶ B) (n : ℕ) : SingularSimplex E n → SingularSimplex B n :=
  (TopCat.toSSet.map p).app (.op ⦋n⦌)

/-- A fixed actual vertex supplies the lift base point. -/
def vertex (n : ℕ) : Convexity.StdSimplex ℝ (Fin (n+1)) :=
  Convexity.StdSimplex.single 0

/-- The standard simplex is homeomorphic to its set of barycentric weight vectors. -/
def weightsHomeomorph (n : ℕ) : Convexity.StdSimplex ℝ (Fin (n+1)) ≃ₜ
    Set.range (fun t : Convexity.StdSimplex ℝ (Fin (n+1)) => ⇑t.weights) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).toHomeomorph

/-- The barycentric weight vectors form a convex set. -/
theorem convex_range_weights (n : ℕ) :
    Convex ℝ (Set.range (fun t : Convexity.StdSimplex ℝ (Fin (n+1)) => ⇑t.weights)) := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  intro f hf g hg a b ha hb hab
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hf hg ⊢
  refine ⟨fun x => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hf.1 x)) (mul_nonneg hb (hg.1 x))
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one, hab]

instance simplexContractible (n : ℕ) : ContractibleSpace (Convexity.StdSimplex ℝ (Fin (n+1))) :=
  haveI := (convex_range_weights n).contractibleSpace ⟨_, Set.mem_range_self (vertex n)⟩
  (weightsHomeomorph n).contractibleSpace

instance simplexLocallyPathConnected (n : ℕ) :
    LocallyPathConnectedSpace (Convexity.StdSimplex ℝ (Fin (n+1))) :=
  haveI := (convex_range_weights n).locallyPathConnectedSpace
  (weightsHomeomorph n).symm.locallyPathConnectedSpace

@[simp] theorem projection_equiv (p : E ⟶ B) (n : ℕ) (σ : SingularSimplex E n) :
    TopCat.toSSetObjEquiv B (.op ⦋n⦌) (projection p n σ)=
      p.hom.comp (TopCat.toSSetObjEquiv E (.op ⦋n⦌) σ) := rfl

omit [ContinuousConstSMul G E] in
/-- Every actual singular simplex downstairs lifts to the covering space. -/
theorem projection_surjective (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (n : ℕ) :
    Function.Surjective (projection p n) := by
  intro σ
  let f := TopCat.toSSetObjEquiv B (.op ⦋n⦌) σ
  obtain ⟨e,he⟩ := hp.surjective (f (vertex n))
  obtain ⟨F,⟨_,hF⟩,_⟩ := hp.isCoveringMap.existsUnique_continuousMap_lifts f (vertex n) e he
  refine ⟨(TopCat.toSSetObjEquiv E (.op ⦋n⦌)).symm F,?_⟩
  apply (TopCat.toSSetObjEquiv B (.op ⦋n⦌)).injective
  rw [projection_equiv,Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  exact congrFun hF

/-- The deck action preserves the literal projected simplex. -/
theorem projection_smul (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    (n : ℕ) (g : G) (σ : SingularSimplex E n) :
    projection p n (g • σ)=projection p n σ := by
  apply (TopCat.toSSetObjEquiv B (.op ⦋n⦌)).injective
  rw [projection_equiv,projection_equiv,singularEquiv_smul]
  apply ContinuousMap.ext
  intro a
  exact hp.map_smul g

/-- Two genuine lifts of a simplex differ by one constant deck transformation. -/
theorem projection_eq_iff_orbit (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    (n : ℕ) (σ τ : SingularSimplex E n) :
    projection p n σ=projection p n τ ↔ σ∈MulAction.orbit G τ := by
  constructor
  · intro h
    let f := TopCat.toSSetObjEquiv E (.op ⦋n⦌) σ
    let k := TopCat.toSSetObjEquiv E (.op ⦋n⦌) τ
    have heq : p ∘ f=p ∘ k := by
      have hh := congrArg (fun s => (TopCat.toSSetObjEquiv B (.op ⦋n⦌) s).toFun) h
      exact hh
    obtain ⟨g,hg⟩ := hp.apply_eq_iff_mem_orbit.mp (congrFun heq (vertex n))
    refine ⟨g,?_⟩
    apply (TopCat.toSSetObjEquiv E (.op ⦋n⦌)).injective
    rw [singularEquiv_smul]
    apply ContinuousMap.ext
    apply congrFun (hp.isCoveringMap.eq_of_comp_eq
      (continuous_const_smul g |>.comp k.continuous) f.continuous ?_ (vertex n) hg)
    funext a
    exact (hp.map_smul g).trans (congrFun heq a).symm
  · rintro ⟨g,rfl⟩
    exact projection_smul p hp n g τ

/-- Actual singular simplices downstairs are precisely deck orbits of singular simplices upstairs. -/
def orbitEquiv (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (n : ℕ) :
    MulAction.orbitRel.Quotient G (SingularSimplex E n) ≃ SingularSimplex B n :=
  Equiv.ofBijective
    (Quotient.lift (projection p n) (fun σ τ h => (projection_eq_iff_orbit p hp n σ τ).mpr h))
    ⟨by
      intro a b h
      induction a using Quotient.inductionOn with | _ σ =>
        induction b using Quotient.inductionOn with | _ τ =>
          exact Quotient.sound ((projection_eq_iff_orbit p hp n σ τ).mp h),
     by
      intro σ
      obtain ⟨τ,hτ⟩ := projection_surjective p hp n σ
      exact ⟨Quotient.mk _ τ,hτ⟩⟩

end TernaryPoly.CoveringSingularOrbits
