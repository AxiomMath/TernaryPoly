module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.UnionHomologyAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalOpenUnion
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalHomology SingularLocalExcision EquivariantSingularSmall
open SingularLocalCap SingularLocalCap.Homology SingularLocalCompactCap.Algebra
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]

/-- Actual local-chain subset inclusions are injective in every degree. -/
theorem localInclusion_degree_injective (A : Set B) (k : ℕ) :
    Function.Injective ((localInclusion p A V).f k) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

variable (U : ℕ → Opens B) (hU : Monotone U)
  (hcover : (⋃ i, (U i : Set B)) = Set.univ)
include hU hcover

/-- Every actual ambient local-homology class is induced by a genuine cycle on one
stage; injectivity of literal chain inclusion ensures that the lifted chain is a cycle. -/
theorem homology_stage_exists (b : ℕ) (h : (localChains p hp.out V).homology b) :
    ∃ i, ∃ z : (restrictedLocalChains p (U i) V).homology b,
      homologyMap (localInclusion p (U i) V) b z = h := by
  obtain ⟨c,rfl⟩ := chainClass_surjective _ b h
  obtain ⟨i,x,hx⟩ := local_chain_stage p V U hU hcover b c.val
  let z := liftChainCycle (localInclusion p (U i) V)
    (localInclusion_degree_injective p V (U i)) b c x hx
  refine ⟨i,Descent.chainClass _ b z,?_⟩
  rw [chainClass_map]
  exact congrArg (Descent.chainClass _ b) (Subtype.ext hx)

/-- Every relation killing an actual stage homology class in the ambient space is
already witnessed at a later stage by the compact finite carrier of its bounding chain. -/
theorem homology_stage_zero (b i : ℕ) (h : (restrictedLocalChains p (U i) V).homology b)
    (hh : homologyMap (localInclusion p (U i) V) b h = 0) :
    ∃ (j : ℕ) (hij : i ≤ j), homologyMap (nestedLocalInclusion p (U i) (U j) (hU hij) V) b h = 0 := by
  obtain ⟨c,rfl⟩ := chainClass_surjective _ b h
  rw [chainClass_map] at hh
  obtain ⟨d,hd⟩ := (chainClass_zero_iff _ b (mapChainCycle (localInclusion p (U i) V) b c)).mp hh
  obtain ⟨j,x,hx⟩ := local_chain_stage p V U hU hcover (b+1) d
  let m := max i j
  have him : i ≤ m := le_max_left _ _
  have hjm : j ≤ m := le_max_right _ _
  let t := nestedLocalInclusion p (U i) (U m) (hU him) V
  let s := nestedLocalInclusion p (U j) (U m) (hU hjm) V
  let y := s.f (b+1) x
  refine ⟨m,him,?_⟩
  rw [chainClass_map]
  apply (chainClass_zero_iff _ b (mapChainCycle t b c)).mpr
  refine ⟨y,?_⟩
  apply localInclusion_degree_injective p V (U m) b
  have hD := congrArg (fun f => f y) ((localInclusion p (U m) V).comm (b+1) b)
  have hx' := congrArg (fun f => f x) (HomologicalComplex.congr_hom
    (nestedLocalInclusion_inclusion p (U j) (U m) (hU hjm) V) (b+1))
  have hc' := congrArg (fun f => f c.val) (HomologicalComplex.congr_hom
    (nestedLocalInclusion_inclusion p (U i) (U m) (hU him) V) b)
  exact hD.symm.trans ((congrArg ((localChains p hp.out V).d (b+1) b) (hx'.trans hx)).trans
    (hd.trans hc'.symm))

end TernaryPoly.SingularLocalOpenUnion
