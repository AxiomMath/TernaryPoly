module

/- Adapted from the rational predecessor EquivariantSingularSmallBasis.lean by explicit base-ring
replacement to ℝ and the actual SmoothSingularGlobal chain model. -/
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Projective
public import TernaryPeriodPolynomials.Topology.SingularHomology.SmallChainComplex
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Module CategoryTheory FreeActionLinearization SmoothSingularGlobal
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
open scoped Classical MonoidAlgebra

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]

/-- The literal chain generator used by the subdivision port is the project's singular generator. -/
theorem chainGenerator_eq (n : ℕ) (σ : SingularSimplex E n) :
    chainGenerator ℝ E n σ = (TopCat.toSSet.obj E).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ 1 := rfl

/-- The actual chain action permutes the port's singular generators. -/
theorem chainAction_generator (n : ℕ) (g : G) (σ : SingularSimplex E n) :
    chainAction G E n g (chainGenerator ℝ E n σ) = chainGenerator ℝ E n (g • σ) :=
  congrArg (fun m => m.hom 1) (generator_smul G E n σ g)

/-- The genuine singular generators form a basis of the actual chain module. -/
def generatorBasis (n : ℕ) : Basis (SingularSimplex E n) ℝ ((underlyingChains E).X n) :=
  (Finsupp.basisSingleOne : Basis (SingularSimplex E n) ℝ (SingularSimplex E n →₀ ℝ)).map
    (degreeFinsuppIso E n).symm.toLinearEquiv

/-- The singular basis uses the literal subdivision-port generators. -/
theorem generatorBasis_apply (n : ℕ) (σ : SingularSimplex E n) :
    generatorBasis E n σ = chainGenerator ℝ E n σ :=
  degreeFinsuppIso_inv_single E n σ 1

/-- The actual span of singular simplices satisfying a specified predicate. -/
def predicateSpan (n : ℕ) (P : SingularSimplex E n → Prop) : Submodule ℝ ((underlyingChains E).X n) :=
  Submodule.span ℝ {c | ∃ σ, P σ ∧ chainGenerator ℝ E n σ = c}

/-- The predicate span is precisely the span of its literal subtype-indexed generators. -/
theorem predicateSpan_eq_range (n : ℕ) (P : SingularSimplex E n → Prop) :
    predicateSpan E n P = Submodule.span ℝ (Set.range (fun σ : {σ // P σ} => chainGenerator ℝ E n σ.val)) := by
  apply congrArg (Submodule.span ℝ)
  ext c
  constructor
  · rintro ⟨σ, hσ, hc⟩
    exact ⟨⟨σ,hσ⟩,hc⟩
  · rintro ⟨σ, hc⟩
    exact ⟨σ.val,σ.property,hc⟩

/-- A basis of the genuine predicate span, indexed by exactly its allowed singular simplices. -/
def predicateBasis (n : ℕ) (P : SingularSimplex E n → Prop) :
    Basis {σ // P σ} ℝ (predicateSpan E n P) := by
  have hli : LinearIndependent ℝ (fun σ : {σ // P σ} => chainGenerator ℝ E n σ.val) := by
    have h := (generatorBasis E n).linearIndependent.comp (fun σ : {σ // P σ} => σ.val)
      Subtype.val_injective
    simpa only [Function.comp_def, generatorBasis_apply] using h
  exact (Basis.span hli).map (LinearEquiv.ofEq _ _ (predicateSpan_eq_range E n P).symm)

/-- Basis vectors of the predicate span retain the literal underlying singular generator. -/
theorem predicateBasis_apply (n : ℕ) (P : SingularSimplex E n → Prop) (σ : {σ // P σ}) :
    (predicateBasis E n P σ).val = chainGenerator ℝ E n σ.val := by
  simp [predicateBasis]

variable (n : ℕ) (P : SingularSimplex E n → Prop)
  [hP : Fact (∀ (g : G) (σ : SingularSimplex E n), P σ → P (g • σ))]

include hP in
/-- Invariance of the simplex family makes its actual generator span stable under the chain action. -/
theorem predicateSpan_invariant (g : G) {c : (underlyingChains E).X n}
    (hc : c ∈ predicateSpan E n P) : chainAction G E n g c ∈ predicateSpan E n P := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    rw [chainAction_generator]
    exact Submodule.subset_span ⟨g • σ,hP.out g σ hσ,rfl⟩
  | zero => simpa only [map_zero] using (predicateSpan E n P).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using (predicateSpan E n P).add_mem ihx ihy
  | smul a x hx ih => simpa only [map_smul] using (predicateSpan E n P).smul_mem a ih

/-- The actual invariant predicate span as a subrepresentation of singular chains. -/
def predicateSubrepresentation : Subrepresentation (chainAction G E n) where
  toSubmodule := predicateSpan E n P
  apply_mem_toSubmodule g _ hc := predicateSpan_invariant G E n P g hc

/-- The representation on the actual predicate-span module. -/
abbrev predicateRep : Rep ℝ G := Rep.of (predicateSubrepresentation G E n P).toRepresentation

/-- The restricted deck action on the actual allowed-simplex subtype. -/
instance predicateMulAction : MulAction G {σ // P σ} where
  smul g σ := ⟨g • σ.val,hP.out g σ.val σ.property⟩
  one_smul σ := Subtype.ext (one_smul G σ.val)
  mul_smul g h σ := Subtype.ext (mul_smul g h σ.val)

/-- Freeness of the space action implies freeness on every invariant family of singular simplices. -/
instance predicateIsCancelSMul [IsCancelSMul G E] : IsCancelSMul G {σ // P σ} where
  right_cancel' g h σ he :=
    (inferInstance : IsCancelSMul G (SingularSimplex E n)).right_cancel' g h σ.val
      (congrArg Subtype.val he)

/-- The literal finitely supported allowed-simplex module is linearly the actual predicate span. -/
def predicateLinearEquiv : ℝ[{σ // P σ}] ≃ₗ[ℝ] predicateSpan E n P :=
  MonoidAlgebra.coeffLinearEquiv ℝ ≪≫ₗ (predicateBasis E n P).repr.symm

/-- A single allowed-simplex coefficient maps to its literal singular-chain multiple. -/
theorem predicateLinearEquiv_single (σ : {σ // P σ}) (r : ℝ) :
    (predicateLinearEquiv E n P (MonoidAlgebra.single σ r)).val = r • chainGenerator ℝ E n σ.val := by
  change ((predicateBasis E n P).repr.symm (Finsupp.single σ r)).val = _
  rw [Basis.repr_symm_single]
  exact congrArg (r • ·) (predicateBasis_apply E n P σ)

/-- The genuine predicate-span representation is the actual permutation representation of its simplices. -/
def predicatePermutationIso : Rep.ofMulAction ℝ G {σ // P σ} ≅ predicateRep G E n P :=
  Rep.mkIso (.mk (predicateLinearEquiv E n P) (fun g => by
    apply MonoidAlgebra.lhom_ext'
    intro σ
    apply LinearMap.ext
    intro r
    apply Subtype.ext
    change (predicateLinearEquiv E n P
      (Representation.ofMulAction ℝ G {σ // P σ} g (MonoidAlgebra.single σ r))).val =
      chainAction G E n g (predicateLinearEquiv E n P (MonoidAlgebra.single σ r)).val
    rw [Representation.ofMulAction_single, predicateLinearEquiv_single, predicateLinearEquiv_single,
      map_smul, chainAction_generator]
    rfl))

/-- The actual invariant predicate-span representation is free on its actual simplex orbits. -/
def predicateIsoFree [IsCancelSMul G E] :
    predicateRep G E n P ≅ Rep.free ℝ G (Orbits G {σ // P σ}) :=
  (predicatePermutationIso G E n P).symm ≪≫ permutationIsoFree ℝ G {σ // P σ}

/-- Every actual invariant singular predicate-span representation is projective. -/
instance predicateRep_projective [IsCancelSMul G E] : Projective (predicateRep G E n P) :=
  Projective.of_iso (predicatePermutationIso G E n P)
    (permutation_projective ℝ G {σ // P σ})

end TernaryPoly.SmoothSingularGlobal
