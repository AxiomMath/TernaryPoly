module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison
open CategoryTheory Category Limits HomologicalComplex
open SingularComponentAugmentation FreeActionLinearization EquivariantSingularResolution
open scoped MonoidAlgebra Simplicial

variable {G ι κ : Type} [Group G] [MulAction G ι] [MulAction G κ]
  (u : ι → κ) (hu : ∀ (g : G) i,u (g • i)=g • u i) (hi : Function.Injective u)

/-- Coefficient restriction along an actual injective equivariant map of permutation bases. -/
def permutationRetractionLinear : ℚ[κ] →ₗ[ℚ] ℚ[ι] :=
  (MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap.comp
    ((Finsupp.lcomapDomain u hi).comp (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)

@[simp] theorem permutationRetraction_coeff (c : ℚ[κ]) (i : ι) :
    (permutationRetractionLinear u hi c).coeff i=c.coeff (u i) := rfl

/-- The coefficient restriction is equivariant for the original action. -/
def permutationRetraction : Rep.ofMulAction ℚ G κ ⟶ Rep.ofMulAction ℚ G ι :=
  Rep.ofHom ⟨permutationRetractionLinear u hi,fun g => by
    apply LinearMap.ext
    intro c
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro i
    change (permutationRetractionLinear u hi (Representation.ofMulAction ℚ G κ g c)).coeff i=
      (Representation.ofMulAction ℚ G ι g (permutationRetractionLinear u hi c)).coeff i
    rw [permutationRetraction_coeff,Representation.coeff_ofMulAction,Representation.coeff_ofMulAction,
      permutationRetraction_coeff,hu]⟩

theorem permutation_retraction : permutationMap u hu ≫ permutationRetraction u hu hi=𝟙 _ := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro i
  apply LinearMap.ext
  intro r
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro j
  change (permutationRetractionLinear u hi (permutationMap u hu (MonoidAlgebra.single i r))).coeff j=
    (MonoidAlgebra.single i r).coeff j
  rw [permutationMap_single,permutationRetraction_coeff]
  simp only [MonoidAlgebra.coeff_single,Finsupp.single_apply,hi.eq_iff]

variable {E F : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G F] [ContinuousConstSMul G F]
  (f : E ⟶ F) (hf : ∀ (g : G) x,f (g • x)=g • f x)

abbrev simplexMap (n : ℕ) : SingularSimplex E n → SingularSimplex F n :=
  (TopCat.toSSet.map f).app (.op ⦋n⦌)

include hf in
theorem simplexMap_equivariant (n : ℕ) (g : G) (x : SingularSimplex E n) :
    simplexMap f n (g • x)=g • simplexMap f n x := by
  apply (TopCat.toSSetObjEquiv F (.op ⦋n⦌)).injective
  ext t
  exact hf g (TopCat.toSSetObjEquiv E (.op ⦋n⦌) x t)

theorem simplexMap_injective (hfi : Function.Injective f) (n : ℕ) : Function.Injective (simplexMap f n) := by
  intro x y h
  apply (TopCat.toSSetObjEquiv E (.op ⦋n⦌)).injective
  ext t
  apply hfi
  exact congrArg (fun z => TopCat.toSSetObjEquiv F (.op ⦋n⦌) z t) h

/-- Every actual singular chain map is exactly the permutation map in its literal simplex bases. -/
theorem degreeMap_natural (n : ℕ) :
    (degreeRepIso G E n).hom ≫ (SingularCoverNaturality.chainMap f hf).f n=
      permutationMap (simplexMap f n) (simplexMap_equivariant f hf n) ≫ (degreeRepIso G F n).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro x
  apply LinearMap.ext
  intro r
  change (SingularCoverNaturality.underlyingMap f).f n (degreeLinearEquiv E n (MonoidAlgebra.single x r))=
    degreeLinearEquiv F n (permutationMap (simplexMap f n) (simplexMap_equivariant f hf n) (MonoidAlgebra.single x r))
  rw [permutationMap_single,degreeLinearEquiv_single,degreeLinearEquiv_single]
  exact congrArg (fun m => m r) (SingularCoverNaturality.generator_map f n x)

/-- An injective equivariant space map has a literal equivariant graded singular-chain retraction. -/
def degreeRetraction (hfi : Function.Injective f) (n : ℕ) :
    (equivariantChains G F).X n ⟶ (equivariantChains G E).X n :=
  (degreeRepIso G F n).inv ≫ permutationRetraction (simplexMap f n)
    (simplexMap_equivariant f hf n) (simplexMap_injective f hfi n) ≫ (degreeRepIso G E n).hom

theorem iso_retraction {C : Type*} [Category* C] {A A' B B' : C}
    (e : A ≅ A') (d : B ≅ B') (f : A' ⟶ B') (p : A ⟶ B) (q : B ⟶ A)
    (h : e.hom ≫ f=p ≫ d.hom) (hq : p ≫ q=𝟙 _) :
    f ≫ (d.inv ≫ q ≫ e.hom)=𝟙 _ := by
  apply (cancel_epi e.hom).mp
  rw [←Category.assoc,h]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  rw [←Category.assoc,hq,id_comp,comp_id]

theorem degreeMap_retraction (hfi : Function.Injective f) (n : ℕ) :
    (SingularCoverNaturality.chainMap f hf).f n ≫ degreeRetraction f hf hfi n=𝟙 _ :=
  iso_retraction (degreeRepIso G E n) (degreeRepIso G F n) _ _ _
    (degreeMap_natural f hf n) (permutation_retraction _ _ _)

end TernaryPoly.BoundaryFaceResolutionComparison
