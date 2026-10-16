module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularPresheaf
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoefficientGluing
public import TernaryPeriodPolynomials.Topology.Covering.SingularOrbits

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set
open SymmetricSpaceCovering FreeActionLinearization
open scoped Simplicial
variable {F : Type} [AddCommGroup F] [Module ℝ F]
  (ρ : Representation ℝ DeckGroup F) (U : Set OrbitSpace)

/-- An actual coefficient section evaluated on the unique vertex of an actual singular zero-simplex. -/
def coefficientSimplex : coefficientSections ρ U →ₗ[ℝ]
    equivariantFunctions DeckGroup (TopCat.of (CoverOpen U)) (Rep.of ρ) 0 where
  toFun f := ⟨fun σ => f.val (TopCat.toSSetObjEquiv _ (.op ⦋0⦌) σ (CoveringSingularOrbits.vertex 0)), by
    intro g σ
    dsimp only
    rw [singularEquiv_smul]
    exact f.property g _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extend the actual vertex-value function linearly to the genuine real equivariant singular chains. -/
def coefficientSingularMap : coefficientSections ρ U →ₗ[ℝ]
    (chainRep DeckGroup (TopCat.of (CoverOpen U)) 0 ⟶ Rep.of ρ) :=
  (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen U)) (Rep.of ρ) 0).symm.toLinearMap.comp
    (coefficientSimplex ρ U)

/-- The singular augmentation is literally evaluation of the coefficient section on zero-simplices. -/
theorem coefficientSingularMap_eval (f : coefficientSections ρ U)
    (σ : SingularSimplex (TopCat.of (CoverOpen U)) 0) :
    cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen U)) (Rep.of ρ) 0
      (coefficientSingularMap ρ U f) σ =
    f.val (TopCat.toSSetObjEquiv _ (.op ⦋0⦌) σ (CoveringSingularOrbits.vertex 0)) := by
  exact congrArg (fun a => a σ)
    ((cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen U)) (Rep.of ρ) 0).apply_symm_apply
      (coefficientSimplex ρ U f))

/-- An actual locally constant coefficient function is constant along every genuine singular simplex. -/
theorem coefficient_along_simplex (f : coefficientSections ρ U) (n : ℕ)
    (σ : SingularSimplex (TopCat.of (CoverOpen U)) n)
    (a b : Convexity.StdSimplex ℝ (Fin (n+1))) :
    f.val (TopCat.toSSetObjEquiv _ (.op ⦋n⦌) σ a) =
      f.val (TopCat.toSSetObjEquiv _ (.op ⦋n⦌) σ b) := by
  exact ((f.val.isLocallyConstant.comp_continuous
    (TopCat.toSSetObjEquiv _ (.op ⦋n⦌) σ).continuous).apply_eq_of_isPreconnected
      isPreconnected_univ (Set.mem_univ a) (Set.mem_univ b))

/-- The actual real singular differential kills the actual locally constant coefficient augmentation. -/
theorem coefficientSingularMap_closed (f : coefficientSections ρ U) :
    (coveringCochains ρ U).d 0 1 (coefficientSingularMap ρ U f) = 0 := by
  change equivariantD DeckGroup (TopCat.of (CoverOpen U)) 1 0 ≫ coefficientSingularMap ρ U f =
    (0 : chainRep DeckGroup (TopCat.of (CoverOpen U)) 1 ⟶ Rep.of ρ)
  apply (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen U)) (Rep.of ρ) 1).injective
  apply Subtype.ext
  funext σ
  erw [evaluate_d]
  change (∑ i : Fin 2, (-1 : ℤ)^i.val •
    cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen U)) (Rep.of ρ) 0
      (coefficientSingularMap ρ U f) ((TopCat.toSSet.obj (TopCat.of (CoverOpen U))).δ i σ)) = (0 : F)
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_smul]
  rw [coefficientSingularMap_eval, coefficientSingularMap_eval]
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
  exact add_neg_eq_zero.mpr (coefficient_along_simplex ρ U f 1 σ _ _)

/-- The actual real equivariant singular complex is augmented by its actual locally constant sections. -/
def coveringSingularAugmentation :
    (CochainComplex.single₀ (ModuleCat ℝ)).obj (ModuleCat.of ℝ (coefficientSections ρ U)) ⟶
      coveringCochains ρ U :=
  SmoothSingularComparison.augmentation (ModuleCat.ofHom (coefficientSingularMap ρ U)) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact coefficientSingularMap_closed ρ U f)

end TernaryPoly.SmoothSingularGlobal
