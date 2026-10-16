module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein
open Homogeneous Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialPathCocycle.Helpers

theorem integral_last_row (matrix : arithmeticLevel) (column : Fin 3) :
    (matrix.val.val 2 column : ZMod 3) = if column = 2 then 1 else 0 := by
  have stabilizes := matrix.property
  change lastRow ᵥ* (reductionThree matrix.val).val = lastRow at stabilizes
  have entry := congrFun stabilizes column
  simpa [lastRow, Matrix.vecMul, dotProduct, Pi.single_apply,
    reductionThree, GeneralLinearGroup.map] using entry

theorem goodFlag_translate (element : rationalLevel) (side : Side) (flag : Flags side)
    (good : GoodFlag side flag) : GoodFlag side (element.val • flag) := by
  rcases element.property with ⟨matrix, matrix_eq⟩
  rcases good with ⟨vector, ⟨representative, representative_eq, coordinates,
    coordinates_side, coordinates_eq⟩, vector_good⟩
  let image : Fin 3 → ℤ := matrix.val.val *ᵥ vector
  have image_good : (image 2 : ZMod 3) = (vector 2 : ZMod 3) := by
    simp only [image, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
    simp [integral_last_row]
  refine ⟨image, ⟨element.val * representative, ?_, coordinates, ?_, ?_⟩, ?_⟩
  · rw [← representative_eq]
    rfl
  · cases side <;> exact coordinates_side
  · rw [GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, coordinates_eq,
      ← matrix_eq]
    funext index
    simp [rationalInclusion, GeneralLinearGroup.map, image, Matrix.mulVec,
      dotProduct, Int.cast_sum, Int.cast_mul]
  · rw [image_good]
    exact vector_good

theorem goodChain_add {first second : EdgeChains}
    (first_good : GoodChain first) (second_good : GoodChain second) :
    GoodChain (first + second) := by
  classical
  intro edge edge_mem
  rcases Finset.mem_union.mp (Finsupp.support_add edge_mem) with first_mem | second_mem
  · exact first_good edge first_mem
  · exact second_good edge second_mem

theorem goodChain_sub {first second : EdgeChains}
    (first_good : GoodChain first) (second_good : GoodChain second) :
    GoodChain (first - second) := by
  classical
  intro edge edge_mem
  rcases Finset.mem_union.mp (Finsupp.support_sub edge_mem) with first_mem | second_mem
  · exact first_good edge first_mem
  · exact second_good edge second_mem

theorem goodChain_translate (element : rationalLevel) {chain : EdgeChains}
    (good : GoodChain chain) : GoodChain (translateChain element.val chain) := by
  classical
  intro edge edge_mem
  change edge ∈ (Finsupp.mapDomain (fun original : Edges => element.val • original) chain).support
    at edge_mem
  rcases Finset.mem_image.mp (Finsupp.mapDomain_support edge_mem) with
    ⟨original, original_mem, original_eq⟩
  rw [← original_eq, endpoint_smul, endpoint_smul]
  exact ⟨goodFlag_translate element .plane _ (good original original_mem).1,
    goodFlag_translate element .line _ (good original original_mem).2⟩

theorem translateChain_one (chain : EdgeChains) : translateChain 1 chain = chain := by
  simp only [translateChain, Finsupp.lmapDomain_apply, one_smul]
  exact Finsupp.mapDomain_id

theorem translateChain_mul (first second : RationalGL3) (chain : EdgeChains) :
    translateChain (first * second) chain =
      translateChain first (translateChain second chain) := by
  simp only [translateChain, Finsupp.lmapDomain_apply, mul_smul]
  exact Finsupp.mapDomain_comp

theorem translateVertex_mul (first second : RationalGL3) (vertex : BuildingVertices) :
    translateVertex (first * second) vertex =
      translateVertex first (translateVertex second vertex) := by
  cases vertex <;> simp [translateVertex, mul_smul]

theorem translateVertex_one (vertex : BuildingVertices) : translateVertex 1 vertex = vertex := by
  cases vertex <;> simp [translateVertex]

theorem chainBoundary_translate (element : RationalGL3) (chain : EdgeChains) :
    chainBoundary (translateChain element chain) =
      Finsupp.lmapDomain ℂ ℂ (translateVertex element) (chainBoundary chain) := by
  have maps : chainBoundary.comp (translateChain element) =
      (Finsupp.lmapDomain ℂ ℂ (translateVertex element)).comp chainBoundary := by
    apply Finsupp.lhom_ext
    intro edge coefficient
    simp [LinearMap.comp_apply, translateChain, chainBoundary, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, Finsupp.linearCombination_single, endpoint_smul,
      translateVertex, map_smul, map_sub]
  exact LinearMap.congr_fun maps chain

def pathDefect (paths : rationalLevel → EdgeChains) (first second : rationalLevel) : EdgeChains :=
  paths first + translateChain first.val (paths second) - paths (first * second)

theorem pathDefect_good (paths : rationalLevel → EdgeChains) (paths_good : IsPathFamily paths)
    (first second : rationalLevel) : GoodCycle (pathDefect paths first second) := by
  refine ⟨?_, goodChain_sub
    (goodChain_add (paths_good first).1 (goodChain_translate first (paths_good second).1))
    (paths_good (first * second)).1⟩
  simp only [pathDefect, map_sub, map_add, chainBoundary_translate, (paths_good first).2,
    (paths_good second).2, (paths_good (first * second)).2, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Subgroup.coe_mul,
    translateVertex_mul]
  abel

theorem pathDefect_identity (paths : rationalLevel → EdgeChains)
    (first second third : rationalLevel) :
    translateChain first.val (pathDefect paths second third) -
      pathDefect paths (first * second) third + pathDefect paths first (second * third) -
      pathDefect paths first second = 0 := by
  simp only [pathDefect, map_sub, map_add, Subgroup.coe_mul, translateChain_mul, mul_assoc]
  abel

def normalizedRepresentative {group : Type} [Group group] (subgroup : Subgroup group)
    (coset : group ⧸ subgroup) : group := by
  classical
  exact if coset = QuotientGroup.mk (1 : group) then 1 else coset.out

theorem normalizedRepresentative_mk {group : Type} [Group group] (subgroup : Subgroup group)
    (coset : group ⧸ subgroup) :
    QuotientGroup.mk (normalizedRepresentative subgroup coset) = coset := by
  classical
  unfold normalizedRepresentative
  split_ifs with identity
  · exact identity.symm
  · exact Quotient.out_eq coset

def subgroupRetraction {group : Type} [Group group] (subgroup : Subgroup group)
    (element : group) : subgroup :=
  ⟨element * normalizedRepresentative subgroup (QuotientGroup.mk element⁻¹), by
    have same := (normalizedRepresentative_mk subgroup (QuotientGroup.mk element⁻¹)).symm
    simpa only [inv_inv] using QuotientGroup.eq.mp same⟩

theorem subgroupRetraction_equivariant {group : Type} [Group group]
    (subgroup : Subgroup group) (translate : subgroup) (element : group) :
    subgroupRetraction subgroup (translate.val * element) =
      translate * subgroupRetraction subgroup element := by
  apply Subtype.ext
  change translate.val * element * normalizedRepresentative subgroup
    (QuotientGroup.mk (translate.val * element)⁻¹) =
    translate.val * (element * normalizedRepresentative subgroup (QuotientGroup.mk element⁻¹))
  rw [_root_.mul_inv_rev,
    QuotientGroup.mk_mul_of_mem _ (subgroup.inv_mem translate.property), mul_assoc]

theorem subgroupRetraction_subgroup {group : Type} [Group group]
    (subgroup : Subgroup group) (element : subgroup) :
    subgroupRetraction subgroup element.val = element := by
  classical
  have identity : (QuotientGroup.mk element.val⁻¹ : group ⧸ subgroup) =
      QuotientGroup.mk (1 : group) := by
    apply QuotientGroup.eq.mpr
    simp only [inv_inv, mul_one]
    exact element.property
  apply Subtype.ext
  simp [subgroupRetraction, normalizedRepresentative, identity]

def arithmeticPathValue {degree : ℕ} (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (paths : rationalLevel → EdgeChains) (first second third : rationalLevel) :
    HomogeneousPoly degree :=
  rationalCoefficientComponent degree trivialCharacter first.val
    (functional (pathDefect paths (first⁻¹ * second) (second⁻¹ * third)))

theorem arithmeticPathValue_equivariant {degree : ℕ}
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree) (paths : rationalLevel → EdgeChains)
    (translate first second third : rationalLevel) :
    arithmeticPathValue functional paths (translate * first) (translate * second)
      (translate * third) = rationalCoefficientComponent degree trivialCharacter translate.val
        (arithmeticPathValue functional paths first second third) := by
  simp [arithmeticPathValue, _root_.mul_inv_rev, mul_assoc, map_mul, Module.End.mul_apply]

theorem arithmeticPathValue_cocycle {degree : ℕ}
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree) (paths : rationalLevel → EdgeChains)
    (paths_good : IsPathFamily paths)
    (equivariant : ∀ element : rationalLevel, ∀ chain, GoodCycle chain →
      functional (translateChain element.val chain) =
        rationalCoefficientComponent degree trivialCharacter element.val (functional chain))
    (first second third fourth : rationalLevel) :
    arithmeticPathValue functional paths second third fourth -
      arithmeticPathValue functional paths first third fourth +
      arithmeticPathValue functional paths first second fourth -
      arithmeticPathValue functional paths first second third = 0 := by
  have identity := congrArg functional (pathDefect_identity paths (first⁻¹ * second)
    (second⁻¹ * third) (third⁻¹ * fourth))
  rw [map_sub, map_add, map_sub, map_zero,
    equivariant _ _ (pathDefect_good paths paths_good _ _)] at identity
  have acted := congrArg (rationalCoefficientComponent degree trivialCharacter first.val) identity
  simp only [map_sub, map_add, map_zero] at acted
  have product_action (left right : RationalGL3) (value : HomogeneousPoly degree) :
      rationalCoefficientComponent degree trivialCharacter left
        (rationalCoefficientComponent degree trivialCharacter right value) =
          rationalCoefficientComponent degree trivialCharacter (left * right) value := by
    rw [map_mul, Module.End.mul_apply]
  rw [product_action] at acted
  simpa [arithmeticPathValue, mul_assoc] using acted

def ambientPathCochain {degree : ℕ}
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (paths : rationalLevel → EdgeChains) :
    cochains rationalLevel (rationalCoefficientComponent degree trivialCharacter) 2 :=
  ⟨fun vertices => arithmeticPathValue functional paths
    (subgroupRetraction rationalLevel (vertices 0))
    (subgroupRetraction rationalLevel (vertices 1))
    (subgroupRetraction rationalLevel (vertices 2)), by
    intro translate vertices
    simp only [subgroupRetraction_equivariant]
    exact arithmeticPathValue_equivariant functional paths translate _ _ _⟩

theorem ambientPathCochain_cocycle {degree : ℕ}
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree) (paths : rationalLevel → EdgeChains)
    (paths_good : IsPathFamily paths)
    (equivariant : ∀ element : rationalLevel, ∀ chain, GoodCycle chain →
      functional (translateChain element.val chain) =
        rationalCoefficientComponent degree trivialCharacter element.val (functional chain)) :
    differentialTwo rationalLevel (rationalCoefficientComponent degree trivialCharacter)
      (ambientPathCochain functional paths) = 0 := by
  funext vertices
  exact arithmeticPathValue_cocycle functional paths paths_good equivariant _ _ _ _

def ambientPathCocycle {degree : ℕ}
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree) (paths : rationalLevel → EdgeChains)
    (paths_good : IsPathFamily paths)
    (equivariant : ∀ element : rationalLevel, ∀ chain, GoodCycle chain →
      functional (translateChain element.val chain) =
        rationalCoefficientComponent degree trivialCharacter element.val (functional chain)) :
    cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter) :=
  ⟨ambientPathCochain functional paths,
    ambientPathCochain_cocycle functional paths paths_good equivariant⟩

theorem ambientPathCocycle_realizes {degree : ℕ}
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree) (paths : rationalLevel → EdgeChains)
    (paths_good : IsPathFamily paths)
    (equivariant : ∀ element : rationalLevel, ∀ chain, GoodCycle chain →
      functional (translateChain element.val chain) =
        rationalCoefficientComponent degree trivialCharacter element.val (functional chain)) :
    RealizesPathClass functional paths
      (ambientPathCocycle functional paths paths_good equivariant) := by
  intro first second third
  simp [ambientPathCocycle, ambientPathCochain, subgroupRetraction_subgroup,
    arithmeticPathValue, pathDefect, mul_assoc]

end TernaryPeriodPolynomials.PolynomialPathCocycle.Helpers
