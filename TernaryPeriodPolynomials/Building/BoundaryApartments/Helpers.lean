module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix Homogeneous

theorem endpoint_translate (side : Side) (matrix : RationalGL3) (edge : Edges) :
    endpoint side (matrix • edge) = matrix • endpoint side edge := by
  induction edge using Quotient.inductionOn with
  | _ representative => rfl

theorem translateChain_one (chain : EdgeChains) : translateChain 1 chain = chain := by
  have function_eq : (fun edge : Edges => (1 : RationalGL3) • edge) = id := by
    funext edge
    exact one_smul RationalGL3 edge
  rw [translateChain, function_eq, Finsupp.lmapDomain_id]
  rfl

theorem translateChain_mul (first second : RationalGL3) (chain : EdgeChains) :
    translateChain (first * second) chain =
      translateChain first (translateChain second chain) := by
  simp only [translateChain, Finsupp.lmapDomain_apply]
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext edge
  exact mul_smul first second edge

def translateVertexChain (matrix : RationalGL3) : VertexChains →ₗ[ℂ] VertexChains :=
  Finsupp.lmapDomain ℂ ℂ (translateVertex matrix)

theorem chainBoundary_translate (matrix : RationalGL3) (chain : EdgeChains) :
    chainBoundary (translateChain matrix chain) =
      translateVertexChain matrix (chainBoundary chain) := by
  have naturality : chainBoundary.comp (translateChain matrix) =
      (translateVertexChain matrix).comp chainBoundary := by
    apply Finsupp.lmapDomain_linearCombination ℂ
    intro edge
    simp only [translateVertexChain, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_sub, Finsupp.mapDomain_single, translateVertex,
      endpoint_translate]
  exact LinearMap.congr_fun naturality chain

theorem goodChain_zero : GoodChain 0 := by
  simp [GoodChain]

theorem goodChain_add {first second : EdgeChains}
    (first_good : GoodChain first) (second_good : GoodChain second) :
    GoodChain (first + second) := by
  classical
  intro edge edge_support
  rcases Finset.mem_union.mp (Finsupp.support_add edge_support) with first_mem | second_mem
  · exact first_good edge first_mem
  · exact second_good edge second_mem

theorem goodChain_sub {first second : EdgeChains}
    (first_good : GoodChain first) (second_good : GoodChain second) :
    GoodChain (first - second) := by
  classical
  intro edge edge_support
  rcases Finset.mem_union.mp (Finsupp.support_sub edge_support) with first_mem | second_mem
  · exact first_good edge first_mem
  · exact second_good edge second_mem

theorem goodCycle_zero : GoodCycle 0 := by
  exact ⟨map_zero _, goodChain_zero⟩

theorem path_difference_goodCycle {first second : rationalLevel → EdgeChains}
    (first_paths : IsPathFamily first) (second_paths : IsPathFamily second)
    (matrix : rationalLevel) : GoodCycle (first matrix - second matrix) := by
  constructor
  · rw [map_sub, (first_paths matrix).2, (second_paths matrix).2, sub_self]
  · exact goodChain_sub (first_paths matrix).1 (second_paths matrix).1

theorem arithmetic_lastRow (matrix : arithmeticLevel) (index : Fin 3) :
    (matrix.val.val 2 index : ZMod 3) = lastRow index := by
  have fixed : lastRow ᵥ* (reductionThree matrix.val).val = lastRow := matrix.property
  have coordinate := congrFun fixed index
  simp only [lastRow, Matrix.single_vecMul, one_smul] at coordinate
  exact coordinate

theorem arithmetic_mulVec_last (matrix : arithmeticLevel) (vector : Fin 3 → ℤ) :
    ((matrix.val.val *ᵥ vector) 2 : ZMod 3) = (vector 2 : ZMod 3) := by
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul,
    arithmetic_lastRow]
  simp [lastRow, Pi.single_apply]

theorem goodFlag_translate (side : Side) (matrix : rationalLevel) (flag : Flags side)
    (flag_good : GoodFlag side flag) : GoodFlag side (matrix.val • flag) := by
  rcases matrix.property with ⟨integral, integral_eq⟩
  rcases flag_good with ⟨vector, ⟨representative, representative_eq, weights,
    weights_condition, weights_eq⟩, vector_good⟩
  refine ⟨integral.val.val *ᵥ vector, ?_, ?_⟩
  · refine ⟨matrix.val * representative, ?_, weights, ?_, ?_⟩
    · change matrix.val • (QuotientGroup.mk representative : Flags side) = _
      rw [representative_eq]
    · cases side <;> exact weights_condition
    · rw [GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, weights_eq]
      rw [← integral_eq]
      change (integral.val.val.map (Int.castRingHom ℚ)) *ᵥ
        (fun index => (vector index : ℚ)) = _
      ext index
      simp [Matrix.mulVec, dotProduct]
  · rw [arithmetic_mulVec_last]
    exact vector_good

theorem goodChain_translate (matrix : rationalLevel) {chain : EdgeChains}
    (chain_good : GoodChain chain) : GoodChain (translateChain matrix.val chain) := by
  classical
  intro edge edge_support
  change edge ∈ (Finsupp.mapDomain (fun current : Edges => matrix.val • current) chain).support
    at edge_support
  rcases Finset.mem_image.mp (Finsupp.mapDomain_support edge_support) with
    ⟨original, original_support, original_eq⟩
  rw [← original_eq, endpoint_translate, endpoint_translate]
  exact ⟨goodFlag_translate .plane matrix _ (chain_good original original_support).1,
    goodFlag_translate .line matrix _ (chain_good original original_support).2⟩

theorem goodCycle_translate (matrix : rationalLevel) {chain : EdgeChains}
    (chain_good : GoodCycle chain) : GoodCycle (translateChain matrix.val chain) := by
  constructor
  · rw [chainBoundary_translate, chain_good.1, map_zero]
  · exact goodChain_translate matrix chain_good.2

def pathDefect (paths : rationalLevel → EdgeChains) (first second : rationalLevel) :
    EdgeChains := paths first + translateChain first.val (paths second) - paths (first * second)

theorem pathDefect_goodCycle {paths : rationalLevel → EdgeChains}
    (paths_good : IsPathFamily paths) (first second : rationalLevel) :
    GoodCycle (pathDefect paths first second) := by
  constructor
  · simp only [pathDefect, map_sub, map_add, chainBoundary_translate,
      (paths_good first).2, (paths_good second).2, (paths_good (first * second)).2,
      translateVertexChain, map_sub, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    have translate_comp : translateVertex first.val (translateVertex second.val pathBase) =
        translateVertex (first * second).val pathBase := by
      simp only [pathBase, translateVertex, mul_smul, Subgroup.coe_mul]
    rw [translate_comp]
    abel
  · exact goodChain_sub
      (goodChain_add (paths_good first).1 (goodChain_translate first (paths_good second).1))
      (paths_good (first * second)).1

theorem pathDefect_identity (paths : rationalLevel → EdgeChains)
    (first second third : rationalLevel) :
    translateChain first.val (pathDefect paths second third) -
      pathDefect paths (first * second) third + pathDefect paths first (second * third) -
        pathDefect paths first second = 0 := by
  simp only [pathDefect, map_sub, map_add, ← translateChain_mul,
    Subgroup.coe_mul, mul_assoc]
  abel

theorem pathDefect_cocycle {degree : ℕ}
    {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {paths : rationalLevel → EdgeChains} (paths_good : IsPathFamily paths)
    (first second third : rationalLevel) :
    rationalCoefficientComponent degree trivialCharacter first.val
        (functional (pathDefect paths second third)) -
      functional (pathDefect paths (first * second) third) +
      functional (pathDefect paths first (second * third)) -
      functional (pathDefect paths first second) = 0 := by
  rw [← functional_property.1 first _ (pathDefect_goodCycle paths_good second third)]
  rw [← map_sub, ← map_add, ← map_sub, pathDefect_identity, map_zero]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
