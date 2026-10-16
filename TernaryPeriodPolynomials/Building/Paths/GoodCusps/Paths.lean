module

public import TernaryPeriodPolynomials.Building.Paths.GoodCusps.Cochains

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialPathGoodCusps.Helpers

def localLoop (paths : rationalLevel → EdgeChains)
    (first second : rationalLevel) (vertex : BuildingVertices) : EdgeChains :=
  paths (first⁻¹ * second) + translateChain (first⁻¹ * second).val
    (chosenPath (translateVertex second⁻¹.val vertex)) -
    chosenPath (translateVertex first⁻¹.val vertex)

theorem vertexTranslation_single (matrix : RationalGL3) (vertex : BuildingVertices) :
    vertexTranslation matrix (Finsupp.single vertex 1) =
      Finsupp.single (translateVertex matrix vertex) 1 := by
  simp [vertexTranslation, Finsupp.lmapDomain]

theorem localLoop_cycle {paths : rationalLevel → EdgeChains}
    (paths_valid : IsPathFamily paths) (first second : rationalLevel)
    (vertex : BuildingVertices) (vertex_good : GoodVertex vertex) :
    GoodCycle (localLoop paths first second vertex) := by
  have first_good := goodVertex_translate first⁻¹ vertex vertex_good
  have second_good := goodVertex_translate second⁻¹ vertex vertex_good
  refine ⟨?_, goodChain_sub
    (goodChain_add (paths_valid (first⁻¹ * second)).1
      (goodChain_translate (first⁻¹ * second) (chosenPath_good _)))
    (chosenPath_good _)⟩
  rw [localLoop, map_sub, map_add, (paths_valid (first⁻¹ * second)).2,
    chainBoundary_translate, chosenPath_boundary _ second_good,
    chosenPath_boundary _ first_good, map_sub, vertexTranslation_single,
    vertexTranslation_single, ← translateVertex_mul]
  have product_eq : (first⁻¹ * second).val * second⁻¹.val = first⁻¹.val := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_right]
  rw [product_eq]
  abel

theorem localLoop_transport (paths : rationalLevel → EdgeChains)
    (group_element first second : rationalLevel) (vertex : BuildingVertices) :
    localLoop paths (group_element * first) (group_element * second) vertex =
      localLoop paths first second (translateVertex group_element⁻¹.val vertex) := by
  simp only [localLoop, mul_inv_rev, inv_mul_cancel_left, Subgroup.coe_mul,
    translateVertex_mul, mul_assoc]

theorem localLoop_defect (paths : rationalLevel → EdgeChains)
    (first second third : rationalLevel) (vertex : BuildingVertices) :
    localLoop paths first second vertex +
      translateChain (first⁻¹ * second).val (localLoop paths second third vertex) -
      localLoop paths first third vertex =
    paths (first⁻¹ * second) +
      translateChain (first⁻¹ * second).val (paths (second⁻¹ * third)) -
      paths (first⁻¹ * third) := by
  have product_eq : (first⁻¹ * second).val * (second⁻¹ * third).val =
      (first⁻¹ * third).val := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left]
  simp only [localLoop, map_sub, map_add, ← translateChain_mul, product_eq]
  abel

def flagVertex (side : Side) (flag : Flags side) : BuildingVertices :=
  match side with | .plane => .inl flag | .line => .inr flag

def localPrimitive {n : ℕ} (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly n)
    (paths : rationalLevel → EdgeChains) (side : Side) :
    MaximalCochains n trivialCharacter side 1 :=
  ⟨fun tuple flag =>
    rationalCoefficientComponent n trivialCharacter (arithmeticProjection (tuple 0)).val
      (functional (localLoop paths (arithmeticProjection (tuple 0))
        (arithmeticProjection (tuple 1))
        (flagVertex side flag))), by
    intro group_element tuple
    funext flag
    simp only [arithmeticProjection_mul, Subgroup.coe_mul, localLoop_transport,
      map_mul, Module.End.mul_apply]
    cases side <;> rfl⟩

theorem localPrimitive_apply {n : ℕ}
    (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly n)
    (paths : rationalLevel → EdgeChains) (side : Side)
    (first second : RationalGL3) (flag : Flags side) :
    (localPrimitive functional paths side).val ![first, second] flag =
      rationalCoefficientComponent n trivialCharacter (arithmeticProjection first).val
        (functional (localLoop paths (arithmeticProjection first)
          (arithmeticProjection second) (flagVertex side flag))) := by rfl

theorem coefficient_transport {n : ℕ} (first second : rationalLevel)
    (value : HomogeneousPoly n) :
    rationalCoefficientComponent n trivialCharacter first.val
      (rationalCoefficientComponent n trivialCharacter (first⁻¹ * second).val value) =
    rationalCoefficientComponent n trivialCharacter second.val value := by
  rw [← Module.End.mul_apply, ← map_mul]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]

theorem localPrimitive_boundary {n : ℕ} {polynomial : HomogeneousPoly n}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly n}
    (functional_valid : IsPolynomialFunctional polynomial functional)
    {paths : rationalLevel → EdgeChains} (paths_valid : IsPathFamily paths)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (realizes : RealizesPathClass functional paths cocycle)
    (side : Side) (tuple : Fin 3 → RationalGL3) (flag : Flags side)
    (flag_good : GoodFlag side flag) :
    (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
      (localPrimitive functional paths side)).val tuple flag =
    (projectedCocycle cocycle).val.val tuple := by
  let first := arithmeticProjection (tuple 0)
  let second := arithmeticProjection (tuple 1)
  let third := arithmeticProjection (tuple 2)
  let vertex := flagVertex side flag
  have vertex_good : GoodVertex vertex := by cases side <;> exact flag_good
  have translated := functional_valid.1 (first⁻¹ * second)
    (localLoop paths second third vertex)
    (localLoop_cycle paths_valid second third vertex vertex_good)
  have transported :
      rationalCoefficientComponent n trivialCharacter first.val
        (functional (translateChain (first⁻¹ * second).val
          (localLoop paths second third vertex))) =
      rationalCoefficientComponent n trivialCharacter second.val
        (functional (localLoop paths second third vertex)) := by
    rw [translated, coefficient_transport]
  have realization := realizes first second third
  rw [← localLoop_defect paths first second third vertex] at realization
  simp only [map_sub, map_add] at realization
  rw [transported] at realization
  change
    (localPrimitive functional paths side).val ![tuple 1, tuple 2] flag -
      (localPrimitive functional paths side).val ![tuple 0, tuple 2] flag +
      (localPrimitive functional paths side).val ![tuple 0, tuple 1] flag =
    cocycle.val.val (fun index => (arithmeticProjection (tuple index)).val)
  rw [localPrimitive_apply, localPrimitive_apply, localPrimitive_apply]
  rw [← tuple_three_eta (fun index => (arithmeticProjection (tuple index)).val)]
  rw [realization]
  abel

def constantFlagCochain {n : ℕ} (side : Side)
    (cochain : cochains rationalLevel (rationalCoefficientComponent n trivialCharacter) 1) :
    MaximalCochains n trivialCharacter side 1 :=
  ⟨fun tuple _ => cochain.val tuple, by
    intro group_element tuple
    funext flag
    exact cochain.property group_element tuple⟩

theorem constantFlagCochain_boundary {n : ℕ} (side : Side)
    (cochain : cochains rationalLevel (rationalCoefficientComponent n trivialCharacter) 1)
    (tuple : Fin 3 → RationalGL3) (flag : Flags side) :
    (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
      (constantFlagCochain side cochain)).val tuple flag =
      (boundaryMap rationalLevel (rationalCoefficientComponent n trivialCharacter)
        cochain).val.val tuple := by rfl

theorem differentialOne_sub_apply {n : ℕ} (side : Side)
    (first second : MaximalCochains n trivialCharacter side 1)
    (tuple : Fin 3 → RationalGL3) (flag : Flags side) :
    (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
      (first - second)).val tuple flag =
    (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
      first).val tuple flag -
    (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
      second).val tuple flag := by
  change (first.val ![tuple 1, tuple 2] flag - second.val ![tuple 1, tuple 2] flag) -
      (first.val ![tuple 0, tuple 2] flag - second.val ![tuple 0, tuple 2] flag) +
      (first.val ![tuple 0, tuple 1] flag - second.val ![tuple 0, tuple 1] flag) = _
  change _ = (first.val ![tuple 1, tuple 2] flag - first.val ![tuple 0, tuple 2] flag +
    first.val ![tuple 0, tuple 1] flag) -
    (second.val ![tuple 1, tuple 2] flag - second.val ![tuple 0, tuple 2] flag +
      second.val ![tuple 0, tuple 1] flag)
  abel

theorem vanishesOnGood_path {n : ℕ} {polynomial : HomogeneousPoly n}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly n}
    (functional_valid : IsPolynomialFunctional polynomial functional)
    {paths : rationalLevel → EdgeChains} (paths_valid : IsPathFamily paths)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (realizes : RealizesPathClass functional paths cocycle) (side : Side) :
    VanishesOnGood n trivialCharacter side
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
        (restrictionCocycle n trivialCharacter side cocycle)) := by
  refine ⟨restrictionCocycle n trivialCharacter side cocycle, rfl,
    localPrimitive functional paths side -
      constantFlagCochain side (projectionHomotopy cocycle), ?_⟩
  intro tuple flag flag_good
  rw [differentialOne_sub_apply]
  change cocycle.val.val tuple =
    (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
      (localPrimitive functional paths side)).val tuple flag -
    (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
      (constantFlagCochain side (projectionHomotopy cocycle))).val tuple flag
  rw [localPrimitive_boundary functional_valid paths_valid realizes side tuple flag flag_good,
    constantFlagCochain_boundary, projectionHomotopy_boundary]
  change cocycle.val.val tuple = (projectedCocycle cocycle).val.val tuple -
    ((projectedCocycle cocycle).val.val tuple - cocycle.val.val tuple)
  abel

end TernaryPeriodPolynomials.PolynomialPathGoodCusps.Helpers
