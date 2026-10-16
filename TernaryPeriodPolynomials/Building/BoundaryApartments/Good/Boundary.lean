module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.Paths
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Cochains

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous

def flagVertex (side : Side) (flag : Flags side) : BuildingVertices :=
  match side with
  | .plane => Sum.inl flag
  | .line => Sum.inr flag

theorem flagVertex_translate (side : Side) (matrix : RationalGL3) (flag : Flags side) :
    flagVertex side (matrix • flag) = translateVertex matrix (flagVertex side flag) := by
  cases side <;> rfl

theorem good_flag_path_exists (side : Side) (flag : Flags side)
    (flag_good : GoodFlag side flag) :
    ∃ chain : EdgeChains, GoodChain chain ∧ chainBoundary chain =
      Finsupp.single (flagVertex side flag) 1 - Finsupp.single pathBase 1 := by
  cases side
  · exact good_plane_path_exists flag flag_good
  · exact good_line_path_exists flag flag_good

def flagPaths (side : Side) (flag : Flags side) : EdgeChains := by
  classical
  exact if flag_good : GoodFlag side flag then
    Classical.choose (good_flag_path_exists side flag flag_good)
  else 0

theorem flagPaths_property (side : Side) (flag : Flags side)
    (flag_good : GoodFlag side flag) :
    GoodChain (flagPaths side flag) ∧ chainBoundary (flagPaths side flag) =
      Finsupp.single (flagVertex side flag) 1 - Finsupp.single pathBase 1 := by
  classical
  rw [flagPaths, dite_eq_left flag_good]
  exact Classical.choose_spec (good_flag_path_exists side flag flag_good)

def flagPathDifference (paths : rationalLevel → EdgeChains) (side : Side)
    (matrix : rationalLevel) (flag : Flags side) : EdgeChains :=
  paths matrix + translateChain matrix.val (flagPaths side (matrix.val⁻¹ • flag)) -
    flagPaths side flag

theorem flagPathDifference_goodCycle {paths : rationalLevel → EdgeChains}
    (paths_good : IsPathFamily paths) (side : Side) (matrix : rationalLevel)
    (flag : Flags side) (flag_good : GoodFlag side flag) :
    GoodCycle (flagPathDifference paths side matrix flag) := by
  have inverse_good : GoodFlag side (matrix.val⁻¹ • flag) :=
    goodFlag_translate side matrix⁻¹ flag flag_good
  constructor
  · simp only [flagPathDifference, map_sub, map_add, chainBoundary_translate,
      (paths_good matrix).2, (flagPaths_property side flag flag_good).2,
      (flagPaths_property side (matrix.val⁻¹ • flag) inverse_good).2,
      translateVertexChain, map_sub, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      ← flagVertex_translate, smul_inv_smul]
    abel
  · exact goodChain_sub
      (goodChain_add (paths_good matrix).1
        (goodChain_translate matrix (flagPaths_property side _ inverse_good).1))
      (flagPaths_property side flag flag_good).1

theorem flagPathDifference_identity (paths : rationalLevel → EdgeChains) (side : Side)
    (first second : rationalLevel) (flag : Flags side) :
    translateChain first.val (flagPathDifference paths side second (first.val⁻¹ • flag)) -
      flagPathDifference paths side (first * second) flag +
        flagPathDifference paths side first flag = pathDefect paths first second := by
  simp only [flagPathDifference, pathDefect, map_sub, map_add, Subgroup.coe_mul,
    _root_.mul_inv_rev, mul_smul, ← translateChain_mul]
  abel

def goodFlagCochain {degree : ℕ} (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree)
    (paths : rationalLevel → EdgeChains) (side : Side) :
    MaximalCochains degree trivialCharacter side 1 :=
  ⟨fun vertices flag =>
    let first := groupRetraction rationalLevel (vertices 0)
    let second := groupRetraction rationalLevel (vertices 1)
    rationalCoefficientComponent degree trivialCharacter first.val
      (functional (flagPathDifference paths side (first⁻¹ * second) (first.val⁻¹ • flag))), by
    intro acting vertices
    funext flag
    change _ = rationalCoefficientComponent degree trivialCharacter acting.val
      (rationalCoefficientComponent degree trivialCharacter
        (groupRetraction rationalLevel (vertices 0)).val
        (functional (flagPathDifference paths side
          ((groupRetraction rationalLevel (vertices 0))⁻¹ *
            groupRetraction rationalLevel (vertices 1))
          ((groupRetraction rationalLevel (vertices 0)).val⁻¹ • (acting.val⁻¹ • flag)))))
    simp only [groupRetraction_equivariant, Subgroup.coe_mul,
      _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul,
      Module.End.mul_apply, mul_smul]⟩

theorem goodFlagCochain_differential {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {paths : rationalLevel → EdgeChains} (paths_good : IsPathFamily paths)
    (side : Side) (vertices : Fin 3 → RationalGL3) (flag : Flags side)
    (flag_good : GoodFlag side flag) :
    (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree trivialCharacter) side)
      (goodFlagCochain functional paths side)).val vertices flag =
      (restrictionCocycle degree trivialCharacter side
        (pathCocycle functional_property paths_good)).val.val vertices flag := by
  let first := groupRetraction rationalLevel (vertices 0)
  let second := groupRetraction rationalLevel (vertices 1)
  let third := groupRetraction rationalLevel (vertices 2)
  have second_flag_good : GoodFlag side (second.val⁻¹ • flag) :=
    goodFlag_translate side second⁻¹ flag flag_good
  have equivariance := functional_property.1 (first⁻¹ * second)
    (flagPathDifference paths side (second⁻¹ * third) (second.val⁻¹ • flag))
    (flagPathDifference_goodCycle paths_good side (second⁻¹ * third) _ second_flag_good)
  have translated := congrArg
    (rationalCoefficientComponent degree trivialCharacter first.val) equivariance
  simp only [← Module.End.mul_apply, ← map_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    mul_inv_cancel_left] at translated
  change rationalCoefficientComponent degree trivialCharacter second.val
      (functional (flagPathDifference paths side (second⁻¹ * third) (second.val⁻¹ • flag))) -
    rationalCoefficientComponent degree trivialCharacter first.val
      (functional (flagPathDifference paths side (first⁻¹ * third) (first.val⁻¹ • flag))) +
    rationalCoefficientComponent degree trivialCharacter first.val
      (functional (flagPathDifference paths side (first⁻¹ * second) (first.val⁻¹ • flag))) =
    rationalCoefficientComponent degree trivialCharacter first.val
      (functional (pathDefect paths (first⁻¹ * second) (second⁻¹ * third)))
  rw [← translated, ← map_sub, ← map_add, ← map_sub, ← map_add]
  have flag_eq : second.val⁻¹ • flag =
      (first⁻¹ * second).val⁻¹ • (first.val⁻¹ • flag) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, mul_smul,
      inv_inv, smul_inv_smul]
  rw [flag_eq, ← flagPathDifference_identity paths side (first⁻¹ * second)
    (second⁻¹ * third) (first.val⁻¹ • flag)]
  simp only [mul_assoc, mul_inv_cancel_left, Subgroup.coe_mul, Subgroup.coe_inv]

theorem pathCocycle_vanishesOnGood {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {paths : rationalLevel → EdgeChains} (paths_good : IsPathFamily paths) (side : Side) :
    VanishesOnGood degree trivialCharacter side
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree trivialCharacter) side)
        (restrictionCocycle degree trivialCharacter side
          (pathCocycle functional_property paths_good))) := by
  refine ⟨restrictionCocycle degree trivialCharacter side
    (pathCocycle functional_property paths_good), rfl,
      goodFlagCochain functional paths side, ?_⟩
  intro vertices flag flag_good
  exact (goodFlagCochain_differential functional_property paths_good side vertices flag flag_good).symm

theorem pathCocycle_goodBoundaryVanishing {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {paths : rationalLevel → EdgeChains} (paths_good : IsPathFamily paths) :
    GoodBoundaryVanishing degree trivialCharacter
      (globalCoordinates degree trivialCharacter (pathCocycle functional_property paths_good)) := by
  exact ⟨pathCocycle_vanishesOnGood functional_property paths_good .plane,
    pathCocycle_vanishesOnGood functional_property paths_good .line⟩

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
