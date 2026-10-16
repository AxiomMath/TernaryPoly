module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.StabilizerDescent

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

section GroupPaths

variable {G C V : Type} [Group G] [AddCommGroup C] [Module ℂ C]
  [AddCommGroup V] [Module ℂ V]

def pathDifferenceCochain (Γ : Subgroup G) (ρ : Representation ℂ G V)
    (values : Γ → V) : cochains Γ ρ 1 :=
  ⟨fun vertices => ρ (ambientRetraction Γ (vertices 0)).val
      (values ((ambientRetraction Γ (vertices 0))⁻¹ *
        ambientRetraction Γ (vertices 1))), by
    intro γ vertices
    simp only [ambientRetraction_equivariant, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left, Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩

theorem pathDifferenceCochain_differential (Γ : Subgroup G)
    (ρ : Representation ℂ G V) (values : Γ → V) (first second third : Γ) :
    (differentialOne Γ ρ (pathDifferenceCochain Γ ρ values)).val
        ![first.val, second.val, third.val] =
      ρ first.val (values (first⁻¹ * second) +
        ρ (first⁻¹ * second).val (values (second⁻¹ * third)) -
          values (first⁻¹ * third)) := by
  change ρ (ambientRetraction Γ second.val).val
      (values ((ambientRetraction Γ second.val)⁻¹ * ambientRetraction Γ third.val)) -
    ρ (ambientRetraction Γ first.val).val
      (values ((ambientRetraction Γ first.val)⁻¹ * ambientRetraction Γ third.val)) +
    ρ (ambientRetraction Γ first.val).val
      (values ((ambientRetraction Γ first.val)⁻¹ * ambientRetraction Γ second.val)) = _
  simp only [ambientRetraction_subgroup, map_sub, map_add,
    ← Module.End.mul_apply, ← map_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    mul_inv_cancel_left]
  abel

theorem cocycle_coboundary_of_path_values (Γ : Subgroup G)
    (ρ : Representation ℂ G V) (c : cocycles Γ ρ) (values : Γ → V)
    (realization : ∀ first second third : Γ,
      c.val.val ![first.val, second.val, third.val] =
        ρ first.val (values (first⁻¹ * second) +
          ρ (first⁻¹ * second).val (values (second⁻¹ * third)) -
            values (first⁻¹ * third))) :
    ∃ primitive : cochains Γ ρ 1, differentialOne Γ ρ primitive = c.val := by
  let initial := pathDifferenceCochain Γ ρ values
  let defect := c - boundaryMap Γ ρ initial
  have vanishing : ∀ vertices : Fin 3 → Γ,
      defect.val.val (fun index => (vertices index).val) = 0 := by
    intro vertices
    have vertices_eq : (fun index => (vertices index).val) =
        ![(vertices 0).val, (vertices 1).val, (vertices 2).val] := by
      funext index
      fin_cases index <;> rfl
    change c.val.val (fun index => (vertices index).val) -
      (differentialOne Γ ρ initial).val (fun index => (vertices index).val) = 0
    rw [vertices_eq, realization, pathDifferenceCochain_differential]
    exact sub_self _
  obtain ⟨correction, correction_eq⟩ :=
    coboundary_of_zero_on_subgroup_vertices Γ ρ defect vanishing
  refine ⟨initial + correction, ?_⟩
  rw [map_add, correction_eq]
  change differentialOne Γ ρ initial + (c.val - differentialOne Γ ρ initial) = c.val
  abel

end GroupPaths

theorem goodChain_add {first second : EdgeChains}
    (first_good : GoodChain first) (second_good : GoodChain second) :
    GoodChain (first + second) := by
  classical
  intro edge supported
  rcases Finset.mem_union.mp (Finsupp.support_add supported) with in_first | in_second
  · exact first_good edge in_first
  · exact second_good edge in_second

theorem goodChain_sub {first second : EdgeChains}
    (first_good : GoodChain first) (second_good : GoodChain second) :
    GoodChain (first - second) := by
  classical
  intro edge supported
  rcases Finset.mem_union.mp (Finsupp.support_sub supported) with in_first | in_second
  · exact first_good edge in_first
  · exact second_good edge in_second

theorem translateChain_mul (first second : RationalGL3) (chain : EdgeChains) :
    translateChain (first * second) chain =
      translateChain first (translateChain second chain) := by
  change Finsupp.mapDomain (fun edge => (first * second) • edge) chain =
    Finsupp.mapDomain (fun edge => first • edge)
      (Finsupp.mapDomain (fun edge => second • edge) chain)
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext edge
  exact mul_smul first second edge

theorem translateChain_one (chain : EdgeChains) : translateChain 1 chain = chain := by
  change Finsupp.mapDomain (fun edge => (1 : RationalGL3) • edge) chain = chain
  simp only [one_smul]
  change Finsupp.mapDomain id chain = chain
  exact Finsupp.mapDomain_id

def translateVertexChains (element : RationalGL3) : VertexChains →ₗ[ℂ] VertexChains :=
  Finsupp.lmapDomain ℂ ℂ (translateVertex element)

theorem chainBoundary_translateChain (element : RationalGL3) (chain : EdgeChains) :
    chainBoundary (translateChain element chain) =
      translateVertexChains element (chainBoundary chain) := by
  have maps_eq : chainBoundary.comp (translateChain element) =
      (translateVertexChains element).comp chainBoundary := by
    apply Finsupp.lhom_ext
    intro edge scalar
    simp only [LinearMap.comp_apply, translateChain, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, chainBoundary, Finsupp.linearCombination_single,
      translateVertexChains, map_smul, map_sub]
    simp only [endpoint_smul, translateVertex]
  exact congrArg (fun linear_map => linear_map chain) maps_eq

theorem pathClass_coboundary_on_base_stabilizer {n : ℕ}
    (f : HomogeneousPoly n) (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly n)
    (functional_property : IsPolynomialFunctional f functional)
    (paths : rationalLevel → EdgeChains)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (path_property : IsPathFamily paths)
    (realization : RealizesPathClass functional paths c)
    (H : Subgroup RationalGL3) (inclusion : H ≤ rationalLevel)
    (fixes_base : ∀ element : H, translateVertex element.val pathBase = pathBase) :
    ∃ primitive : cochains H (rationalCoefficientComponent n trivialCharacter) 1,
      differentialOne H (rationalCoefficientComponent n trivialCharacter) primitive =
        (restrictCocycle rationalLevel H inclusion
          (rationalCoefficientComponent n trivialCharacter) c).val := by
  let embed : H →* rationalLevel :=
    { toFun := fun element => ⟨element.val, inclusion element.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have cycle_property : ∀ element : H, GoodCycle (paths (embed element)) := by
    intro element
    obtain ⟨good, boundary⟩ := path_property (embed element)
    refine ⟨?_, good⟩
    rw [boundary]
    change Finsupp.single (translateVertex element.val pathBase) 1 -
      Finsupp.single pathBase 1 = 0
    rw [fixes_base, sub_self]
  apply cocycle_coboundary_of_path_values H
    (rationalCoefficientComponent n trivialCharacter)
    (restrictCocycle rationalLevel H inclusion
      (rationalCoefficientComponent n trivialCharacter) c)
    (fun element => functional (paths (embed element)))
  intro first second third
  have path_value := realization (embed first) (embed second) (embed third)
  have equivariance := functional_property.1 (embed (first⁻¹ * second))
    (paths (embed (second⁻¹ * third))) (cycle_property (second⁻¹ * third))
  dsimp only [embed, MonoidHom.coe_mk, OneHom.coe_mk] at path_value equivariance
  change c.val.val ![first.val, second.val, third.val] = _
  rw [path_value]
  apply congrArg (rationalCoefficientComponent n trivialCharacter first.val)
  simp only [map_sub, map_add]
  dsimp only [embed, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← equivariance]
  rfl

theorem pathClass_coboundary_of_cycle_correction {n : ℕ}
    (f : HomogeneousPoly n) (functional : EdgeChains →ₗ[ℂ] HomogeneousPoly n)
    (functional_property : IsPolynomialFunctional f functional)
    (paths : rationalLevel → EdgeChains)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (realization : RealizesPathClass functional paths c)
    (H : Subgroup RationalGL3) (inclusion : H ≤ rationalLevel)
    (reference : EdgeChains)
    (cycle_correction : ∀ element : H,
      GoodCycle (paths ⟨element.val, inclusion element.property⟩ +
        translateChain element.val reference - reference)) :
    ∃ primitive : cochains H (rationalCoefficientComponent n trivialCharacter) 1,
      differentialOne H (rationalCoefficientComponent n trivialCharacter) primitive =
        (restrictCocycle rationalLevel H inclusion
          (rationalCoefficientComponent n trivialCharacter) c).val := by
  let embed : H →* rationalLevel :=
    { toFun := fun element => ⟨element.val, inclusion element.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let corrected := fun element : H =>
    paths (embed element) + translateChain element.val reference - reference
  let values := fun element : H => functional (corrected element)
  apply cocycle_coboundary_of_path_values H
    (rationalCoefficientComponent n trivialCharacter)
    (restrictCocycle rationalLevel H inclusion
      (rationalCoefficientComponent n trivialCharacter) c) values
  intro first second third
  have path_value := realization (embed first) (embed second) (embed third)
  have equivariance := functional_property.1 (embed (first⁻¹ * second))
    (corrected (second⁻¹ * third)) (cycle_correction (second⁻¹ * third))
  dsimp only [embed, MonoidHom.coe_mk, OneHom.coe_mk] at path_value equivariance
  change c.val.val ![first.val, second.val, third.val] = _
  rw [path_value]
  apply congrArg (rationalCoefficientComponent n trivialCharacter first.val)
  change functional (paths (embed first⁻¹ * embed second) +
    translateChain (first⁻¹ * second).val (paths (embed second⁻¹ * embed third)) -
      paths (embed first⁻¹ * embed third)) = _
  change _ = functional (corrected (first⁻¹ * second)) +
    rationalCoefficientComponent n trivialCharacter (first⁻¹ * second).val
      (functional (corrected (second⁻¹ * third))) -
        functional (corrected (first⁻¹ * third))
  rw [← equivariance, ← map_add, ← map_sub]
  apply congrArg functional
  dsimp only [corrected]
  rw [map_sub, map_add, ← translateChain_mul]
  have product_eq : (first⁻¹ * second).val * (second⁻¹ * third).val =
      (first⁻¹ * third).val := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left]
  rw [product_eq]
  simp only [map_mul, map_inv]
  abel

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
