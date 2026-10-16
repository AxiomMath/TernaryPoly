module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.Apartments
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix

theorem goodCycle_smul (scalar : ℂ) {chain : EdgeChains} (cycle : GoodCycle chain) :
    GoodCycle (scalar • chain) := by
  constructor
  · rw [map_smul, cycle.1, smul_zero]
  · intro edge edge_mem
    have edge_nonzero : (scalar • chain) edge ≠ 0 := Finsupp.mem_support_iff.mp edge_mem
    have original_nonzero : chain edge ≠ 0 := by
      intro original_zero
      exact edge_nonzero (by simp [original_zero])
    exact cycle.2 edge (Finsupp.mem_support_iff.mpr original_nonzero)

def goodCycleModule : Submodule ℂ EdgeChains where
  carrier := {chain | GoodCycle chain}
  zero_mem' := ⟨map_zero _, goodChain_zero⟩
  add_mem' first second :=
    ⟨by rw [map_add, first.1, second.1, add_zero], goodChain_add first.2 second.2⟩
  smul_mem' := fun scalar _ cycle => goodCycle_smul scalar cycle

def translateGoodCycle (matrix : rationalLevel) : goodCycleModule →ₗ[ℂ] goodCycleModule where
  toFun chain := ⟨translateChain matrix.val chain.val, goodCycle_translate matrix chain.property⟩
  map_add' first second := by apply Subtype.ext; exact map_add (translateChain matrix.val) _ _
  map_smul' scalar chain := by apply Subtype.ext; exact map_smul (translateChain matrix.val) scalar _

def normalizedApartmentCycle (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) : goodCycleModule :=
  ⟨apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frame),
    normalizedApartment_goodCycle frame normalized⟩

theorem polynomialFunctional_exists_of_goodCycleMap {degree : ℕ}
    (polynomial : HomogeneousPoly degree)
    (cycle_map : goodCycleModule →ₗ[ℂ] HomogeneousPoly degree)
    (equivariant : ∀ matrix : rationalLevel, ∀ chain : goodCycleModule,
      cycle_map (translateGoodCycle matrix chain) =
        rationalCoefficientComponent degree trivialCharacter matrix.val (cycle_map chain))
    (normalization : ∀ frame : IntegralGL3,
      ∀ normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1,
      (cycle_map (normalizedApartmentCycle frame normalized)).val =
        MvPolynomial.C ((GeneralLinearGroup.det frame : ℤ) : ℂ) *
          substitute ((GeneralLinearGroup.map (Int.castRingHom ℂ) frame)⁻¹).val polynomial.val) :
    ∃ functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree,
      IsPolynomialFunctional polynomial functional := by
  obtain ⟨functional, extension⟩ := LinearMap.exists_extend cycle_map
  have restriction (chain : goodCycleModule) : functional chain.val = cycle_map chain :=
    LinearMap.congr_fun extension chain
  refine ⟨functional, ?_, ?_⟩
  · intro matrix chain cycle
    let good_chain : goodCycleModule := ⟨chain, cycle⟩
    have translated := restriction (translateGoodCycle matrix good_chain)
    change functional (translateChain matrix.val chain) =
      cycle_map (translateGoodCycle matrix good_chain) at translated
    rw [translated, equivariant, ← restriction good_chain]
  · intro frame normalized
    have apartment_value := restriction (normalizedApartmentCycle frame normalized)
    change functional (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frame)) =
      cycle_map (normalizedApartmentCycle frame normalized) at apartment_value
    rw [apartment_value]
    exact normalization frame normalized

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
