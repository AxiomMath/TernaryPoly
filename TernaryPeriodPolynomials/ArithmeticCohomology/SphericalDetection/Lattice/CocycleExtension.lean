module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.Lattice
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def latticeHomOfCommute {H : Type*} [Group H] (first second : H) (commute : Commute first second) :
    RadicalLattice →* H where
  toFun element := first ^ element.toAdd.1 * second ^ element.toAdd.2
  map_one' := by simp
  map_mul' left right := by
    change first ^ (left.toAdd.1 + right.toAdd.1) * second ^ (left.toAdd.2 + right.toAdd.2) = _
    rw [zpow_add, zpow_add]
    calc
      _ = first ^ left.toAdd.1 * (first ^ right.toAdd.1 * second ^ left.toAdd.2) * second ^ right.toAdd.2 := by
        simp only [mul_assoc]
      _ = first ^ left.toAdd.1 * (second ^ left.toAdd.2 * first ^ right.toAdd.1) * second ^ right.toAdd.2 := by
        rw [(commute.zpow_zpow right.toAdd.1 left.toAdd.2).eq]
      _ = _ := by simp only [mul_assoc]

theorem latticeHomOfCommute_first {H : Type*} [Group H] (first second : H) (commute : Commute first second) :
    latticeHomOfCommute first second commute radicalLatticeFirst = first := by
  simp [latticeHomOfCommute, radicalLatticeFirst]

theorem latticeHomOfCommute_second {H : Type*} [Group H] (first second : H) (commute : Commute first second) :
    latticeHomOfCommute first second commute radicalLatticeSecond = second := by
  simp [latticeHomOfCommute, radicalLatticeSecond]

theorem latticeHom_ext {H : Type*} [Group H] (first second : RadicalLattice →* H)
    (first_eq : first radicalLatticeFirst = second radicalLatticeFirst)
    (second_eq : first radicalLatticeSecond = second radicalLatticeSecond) : first = second := by
  apply MonoidHom.ext
  intro element
  obtain ⟨first_power, second_power, rfl⟩ := radicalLattice_generated element
  simp only [map_mul, map_zpow, first_eq, second_eq]

def representationLinearEquiv {G : Type} [Group G] (representation : Rep ℂ G) (element : G) :
    representation ≃ₗ[ℂ] representation where
  toLinearMap := representation.ρ element
  invFun := representation.ρ element⁻¹
  left_inv vector := by
    change representation.ρ element⁻¹ (representation.ρ element vector) = vector
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv vector := by
    change representation.ρ element (representation.ρ element⁻¹ vector) = vector
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem representationLinearEquiv_apply {G : Type} [Group G] (representation : Rep ℂ G)
    (element : G) (vector : representation) :
    representationLinearEquiv representation element vector = representation.ρ element vector := rfl

def representationLinearEquivHom {G : Type} [Group G] (representation : Rep ℂ G) :
    G →* (representation ≃ₗ[ℂ] representation) where
  toFun := representationLinearEquiv representation
  map_one' := by
    apply LinearEquiv.ext
    intro vector
    exact congrArg (fun operator : Module.End ℂ representation => operator vector) representation.ρ.map_one
  map_mul' first second := by
    apply LinearEquiv.ext
    intro vector
    exact congrArg (fun operator : Module.End ℂ representation => operator vector) (representation.ρ.map_mul first second)

def affineCocycleGenerator {G : Type} [Group G] (representation : Rep ℂ G) (element : G)
    (value : representation) : representation ≃ᵃ[ℂ] representation :=
  (representationLinearEquiv representation element).toAffineEquiv.trans
    (AffineEquiv.constVAdd ℂ representation value)

theorem affineCocycleGenerator_apply {G : Type} [Group G] (representation : Rep ℂ G) (element : G)
    (value vector : representation) :
    affineCocycleGenerator representation element value vector = value + representation.ρ element vector := rfl

theorem affineCocycleGenerator_linear {G : Type} [Group G] (representation : Rep ℂ G) (element : G)
    (value : representation) :
    (affineCocycleGenerator representation element value).linear = representationLinearEquiv representation element := by
  apply LinearEquiv.ext
  intro vector
  rfl

theorem affineCocycleGenerators_commute (representation : Rep ℂ RadicalLattice) (alpha beta : representation)
    (closed : (representation.ρ radicalLatticeFirst - 1) beta =
      (representation.ρ radicalLatticeSecond - 1) alpha) :
    Commute (affineCocycleGenerator representation radicalLatticeFirst alpha)
      (affineCocycleGenerator representation radicalLatticeSecond beta) := by
  apply AffineEquiv.ext
  intro vector
  change alpha + representation.ρ radicalLatticeFirst (beta + representation.ρ radicalLatticeSecond vector) =
    beta + representation.ρ radicalLatticeSecond (alpha + representation.ρ radicalLatticeFirst vector)
  have translations : representation.ρ radicalLatticeFirst beta + alpha =
      representation.ρ radicalLatticeSecond alpha + beta := sub_eq_sub_iff_add_eq_add.mp closed
  have actions : representation.ρ radicalLatticeFirst (representation.ρ radicalLatticeSecond vector) =
      representation.ρ radicalLatticeSecond (representation.ρ radicalLatticeFirst vector) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      mul_comm radicalLatticeFirst radicalLatticeSecond]
  rw [map_add, map_add, actions]
  calc
    _ = (representation.ρ radicalLatticeFirst beta + alpha) +
        representation.ρ radicalLatticeSecond (representation.ρ radicalLatticeFirst vector) := by abel
    _ = _ := by rw [translations]; abel

def latticeAffineAction (representation : Rep ℂ RadicalLattice) (alpha beta : representation)
    (closed : (representation.ρ radicalLatticeFirst - 1) beta =
      (representation.ρ radicalLatticeSecond - 1) alpha) :
    RadicalLattice →* (representation ≃ᵃ[ℂ] representation) :=
  latticeHomOfCommute _ _ (affineCocycleGenerators_commute representation alpha beta closed)

theorem latticeAffineAction_linear (representation : Rep ℂ RadicalLattice) (alpha beta : representation)
    (closed : (representation.ρ radicalLatticeFirst - 1) beta =
      (representation.ρ radicalLatticeSecond - 1) alpha) (element : RadicalLattice) :
    (latticeAffineAction representation alpha beta closed element).linear =
      representationLinearEquiv representation element := by
  have equality : AffineEquiv.linearHom.comp (latticeAffineAction representation alpha beta closed) =
      representationLinearEquivHom representation := by
    apply latticeHom_ext
    · change (latticeAffineAction representation alpha beta closed radicalLatticeFirst).linear = _
      rw [latticeAffineAction, latticeHomOfCommute_first, affineCocycleGenerator_linear]
      rfl
    · change (latticeAffineAction representation alpha beta closed radicalLatticeSecond).linear = _
      rw [latticeAffineAction, latticeHomOfCommute_second, affineCocycleGenerator_linear]
      rfl
  exact congrArg (fun hom : RadicalLattice →* (representation ≃ₗ[ℂ] representation) => hom element) equality

def latticeCocycleOfClosedPair (representation : Rep ℂ RadicalLattice) (alpha beta : representation)
    (closed : (representation.ρ radicalLatticeFirst - 1) beta =
      (representation.ρ radicalLatticeSecond - 1) alpha) : groupCohomology.cocycles₁ representation := by
  refine ⟨fun element => latticeAffineAction representation alpha beta closed element 0, ?_⟩
  apply (groupCohomology.mem_cocycles₁_iff _).mpr
  intro first second
  rw [map_mul]
  change latticeAffineAction representation alpha beta closed first
    (latticeAffineAction representation alpha beta closed second 0) = _
  have affine := (latticeAffineAction representation alpha beta closed first).map_vadd 0
    (latticeAffineAction representation alpha beta closed second 0)
  rw [latticeAffineAction_linear] at affine
  simpa only [vadd_eq_add, add_zero, representationLinearEquiv_apply] using affine

theorem latticeCocycleOfClosedPair_first (representation : Rep ℂ RadicalLattice) (alpha beta : representation)
    (closed : (representation.ρ radicalLatticeFirst - 1) beta =
      (representation.ρ radicalLatticeSecond - 1) alpha) :
    latticeCocycleOfClosedPair representation alpha beta closed radicalLatticeFirst = alpha := by
  change latticeAffineAction representation alpha beta closed radicalLatticeFirst 0 = alpha
  rw [latticeAffineAction, latticeHomOfCommute_first, affineCocycleGenerator_apply, map_zero, add_zero]

theorem latticeCocycleOfClosedPair_second (representation : Rep ℂ RadicalLattice) (alpha beta : representation)
    (closed : (representation.ρ radicalLatticeFirst - 1) beta =
      (representation.ρ radicalLatticeSecond - 1) alpha) :
    latticeCocycleOfClosedPair representation alpha beta closed radicalLatticeSecond = beta := by
  change latticeAffineAction representation alpha beta closed radicalLatticeSecond 0 = beta
  rw [latticeAffineAction, latticeHomOfCommute_second, affineCocycleGenerator_apply, map_zero, add_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
