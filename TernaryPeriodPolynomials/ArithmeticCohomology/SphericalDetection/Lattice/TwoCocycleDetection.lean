module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Lattice.CocycleExtension
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Two.CocycleExtension

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def latticeTwoCocycleAlternation (representation : Rep ℂ RadicalLattice) :
    groupCohomology.cocycles₂ representation →ₗ[ℂ] representation where
  toFun cycle := cycle (radicalLatticeFirst, radicalLatticeSecond) - cycle (radicalLatticeSecond, radicalLatticeFirst)
  map_add' first second := by
    change (first (radicalLatticeFirst, radicalLatticeSecond) + second (radicalLatticeFirst, radicalLatticeSecond)) -
      (first (radicalLatticeSecond, radicalLatticeFirst) + second (radicalLatticeSecond, radicalLatticeFirst)) =
      (first (radicalLatticeFirst, radicalLatticeSecond) - first (radicalLatticeSecond, radicalLatticeFirst)) +
      (second (radicalLatticeFirst, radicalLatticeSecond) - second (radicalLatticeSecond, radicalLatticeFirst))
    abel
  map_smul' scalar cycle := by
    exact (smul_sub scalar _ _).symm

theorem latticeTwoCocycleAlternation_apply (representation : Rep ℂ RadicalLattice)
    (cycle : groupCohomology.cocycles₂ representation) :
    latticeTwoCocycleAlternation representation cycle =
      cycle (radicalLatticeFirst, radicalLatticeSecond) - cycle (radicalLatticeSecond, radicalLatticeFirst) := rfl

theorem latticeTwoCocycleAlternation_boundary (representation : Rep ℂ RadicalLattice) (primitive : RadicalLattice → representation) :
    latticeTwoCocycleAlternation representation (twoBoundaryCycle representation primitive) =
      (representation.ρ radicalLatticeFirst - 1) (primitive radicalLatticeSecond) -
        (representation.ρ radicalLatticeSecond - 1) (primitive radicalLatticeFirst) := by
  rw [latticeTwoCocycleAlternation_apply, twoBoundaryCycle_apply, twoBoundaryCycle_apply,
    mul_comm radicalLatticeFirst radicalLatticeSecond]
  change representation.ρ radicalLatticeFirst (primitive radicalLatticeSecond) -
    primitive (radicalLatticeSecond * radicalLatticeFirst) + primitive radicalLatticeFirst -
    (representation.ρ radicalLatticeSecond (primitive radicalLatticeFirst) -
      primitive (radicalLatticeSecond * radicalLatticeFirst) + primitive radicalLatticeSecond) =
    (representation.ρ radicalLatticeFirst (primitive radicalLatticeSecond) - primitive radicalLatticeSecond) -
      (representation.ρ radicalLatticeSecond (primitive radicalLatticeFirst) - primitive radicalLatticeFirst)
  abel

theorem latticeTwoCocycle_H2_zero_of_normalized_alternation (representation : Rep ℂ RadicalLattice)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0)
    (alpha beta : representation)
    (alternation : latticeTwoCocycleAlternation representation cycle =
      (representation.ρ radicalLatticeFirst - 1) beta - (representation.ρ radicalLatticeSecond - 1) alpha) :
    groupCohomology.H2π representation cycle = 0 := by
  let first : TwoCocycleExtension representation cycle unit_zero := ⟨-alpha, radicalLatticeFirst⟩
  let second : TwoCocycleExtension representation cycle unit_zero := ⟨-beta, radicalLatticeSecond⟩
  have commute : Commute first second := by
    apply TwoCocycleExtension.ext
    · change -alpha + representation.ρ radicalLatticeFirst (-beta) + cycle (radicalLatticeFirst, radicalLatticeSecond) =
        -beta + representation.ρ radicalLatticeSecond (-alpha) + cycle (radicalLatticeSecond, radicalLatticeFirst)
      change cycle (radicalLatticeFirst, radicalLatticeSecond) - cycle (radicalLatticeSecond, radicalLatticeFirst) =
        (representation.ρ radicalLatticeFirst beta - beta) - (representation.ρ radicalLatticeSecond alpha - alpha) at alternation
      rw [map_neg, map_neg]
      linear_combination (norm := abel) alternation
    · exact mul_comm _ _
  let splitting := latticeHomOfCommute first second commute
  have projects : (twoCocycleExtensionProjection representation cycle unit_zero).comp splitting = MonoidHom.id RadicalLattice := by
    apply latticeHom_ext
    · change twoCocycleExtensionProjection representation cycle unit_zero (splitting radicalLatticeFirst) = radicalLatticeFirst
      rw [latticeHomOfCommute_first]
      rfl
    · change twoCocycleExtensionProjection representation cycle unit_zero (splitting radicalLatticeSecond) = radicalLatticeSecond
      rw [latticeHomOfCommute_second]
      rfl
  rw [groupCohomology.H2π_eq_zero_iff]
  refine ⟨fun element => -(splitting element).coefficient, ?_⟩
  funext pair
  exact twoCocycleExtension_section_boundary representation cycle unit_zero splitting
    (fun element => congrArg (fun hom : RadicalLattice →* RadicalLattice => hom element) projects) pair.1 pair.2

/-- Actual lattice H2 vanishes exactly when its generator alternation is a sum of action differences. -/
theorem latticeTwoCocycle_H2_zero_iff (representation : Rep ℂ RadicalLattice)
    (cycle : groupCohomology.cocycles₂ representation) :
    groupCohomology.H2π representation cycle = 0 ↔
      ∃ alpha beta : representation, latticeTwoCocycleAlternation representation cycle =
        (representation.ρ radicalLatticeFirst - 1) beta - (representation.ρ radicalLatticeSecond - 1) alpha := by
  constructor
  · intro zero
    obtain ⟨primitive, boundary⟩ := (groupCohomology.H2π_eq_zero_iff cycle).mp zero
    change RadicalLattice → representation at primitive
    refine ⟨primitive radicalLatticeFirst, primitive radicalLatticeSecond, ?_⟩
    have equality : twoBoundaryCycle representation primitive = cycle := Subtype.ext boundary
    rw [← equality, latticeTwoCocycleAlternation_boundary]
  · rintro ⟨alpha, beta, alternation⟩
    rw [← unitNormalizedTwoCocycle_H2]
    apply latticeTwoCocycle_H2_zero_of_normalized_alternation representation
      (unitNormalizedTwoCocycle representation cycle) (unitNormalizedTwoCocycle_unit representation cycle)
      (alpha - cycle (1, 1)) (beta - cycle (1, 1))
    rw [unitNormalizedTwoCocycle,
      (latticeTwoCocycleAlternation representation).map_sub cycle (twoBoundaryCycle representation (fun _ => cycle (1, 1))),
      latticeTwoCocycleAlternation_boundary, alternation, map_sub, map_sub]
    abel

end TernaryPeriodPolynomials.SphericalDetection.Helpers
