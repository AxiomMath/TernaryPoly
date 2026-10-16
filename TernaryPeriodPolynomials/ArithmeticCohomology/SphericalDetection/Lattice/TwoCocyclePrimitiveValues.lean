module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Lattice.TwoCocycleDetection

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem latticeTwoCocycle_exists_primitive_of_alternation (representation : Rep ℂ RadicalLattice)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0)
    (alpha beta : representation)
    (alternation : latticeTwoCocycleAlternation representation cycle =
      (representation.ρ radicalLatticeFirst - 1) beta - (representation.ρ radicalLatticeSecond - 1) alpha) :
    ∃ primitive : RadicalLattice → representation,
      primitive radicalLatticeFirst = alpha ∧ primitive radicalLatticeSecond = beta ∧
      ∀ first second, representation.ρ first (primitive second) - primitive (first * second) + primitive first = cycle (first, second) := by
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
  refine ⟨fun element => -(splitting element).coefficient, ?_, ?_, ?_⟩
  · change -(splitting radicalLatticeFirst).coefficient = alpha
    rw [latticeHomOfCommute_first]
    exact neg_neg alpha
  · change -(splitting radicalLatticeSecond).coefficient = beta
    rw [latticeHomOfCommute_second]
    exact neg_neg beta
  · exact twoCocycleExtension_section_boundary representation cycle unit_zero splitting
      (fun element => congrArg (fun hom : RadicalLattice →* RadicalLattice => hom element) projects)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
