module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Kostant
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Radical

@[expose] public section


/-!
# The Kostant law for the genuine radical cocycle

If the radical cocycle `lam` of a `PlaneCupData` agrees on the radical lattice with the radical
`planeRadical n trivialCharacter` of the real plane parabolic at the real unipotent
`planeUnipotent r₁ r₂` of the lattice point `(r₁, r₂)`, then `lam` satisfies the Kostant law with
`c = -1` (`kostantLaw_of_planeRadical`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

open MvPolynomial GeneralEisenstein
open GeneralEisenstein.Adelic (planeUnipotent)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (RadicalLattice radicalLatticeFirst radicalLatticeSecond identityPlaneRadicalInclusion
    binaryHomogeneousRestrict binaryHomogeneousRestrict_apply)

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

/-- **The Kostant law for `planeRadical`.**  `c = -1`. -/
theorem kostantLaw_of_planeRadical {n : ℕ} {lam : RadicalLattice → (PlaneQ n →ₗ[ℂ] PlaneV n)}
    (hlam : ∀ (r : RadicalLattice) (q : PlaneQ n),
      lam r q =
        planeRadical n trivialCharacter
          ⟨planeUnipotent (((r.toAdd.1 : ℤ) : ℝ)) (((r.toAdd.2 : ℤ) : ℝ)),
            planeUnipotent_mem _ _⟩ q) :
    KostantLaw n lam (-1) := by
  apply kostantLaw_of_derivative
  · intro q
    rw [hlam, binaryHomogeneousRestrict_apply,
      binaryPolynomialRestrict_planeRadical_unipotent]
    simp [radicalLatticeFirst]
  · intro q
    rw [hlam, binaryHomogeneousRestrict_apply,
      binaryPolynomialRestrict_planeRadical_unipotent]
    simp [radicalLatticeSecond]

end TernaryPeriodPolynomials.SourceConstruction
