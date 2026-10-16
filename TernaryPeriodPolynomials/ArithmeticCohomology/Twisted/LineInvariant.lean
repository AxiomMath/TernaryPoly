module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineStab

@[expose] public section


/-!
# Radical invariants of the twisted good line, and injectivity of the edge

The invariants of the lower radical in the twisted coefficient system are the binary forms
`binaryHomogeneousLift n b`, and the Levi quotient acts on them through `Sym^n` with determinant
twist `0` (the untwisted twist `-1` raised by one), `goodLineInvariantIsoT`.  Since `-1 ∈ GL₂(ℤ)` is
central and acts by `-1` on `Sym^n` for odd `n`, `H²(GL₂(ℤ), Sym^n)` vanishes
(`arithmeticBinaryH2_zero_of_oddT`), and hence the twisted good-line edge is injective for odd `n`
(`goodLineBinaryEdge_injective_of_oddT`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Twisted

theorem lowerRadicalInvariants_eqT (n : ℕ) (χ : RankOneCharacter) :
    (lowerRadicalLatticeRep n).ρ.invariants = (goodLineRadicalRepT n χ).ρ.invariants := by
  apply Submodule.ext
  intro vector
  have left := Representation.mem_invariants (lowerRadicalLatticeRep n).ρ vector
  have right := Representation.mem_invariants (goodLineRadicalRepT n χ).ρ vector
  refine left.trans (Iff.trans ?_ right.symm)
  apply forall_congr'
  intro element
  change rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice element) vector = vector ↔
    rationalCoefficientComponent n χ (lowerRadicalLattice element) vector = vector
  rw [rho_lowerRadicalLattice n χ element]

/-- Binary coordinates on the radical invariants of the twisted good-line stabilizer. -/
def lowerRadicalInvariantEquivT (n : ℕ) (χ : RankOneCharacter) :
    Binary.HomogeneousPoly n ≃ₗ[ℂ] (goodLineRadicalRepT n χ).ρ.invariants :=
  (lowerRadicalInvariantEquiv n).trans (LinearEquiv.ofEq _ _ (lowerRadicalInvariants_eqT n χ))

theorem lowerRadicalInvariantEquivT_apply (n : ℕ) (χ : RankOneCharacter)
    (binary : Binary.HomogeneousPoly n) :
    (lowerRadicalInvariantEquivT n χ binary).val = binaryHomogeneousLift n binary := rfl

/-- The twisted Levi action on the radical invariants: the untwisted action with the determinant
twist raised by one. -/
theorem arithmeticLevi_lowerInvariantT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (binary : Binary.HomogeneousPoly n) :
    rationalCoefficientComponent n χ (arithmeticLevi matrix) (binaryHomogeneousLift n binary) =
      binaryHomogeneousLift n ((arithmeticBinaryRep n 0).ρ matrix binary) := by
  have twist := homogeneousAction_succ_twist n (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
  rw [neg_add_cancel, goodLineDetMapT] at twist
  have action : (((GeneralLinearGroup.det matrix : ℤˣ) : ℤ) : ℂ) •
        (arithmeticBinaryRep n (-1)).ρ matrix binary = (arithmeticBinaryRep n 0).ρ matrix binary :=
    (LinearMap.congr_fun twist binary).symm
  rw [rho_arithmeticLevi_odd n hχ matrix, LinearMap.smul_apply,
    arithmeticLevi_lowerInvariant n matrix binary, ← action]
  exact (map_smul (binaryHomogeneousLift n) _ _).symm

/-- The radical invariants of the twisted good-line stabilizer form `Sym^n` as a representation of
the Levi quotient. -/
def goodLineInvariantIsoT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    arithmeticBinaryRep n 0 ≅ splitInvariantRepresentation goodLineSplitting (goodLineCoefficientRepT n χ) :=
  Rep.mkIso (Representation.Equiv.mk (lowerRadicalInvariantEquivT n χ) (by
    intro matrix
    apply LinearMap.ext
    intro binary
    apply Subtype.ext
    exact (arithmeticLevi_lowerInvariantT n χ hχ matrix binary).symm))

def goodLineInvariantH2IsoT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    groupCohomology.H2 (arithmeticBinaryRep n 0) ≅
      groupCohomology.H2 (splitInvariantRepresentation goodLineSplitting (goodLineCoefficientRepT n χ)) :=
  (groupCohomology.functor ℂ (GeneralLinearGroup (Fin 2) ℤ) 2).mapIso (goodLineInvariantIsoT n χ hχ)

/-- The central element `-1 ∈ GL₂(ℤ)` acts on `Sym^d` by `-1` when `d` is odd. -/
theorem arithmeticBinaryRep_scalar_neg_one_zeroT (degree : ℕ) (odd : Odd degree)
    (polynomial : Binary.HomogeneousPoly degree) :
    (arithmeticBinaryRep degree 0).ρ (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) polynomial =
      (-1 : ℂ) • polynomial := by
  have unit_determinant : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) = 1 := by
    simp [GeneralLinearGroup.det_scalar]
  have determinant : (((GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) : ℤˣ) : ℤ) : ℂ) = 1 := by
    simp [unit_determinant]
  have twist := homogeneousAction_succ_twist degree (-1)
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)))
  rw [neg_add_cancel, goodLineDetMapT, determinant, one_smul] at twist
  change Binary.homogeneousAction degree 0
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ))) polynomial = _
  rw [twist]
  exact arithmeticBinaryRep_scalar_neg_one degree odd polynomial

theorem arithmeticBinaryH2_zero_of_oddT (degree : ℕ) (odd : Odd degree)
    (cohomology : groupCohomology.H2 (arithmeticBinaryRep degree 0)) : cohomology = 0 :=
  groupH2_zero_of_central_scalar (arithmeticBinaryRep degree 0)
    (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) (GeneralLinearGroup.scalar_commute (-1))
    (-1) (by norm_num) (arithmeticBinaryRep_scalar_neg_one_zeroT degree odd) cohomology

theorem goodLineInvariantH2_zero_of_oddT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (odd : Odd n)
    (cohomology : groupCohomology.H2 (splitInvariantRepresentation goodLineSplitting (goodLineCoefficientRepT n χ))) :
    cohomology = 0 := by
  obtain ⟨binary_class, rfl⟩ :=
    (ConcreteCategory.bijective_of_isIso (goodLineInvariantH2IsoT n χ hχ).hom).surjective cohomology
  rw [arithmeticBinaryH2_zero_of_oddT n odd binary_class, map_zero]

theorem goodLineBinaryEdge_kernelT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) :
    (goodLineBinaryEdgeT n χ hχ positive).ker =
      (splitInvariantInflationKernel goodLineSplitting (goodLineCoefficientRepT n χ)).range := by
  rw [splitCohomologyEdge_exact]
  apply LinearMap.ker_comp_of_ker_eq_bot
  exact LinearMap.ker_eq_bot.mpr
    (ConcreteCategory.bijective_of_isIso (goodLineLeviCohomologyIsoT n χ hχ positive).hom).injective

theorem goodLineBinaryEdge_zero_iff_inflationT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n)
    (cohomology : (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRepT n χ)).ker) :
    goodLineBinaryEdgeT n χ hχ positive cohomology = 0 ↔
      ∃ levi_class : groupCohomology.H2
          (splitInvariantRepresentation goodLineSplitting (goodLineCoefficientRepT n χ)),
        splitInvariantInflation goodLineSplitting (goodLineCoefficientRepT n χ) levi_class =
          cohomology.val := by
  change cohomology ∈ (goodLineBinaryEdgeT n χ hχ positive).ker ↔ _
  rw [goodLineBinaryEdge_kernelT]
  constructor
  · rintro ⟨levi_class, equality⟩
    exact ⟨levi_class, congrArg Subtype.val equality⟩
  · rintro ⟨levi_class, equality⟩
    exact ⟨levi_class, Subtype.ext equality⟩

theorem goodLineBinaryEdge_injective_of_invariant_H2_zeroT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n)
    (vanishing : ∀ cohomology : groupCohomology.H2
      (splitInvariantRepresentation goodLineSplitting (goodLineCoefficientRepT n χ)), cohomology = 0) :
    Function.Injective (goodLineBinaryEdgeT n χ hχ positive) :=
  (ConcreteCategory.bijective_of_isIso (goodLineLeviCohomologyIsoT n χ hχ positive).hom).injective.comp
    (splitCohomologyEdge_injective_of_invariant_H2_zero goodLineSplitting (goodLineCoefficientRepT n χ)
      vanishing)

/-- **The twisted good-line edge is injective for odd `n`.** -/
theorem goodLineBinaryEdge_injective_of_oddT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n) :
    Function.Injective (goodLineBinaryEdgeT n χ hχ positive) :=
  goodLineBinaryEdge_injective_of_invariant_H2_zeroT n χ hχ positive
    (goodLineInvariantH2_zero_of_oddT n χ hχ odd)

end TernaryPeriodPolynomials.Twisted
