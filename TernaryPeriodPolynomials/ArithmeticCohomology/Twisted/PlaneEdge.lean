module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PlaneStab
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IdentityPlaneRestriction

@[expose] public section


/-!
# The twisted identity-plane binary edge: injectivity and the full edge

For `χ(-1_∞) = -1` the radical invariants form the trivial `GL₂(ℤ)`-module, whose second cohomology
vanishes (it is trivial on `SL₂(ℤ)`).  Hence the twisted Hochschild–Serre edge
`identityPlaneBinaryEdgeT` is injective.  In odd degree the central Levi element `-1` has
determinant `1`, so the restriction of every identity-plane class to the radical vanishes exactly as
in the untwisted case, and the edge is defined on all of `H²(Λ₀, V_χ)`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Twisted

/-! ### Vanishing of the invariant cohomology and injectivity of the edge -/

/-- `H²(GL₂(ℤ), ℂ) = 0` for the trivial representation. -/
theorem arithmeticTrivialH2_zero (cohomology : groupCohomology.H2 arithmeticTrivialRep) :
    cohomology = 0 := by
  apply splitRestriction_injective_of_finite_quotient integralDeterminantSplitting arithmeticTrivialRep
  rw [map_zero]
  exact modularTrivialH2_zero (Rep.res SpecialLinearGroup.toGL arithmeticTrivialRep)
    (fun _ _ => rfl) _

theorem identityPlaneInvariantH2_zeroT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cohomology : groupCohomology.H2
      (splitInvariantRepresentation identityPlaneSplitting (identityPlaneCoefficientRepT n χ))) :
    cohomology = 0 := by
  obtain ⟨source_class, rfl⟩ :=
    (ConcreteCategory.bijective_of_isIso (identityPlaneInvariantH2IsoT n χ hχ).hom).surjective cohomology
  rw [arithmeticTrivialH2_zero source_class, map_zero]

theorem identityPlaneBinaryEdgeT_kernel (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    (identityPlaneBinaryEdgeT n χ hχ).ker =
      (splitInvariantInflationKernel identityPlaneSplitting (identityPlaneCoefficientRepT n χ)).range := by
  rw [splitCohomologyEdge_exact]
  apply LinearMap.ker_comp_of_ker_eq_bot
  exact LinearMap.ker_eq_bot.mpr
    (ConcreteCategory.bijective_of_isIso (identityPlaneLeviCohomologyIsoT n χ hχ).hom).injective

theorem identityPlaneBinaryEdgeT_zero_iff_inflation (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cohomology : (twoCohomologyRestriction identityPlaneRadicalInclusion
      (identityPlaneCoefficientRepT n χ)).ker) :
    identityPlaneBinaryEdgeT n χ hχ cohomology = 0 ↔
      ∃ levi_class : groupCohomology.H2
        (splitInvariantRepresentation identityPlaneSplitting (identityPlaneCoefficientRepT n χ)),
        splitInvariantInflation identityPlaneSplitting (identityPlaneCoefficientRepT n χ) levi_class =
          cohomology.val := by
  change cohomology ∈ (identityPlaneBinaryEdgeT n χ hχ).ker ↔ _
  rw [identityPlaneBinaryEdgeT_kernel]
  constructor
  · rintro ⟨levi_class, equality⟩
    exact ⟨levi_class, congrArg Subtype.val equality⟩
  · rintro ⟨levi_class, equality⟩
    exact ⟨levi_class, Subtype.ext equality⟩

/-- The inflation of `H²(GL₂(ℤ), ℂ)` into `H²(Λ₀, V_χ)` through the radical invariants. -/
def identityPlaneTrivialInflationT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    groupCohomology.H2 arithmeticTrivialRep →ₗ[ℂ] groupCohomology.H2 (identityPlaneCoefficientRepT n χ) :=
  (splitInvariantInflation identityPlaneSplitting (identityPlaneCoefficientRepT n χ)).comp
    (identityPlaneInvariantH2IsoT n χ hχ).hom.hom

theorem identityPlaneBinaryEdgeT_zero_iff_trivialInflation (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cohomology : (twoCohomologyRestriction identityPlaneRadicalInclusion
      (identityPlaneCoefficientRepT n χ)).ker) :
    identityPlaneBinaryEdgeT n χ hχ cohomology = 0 ↔
      ∃ trivial_class : groupCohomology.H2 arithmeticTrivialRep,
        identityPlaneTrivialInflationT n χ hχ trivial_class = cohomology.val := by
  rw [identityPlaneBinaryEdgeT_zero_iff_inflation]
  constructor
  · rintro ⟨levi_class, equality⟩
    obtain ⟨trivial_class, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (identityPlaneInvariantH2IsoT n χ hχ).hom).surjective levi_class
    exact ⟨trivial_class, equality⟩
  · rintro ⟨trivial_class, equality⟩
    exact ⟨(identityPlaneInvariantH2IsoT n χ hχ).hom trivial_class, equality⟩

/-- **The twisted edge is injective.** -/
theorem identityPlaneBinaryEdgeT_injective (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    Function.Injective (identityPlaneBinaryEdgeT n χ hχ) :=
  (ConcreteCategory.bijective_of_isIso (identityPlaneLeviCohomologyIsoT n χ hχ).hom).injective.comp
    (splitCohomologyEdge_injective_of_invariant_H2_zero identityPlaneSplitting
      (identityPlaneCoefficientRepT n χ) (identityPlaneInvariantH2_zeroT n χ hχ))

/-! ### The binary restriction and the radical H² criterion -/

theorem binaryHomogeneousRestrict_radicalT (n : ℕ) (χ : RankOneCharacter) (element : RadicalLattice)
    (polynomial : HomogeneousPoly n) :
    binaryHomogeneousRestrict n
        ((identityPlaneCoefficientRepT n χ).ρ (identityPlaneRadicalInclusion element) polynomial) =
      binaryHomogeneousRestrict n polynomial := by
  exact (congrArg
    (fun operator : Module.End ℂ (HomogeneousPoly n) => binaryHomogeneousRestrict n (operator polynomial))
    (rho_upperRadicalLattice n χ element)).trans
      (binaryHomogeneousRestrict_upperLattice n element polynomial)

/-- The twisted Levi action on the binary restriction: `Sym^n ⊗ det⁰`. -/
theorem binaryHomogeneousRestrict_arithmeticLeviT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (polynomial : HomogeneousPoly n) :
    binaryHomogeneousRestrict n (rationalCoefficientComponent n χ (arithmeticLevi matrix) polynomial) =
      Binary.homogeneousAction n 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (binaryHomogeneousRestrict n polynomial) := by
  rw [rho_arithmeticLevi_odd n hχ matrix, LinearMap.smul_apply, map_smul (binaryHomogeneousRestrict n),
    binaryHomogeneousRestrict_arithmeticLevi, homogeneousAction_zero_twist_apply]

theorem binaryHomogeneousRestrict_sectionT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (polynomial : HomogeneousPoly n) :
    binaryHomogeneousRestrict n
        ((identityPlaneCoefficientRepT n χ).ρ (identityPlaneLeviSection matrix) polynomial) =
      Binary.homogeneousAction n 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (binaryHomogeneousRestrict n polynomial) :=
  binaryHomogeneousRestrict_arithmeticLeviT n χ hχ matrix polynomial

theorem det_scalar_neg_one :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) = 1 := by
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin]
  exact neg_one_sq

/-- The central element `-1` of the Levi acts by `-1` on the binary restriction in odd degree: the
determinant of `-1` is `1`, so the twist is invisible. -/
theorem binaryHomogeneousRestrict_leviScalarT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (odd : Odd n)
    (polynomial : HomogeneousPoly n) :
    binaryHomogeneousRestrict n
        (rationalCoefficientComponent n χ
          (arithmeticLevi (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ))) polynomial) =
      -binaryHomogeneousRestrict n polynomial := by
  rw [rho_arithmeticLevi_odd n hχ, det_scalar_neg_one, LinearMap.smul_apply, Units.val_one,
    Int.cast_one, one_smul]
  exact binaryHomogeneousRestrict_scalar_neg_one n odd polynomial

theorem binaryHomogeneousRestrict_scalar_neg_oneT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (odd : Odd n)
    (polynomial : HomogeneousPoly n) :
    binaryHomogeneousRestrict n
        ((identityPlaneCoefficientRepT n χ).ρ
          (identityPlaneLeviSection (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ))) polynomial) =
      -binaryHomogeneousRestrict n polynomial :=
  binaryHomogeneousRestrict_leviScalarT n χ hχ odd polynomial

theorem radicalFirstRangeT (n : ℕ) (χ : RankOneCharacter) (positive : 0 < n) :
    ((rationalCoefficientComponent n χ (upperRadicalLattice radicalLatticeFirst)) - 1).range =
      (binaryHomogeneousRestrict n).ker := by
  rw [rho_upperRadicalLattice n χ radicalLatticeFirst]
  exact upperRadicalLattice_first_range n positive

theorem radicalSecondRangeT (n : ℕ) (χ : RankOneCharacter) (positive : 0 < n) :
    ((rationalCoefficientComponent n χ (upperRadicalLattice radicalLatticeSecond)) - 1).range =
      (binaryHomogeneousRestrict n).ker := by
  rw [rho_upperRadicalLattice n χ radicalLatticeSecond]
  exact upperRadicalLattice_second_range n positive

/-- A two-cocycle of the restricted twisted representation is a coboundary on the radical exactly when
the binary restriction of its alternation vanishes. -/
theorem radicalTwoCocycle_H2_zero_iffT (n : ℕ) (χ : RankOneCharacter) (positive : 0 < n)
    (cycle : groupCohomology.cocycles₂
      (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))) :
    groupCohomology.H2π (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) cycle = 0 ↔
      binaryHomogeneousRestrict n (latticeTwoCocycleAlternation
        (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) cycle) = 0 := by
  rw [latticeTwoCocycle_H2_zero_iff]
  constructor
  · rintro ⟨alpha, beta, equality⟩
    have first : ((Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)).ρ
        radicalLatticeFirst - 1) beta ∈ (binaryHomogeneousRestrict n).ker := by
      rw [← radicalFirstRangeT n χ positive]
      exact ⟨beta, rfl⟩
    have second : ((Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)).ρ
        radicalLatticeSecond - 1) alpha ∈ (binaryHomogeneousRestrict n).ker := by
      rw [← radicalSecondRangeT n χ positive]
      exact ⟨alpha, rfl⟩
    rw [equality]
    exact (binaryHomogeneousRestrict n).map_sub _ _ |>.trans (by rw [first, second, sub_self])
  · intro zero
    have member : latticeTwoCocycleAlternation
        (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) cycle ∈
        ((rationalCoefficientComponent n χ (upperRadicalLattice radicalLatticeFirst)) - 1).range := by
      rw [radicalFirstRangeT n χ positive]
      exact zero
    obtain ⟨beta, equality⟩ := member
    exact ⟨0, beta, by rw [map_zero, sub_zero]; exact equality.symm⟩

/-! ### Odd degree: the restriction to the radical vanishes -/

/-- In odd degree every identity-plane twisted class restricts to a coboundary on the radical. -/
theorem identityPlaneTwoCocycle_restriction_zeroT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n)
    (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRepT n χ)) :
    groupCohomology.H2π (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))
      (twoCocycleRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ) cycle) = 0 := by
  apply (radicalTwoCocycle_H2_zero_iffT n χ positive
    (twoCocycleRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ) cycle)).mpr
  exact twoCocycle_projected_alternation_zero identityPlaneRadicalInclusion
    (identityPlaneCoefficientRepT n χ) (binaryHomogeneousRestrict n)
    (binaryHomogeneousRestrict_radicalT n χ)
    (identityPlaneLeviSection (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)))
    identityPlaneLevi_neg_one_conjugates (binaryHomogeneousRestrict_scalar_neg_oneT n χ hχ odd)
    cycle radicalLatticeFirst radicalLatticeSecond

theorem identityPlaneH2_restriction_zeroT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n)
    (cohomology : groupCohomology.H2 (identityPlaneCoefficientRepT n χ)) :
    twoCohomologyRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)
      cohomology = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective (identityPlaneCoefficientRepT n χ) cohomology
  rw [twoCohomologyRestriction_apply]
  exact identityPlaneTwoCocycle_restriction_zeroT n χ hχ positive odd cycle

def identityPlaneH2ToRestrictionKernelT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n) :
    groupCohomology.H2 (identityPlaneCoefficientRepT n χ) →ₗ[ℂ]
      (twoCohomologyRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)).ker :=
  LinearMap.id.codRestrict _ (identityPlaneH2_restriction_zeroT n χ hχ positive odd)

/-- **In odd degree the twisted binary edge is defined on every `H²(Λ₀, V_χ)` class.** -/
def identityPlaneFullBinaryEdgeT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n) :
    groupCohomology.H2 (identityPlaneCoefficientRepT n χ) →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0) :=
  (identityPlaneBinaryEdgeT n χ hχ).comp (identityPlaneH2ToRestrictionKernelT n χ hχ positive odd)

theorem identityPlaneFullBinaryEdgeT_injective (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n) :
    Function.Injective (identityPlaneFullBinaryEdgeT n χ hχ positive odd) := by
  intro first second equality
  have kernels := identityPlaneBinaryEdgeT_injective n χ hχ equality
  exact congrArg Subtype.val kernels

theorem identityPlaneFullBinaryEdgeT_zero_iff (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n)
    (cohomology : groupCohomology.H2 (identityPlaneCoefficientRepT n χ)) :
    identityPlaneFullBinaryEdgeT n χ hχ positive odd cohomology = 0 ↔ cohomology = 0 :=
  LinearMap.map_eq_zero_iff _ (identityPlaneFullBinaryEdgeT_injective n χ hχ positive odd)

end TernaryPeriodPolynomials.Twisted
