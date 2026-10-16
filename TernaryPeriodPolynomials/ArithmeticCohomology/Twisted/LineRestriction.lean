module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEven

@[expose] public section


/-!
# The radical restriction at the sign-twisted good line vanishes identically

Let `κ` be the coefficient of `X₂ⁿ`, which kills `N₀ V + N₁ V` and is invariant under the lower
radical (`GoodLineRestriction`).  For a two-cocycle `z` of the good-line stabilizer with
sign-twisted coefficients, the form `(u, v) ↦ κ(z(u, v) - z(v, u))` on the radical `ℤ²` is
`det(u, v)` times its value `a` at `(e₁, e₂)`.  The Levi element `diag(m, 1)` acts on `κ` with the
factor `det m` coming from the sign twist times `det m⁻¹` from `κ` itself, hence trivially, so
conjugation gives `a = det m · a` for every `m ∈ GL₂(ℤ)`.  Taking `m = diag(-1, 1)` gives `a = 0`,
so the restriction of every class to the radical vanishes (for the trivial character the two factors
cancel the other way and no conclusion is possible).  Consequently the good-line edge is defined on
all of `H²(Λ₁, V_χ)` (`goodLineFullBinaryEdgeT`) and is injective.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.Twisted

/-! ### Transport of radical two-cocycles -/

/-- Transport of two-cocycles of the twisted radical representation to the untwisted one. -/
def goodLineCocycle2CastT (n : ℕ) (χ : RankOneCharacter) :
    groupCohomology.cocycles₂ (goodLineRadicalRepT n χ) →ₗ[ℂ]
      groupCohomology.cocycles₂ (lowerRadicalLatticeRep n) :=
  (groupCohomology.mapCocycles₂ (MonoidHom.id RadicalLattice) (lowerRadicalHomT n χ)).hom

theorem goodLineCocycle2CastT_apply (n : ℕ) (χ : RankOneCharacter)
    (cycle : groupCohomology.cocycles₂ (goodLineRadicalRepT n χ))
    (pair : RadicalLattice × RadicalLattice) :
    goodLineCocycle2CastT n χ cycle pair = cycle pair := by
  have equality := groupCohomology.mapCocycles₂_comp_i_apply (MonoidHom.id RadicalLattice)
    (lowerRadicalHomT n χ) cycle
  exact congrFun equality pair

/-- Transport of the degree-two radical cohomology. -/
def goodLineH2CastIsoT (n : ℕ) (χ : RankOneCharacter) :
    groupCohomology.H2 (goodLineRadicalRepT n χ) ≅ groupCohomology.H2 (lowerRadicalLatticeRep n) :=
  (groupCohomology.functor ℂ RadicalLattice 2).mapIso (lowerRadicalIsoT n χ)

theorem goodLineH2CastIsoT_apply (n : ℕ) (χ : RankOneCharacter)
    (cycle : groupCohomology.cocycles₂ (goodLineRadicalRepT n χ)) :
    (goodLineH2CastIsoT n χ).hom (groupCohomology.H2π (goodLineRadicalRepT n χ) cycle) =
      groupCohomology.H2π (lowerRadicalLatticeRep n) (goodLineCocycle2CastT n χ cycle) :=
  groupCohomology.H2π_comp_map_apply (A := lowerRadicalRepT n χ) (B := lowerRadicalLatticeRep n)
    (MonoidHom.id RadicalLattice) (lowerRadicalHomT n χ) cycle

/-! ### The `κ`-alternation of a radical two-cocycle -/

/-- The `κ`-alternation form `(u, v) ↦ κ(z(u, v) - z(v, u))` of a two-cocycle on the lower radical. -/
def goodLineAltT (n : ℕ) (χ : RankOneCharacter)
    (cycle : groupCohomology.cocycles₂ (goodLineCoefficientRepT n χ)) (first second : RadicalLattice) : ℂ :=
  GoodLineRestriction.kappa n
    (cycle (goodLineRadicalInclusion first, goodLineRadicalInclusion second) -
      cycle (goodLineRadicalInclusion second, goodLineRadicalInclusion first))

/-- The lower radical acts trivially on the coefficient `κ`, also for the twisted coefficients. -/
theorem goodLineRadicalTrivialT (n : ℕ) (χ : RankOneCharacter) (radical : RadicalLattice)
    (vector : HomogeneousPoly n) :
    GoodLineRestriction.kappa n ((goodLineCoefficientRepT n χ).ρ (goodLineRadicalInclusion radical) vector) =
      GoodLineRestriction.kappa n vector := by
  change GoodLineRestriction.kappa n (rationalCoefficientComponent n χ (lowerRadicalLattice radical) vector) =
    GoodLineRestriction.kappa n vector
  rw [rho_lowerRadicalLattice n χ radical]
  exact GoodLineRestriction.kappa_rhoU n radical vector

theorem goodLineAltT_eq_det (n : ℕ) (χ : RankOneCharacter)
    (cycle : groupCohomology.cocycles₂ (goodLineCoefficientRepT n χ)) (u v : RadicalLattice) :
    goodLineAltT n χ cycle u v =
      (u.toAdd.1 * v.toAdd.2 - u.toAdd.2 * v.toAdd.1) •
        goodLineAltT n χ cycle radicalLatticeFirst radicalLatticeSecond := by
  apply IdentityPlaneEven.alternating_eq_det (goodLineAltT n χ cycle)
  · intro x y z
    exact IdentityPlaneEven.projected_alternation_mul goodLineRadicalInclusion
      (goodLineCoefficientRepT n χ) (GoodLineRestriction.kappa n) (goodLineRadicalTrivialT n χ)
      cycle x y z
  · intro x y
    exact IdentityPlaneEven.map_sub_eq_neg_map_sub (GoodLineRestriction.kappa n) _ _
  · intro x
    rw [goodLineAltT, sub_self]
    exact LinearMap.map_zero _

/-! ### Levi conjugation -/

theorem goodLineLevi_conjugatesT (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    (goodLineLeviSection matrix)⁻¹ * goodLineRadicalInclusion radical * goodLineLeviSection matrix =
      goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical) := by
  apply Subtype.ext
  change (arithmeticLevi matrix)⁻¹ * lowerRadicalLattice radical * arithmeticLevi matrix =
    lowerRadicalLattice (lowerLeviLatticeInput matrix radical)
  rw [mul_assoc, lowerLeviLatticeInput_conjugation, inv_mul_cancel_left]

/-- The rational determinant of the complex image of an integral matrix. -/
theorem goodLineValDetMapT (m : GeneralLinearGroup (Fin 2) ℤ) :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) m).val.det = (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) :=
  (GeneralLinearGroup.val_det_apply _).symm.trans (goodLineDetMapT m)

/-- **The sign twist cancels the determinant in the `κ`-factor of the Levi element.** -/
theorem goodLineKappa_leviT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (m : GeneralLinearGroup (Fin 2) ℤ)
    (vector : HomogeneousPoly n) :
    GoodLineRestriction.kappa n ((goodLineCoefficientRepT n χ).ρ (goodLineLeviSection m) vector) =
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (GoodLineRestriction.kappa n vector) := by
  have nonzero : (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) ≠ 0 :=
    left_ne_zero_of_mul_eq_one (goodLineDetSqT m)
  have scalar : (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) *
      ((((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ)⁻¹ * (((1 : ℂˣ) : ℂ)⁻¹) ^ (n + 1)) = 1 := by
    simp only [Units.val_one, inv_one, one_pow, mul_one]
    exact mul_inv_cancel₀ nonzero
  change GoodLineRestriction.kappa n (rationalCoefficientComponent n χ (arithmeticLevi m) vector) =
    GoodLineRestriction.kappa n vector
  rw [rho_arithmeticLevi_odd n hχ m, LinearMap.smul_apply, map_smul,
    arithmeticLeviCoefficient_homogeneous, GoodLineRestriction.kappa_levi, goodLineValDetMapT,
    smul_eq_mul, ← mul_assoc, scalar, one_mul]

/-- **Conjugation by `diag(m, 1)` preserves the `κ`-alternation of a twisted good-line cocycle.** -/
theorem goodLineAltT_leviT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (m : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₂ (goodLineCoefficientRepT n χ)) (u v : RadicalLattice) :
    goodLineAltT n χ cycle (lowerLeviLatticeInput m u) (lowerLeviLatticeInput m v) =
      goodLineAltT n χ cycle u v :=
  IdentityPlaneEven.projected_alternation_conj goodLineRadicalInclusion (goodLineCoefficientRepT n χ)
    (GoodLineRestriction.kappa n) (goodLineRadicalTrivialT n χ) (goodLineLeviSection m)
    (lowerLeviLatticeInput m) (goodLineLevi_conjugatesT m) LinearMap.id (goodLineKappa_leviT n χ hχ m)
    cycle u v

/-- The Levi matrix `diag(-1, 1)` of determinant `-1`. -/
def goodLineFlipT : GeneralLinearGroup (Fin 2) ℤ :=
  ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem goodLineFlipT_det :
    (lowerLeviLatticeInput goodLineFlipT radicalLatticeFirst).toAdd.1 *
        (lowerLeviLatticeInput goodLineFlipT radicalLatticeSecond).toAdd.2 -
      (lowerLeviLatticeInput goodLineFlipT radicalLatticeFirst).toAdd.2 *
        (lowerLeviLatticeInput goodLineFlipT radicalLatticeSecond).toAdd.1 = -1 := by
  simp [lowerLeviLatticeInput, radicalLatticeFirst, radicalLatticeSecond, goodLineFlipT]

/-- **For the sign-twisted coefficients the `κ`-alternation of every radical two-cocycle
vanishes.** -/
theorem goodLineAltT_eq_zeroT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cycle : groupCohomology.cocycles₂ (goodLineCoefficientRepT n χ)) :
    goodLineAltT n χ cycle radicalLatticeFirst radicalLatticeSecond = 0 := by
  have conjugated := goodLineAltT_leviT n χ hχ goodLineFlipT cycle radicalLatticeFirst radicalLatticeSecond
  rw [goodLineAltT_eq_det n χ cycle (lowerLeviLatticeInput goodLineFlipT radicalLatticeFirst)
    (lowerLeviLatticeInput goodLineFlipT radicalLatticeSecond), goodLineFlipT_det, zsmul_eq_mul]
    at conjugated
  push_cast at conjugated
  linear_combination (-1 / 2 : ℂ) * conjugated

/-! ### Vanishing of the radical restriction -/

theorem goodLineTwoCocycle_restriction_zeroT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cycle : groupCohomology.cocycles₂ (goodLineCoefficientRepT n χ)) :
    groupCohomology.H2π (goodLineRadicalRepT n χ)
      (twoCocycleRestriction goodLineRadicalInclusion (goodLineCoefficientRepT n χ) cycle) = 0 := by
  have vanishing : groupCohomology.H2π (lowerRadicalLatticeRep n)
      (goodLineCocycle2CastT n χ
        (twoCocycleRestriction goodLineRadicalInclusion (goodLineCoefficientRepT n χ) cycle)) = 0 := by
    apply GoodLineRestriction.H2_zero_of_kappa
    have alternation : latticeTwoCocycleAlternation (lowerRadicalLatticeRep n)
        (goodLineCocycle2CastT n χ
          (twoCocycleRestriction goodLineRadicalInclusion (goodLineCoefficientRepT n χ) cycle)) =
        cycle (goodLineRadicalInclusion radicalLatticeFirst, goodLineRadicalInclusion radicalLatticeSecond) -
          cycle (goodLineRadicalInclusion radicalLatticeSecond, goodLineRadicalInclusion radicalLatticeFirst) := by
      rw [latticeTwoCocycleAlternation_apply, goodLineCocycle2CastT_apply, goodLineCocycle2CastT_apply]
      rfl
    rw [alternation]
    exact goodLineAltT_eq_zeroT n χ hχ cycle
  have transported := goodLineH2CastIsoT_apply n χ
    (twoCocycleRestriction goodLineRadicalInclusion (goodLineCoefficientRepT n χ) cycle)
  rw [vanishing] at transported
  exact (ConcreteCategory.bijective_of_isIso (goodLineH2CastIsoT n χ).hom).injective
    (transported.trans (LinearMap.map_zero (goodLineH2CastIsoT n χ).hom.hom).symm)

/-- **The restriction of every class of `H²(Λ₁, V_χ)` to the lower radical vanishes.** -/
theorem goodLineH2_restriction_zeroT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cohomology : groupCohomology.H2 (goodLineCoefficientRepT n χ)) :
    twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRepT n χ) cohomology = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective (goodLineCoefficientRepT n χ) cohomology
  rw [twoCohomologyRestriction_apply]
  exact goodLineTwoCocycle_restriction_zeroT n χ hχ cycle

/-! ### The edge on the whole group cohomology -/

/-- The edge is injective for every `n > 0`, since `H²(GL₂(ℤ), W)` vanishes for every complex
representation `W`. -/
theorem goodLineBinaryEdge_injectiveT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) :
    Function.Injective (goodLineBinaryEdgeT n χ hχ positive) :=
  goodLineBinaryEdge_injective_of_invariant_H2_zeroT n χ hχ positive
    (fun cohomology => ModularH2.binaryH2_zero _ cohomology)

def goodLineH2ToRestrictionKernelT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    groupCohomology.H2 (goodLineCoefficientRepT n χ) →ₗ[ℂ]
      (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRepT n χ)).ker :=
  LinearMap.id.codRestrict _ (goodLineH2_restriction_zeroT n χ hχ)

/-- **The binary edge of the sign-twisted good line, defined on all of `H²(Λ₁, V_χ)`.** -/
def goodLineFullBinaryEdgeT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) :
    groupCohomology.H2 (goodLineCoefficientRepT n χ) →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1)) :=
  (goodLineBinaryEdgeT n χ hχ positive).comp (goodLineH2ToRestrictionKernelT n χ hχ)

theorem goodLineFullBinaryEdgeT_injective (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) :
    Function.Injective (goodLineFullBinaryEdgeT n χ hχ positive) := by
  intro first second equality
  have kernels := goodLineBinaryEdge_injectiveT n χ hχ positive equality
  exact congrArg Subtype.val kernels

theorem goodLineFullBinaryEdgeT_zero_iff (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n)
    (cohomology : groupCohomology.H2 (goodLineCoefficientRepT n χ)) :
    goodLineFullBinaryEdgeT n χ hχ positive cohomology = 0 ↔ cohomology = 0 :=
  LinearMap.map_eq_zero_iff _ (goodLineFullBinaryEdgeT_injective n χ hχ positive)

/-- On a relative class the full edge is the class of the edge cocycle. -/
theorem goodLineFullBinaryEdgeT_relative (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ)) :
    goodLineFullBinaryEdgeT n χ hχ positive (groupCohomology.H2π (goodLineCoefficientRepT n χ) cycle.val) =
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) (goodLineBinaryEdgeCycleT n χ hχ positive cycle) := by
  rw [goodLineBinaryEdgeCycle_H1T]
  rfl

/-- **Vanishing criterion for a relative class**, without a parity hypothesis. -/
theorem goodLineRelativeH2_zero_iff_binaryPotential_allT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ)) :
    groupCohomology.H2π (goodLineCoefficientRepT n χ) cycle.val = 0 ↔
      ∃ potential : Binary.HomogeneousPoly (n + 1), ∀ matrix : GeneralLinearGroup (Fin 2) ℤ,
        goodLineBinaryEdgeCycleT n χ hχ positive cycle matrix =
          Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) potential -
            potential := by
  rw [← goodLineFullBinaryEdgeT_zero_iff n χ hχ positive, goodLineFullBinaryEdgeT_relative,
    groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨potential, equality⟩
    exact ⟨potential, fun matrix => (congrFun equality matrix).symm⟩
  · rintro ⟨potential, equality⟩
    exact ⟨potential, funext (fun matrix => (equality matrix).symm)⟩

/-! ### The ambient version -/

/-- The edge on the ambient homogeneous cocycles of the good-line stabilizer with coefficients
`rationalCoefficientComponent n χ`. -/
def goodLineAmbientBinaryEdgeT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) :
    cocycles (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent n χ) →ₗ[ℂ]
        groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1)) :=
  (goodLineFullBinaryEdgeT n χ hχ positive).comp
    ((groupCohomology.H2π (goodLineCoefficientRepT n χ)).hom.comp
      (ambientCocycleToGroup (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n χ)))

theorem goodLineAmbientBinaryEdgeT_apply (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n)
    (cycle : cocycles (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent n χ)) :
    goodLineAmbientBinaryEdgeT n χ hχ positive cycle =
      goodLineFullBinaryEdgeT n χ hχ positive
        (groupCohomology.H2π (goodLineCoefficientRepT n χ)
          (ambientCocycleToGroup (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
            (rationalCoefficientComponent n χ) cycle)) := rfl

/-- Detection for the ambient homogeneous cochains. -/
theorem goodLineAmbientBinaryEdgeT_zero_iff (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n)
    (cycle : cocycles (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent n χ)) :
    goodLineAmbientBinaryEdgeT n χ hχ positive cycle = 0 ↔
      ∃ primitive, differentialOne (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n χ) primitive = cycle.val :=
  (goodLineFullBinaryEdgeT_zero_iff n χ hχ positive _).trans
    (ambientCocycle_H2_zero_iff (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent n χ) cycle)

end TernaryPeriodPolynomials.Twisted
