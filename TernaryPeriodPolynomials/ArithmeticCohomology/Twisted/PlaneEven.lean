module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PlaneEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEven

@[expose] public section


/-!
# The twisted identity-plane cusp has no cohomology in even degree

Let `Λ₀ = U ⋊ GL₂(ℤ)` be the stabilizer of the identity plane, `U ≅ ℤ²` its unipotent radical, and
`V_χ = rationalCoefficientComponent n χ` with `χ(-1_∞) = -1` and `n > 0` even.  Then `H²(Λ₀, V_χ) = 0`.

* The restriction to `U` vanishes: the projected alternation of a two-cocycle is `SL₂(ℤ)`-invariant
  (on `SL₂(ℤ)` the sign twist is invisible), hence zero.
* The edge target `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁰)` vanishes because the central element `-1` acts by `-1`
  on `Sym^{n+1}` with `n + 1` odd.
* The twisted edge is injective on the kernel of the restriction to `U`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.Twisted

/-- The projected alternation of a twisted identity-plane two-cocycle on the radical. -/
def alternationT (n : ℕ) (χ : RankOneCharacter)
    (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRepT n χ)) (u v : RadicalLattice) :
    Binary.HomogeneousPoly n :=
  binaryHomogeneousRestrict n
    (cycle (identityPlaneRadicalInclusion u, identityPlaneRadicalInclusion v) -
      cycle (identityPlaneRadicalInclusion v, identityPlaneRadicalInclusion u))

theorem alternationT_eq_det (n : ℕ) (χ : RankOneCharacter)
    (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRepT n χ)) (u v : RadicalLattice) :
    alternationT n χ cycle u v = (u.toAdd.1 * v.toAdd.2 - u.toAdd.2 * v.toAdd.1) •
      alternationT n χ cycle radicalLatticeFirst radicalLatticeSecond := by
  apply IdentityPlaneEven.alternating_eq_det (alternationT n χ cycle)
  · exact IdentityPlaneEven.projected_alternation_mul identityPlaneRadicalInclusion
      (identityPlaneCoefficientRepT n χ) (binaryHomogeneousRestrict n)
      (binaryHomogeneousRestrict_radicalT n χ) cycle
  · intro x y
    exact IdentityPlaneEven.map_sub_eq_neg_map_sub (binaryHomogeneousRestrict n) _ _
  · intro x
    rw [alternationT, sub_self]
    exact LinearMap.map_zero _

/-- The Levi element `diag(A, 1)` transforms the projected alternation by `A` with twist `0`. -/
theorem alternationT_levi (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRepT n χ))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (u v : RadicalLattice) :
    Binary.homogeneousAction n 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (alternationT n χ cycle (upperLeviLatticeInput matrix u) (upperLeviLatticeInput matrix v)) =
      alternationT n χ cycle u v :=
  IdentityPlaneEven.projected_alternation_conj identityPlaneRadicalInclusion
    (identityPlaneCoefficientRepT n χ) (binaryHomogeneousRestrict n)
    (binaryHomogeneousRestrict_radicalT n χ) (identityPlaneLeviSection matrix)
    (upperLeviLatticeInput matrix) (IdentityPlaneEven.identityPlaneLevi_conjugates matrix) _
    (binaryHomogeneousRestrict_sectionT n χ hχ matrix) cycle u v

/-- The projected alternation at `(e₁, e₂)` is `SL₂(ℤ)`-invariant. -/
theorem alternationT_modular_fixed (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRepT n χ))
    (g : SpecialLinearGroup (Fin 2) ℤ) :
    (ModularSymDimension.symRep n 0).ρ g
        (alternationT n χ cycle radicalLatticeFirst radicalLatticeSecond) =
      alternationT n χ cycle radicalLatticeFirst radicalLatticeSecond := by
  have h := alternationT_levi n χ hχ cycle (SpecialLinearGroup.toGL g) radicalLatticeFirst
    radicalLatticeSecond
  rw [alternationT_eq_det n χ cycle (upperLeviLatticeInput _ radicalLatticeFirst)] at h
  have hinv : ((SpecialLinearGroup.toGL g)⁻¹ : GeneralLinearGroup (Fin 2) ℤ).val =
      ((g⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← map_inv]
    rfl
  have hdet := (g⁻¹).property
  rw [Matrix.det_fin_two] at hdet
  have hone : ((upperLeviLatticeInput (SpecialLinearGroup.toGL g) radicalLatticeFirst).toAdd.1 *
        (upperLeviLatticeInput (SpecialLinearGroup.toGL g) radicalLatticeSecond).toAdd.2 -
      (upperLeviLatticeInput (SpecialLinearGroup.toGL g) radicalLatticeFirst).toAdd.2 *
        (upperLeviLatticeInput (SpecialLinearGroup.toGL g) radicalLatticeSecond).toAdd.1) = 1 := by
    simp only [upperLeviLatticeInput, radicalLatticeFirst, radicalLatticeSecond, MonoidHom.coe_mk,
      OneHom.coe_mk, toAdd_ofAdd, hinv, mul_one, mul_zero, add_zero, zero_add]
    linear_combination hdet
  rw [hone, one_smul] at h
  exact h

/-- **For even `n > 0` the projected alternation vanishes.** -/
theorem alternationT_eq_zero (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRepT n χ)) :
    alternationT n χ cycle radicalLatticeFirst radicalLatticeSecond = 0 := by
  have hmem : alternationT n χ cycle radicalLatticeFirst radicalLatticeSecond ∈
      ModularH1.fixedSpace (ModularSymDimension.symRep n 0) ModularGroup.S ⊓
        ModularH1.fixedSpace (ModularSymDimension.symRep n 0) modularOrderSix :=
    (ModularH1.mem_inf_fixed_iff (ModularSymDimension.symRep n 0) _).mpr
      (alternationT_modular_fixed n χ hχ cycle)
  rw [ModularSymDimension.inf_fixed_eq_bot hn 0] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

/-- Every twisted identity-plane two-cocycle restricts to a coboundary on the radical (`n > 0`). -/
theorem twoCocycle_restriction_zeroT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRepT n χ)) :
    groupCohomology.H2π (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))
      (twoCocycleRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ) cycle) =
        0 :=
  (radicalTwoCocycle_H2_zero_iffT n χ hn _).mpr (alternationT_eq_zero n χ hχ hn cycle)

theorem H2_restriction_zeroT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (cohomology : groupCohomology.H2 (identityPlaneCoefficientRepT n χ)) :
    twoCohomologyRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)
      cohomology = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective (identityPlaneCoefficientRepT n χ) cohomology
  rw [twoCohomologyRestriction_apply]
  exact twoCocycle_restriction_zeroT n χ hχ hn cycle

/-- `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁰) = 0` for even `n`. -/
theorem binaryH1_eq_zeroT (n : ℕ) (heven : Even n)
    (x : groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0)) : x = 0 :=
  IdentityPlaneEven.arithmeticH1_eq_zero_of_odd (n + 1) heven.add_one 0 x

/-- **`H²(Λ₀, V_χ) = 0` for even `n > 0`** (group cohomology). -/
theorem groupH2_eq_zeroT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (heven : Even n)
    (cohomology : groupCohomology.H2 (identityPlaneCoefficientRepT n χ)) : cohomology = 0 := by
  have hker := H2_restriction_zeroT n χ hχ hn cohomology
  have hedge : identityPlaneBinaryEdgeT n χ hχ ⟨cohomology, hker⟩ = identityPlaneBinaryEdgeT n χ hχ 0 :=
    (binaryH1_eq_zeroT n heven _).trans (binaryH1_eq_zeroT n heven _).symm
  exact congrArg Subtype.val (identityPlaneBinaryEdgeT_injective n χ hχ hedge)

/-- **The ambient homogeneous `H²(Λ₀, V_χ)` vanishes for even `n > 0`.** -/
theorem ambientH2_eq_zeroT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (heven : Even n)
    (x : H2 (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent n χ)) : x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change classOf (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
    (rationalCoefficientComponent n χ) C = 0
  rw [classOf_eq_zero_iff]
  exact (ambientCocycle_H2_zero_iff _ _ C).mp (groupH2_eq_zeroT n χ hχ hn heven _)

open CuspReduction

/-- **The local cohomology at the identity-plane cusp vanishes for even `n > 0`** (sign-twisted). -/
theorem cuspH2_identityPlane_eq_zeroT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (heven : Even n)
    (x : CuspH2 n χ .plane false) : x = 0 :=
  ambientH2_eq_zeroT n χ hχ hn heven x

theorem cuspH2_identityPlane_subsingletonT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (heven : Even n) :
    Subsingleton (CuspH2 n χ .plane false) :=
  ⟨fun x y => (cuspH2_identityPlane_eq_zeroT n χ hχ hn heven x).trans
    (cuspH2_identityPlane_eq_zeroT n χ hχ hn heven y).symm⟩

/-- For even `n > 0` the local joint generalized eigenspace at the identity-plane cusp is zero. -/
theorem localJoint_identityPlane_eq_botT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (heven : Even n)
    (c : HeckeCorrespondence → ℂ) : localJoint n χ c .plane false = ⊥ := by
  rw [eq_bot_iff]
  intro x _
  rw [Submodule.mem_bot]
  exact cuspH2_identityPlane_eq_zeroT n χ hχ hn heven x

end TernaryPeriodPolynomials.Twisted
