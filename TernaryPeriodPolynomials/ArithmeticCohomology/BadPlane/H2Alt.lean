module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.RightEdge.Cohomology

@[expose] public section


/-!
# `H²(N_P, E_n)` of the bad-plane radical: the alternation coordinate (injectivity and Levi equivariance)

For the paper's objects at `K†` (`P_0` the bad-plane stabilizer, `N_P = ⟨U₁₃, U₂₃⟩ = RadicalLattice`, `E_n = identityPlaneCoefficientRep n`, coefficients ℂ) and `n > 0`:
`altH2 : H²(N_P, E_n) → Sym^n(ℂ²)`, `[z] ↦ π(z(e₁,e₂) - z(e₂,e₁))` (`π` the restriction `z = 0`), is well defined and injective (`altH2_injective`, from
`SphericalDetection.upperRadicalTwoCocycle_H2_zero_iff`), and Levi equivariant (`altH2_levi`): the Levi action `splitRadicalH2Action` of `l ∈ GL₂(ℤ)` is carried to the action
`Binary.homogeneousAction n (-2)`, i.e. `det⁻² Sym^n` (the inverse conjugation `splitRadicalInput = upperLeviLatticeInput l` has determinant `det l⁻¹`, and the restriction `π`
intertwines `E_n` with `det⁻¹ Sym^n`).  Surjectivity is in `BadPlaneH2Rat`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.IdentityPlaneEven
open TernaryPeriodPolynomials.Argument.RightEdge
open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Identities.BadPlane

variable (n : ℕ)

/-- The projected alternation `π (z(u,v) - z(v,u))` of a two-cocycle of the radical lattice. -/
def altB (z : groupCohomology.cocycles₂ (upperRadicalLatticeRep n)) (u v : RadicalLattice) :
    Binary.HomogeneousPoly n :=
  binaryHomogeneousRestrict n (z (u, v) - z (v, u))

theorem altB_mul (z : groupCohomology.cocycles₂ (upperRadicalLatticeRep n)) (x y w : RadicalLattice) :
    altB n z (x * y) w = altB n z x w + altB n z y w :=
  projected_alternation_mul (MonoidHom.id RadicalLattice) (upperRadicalLatticeRep n)
    (binaryHomogeneousRestrict n) (binaryHomogeneousRestrict_upperLattice n) z x y w

theorem altB_anti (z : groupCohomology.cocycles₂ (upperRadicalLatticeRep n)) (x y : RadicalLattice) :
    altB n z x y = -altB n z y x := by
  exact map_sub_eq_neg_map_sub (binaryHomogeneousRestrict n) _ _

theorem altB_diag (z : groupCohomology.cocycles₂ (upperRadicalLatticeRep n)) (x : RadicalLattice) :
    altB n z x x = 0 := by
  unfold altB
  rw [sub_self]
  exact LinearMap.map_zero _

theorem altB_eq_det (z : groupCohomology.cocycles₂ (upperRadicalLatticeRep n)) (u v : RadicalLattice) :
    altB n z u v = (u.toAdd.1 * v.toAdd.2 - u.toAdd.2 * v.toAdd.1) • altB n z radicalLatticeFirst radicalLatticeSecond :=
  alternating_eq_det (altB n z) (altB_mul n z) (altB_anti n z) (altB_diag n z) u v

/-- The alternation map `H²`-coordinate on cocycles. -/
def altF : groupCohomology.cocycles₂ (upperRadicalLatticeRep n) →ₗ[ℂ] Binary.HomogeneousPoly n :=
  (binaryHomogeneousRestrict n).comp (latticeTwoCocycleAlternation (upperRadicalLatticeRep n))

theorem altF_apply (z : groupCohomology.cocycles₂ (upperRadicalLatticeRep n)) :
    altF n z = altB n z radicalLatticeFirst radicalLatticeSecond := rfl

theorem altF_eq_zero_iff (hn : 0 < n) (z : groupCohomology.cocycles₂ (upperRadicalLatticeRep n)) :
    groupCohomology.H2π (upperRadicalLatticeRep n) z = 0 ↔ altF n z = 0 :=
  upperRadicalTwoCocycle_H2_zero_iff n hn z

/-- The class map `H2π` as a linear map. -/
abbrev H2pi : groupCohomology.cocycles₂ (upperRadicalLatticeRep n) →ₗ[ℂ]
    groupCohomology.H2 (upperRadicalLatticeRep n) :=
  (groupCohomology.H2π (upperRadicalLatticeRep n)).hom

theorem H2pi_surjective : Function.Surjective (H2pi n) := twoCocycle_H2_surjective _

theorem ker_H2pi_le (hn : 0 < n) : LinearMap.ker (H2pi n) ≤ LinearMap.ker (altF n) := by
  intro z hz
  exact (altF_eq_zero_iff n hn z).mp hz

/-- The coordinate `H²(N_P, E_n) → Sym^n(ℂ²)` of a class: the projected alternation `π(z(e₁,e₂) - z(e₂,e₁))`. -/
def altH2 (hn : 0 < n) : groupCohomology.H2 (upperRadicalLatticeRep n) →ₗ[ℂ] Binary.HomogeneousPoly n :=
  (Submodule.liftQ (LinearMap.ker (H2pi n)) (altF n) (ker_H2pi_le n hn)).comp
    (LinearMap.quotKerEquivOfSurjective (H2pi n) (H2pi_surjective n)).symm.toLinearMap

theorem altH2_H2pi (hn : 0 < n) (z : groupCohomology.cocycles₂ (upperRadicalLatticeRep n)) :
    altH2 n hn (H2pi n z) = altF n z := by
  have h := (LinearMap.quotKerEquivOfSurjective (H2pi n) (H2pi_surjective n)).symm_apply_apply
    (Submodule.Quotient.mk z)
  unfold altH2
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have h2 : (LinearMap.quotKerEquivOfSurjective (H2pi n) (H2pi_surjective n)).symm (H2pi n z) =
      Submodule.Quotient.mk z := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [h2]
  rfl

theorem altH2_injective (hn : 0 < n) : Function.Injective (altH2 n hn) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z, rfl⟩ := H2pi_surjective n x
  rw [altH2_H2pi n hn] at hx
  exact (altF_eq_zero_iff n hn z).mpr hx

open TernaryPeriodPolynomials.Argument.RightEdge in
theorem radicalInput_eq (l : GL (Fin 2) ℤ) :
    splitRadicalInput identityPlaneSplitting l = upperLeviLatticeInput l := by
  apply MonoidHom.ext
  intro a
  apply identityPlaneRadicalInclusion_injective
  have h1 := splitRadicalInput_commute identityPlaneSplitting l a
  have h2 := identityPlaneLevi_conjugates l a
  change identityPlaneRadicalInclusion a * identityPlaneLeviSection l =
    identityPlaneLeviSection l * identityPlaneRadicalInclusion (splitRadicalInput identityPlaneSplitting l a) at h1
  rw [← h2, mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]

theorem det_upperLevi (l : GL (Fin 2) ℤ) :
    ((upperLeviLatticeInput l radicalLatticeFirst).toAdd.1 * (upperLeviLatticeInput l radicalLatticeSecond).toAdd.2 -
      (upperLeviLatticeInput l radicalLatticeFirst).toAdd.2 * (upperLeviLatticeInput l radicalLatticeSecond).toAdd.1) =
      ((l⁻¹ : GL (Fin 2) ℤ).val.det) := by
  simp only [upperLeviLatticeInput, radicalLatticeFirst, radicalLatticeSecond, MonoidHom.coe_mk,
    OneHom.coe_mk, toAdd_ofAdd, Matrix.det_fin_two]
  ring

theorem homAction_twist (A : Binary.GL2) (a : Binary.HomogeneousPoly n) :
    Binary.homogeneousAction n (-2) A a =
      (((GeneralLinearGroup.det A : ℂˣ) : ℂ))⁻¹ • Binary.homogeneousAction n (-1) A a := by
  apply Subtype.ext
  change Binary.action (-2) A a.val = _
  rw [Submodule.coe_smul]
  change Binary.action (-2) A a.val = ((GeneralLinearGroup.det A : ℂˣ) : ℂ)⁻¹ • Binary.action (-1) A a.val
  rw [Binary.action_apply, Binary.action_apply, smul_smul]
  congr 1
  change ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ (-2 : ℤ) =
    ((GeneralLinearGroup.det A : ℂˣ) : ℂ)⁻¹ * ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ (-1 : ℤ)
  have hne : ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_one, zpow_two, mul_inv]

theorem det_cast (l : GL (Fin 2) ℤ) :
    (((l⁻¹ : GL (Fin 2) ℤ).val.det : ℤ) : ℂ) = (((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) l) :
      ℂˣ) : ℂ))⁻¹ := by
  have h : (l⁻¹ : GL (Fin 2) ℤ).val.det * l.val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  have hc : (((l⁻¹ : GL (Fin 2) ℤ).val.det : ℤ) : ℂ) * ((l.val.det : ℤ) : ℂ) = 1 := by exact_mod_cast h
  have hd : ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) l) : ℂˣ) : ℂ) =
      ((l.val.det : ℤ) : ℂ) := by
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact (RingHom.map_det (Int.castRingHom ℂ) l.val).symm
  rw [hd]
  exact eq_inv_of_mul_eq_one_left hc

theorem altF_levi_aux (l : GL (Fin 2) ℤ)
    (z w : groupCohomology.cocycles₂ (upperRadicalLatticeRep n))
    (hw : ∀ a b : RadicalLattice, w (a, b) = (identityPlaneCoefficientRep n).ρ (identityPlaneSplitting l)
      (z (upperLeviLatticeInput l a, upperLeviLatticeInput l b))) :
    altF n w = Binary.homogeneousAction n (-2) (GeneralLinearGroup.map (Int.castRingHom ℂ) l) (altF n z) := by
  have e1 : altF n w = binaryHomogeneousRestrict n ((identityPlaneCoefficientRep n).ρ (identityPlaneSplitting l)
      (z (upperLeviLatticeInput l radicalLatticeFirst, upperLeviLatticeInput l radicalLatticeSecond) -
        z (upperLeviLatticeInput l radicalLatticeSecond, upperLeviLatticeInput l radicalLatticeFirst))) := by
    rw [altF_apply]
    unfold altB
    rw [hw, hw]
    exact congrArg (binaryHomogeneousRestrict n) (LinearMap.map_sub _ _ _).symm
  have e2 := binaryHomogeneousRestrict_arithmeticLevi n l
    (z (upperLeviLatticeInput l radicalLatticeFirst, upperLeviLatticeInput l radicalLatticeSecond) -
        z (upperLeviLatticeInput l radicalLatticeSecond, upperLeviLatticeInput l radicalLatticeFirst))
  have e3 : binaryHomogeneousRestrict n (z (upperLeviLatticeInput l radicalLatticeFirst, upperLeviLatticeInput l radicalLatticeSecond) -
        z (upperLeviLatticeInput l radicalLatticeSecond, upperLeviLatticeInput l radicalLatticeFirst)) =
      altB n z (upperLeviLatticeInput l radicalLatticeFirst) (upperLeviLatticeInput l radicalLatticeSecond) := rfl
  rw [e1]
  refine e2.trans ?_
  rw [e3, altB_eq_det n z, det_upperLevi, ← altF_apply, homAction_twist, map_zsmul, ← det_cast l]
  exact (Int.cast_smul_eq_zsmul ℂ _ _).symm

open TernaryPeriodPolynomials.Argument.RightEdge in
/-- **The coordinate `altH2` is equivariant**: the Levi action on `H²(N_P, E_n)` becomes the action on `Sym^n` twisted by `det⁻²`. -/
theorem altH2_levi (hn : 0 < n) (l : GL (Fin 2) ℤ)
    (x : groupCohomology.H2 (Rep.res identityPlaneExtension.inl (identityPlaneCoefficientRep n))) :
    altH2 n hn (splitRadicalH2Action identityPlaneSplitting (identityPlaneCoefficientRep n) l x) =
      Binary.homogeneousAction n (-2) (GeneralLinearGroup.map (Int.castRingHom ℂ) l) (altH2 n hn x) := by
  obtain ⟨z, hz⟩ := H2pi_surjective n x
  let z' : groupCohomology.cocycles₂ (Rep.res identityPlaneExtension.inl (identityPlaneCoefficientRep n)) := z
  have hx : x = groupCohomology.H2π (Rep.res identityPlaneExtension.inl (identityPlaneCoefficientRep n)) z' :=
    hz.symm
  have h1 : ∀ w : groupCohomology.cocycles₂ (Rep.res identityPlaneExtension.inl (identityPlaneCoefficientRep n)),
      altH2 n hn (groupCohomology.H2π (Rep.res identityPlaneExtension.inl (identityPlaneCoefficientRep n)) w) =
        altF n w := fun w => altH2_H2pi n hn w
  rw [hx, splitRadicalH2Action_π, h1, h1]
  exact altF_levi_aux n l z _ (fun a b => by
    rw [← radicalInput_eq l]
    exact splitRadicalH2Action_cocycle identityPlaneSplitting (identityPlaneCoefficientRep n) l z' a b)

end TernaryPeriodPolynomials.Argument.Identities.BadPlane
