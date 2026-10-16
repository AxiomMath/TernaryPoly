module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CuspRestriction
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.TransferBack

@[expose] public section


/-!
# M4: the `K†` plane coordinate of `classK x` in terms of the per-cusp restrictions of `x`

Formalized by Claude Sonnet 5.5.

* `isConj_stab_principal`, `res_actH2_conj`: conjugation naturality, `res_{Γ_F∩Γ(N)}(q • y) = conj_q(res_{Γ_{q⁻¹F}∩Γ(N)} y)`.
* `seedAt`, `res_classPrincipal_eq_seedAt`: the restriction of the transported class to `Γ_{planeFlagAt h} ∩ Γ(N)` is `resAtC N h n x` read on the homogeneous side.
* **`planeCoordinate_formula`**: `res_{Γ_F}(classK x) = |K†/Γ(N)|⁻¹ ∑_q tr_{Γ_F∩Γ(N)}^{Γ_F}( conj_q (seed data of x at the plane q⁻¹F) )`.
* `planeCoordinate_component`: the Shapiro component of `(globalCoordinates c).1` at `F` is `res_{Γ_F}(classK x)`.
* **`planeCoordinate_congr`**: classes of `Γ(N)` with the same restrictions to all plane groups `Γ_{h⁻¹Ph}` have the same `K†` plane coordinate.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

open TernaryPeriodPolynomials.Argument.FormSeriesModel TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.ConvergenceC4

section Conj

variable (N : ℕ)

theorem isConj_stab_principal {q : RationalGL3} (hq : q ∈ rationalLevel) {F F' : Flags .plane}
    (hF : F' = q⁻¹ • F) :
    IsConj (fixedPointLevel (levelPrincipal N) F') (fixedPointLevel (levelPrincipal N) F) q := by
  intro x
  subst hF
  constructor
  · rintro ⟨hxM, hxF⟩
    refine ⟨levelPrincipal_norm N q hq x hxM, ?_⟩
    apply MulAction.mem_stabilizer_iff.mpr
    have := MulAction.mem_stabilizer_iff.mp hxF
    rw [mul_smul, mul_smul, smul_inv_smul, this]
  · rintro ⟨hxM, hxF⟩
    have hxM' : x ∈ levelPrincipal N := by
      have := levelPrincipal_norm N q⁻¹ ((rationalLevel).inv_mem hq) _ hxM
      simpa [mul_assoc] using this
    refine ⟨hxM', ?_⟩
    apply MulAction.mem_stabilizer_iff.mpr
    have h2 := MulAction.mem_stabilizer_iff.mp hxF
    rw [mul_smul, mul_smul, smul_inv_smul] at h2
    exact smul_left_cancel q⁻¹ h2

variable (n : ℕ)

theorem res_actH2_conj {q : RationalGL3} (hq : q ∈ rationalLevel) {F F' : Flags .plane} (hF : F' = q⁻¹ • F)
    (y : H2 (levelPrincipal N) (rationalCoefficientComponent n trivialCharacter)) :
    resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_self (levelPrincipal N) F)
        (actH2 (rationalCoefficientComponent n trivialCharacter) q (levelPrincipal_norm N q hq) y) =
      actH2Conj (rationalCoefficientComponent n trivialCharacter) q (isConj_stab_principal N hq hF)
        (resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_self (levelPrincipal N) F') y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

end Conj

section Formula

variable (N n : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N)

/-- The class `y ∈ H²(Γ_{h⁻¹Ph}, E_n)` read on the homogeneous side at the plane `planeFlagAt h`. -/
def seedAt (h : SL(3, ℤ)) : groupCohomology.H2 (faceRep N h n) →ₗ[ℂ]
    H2 (fixedPointLevel (levelPrincipal N) (planeFlagAt h)) (rationalCoefficientComponent n trivialCharacter) :=
  (planeH2Equiv N h3 h n trivialCharacter hN).symm.toLinearMap

omit [NeZero N] in
theorem res_classPrincipal_eq_seedAt (h : SL(3, ℤ)) (x : groupCohomology.H2 (gammaRep (gammaN N) n)) :
    resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_self (levelPrincipal N) (planeFlagAt h))
        (classPrincipal N h3 n hN x) = seedAt N n h3 hN h (resAtC N h n x) := by
  have := planeH2Equiv_res_classPrincipal N h n h3 hN x
  change _ = (planeH2Equiv N h3 h n trivialCharacter hN).symm _
  rw [← this, LinearEquiv.symm_apply_apply]

/-- **M4, the two non-S6 pieces: Mackey/conjugation formula for the plane coordinate (unconditional).**
For every rational plane `F`, the plane coordinate of `classK x` at `F` is
`|K†/Γ(N)|⁻¹ ∑_q tr_{Γ_F∩Γ(N)}^{Γ_F} ( conj_q ( seed data of x at the plane q⁻¹F ) )`,
where "seed data at the plane `q⁻¹F = h_q⁻¹⟨e₁,e₂⟩`" is `resAtC N h_q n x` (restriction of `x` to `Γ_{h_q⁻¹Ph_q}`) read on the
homogeneous side (`seedAt`).  Thus the plane coordinate is determined by the per-cusp restrictions of `x` (S6's M1/M2 values). -/
theorem planeCoordinate_formula (x : groupCohomology.H2 (gammaRep (gammaN N) n)) (F : Flags .plane) :
    resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_level F) (classK N h3 hN n x) =
      ((Fintype.card (↥rationalLevel ⧸ (levelPrincipal N).subgroupOf rationalLevel) : ℂ)⁻¹) •
        ∑ q : ↥rationalLevel ⧸ (levelPrincipal N).subgroupOf rationalLevel,
          trLevel (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N) (levelPrincipal_le N)
            (levelPrincipal_norm N) F
            (actH2Conj (rationalCoefficientComponent n trivialCharacter) ((Quotient.out q : ↥rationalLevel) : RationalGL3)
              (isConj_stab_principal N (Quotient.out q).2
                (Classical.choose_spec (planeFlagAt_surjective (((Quotient.out q : ↥rationalLevel) : RationalGL3)⁻¹ • F))))
              (seedAt N n h3 hN (Classical.choose (planeFlagAt_surjective (((Quotient.out q : ↥rationalLevel) : RationalGL3)⁻¹ • F)))
                (resAtC N (Classical.choose (planeFlagAt_surjective (((Quotient.out q : ↥rationalLevel) : RationalGL3)⁻¹ • F))) n x))) := by
  have hPC := trLevel_resH2 (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N) (levelPrincipal_le N)
    (levelPrincipal_norm N) F
    ((resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_level F)) (classK N h3 hN n x))
  rw [← hPC, res_classK_eq_avg N n h3 hN x F, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  rw [res_actH2_conj N n (Quotient.out q).2 (Classical.choose_spec (planeFlagAt_surjective _)),
    res_classPrincipal_eq_seedAt N n h3 hN]

end Formula

section Shapiro

variable (N n : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N)

/-- **Shapiro components of the plane coordinate.**  The component at the flag `F` of the plane coordinate of a global cocycle representing
`classK x` is the restriction of `classK x` to `Γ_F`. -/
theorem planeCoordinate_component (x : groupCohomology.H2 (gammaRep (gammaN N) n))
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c = classK N h3 hN n x)
    (F : Flags .plane) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F
        (globalCoordinates n trivialCharacter c).1 =
      resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_level F) (classK N h3 hN n x) := by
  rw [← hc]
  rfl

/-- **M4, determination of the plane coordinate by the per-cusp restrictions (unconditional).**  Two classes of `Γ(N)` with the same
restrictions to every plane group `Γ_{h⁻¹Ph}` have the same `K†` plane coordinate.  (With `planeCoordinate_formula` and S6's per-cusp
values this reduces M4 to exactly those values.) -/
theorem planeCoordinate_congr (x x' : groupCohomology.H2 (gammaRep (gammaN N) n))
    (hx : ∀ h : SL(3, ℤ), resAtC N h n x = resAtC N h n x')
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c = classK N h3 hN n x)
    (hc' : classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c' = classK N h3 hN n x') :
    (globalCoordinates n trivialCharacter c).1 = (globalCoordinates n trivialCharacter c').1 := by
  rw [← sub_eq_zero]
  refine (eq_zero_iff_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) _).mpr fun F => ?_
  refine (map_sub (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F) _ _).trans
    (sub_eq_zero.mpr ?_)
  have e1 := planeCoordinate_component N n h3 hN x c hc F
  have e2 := planeCoordinate_component N n h3 hN x' c' hc' F
  have f1 := planeCoordinate_formula N n h3 hN x F
  have f2 := planeCoordinate_formula N n h3 hN x' F
  simp only [hx] at f1
  exact e1.trans (f1.trans (f2.symm.trans e2.symm))

end Shapiro

end TernaryPeriodPolynomials.Argument.FormClassK
