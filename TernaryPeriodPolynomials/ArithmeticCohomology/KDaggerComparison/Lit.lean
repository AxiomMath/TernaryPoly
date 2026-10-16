module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CuspRestriction
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.ZeroFlagsPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineLevelDescent

@[expose] public section


/-!
# `K†` comparison, CMP-1: the literal `Γ(N)` class of a `K†`-class

`litClass N h3 hN n : H²(K†, E_n) → H²(Γ(N), E_n)` is the restriction to `Γ ∩ Γ(N) ≅ Γ(N)` (homogeneous model, then the `principalIso`).
`classPrincipal_litClass`: the transport `classPrincipal` inverts it, so it is the restriction map read in Mathlib's `H²`.
`lineH2Equiv_res_classPrincipal`: the line analogue of the `planeH2Equiv_res_classPrincipal` (restriction to the line group).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

/-- **The literal class of a `K†`-class** (CMP-1, one direction). -/
def litClass : H2 rationalLevel (rationalCoefficientComponent n trivialCharacter) →ₗ[ℂ]
    groupCohomology.H2 (gammaRep (gammaN N) n) :=
  (principalIso N h3 n hN).inv.hom ∘ₗ
    ((bridge (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N)).toLinearMap ∘ₗ
      resH2 (rationalCoefficientComponent n trivialCharacter) (levelPrincipal_le N))

omit [NeZero N] in
theorem classPrincipal_litClass (a : H2 rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    classPrincipal N h3 n hN (litClass N h3 hN n a) =
      resH2 (rationalCoefficientComponent n trivialCharacter) (levelPrincipal_le N) a := by
  unfold classPrincipal litClass
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have h := congrArg (fun φ => φ.hom
    (bridge (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N)
      (resH2 (rationalCoefficientComponent n trivialCharacter) (levelPrincipal_le N) a)))
    (principalIso N h3 n hN).inv_hom_id
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  rw [h]
  exact LinearEquiv.symm_apply_apply _ _

/-- `litClass` with the codomain written as the literal `Γ(N)` module of Prop C.5 (`gammaRep (gammaN N) n = gammaNRepAll N n`). -/
def litAll : H2 rationalLevel (rationalCoefficientComponent n trivialCharacter) →ₗ[ℂ]
    groupCohomology.H2 (gammaNRepAll N n) := litClass N h3 hN n

omit [NeZero N] in
theorem classPrincipal_litAll (a : H2 rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    classPrincipal N h3 n hN (litAll N h3 hN n a) =
      resH2 (rationalCoefficientComponent n trivialCharacter) (levelPrincipal_le N) a :=
  classPrincipal_litClass N h3 hN n a

omit [NeZero N] in
theorem rPlane_eq_resAtC (h : SL(3, ℤ)) : rPlane N n h = resAtC N h n := by
  unfold rPlane resAtC twoCohomologyRestriction
  rfl

omit [NeZero N] in
theorem lineH2Equiv_res_classPrincipal (h : SL(3, ℤ)) (x : groupCohomology.H2 (gammaRep (gammaN N) n)) :
    lineH2Equiv N h3 h n trivialCharacter hN
        (resH2 (rationalCoefficientComponent n trivialCharacter)
          (fixedPointLevel_le_self (levelPrincipal N) (lineFlagAt h)) (classPrincipal N h3 n hN x)) =
      rLine N n h x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    unfold lineH2Equiv
    rw [LinearEquiv.trans_apply, ← bridge_res]
    have hb : bridge (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N)
        (classPrincipal N h3 n hN (groupCohomology.H2π (gammaRep (gammaN N) n) c)) =
        (principalIso N h3 n hN).hom.hom (groupCohomology.H2π (gammaRep (gammaN N) n) c) := by
      unfold classPrincipal
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [hb]
    unfold principalIso
    simp only [groupCohomology.mapIso_hom]
    rw [groupCohomology.H2π_comp_map_apply]
    rw [groupCohomology.H2π_comp_map_apply]
    refine Eq.trans (EdgeNat.h2Map_π (lineEmbed N h3 h) (lineRep N h n trivialCharacter) (lineFaceRep N h n)
      LinearMap.id (lineEmbed_hT N h3 h n trivialCharacter) _) ?_
    refine Eq.trans ?_ (twoCohomologyRestriction_apply
      (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp)) (gammaNRepAll N n) c).symm
    congr 1
    apply Subtype.ext
    funext p
    obtain ⟨a, b⟩ := p
    have hE : ∀ a : ↥(gammaNQAt N h), (principalEquiv N h3 hN).symm
        (Subgroup.inclusion (fixedPointLevel_le_self (levelPrincipal N) (lineFlagAt h)) (lineEmbed N h3 h a)) =
        Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp) a := by
      intro a
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      change (lineEmbed N h3 h a).1 = (Matrix.SpecialLinearGroup.mapGL ℚ a.1)
      rw [lineEmbed_val]
    change c.1 ((principalEquiv N h3 hN).symm
        (Subgroup.inclusion (fixedPointLevel_le_self (levelPrincipal N) (lineFlagAt h)) (lineEmbed N h3 h a)),
      (principalEquiv N h3 hN).symm
        (Subgroup.inclusion (fixedPointLevel_le_self (levelPrincipal N) (lineFlagAt h)) (lineEmbed N h3 h b))) =
      c.1 (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp) a,
        Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N h hp) b)
    rw [hE, hE]


end TernaryPeriodPolynomials.Argument.KDaggerComparison
