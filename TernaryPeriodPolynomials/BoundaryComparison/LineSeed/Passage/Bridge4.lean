module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Bridge3
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Transport
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.ClassFinal

@[expose] public section


/-!
# The glue between the transport formula and the clean-frame bridge (Passage bridge, part 4)

`toH2L_eq_bridge`: the comparison `toH2L` of the good-line stabilizer `Λ₁` with Mathlib's `H²` is the bridge of `LevelTransfer`.  `phiLineAt_clean`: for a transporter `q` of the *clean frame*
(`mapGL ℚ h * q = Π`, `rationalGoodLine`), the pullback along `faceToStd` of the bridge of the restriction of `X` to `Γ_{std} ∩ Γ(N)` is the image under `H²(cleanHom, cleanMor)` of `linePlusRes n X`, so
that `phiLineAt h a` is expressed through `linePlusRes` and the clean-frame comparison (`phiLineAt_eq_clean`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix CategoryTheory groupCohomology
open TernaryPeriodPolynomials.Argument.LevelTransfer

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.LineCoordinates (Λ₁)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c (coeff_mapGL)
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.KDaggerComparison (stdLine faceToStd stdRep faceToStd_hT)

theorem toH2L_eq_bridge (n : ℕ) (X : H2 Λ₁ (ρn n)) : toH2L n X = bridge (ρn n) Λ₁ X := by
  obtain ⟨C, rfl⟩ := Submodule.Quotient.mk_surjective _ X
  rw [bridge_mk]
  change (H2π (goodLineCoefficientRep n)).hom (ambientCocycleToGroup Λ₁ (ρn n) C) = _
  congr 1
  apply Subtype.ext
  funext p
  exact (bridgeCocycle_apply (ρn n) Λ₁ C p.1 p.2).symm



section Generic

theorem mapCocycles₂_apply_edgeNat {G H : Type} [Group G] [Group H] (α : H →* G) (A : Rep ℂ G) (B : Rep ℂ H)
    (T : A →ₗ[ℂ] B) (hT : ∀ (g : H) (v : A), T (A.ρ (α g) v) = B.ρ g (T v)) (z : cocycles₂ A) (a b : H) :
    (mapCocycles₂ α (EdgeNat.comparison α A B T hT) z).1 (a, b) = T (z.1 (α a, α b)) := rfl

theorem mapCocycles₂_apply_hom {G H : Type} [Group G] [Group H] (α : H →* G) (A : Rep ℂ G) (B : Rep ℂ H)
    (φ : Rep.res α A ⟶ B) (z : cocycles₂ A) (a b : H) :
    (mapCocycles₂ α φ z).1 (a, b) = φ.hom (z.1 (α a, α b)) := rfl

theorem ambientCocycleToGroup_apply' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (Γ : Subgroup G)
    (ρ : Representation ℂ G V) (C : Homogeneous.cocycles Γ ρ) (a b : Γ) :
    (ambientCocycleToGroup Γ ρ C).1 (a, b) = C.val.val ![1, (a : G), (a : G) * (b : G)] := rfl

end Generic

section CleanMorHom

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (h : SL(3, ℤ)) (n : ℕ)

theorem cleanMor_hom (v : HomogeneousPoly n) : (Rep.Hom.hom (cleanMor N h3 h n)) v = cleanLin h n v := rfl

end CleanMorHom

section Glue

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (n : ℕ) (h : SL(3, ℤ)) {q : RationalGL3} (hq : q ∈ rationalLevel)
  (hF : q • stdLine = lineFlagAt h) (hclean : Matrix.SpecialLinearGroup.mapGL ℚ h * q = rationalGoodLine)

omit [NeZero N] in
include hclean in
theorem q_eq_clean : q = Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * rationalGoodLine := by
  rw [map_inv]
  exact (inv_mul_eq_iff_eq_mul.mpr hclean.symm).symm

omit [NeZero N] in
include hclean in
theorem faceToStd_val_clean (p : ↥(gammaNQAt N h)) :
    ((faceToStd N h3 h hq hF p).1 : RationalGL3) =
      (((cleanHom N h3 h p : Lam1Plus) : Lam1) : RationalGL3) := by
  have hq' := q_eq_clean h hclean
  change q⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ p.1 * q =
    rationalGoodLine * Matrix.SpecialLinearGroup.mapGL ℚ (h * p.1 * h⁻¹) * rationalGoodLine
  have hs : rationalGoodLine⁻¹ = rationalGoodLine := inv_eq_of_mul_eq_one_right rationalGoodLine_sq
  rw [hq']
  simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, hs, mul_assoc]

omit [NeZero N] in
include hclean in
theorem rho_q_clean : rationalCoefficientComponent n trivialCharacter q =
    (cleanLin h n : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n) := by
  have hq' := q_eq_clean h hclean
  rw [hq', map_mul, coeff_mapGL]
  have hpi : rationalCoefficientComponent n trivialCharacter rationalGoodLine = pivotT n := by
    change componentCharacter trivialCharacter _ • GeneralEisenstein.realCoefficient n _ = _
    have h1 : componentCharacter trivialCharacter
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) rationalGoodLine) = 1 := rfl
    rw [h1, one_smul]
    rfl
  rw [hpi]
  rfl


include hclean in
/-- **Clean-frame form of S3's transport formula.** -/
theorem phiLineAt_clean (X : H2 Λ₁ (ρn n)) :
    EdgeNat.h2Map (faceToStd N h3 h hq hF) (stdRep N n) (lineFaceRep N h n)
        (rationalCoefficientComponent n trivialCharacter q) (faceToStd_hT N n h3 h hq hF)
        (bridge (rationalCoefficientComponent n trivialCharacter)
          (fixedPointLevel (levelPrincipal N) stdLine)
          (resPrincipal N stdLine (rationalCoefficientComponent n trivialCharacter) X)) =
      (groupCohomology.map (cleanHom N h3 h) (cleanMor N h3 h n) 2).hom (linePlusRes n X) := by
  obtain ⟨C, rfl⟩ := Submodule.Quotient.mk_surjective _ X
  have e1 : resPrincipal N stdLine (rationalCoefficientComponent n trivialCharacter)
      (Submodule.Quotient.mk C) = Submodule.Quotient.mk (cocyclesRes (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_mono_level (levelPrincipal N) (levelPrincipal_le N) stdLine) C) := rfl
  have e2 : linePlusRes n (Submodule.Quotient.mk C) = H2π (linePlusRep n)
      (twoCocycleRestriction Lam1Plus.subtype (goodLineCoefficientRep n) (ambientCocycleToGroup Λ₁ (ρn n) C)) := by
    change twoCohomologyRestriction Lam1Plus.subtype (goodLineCoefficientRep n) (toH2L n (Submodule.Quotient.mk C)) = _
    erw [toH2L_classOf, twoCohomologyRestriction_apply]
  erw [e1, bridge_mk, e2]
  refine (EdgeNat.h2Map_π (faceToStd N h3 h hq hF) (stdRep N n) (lineFaceRep N h n)
    (rationalCoefficientComponent n trivialCharacter q) (faceToStd_hT N n h3 h hq hF) _).trans ?_
  refine Eq.trans ?_ (groupCohomology.H2π_comp_map_apply (cleanHom N h3 h) (cleanMor N h3 h n) _).symm
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  have hrho := rho_q_clean n h hclean
  have fa := faceToStd_val_clean N h3 h hq hF hclean a
  have fab := faceToStd_val_clean N h3 h hq hF hclean (a * b)
  rw [map_mul] at fab
  have l1 := (mapCocycles₂_apply_edgeNat (faceToStd N h3 h hq hF) (stdRep N n) (lineFaceRep N h n)
      (rationalCoefficientComponent n trivialCharacter q) (faceToStd_hT N n h3 h hq hF)
      (bridgeCocycle (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel (levelPrincipal N) stdLine)
        (cocyclesRes (rationalCoefficientComponent n trivialCharacter)
          (fixedPointLevel_mono_level (levelPrincipal N) (levelPrincipal_le N) stdLine) C)) a b).trans
    (congrArg (rationalCoefficientComponent n trivialCharacter q)
      (bridgeCocycle_apply (rationalCoefficientComponent n trivialCharacter) _ _ _ _))
  have r1 := mapCocycles₂_apply_hom (cleanHom N h3 h) (linePlusRep n) (lineFaceRep N h n) (cleanMor N h3 h n)
    (twoCocycleRestriction Lam1Plus.subtype (goodLineCoefficientRep n) (ambientCocycleToGroup Λ₁ (ρn n) C)) a b
  refine l1.trans (Eq.trans ?_ r1.symm)
  have hv : (![1, ((faceToStd N h3 h hq hF a : ↥(fixedPointLevel (levelPrincipal N) stdLine)) : RationalGL3),
      ((faceToStd N h3 h hq hF a * faceToStd N h3 h hq hF b : ↥(fixedPointLevel (levelPrincipal N) stdLine)) :
        RationalGL3)] : Fin 3 → RationalGL3) =
      ![1, (((cleanHom N h3 h a : Lam1Plus) : Lam1) : RationalGL3),
        (((cleanHom N h3 h a : Lam1Plus) : Lam1) : RationalGL3) * (((cleanHom N h3 h b : Lam1Plus) : Lam1) : RationalGL3)] := by
    have fab' : ((faceToStd N h3 h hq hF a * faceToStd N h3 h hq hF b : ↥(fixedPointLevel (levelPrincipal N) stdLine)) :
        RationalGL3) = (((cleanHom N h3 h a : Lam1Plus) : Lam1) : RationalGL3) *
          (((cleanHom N h3 h b : Lam1Plus) : Lam1) : RationalGL3) := by
      rw [map_mul] at fab
      exact fab
    rw [fa, fab']
  have r3 : (Rep.Hom.hom (cleanMor N h3 h n))
      ((twoCocycleRestriction Lam1Plus.subtype (goodLineCoefficientRep n) (ambientCocycleToGroup Λ₁ (ρn n) C)).1
        (cleanHom N h3 h a, cleanHom N h3 h b)) =
      cleanLin h n (C.val.val ![1, (((cleanHom N h3 h a : Lam1Plus) : Lam1) : RationalGL3),
        (((cleanHom N h3 h a : Lam1Plus) : Lam1) : RationalGL3) * (((cleanHom N h3 h b : Lam1Plus) : Lam1) : RationalGL3)]) :=
    (cleanMor_hom N h3 h n _).trans (congrArg (cleanLin h n)
      ((twoCocycleRestriction_apply Lam1Plus.subtype (goodLineCoefficientRep n) _ _ _).trans
        (ambientCocycleToGroup_apply' Λ₁ (ρn n) C _ _)))
  refine Eq.trans ?_ r3.symm
  rw [← hv, ← hrho]
  rfl

end Glue

end TernaryPeriodPolynomials.Argument.LineSeed
