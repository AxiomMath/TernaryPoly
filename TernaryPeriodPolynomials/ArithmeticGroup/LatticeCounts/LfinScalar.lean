module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LfinBlockMulti
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitDetNorm

@[expose] public section


/-!
# Scalar split of the global determinant (route (b), step (B1b))

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

Restriction: the base point `g_f : GL₂(𝔸_f)` is integral at every
place, including place `3`; this enters only through `LfinBlockMulti.block_multi`.

For `X : GL₂(𝔸_f)` whose local values are `blk2 (P_w)` on `S` and `1` off `S`, the global determinant is
the single-place product `∏_{w ∈ S} finiteAtPlaceUnit w (det_w X)`. Hence
`normPower(det(X · g_f))` is the product over `S` of the local exponentials
`exp(b · log ‖det_w X‖)` times `normPower(det g_f)`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix PadicInt
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSection
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitDetNorm
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinFactor
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (finiteCompletionPadicEquiv finiteAtPlaceUnit finiteAtPlaceUnit_same finiteAtPlaceUnit_away
    finiteAtPadicUnit)

open Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LfinScalar

section Single

/-- `normPower` of the place-`v` embedding of a unit is `exp(b · log ‖pe v u‖)`. -/
theorem normPower_finiteAtPlaceUnit (v : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (u : (v.adicCompletion ℚ)ˣ) (b : ℂ) :
    normPower (Norm.finiteAdeleUnit (finiteAtPlaceUnit v u)) b =
      Complex.exp (b * (Real.log ‖pe v u.val‖ : ℂ)) := by
  rw [finiteAtPlaceUnit_eq_padic v u, norm_finiteAdeleUnit_eq]
  exact TernaryPeriodPolynomials.SphericalDetection.Helpers.normPower_finiteAtPadicUnit v _ b

end Single

section Product

/-- `normPower` of a finite product of single-place units is the product of the local exponentials. -/
theorem normPower_prod_finiteAtPlaceUnit (S : Finset FinitePlace)
    (d : ∀ w : FinitePlace, (w.adicCompletion ℚ)ˣ) (b : ℂ) :
    normPower (Norm.finiteAdeleUnit (∏ w ∈ S, finiteAtPlaceUnit w (d w))) b =
      ∏ w ∈ S, Complex.exp (b * (Real.log ‖pe w (d w).val‖ : ℂ)) := by
  refine Finset.induction_on S ?_ ?_
  · have h1 : Norm.finiteAdeleUnit (1 : FiniteAdelesˣ) = 1 := Units.ext rfl
    rw [Finset.prod_empty, Finset.prod_empty, h1]
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_one b
  · intro a T ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, finiteAdeleUnit_mul,
      TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_mul,
      normPower_finiteAtPlaceUnit a (d a) b, ih]

end Product

section Det

/-- The determinant of `X` is the product of its single-place determinants over `S`,
provided it is `1` at every place off `S`. -/
theorem det_eq_prod (S : Finset FinitePlace) (X : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (hout : ∀ w : FinitePlace, w ∉ S →
      GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation w) X) = 1) :
    GeneralLinearGroup.det X =
      ∏ w ∈ S, finiteAtPlaceUnit w
        (GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation w) X)) := by
  apply Units.ext
  apply eq_of_eval
  intro p
  have hloc : Units.map (finiteEvaluation p).toMonoidHom (GeneralLinearGroup.det X) =
      GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation p) X) :=
    (TernaryPeriodPolynomials.SphericalDetection.Helpers.generalLinearGroup_det_map
      (finiteEvaluation p) X).symm
  have term : ∀ w ∈ S, Units.map (finiteEvaluation p).toMonoidHom
      (finiteAtPlaceUnit w (GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation w) X))) =
      if w = p then GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation p) X) else 1 := by
    intro w _
    by_cases hw : w = p
    · subst hw
      rw [ite_eq_left rfl, finiteAtPlaceUnit_same]
    · rw [ite_eq_right hw, finiteAtPlaceUnit_away w _ p (Ne.symm hw)]
  have hprod : Units.map (finiteEvaluation p).toMonoidHom
      (∏ w ∈ S, finiteAtPlaceUnit w
        (GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation w) X))) =
      if p ∈ S then GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation p) X) else 1 := by
    rw [map_prod, Finset.prod_congr rfl term]
    simp [Finset.prod_ite_eq']
  by_cases hp : p ∈ S
  · rw [ite_eq_left hp] at hprod
    have h1 : finiteEvaluation p (GeneralLinearGroup.det X).val =
        (GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation p) X)).val :=
      congrArg Units.val hloc
    have h2 : finiteEvaluation p (∏ w ∈ S, finiteAtPlaceUnit w
        (GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation w) X))).val =
        (GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation p) X)).val :=
      congrArg Units.val hprod
    exact h1.trans h2.symm
  · rw [ite_eq_right hp] at hprod
    have h1 : finiteEvaluation p (GeneralLinearGroup.det X).val =
        (GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation p) X)).val :=
      congrArg Units.val hloc
    have h2 : finiteEvaluation p (∏ w ∈ S, finiteAtPlaceUnit w
        (GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation w) X))).val = 1 :=
      congrArg Units.val hprod
    have h3 : finiteEvaluation p (GeneralLinearGroup.det X).val = 1 := by
      rw [h1, hout p hp, Units.val_one]
    exact h3.trans h2.symm

/-- The local determinant of a block-shaped `X`. -/
theorem det_map_val_of_block (S : Finset FinitePlace)
    (X : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (P : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hloc : ∀ w : FinitePlace, (GeneralLinearGroup.map (finiteEvaluation w) X).val =
      if w ∈ S then blk2 (P w).val else 1) (w : FinitePlace) :
    (GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation w) X)).val =
      if w ∈ S then (blk2 (P w).val).det else 1 := by
  rw [show (GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation w) X)).val =
      (GeneralLinearGroup.map (finiteEvaluation w) X).val.det from rfl, hloc w]
  split_ifs <;> simp

theorem det_map_eq_one_of_out (S : Finset FinitePlace)
    (X : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (P : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hloc : ∀ w : FinitePlace, (GeneralLinearGroup.map (finiteEvaluation w) X).val =
      if w ∈ S then blk2 (P w).val else 1) (w : FinitePlace) (hw : w ∉ S) :
    GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation w) X) = 1 := by
  apply Units.ext
  rw [det_map_val_of_block S X P hloc w, ite_eq_right hw, Units.val_one]

/-- `normPower` of the global determinant of `X` is the product of the local exponentials. -/
theorem normPower_det_eq_prod (S : Finset FinitePlace)
    (X : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (hout : ∀ w : FinitePlace, w ∉ S →
      GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation w) X) = 1) (b : ℂ) :
    normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det X)) b =
      ∏ w ∈ S, Complex.exp (b * (Real.log
        ‖pe w (GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation w) X)).val‖ : ℂ)) := by
  rw [det_eq_prod S X hout]
  exact normPower_prod_finiteAtPlaceUnit S
    (fun w => GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEvaluation w) X)) b

/-- **Scalar split.** `normPower(det(X · g_f))` splits as the product over `S` of the local
exponentials of the `GL₂` block determinants, times `normPower(det g_f)`. -/
theorem normPower_det_mul_split (S : Finset FinitePlace)
    (X gf : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (P : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hloc : ∀ w : FinitePlace, (GeneralLinearGroup.map (finiteEvaluation w) X).val =
      if w ∈ S then blk2 (P w).val else 1) (b : ℂ) :
    normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det (X * gf))) b =
      (∏ w ∈ S, Complex.exp (b * (Real.log ‖pe w (blk2 (P w).val).det‖ : ℂ))) *
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf)) b := by
  rw [map_mul GeneralLinearGroup.det, finiteAdeleUnit_mul,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_mul,
    normPower_det_eq_prod S X (fun w hw => det_map_eq_one_of_out S X P hloc w hw) b]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [det_map_val_of_block S X P hloc w, ite_eq_left hw]

end Det

section Block

/-- **Block lemma with scalar split.** Restatement of `LfinBlockMulti.block_multi` with the scalar
written as the product of local exponentials over `S`, times `normPower(det g_f)`. -/
theorem block_multi_scalar (S : Finset FinitePlace)
    (P κ : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hP : ∀ w ∈ S, (P w).val 2 0 = 0 ∧ (P w).val 2 1 = 0)
    (L : GeneralLinearGroup (Fin 3) FiniteAdeles)
    (hS : ∀ w ∈ S, evM3 w L.val = (P w).val * (κ w).val)
    (hκ : ∀ w ∈ S, IntGL3 w (κ w).val)
    (hL : ∀ w, w ∉ S → IntGL3 w (evM3 w L.val))
    (gf : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (hgf : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) gf).val)
    {σ : CuspidalRepresentation} (b : ℂ) {vec : σ.H} (hsph : vec ∈ sphericalSubspace σ) :
    ∃ X : GeneralLinearGroup (Fin 2) FiniteAdeles,
      (∀ w, (GeneralLinearGroup.map (finiteEvaluation w) X).val =
        if w ∈ S then blk2 (P w).val else 1) ∧
      finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 b (L * blkGL gf) vec =
        ((∏ w ∈ S, Complex.exp (b * (Real.log ‖pe w (blk2 (P w).val).det‖ : ℂ))) *
          normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf)) b) •
          σ.π (atFinite (X * gf)) vec := by
  obtain ⟨X, hX, heq⟩ := block_multi S P κ hP L hS hκ hL gf hgf b hsph
  refine ⟨X, hX, ?_⟩
  rw [heq, normPower_det_mul_split S X gf P hX b]

end Block

end TernaryPeriodPolynomials.Argument.LatticeCounts.LfinScalar

end
