module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LfinFactor
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitPlaneG

@[expose] public section


/-!
# Multi-place block lemma at the 2×2 level (route (b), step (B1))

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

Restriction: the base point `g_f : GL₂(𝔸_f)` is integral at every place,
including place `3`. The hypothesis is `hgf`.

For `L = Lfin z` with `L = Pl · K` (`LfinFactor.lfin_factor`), the plane section at `L · blkGL g_f` is
the plane section at `Pl · blkGL g_f`, with `K'' = blkGL g_f⁻¹ · K · blkGL g_f` integral at every place.
Hence `finitePlaneVector_eq_block` applies, and the `GL₂` block of `Pl` is determined place by place:
`S`-local block `blk2 (P_w)` on `S` and `1` off `S`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSection
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinFactor
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

open Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti

/-- The `2 × 2` upper block of a `3 × 3` matrix. -/
def blk2 {R : Type*} (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 2) (Fin 2) R :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

theorem blk2_one {R : Type*} [Ring R] : blk2 (1 : Matrix (Fin 3) (Fin 3) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk2]

/-- Evaluation commutes with the `GL₂ → GL₃` block embedding. -/
theorem ev_blkGL (w : FinitePlace) (g : GeneralLinearGroup (Fin 2) FiniteAdeles) :
    GeneralLinearGroup.map (finiteEvaluation w) (blkGL g) =
      blkLocGL w (GeneralLinearGroup.map (finiteEvaluation w) g) := by
  apply Units.ext
  show (blk3 g.val).map (finiteEvaluation w) = blk3 (g.val.map (finiteEvaluation w))
  exact blk3_map _ _

/-- Evaluation of the `GL₂` block of a plane element is the `blk2` of its evaluation. -/
theorem ev_planeBlockGL (w : FinitePlace) (p : GeneralLinearGroup (Fin 3) FiniteAdeles)
    (hp : p ∈ planeParabolic FiniteAdeles) :
    (GeneralLinearGroup.map (finiteEvaluation w) (planeBlockGL p hp)).val =
      blk2 (p.val.map (finiteEvaluation w)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem IS3_inv_of (w : FinitePlace) {U : GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ)}
    (hU : IS3 w U) : IS3 w U⁻¹ :=
  ⟨hU.2, by rw [inv_inv]; exact hU.1⟩

theorem intGL3_of_IS3 (w : FinitePlace) {U : GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ)}
    (hU : IS3 w U) : IntGL3 w U.val :=
  ⟨Matrix.isUnit_det_of_right_inverse (Units.mul_inv U), hU.1, fun i j => by
    rw [← Matrix.coe_units_inv]
    exact hU.2 i j⟩

theorem IS3_of_intGL3 (w : FinitePlace) {U : GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ)}
    (hU : IntGL3 w U.val) : IS3 w U :=
  ⟨hU.2.1, fun i j => by
    rw [Matrix.coe_units_inv]
    exact hU.2.2 i j⟩

/-- Bridge: the value of a mapped unit is `evM3` of the value (definitional; used by `rw`, not by unification). -/
theorem val_map_evM3 (w : FinitePlace) (g : GeneralLinearGroup (Fin 3) FiniteAdeles) :
    (GeneralLinearGroup.map (finiteEvaluation w) g).val = evM3 w g.val :=
  rfl

/-- Integral lift for an arbitrary element, stated on a variable; the conversion is by `rw` with the bridge. -/
theorem lift_of_all_IS3 (g : GeneralLinearGroup (Fin 3) FiniteAdeles)
    (h : ∀ w : FinitePlace, IS3 w (GeneralLinearGroup.map (finiteEvaluation w) g)) :
    ∃ kI : GeneralLinearGroup (Fin 3) IntegralAdeles,
      GeneralLinearGroup.map integralEmbedding kI = g :=
  mem_gl3_integral_of_intGL3 g fun w => by
    have h' := intGL3_of_IS3 w (h w)
    rw [val_map_evM3] at h'
    exact h'

/-- **Multi-place block lemma (2 × 2 base).** With `L = Lfin z` factored as in `lfin_factor`, and
`g_f ∈ GL₂(𝔸_f)` integral at every place (restriction (a)), the plane section at `L · blkGL g_f`
equals the `GL₂`-block value at `X · g_f`, where `X` is the block of the plane part, whose local
values are `blk2 (P_w)` on `S` and `1` off `S`. The scalar is `normPower` of `det (X · g_f)`. -/
theorem block_multi (S : Finset FinitePlace)
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
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det (X * gf))) b •
          σ.π (atFinite (X * gf)) vec := by
  obtain ⟨Pl, K, hLK, hPl, hPlev, hKev, kI, hkI⟩ := lfin_factor S P κ hP L hS hκ hL
  have hBmem : blkGL gf ∈ planeParabolic FiniteAdeles := blkGL_mem_plane gf
  have hIS : ∀ w, IS3 w (GeneralLinearGroup.map (finiteEvaluation w) K) := by
    intro w
    apply IS3_of_intGL3 w
    have h : IntGL3 w (evM3 w K.val) := by
      rw [hKev w]
      split_ifs with hw
      · exact hκ w hw
      · exact hL w hw
    exact h
  have hIS2 : ∀ w, IS3 w (GeneralLinearGroup.map (finiteEvaluation w) (blkGL gf)) := by
    intro w
    rw [ev_blkGL]
    exact IS3_blkLocGL w _ (hgf w)
  have hK2 : ∀ w, IS3 w
      (GeneralLinearGroup.map (finiteEvaluation w) ((blkGL gf)⁻¹ * K * blkGL gf)) := by
    intro w
    rw [map_mul, map_mul, map_inv]
    exact IS3_mul w (IS3_mul w (IS3_inv_of w (hIS2 w)) (hIS w)) (hIS2 w)
  obtain ⟨kI2, hkI2⟩ := lift_of_all_IS3 ((blkGL gf)⁻¹ * K * blkGL gf) hK2
  have hp : Pl * blkGL gf ∈ planeParabolic FiniteAdeles :=
    (planeParabolic FiniteAdeles).mul_mem hPl hBmem
  have hg : L * blkGL gf = (Pl * blkGL gf) * GeneralLinearGroup.map integralEmbedding kI2 := by
    rw [hkI2, hLK]
    simp only [mul_assoc, mul_inv_cancel_left]
  have hfin := finitePlaneVector_eq_block GeneralEisenstein.trivialCharacter b (fun _ => rfl)
    hsph hp kI2 hg
  refine ⟨planeBlockGL Pl hPl, ?_, ?_⟩
  · intro w
    rw [ev_planeBlockGL w Pl hPl]
    show blk2 (evM3 w Pl.val) = _
    rw [hPlev w]
    simp only [LfinFactor.pick]
    split_ifs with hw
    · rfl
    · exact blk2_one
  · rw [hfin, planeBlockGL_mul hPl hBmem, planeBlockGL_blkGL gf (blkGL_mem_plane gf)]

end TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti

end
