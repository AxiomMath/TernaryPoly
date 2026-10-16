module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.Integrand
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LfinBlockMulti

@[expose] public section


open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-!
# Global limit: translation invariance of the global integrand by integral pairs

`globalIntegrand_add_integral`: for a base `Z ∈ GL₂(Ẑ)` (integral at every place), `F(s + a, t + b) = F(s, t)` for finite adeles `a, b` integral at every place.  Proof: `L(s + a, t + b) = L(s, t) · U(a, b)`
(`LfinGLof_add`) with `U(a,b) = [[1,a,b],[0,1,0],[0,0,1]]`, and `(blk Z)⁻¹ U(a,b) (blk Z)` is integral at every place, so the right `GL₃(Ẑ)`-invariance of the plane vector
(`finitePlaneVector_mul_integral`) removes it.  Consequence (`GlobalLimitMeas`): `F` is locally constant, hence continuous and measurable.

Formalized by Claude Sonnet 5.5.
-/

open Classical

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitInvariance

section Ring

variable {R : Type*} [CommRing R]

/-- The unipotent matrix `[[1,a,b],[0,1,0],[0,0,1]]`. -/
def UcpM (a b : R) : Matrix (Fin 3) (Fin 3) R := !![1, a, b; 0, 1, 0; 0, 0, 1]

/-- Its inverse. -/
def UcpMInv (a b : R) : Matrix (Fin 3) (Fin 3) R := !![1, -a, -b; 0, 1, 0; 0, 0, 1]

theorem UcpM_mul_inv (a b : R) : UcpM a b * UcpMInv a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UcpM, UcpMInv, Matrix.mul_apply, Fin.sum_univ_three]

theorem UcpMInv_mul (a b : R) : UcpMInv a b * UcpM a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UcpM, UcpMInv, Matrix.mul_apply, Fin.sum_univ_three]

/-- The unit `U(a, b)`. -/
def UcpGL (a b : R) : GeneralLinearGroup (Fin 3) R :=
  ⟨UcpM a b, UcpMInv a b, UcpM_mul_inv a b, UcpMInv_mul a b⟩

/-- **`L(s + a, t + b) = L(s, t) · U(a, b)`.** -/
theorem LstR_add (s t a b : R) : LstR (s + a) (t + b) = LstR s t * UcpM a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LstR, UcpM, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

end Ring

theorem LfinGLof_add (s t a b : FiniteAdeles) : LfinGLof (s + a) (t + b) = LfinGLof s t * UcpGL a b :=
  Units.ext (LstR_add s t a b)

theorem IS3_UcpGL (w : FinitePlace) {a b : w.adicCompletion ℚ} (ha : a ∈ OS w) (hb : b ∈ OS w) :
    IS3 w (UcpGL a b) := by
  have h1 : (1 : w.adicCompletion ℚ) ∈ OS w := (OS w).one_mem
  have h0 : (0 : w.adicCompletion ℚ) ∈ OS w := (OS w).zero_mem
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [UcpGL, UcpM, ha, hb, h1, h0]
  · change UcpMInv a b i j ∈ OS w
    fin_cases i <;> fin_cases j <;> simp [UcpMInv, (OS w).neg_mem ha, (OS w).neg_mem hb, h1, h0]

theorem map_UcpGL (w : FinitePlace) (a b : FiniteAdeles) :
    GeneralLinearGroup.map (finiteEvaluation w) (UcpGL a b) =
      UcpGL (finiteEvaluation w a) (finiteEvaluation w b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UcpGL, UcpM, GeneralLinearGroup.map_apply]

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- **Translation invariance of the global integrand by integral pairs** (`Z ∈ GL₂(Ẑ)` at every place):
`F(s + a, t + b) = F(s, t)` for `a, b` integral at every place. -/
theorem globalIntegrand_add_integral (I : EichlerInput σ n) (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) (z : FiniteAwayThree × FiniteAwayThree) (a b : FiniteAwayThree)
    (ha : ∀ w, finiteEvaluation w (awayVal a) ∈ OS w) (hb : ∀ w, finiteEvaluation w (awayVal b) ∈ OS w) :
    globalIntegrand I Z gInf (z.1 + a, z.2 + b) = globalIntegrand I Z gInf z := by
  have hIS : ∀ w, IS3 w (GeneralLinearGroup.map (finiteEvaluation w) (blkGL Z)) := by
    intro w
    rw [ev_blkGL]
    exact IS3_blkLocGL w _ (hZ w)
  have hK : ∀ w, IS3 w (GeneralLinearGroup.map (finiteEvaluation w) ((blkGL Z)⁻¹ * UcpGL (awayVal a) (awayVal b) * blkGL Z)) := by
    intro w
    rw [map_mul, map_mul, map_inv, map_UcpGL]
    exact IS3_mul w (IS3_mul w (IS3_inv_of w (hIS w)) (IS3_UcpGL w (ha w) (hb w))) (hIS w)
  obtain ⟨kI, hkI⟩ := lift_of_all_IS3 _ hK
  unfold globalIntegrand
  have hadd : awayVal (z.1 + a) = awayVal z.1 + awayVal a := map_add (AddSubgroup.subtype _) _ _
  have hadd2 : awayVal (z.2 + b) = awayVal z.2 + awayVal b := map_add (AddSubgroup.subtype _) _ _
  rw [hadd, hadd2, LfinGLof_add]
  have hg : LfinGLof (awayVal z.1) (awayVal z.2) * UcpGL (awayVal a) (awayVal b) * blkGL Z =
      (LfinGLof (awayVal z.1) (awayVal z.2) * blkGL Z) * GeneralLinearGroup.map integralEmbedding kI := by
    rw [hkI]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [hg, finitePlaneVector_mul_integral GeneralEisenstein.trivialCharacter 0 (expo I) (fun _ => rfl)
    (fun kk => I.vector_spherical kk)]

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitInvariance
