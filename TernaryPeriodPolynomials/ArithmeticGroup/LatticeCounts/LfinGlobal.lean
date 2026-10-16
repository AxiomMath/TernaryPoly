module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LfinScalar
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.ThreeSplitting

@[expose] public section


/-!
# Global `Lfin z` and its local values (route (b), step (B2a))

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

For finite adeles `s, t`, the global matrix `Lfin(s,t) ∈ GL₃(𝔸_f)` is the ring-generic
`L(s,t) = [[0,1,0],[0,0,1],[1,s,t]]`. Its evaluation at `w` is the local `L(s_w, t_w)`.
On `FiniteAwayThree²` (the 3-component of each coordinate is zero) the element is integral at
every place `w ∉ S` as soon as both coordinates are integral at `w`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers (FiniteAwayThree)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift

open Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal

section Ring

variable {R : Type*} [CommRing R]

/-- `L(s,t) = [[0,1,0],[0,0,1],[1,s,t]]` over any commutative ring. -/
def LstR (s t : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, 1, 0; 0, 0, 1; 1, s, t]

/-- Its inverse `[[-s,-t,1],[1,0,0],[0,1,0]]`. -/
def LstRInv (s t : R) : Matrix (Fin 3) (Fin 3) R :=
  !![-s, -t, 1; 1, 0, 0; 0, 1, 0]

theorem LstR_mul_LstRInv (s t : R) : LstR s t * LstRInv s t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LstR, LstRInv, Matrix.mul_apply, Fin.sum_univ_three]

theorem LstRInv_mul_LstR (s t : R) : LstRInv s t * LstR s t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LstR, LstRInv, Matrix.mul_apply, Fin.sum_univ_three]

end Ring

section Global

/-- The global `L(s,t)` as an element of `GL₃(𝔸_f)`. -/
def LfinGLof (s t : FiniteAdeles) : GeneralLinearGroup (Fin 3) FiniteAdeles :=
  Units.mk (LstR s t) (LstRInv s t) (LstR_mul_LstRInv s t) (LstRInv_mul_LstR s t)

theorem LfinGLof_val (s t : FiniteAdeles) : (LfinGLof s t).val = LstR s t :=
  rfl

/-- Evaluation of the global `L(s,t)` at `w` is the local `L(s_w, t_w)`. -/
theorem evM3_LfinGLof (w : FinitePlace) (s t : FiniteAdeles) :
    evM3 w (LfinGLof s t).val = LstR (finiteEvaluation w s) (finiteEvaluation w t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evM3, LfinGLof_val, LstR]

/-- The projection of a point of `FiniteAwayThree` to the finite adeles. -/
def awayVal (x : FiniteAwayThree) : FiniteAdeles := AddSubgroup.subtype _ x

end Global

section Integral

/-- `L(s,t)` is `GL₃`-integral at `w` when `s, t` are integral at `w`. -/
theorem intGL3_LstR (w : FinitePlace) {s t : w.adicCompletion ℚ} (hs : s ∈ OS w) (ht : t ∈ OS w) :
    IntGL3 w (LstR s t) := by
  have hn1 : -s ∈ OS w := (OS w).neg_mem hs
  have hn2 : -t ∈ OS w := (OS w).neg_mem ht
  refine ⟨Matrix.isUnit_det_of_right_inverse (LstR_mul_LstRInv s t), fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [LstR, hs, ht, (OS w).one_mem, (OS w).zero_mem]
  · rw [Matrix.inv_eq_right_inv (LstR_mul_LstRInv s t)]
    fin_cases i <;> fin_cases j <;> simp [LstRInv, hn1, hn2, (OS w).one_mem, (OS w).zero_mem]

/-- Both coordinates of `z` are integral at every place off `S`. -/
def UregionS (S : Finset FinitePlace) : Set (FiniteAwayThree × FiniteAwayThree) :=
  {z | ∀ w : FinitePlace, w ∉ S →
    finiteEvaluation w (awayVal z.1) ∈ OS w ∧ finiteEvaluation w (awayVal z.2) ∈ OS w}

/-- On `U_S`, the global `L(z)` is integral at every place off `S`. -/
theorem intGL3_LfinGLof_of_mem {S : Finset FinitePlace} {z : FiniteAwayThree × FiniteAwayThree}
    (hz : z ∈ UregionS S) (w : FinitePlace) (hw : w ∉ S) :
    IntGL3 w (evM3 w (LfinGLof (awayVal z.1) (awayVal z.2)).val) := by
  rw [evM3_LfinGLof]
  exact intGL3_LstR w (hz w hw).1 (hz w hw).2

end Integral

end TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal

end
