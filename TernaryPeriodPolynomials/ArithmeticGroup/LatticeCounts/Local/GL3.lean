module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.RightTranslation
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REVector

@[expose] public section


/-!
# The local `GL₃` embedding `ι_v : GL₃(K_v) → GL₃(𝔸_f)` (part 3a)

`ιMat3 v M` is `M` at the place `v` and the identity at every other place; `ιGL3 v` is its restriction
to `GL₃`.  Proved: multiplicativity, `ιGL3` lands in the upper plane parabolic when the local element does,
and the upper `GL₂` block of `ιGL3 v P` is `ιGL v (planeBlockGL P)`.

Formalized by Claude Haiku 5.5.
-/

open Matrix
open Classical
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic (OS)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry (planeBlockGL_val_apply)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3

/-- The adele with value `x` at `v` and `1` elsewhere, entry `(i,j)` (indices in `Fin 3`). -/
def ιEntry3 (v : FinitePlace) (x : v.adicCompletion ℚ) (i j : Fin 3) : FiniteAdeles :=
  ⟨fun w => if hw : w = v then
      cast (congrArg (fun u : FinitePlace => u.adicCompletion ℚ) hw).symm x
    else (1 : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) i j,
   (Filter.eventually_cofinite_ne v).mono fun w hw => by
     dsimp only
     rw [dite_eq_right hw, Matrix.one_apply]
     split_ifs
     · exact (OS w).one_mem
     · exact (OS w).zero_mem⟩

theorem eval_ιEntry3_self (v : FinitePlace) (x : v.adicCompletion ℚ) (i j : Fin 3) :
    finiteEvaluation v (ιEntry3 v x i j) = x := by
  show (if h : v = v then _ else _) = x
  rw [dite_eq_left rfl]
  exact cast_eq _ x

theorem eval_ιEntry3_ne (v w : FinitePlace) (hw : w ≠ v) (x : v.adicCompletion ℚ) (i j : Fin 3) :
    finiteEvaluation w (ιEntry3 v x i j) = (1 : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) i j := by
  show (if h : w = v then _ else _) = _
  rw [dite_eq_right hw]

/-- `ι_v(M)` for a `3 × 3` local matrix. -/
def ιMat3 (v : FinitePlace) (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :
    Matrix (Fin 3) (Fin 3) FiniteAdeles :=
  fun i j => ιEntry3 v (M i j) i j

/-- Evaluation of a finite-adelic `3 × 3` matrix at `w`. -/
def evM3 (w : FinitePlace) (M : Matrix (Fin 3) (Fin 3) FiniteAdeles) :
    Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ) :=
  M.map (finiteEvaluation w)

theorem evM3_ιMat3_self (v : FinitePlace) (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :
    evM3 v (ιMat3 v M) = M :=
  Matrix.ext fun i j => eval_ιEntry3_self v (M i j) i j

theorem evM3_ιMat3_ne (v w : FinitePlace) (hw : w ≠ v) (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :
    evM3 w (ιMat3 v M) = 1 :=
  Matrix.ext fun i j => eval_ιEntry3_ne v w hw (M i j) i j

theorem ext_of_evM3 {A B : Matrix (Fin 3) (Fin 3) FiniteAdeles}
    (h : ∀ w : FinitePlace, evM3 w A = evM3 w B) : A = B :=
  Matrix.ext fun i j => RestrictedProduct.ext _ _ fun w => congrFun (congrFun (h w) i) j

theorem ιMat3_mul (v : FinitePlace) (M N : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :
    ιMat3 v (M * N) = ιMat3 v M * ιMat3 v N := by
  apply ext_of_evM3
  intro w
  have hmul : evM3 w (ιMat3 v M * ιMat3 v N) = evM3 w (ιMat3 v M) * evM3 w (ιMat3 v N) := by
    unfold evM3
    exact Matrix.map_mul
  rw [hmul]
  by_cases hw : w = v
  · subst hw
    rw [evM3_ιMat3_self, evM3_ιMat3_self, evM3_ιMat3_self]
  · rw [evM3_ιMat3_ne v w hw, evM3_ιMat3_ne v w hw, evM3_ιMat3_ne v w hw, one_mul]

theorem ιMat3_one (v : FinitePlace) : ιMat3 v (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = 1 := by
  apply ext_of_evM3
  intro w
  by_cases hw : w = v
  · subst hw
    rw [evM3_ιMat3_self]
    unfold evM3
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  · rw [evM3_ιMat3_ne v w hw]
    unfold evM3
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm

/-- `ι_v(A)` for `A ∈ GL₃(K_v)`. -/
def ιGL3 (v : FinitePlace) (A : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ)) :
    GeneralLinearGroup (Fin 3) FiniteAdeles :=
  ⟨ιMat3 v A.val, ιMat3 v A⁻¹.val,
    by rw [← ιMat3_mul, Units.mul_inv, ιMat3_one],
    by rw [← ιMat3_mul, Units.inv_mul, ιMat3_one]⟩

theorem ιGL3_val (v : FinitePlace) (A : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ)) :
    (ιGL3 v A).val = ιMat3 v A.val := rfl

theorem ιEntry3_zero (v : FinitePlace) {i j : Fin 3} (hij : i ≠ j) : ιEntry3 v 0 i j = 0 := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  show finiteEvaluation w (ιEntry3 v 0 i j) = finiteEvaluation w 0
  by_cases hw : w = v
  · subst hw
    rw [eval_ιEntry3_self, map_zero]
  · rw [eval_ιEntry3_ne v w hw, map_zero, Matrix.one_apply_ne hij]

/-- The local upper plane parabolic embeds into the finite upper plane parabolic. -/
theorem ιGL3_mem_plane (v : FinitePlace) {P : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ)}
    (hP : P ∈ planeParabolic (v.adicCompletion ℚ)) : ιGL3 v P ∈ planeParabolic FiniteAdeles := by
  have h20 : P.val 2 0 = 0 := hP.1
  have h21 : P.val 2 1 = 0 := hP.2
  refine ⟨?_, ?_⟩
  · show ιEntry3 v (P.val 2 0) 2 0 = 0
    rw [h20, ιEntry3_zero v (by decide)]
  · show ιEntry3 v (P.val 2 1) 2 1 = 0
    rw [h21, ιEntry3_zero v (by decide)]

/-- The entries of `ιEntry3` on the upper `2 × 2` corner agree with `ιEntry`. -/
theorem ιEntry3_castSucc (v : FinitePlace) (x : v.adicCompletion ℚ) (i j : Fin 2) :
    ιEntry3 v x i.castSucc j.castSucc = ιEntry v x i j := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  show finiteEvaluation w (ιEntry3 v x i.castSucc j.castSucc) = finiteEvaluation w (ιEntry v x i j)
  by_cases hw : w = v
  · subst hw
    rw [eval_ιEntry3_self, eval_ιEntry_self]
  · rw [eval_ιEntry3_ne v w hw, eval_ιEntry_ne v w hw, Matrix.one_apply, Matrix.one_apply]
    simp

/-- The `GL₂` block of `ι_v(P)` is `ι_v` of the `GL₂` block of `P`. -/
theorem planeBlockGL_ιGL3 (v : FinitePlace) {P : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ)}
    (hP : P ∈ planeParabolic (v.adicCompletion ℚ)) :
    planeBlockGL (ιGL3 v P) (ιGL3_mem_plane v hP) =
      ιGL v (planeBlockGL P hP) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  rw [planeBlockGL_val_apply, ιGL3_val, ιGL_val]
  show ιEntry3 v (P.val i.castSucc j.castSucc) i.castSucc j.castSucc =
    ιEntry v ((planeBlockGL P hP).val i j) i j
  rw [planeBlockGL_val_apply, ιEntry3_castSucc]

end TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3

end
