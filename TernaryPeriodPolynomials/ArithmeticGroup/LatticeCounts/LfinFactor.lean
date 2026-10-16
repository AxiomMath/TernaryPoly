module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.IntegralLift

@[expose] public section


/-!
# Algebraic factorisation of a finite-adelic `GL₃` element (route (b), step (F))

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

Let `L ∈ GL₃(𝔸_f)`, a finite set `S` of places, local `P_w` (plane parabolic for `w ∈ S`) and local
`κ_w ∈ GL₃(ℚ_w)` with `L_w = P_w κ_w` at `w ∈ S`, `κ_w` integral at `w ∈ S`, and `L_w` integral at
`w ∉ S`. Then `L = Pl · K`, where `Pl` is the plane element with `P_w` at `w ∈ S` and `1` elsewhere,
and `K` is `κ_w` at `w ∈ S`, `L_w` off `S`, lies in `GL₃(IntegralAdeles)` after `integralEmbedding`.

`Pl` is built entrywise (`locMat`), not as a noncommutative `Finset.prod`.

Restriction: the base point `g_f` is not part of this lemma. The
route applies it with `L = Lfin z` and `z` integral outside `S`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic (OS)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift

open Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LfinFactor

/-- The `3 × 3` matrix over the finite adeles with `(i,j)`-entry `w ↦ F w i j`, for a family that
is integral at almost all places. -/
def locMat (F : ∀ w : FinitePlace, Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ))
    (hF : ∀ i j, ∀ᶠ w in Filter.cofinite, F w i j ∈ OS w) :
    Matrix (Fin 3) (Fin 3) FiniteAdeles :=
  fun i j => ⟨fun w => F w i j, hF i j⟩

theorem evM3_locMat (F : ∀ w : FinitePlace, Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ))
    (hF : ∀ i j, ∀ᶠ w in Filter.cofinite, F w i j ∈ OS w) (w : FinitePlace) :
    evM3 w (locMat F hF) = F w :=
  Matrix.ext fun _ _ => rfl

theorem evM3_mul' (w : FinitePlace) (A B : Matrix (Fin 3) (Fin 3) FiniteAdeles) :
    evM3 w (A * B) = evM3 w A * evM3 w B := by
  unfold evM3
  exact Matrix.map_mul

theorem evM3_one' (w : FinitePlace) :
    evM3 w (1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) = 1 := by
  unfold evM3
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem eq_of_eval {a b : FiniteAdeles} (h : ∀ w : FinitePlace, finiteEvaluation w a = finiteEvaluation w b) :
    a = b :=
  RestrictedProduct.ext _ _ h

theorem one_entry_mem (w : FinitePlace) (i j : Fin 3) :
    (1 : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) i j ∈ OS w := by
  rw [Matrix.one_apply]
  split_ifs
  · exact (OS w).one_mem
  · exact (OS w).zero_mem

theorem eventually_notMem (S : Finset FinitePlace) : ∀ᶠ w in Filter.cofinite, w ∉ S :=
  Filter.eventually_cofinite.2 (S.finite_toSet.subset fun w hw => by simpa using hw)

/-- The family equal to `X w` on `S` and to `1` off `S`. -/
def pick (S : Finset FinitePlace) (X : ∀ w : FinitePlace, Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) :
    ∀ w : FinitePlace, Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ) :=
  fun w => if w ∈ S then X w else 1

theorem pick_eventually (S : Finset FinitePlace)
    (X : ∀ w : FinitePlace, Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) (i j : Fin 3) :
    ∀ᶠ w in Filter.cofinite, pick S X w i j ∈ OS w :=
  (eventually_notMem S).mono fun w hw => by
    simp only [pick, ite_eq_right hw]
    exact one_entry_mem w i j

/-- **Algebraic factorisation.** `L = Pl · K` with `Pl` plane, `Pl_w = P_w` on `S`, and
`K` integral at every place (`K_w = κ_w` on `S`, `K_w = L_w` off `S`), so `K` lifts to
`GL₃(IntegralAdeles)`. -/
theorem lfin_factor (S : Finset FinitePlace)
    (P κ : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hP : ∀ w ∈ S, (P w).val 2 0 = 0 ∧ (P w).val 2 1 = 0)
    (L : GeneralLinearGroup (Fin 3) FiniteAdeles)
    (hS : ∀ w ∈ S, evM3 w L.val = (P w).val * (κ w).val)
    (hκ : ∀ w ∈ S, IntGL3 w (κ w).val)
    (hL : ∀ w, w ∉ S → IntGL3 w (evM3 w L.val)) :
    ∃ Pl K : GeneralLinearGroup (Fin 3) FiniteAdeles,
      L = Pl * K ∧ Pl ∈ planeParabolic FiniteAdeles ∧
      (∀ w, evM3 w Pl.val = pick S (fun w => (P w).val) w) ∧
      (∀ w, evM3 w K.val = if w ∈ S then (κ w).val else evM3 w L.val) ∧
      ∃ kI : GeneralLinearGroup (Fin 3) IntegralAdeles,
        GeneralLinearGroup.map integralEmbedding kI = K := by
  let PlM : Matrix (Fin 3) (Fin 3) FiniteAdeles :=
    locMat (pick S fun w => (P w).val) (pick_eventually S _)
  let PlI : Matrix (Fin 3) (Fin 3) FiniteAdeles :=
    locMat (pick S fun w => (P w)⁻¹.val) (pick_eventually S _)
  have evPlM : ∀ w, evM3 w PlM = pick S (fun w => (P w).val) w :=
    fun w => evM3_locMat _ _ w
  have evPlI : ∀ w, evM3 w PlI = pick S (fun w => (P w)⁻¹.val) w :=
    fun w => evM3_locMat _ _ w
  have hPlMI : PlM * PlI = 1 := by
    apply ext_of_evM3
    intro w
    rw [evM3_mul', evPlM, evPlI, evM3_one']
    unfold pick
    split_ifs
    · simp
    · exact Matrix.one_mul _
  have hPlIM : PlI * PlM = 1 := by
    apply ext_of_evM3
    intro w
    rw [evM3_mul', evPlM, evPlI, evM3_one']
    unfold pick
    split_ifs
    · simp
    · exact Matrix.one_mul _
  let Pl : GeneralLinearGroup (Fin 3) FiniteAdeles := ⟨PlM, PlI, hPlMI, hPlIM⟩
  let K : GeneralLinearGroup (Fin 3) FiniteAdeles :=
    ⟨PlI * L.val, L⁻¹.val * PlM, by
      rw [mul_assoc, ← mul_assoc L.val, Units.mul_inv, one_mul, hPlIM],
      by
        rw [mul_assoc, ← mul_assoc PlM PlI, hPlMI, one_mul, Units.inv_mul]⟩
  have hK : ∀ w, evM3 w K.val = if w ∈ S then (κ w).val else evM3 w L.val := by
    intro w
    show evM3 w (PlI * L.val) = _
    rw [evM3_mul', evPlI]
    unfold pick
    split_ifs with h
    · rw [hS w h, ← mul_assoc, Units.inv_mul, one_mul]
    · rw [one_mul]
  refine ⟨Pl, K, ?_, ?_, evPlM, hK, ?_⟩
  · apply Units.ext
    rw [Units.val_mul]
    show L.val = PlM * (PlI * L.val)
    rw [← mul_assoc, hPlMI, one_mul]
  · have h20 : Pl.val 2 0 = 0 := by
      apply eq_of_eval
      intro w
      rw [map_zero]
      show evM3 w PlM 2 0 = 0
      rw [evPlM]
      unfold pick
      split_ifs with h
      · exact (hP w h).1
      · simp
    have h21 : Pl.val 2 1 = 0 := by
      apply eq_of_eval
      intro w
      rw [map_zero]
      show evM3 w PlM 2 1 = 0
      rw [evPlM]
      unfold pick
      split_ifs with h
      · exact (hP w h).2
      · simp
    exact ⟨h20, h21⟩
  · apply mem_gl3_integral_of_intGL3
    intro w
    rw [hK w]
    split_ifs with h
    · exact hκ w h
    · exact hL w h

end TernaryPeriodPolynomials.Argument.LatticeCounts.LfinFactor

end
