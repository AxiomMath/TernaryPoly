module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.PairValueAux
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FlatHexM

@[expose] public section


/-!
# The plane coordinates of the chambers of the flat

`rho_chamber`: for the `k`-th Weyl chamber of the diagonal flat, the plane coordinates `rhoE ∘ psi` (log-pivots) of the form with
simple-root parameters `(s, t)` are `hexM k · (log s, log t)` (matrices `hexM` of `FlatHexM`).  The determinants are
`4 · (-1)^k`; the chamber sign `(-1)^k` of the flat chain times the orientation of `hexM k` is therefore always positive.

Formalized by Claude Sonnet 5.5.
-/

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceFlagCoordinates
  TernaryPoly.SymmetricSpaceRationalAction TernaryPoly.SymmetricSpaceRationalCharts
  TernaryPoly.SymmetricSpaceParabolicCoordinates
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

theorem normalize_diag_eq (d0 d1 d2 : ℝ) (h2 : 0 < d2) :
    normalize (Matrix.diagonal ![d0, d1, d2]) = normalize (Matrix.diagonal ![d0 / d2, d1 / d2, 1]) := by
  have : (Matrix.diagonal ![d0, d1, d2] : Mat) = d2 • Matrix.diagonal ![d0 / d2, d1 / d2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
  rw [this]
  exact SymmetricSpacePositive.normalize_smul _ h2.ne' _

/-- The plane coordinates of a diagonal form. -/
theorem rho_diag (S : Space) (d0 d1 d2 : ℝ) (h0 : 0 < d0) (h1 : 0 < d1) (h2 : 0 < d2)
    (hS : S.val = normalize (Matrix.diagonal ![d0, d1, d2])) :
    rhoE (psi S) = mk2 (Real.log (d0 / d2)) (Real.log (d1 / d2)) := by
  have ha : 0 < d0 / d2 := div_pos h0 h2
  have hb : 0 < d1 / d2 := div_pos h1 h2
  have hSp : S = ldlHomeomorph.symm ((![0, 0, 0] : Vec3), ((⟨d0 / d2, ha⟩ : PositiveScale), (⟨d1 / d2, hb⟩ : PositiveScale))) := by
    apply Subtype.ext
    rw [ldlHomeomorph_symm, hS, normalize_diag_eq d0 d1 d2 h2]
    congr 1
    simp [flagMatrix, upper_zero, SymmetricSpaceFlagCoordinates.diagonal]
  have hl : ldlHomeomorph S = ((![0, 0, 0] : Vec3), ((⟨d0 / d2, ha⟩ : PositiveScale), (⟨d1 / d2, hb⟩ : PositiveScale))) := by
    rw [hSp]; exact ldlHomeomorph.apply_symm_apply _
  rw [rhoE_psi]
  change (tHomeo (ldlHomeomorph S).2 : R2) = _
  rw [hl]
  ext i
  fin_cases i <;> simp [tHomeo, mk2, symm_eq_log]


theorem conjugate_diag_perm (σ : Equiv.Perm (Fin 3)) (e : Fin 3 → ℝ) :
    conjugate (realRational (permGL σ)) (Matrix.diagonal e) = Matrix.diagonal (fun i => e (σ.symm i)) := by
  ext i j
  simp [conjugate, permGL, Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Matrix.diagonal_apply, Matrix.star_eq_conjTranspose, Fin.sum_univ_succ]
  have key : ∀ a b : Fin 3, ((((if a = 0 then (1 : ℚ) else 0 : ℚ) : ℝ)) * e 0 * ((if b = 0 then (1 : ℚ) else 0 : ℚ) : ℝ) +
      (((if a = 1 then (1 : ℚ) else 0 : ℚ) : ℝ) * e 1 * ((if b = 1 then (1 : ℚ) else 0 : ℚ) : ℝ) +
        ((if a = 2 then (1 : ℚ) else 0 : ℚ) : ℝ) * e 2 * ((if b = 2 then (1 : ℚ) else 0 : ℚ) : ℝ))) = if a = b then e a else 0 := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp
  rw [key]
  by_cases h : i = j
  · subst h; simp
  · have : σ.symm i ≠ σ.symm j := fun h' => h (σ.symm.injective h')
    simp [h, this]


theorem hexPerm_symm_table :
    ((hexPerm 0).symm 0 = 0 ∧ (hexPerm 0).symm 1 = 1 ∧ (hexPerm 0).symm 2 = 2) ∧
    ((hexPerm 1).symm 0 = 1 ∧ (hexPerm 1).symm 1 = 0 ∧ (hexPerm 1).symm 2 = 2) ∧
    ((hexPerm 2).symm 0 = 2 ∧ (hexPerm 2).symm 1 = 0 ∧ (hexPerm 2).symm 2 = 1) ∧
    ((hexPerm 3).symm 0 = 2 ∧ (hexPerm 3).symm 1 = 1 ∧ (hexPerm 3).symm 2 = 0) ∧
    ((hexPerm 4).symm 0 = 1 ∧ (hexPerm 4).symm 1 = 2 ∧ (hexPerm 4).symm 2 = 0) ∧
    ((hexPerm 5).symm 0 = 0 ∧ (hexPerm 5).symm 1 = 2 ∧ (hexPerm 5).symm 2 = 1) := by
  decide

theorem rho_chamber (k : Fin 6) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    rhoE (psi (act (realRational (hexW k.val)) (diagSpace s t hs ht))) =
      mk2 (hexM k 0 0 * Real.log s + hexM k 0 1 * Real.log t)
        (hexM k 1 0 * Real.log s + hexM k 1 1 * Real.log t) := by
  set e : Fin 3 → ℝ := ![(s ^ 2 * t ^ 2)⁻¹, (t ^ 2)⁻¹, 1] with he
  have hepos : ∀ i, 0 < e i := by
    intro i; fin_cases i <;> simp [he] <;> positivity
  have hlog : ∀ i, Real.log (e i) = ![-2 * (Real.log s + Real.log t), -2 * Real.log t, 0] i := by
    intro i
    fin_cases i
    · simp [he, Real.log_inv, Real.log_mul, Real.log_pow, hs.ne', ht.ne']; ring
    · simp [he, Real.log_inv, Real.log_pow]
    · simp [he]
  have hpd : (Matrix.diagonal e : Mat).PosDef := by
    rw [Matrix.posDef_diagonal_iff]; exact hepos
  have hSval : (act (realRational (hexW k.val)) (diagSpace s t hs ht)).val =
      normalize (Matrix.diagonal (fun i => e ((hexPerm k.val).symm i))) := by
    change normalize (conjugate (realRational (hexW k.val)) (diagSpace s t hs ht).val) = _
    rw [diagSpace_val, show (Matrix.diagonal ![(s ^ 2 * t ^ 2)⁻¹, (t ^ 2)⁻¹, 1] : Mat) = Matrix.diagonal e from rfl,
      conjugate_normalize _ _ hpd, hexW, conjugate_diag_perm]
  have hrho := rho_diag _ (e ((hexPerm k.val).symm 0)) (e ((hexPerm k.val).symm 1)) (e ((hexPerm k.val).symm 2))
    (hepos _) (hepos _) (hepos _) (by rw [hSval]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp)
  rw [hrho, Real.log_div (hepos _).ne' (hepos _).ne', Real.log_div (hepos _).ne' (hepos _).ne',
    hlog, hlog, hlog]
  obtain ⟨t0, t1, t2, t3, t4, t5⟩ := hexPerm_symm_table
  fin_cases k
  all_goals
    ext i
    fin_cases i
    all_goals simp [mk2, hexM, t0, t1, t2, t3, t4, t5]
    all_goals ring

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
