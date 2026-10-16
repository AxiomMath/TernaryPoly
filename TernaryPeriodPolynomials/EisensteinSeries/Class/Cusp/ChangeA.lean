module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KSeries
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBruhat
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cell.KNeg

@[expose] public section


open scoped MatrixGroups
open ComplexConjugate
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open MvPolynomial
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c

/-!
# The series at an integral cusp of `P(ℤ)` is a standard series of a transformed cusp form

Formalized by Claude Sonnet 5.5.

For `q ∈ P(ℤ) = planeBorel` the series of the holomorphic seed at the cusp `ofSL q` is the series at the standard cusp of the Levi-transformed cusp form:
`seriesFormK_false_stab` (bottom entry `1`: `f ↦ f|A`) and `seriesFormK_false_neg` (bottom entry `-1`: `f ↦ (f|A)^*`, conjugated series); `exists_cuspChange`
packages both.  The cosets of the cusp `q` are the standard plane cosets (`cosetEquivBorel`).
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

theorem conj_planeStab_of_planeBorel {q p : SL(3, ℤ)} (hq : q ∈ planeBorel) (hp : p ∈ planeStab) :
    q * p * q⁻¹ ∈ planeStab := by
  have hq' := planeBorel.inv_mem hq
  have hqq : (q : Matrix (Fin 3) (Fin 3) ℤ) * ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
  have h22 := congrFun (congrFun hqq 2) 2
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hq0', hq1'⟩ := hq'
  obtain ⟨hp0, hp1, hp2⟩ := hp
  simp only [Matrix.mul_apply, Fin.sum_univ_three, hq0, hq1, Matrix.one_apply_eq] at h22
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hq0, hq1, hq0', hq1', hp0, hp1, hp2] <;>
    linarith



theorem mem_stabRow_ofSL_borel {q : SL(3, ℤ)} (hq : q ∈ planeBorel) (p : SL(3, ℤ)) :
    p ∈ stabRow (CuspData.ofSL q).r ↔ p ∈ planeStab := by
  rw [mem_stabRow_ofSL]
  constructor
  · intro h
    have := conj_planeStab_of_planeBorel (planeBorel.inv_mem hq) h
    simpa [mul_assoc] using this
  · exact conj_planeStab_of_planeBorel hq

/-- For `q ∈ P(ℤ)` the cusp cosets at the cusp `q` are the standard plane cosets. -/
def cosetEquivBorel (N : ℕ) {q : SL(3, ℤ)} (hq : q ∈ planeBorel) :
    CuspCoset (gammaN N) (CuspData.ofSL q).r ≃ PlaneCoset (gammaN N) :=
  Quotient.congr (Equiv.refl _) (fun a b => by
    simp only [Equiv.refl_apply]
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact mem_stabRow_ofSL_borel hq _)

theorem cosetEquivBorel_mk (N : ℕ) {q : SL(3, ℤ)} (hq : q ∈ planeBorel) (a : ↥(gammaN N)) :
    cosetEquivBorel N hq (Quotient.mk _ a) = Quotient.mk _ a := rfl

theorem summandPoly_congr_upper (n : ℕ) {h h' : ℂ → ℂ} (heq : ∀ z : ℂ, 0 < z.im → h z = h' z)
    {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    summandPoly n h g y a b = summandPoly n h' g y a b := by
  have e : formPullback (planeAct g) (seedForm n h) y a b = formPullback (planeAct g) (seedForm n h') y a b :=
    formPullback_congr_form y (fun a' b' => seedForm_congr_value n h' h _
      (heq _ (seedTau_im_pos (planeAct_mem hg hy))) a' b') a b
  unfold summandPoly
  rw [e]



section K

open UpperHalfPlane ModularForm

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

omit [NeZero N] in
theorem summandPoly_stab_mul_levi {q : SL(3, ℤ)} (hq : q ∈ planeStab) {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hG : G.det = 1) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    summandPoly n (hfun f) (realMat q * G) y a b =
      summandPoly n (hfun (cuspSlash N n (leviBlock q hq) f)) G y a b := by
  have h0 : (realMat q) 2 0 = 0 := by simp [realMat_apply, hq.1]
  have h1 : (realMat q) 2 1 = 0 := by simp [realMat_apply, hq.2.1]
  have hc : 0 < (realMat q) 2 2 := by simp [realMat_apply, hq.2.2]
  rw [summandPoly_bottom_mul n (hfun f) (det_realMat q) h0 h1 hc hG hy a b]
  refine summandPoly_congr_upper n (fun z hz => ?_) hG hy a b
  rw [← coe_mapGL_leviBlock q hq]
  exact slashTwisted_cuspSlash N n (leviBlock q hq) f hz

omit [NeZero N] in
theorem seriesFormK_false_stab {q : SL(3, ℤ)} (hq : q ∈ planeStab) {y : Fin 5 → ℝ} (hy : y ∈ Omega)
    (a c : Fin 5) :
    seriesFormK false (CuspData.ofSL q) (gammaN N) n f y a c =
      seriesForm (gammaN N) n (cuspSlash N n (leviBlock q hq) f) y a c := by
  have hqB : q ∈ planeBorel := ⟨hq.1, hq.2.1⟩
  apply MvPolynomial.ext
  intro m
  rw [coeff_seriesFormK, coeff_seriesForm]
  unfold seriesCoeffK seriesCoeff
  rw [← (cosetEquivBorel N hqB).tsum_eq (fun c' => termFun (gammaN N) n (cuspSlash N n (leviBlock q hq) f) c' a c m y)]
  refine tsum_congr fun w => ?_
  have hw : cosetEquivBorel N hqB w = Quotient.mk _ (Quotient.out w) := by
    conv_lhs => rw [← Quotient.out_eq w]
    rfl
  unfold termFunK termFun
  rw [summandK_false, ofSL_a, summandPoly_stab_mul_levi N n f hq (det_realMat _) hy a c, hw]
  rw [summandPoly_out_eq N n (cuspSlash N n (leviBlock q hq) f) _ hy a c]



omit [NeZero N] in
theorem planeBorel_cases {q : SL(3, ℤ)} (hq : q ∈ planeBorel) : q ∈ planeStab ∨ q * rPrime ∈ planeStab := by
  have hdet : (q : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := q.2
  obtain ⟨h0, h1⟩ := hq
  rw [Matrix.det_fin_three, h0, h1] at hdet
  have hu : IsUnit ((q : Matrix (Fin 3) (Fin 3) ℤ) 2 2) :=
    isUnit_iff_exists_inv.2 ⟨(q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 1 1 -
      (q : Matrix (Fin 3) (Fin 3) ℤ) 0 1 * (q : Matrix (Fin 3) (Fin 3) ℤ) 1 0, by linear_combination hdet⟩
  rcases Int.isUnit_iff.1 hu with h | h
  · exact Or.inl ⟨h0, h1, h⟩
  · refine Or.inr ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, rPrime_val, h0, h1, h]

omit [NeZero N] in
theorem neg_entries {q : SL(3, ℤ)} (hq : q * rPrime ∈ planeStab) :
    (q : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧ (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 ∧
      (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1 := by
  obtain ⟨a, b, c⟩ := hq
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, rPrime_val] at a b c
  simp at a b c
  exact ⟨a, b, by linarith⟩

omit [NeZero N] in
theorem summandPoly_neg_mul {q : SL(3, ℤ)} (hq : q * rPrime ∈ planeStab) {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hG : G.det = 1) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    summandPoly n (hfun f) (realMat q * G) y a b =
      cxP true (summandPoly n (hfun (fStarGen (leviGroup N) (leviGroup_J_stable N)
        (cuspSlash N n (leviBlock (q * rPrime) hq) f))) G y a b) := by
  obtain ⟨e0, e1, e2⟩ := neg_entries hq
  have h0 : (realMat q) 2 0 = 0 := by simp [realMat_apply, e0]
  have h1 : (realMat q) 2 1 = 0 := by simp [realMat_apply, e1]
  have hc : (realMat q) 2 2 < 0 := by simp [realMat_apply, e2]
  rw [summandPoly_bottom_neg_mul n (hfun f) (det_realMat q) h0 h1 hc hG hy a b]
  have hfeq : ∀ z : ℂ, 0 < z.im → hStar (slashTwisted (n + 3) (topBlock (realMat q * realMat rPrime)) (hfun f)) z =
      hfun (fStarGen (leviGroup N) (leviGroup_J_stable N) (cuspSlash N n (leviBlock (q * rPrime) hq) f)) z := by
    intro z hz
    have hz' : 0 < (-(conj z)).im := by simpa using hz
    have e1 : hfun (fStarGen (leviGroup N) (leviGroup_J_stable N) (cuspSlash N n (leviBlock (q * rPrime) hq) f)) z =
        conj (cuspH (leviGroup N) n (cuspSlash N n (leviBlock (q * rPrime) hq) f) (-(conj z))) :=
      fStarGen_cuspH (leviGroup N) (leviGroup_J_stable N) _ hz
    rw [e1, ← realMat_mul, ← coe_mapGL_leviBlock (q * rPrime) hq]
    exact congrArg conj (slashTwisted_cuspSlash N n (leviBlock (q * rPrime) hq) f hz')
  rw [summandPoly_congr_upper n hfeq hG hy a b]

omit [NeZero N] in
theorem seriesFormK_false_neg {q : SL(3, ℤ)} (hqB : q ∈ planeBorel) (hq : q * rPrime ∈ planeStab)
    {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a c : Fin 5) :
    seriesFormK false (CuspData.ofSL q) (gammaN N) n f y a c =
      cxP true (seriesForm (gammaN N) n (fStarGen (leviGroup N) (leviGroup_J_stable N)
        (cuspSlash N n (leviBlock (q * rPrime) hq) f)) y a c) := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_seriesFormK, coeff_cxP, coeff_seriesForm]
  unfold seriesCoeffK seriesCoeff
  rw [cx_tsum, ← (cosetEquivBorel N hqB).tsum_eq (fun c' => cx true (termFun (gammaN N) n
    (fStarGen (leviGroup N) (leviGroup_J_stable N) (cuspSlash N n (leviBlock (q * rPrime) hq) f)) c' a c m y))]
  refine tsum_congr fun w => ?_
  have hw : cosetEquivBorel N hqB w = Quotient.mk _ (Quotient.out w) := by
    conv_lhs => rw [← Quotient.out_eq w]
    rfl
  unfold termFunK termFun
  rw [summandK_false, ofSL_a, summandPoly_neg_mul N n f hq (det_realMat _) hy a c, hw, coeff_cxP]
  rw [summandPoly_out_eq N n (fStarGen (leviGroup N) (leviGroup_J_stable N)
    (cuspSlash N n (leviBlock (q * rPrime) hq) f)) _ hy a c]

omit [NeZero N] in
/-- **The series at an integral cusp `q ∈ P(ℤ)` is the standard series of a transformed cusp form** (conjugated when the Levi block has determinant `-1`):
there are `s : Bool` and a map `φ` of cusp forms (the Levi slash, followed by `f ↦ f^*` for `s = true`) with `𝓔_q(f) = cxP s 𝓔_P(φ f)` on `Ω`. -/
theorem exists_cuspChange {q : SL(3, ℤ)} (hq : q ∈ planeBorel) :
    ∃ (s : Bool) (φ : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ) → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)),
      ∀ (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) {y : Fin 5 → ℝ}, y ∈ Omega → ∀ a c : Fin 5,
        seriesFormK false (CuspData.ofSL q) (gammaN N) n f y a c = cxP s (seriesForm (gammaN N) n (φ f) y a c) := by
  rcases planeBorel_cases hq with h | h
  · exact ⟨false, fun f => cuspSlash N n (leviBlock q h) f, fun f y hy a c => by
      rw [cxP_false]; exact seriesFormK_false_stab N n f h hy a c⟩
  · exact ⟨true, fun f => fStarGen (leviGroup N) (leviGroup_J_stable N) (cuspSlash N n (leviBlock (q * rPrime) h) f),
      fun f y hy a c => seriesFormK_false_neg N n f hq h hy a c⟩

end K

end TernaryPeriodPolynomials.Argument.EisensteinClass
