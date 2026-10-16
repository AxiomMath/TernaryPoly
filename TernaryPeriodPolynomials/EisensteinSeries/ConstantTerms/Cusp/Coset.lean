module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Packaging

@[expose] public section


/-!
# Proposition C.4: plane cusps and the cosets of their stabilizers

A plane cusp is presented by a change of basis `a ∈ SL₃(ℝ)` whose third row is a real multiple of
a nonzero integral row `r` (`CuspData`); the standard cusp has `a = 1`, `r = e₃`. The cusp
stabilizer in `Γ` is the stabilizer of `r` under right multiplication, the cosets `Γ_P\Γ` inject
into the nonzero integral rows `r γ`, and a bound by a negative power of the height of `a γ`
is dominated by a summable function on the cosets (`exists_summable_dominating_cusp`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-! ### A plane cusp datum -/

/-- A rational plane cusp, presented by the change of basis `a ∈ SL₃(ℝ)` that moves the cusp to the
standard plane cusp: the third row of `a` is a real multiple `lam • r` of a nonzero integral row
`r`. The cusp is `a⁻¹ P a`; for `a ∈ SL₃(ℤ)` and, up to a real scalar, for `a⁻¹ ∈ GL₃(ℚ)`, such an
`r` exists. -/
structure CuspData where
  /-- The change of basis. -/
  a : Matrix (Fin 3) (Fin 3) ℝ
  det_a : a.det = 1
  /-- The integral row proportional to the third row of `a`. -/
  r : Fin 3 → ℤ
  lam : ℝ
  row_a : ∀ j, a 2 j = lam * (r j : ℝ)

namespace CuspData

variable (D : CuspData)

theorem r_ne_zero : D.r ≠ 0 := by
  intro h
  have : ∀ j, D.a 2 j = 0 := fun j => by simp [D.row_a j, h]
  have h0 := Matrix.det_eq_zero_of_row_eq_zero (A := D.a) 2 this
  rw [D.det_a] at h0
  exact one_ne_zero h0

theorem lam_ne_zero : D.lam ≠ 0 := by
  intro h
  have : ∀ j, D.a 2 j = 0 := fun j => by simp [D.row_a j, h]
  have h0 := Matrix.det_eq_zero_of_row_eq_zero (A := D.a) 2 this
  rw [D.det_a] at h0
  exact one_ne_zero h0

/-- The standard cusp: `a = 1`, `r = e₃`. -/
def standard : CuspData where
  a := 1
  det_a := Matrix.det_one
  r := ![0, 0, 1]
  lam := 1
  row_a j := by fin_cases j <;> simp [Matrix.one_apply]

end CuspData

/-! ### The cosets of the cusp stabilizer -/

/-- The stabilizer of the integral row `r` under right multiplication: the integral cusp
stabilizer `Γ_P` (transported to the cusp). -/
def stabRow (r : Fin 3 → ℤ) : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ) where
  carrier := {p | r ᵥ* (p : Matrix (Fin 3) (Fin 3) ℤ) = r}
  mul_mem' := by
    intro p q hp hq
    show r ᵥ* ((p * q : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = r
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.vecMul_vecMul]
    have hp' : r ᵥ* (p : Matrix (Fin 3) (Fin 3) ℤ) = r := hp
    have hq' : r ᵥ* (q : Matrix (Fin 3) (Fin 3) ℤ) = r := hq
    rw [hp', hq']
  one_mem' := by
    show r ᵥ* ((1 : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = r
    simp
  inv_mem' := by
    intro p hp
    have hp' : r ᵥ* (p : Matrix (Fin 3) (Fin 3) ℤ) = r := hp
    show r ᵥ* ((p⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = r
    have : (r ᵥ* (p : Matrix (Fin 3) (Fin 3) ℤ)) ᵥ*
        ((p⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = r := by
      rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
      simp
    rwa [hp'] at this

section Cosets

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (r : Fin 3 → ℤ)

/-- The right coset space `Γ_P \ Γ` of the cusp with row `r`. -/
abbrev CuspCoset := Quotient (QuotientGroup.rightRel ((stabRow r).subgroupOf Γ))

/-- The row `r γ ∈ ℤ³` of a coset. -/
def cuspRow : CuspCoset Γ r → (Fin 3 → ℤ) :=
  Quotient.lift (fun a : Γ => r ᵥ* (a.1 : Matrix (Fin 3) (Fin 3) ℤ)) (by
    intro a b hab
    have hH : b.1 * a.1⁻¹ ∈ stabRow r := by
      have := QuotientGroup.rightRel_apply.1 hab
      simpa using Subgroup.mem_subgroupOf.1 this
    have hH' : r ᵥ* ((b.1 * a.1⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
        Matrix (Fin 3) (Fin 3) ℤ) = r := hH
    have e : b.1 = (b.1 * a.1⁻¹) * a.1 := by simp
    show r ᵥ* (a.1 : Matrix (Fin 3) (Fin 3) ℤ) = r ᵥ* (b.1 : Matrix (Fin 3) (Fin 3) ℤ)
    conv_rhs => rw [e, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.vecMul_vecMul, hH'])

theorem cuspRow_mk (a : Γ) :
    cuspRow Γ r (Quotient.mk _ a) = r ᵥ* (a.1 : Matrix (Fin 3) (Fin 3) ℤ) := rfl

theorem cuspRow_injective : Function.Injective (cuspRow Γ r) := by
  intro x y
  induction x using Quotient.inductionOn with | _ a => ?_
  induction y using Quotient.inductionOn with | _ b => ?_
  intro h
  apply Quotient.sound
  refine QuotientGroup.rightRel_apply.2 (Subgroup.mem_subgroupOf.2 ?_)
  have h' : r ᵥ* (a.1 : Matrix (Fin 3) (Fin 3) ℤ) = r ᵥ* (b.1 : Matrix (Fin 3) (Fin 3) ℤ) := h
  show r ᵥ* ((b.1 * a.1⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = r
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.vecMul_vecMul, ← h', Matrix.vecMul_vecMul,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
  simp

theorem vecMul_ne_zero {r : Fin 3 → ℤ} (hr : r ≠ 0) (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
    r ᵥ* (γ : Matrix (Fin 3) (Fin 3) ℤ) ≠ 0 := by
  intro h
  apply hr
  have : (r ᵥ* (γ : Matrix (Fin 3) (Fin 3) ℤ)) ᵥ*
      ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = r := by
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    simp
  rw [h] at this
  simpa using this.symm

end Cosets

/-! ### Domination over the cusp cosets -/

theorem row_mul_eq (D : CuspData) (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (j : Fin 3) :
    (D.a * realMat γ) 2 j = D.lam * ((D.r ᵥ* (γ : Matrix (Fin 3) (Fin 3) ℤ)) j : ℝ) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, D.row_a,
    realMat_apply]
  push_cast
  ring

/-- A bound `B(γ,q) ≤ C / (√ t(a γ q))^{n+3}` on a compact set is dominated by a summable
function on the cosets `Γ_P \ Γ` of the cusp. -/
theorem exists_summable_dominating_cusp (D : CuspData)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ)
    (hn : 4 ≤ n) {K : Set (Fin 5 → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Omega)
    (B : Γ → (Fin 5 → ℝ) → ℝ) (C₁ : ℝ)
    (hB : ∀ γ : Γ, ∀ q ∈ K,
      B γ q ≤ C₁ / (Real.sqrt (planeAct (D.a * realMat γ.1) q 4)) ^ (n + 3)) :
    ∃ b : CuspCoset Γ D.r → ℝ, Summable b ∧ ∀ (γ : Γ), ∀ q ∈ K, B γ q ≤ b (Quotient.mk _ γ) := by
  set s : ℝ := ((n : ℝ) + 3) / 2 with hs
  obtain ⟨Λ₀, hΛ₀⟩ := exists_bound_planePinv hK hKΩ
  set L : ℝ := max Λ₀ 1 with hL
  have hL1 : 1 ≤ L := le_max_right _ _
  have hL0 : 0 < 3 * L := by linarith
  set C₂ : ℝ := max C₁ 0 with hC₂
  have hlam : 0 < |D.lam| := abs_pos.2 D.lam_ne_zero
  refine ⟨fun c => C₂ * (3 * L) ^ s * (|D.lam| * ‖(fun j => (cuspRow Γ D.r c j : ℝ))‖) ^ (-s),
    ?_, ?_⟩
  · have hr : -s < -3 := by
      rw [hs]; have : (4 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h1 := summable_intVec_norm_rpow hr
    have h2 : Summable ((fun v : Fin 3 → ℤ => ‖(fun j => (v j : ℝ))‖ ^ (-s)) ∘ cuspRow Γ D.r) :=
      h1.comp_injective (cuspRow_injective Γ D.r)
    have h3 := h2.mul_left (C₂ * (3 * L) ^ s * |D.lam| ^ (-s))
    refine h3.congr fun c => ?_
    have hv : 0 ≤ ‖(fun j => (cuspRow Γ D.r c j : ℝ))‖ := norm_nonneg _
    simp only [Function.comp]
    rw [Real.mul_rpow hlam.le hv]
    ring
  · intro a q hq
    set g := D.a * realMat a.1 with hg
    have hdet : g.det = 1 := by
      rw [hg, Matrix.det_mul, D.det_a, det_realMat, one_mul]
    have hqΩ := hKΩ hq
    have hT := (planeAct_mem hdet hqΩ).2
    have hbound := hB a q hq
    have hrow : ‖fun j : Fin 3 => g 2 j‖ ≤ 3 * L * planeAct g q 4 :=
      norm_bottomRow_le hdet hqΩ L (fun l j' => (hΛ₀ q hq l j').trans (le_max_left _ _))
    have hvec : (fun j : Fin 3 => g 2 j) =
        D.lam • fun j => ((cuspRow Γ D.r (Quotient.mk _ a) j : ℤ) : ℝ) := by
      funext j
      simp [hg, row_mul_eq, cuspRow_mk]
    rw [hvec, norm_smul, Real.norm_eq_abs] at hrow
    set v : ℝ := |D.lam| * ‖fun j => ((cuspRow Γ D.r (Quotient.mk _ a) j : ℤ) : ℝ)‖ with hv
    have hvpos : 0 < v := by
      rw [hv]
      refine mul_pos hlam ?_
      rw [norm_pos_iff]
      intro h0
      apply vecMul_ne_zero D.r_ne_zero a.1
      funext j
      have := congrFun h0 j
      simpa [cuspRow_mk] using this
    have hX : v / (3 * L) ≤ planeAct g q 4 := by
      rw [div_le_iff₀ hL0]; linarith
    have hpow : (v / (3 * L)) ^ s ≤ (Real.sqrt (planeAct g q 4)) ^ (n + 3) := by
      rw [sqrt_pow_eq_rpow' _ hT.le]
      have : ((n + 3 : ℕ) : ℝ) / 2 = s := by rw [hs]; push_cast; ring
      rw [this]
      exact Real.rpow_le_rpow (div_pos hvpos hL0).le hX (by rw [hs]; positivity)
    have hXs : 0 < (v / (3 * L)) ^ s := Real.rpow_pos_of_pos (div_pos hvpos hL0) _
    refine hbound.trans ?_
    calc C₁ / (Real.sqrt (planeAct g q 4)) ^ (n + 3)
        ≤ C₂ / (Real.sqrt (planeAct g q 4)) ^ (n + 3) :=
          div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ C₂ / (v / (3 * L)) ^ s :=
          div_le_div_of_nonneg_left (le_max_right _ _) hXs hpow
      _ = C₂ * (3 * L) ^ s * v ^ (-s) := by
          rw [Real.div_rpow hvpos.le hL0.le, Real.rpow_neg hvpos.le]
          field_simp

end TernaryPeriodPolynomials.Argument.ConvergenceC4
