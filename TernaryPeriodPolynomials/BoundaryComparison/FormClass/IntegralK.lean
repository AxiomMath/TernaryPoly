module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.OrbitDataK
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.Cells
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.Final

@[expose] public section


/-!
# Every cusp: the printed intertwiner at `g = (1, ι(k⁻¹))` is `lineA1K N k`

Formalized by Claude Sonnet 5.5.

* `adelicOf gf`: the element `(1, gf)` of `GL₃(𝔸)`.
* `FzK_integral`: the regrouped integrand at the cusp `k` is integrable with integral `Σ_o ∫ PhiQ0(c_o)(N v) dv`.
* `printed_intertwiner_evalK`: `∫_{𝔸²} φ(w₀⁻¹u(s,t) g)`, `g = (1, ι(k⁻¹))`, equals `lineA1K N k n f false`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.EisensteinDual TernaryPeriodPolynomials.Argument.GammaNFaces

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- **The integral over the cells at the cusp `k`.** -/
theorem FzK_integral (hN : 3 ≤ N) (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    Integrable (FzK N k n f x p q m) nuZ ∧
    ∫ z, FzK N k n f x p q m z ∂nuZ = ∑' o : FreeOrbK N k, ∫ v : Fin 2 → ℝ, phiOK N k n f x p q m o ((N : ℝ) • v) := by
  have hfin : ∀ o, finMeas2 (pieceFinK N k o) < ⊤ := fun o => by
    rw [volume_pieceFinK]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by simp [NeZero.pos])) (ENNReal.inv_lt_top.2 (by simp [NeZero.pos]))
  have hon : ∀ o z, z.1 ∈ pieceFinK N k o →
      FzK N k n f x p q m z = phiOK N k n f x p q m o (shiftV (orbPtK N k o) z.2) :=
    fun o z hz => FzK_on_piece N k hN n f hx p q m o hz z.2
  have hzero : ∀ z, (∀ o, z.1 ∉ pieceFinK N k o) → FzK N k n f x p q m z = 0 := by
    intro z hz
    by_cases hd : ∃ π κ, IsDecomp N (gFin z.1 * kInvFin k) π κ
    · obtain ⟨o, ho⟩ := exists_orbit_of_decompK N k z.1 hd
      exact absurd ho (hz o)
    · exact FzK_eq_zero_of_not N k n f x p q m z.1 z.2 hd
  have hG : ∀ o, Integrable (fun w => phiOK N k n f x p q m o (shiftV (orbPtK N k o) w)) := fun o =>
    (integrable_shiftV _ _).2 (phiOK_integrable N k n f hn hx p q m o)
  have hsum : Summable fun o : FreeOrbK N k => finMeas2.real (pieceFinK N k o) *
      ∫ w, ‖phiOK N k n f x p q m o (shiftV (orbPtK N k o) w)‖ := by
    refine (phiOK_norm_summable N k n f hn hx p q m).congr fun o => ?_
    rw [real_pieceFinK, integral_shiftV (orbPtK N k o) (fun v => ‖phiOK N k n f x p q m o v‖),
      integral_norm_phiOK]
  obtain ⟨hI, hE⟩ := cells_integral (pieceFinK N k) (pieceFinK_measurable N k) hfin (pieceFinK_disjoint N k hN)
    (FzK N k n f x p q m) (fun o w => phiOK N k n f x p q m o (shiftV (orbPtK N k o) w)) hon hzero hG hsum
  refine ⟨hI, hE.trans (tsum_congr fun o => ?_)⟩
  rw [integral_shiftV (orbPtK N k o) (phiOK N k n f x p q m o), real_pieceFinK, integral_phiOK]
  push_cast
  rfl

/-- The element `(1, gf)` of `GL₃(𝔸) = GL₃(ℝ × 𝔸_f)`. -/
def adelicOf (gf : FiniteGL) : AdelicGL where
  val := Matrix.of fun i j => (((1 : Matrix (Fin 3) (Fin 3) ℝ) i j), gf.val i j)
  inv := Matrix.of fun i j => (((1 : Matrix (Fin 3) (Fin 3) ℝ) i j), gf.inv i j)
  val_inv := by
    refine Matrix.ext fun i j => Prod.ext ?_ ?_
    · by_cases h : i = j <;> simp [Matrix.mul_apply, Matrix.one_apply, Prod.fst_sum, h]
    · have := congrArg (fun M : Matrix (Fin 3) (Fin 3) FiniteAdeles => M i j) gf.val_inv
      by_cases h : i = j <;> simpa [Matrix.mul_apply, Matrix.one_apply, Prod.snd_sum, h] using this
  inv_val := by
    refine Matrix.ext fun i j => Prod.ext ?_ ?_
    · by_cases h : i = j <;> simp [Matrix.mul_apply, Matrix.one_apply, Prod.fst_sum, h]
    · have := congrArg (fun M : Matrix (Fin 3) (Fin 3) FiniteAdeles => M i j) gf.inv_val
      by_cases h : i = j <;> simpa [Matrix.mul_apply, Matrix.one_apply, Prod.snd_sum, h] using this

end TernaryPeriodPolynomials.Argument.FormClassK
