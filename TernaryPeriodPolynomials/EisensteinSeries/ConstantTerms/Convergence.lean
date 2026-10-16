module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Coset
public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Perm.ConjAct
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.MvPowerSeries.LexOrder
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.Tactic.MoveAdd
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.Order.ExtrClosure
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.UrysohnsLemma

@[expose] public section


/-!
# Value-level normal convergence of the series (Appendix C.3, Proposition C.4, zero order)

The coefficients of the terms of `ar:eq:Eseries` are dominated, uniformly on compacta of `Ω`, by a
summable function on `Γ_P \ Γ` (for `n ≥ 4`, i.e. `k = n + 3 > 6`). This is the VALUE-LEVEL statement
only: normal convergence of the derivatives, smoothness and closedness are Phase B.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### The terms of the series and their normal convergence -/

section Convergence

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] (n : ℕ)
  [SlashInvariantFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

/-- The hypothesis that the Levi block of every plane-stabilizer element of `Γ` lies in `Λ`. -/
def LeviIn : Prop :=
  ∀ γ ∈ Γ, γ ∈ planeStab → ∃ g ∈ Λ, (g : Matrix (Fin 2) (Fin 2) ℝ) = topBlock (realMat γ)

/-- The `m`-th coefficient of the `(i, j)` component of the summand of the coset `Γ_P γ`, at the
point `q ∈ Ω`: well defined on cosets by `summandPoly_stab_mul`. -/
def cosetTerm (hLevi : LeviIn Γ Λ) {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) : PlaneCoset Γ → ℂ :=
  Quotient.lift (fun a : Γ =>
      (summandPoly n (fun z => f (ofComplex z)) (realMat a.1) q i j).coeff m) (by
    intro a b hab
    have hH : b.1 * a.1⁻¹ ∈ planeStab := by
      have := QuotientGroup.rightRel_apply.1 hab
      simpa using Subgroup.mem_subgroupOf.1 this
    have hΓ : b.1 * a.1⁻¹ ∈ Γ := Γ.mul_mem b.2 (Γ.inv_mem a.2)
    have hS := summandPoly_stab_mul Λ n f (b.1 * a.1⁻¹) a.1 hH (hLevi _ hΓ hH) hq i j
    have e : (b.1 * a.1⁻¹) * a.1 = b.1 := by simp
    rw [e] at hS
    show (summandPoly n (fun z => f (ofComplex z)) (realMat a.1) q i j).coeff m =
      (summandPoly n (fun z => f (ofComplex z)) (realMat b.1) q i j).coeff m
    rw [hS])

theorem cosetTerm_mk (hLevi : LeviIn Γ Λ) {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) (a : Γ) :
    cosetTerm Γ Λ n f hLevi hq i j m (Quotient.mk _ a) =
      (summandPoly n (fun z => f (ofComplex z)) (realMat a.1) q i j).coeff m := rfl

theorem sqrt_pow_eq_rpow (T : ℝ) (hT : 0 ≤ T) (N : ℕ) : (Real.sqrt T) ^ N = T ^ ((N : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hT]
  ring_nf

end Convergence

section Convergence2

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic] (n : ℕ)
  [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

/-- **Normal convergence (zero order).** For `n ≥ 4` and a cusp form `f` of weight `n + 3`, on
every compact `K ⊂ Ω` the coefficients of the terms of the series are dominated by a summable
function on `Γ_P \ Γ`, uniformly in the point. -/
theorem exists_summable_bound (hn : 4 ≤ n)
    (hLevi : LeviIn Γ Λ) {K : Set (Fin 5 → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Omega) :
    ∃ b : PlaneCoset Γ → ℝ, Summable b ∧ ∀ (q : Fin 5 → ℝ) (hq : q ∈ K) (i j : Fin 5)
      (m : Fin 3 →₀ ℕ) (c : PlaneCoset Γ),
      ‖cosetTerm Γ Λ n f hLevi (hKΩ hq) i j m c‖ ≤ b c := by
  set s : ℝ := ((n : ℝ) + 3) / 2 with hs
  -- the cusp-form bound
  obtain ⟨Ch, hCh⟩ := CuspFormClass.exists_bound (k := ((n + 3 : ℕ) : ℤ)) f
  have hh : ∀ τ : ℂ, 0 < τ.im → ‖(fun z => f (ofComplex z)) τ‖ * τ.im ^ (((n : ℝ) + 3) / 2) ≤ Ch := by
    intro τ hτ
    have h1 := hCh ⟨τ, hτ⟩
    have h2 : (fun z => f (ofComplex z)) τ = f ⟨τ, hτ⟩ := by
      simp [ofComplex_apply_of_im_pos hτ]
    rw [h2]
    have hpos : 0 < (⟨τ, hτ⟩ : ℍ).im ^ ((((n + 3 : ℕ) : ℤ) : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by simpa using hτ) _
    have h3 : ((((n + 3 : ℕ) : ℤ) : ℝ) / 2) = ((n : ℝ) + 3) / 2 := by push_cast; ring
    rw [h3] at h1 hpos
    have : ‖f ⟨τ, hτ⟩‖ * (⟨τ, hτ⟩ : ℍ).im ^ (((n : ℝ) + 3) / 2) ≤ Ch := by
      calc _ ≤ Ch / (⟨τ, hτ⟩ : ℍ).im ^ (((n : ℝ) + 3) / 2) *
            (⟨τ, hτ⟩ : ℍ).im ^ (((n : ℝ) + 3) / 2) := mul_le_mul_of_nonneg_right h1 hpos.le
        _ = Ch := div_mul_cancel₀ _ hpos.ne'
    simpa using this
  obtain ⟨C₁, hC₁⟩ := summand_value_bound n (fun z => f (ofComplex z)) Ch hh hK hKΩ
  obtain ⟨Λ₀, hΛ₀⟩ := exists_bound_planePinv hK hKΩ
  set L : ℝ := max Λ₀ 1 with hL
  have hL1 : 1 ≤ L := le_max_right _ _
  have hL0 : 0 < 3 * L := by linarith
  set C₂ : ℝ := max C₁ 0 with hC₂
  refine ⟨fun c => C₂ * (3 * L) ^ s * ‖(fun j => (cosetRow Γ c j : ℝ))‖ ^ (-s), ?_, ?_⟩
  · have hr : -s < -3 := by
      rw [hs]; have : (4 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h1 := summable_intVec_norm_rpow hr
    have h2 : Summable ((fun v : Fin 3 → ℤ => ‖(fun j => (v j : ℝ))‖ ^ (-s)) ∘ cosetRow Γ) :=
      h1.comp_injective (cosetRow_injective Γ)
    exact (h2.mul_left (C₂ * (3 * L) ^ s))
  · intro q hq i j m c
    induction c using Quotient.inductionOn with | _ a => ?_
    rw [cosetTerm_mk]
    set g := realMat a.1 with hg
    have hdet : g.det = 1 := det_realMat a.1
    have hqΩ := hKΩ hq
    have hT := (planeAct_mem hdet hqΩ).2
    have hbound := hC₁ g hdet q hq i j m
    -- comparison of the normal height with the bottom row
    have hrow : ‖fun j : Fin 3 => g 2 j‖ ≤ 3 * L * planeAct g q 4 :=
      norm_bottomRow_le hdet hqΩ L (fun l j' => (hΛ₀ q hq l j').trans (le_max_left _ _))
    have hvec : (fun j : Fin 3 => g 2 j) = fun j => ((cosetRow Γ (Quotient.mk _ a) j : ℤ) : ℝ) := by
      funext j
      simp [hg, realMat_apply, cosetRow, bottomRowZ]
    rw [hvec] at hrow
    set v : ℝ := ‖fun j => ((cosetRow Γ (Quotient.mk _ a) j : ℤ) : ℝ)‖ with hv
    have hvpos : 0 < v := by
      rw [hv, norm_pos_iff]
      intro h0
      apply bottomRowZ_ne_zero a.1
      funext j
      have := congrFun h0 j
      simpa [cosetRow, bottomRowZ] using this
    have hX : v / (3 * L) ≤ planeAct g q 4 := by
      rw [div_le_iff₀ hL0]; linarith
    have hpow : (v / (3 * L)) ^ s ≤ (Real.sqrt (planeAct g q 4)) ^ (n + 3) := by
      rw [sqrt_pow_eq_rpow _ hT.le]
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
end Convergence2

end TernaryPeriodPolynomials.Argument.ConvergenceC4
