module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.ValueBound
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.PSeries
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal

@[expose] public section


/-!
# Normal height versus bottom row; summability over `ℤ³` (Appendix C.3, Proposition C.4)

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### Comparison of the normal height with the bottom row -/

/-- The bottom row of `g` is bounded by `3 Λ t(g q)`, `t = (planeAct g q) 4`. -/
theorem bottomRow_le {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) (Λ : ℝ) (hΛ : ∀ l j, |planePinv q l j| ≤ Λ) (j : Fin 3) :
    |g 2 j| ≤ 3 * Λ * planeAct g q 4 := by
  have hq'' := planeAct_mem hg hq
  set w : Fin 3 → ℝ := fun l => ∑ i : Fin 3, g 2 i * planeP q i l with hw
  have hG : (g * planeGram q * g.transpose) 2 2 = ∑ l : Fin 3, w l ^ 2 := by
    rw [← planeP_mul_transpose hq, conj_apply]
    have := quad_rowvec (fun i => g 2 i) (planeP q)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] at this ⊢
    simp only [hw, Fin.sum_univ_three]
    linarith
  have hT : planeAct g q 4 = Real.sqrt (∑ l : Fin 3, w l ^ 2) := by
    show planePoint (g * planeGram q * g.transpose) 4 = _
    rw [planePoint_four, hG]
  have hwl : ∀ l, |w l| ≤ planeAct g q 4 := by
    intro l
    rw [hT]
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun l => w l ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ l)
  have hgw : g 2 j = ∑ l : Fin 3, w l * planePinv q l j := by
    have : g = (g * planeP q) * planePinv q := by
      rw [Matrix.mul_assoc, planeP_mul_planePinv hq, Matrix.mul_one]
    conv_lhs => rw [this]
    simp [Matrix.mul_apply, hw]
  rw [hgw]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l : Fin 3, |w l * planePinv q l j|
      ≤ ∑ _l : Fin 3, planeAct g q 4 * Λ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hwl l) (hΛ l j) (abs_nonneg _) (planeAct_mem hg hq).2.le
    _ = 3 * Λ * planeAct g q 4 := by simp; ring

theorem norm_bottomRow_le {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) (Λ : ℝ) (hΛ : ∀ l j, |planePinv q l j| ≤ Λ) :
    ‖fun j : Fin 3 => g 2 j‖ ≤ 3 * Λ * planeAct g q 4 := by
  have h0 : 0 ≤ 3 * Λ * planeAct g q 4 := by
    have := bottomRow_le hg hq Λ hΛ 0
    exact (abs_nonneg _).trans this
  refine (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  simpa using bottomRow_le hg hq Λ hΛ j

/-! ### The lattice `ℤ³` and summability of `‖v‖^r` -/

/-- The integer lattice `ℤ³ ⊂ ℝ³`. -/
abbrev latticeZ3 : Submodule ℤ (Fin 3 → ℝ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))

theorem intVec_mem_latticeZ3 (v : Fin 3 → ℤ) : (fun j => (v j : ℝ)) ∈ latticeZ3 := by
  have : (fun j => (v j : ℝ)) = ∑ j : Fin 3, (v j) • (Pi.basisFun ℝ (Fin 3) j : Fin 3 → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem finrank_latticeZ3 : Module.finrank ℤ latticeZ3 = 3 := by
  have := ZLattice.rank ℝ latticeZ3
  rw [this]
  simp

/-- The embedding of `ℤ³` into the lattice. -/
def intVecToLattice (v : Fin 3 → ℤ) : latticeZ3 := ⟨fun j => (v j : ℝ), intVec_mem_latticeZ3 v⟩

theorem intVecToLattice_injective : Function.Injective intVecToLattice := by
  intro v w h
  funext j
  have h' := congrArg Subtype.val h
  have := congrFun h' j
  simp only [intVecToLattice] at this
  exact_mod_cast this

/-- `∑_{v ∈ ℤ³ ∖ 0} ‖v‖^r` converges for `r < -3`. -/
theorem summable_intVec_norm_rpow {r : ℝ} (hr : r < -3) :
    Summable fun v : Fin 3 → ℤ => ‖(fun j => (v j : ℝ))‖ ^ r := by
  have hs : Summable fun z : latticeZ3 => ‖z‖ ^ r :=
    ZLattice.summable_norm_rpow latticeZ3 r (by rw [finrank_latticeZ3]; exact_mod_cast hr)
  have h2 : Summable ((fun z : latticeZ3 => ‖z‖ ^ r) ∘ intVecToLattice) :=
    hs.comp_injective intVecToLattice_injective
  refine h2.congr fun v => ?_
  rfl

end TernaryPeriodPolynomials.Argument.ConvergenceC4
