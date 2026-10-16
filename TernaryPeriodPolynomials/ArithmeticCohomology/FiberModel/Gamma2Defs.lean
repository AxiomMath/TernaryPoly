module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# The binary group `Γ₂` and its generators (`eq:Gamma-presentation`)

`Γ₂ = {g ∈ GL₂(ℤ) : (0,1) g = (0,1) (mod 3)}` and the matrices
`U₀ = (1 0; 3 1)`, `T = (1 1; 0 1)`, `A₀ = U₀ T⁻¹ = (1 -1; 3 -2)`, `R₀ = diag(-1, 1)`,
`B₀ = U₀ R₀ = (-1 0; -3 1)` of the paper.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

/-- The integral general linear group in dimension two. -/
abbrev GL2Z : Type := Matrix.GeneralLinearGroup (Fin 2) ℤ

/-- The stabilizer of the covector `(0,1)` in `GL₂(𝔽₃)` for the right action. -/
def covStab : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) where
  carrier := {h | Matrix.vecMul (![0, 1] : Fin 2 → ZMod 3) h.val = ![0, 1]}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    rw [← Matrix.vecMul_vecMul, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    have h : Matrix.vecMul (Matrix.vecMul (![0, 1] : Fin 2 → ZMod 3) a.val) (a⁻¹).val =
        Matrix.vecMul (![0, 1] : Fin 2 → ZMod 3) 1 := by
      rw [Matrix.vecMul_vecMul, Units.mul_inv]
    rwa [ha, Matrix.vecMul_one] at h

/-- `Γ₂ = {g ∈ GL₂(ℤ) : (0,1) g = (0,1) (mod 3)}`. -/
def Gamma2 : Subgroup GL2Z :=
  covStab.comap (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3)))

theorem mem_Gamma2 (g : GL2Z) : g ∈ Gamma2 ↔ g.val 1 0 % 3 = 0 ∧ g.val 1 1 % 3 = 1 := by
  change Matrix.vecMul (![0, 1] : Fin 2 → ZMod 3)
      (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3)) g).val = ![0, 1] ↔ _
  have h0 : ∀ x : ℤ, (x : ZMod 3) = 0 ↔ x % 3 = 0 := fun x => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    omega
  have h1 : ∀ x : ℤ, (x : ZMod 3) = 1 ↔ x % 3 = 1 := fun x => by
    have := ZMod.intCast_eq_intCast_iff' x 1 3
    simp only [Int.cast_one] at this
    rw [this]
    norm_num
  constructor
  · intro h
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at e0 e1
    exact ⟨(h0 _).mp e0, (h1 _).mp e1⟩
  · rintro ⟨e0, e1⟩
    funext i
    fin_cases i
    · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
      exact (h0 _).mpr e0
    · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
      exact (h1 _).mpr e1

/-- `U₀ = (1 0; 3 1)`. -/
def U0 : GL2Z := ⟨!![1, 0; 3, 1], !![1, 0; -3, 1], by decide +kernel, by decide +kernel⟩
/-- `T = (1 1; 0 1)`. -/
def Tm : GL2Z := ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by decide +kernel, by decide +kernel⟩
/-- `A₀ = U₀ T⁻¹ = (1 -1; 3 -2)`, of order three. -/
def A0 : GL2Z := ⟨!![1, -1; 3, -2], !![-2, 1; -3, 1], by decide +kernel, by decide +kernel⟩
/-- `R₀ = diag(-1, 1)`, with `R₀ U₀ R₀ = U₀⁻¹`. -/
def R0 : GL2Z := ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by decide +kernel, by decide +kernel⟩
/-- `B₀ = U₀ R₀ = (-1 0; -3 1)`, an involution. -/
def B0 : GL2Z := ⟨!![-1, 0; -3, 1], !![-1, 0; -3, 1], by decide +kernel, by decide +kernel⟩

theorem A0_eq : A0 = U0 * Tm⁻¹ := by decide +kernel
theorem B0_eq : B0 = U0 * R0 := by decide +kernel
theorem A0_cube : A0 ^ 3 = 1 := by decide +kernel
theorem B0_sq : B0 ^ 2 = 1 := by decide +kernel
theorem R0_sq : R0 ^ 2 = 1 := by decide +kernel
theorem R0_U0 : R0 * U0 * R0 = U0⁻¹ := by decide +kernel
theorem R0_A0 : R0 * A0 * R0 = U0⁻¹ * A0⁻¹ * U0 := by decide +kernel
theorem B0_A0 : B0 * A0 * B0 = A0⁻¹ := by decide +kernel

theorem A0_mem : A0 ∈ Gamma2 := (mem_Gamma2 _).mpr (by decide +kernel)
theorem B0_mem : B0 ∈ Gamma2 := (mem_Gamma2 _).mpr (by decide +kernel)
theorem R0_mem : R0 ∈ Gamma2 := (mem_Gamma2 _).mpr (by decide +kernel)
theorem U0_mem : U0 ∈ Gamma2 := (mem_Gamma2 _).mpr (by decide +kernel)
theorem Tm_mem : Tm ∈ Gamma2 := (mem_Gamma2 _).mpr (by decide +kernel)

end TernaryPeriodPolynomials.Argument.FiberModel
