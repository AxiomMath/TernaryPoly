module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Data.Fin.Parity
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Alternating two-forms on `ℝ⁵` from their components

For `c : Fin 5 → Fin 5 → F` the map
`(v, w) ↦ ∑ₐ∑_b ½ (vₐ w_b - v_b wₐ) • c a b`
is an alternating continuous bilinear map `altRaw c : ℝ⁵ [⋀^Fin 2]→L[ℝ] F`, linear in `c`
(`altCLM`), whose value on the coordinate vectors `(eᵢ, eⱼ)` is `½ (c i j - c j i)`; for an
antisymmetric family of components it is `c i j` (`altRaw_basis_of_antisymm`) and
`(v, w) ↦ ∑ vₐ w_b c a b` (`altRaw_apply_of_antisymm`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The (antisymmetrized) bilinear expression of the components `c a b`, as a function of the pair of
tangent vectors. -/
def altFun (c : Fin 5 → Fin 5 → F) (v : Fin 2 → (Fin 5 → ℝ)) : F :=
  ∑ a, ∑ b, ((1 / 2 : ℝ) * (v 0 a * v 1 b - v 0 b * v 1 a)) • c a b

theorem altFun_update0 (c : Fin 5 → Fin 5 → F) (v : Fin 2 → (Fin 5 → ℝ)) (x : Fin 5 → ℝ) :
    altFun c (Function.update v 0 x) =
      ∑ a, ∑ b, ((1 / 2 : ℝ) * (x a * v 1 b - x b * v 1 a)) • c a b := by
  simp [altFun]

theorem altFun_update1 (c : Fin 5 → Fin 5 → F) (v : Fin 2 → (Fin 5 → ℝ)) (x : Fin 5 → ℝ) :
    altFun c (Function.update v 1 x) =
      ∑ a, ∑ b, ((1 / 2 : ℝ) * (v 0 a * x b - v 0 b * x a)) • c a b := by
  simp [altFun]

/-- `altFun c` is multilinear in the two tangent vectors. -/
def altMulti (c : Fin 5 → Fin 5 → F) : MultilinearMap ℝ (fun _ : Fin 2 => Fin 5 → ℝ) F where
  toFun := altFun c
  map_update_add' := by
    intro d v i x y
    obtain rfl : d = instDecidableEqFin 2 := Subsingleton.elim _ _
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · simp only [altFun_update0, ← Finset.sum_add_distrib, ← add_smul, Pi.add_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1; ring
    · simp only [altFun_update1, ← Finset.sum_add_distrib, ← add_smul, Pi.add_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1; ring
  map_update_smul' := by
    intro d v i r x
    obtain rfl : d = instDecidableEqFin 2 := Subsingleton.elim _ _
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · change altFun c _ = r • altFun c _
      simp only [altFun_update0, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1; ring
    · change altFun c _ = r • altFun c _
      simp only [altFun_update1, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1; ring

theorem continuous_altFun (c : Fin 5 → Fin 5 → F) : Continuous (altFun c) := by
  unfold altFun
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  fun_prop

/-- **The alternating continuous bilinear map with components `c`.** -/
def altRaw (c : Fin 5 → Fin 5 → F) : (Fin 5 → ℝ) [⋀^Fin 2]→L[ℝ] F where
  toContinuousMultilinearMap := ⟨altMulti c, continuous_altFun c⟩
  map_eq_zero_of_eq' v i j hv hij := by
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    show altFun c v = 0
    unfold altFun
    rw [← h01]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [show v 0 a * v 0 b - v 0 b * v 0 a = 0 by ring, mul_zero, zero_smul]

theorem altRaw_apply (c : Fin 5 → Fin 5 → F) (v : Fin 2 → (Fin 5 → ℝ)) :
    altRaw c v = ∑ a, ∑ b, ((1 / 2 : ℝ) * (v 0 a * v 1 b - v 0 b * v 1 a)) • c a b := rfl

theorem altRaw_add (c c' : Fin 5 → Fin 5 → F) : altRaw (c + c') = altRaw c + altRaw c' := by
  ext v
  simp only [ContinuousAlternatingMap.add_apply, altRaw_apply, Pi.add_apply, smul_add,
    Finset.sum_add_distrib]

theorem altRaw_smul (r : ℝ) (c : Fin 5 → Fin 5 → F) : altRaw (r • c) = r • altRaw c := by
  ext v
  simp only [ContinuousAlternatingMap.smul_apply, altRaw_apply, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [smul_comm]

/-- The linear map `c ↦ altRaw c` (continuous because the space of components is finite
dimensional). -/
def altLin : (Fin 5 → Fin 5 → F) →ₗ[ℝ] (Fin 5 → ℝ) [⋀^Fin 2]→L[ℝ] F where
  toFun := altRaw
  map_add' := altRaw_add
  map_smul' := altRaw_smul

theorem altLin_apply (c : Fin 5 → Fin 5 → F) : altLin c = altRaw c := rfl

/-- The antisymmetrization is harmless for antisymmetric components. -/
theorem altRaw_apply_of_antisymm (c : Fin 5 → Fin 5 → F) (hc : ∀ a b, c a b = - c b a)
    (v : Fin 2 → (Fin 5 → ℝ)) :
    altRaw c v = ∑ a, ∑ b, (v 0 a * v 1 b) • c a b := by
  rw [altRaw_apply]
  have h2 : ∑ a, ∑ b, (v 0 b * v 1 a) • c a b = - ∑ a, ∑ b, (v 0 a * v 1 b) • c a b := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hc a b, hc b a, neg_neg, smul_neg]
  have e : ∑ a, ∑ b, ((1 / 2 : ℝ) * (v 0 a * v 1 b - v 0 b * v 1 a)) • c a b =
      (1 / 2 : ℝ) • (∑ a, ∑ b, (v 0 a * v 1 b) • c a b) -
        (1 / 2 : ℝ) • ∑ a, ∑ b, (v 0 b * v 1 a) • c a b := by
    simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, mul_smul, Finset.smul_sum]
  rw [e, h2]
  module

/-- The value on the coordinate vectors `(eᵢ, eⱼ)`. -/
theorem altRaw_basis (c : Fin 5 → Fin 5 → F) (i j : Fin 5) :
    altRaw c ![Pi.single i 1, Pi.single j 1] = (1 / 2 : ℝ) • (c i j - c j i) := by
  rw [altRaw_apply]
  simp [Pi.single_apply, mul_sub, sub_smul, Finset.sum_sub_distrib, smul_sub, eq_comm]

/-- For antisymmetric components, the value on `(eᵢ, eⱼ)` is the component `c i j`. -/
theorem altRaw_basis_of_antisymm (c : Fin 5 → Fin 5 → F) (hc : ∀ a b, c a b = - c b a)
    (i j : Fin 5) : altRaw c ![Pi.single i 1, Pi.single j 1] = c i j := by
  rw [altRaw_basis, hc j i, sub_neg_eq_add, ← two_smul ℝ (c i j), smul_smul]
  norm_num

/-- Two alternating two-forms on `ℝ⁵` agreeing on all pairs of coordinate vectors are equal. -/
theorem ext2 {f g : (Fin 5 → ℝ) [⋀^Fin 2]→L[ℝ] F}
    (h : ∀ i j, f ![Pi.single i 1, Pi.single j 1] = g ![Pi.single i 1, Pi.single j 1]) :
    f = g := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine (Pi.basisFun ℝ (Fin 5)).ext_alternating ?_
  intro v _
  have hv : (fun k => (Pi.basisFun ℝ (Fin 5)) (v k)) =
      ![Pi.single (v 0) 1, Pi.single (v 1) 1] := by
    funext k; fin_cases k <;> simp
  rw [hv]
  exact h (v 0) (v 1)

section Continuous

variable [FiniteDimensional ℝ F]

/-- **`c ↦ altRaw c` as a continuous linear map** (the space of components is finite dimensional). -/
def altCLM : (Fin 5 → Fin 5 → F) →L[ℝ] (Fin 5 → ℝ) [⋀^Fin 2]→L[ℝ] F :=
  LinearMap.toContinuousLinearMap altLin

theorem altCLM_apply (c : Fin 5 → Fin 5 → F) : altCLM c = altRaw c := rfl

end Continuous

end TernaryPeriodPolynomials.Argument.EisensteinClass
