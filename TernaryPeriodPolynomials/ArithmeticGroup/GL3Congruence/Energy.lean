module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Basic.UnivLE
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
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


open Finset
noncomputable section
namespace TernaryPoly.IntegralGL3Congruence

variable {ι : Type} [Fintype ι]

/-- The integral sum of squared coordinates over one complete finite linear orbit. -/
def orbitEnergy (L : Module.End ℤ (ι → ℤ)) (m : ℕ) (v : ι → ℤ) : ℤ :=
  ∑ k ∈ Finset.range m,∑ i,((L^k) v i)^2

theorem orbitEnergy_nonneg (L : Module.End ℤ (ι → ℤ)) (m : ℕ) (v : ι → ℤ) :
    0≤orbitEnergy L m v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp] theorem orbitEnergy_zero (L : Module.End ℤ (ι → ℤ)) (m : ℕ) :
    orbitEnergy L m 0=0 := by simp [orbitEnergy]

/-- A positive-length orbit energy detects the zero lattice vector. -/
theorem orbitEnergy_eq_zero_iff (L : Module.End ℤ (ι → ℤ)) (m : ℕ) (hm : 0<m)
    (v : ι → ℤ) : orbitEnergy L m v=0 ↔ v=0 := by
  constructor
  · intro h
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k (_ : k∈Finset.range m) =>
      Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => sq_nonneg ((L^k) v i)))).mp h
    have h0 := hk 0 (Finset.mem_range.mpr hm)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i∈Finset.univ) =>
      sq_nonneg ((L^0) v i))).mp h0
    funext i
    have hz := hi i (Finset.mem_univ i)
    simpa using (sq_eq_zero_iff.mp hz)
  · rintro rfl
    exact orbitEnergy_zero L m

theorem orbitEnergy_pos (L : Module.End ℤ (ι → ℤ)) (m : ℕ) (hm : 0<m)
    (v : ι → ℤ) (hv : v≠0) : 0<orbitEnergy L m v := by
  have hn := orbitEnergy_nonneg L m v
  have he : orbitEnergy L m v≠0 := by
    intro h
    exact hv ((orbitEnergy_eq_zero_iff L m hm v).mp h)
  omega

/-- Integral scalar dilation multiplies orbit energy by its square. -/
theorem orbitEnergy_smul (L : Module.End ℤ (ι → ℤ)) (m : ℕ) (c : ℤ) (v : ι → ℤ) :
    orbitEnergy L m (c • v)=c^2*orbitEnergy L m v := by
  simp only [orbitEnergy,LinearMap.map_smul_of_tower,Pi.smul_apply,smul_eq_mul,mul_pow,
    Finset.mul_sum]

/-- The elementary squared-difference bound holds in the averaged integral form. -/
theorem orbitEnergy_sub_le (L : Module.End ℤ (ι → ℤ)) (m : ℕ) (v w : ι → ℤ) :
    orbitEnergy L m (v-w)≤2*orbitEnergy L m v+2*orbitEnergy L m w := by
  calc
    orbitEnergy L m (v-w)≤∑ k∈Finset.range m,∑i,
        (2*((L^k) v i)^2+2*((L^k) w i)^2) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro i _
      simp only [map_sub,Pi.sub_apply]
      nlinarith [sq_nonneg ((L^k) v i+(L^k) w i)]
    _=2*orbitEnergy L m v+2*orbitEnergy L m w := by
      simp [orbitEnergy,Finset.sum_add_distrib,Finset.mul_sum]

/-- Averaging over a full period makes the integral energy exactly invariant. -/
theorem orbitEnergy_apply (L : Module.End ℤ (ι → ℤ)) (m : ℕ) (hp : L^m=1)
    (v : ι → ℤ) : orbitEnergy L m (L v)=orbitEnergy L m v := by
  let f : ℕ → ℤ := fun k => ∑i,((L^k) v i)^2
  have hperiod : f m=f 0 := by simp [f,hp]
  have hs := Finset.sum_range_succ' f m
  rw [Finset.sum_range_succ,hperiod] at hs
  have hshift : (∑k∈Finset.range m,f (k+1))=∑k∈Finset.range m,f k := by
    linear_combination -hs
  change (∑k∈Finset.range m,∑i,((L^k) (L v) i)^2)=_
  have hf (k : ℕ) : (∑i,((L^k) (L v) i)^2)=f (k+1) := by
    simp only [f,pow_succ,Module.End.mul_apply]
  simp only [hf]
  exact hshift

end TernaryPoly.IntegralGL3Congruence
