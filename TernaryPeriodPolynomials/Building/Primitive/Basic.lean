module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


open MvPolynomial

namespace TernaryPoly

/-- Every rational polynomial has an integral multiple with integer coefficients. -/
theorem exists_integral_multiple {σ : Type*} (f : MvPolynomial σ ℚ) :
    ∃ a : ℤ, a ≠ 0 ∧ ∃ p : MvPolynomial σ ℤ,
      map (Int.castRingHom ℚ) p = (a : ℚ) • f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    refine ⟨r.den, by exact_mod_cast r.den_nz, monomial d r.num, ?_⟩
    rw [map_monomial, smul_monomial]
    congr 1
    simp [Rat.den_mul_eq_num]
  | add f g hf hg =>
    obtain ⟨a, ha, p, hp⟩ := hf
    obtain ⟨b, hb, q, hq⟩ := hg
    refine ⟨a*b, mul_ne_zero ha hb, b • p + a • q, ?_⟩
    simp only [map_add, map_zsmul, hp, hq, Int.cast_mul,
      ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_add]
    rw [mul_comm (b : ℚ) (a : ℚ)]

/-- A nonzero integer polynomial is divisible by only finitely many powers of two. -/
theorem finiteMultiplicity_two_polynomial {σ : Type*} {p : MvPolynomial σ ℤ}
    (hp : p ≠ 0) : FiniteMultiplicity (MvPolynomial.C (2 : ℤ)) p := by
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hp
  have hc : FiniteMultiplicity (2 : ℤ) (p.coeff d) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hd⟩
  obtain ⟨n, hn⟩ := FiniteMultiplicity.def.mp hc
  refine FiniteMultiplicity.def.mpr ⟨n, ?_⟩
  intro h
  rw [← map_pow] at h
  exact hn ((C_dvd_iff_dvd_coeff _ p).mp h d)

/-- Remove the largest common power of two from all coefficients. -/
theorem exists_two_primitive_factor {σ : Type*} {p : MvPolynomial σ ℤ}
    (hp : p ≠ 0) :
    ∃ n : ℕ, ∃ q : MvPolynomial σ ℤ,
      p = MvPolynomial.C ((2 : ℤ)^n) * q ∧
      map (Int.castRingHom (ZMod 2)) q ≠ 0 := by
  have hfinite := finiteMultiplicity_two_polynomial hp
  obtain ⟨q, hq, hnot⟩ := hfinite.exists_eq_pow_mul_and_not_dvd
  refine ⟨multiplicity (MvPolynomial.C (2 : ℤ)) p, q, ?_, ?_⟩
  · simpa only [map_pow] using hq
  · intro hz
    apply hnot
    exact (C_dvd_iff_map_hom_eq_zero (Int.castRingHom (ZMod 2)) (2 : ℤ)
      (CharP.intCast_eq_zero_iff (ZMod 2) 2) q).mpr hz

/-- Every nonzero rational polynomial has an integral scaling nonzero modulo two. -/
theorem exists_primitive_integral_multiple {σ : Type*} {f : MvPolynomial σ ℚ}
    (hf : f ≠ 0) :
    ∃ a : ℚ, a ≠ 0 ∧ ∃ p : MvPolynomial σ ℤ,
      map (Int.castRingHom ℚ) p = a • f ∧
      map (Int.castRingHom (ZMod 2)) p ≠ 0 := by
  obtain ⟨a, ha, p, hp⟩ := exists_integral_multiple f
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hp
    exact (smul_ne_zero haQ hf) hp.symm
  obtain ⟨n, q, hq, hmod⟩ := exists_two_primitive_factor hp0
  have ht : (2 : ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hscale : (2 : ℚ)^n • map (Int.castRingHom ℚ) q = (a : ℚ) • f := by
    rw [hq, map_mul, map_C] at hp
    simpa only [map_pow, map_ofNat,
      Algebra.smul_def, algebraMap_eq] using hp
  refine ⟨((2 : ℚ)^n)⁻¹ * (a : ℚ), mul_ne_zero (inv_ne_zero ht) haQ, q, ?_, hmod⟩
  calc
    map (Int.castRingHom ℚ) q =
        ((2 : ℚ)^n)⁻¹ • ((2 : ℚ)^n • map (Int.castRingHom ℚ) q) := by
      rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    _ = (((2 : ℚ)^n)⁻¹ * (a : ℚ)) • f := by rw [hscale, smul_smul]

end TernaryPoly
