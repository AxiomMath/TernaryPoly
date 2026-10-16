module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CuspDecompK2

@[expose] public section


/-!
# Every cusp: orbits of the line radical lattice and their rational points

Formalized by Claude Sonnet 5.5.

For `k ∈ SL₃(ℤ)`: `ptCk k c` is the point `(ρ₁/ρ₀, ρ₂/ρ₀)` of the bottom row of `k a` for a representative `a` of the coset `c`;
`orbit_of_pt_shift_elt_K`: cosets whose points differ by `Nℤ²` lie in one orbit of the line radical lattice.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ))

/-- The rational point of a coset at the cusp `k`. -/
def ptCk (c : Ck N k) : ℚ × ℚ := rowPt (cuspRow (gammaN N) (CuspData.ofSL k).r c)

omit [NeZero N] in
theorem ptCk_out (c : Ck N k) : ptCk N k c = slRowPt (k * (Quotient.out c).1) := by
  unfold ptCk slRowPt rowPt
  rw [cuspRow_out, cuspRow_out, cuspRow_out]

omit [NeZero N] in
theorem ptCk_latQ (ℓ : Fin 2 → ℤ) (c : Ck N k) (h0 : cuspRow (gammaN N) (CuspData.ofSL k).r c 0 ≠ 0) :
    ptCk N k (cmulR N k (latQ N ℓ) c) = ((ptCk N k c).1 - N * ℓ 1, (ptCk N k c).2 - N * ℓ 0) := by
  obtain ⟨e0, e1, e2⟩ := cuspRow_latK N k ℓ c
  have h0' : ((cuspRow (gammaN N) (CuspData.ofSL k).r c 0 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h0
  unfold ptCk rowPt
  rw [e0, e1, e2]
  push_cast
  ext <;> simp <;> field_simp

omit [NeZero N] in
theorem cuspRow_ne_zero_iffK (c : Ck N k) :
    cuspRow (gammaN N) (CuspData.ofSL k).r c 0 ≠ 0 ↔
      ((k * (Quotient.out c).1 : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0 := by
  rw [cuspRow_out]

omit [NeZero N] in
theorem conj_mem_gammaN (a : SL(3, ℤ)) (ha : a ∈ gammaN N) : k * a * k⁻¹ ∈ gammaN N := by
  simpa using (gammaN_normal N).conj_mem a ha k

omit [NeZero N] in
/-- **Cosets whose points differ by `N ℤ²` lie in one orbit of the line radical lattice (cusp `k`).** -/
theorem orbit_of_pt_shift_elt_K (hN : 3 ≤ N) {a a' : ↥(gammaN N)}
    (h0a : ((k * a.1 : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0)
    (h0a' : ((k * a'.1 : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0)
    (m : Fin 2 → ℤ) (h : slRowPt (k * a'.1) = ((slRowPt (k * a.1)).1 + N * m 0, (slRowPt (k * a.1)).2 + N * m 1)) :
    cmulR N k (latQ N ![-(m 1), -(m 0)]) (Quotient.mk _ a) = (Quotient.mk _ a' : Ck N k) := by
  set ℓ : Fin 2 → ℤ := ![-(m 1), -(m 0)] with hℓ
  set L : SL(3, ℤ) := (latQ N ℓ).1 with hL
  have hLN : L ∈ gammaN N := (latQ N ℓ).2
  set r := slRowPt (k * a.1) with hr
  set r' := slRowPt (k * a'.1) with hr'
  have hg : gFin (algebraMap ℚ FiniteAdeles r'.1, algebraMap ℚ FiniteAdeles r'.2) =
      gFin (algebraMap ℚ FiniteAdeles r.1, algebraMap ℚ FiniteAdeles r.2) *
        rationalFinite (Matrix.SpecialLinearGroup.mapGL ℚ L) := by
    have e : (algebraMap ℚ FiniteAdeles r'.1, algebraMap ℚ FiniteAdeles r'.2) =
        (algebraMap ℚ FiniteAdeles r.1, algebraMap ℚ FiniteAdeles r.2) +
          (algebraMap ℚ FiniteAdeles ((N : ℚ) * m 0), algebraMap ℚ FiniteAdeles ((N : ℚ) * m 1)) := by
      rw [h]; simp only [map_add]; rfl
    rw [e, gFin_add, hL, ← upper_latQ N m]
  have hX : (weyl⁻¹ * upperUnipotent r'.1 r'.2 : GL3 ℚ) = (weyl⁻¹ * upperUnipotent r.1 r.2 : GL3 ℚ) *
      Matrix.SpecialLinearGroup.mapGL ℚ L := by
    apply rationalFinite_injective
    rw [← gFin_rational r', hg, gFin_rational r, ← map_mul]
  have hAN : k * a.1 * k⁻¹ ∈ gammaN N := conj_mem_gammaN N k a.1 a.2
  have hA'N : k * a'.1 * k⁻¹ ∈ gammaN N := conj_mem_gammaN N k a'.1 a'.2
  have key : piOf r' (k * a'.1) * Matrix.SpecialLinearGroup.mapGL ℚ (k * a'.1) =
      piOf r (k * a.1) * Matrix.SpecialLinearGroup.mapGL ℚ (k * a.1 * L) := by
    rw [piOf_mul, map_mul (Matrix.SpecialLinearGroup.mapGL ℚ) (k * a.1) L, ← mul_assoc, piOf_mul, hX]
  have hw : Matrix.SpecialLinearGroup.mapGL ℚ (k * a'.1 * (k * a.1 * L)⁻¹) = (piOf r' (k * a'.1))⁻¹ * piOf r (k * a.1) := by
    rw [map_mul, map_inv]
    calc _ = (piOf r' (k * a'.1))⁻¹ * (piOf r' (k * a'.1) * Matrix.SpecialLinearGroup.mapGL ℚ (k * a'.1)) *
          (Matrix.SpecialLinearGroup.mapGL ℚ (k * a.1 * L))⁻¹ := by group
      _ = _ := by rw [key]; group
  have hpar : (piOf r' (k * a'.1))⁻¹ * piOf r (k * a.1) ∈ planeParabolic ℚ :=
    (planeParabolic ℚ).mul_mem ((planeParabolic ℚ).inv_mem (piOf_mem _ h0a')) (piOf_mem _ h0a)
  set w'' : SL(3, ℤ) := k * a'.1 * (k * a.1 * L)⁻¹ with hw''
  have hw''N : w'' ∈ gammaN N := by
    have : w'' = k * (a'.1 * (a.1 * L)⁻¹) * k⁻¹ := by rw [hw'']; group
    rw [this]
    exact conj_mem_gammaN N k _ ((gammaN N).mul_mem a'.2 ((gammaN N).inv_mem ((gammaN N).mul_mem a.2 hLN)))
  have h20 : ((w'' : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℤ) = 0 := by
    have := hpar.1
    rw [← hw, Matrix.SpecialLinearGroup.mapGL_coe_matrix] at this
    simpa using this
  have h21 : ((w'' : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℤ) = 0 := by
    have := hpar.2
    rw [← hw, Matrix.SpecialLinearGroup.mapGL_coe_matrix] at this
    simpa using this
  have hstab := mem_planeStab_of_gammaN hN hw''N h20 h21
  rw [cmulR_mk]
  apply Quotient.sound
  refine QuotientGroup.rightRel_apply.2 (Subgroup.mem_subgroupOf.2 ?_)
  have e : ((a' * (a * latQ N ℓ)⁻¹ : ↥(gammaN N)) : SL(3, ℤ)) = a'.1 * (a.1 * L)⁻¹ := by simp [hL]
  rw [e, mem_stabRow_ofSL]
  have : k * (a'.1 * (a.1 * L)⁻¹) * k⁻¹ = w'' := by rw [hw'']; group
  rw [this]
  exact hstab

end TernaryPeriodPolynomials.Argument.FormClassK
