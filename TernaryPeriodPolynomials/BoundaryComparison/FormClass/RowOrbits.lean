module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.RowDictionary

@[expose] public section


/-!
# (C), step 3b: the rational points of the intertwiner and the orbits of the line radical lattice

Formalized by Claude Sonnet 5.5.

`ptC c ∈ ℚ²` is the point `(ρ₁/ρ₀, ρ₂/ρ₀)` of the bottom row `ρ` of the coset `c ∈ Γ_P\Γ(N)`.
* `ptC_latQ`: the lattice action shifts `ptC` by `N ℓ`.
* `orbit_of_pt_shift`: cosets whose points differ by `N ℤ²` lie in one orbit of the line radical lattice (uses `decomp_ratio`).
* `exists_coset_of_decomp`: if `w₀⁻¹ u(r)` is decomposable (`∈ P(ℚ) K(N)`) then `r = ptC c` for a coset `c` with `ρ₀ ≠ 0`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

theorem rationalFinite_injective : Function.Injective rationalFinite := by
  intro g h hgh
  let v0 : FinitePlace := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  apply Units.ext
  ext i j
  have := congrArg (fun x : FiniteGL => (x : Matrix (Fin 3) (Fin 3) FiniteAdeles) i j) hgh
  simp only [rationalFinite, GeneralLinearGroup.map_apply] at this
  have h2 := congrArg (finiteEvaluation v0) this
  simp only [finiteEvaluation_rational] at h2
  exact (algebraMap ℚ (v0.adicCompletion ℚ)).injective h2

theorem mapGL_rat_injective : Function.Injective (Matrix.SpecialLinearGroup.mapGL ℚ : SL(3, ℤ) → GL3 ℚ) := by
  intro a b hab
  apply Subtype.ext
  ext i j
  have := congrArg (fun x : GL3 ℚ => (x : Matrix (Fin 3) (Fin 3) ℚ) i j) hab
  simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    algebraMap_int_eq, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom] at this
  exact_mod_cast this

variable (N : ℕ) [NeZero N]

/-- The rational point of a coset of the standard cusp. -/
def ptC (c : Ck N 1) : ℚ × ℚ := rowPt (cuspRow (gammaN N) (CuspData.ofSL 1).r c)

omit [NeZero N] in
theorem cuspRow_one (c : Ck N 1) (j : Fin 3) :
    cuspRow (gammaN N) (CuspData.ofSL 1).r c j = ((Quotient.out c).1 : Matrix (Fin 3) (Fin 3) ℤ) 2 j := by
  rw [cuspRow_out, one_mul]

omit [NeZero N] in
theorem ptC_out (c : Ck N 1) : ptC N c = slRowPt (Quotient.out c).1 := by
  unfold ptC slRowPt rowPt
  rw [cuspRow_one, cuspRow_one, cuspRow_one]

omit [NeZero N] in
theorem ptC_latQ (ℓ : Fin 2 → ℤ) (c : Ck N 1) (h0 : cuspRow (gammaN N) (CuspData.ofSL 1).r c 0 ≠ 0) :
    ptC N (cmulR N 1 (latQ N ℓ) c) = ((ptC N c).1 - N * ℓ 1, (ptC N c).2 - N * ℓ 0) := by
  obtain ⟨e0, e1, e2⟩ := cuspRow_latK N 1 ℓ c
  have h0' : ((cuspRow (gammaN N) (CuspData.ofSL 1).r c 0 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h0
  unfold ptC rowPt
  rw [e0, e1, e2]
  push_cast
  ext <;> simp <;> field_simp

/-- **The cover**: if `w₀⁻¹ u(r)` is decomposable, `r` is the point of a coset of `Γ(N)` with `ρ₀ ≠ 0`. -/
theorem exists_elt_of_decomp (r : ℚ × ℚ)
    (h : ∃ π κ, IsDecomp N (gFin (algebraMap ℚ FiniteAdeles r.1, algebraMap ℚ FiniteAdeles r.2)) π κ) :
    ∃ a : SL(3, ℤ), a ∈ gammaN N ∧ (a : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0 ∧ slRowPt a = r := by
  obtain ⟨π, κ, hd⟩ := h
  set X : GL3 ℚ := weyl⁻¹ * upperUnipotent r.1 r.2 with hX
  have h1 : rationalFinite (π⁻¹ * X) = GeneralLinearGroup.map integralEmbedding κ := by
    have e : rationalFinite X = rationalFinite π * GeneralLinearGroup.map integralEmbedding κ := by
      rw [← gFin_rational r]; exact hd.eq
    rw [map_mul, map_inv, e, inv_mul_cancel_left]
  have hdet : (π⁻¹ * X).val.det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hd.ppos.inv.det, hX, weylInvU_val, Matrix.det_fin_three]
    simp
  obtain ⟨w, hwN, hw⟩ := gammaN_of_rat_levelKernel N (π⁻¹ * X) hdet κ hd.ker h1
  have hXe : X.val = π.val * (π⁻¹ * X).val := by rw [← Units.val_mul]; congr 1; group
  have row : ∀ j, X.val 2 j = π.val 2 2 * ((w : Matrix (Fin 3) (Fin 3) ℤ) 2 j : ℚ) := by
    intro j
    rw [hXe, Matrix.mul_apply, Fin.sum_univ_three, hd.ppos.mem.1, hd.ppos.mem.2, hw 2 j]
    ring
  have e0 : X.val 2 0 = 1 := by rw [hX, weylInvU_val]; simp
  have e1 : X.val 2 1 = r.1 := by rw [hX, weylInvU_val]; simp
  have e2 : X.val 2 2 = r.2 := by rw [hX, weylInvU_val]; simp
  have hw0 : ((w : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ) ≠ 0 := by
    intro h0
    have := row 0
    rw [e0, h0, mul_zero] at this
    exact one_ne_zero this
  refine ⟨w, hwN, by exact_mod_cast hw0, ?_⟩
  have p22 : π.val 2 2 = (((w : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ))⁻¹ := by
    have := row 0
    rw [e0] at this
    field_simp
    linarith
  unfold slRowPt rowPt
  ext
  · simp only
    rw [← e1, row 1, p22]; field_simp
  · simp only
    rw [← e2, row 2, p22]; field_simp

omit [NeZero N] in
theorem upper_latQ (m : Fin 2 → ℤ) :
    upperUnipotent (algebraMap ℚ FiniteAdeles ((N : ℚ) * m 0)) (algebraMap ℚ FiniteAdeles ((N : ℚ) * m 1)) =
      rationalFinite (Matrix.SpecialLinearGroup.mapGL ℚ (latQ N ![-(m 1), -(m 0)]).1) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalFinite, upperUnipotent, latQ_val, Matrix.SpecialLinearGroup.mapGL_coe_matrix]

/-- **Cosets whose points differ by `N ℤ²` lie in one orbit of the line radical lattice.** -/
theorem orbit_of_pt_shift_elt (hN : 3 ≤ N) {a a' : ↥(gammaN N)}
    (h0a : (a.1 : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0) (h0a' : (a'.1 : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0)
    (m : Fin 2 → ℤ) (h : slRowPt a'.1 = ((slRowPt a.1).1 + N * m 0, (slRowPt a.1).2 + N * m 1)) :
    cmulR N 1 (latQ N ![-(m 1), -(m 0)]) (Quotient.mk _ a) = (Quotient.mk _ a' : Ck N 1) := by
  set ℓ : Fin 2 → ℤ := ![-(m 1), -(m 0)] with hℓ
  set L : SL(3, ℤ) := (latQ N ℓ).1 with hL
  have hLN : L ∈ gammaN N := (latQ N ℓ).2
  have D1 := decomp_gFin N a'.2 h0a'
  have D2 := (decomp_gFin N a.2 h0a).mul_ker N (mapGL_mem_levelKernel N hLN)
  have hg : gFin (algebraMap ℚ FiniteAdeles (slRowPt a'.1).1, algebraMap ℚ FiniteAdeles (slRowPt a'.1).2) =
      gFin (algebraMap ℚ FiniteAdeles (slRowPt a.1).1, algebraMap ℚ FiniteAdeles (slRowPt a.1).2) *
        GeneralLinearGroup.map integralEmbedding (Matrix.SpecialLinearGroup.mapGL IntegralAdeles L) := by
    rw [← rationalFinite_mapGL, hL, ← upper_latQ N m, h]
    have : (algebraMap ℚ FiniteAdeles ((slRowPt a.1).1 + N * m 0), algebraMap ℚ FiniteAdeles ((slRowPt a.1).2 + N * m 1)) =
        (algebraMap ℚ FiniteAdeles (slRowPt a.1).1, algebraMap ℚ FiniteAdeles (slRowPt a.1).2) +
          (algebraMap ℚ FiniteAdeles ((N : ℚ) * m 0), algebraMap ℚ FiniteAdeles ((N : ℚ) * m 1)) := by
      simp only [map_add]; rfl
    simp only
    rw [this, gFin_add]
  rw [hg] at D1
  obtain ⟨w, hw, hwe⟩ := decomp_ratio N hN D2 D1
  have key : (piOf (slRowPt a'.1) a'.1) * Matrix.SpecialLinearGroup.mapGL ℚ a'.1 =
      (piOf (slRowPt a.1) a.1) * Matrix.SpecialLinearGroup.mapGL ℚ (a.1 * L) := by
    apply rationalFinite_injective
    have e1 := D1.eq
    rw [← rationalFinite_mapGL L, ← rationalFinite_mapGL a'.1] at e1
    have e2 := D2.eq
    rw [map_mul, ← rationalFinite_mapGL L, ← rationalFinite_mapGL a.1] at e2
    simp only [map_mul]
    exact e1.symm.trans e2
  have h1 : a'.1 = w * (a.1 * L) := by
    apply mapGL_rat_injective
    calc Matrix.SpecialLinearGroup.mapGL ℚ a'.1
        = (piOf (slRowPt a'.1) a'.1)⁻¹ * ((piOf (slRowPt a'.1) a'.1) * Matrix.SpecialLinearGroup.mapGL ℚ a'.1) := by
          group
      _ = (piOf (slRowPt a'.1) a'.1)⁻¹ * ((piOf (slRowPt a.1) a.1) * Matrix.SpecialLinearGroup.mapGL ℚ (a.1 * L)) := by
          rw [key]
      _ = ((piOf (slRowPt a'.1) a'.1)⁻¹ * piOf (slRowPt a.1) a.1) * Matrix.SpecialLinearGroup.mapGL ℚ (a.1 * L) := by
          group
      _ = _ := by rw [hwe]; simp only [map_mul]
  rw [cmulR_mk]
  apply Quotient.sound
  refine QuotientGroup.rightRel_apply.2 (Subgroup.mem_subgroupOf.2 ?_)
  have e : ((a' * (a * latQ N ℓ)⁻¹ : ↥(gammaN N)) : SL(3, ℤ)) = w := by
    have : ((a' * (a * latQ N ℓ)⁻¹ : ↥(gammaN N)) : SL(3, ℤ)) = a'.1 * (a.1 * L)⁻¹ := by
      simp [hL]
    rw [this, h1]; group
  rw [e]
  exact (mem_stabRow_ofSL 1 w).2 (by simpa using hw.2)

omit [NeZero N] in
theorem cuspRow_ne_zero_iff (c : Ck N 1) :
    cuspRow (gammaN N) (CuspData.ofSL 1).r c 0 ≠ 0 ↔ ((Quotient.out c).1 : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0 := by
  rw [cuspRow_one]

/-- **Orbit criterion at the level of cosets.** -/
theorem orbit_of_pt_shift (hN : 3 ≤ N) {c c' : Ck N 1}
    (h0 : cuspRow (gammaN N) (CuspData.ofSL 1).r c 0 ≠ 0) (h0' : cuspRow (gammaN N) (CuspData.ofSL 1).r c' 0 ≠ 0)
    (m : Fin 2 → ℤ) (h : ptC N c' = ((ptC N c).1 + N * m 0, (ptC N c).2 + N * m 1)) :
    ∃ ℓ : Fin 2 → ℤ, cmulR N 1 (latQ N ℓ) c = c' := by
  have := orbit_of_pt_shift_elt N hN (a := Quotient.out c) (a' := Quotient.out c')
    ((cuspRow_ne_zero_iff N c).1 h0) ((cuspRow_ne_zero_iff N c').1 h0') m
    (by rw [← ptC_out, ← ptC_out]; exact h)
  rw [Quotient.out_eq, Quotient.out_eq] at this
  exact ⟨_, this⟩

end TernaryPeriodPolynomials.Argument.FormClassK
