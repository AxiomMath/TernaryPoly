module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Hecke.RecursionCoeff
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.FhSL2Invariance
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.HermiteCount

@[expose] public section


/-!
# `eq:lattice-hecke` and `eq:cyclic-hecke` at finite coordinate one

Formalized by Claude Sonnet 5.5.

`eq_lattice_hecke_finite_one`: for a normalized level-one cusp eigenform `h`,
`∑_{t ∈ hnfData (p^r)} F_h(L_t⁻¹ g) = (p^r)^{1-k/2} a_h(p^r) F_h(g)` (`L_t = [[a,0],[b,d]]`).  It combines
`HeckeDictionaryCusp.sum_Fh_lower_cusp` (the sum is `m^{1-k/2} Nf(S⁻¹g) T_m h((S⁻¹g) i)`), `latticeOp_prime_pow_eq_coeff`
(`T_{p^r} h = a_h(p^r) h`) and `FhSL2Invariance.Fh_sl2_mul` for `S⁻¹ ∈ SL₂(ℤ)` (`Fh_Sgl_inv`), which removes the last `S⁻¹`.
No plane-transformation bridge is assumed: this is the real-coordinate Fh-form.  `eq_cyclic_hecke_finite_one`: subtracting the noncyclic
triples (`nonCyclicHNF_eq`, `Fh_Gl_scale`: `F_h(L_{pT}⁻¹ g) = F_h(L_T⁻¹ g)`) gives
`(p^r)^{1-k/2} {a_h(p^r) - p^{k-2} a_h(p^{r-2})} F_h(g)` with the convention `a_h(p^{-1}) = a_h(p^{-2}) = 0`.
-/

open Matrix UpperHalfPlane ModularForm
open TernaryPeriodPolynomials.Argument.LatticeCounts
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionaryCusp
open TernaryPeriodPolynomials.Argument.LatticeCounts.FhSL2Invariance
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (HasPrimeHeckeRelations)

open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeOperator
open Finset

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion

theorem Fh_Sgl_inv (k : ℤ) (h : CuspForm levelOne k) (X : GL (Fin 2) ℝ)
    (hX : 0 < (Matrix.GeneralLinearGroup.det X).val) : Fh k ⇑h (Sgl⁻¹ * X) = Fh k ⇑h X := by
  have e : sl2 Sint⁻¹ = Sgl⁻¹ := by
    show (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ) Sint⁻¹ = Sgl⁻¹
    rw [map_inv, Sint_map]
  rw [← e]
  exact Fh_sl2_mul k Sint⁻¹ X hX

/-- **`eq:lattice-hecke` at finite coordinate one**: for a normalized level-one cusp eigenform,
`∑_{[ℤ²:Λ]=p^r} F_h(A_Λ⁻¹ g) = (p^r)^{1-k/2} a_h(p^r) F_h(g)`, the sum over the Hermite triples of index `p^r` with
`A_t = [[a,0],[b,d]]`. -/
theorem eq_lattice_hecke_finite_one (k : ℤ) (h : CuspForm levelOne k) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations k h eigenvalues)
    (normalized : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1) (p : Nat.Primes) (r : ℕ)
    (g : GL (Fin 2) ℝ) (hg : 0 < (Matrix.GeneralLinearGroup.det g).val) :
    ∑ t ∈ hnfData (p.val ^ r), Fh k ⇑h (Gl t g) =
      ((p.val ^ r : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) * (UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ r) * Fh k ⇑h g := by
  have hm : 0 < p.val ^ r := pow_pos p.property.pos r
  rw [sum_Fh_lower_cusp h hm g hg]
  have hSinv : (Matrix.GeneralLinearGroup.det (Sgl⁻¹)).val = 1 := by
    rw [map_inv, Units.val_inv_eq_inv_val, Sgl_det, inv_one]
  have hg' : 0 < (Matrix.GeneralLinearGroup.det (Sgl⁻¹ * g)).val := by
    rw [map_mul, Units.val_mul, hSinv, one_mul]; exact hg
  rw [latticeOp_prime_pow_eq_coeff h eigenvalues relations normalized p r, ← Fh_Sgl_inv k h g hg]
  unfold Fh
  push_cast
  ring


theorem scalar_comm (u : ℝˣ) (X : GL (Fin 2) ℝ) :
    GeneralLinearGroup.scalar (Fin 2) u * X = X * GeneralLinearGroup.scalar (Fin 2) u := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

theorem Gl_scale {p : ℕ} (hp0 : 0 < p) {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (g : GL (Fin 2) ℝ) :
    Gl (p * t.1, p * t.2.1, p * t.2.2) g =
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ((p : ℝ)⁻¹) (inv_ne_zero (by exact_mod_cast hp0.ne'))) * Gl t g := by
  have ht' : 0 < (p * t.1, p * t.2.1, p * t.2.2).1 ∧ 0 < (p * t.1, p * t.2.1, p * t.2.2).2.2 :=
    ⟨Nat.mul_pos hp0 ht.1, Nat.mul_pos hp0 ht.2⟩
  rw [Gl_eq ht', Gl_eq ht]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hmul : GeneralLinearGroup.mkOfDetNeZero (lowMat (p * t.1, p * t.2.1, p * t.2.2)) (lowMat_det_ne_zero ht') =
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) hp) *
        GeneralLinearGroup.mkOfDetNeZero (lowMat t) (lowMat_det_ne_zero ht) := by
    apply Units.ext
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowMat, GeneralLinearGroup.mkOfDetNeZero]
  rw [hmul, _root_.mul_inv_rev]
  have : (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) hp))⁻¹ =
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ((p : ℝ)⁻¹) (inv_ne_zero hp)) := by
    rw [← map_inv]; congr 1; apply Units.ext; simp
  rw [this, ← scalar_comm, mul_assoc]


theorem Gl_det_pos {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) {g : GL (Fin 2) ℝ}
    (hg : 0 < (Matrix.GeneralLinearGroup.det g).val) : 0 < (Matrix.GeneralLinearGroup.det (Gl t g)).val := by
  rw [Gl_eq ht, map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val]
  have : (Matrix.GeneralLinearGroup.det (GeneralLinearGroup.mkOfDetNeZero (lowMat t) (lowMat_det_ne_zero ht))).val =
      (t.1 : ℝ) * (t.2.2 : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact lowMat_det t
  rw [this]
  have h1 : (0 : ℝ) < t.1 := by exact_mod_cast ht.1
  have h2 : (0 : ℝ) < t.2.2 := by exact_mod_cast ht.2
  positivity

theorem Fh_Gl_scale (k : ℤ) (h : CuspForm levelOne k) {p : ℕ} (hp0 : 0 < p) {t : ℕ × ℕ × ℕ}
    (ht : 0 < t.1 ∧ 0 < t.2.2) {g : GL (Fin 2) ℝ} (hg : 0 < (Matrix.GeneralLinearGroup.det g).val) :
    Fh k ⇑h (Gl (p * t.1, p * t.2.1, p * t.2.2) g) = Fh k ⇑h (Gl t g) := by
  rw [Gl_scale hp0 ht g]
  exact Fh_scalar_pos k ⇑h _ (inv_pos.mpr (by exact_mod_cast hp0)) _ (Gl_det_pos ht hg)

theorem cpow_shift (p : ℕ) (hp : 0 < p) (k : ℤ) (n : ℕ) :
    ((p ^ n : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) =
      ((p ^ (n + 2) : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) * (p : ℂ) ^ (k - 2) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  set s : ℂ := 1 - (k : ℂ) / 2 with hs
  have h1 : (((p ^ (n + 2) : ℕ)) : ℂ) = ((p ^ n : ℕ) : ℂ) * ((p : ℂ) * (p : ℂ)) := by
    push_cast; ring
  have h2 : (((p : ℝ) * (p : ℝ) : ℝ) : ℂ) = (p : ℂ) * (p : ℂ) := by push_cast; ring
  have hpn : (((p ^ n : ℕ) : ℝ) : ℂ) = ((p ^ n : ℕ) : ℂ) := by push_cast; rfl
  rw [h1]
  have e1 : (((p ^ n : ℕ) : ℂ) * ((p : ℂ) * (p : ℂ))) ^ s =
      ((p ^ n : ℕ) : ℂ) ^ s * (((p : ℂ) * (p : ℂ)) ^ s) := by
    rw [← hpn, ← h2]
    rw [← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  have e2 : ((p : ℂ) * (p : ℂ)) ^ s = (p : ℂ) ^ s * (p : ℂ) ^ s := by
    have := Complex.mul_cpow_ofReal_nonneg (a := (p : ℝ)) (b := (p : ℝ)) (by positivity) (by positivity) s
    simpa using this
  have e3 : (p : ℂ) ^ s * (p : ℂ) ^ s * (p : ℂ) ^ (k - 2) = 1 := by
    rw [← Complex.cpow_intCast, ← Complex.cpow_add _ _ hp0, ← Complex.cpow_add _ _ hp0]
    rw [show s + s + ((k - 2 : ℤ) : ℂ) = 0 by rw [hs]; push_cast; ring]
    simp
  rw [e1, e2]
  linear_combination (-(((p ^ n : ℕ) : ℂ) ^ s)) * e3


open TernaryPeriodPolynomials.Argument.LatticeCounts in
/-- **`eq:cyclic-hecke` at finite coordinate one**: subtracting the noncyclic lattices (`p` times the lattices of index
`p^{r-2}`), `∑_{Λ cyclic} F_h(A_Λ⁻¹ g) = (p^r)^{1-k/2} {a_h(p^r) - p^{k-2} a_h(p^{r-2})} F_h(g)` with `a_h(p^{-1}) = a_h(p^{-2}) = 0`. -/
theorem eq_cyclic_hecke_finite_one (k : ℤ) (h : CuspForm levelOne k) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations k h eigenvalues)
    (normalized : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1) (p : Nat.Primes) (r : ℕ)
    (g : GL (Fin 2) ℝ) (hg : 0 < (Matrix.GeneralLinearGroup.det g).val) :
    ∑ t ∈ cyclicHNF p.val r, Fh k ⇑h (Gl t g) =
      ((p.val ^ r : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) *
        ((UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ r) -
          (p.val : ℂ) ^ (k - 2) *
            (if 2 ≤ r then (UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ (r - 2)) else 0)) * Fh k ⇑h g := by
  have : Fact p.val.Prime := ⟨p.property⟩
  have hp0 : 0 < p.val := p.property.pos
  have hsplit : ∑ t ∈ cyclicHNF p.val r, Fh k ⇑h (Gl t g) + ∑ t ∈ nonCyclicHNF p.val r, Fh k ⇑h (Gl t g) =
      ∑ t ∈ hnfData (p.val ^ r), Fh k ⇑h (Gl t g) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  rw [eq_lattice_hecke_finite_one k h eigenvalues relations normalized p r g hg] at hsplit
  have hnon : ∑ t ∈ nonCyclicHNF p.val r, Fh k ⇑h (Gl t g) =
      if 2 ≤ r then ((p.val ^ (r - 2) : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) *
        (UpperHalfPlane.qExpansion 1 h).coeff (p.val ^ (r - 2)) * Fh k ⇑h g else 0 := by
    by_cases hr : 2 ≤ r
    · rw [ite_eq_left hr, nonCyclicHNF_eq hr, Finset.sum_image (fun x _ y _ hxy => scaleHNF_injective hp0.ne' hxy)]
      have : ∀ T ∈ hnfData (p.val ^ (r - 2)), Fh k ⇑h (Gl (scaleHNF p.val T) g) = Fh k ⇑h (Gl T g) := by
        intro T hT
        rw [mem_hnfData (pow_pos hp0 _)] at hT
        obtain ⟨h1, h2, _⟩ := hT
        have hd : 0 < T.2.2 := Nat.pos_of_ne_zero fun h0 => by
          rw [h0, mul_zero] at h2; exact (pow_pos hp0 _).ne' h2.symm
        exact Fh_Gl_scale k h hp0 ⟨h1, hd⟩ hg
      rw [Finset.sum_congr rfl this]
      exact eq_lattice_hecke_finite_one k h eigenvalues relations normalized p (r - 2) g hg
    · rw [ite_eq_right hr]
      have hr' : r = 0 ∨ r = 1 := by omega
      rcases hr' with rfl | rfl
      · have : nonCyclicHNF p.val 0 = ∅ := by
          unfold nonCyclicHNF
          rw [hnfData_one]
          ext ⟨a, b, d⟩
          simp only [mem_filter, mem_singleton, Prod.mk.injEq]
          constructor
          · rintro ⟨⟨rfl, rfl, rfl⟩, hne⟩
            exact absurd rfl hne
          · intro h0
            exact absurd h0 (Finset.notMem_empty _)
        rw [this, Finset.sum_empty]
      · have := card_cyclicHNF_one (p := p.val)
        rw [Finset.card_eq_zero] at this
        rw [this, Finset.sum_empty]
  by_cases hr : 2 ≤ r
  · rw [ite_eq_left hr] at hnon ⊢
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
    simp only [Nat.add_sub_cancel] at hnon ⊢
    rw [cpow_shift p.val hp0 k n] at hnon
    linear_combination hsplit - hnon
  · rw [ite_eq_right hr] at hnon ⊢
    linear_combination hsplit - hnon


end TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion
