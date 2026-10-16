module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.FiniteReduction

@[expose] public section


/-!
# `ℚ ∩ ℤ̂ = ℤ` at matrix level, and reductions differ by `SL₂(ℤ)` (step (b))

Formalized by Claude Haiku 5.5.

* `den_eq_one_of_valuation_le_one`: a rational with `v`-adic valuation at most one at every
  finite place `v : HeightOneSpectrum ℤ` is an integer (scalar level).
* `entry_integral_of_mem`, `rat_matrix_int`: a rational `GL₂` element whose finite image lies in
  `GL₂(ℤ̂)` has integer entries (entrywise).
* `sl2_of_int_det`: such an element of positive determinant is the image of `SL₂(ℤ)`.
* `reductions_differ`: two positive-determinant reductions of the same `g_f` differ by `SL₂(ℤ)`.
-/

open IsDedekindDomain GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.RationalIntegral

/-- A rational with valuation at most one at every finite place is an integer. -/
theorem den_eq_one_of_valuation_le_one (q : ℚ)
    (h : ∀ v : HeightOneSpectrum ℤ, v.valuation ℚ q ≤ 1) : q.den = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let v : HeightOneSpectrum ℤ :=
    { asIdeal := Ideal.span {(p : ℤ)}
      isPrime := (Ideal.span_singleton_prime hz).2 (Nat.prime_iff_prime_int.mp hp)
      ne_bot := fun h0 => hz (Ideal.span_singleton_eq_bot.1 h0) }
  have hnot : ((q.den : ℕ) : ℤ) ∉ v.asIdeal := Rat.valuation_le_one_iff_den.1 (h v)
  exact hnot (Ideal.mem_span_singleton.2 (by exact_mod_cast hpd))

/-- A rational coordinate of an integral finite adele has valuation at most one. -/
theorem valuation_le_one_of_integralAdele (q : ℚ) (y : IntegralAdeles)
    (hy : integralEmbedding y = algebraMap ℚ FiniteAdeles q) (v : HeightOneSpectrum ℤ) :
    v.valuation ℚ q ≤ 1 := by
  have h1 : (y v).val = algebraMap ℚ (v.adicCompletion ℚ) q := by
    have := congrArg (finiteEvaluation v) hy
    rw [integralEmbedding_at, finiteEvaluation_rational] at this
    exact this
  have hmem : (y v).val ∈ v.adicCompletionIntegers ℚ := (y v).property
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, h1] at hmem
  rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hmem

/-- Entries of a rational `GL₂` element whose finite image is in `GL₂(ℤ̂)` have valuation at
most one at every finite place. -/
theorem entry_integral_of_mem (g : BinaryRationalGL)
    (hg : binaryRationalFinite g ∈ binaryIntegralFinite) (i j : Fin 2)
    (v : HeightOneSpectrum ℤ) : v.valuation ℚ (g.val i j) ≤ 1 := by
  rw [binaryIntegralFinite, MonoidHom.mem_range] at hg
  obtain ⟨y, hy⟩ := hg
  have hent : integralEmbedding (y.val i j) = algebraMap ℚ FiniteAdeles (g.val i j) :=
    congrArg (fun M : BinaryFiniteGL => M.val i j) hy
  exact valuation_le_one_of_integralAdele (g.val i j) (y.val i j) hent v

/-- Entrywise integrality: a rational `GL₂` element with integral finite image is an integer
matrix. -/
theorem rat_matrix_int (g : BinaryRationalGL)
    (hg : binaryRationalFinite g ∈ binaryIntegralFinite) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℤ,
      (g.val : Matrix (Fin 2) (Fin 2) ℚ) = M.map (Int.cast) := by
  refine ⟨fun i j => (g.val i j).num, ?_⟩
  ext i j
  have hden := den_eq_one_of_valuation_le_one (g.val i j)
    (fun v => entry_integral_of_mem g hg i j v)
  exact ((Rat.den_eq_one_iff _).1 hden).symm

/-- A rational `GL₂` element of positive determinant with integral finite image and integral
finite inverse image is the image of `SL₂(ℤ)`. -/
theorem sl2_of_int_det (g : BinaryRationalGL)
    (hg : binaryRationalFinite g ∈ binaryIntegralFinite)
    (hginv : binaryRationalFinite g⁻¹ ∈ binaryIntegralFinite)
    (hpos : 0 < (Matrix.GeneralLinearGroup.det g).val) :
    ∃ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (g.val : Matrix (Fin 2) (Fin 2) ℚ) = (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast) := by
  obtain ⟨M, hM⟩ := rat_matrix_int g hg
  obtain ⟨N, hN⟩ := rat_matrix_int g⁻¹ hginv
  have hdetM : (Matrix.GeneralLinearGroup.det g).val = (M.det : ℚ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hM]
    exact (RingHom.map_det (Int.castRingHom ℚ) M).symm
  have hdetN : (Matrix.GeneralLinearGroup.det g⁻¹).val = (N.det : ℚ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hN]
    exact (RingHom.map_det (Int.castRingHom ℚ) N).symm
  have hprod : (Matrix.GeneralLinearGroup.det g).val *
      (Matrix.GeneralLinearGroup.det g⁻¹).val = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [hdetM, hdetN] at hprod
  have hint : M.det * N.det = 1 := by exact_mod_cast hprod
  have hMpos : 0 < M.det := by
    have : (0 : ℚ) < (M.det : ℚ) := by rwa [hdetM] at hpos
    exact_mod_cast this
  have hdet1 : M.det = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hint with h | h
    · exact h.1
    · omega
  exact ⟨⟨M, hdet1⟩, hM⟩

/-- Two positive-determinant rational reductions of the same finite-adelic matrix differ by an
element of `SL₂(ℤ)`. -/
theorem reductions_differ (gf : BinaryFiniteGL) (γ₁ γ₂ : BinaryRationalGL)
    (h1 : binaryRationalFinite γ₁ * gf ∈ binaryIntegralFinite)
    (h2 : binaryRationalFinite γ₂ * gf ∈ binaryIntegralFinite)
    (p1 : 0 < (Matrix.GeneralLinearGroup.det γ₁).val)
    (p2 : 0 < (Matrix.GeneralLinearGroup.det γ₂).val) :
    ∃ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (γ₂.val : Matrix (Fin 2) (Fin 2) ℚ) =
        (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast) * γ₁.val := by
  have hrel : binaryRationalFinite (γ₂ * γ₁⁻¹) =
      (binaryRationalFinite γ₂ * gf) * (binaryRationalFinite γ₁ * gf)⁻¹ := by
    rw [map_mul, map_inv]
    group
  have hmem : binaryRationalFinite (γ₂ * γ₁⁻¹) ∈ binaryIntegralFinite := by
    rw [hrel]
    exact mul_mem h2 (inv_mem h1)
  have hmemInv : binaryRationalFinite (γ₂ * γ₁⁻¹)⁻¹ ∈ binaryIntegralFinite := by
    rw [map_inv]
    exact inv_mem hmem
  have hpos : 0 < (Matrix.GeneralLinearGroup.det (γ₂ * γ₁⁻¹)).val := by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    exact mul_pos p2 (inv_pos.2 p1)
  obtain ⟨δ, hδ⟩ := sl2_of_int_det (γ₂ * γ₁⁻¹) hmem hmemInv hpos
  refine ⟨δ, ?_⟩
  rw [← hδ, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

end TernaryPeriodPolynomials.Argument.LatticeCounts.RationalIntegral
