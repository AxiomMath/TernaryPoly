module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.Iwasawa
public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Integers

@[expose] public section


/-!
# Local integrality at one finite place

Formalized by Claude Haiku 5.5.

For a finite place `v` of `ℚ`, `IntGL v X` says that a matrix `X` over the local field `K_v`
lies in `GL₂(O_v)`: `det X` is a unit, and entries of `X` and of `X⁻¹` lie in `O_v`.

* `intGL_iff_pInt`: transport along the `ℚ`-isomorphism `K_v ≃ ℚ_[p_v]` (`adicCompletion.padicEquiv`).
* `local_step`: for any invertible `A` over `K_v`, a rational `q` with `det q = p_v^E > 0`,
  entries in `ℤ[1/p_v]`, and `q A ∈ GL₂(O_v)`.
* `intGL_of_denom`: for a place `w ≠ v`, such a `q` is in `GL₂(O_w)`.
-/

open Matrix
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalIwasawa

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic

/-- The local ring of integers at `v`, as a subring of `K_v`. -/
abbrev OS (v : FinitePlace) : Subring (v.adicCompletion ℚ) :=
  (v.adicCompletionIntegers ℚ).toSubring

/-- `GL₂(O_v)` inside `GL₂(K_v)`, as a predicate on matrices. -/
def IntGL (v : FinitePlace) (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) : Prop :=
  IsUnit X.det ∧ (∀ i j, X i j ∈ OS v) ∧ (∀ i j, X⁻¹ i j ∈ OS v)

instance instFactPrimes (v : FinitePlace) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The `ℚ`-algebra isomorphism `K_v ≃ ℚ_[p_v]` as a ring hom. -/
def pe (v : FinitePlace) :
    v.adicCompletion ℚ →+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom

theorem pe_apply (v : FinitePlace) (x : v.adicCompletion ℚ) :
    pe v x = Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x := rfl

theorem pe_algebraMap (v : FinitePlace) (r : ℚ) :
    pe v (algebraMap ℚ (v.adicCompletion ℚ) r) =
      algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] r :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).commutes r

/-- Membership in `O_v` is the norm bound on the `p_v`-adic side. -/
theorem mem_iff_norm (v : FinitePlace) (x : v.adicCompletion ℚ) :
    x ∈ OS v ↔ ‖pe v x‖ ≤ 1 := by
  rw [pe_apply]
  constructor
  · intro hx
    exact (PadicInt.mem_subring_iff (Rat.HeightOneSpectrum.primesEquiv v : ℕ)).1
      ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hx)
  · intro hx
    obtain ⟨y, hy, hyx⟩ :=
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).surjOn
        ((PadicInt.mem_subring_iff (Rat.HeightOneSpectrum.primesEquiv v : ℕ)).2 hx)
    have : y = x := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective hyx
    subst this
    exact hy

theorem det_mem (v : FinitePlace) {X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (hX : ∀ i j, X i j ∈ OS v) : X.det ∈ OS v := by
  rw [Matrix.det_fin_two]
  exact (OS v).sub_mem ((OS v).mul_mem (hX 0 0) (hX 1 1)) ((OS v).mul_mem (hX 0 1) (hX 1 0))

theorem map_det_pe (v : FinitePlace) (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    (X.map (pe v)).det = pe v X.det := by
  simp [Matrix.det_fin_two]

theorem pe_map_inv (v : FinitePlace) {X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (hX : IsUnit X.det) : (X.map (pe v))⁻¹ = (X⁻¹).map (pe v) := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv X hX]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- Transport: `GL₂(O_v)` corresponds to `PInt` on the `p_v`-adic side. -/
theorem intGL_iff_pInt (v : FinitePlace) (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    IntGL v X ↔ PInt (X.map (pe v)) := by
  constructor
  · rintro ⟨hdet, hX, hXi⟩
    have hdetmem : X.det ∈ OS v := det_mem v hX
    have hdetinv : (X⁻¹).det ∈ OS v := det_mem v hXi
    have hprod : X.det * (X⁻¹).det = 1 := by
      rw [← Matrix.det_mul, Matrix.mul_nonsing_inv X hdet, Matrix.det_one]
    have hmul : pe v X.det * pe v (X⁻¹).det = 1 := by
      rw [← map_mul, hprod, map_one]
    refine ⟨fun i j => ?_, ?_⟩
    · rw [Matrix.map_apply]
      exact (mem_iff_norm v _).1 (hX i j)
    · rw [map_det_pe]
      apply le_antisymm ((mem_iff_norm v _).1 hdetmem)
      have h2 := (mem_iff_norm v _).1 hdetinv
      calc (1 : ℝ) = ‖pe v X.det‖ * ‖pe v (X⁻¹).det‖ := by
            rw [← norm_mul, hmul, norm_one]
        _ ≤ ‖pe v X.det‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖pe v X.det‖ := mul_one _
  · rintro ⟨hn, hd⟩
    have hne : (X.map (pe v)).det ≠ 0 := by
      intro h
      rw [h, norm_zero] at hd
      exact zero_ne_one hd
    rw [map_det_pe] at hne
    have hdetX : X.det ≠ 0 := fun h => hne (by rw [h, map_zero])
    have hunit : IsUnit X.det := isUnit_iff_ne_zero.2 hdetX
    refine ⟨hunit, fun i j => (mem_iff_norm v _).2 ?_, fun i j => (mem_iff_norm v _).2 ?_⟩
    · have h := hn i j
      rw [Matrix.map_apply] at h
      exact h
    · have hinv := pInt_inv (⟨hn, hd⟩ : PInt (X.map (pe v)))
      have h2 := hinv.1 i j
      rw [pe_map_inv v hunit, Matrix.map_apply] at h2
      exact h2

/-- Closure of `GL₂(O_v)` entries under products. -/
theorem mul_entries_mem (v : FinitePlace) {X Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (hX : ∀ i j, X i j ∈ OS v) (hY : ∀ i j, Y i j ∈ OS v) : ∀ i j, (X * Y) i j ∈ OS v := by
  intro i j
  rw [Matrix.mul_apply]
  exact (OS v).sum_mem (fun k _ => (OS v).mul_mem (hX i k) (hY k j))

theorem intGL_mul {v : FinitePlace} {A B : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (hA : IntGL v A) (hB : IntGL v B) : IntGL v (A * B) := by
  refine ⟨?_, mul_entries_mem v hA.2.1 hB.2.1, ?_⟩
  · rw [Matrix.det_mul]
    exact hA.1.mul hB.1
  · rw [Matrix.mul_inv_rev]
    exact mul_entries_mem v hB.2.2 hA.2.2

theorem intGL_one (v : FinitePlace) : IntGL v 1 := by
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))⁻¹ = 1 :=
    Matrix.inv_eq_right_inv (by rw [mul_one])
  refine ⟨?_, fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.det_one]
    exact isUnit_one
  · rw [Matrix.one_apply]
    split_ifs
    · exact (OS v).one_mem
    · exact (OS v).zero_mem
  · rw [h1, Matrix.one_apply]
    split_ifs
    · exact (OS v).one_mem
    · exact (OS v).zero_mem

/-- Entries of the inverse of a matrix with integral entries and integral inverse determinant. -/
theorem inv_entries_mem (v : FinitePlace) (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hX : ∀ i j, X i j ∈ OS v) (hd : X.det⁻¹ ∈ OS v) : ∀ i j, X⁻¹ i j ∈ OS v := by
  intro i j
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, Matrix.adjugate_fin_two,
    smul_eq_mul]
  fin_cases i <;> fin_cases j <;> first
    | exact (OS v).mul_mem hd (hX 1 1)
    | exact (OS v).mul_mem hd (hX 0 0)
    | exact (OS v).mul_mem hd ((OS v).neg_mem (hX 0 1))
    | exact (OS v).mul_mem hd ((OS v).neg_mem (hX 1 0))

/-- Local step: a rational `q` with `det q = p_v^E`, entries in `ℤ[1/p_v]`, and `q A ∈ GL₂(O_v)`. -/
theorem local_step (v : FinitePlace) (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hA : IsUnit A.det) :
    ∃ q : Matrix (Fin 2) (Fin 2) ℚ, 0 < q.det ∧
      (∀ i j, ∃ (n : ℤ) (k : ℕ), q i j * ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) ^ k = n) ∧
      (∃ E : ℤ, q.det = ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) ^ E) ∧
      IntGL v (q.map (algebraMap ℚ (v.adicCompletion ℚ)) * A) := by
  have hdetA : (A.map (pe v)).det ≠ 0 := by
    rw [map_det_pe]
    exact (map_ne_zero (pe v)).2 (isUnit_iff_ne_zero.1 hA)
  obtain ⟨q, hqdet, hqden, hPI⟩ :=
    exists_local_reduction (p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) (A.map (pe v)) hdetA
  obtain ⟨E, hE⟩ := hqdet
  have hmat : (q.map (algebraMap ℚ (v.adicCompletion ℚ))).map (pe v) =
      q.map (algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) := by
    ext i j
    simp only [Matrix.map_apply]
    exact pe_algebraMap v (q i j)
  refine ⟨q, ?_, hqden, ⟨E, hE⟩, ?_⟩
  · rw [hE]
    exact zpow_pos (Nat.cast_pos.2 (Rat.HeightOneSpectrum.primesEquiv v).2.pos) E
  · rw [intGL_iff_pInt, Matrix.map_mul, hmat]
    exact hPI

/-- The prime attached to `v` is not in the ideal of any other height-one prime `w`. -/
theorem natGen_notMem (v w : FinitePlace) (hwv : w ≠ v) :
    ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ) ∉ w.asIdeal := by
  intro hmem
  apply hwv
  have hdvd : Rat.HeightOneSpectrum.natGenerator w ∣ (Rat.HeightOneSpectrum.primesEquiv v : ℕ) := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv ℤ) hmem
    simpa using this
  have heq : Rat.HeightOneSpectrum.natGenerator w = (Rat.HeightOneSpectrum.primesEquiv v : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w)
      (Rat.HeightOneSpectrum.primesEquiv v).2).1 hdvd
  apply (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).injective
  exact Subtype.ext heq

/-- A rational `q` of the local-step shape lies in `GL₂(O_w)` for every place `w ≠ v`. -/
theorem intGL_of_denom (v w : FinitePlace) (hwv : w ≠ v) (q : Matrix (Fin 2) (Fin 2) ℚ)
    (hq : ∀ i j, ∃ (n : ℤ) (k : ℕ), q i j * ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) ^ k = n)
    (hdet : ∃ E : ℤ, q.det = ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) ^ E) :
    IntGL w (q.map (algebraMap ℚ (w.adicCompletion ℚ))) := by
  obtain ⟨E, hE⟩ := hdet
  set P : ℚ := ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) with hP
  have hP1 : w.valuation ℚ P = 1 := by
    have h := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w) (K := ℚ)
      (r := ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ))).2 (natGen_notMem v w hwv)
    simpa [hP] using h
  have hbound : ∀ (r : ℚ) (n : ℤ) (k : ℕ), r * P ^ k = n → w.valuation ℚ r ≤ 1 := by
    intro r n k h
    have h1 : w.valuation ℚ (r * P ^ k) ≤ 1 := by
      rw [h]
      have := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (R := ℤ) (v := w) (K := ℚ) n
      simpa using this
    rwa [map_mul, map_pow, hP1, one_pow, mul_one] at h1
  have key : ∀ k : ℚ, Valued.v (algebraMap ℚ (w.adicCompletion ℚ) k) = w.valuation ℚ k := by
    intro k
    exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := ℤ) (v := w) (K := ℚ) k
  have hmem : ∀ r : ℚ, (∃ (n : ℤ) (k : ℕ), r * P ^ k = n) →
      algebraMap ℚ (w.adicCompletion ℚ) r ∈ OS w := by
    rintro r ⟨n, k, h⟩
    have hv : w.valuation ℚ r ≤ 1 := hbound r n k h
    show algebraMap ℚ (w.adicCompletion ℚ) r ∈ w.adicCompletionIntegers ℚ
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, key]
    exact hv
  have hdetval : w.valuation ℚ q.det = 1 := by
    rw [hE, map_zpow₀, hP1, one_zpow]
  have hdetq : q.det ≠ 0 := by
    rw [hE]
    exact zpow_ne_zero _ (Nat.cast_ne_zero.2 (Rat.HeightOneSpectrum.primesEquiv v).2.ne_zero)
  have hdetmap : (q.map (algebraMap ℚ (w.adicCompletion ℚ))).det =
      algebraMap ℚ (w.adicCompletion ℚ) q.det :=
    (RingHom.map_det (algebraMap ℚ (w.adicCompletion ℚ)) q).symm
  have hXint : ∀ i j, (q.map (algebraMap ℚ (w.adicCompletion ℚ))) i j ∈ OS w := by
    intro i j
    rw [Matrix.map_apply]
    exact hmem (q i j) (hq i j)
  have hdinv : (q.map (algebraMap ℚ (w.adicCompletion ℚ))).det⁻¹ ∈ OS w := by
    rw [hdetmap]
    show (algebraMap ℚ (w.adicCompletion ℚ) q.det)⁻¹ ∈ w.adicCompletionIntegers ℚ
    have hv : w.valuation ℚ q.det⁻¹ ≤ 1 := by simp [map_inv₀, hdetval]
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← map_inv₀ (algebraMap ℚ (w.adicCompletion ℚ)), key]
    exact hv
  refine ⟨?_, hXint, inv_entries_mem w _ hXint hdinv⟩
  rw [hdetmap]
  exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hdetq)

end TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
