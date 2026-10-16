module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.ThreeLocal

@[expose] public section


/-!
# Splitting off the component at three

Every `t ∈ GL₃(ℚ)` factors as `t = a * b` where `a` lies in the local level at
every place `v ≠ 3` and `b` is `Good` (its component at three lies in `K₁(3)`).

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix IsDedekindDomain
open TernaryPeriodPolynomials.HeckeStability

namespace TernaryPeriodPolynomials.HeckeCommutativity

theorem exists_three_pow_mul (z : ℤ) (hz : z ≠ 0) :
    ∃ e : ℕ, ∃ w : ℤ, ¬ (3 : ℤ) ∣ w ∧ z = 3 ^ e * w := by
  obtain ⟨e, n', hn', hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hz) 3
    (by norm_num)
  refine ⟨e, z.sign * n', ?_, ?_⟩
  · intro h
    apply hn'
    have h' : (3 : ℤ) ∣ (n' : ℤ) := by
      rcases Int.sign_trichotomy z with hs | hs | hs
      · rw [hs, one_mul] at h; exact h
      · exact absurd (Int.sign_eq_zero_iff_zero.mp hs) hz
      · rw [hs] at h; simpa using h
    exact_mod_cast h'
  · have : (z.natAbs : ℤ) = 3 ^ e * n' := by exact_mod_cast hn
    calc z = z.sign * (z.natAbs : ℤ) := (Int.sign_mul_natAbs z).symm
      _ = 3 ^ e * (z.sign * n') := by rw [this]; ring

/-- Lift of a matrix invertible modulo three to `GL₃(ℤ)`. -/
theorem exists_glInt_lift (R : Matrix (Fin 3) (Fin 3) ℤ) (hR : ((R.det : ℤ) : ZMod 3) ≠ 0) :
    ∃ G G' : Matrix (Fin 3) (Fin 3) ℤ, G * G' = 1 ∧ G' * G = 1 ∧
      ∀ i j, (3 : ℤ) ∣ G i j - R i j := by
  obtain ⟨ε, hε1, hεR⟩ : ∃ ε : ℤ, ε * ε = 1 ∧ ((R.det : ℤ) : ZMod 3) = ε := by
    by_cases h1 : ((R.det : ℤ) : ZMod 3) = 1
    · exact ⟨1, by norm_num, by rw [h1]; simp⟩
    · exact ⟨-1, by norm_num, by rw [zmod_three_eq_neg_one hR h1]; simp; rfl⟩
  let E : Matrix (Fin 3) (Fin 3) ℤ := diagonal ![1, 1, ε]
  have hEE : E * E = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hε1]
  have hdetE : E.det = ε := by simp [E, det_diagonal, Fin.prod_univ_three]
  let τ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) :=
    ⟨(Int.castRingHom (ZMod 3)).mapMatrix (R * E), by
      rw [← RingHom.map_det, det_mul, hdetE, map_mul]
      simp only [eq_intCast]
      rw [hεR]
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 3) hε1⟩
  obtain ⟨σ, hσ⟩ := StrongApproximation.map_intCast_surjective 3 3 τ
  have hσE : (Int.castRingHom (ZMod 3)).mapMatrix (σ : Matrix (Fin 3) (Fin 3) ℤ) =
      (Int.castRingHom (ZMod 3)).mapMatrix (R * E) := by
    have := congrArg (fun S : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) =>
      (S : Matrix (Fin 3) (Fin 3) (ZMod 3))) hσ
    simpa [τ] using this
  have hσσ : (σ : Matrix (Fin 3) (Fin 3) ℤ) * ((σ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
      Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hσσ' : ((σ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *
      (σ : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  refine ⟨(σ : Matrix (Fin 3) (Fin 3) ℤ) * E,
    E * ((σ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ), ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE, Matrix.one_mul, hσσ]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (σ : Matrix (Fin 3) (Fin 3) ℤ), hσσ',
      Matrix.one_mul, hEE]
  · have hmod : (Int.castRingHom (ZMod 3)).mapMatrix ((σ : Matrix (Fin 3) (Fin 3) ℤ) * E) =
        (Int.castRingHom (ZMod 3)).mapMatrix R := by
      rw [map_mul, hσE, ← map_mul, Matrix.mul_assoc, hEE, Matrix.mul_one]
    intro i j
    have := dvd_of_intCast_matrix_eq hmod i j
    exact_mod_cast this

theorem intAt_intMat {v : FinitePlace} (M : Matrix (Fin 3) (Fin 3) ℤ) :
    ∀ i j, IntAt v (M.map (Int.cast : ℤ → ℚ) i j) :=
  fun i j => intAt_intCast v (M i j)

theorem intAt_smul_mat {v : FinitePlace} {c : ℚ} (hc : IntAt v c) {A : Matrix (Fin 3) (Fin 3) ℚ}
    (hA : ∀ i j, IntAt v (A i j)) : ∀ i j, IntAt v ((c • A) i j) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact intAt_mul hc (hA i j)

theorem intAt_diagonal {v : FinitePlace} {f : Fin 3 → ℚ} (hf : ∀ i, IntAt v (f i)) :
    ∀ i j, IntAt v (diagonal f i j) := by
  intro i j
  rw [diagonal_apply]
  split_ifs with h
  · exact hf i
  · exact intAt_zero v

theorem intCast_map_one :
    (1 : Matrix (Fin 3) (Fin 3) ℤ).map (Int.cast : ℤ → ℚ) = 1 :=
  Matrix.map_one _ Int.cast_zero Int.cast_one

/-- **Splitting off the component at three.** -/
theorem exists_three_factorization (t : RationalGL3) :
    ∃ a b : RationalGL3, t = a * b ∧ (∀ v, v ≠ placeThree → LocK a v) ∧ Good b := by
  classical
  obtain ⟨d, hd, N, hN⟩ := CosetDecomposition.exists_integral_multiple t.val
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have htN : t.val = (d : ℚ)⁻¹ • N.map (Int.cast : ℤ → ℚ) := by
    apply Matrix.ext
    intro i j
    rw [Matrix.smul_apply, Matrix.map_apply, ← hN i j, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hd0, one_mul]
  have hdetN : N.det ≠ 0 := by
    intro h0
    have hdt : t.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp t.isUnit).ne_zero
    apply hdt
    rw [htN, Matrix.det_smul]
    have : (N.map (Int.cast : ℤ → ℚ)).det = ((N.det : ℤ) : ℚ) := by
      have := RingHom.map_det (Int.castRingHom ℚ) N
      simpa using this.symm
    rw [this, h0]
    simp
  obtain ⟨A, Q, A', Q', n, hAA', hA'A, hQQ', hQ'Q, hNeq⟩ := exists_eq_mul_diagonal_mul N hdetN
  have hn0 : ∀ i, n i ≠ 0 := by
    intro i h
    apply hdetN
    rw [hNeq, det_mul, det_mul, det_diagonal, Finset.prod_eq_zero (Finset.mem_univ i) h]
    ring
  choose e m hm3 hnm using fun i => exists_three_pow_mul (n i) (hn0 i)
  obtain ⟨f, d', hd'3, hdd'⟩ := exists_three_pow_mul d hd
  obtain ⟨u, d'', huv⟩ : IsCoprime (3 : ℤ) d' := (Int.prime_three.coprime_iff_not_dvd).mpr hd'3
  have hd'0 : (d' : ℚ) ≠ 0 := by
    intro h
    apply hd'3
    rw [show d' = 0 by exact_mod_cast h]
    exact dvd_zero _
  have hm0 : ∀ i, (m i : ℚ) ≠ 0 := by
    intro i h
    apply hm3 i
    rw [show m i = 0 by exact_mod_cast h]
    exact dvd_zero _
  -- reductions modulo three
  have hz3 : ∀ z : ℤ, ¬ (3 : ℤ) ∣ z → ((z : ℤ) : ZMod 3) ≠ 0 := fun z hz h =>
    hz (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd z 3).mp h)
  have hdd'' : ((d' : ℤ) : ZMod 3) * ((d'' : ℤ) : ZMod 3) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod 3) huv
    push_cast at this
    rw [show (3 : ZMod 3) = 0 from rfl, mul_zero, zero_add] at this
    rw [mul_comm]
    exact this
  have hunitA : ((A.det : ℤ) : ZMod 3) ≠ 0 := by
    intro h
    have := congrArg (Int.cast : ℤ → ZMod 3) (show A.det * A'.det = 1 by
      rw [← Matrix.det_mul, hAA', Matrix.det_one])
    rw [Int.cast_mul, h, zero_mul, Int.cast_one] at this
    exact zero_ne_one this
  have hunitQ : ((Q.det : ℤ) : ZMod 3) ≠ 0 := by
    intro h
    have := congrArg (Int.cast : ℤ → ZMod 3) (show Q.det * Q'.det = 1 by
      rw [← Matrix.det_mul, hQQ', Matrix.det_one])
    rw [Int.cast_mul, h, zero_mul, Int.cast_one] at this
    exact zero_ne_one this
  let R : Matrix (Fin 3) (Fin 3) ℤ := A * diagonal m * Q
  have hdetR : ((R.det : ℤ) : ZMod 3) ≠ 0 := by
    simp only [R, det_mul, det_diagonal, Int.cast_mul, Int.cast_prod]
    refine mul_ne_zero (mul_ne_zero hunitA ?_) hunitQ
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hz3 _ (hm3 i))
  have hdetdR : (((d'' • R).det : ℤ) : ZMod 3) ≠ 0 := by
    rw [Matrix.det_smul, Fintype.card_fin, Int.cast_mul, Int.cast_pow]
    refine mul_ne_zero (pow_ne_zero _ ?_) hdetR
    intro h
    rw [h, mul_zero] at hdd''
    exact zero_ne_one hdd''
  obtain ⟨G, G', hGG', hG'G, hGR⟩ := exists_glInt_lift (d'' • R) hdetdR
  -- rational versions
  set Aq := A.map (Int.cast : ℤ → ℚ) with hAqdef
  set A'q := A'.map (Int.cast : ℤ → ℚ) with hA'qdef
  set Qq := Q.map (Int.cast : ℤ → ℚ) with hQqdef
  set Q'q := Q'.map (Int.cast : ℤ → ℚ) with hQ'qdef
  set Gq := G.map (Int.cast : ℤ → ℚ) with hGqdef
  set G'q := G'.map (Int.cast : ℤ → ℚ) with hG'qdef
  have hAq : Aq * A'q = 1 := by rw [← intCast_map_mul, hAA', intCast_map_one]
  have hQq : Qq * Q'q = 1 := by rw [← intCast_map_mul, hQQ', intCast_map_one]
  have hQ'q : Q'q * Qq = 1 := by rw [← intCast_map_mul, hQ'Q, intCast_map_one]
  have hGq : Gq * G'q = 1 := by rw [← intCast_map_mul, hGG', intCast_map_one]
  have hG'q : G'q * Gq = 1 := by rw [← intCast_map_mul, hG'G, intCast_map_one]
  let Dm : Matrix (Fin 3) (Fin 3) ℚ := diagonal (fun i => (m i : ℚ))
  let Dmi : Matrix (Fin 3) (Fin 3) ℚ := diagonal (fun i => ((m i : ℚ))⁻¹)
  let D3 : Matrix (Fin 3) (Fin 3) ℚ := diagonal (fun i => (3 : ℚ) ^ e i)
  let D3i : Matrix (Fin 3) (Fin 3) ℚ := diagonal (fun i => ((3 : ℚ) ^ e i)⁻¹)
  have hDm : Dm * Dmi = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hm0 i)
  have hDmi : Dmi * Dm = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hm0 i)
  have hD3 : D3 * D3i = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))
  have hdiag : (diagonal n).map (Int.cast : ℤ → ℚ) = D3 * Dm := by
    rw [Matrix.diagonal_map Int.cast_zero, diagonal_mul_diagonal]
    congr 1
    funext i
    show ((n i : ℤ) : ℚ) = (3 : ℚ) ^ e i * (m i : ℚ)
    rw [hnm i]
    push_cast
    ring
  have hNq : N.map (Int.cast : ℤ → ℚ) = Aq * (D3 * Dm) * Qq := by
    rw [hNeq, intCast_map_mul, intCast_map_mul, hdiag]
  have hRq : R.map (Int.cast : ℤ → ℚ) = Aq * Dm * Qq := by
    simp only [R]
    rw [intCast_map_mul, intCast_map_mul, Matrix.diagonal_map Int.cast_zero]
  -- the factor `b`
  let bval : Matrix (Fin 3) (Fin 3) ℚ := (d' : ℚ)⁻¹ • (G'q * Aq * Dm * Qq)
  let binv : Matrix (Fin 3) (Fin 3) ℚ := (d' : ℚ) • (Q'q * Dmi * A'q * Gq)
  have hb1 : bval * binv = 1 := by
    simp only [bval, binv]
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hd'0, one_smul]
    calc G'q * Aq * Dm * Qq * (Q'q * Dmi * A'q * Gq)
        = G'q * Aq * Dm * (Qq * Q'q) * Dmi * A'q * Gq := by simp only [Matrix.mul_assoc]
      _ = G'q * Aq * (Dm * Dmi) * A'q * Gq := by rw [hQq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = G'q * (Aq * A'q) * Gq := by rw [hDm, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAq, Matrix.mul_one, hG'q]
  have hb2 : binv * bval = 1 := by
    have hA'q : A'q * Aq = 1 := by rw [← intCast_map_mul, hA'A, intCast_map_one]
    simp only [bval, binv]
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hd'0, one_smul]
    calc Q'q * Dmi * A'q * Gq * (G'q * Aq * Dm * Qq)
        = Q'q * Dmi * A'q * (Gq * G'q) * Aq * Dm * Qq := by simp only [Matrix.mul_assoc]
      _ = Q'q * Dmi * (A'q * Aq) * Dm * Qq := by rw [hGq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Q'q * (Dmi * Dm) * Qq := by rw [hA'q, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDmi, Matrix.mul_one, hQ'q]
  let b : RationalGL3 := ⟨bval, binv, hb1, hb2⟩
  have hgood : Good b := by
    refine ⟨d', hz3 _ hd'3, G' * R, ?_, ?_, ?_⟩
    · change (d' : ℚ) • bval = _
      simp only [bval, smul_smul, mul_inv_cancel₀ hd'0, one_smul]
      rw [intCast_map_mul, hRq]
      simp only [Matrix.mul_assoc]
      rfl
    · rw [det_mul, Int.cast_mul]
      refine mul_ne_zero ?_ hdetR
      intro h
      have := congrArg (Int.cast : ℤ → ZMod 3) (show G'.det * G.det = 1 by
        rw [← Matrix.det_mul, hG'G, Matrix.det_one])
      rw [Int.cast_mul, h, zero_mul, Int.cast_one] at this
      exact zero_ne_one this
    · -- modulo three, `G' R ≡ d' · 1`
      have hGmod := intCast_matrix_eq_of_dvd (N := 3) (fun i j => by exact_mod_cast hGR i j)
      have hkey : (Int.castRingHom (ZMod 3)).mapMatrix (G' * R) =
          ((d' : ℤ) : ZMod 3) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
        have e1 : (Int.castRingHom (ZMod 3)).mapMatrix R =
            ((d' : ℤ) : ZMod 3) • (Int.castRingHom (ZMod 3)).mapMatrix G := by
          rw [hGmod]
          apply Matrix.ext
          intro i j
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
            eq_intCast, Int.cast_mul]
          rw [← mul_assoc, hdd'', one_mul]
        rw [map_mul, e1, Matrix.mul_smul, ← map_mul, hG'G, map_one]
      intro j
      have := congrArg (fun M : Matrix (Fin 3) (Fin 3) (ZMod 3) => M 2 j) hkey
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast, Matrix.smul_apply,
        smul_eq_mul, Matrix.one_apply] at this
      rw [this]
      split_ifs with h1 h2 h2
      · simp
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
  -- the factor `a`
  refine ⟨t * b⁻¹, b, by group, ?_, hgood⟩
  intro v hv
  have h3f : IntAt v (((3 : ℚ) ^ f)⁻¹) := by
    have := intAt_inv_intCast v ((3 : ℤ) ^ f) (not_dvd_three_pow hv f)
    simpa using this
  have h3e : ∀ i, IntAt v (((3 : ℚ) ^ e i)⁻¹) := by
    intro i
    have := intAt_inv_intCast v ((3 : ℤ) ^ e i) (not_dvd_three_pow hv (e i))
    simpa using this
  have h3e' : ∀ i, IntAt v ((3 : ℚ) ^ e i) := by
    intro i
    have := intAt_intCast v ((3 : ℤ) ^ e i)
    simpa using this
  have hdratio : (d : ℚ)⁻¹ * d' = ((3 : ℚ) ^ f)⁻¹ := by
    rw [hdd']
    push_cast
    field_simp
  have haval : (t * b⁻¹).val = ((3 : ℚ) ^ f)⁻¹ • (Aq * D3 * A'q * Gq) := by
    rw [Units.val_mul]
    change t.val * binv = _
    rw [htN, hNq]
    simp only [binv]
    rw [smul_mul_smul_comm, hdratio]
    congr 1
    calc Aq * (D3 * Dm) * Qq * (Q'q * Dmi * A'q * Gq)
        = Aq * D3 * Dm * (Qq * Q'q) * Dmi * A'q * Gq := by simp only [Matrix.mul_assoc]
      _ = Aq * D3 * (Dm * Dmi) * A'q * Gq := by rw [hQq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Aq * D3 * A'q * Gq := by rw [hDm, Matrix.mul_one]
  -- inverse of `t`
  let tinv : Matrix (Fin 3) (Fin 3) ℚ := (d : ℚ) • (Q'q * (Dmi * D3i) * A'q)
  have ht1 : t.val * tinv = 1 := by
    rw [htN, hNq]
    simp only [tinv]
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hd0, one_smul]
    have hDD : D3 * Dm * (Dmi * D3i) = 1 := by
      calc D3 * Dm * (Dmi * D3i) = D3 * (Dm * Dmi) * D3i := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hDm, Matrix.mul_one, hD3]
    calc Aq * (D3 * Dm) * Qq * (Q'q * (Dmi * D3i) * A'q)
        = Aq * (D3 * Dm) * (Qq * Q'q) * (Dmi * D3i) * A'q := by simp only [Matrix.mul_assoc]
      _ = Aq * (D3 * Dm * (Dmi * D3i)) * A'q := by rw [hQq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDD, Matrix.mul_one, hAq]
  have htinv : (t⁻¹).val = tinv := Units.inv_eq_of_mul_eq_one_right ht1
  have hdratio' : (d' : ℚ)⁻¹ * d = (3 : ℚ) ^ f := by
    rw [hdd']
    push_cast
    field_simp
  have hainv : ((t * b⁻¹)⁻¹).val = (3 : ℚ) ^ f • (G'q * Aq * D3i * A'q) := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, htinv]
    change bval * tinv = _
    simp only [bval, tinv]
    rw [smul_mul_smul_comm, hdratio']
    congr 1
    have hDD : Dm * (Dmi * D3i) = D3i := by rw [← Matrix.mul_assoc, hDm, Matrix.one_mul]
    calc G'q * Aq * Dm * Qq * (Q'q * (Dmi * D3i) * A'q)
        = G'q * Aq * Dm * (Qq * Q'q) * (Dmi * D3i) * A'q := by simp only [Matrix.mul_assoc]
      _ = G'q * Aq * (Dm * (Dmi * D3i)) * A'q := by rw [hQq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = G'q * Aq * D3i * A'q := by rw [hDD]
  refine ⟨?_, ?_, fun h => absurd h hv⟩
  · rw [haval]
    exact intAt_smul_mat h3f (intAt_mat_mul (intAt_mat_mul (intAt_mat_mul (intAt_intMat A)
      (intAt_diagonal h3e')) (intAt_intMat A')) (intAt_intMat G))
  · rw [hainv]
    have h3f' : IntAt v ((3 : ℚ) ^ f) := by simpa using intAt_intCast v ((3 : ℤ) ^ f)
    exact intAt_smul_mat h3f' (intAt_mat_mul (intAt_mat_mul (intAt_mat_mul (intAt_intMat G')
      (intAt_intMat A)) (intAt_diagonal h3e)) (intAt_intMat A'))

end TernaryPeriodPolynomials.HeckeCommutativity
