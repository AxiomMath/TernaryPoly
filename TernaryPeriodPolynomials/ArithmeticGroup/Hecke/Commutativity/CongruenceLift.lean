module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.StrongApproximation

@[expose] public section


/-!
# Simultaneous congruence lifts in `SL₃(ℤ)`

For `d` prime to three and an integer matrix `A'` of determinant one there is
`σ ∈ SL₃(ℤ)` with `σ ≡ A' (mod 3)` and `σ⁻¹ ≡ 1 (mod d)`.  This combines the
Chinese remainder theorem with strong approximation
(`StrongApproximation.map_intCast_surjective`).

Original work (AxiomDeep, Claude Opus 5.5).
-/

open Matrix

namespace TernaryPeriodPolynomials.HeckeCommutativity

open TernaryPeriodPolynomials.HeckeStability

theorem intCast_matrix_eq_of_dvd {N : ℕ} {C C' : Matrix (Fin 3) (Fin 3) ℤ}
    (h : ∀ i j, (N : ℤ) ∣ C i j - C' i j) :
    (Int.castRingHom (ZMod N)).mapMatrix C = (Int.castRingHom (ZMod N)).mapMatrix C' := by
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_sub_comm.mp (h i j))

theorem dvd_of_intCast_matrix_eq {N : ℕ} {C C' : Matrix (Fin 3) (Fin 3) ℤ}
    (h : (Int.castRingHom (ZMod N)).mapMatrix C = (Int.castRingHom (ZMod N)).mapMatrix C')
    (i j : Fin 3) : (N : ℤ) ∣ C i j - C' i j := by
  have hij := congrArg (fun M : Matrix (Fin 3) (Fin 3) (ZMod N) => M i j) h
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] at hij
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hij.symm
  exact this

/-- Simultaneous lift: `σ ≡ A' (mod 3)` and `σ⁻¹ ≡ 1 (mod d)`. -/
theorem exists_sl_lift (A' : Matrix (Fin 3) (Fin 3) ℤ) (hA' : A'.det = 1) (d : ℤ)
    (hd : ¬ (3 : ℤ) ∣ d) :
    ∃ σ : Matrix.SpecialLinearGroup (Fin 3) ℤ,
      (∀ i j, (3 : ℤ) ∣ (σ : Matrix (Fin 3) (Fin 3) ℤ) i j - A' i j) ∧
      ∀ i j, d ∣ ((σ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) i j -
        (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
  have hcop : IsCoprime (3 : ℤ) d := (Int.prime_three.coprime_iff_not_dvd).mpr hd
  obtain ⟨u, v, huv⟩ := hcop
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero _)
  let C : Matrix (Fin 3) (Fin 3) ℤ := (v * d) • A' + (u * 3) • (1 : Matrix (Fin 3) (Fin 3) ℤ)
  have hC3 : ∀ i j, ((3 : ℕ) : ℤ) ∣ C i j - A' i j := by
    intro i j
    refine ⟨u * ((1 : Matrix (Fin 3) (Fin 3) ℤ) i j - A' i j), ?_⟩
    simp only [C, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    linear_combination (A' i j) * huv
  have hCd : ∀ i j, ((d.natAbs : ℕ) : ℤ) ∣ C i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
    intro i j
    rw [Int.natCast_dvd]
    apply Int.natAbs_dvd_natAbs.mpr
    refine ⟨v * (A' i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j), ?_⟩
    simp only [C, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination ((1 : Matrix (Fin 3) (Fin 3) ℤ) i j) * huv
  -- determinant congruences
  have hdet3 : (3 : ℤ) ∣ C.det - 1 := by
    have e := intCast_matrix_eq_of_dvd hC3
    have := congrArg Matrix.det e
    rw [← RingHom.map_det, ← RingHom.map_det, hA', map_one] at this
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 C.det 3).mp (by simpa using this.symm)
    simpa using h2
  have hdetd : d ∣ C.det - 1 := by
    have e := intCast_matrix_eq_of_dvd hCd
    have := congrArg Matrix.det e
    rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one, map_one] at this
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 C.det d.natAbs).mp (by simpa using this.symm)
    have h3 : ((d.natAbs : ℕ) : ℤ) ∣ C.det - 1 := by simpa using h2
    exact (Int.natAbs_dvd.mp (by simpa using h3) : _)
  have hN : ((3 * d.natAbs : ℕ) : ℤ) ∣ C.det - 1 := by
    have h := IsCoprime.mul_dvd ⟨u, v, huv⟩ hdet3 hdetd
    rw [Int.natCast_dvd]
    simpa [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr h
  set N : ℕ := 3 * d.natAbs with hNdef
  have : NeZero N := ⟨by
    rw [hNdef]
    exact Nat.mul_ne_zero (by norm_num) (Int.natAbs_ne_zero.mpr hd0)⟩
  let τ : Matrix.SpecialLinearGroup (Fin 3) (ZMod N) :=
    ⟨(Int.castRingHom (ZMod N)).mapMatrix C, by
      rw [← RingHom.map_det]
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 C.det N).mpr hN
      simpa using this.symm⟩
  obtain ⟨σ, hσ⟩ := StrongApproximation.map_intCast_surjective N 3 τ
  have hσC : (Int.castRingHom (ZMod N)).mapMatrix (σ : Matrix (Fin 3) (Fin 3) ℤ) =
      (Int.castRingHom (ZMod N)).mapMatrix C := by
    have := congrArg (fun S : Matrix.SpecialLinearGroup (Fin 3) (ZMod N) =>
      (S : Matrix (Fin 3) (Fin 3) (ZMod N))) hσ
    simpa [τ] using this
  have hσCN : ∀ i j, (N : ℤ) ∣ (σ : Matrix (Fin 3) (Fin 3) ℤ) i j - C i j :=
    dvd_of_intCast_matrix_eq hσC
  refine ⟨σ, ?_, ?_⟩
  · intro i j
    have h1 : (3 : ℤ) ∣ (σ : Matrix (Fin 3) (Fin 3) ℤ) i j - C i j :=
      (Dvd.intro _ (by push_cast [hNdef]; ring) : (3 : ℤ) ∣ (N : ℤ)).trans (hσCN i j)
    have h2 : (3 : ℤ) ∣ C i j - A' i j := by exact_mod_cast hC3 i j
    have := dvd_add h1 h2
    simpa using this
  · -- `σ ≡ 1 (mod d)`, hence `σ⁻¹ ≡ 1 (mod d)`.
    have hσ1 : ∀ i j, ((d.natAbs : ℕ) : ℤ) ∣ (σ : Matrix (Fin 3) (Fin 3) ℤ) i j -
        (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
      intro i j
      have h1 : ((d.natAbs : ℕ) : ℤ) ∣ (σ : Matrix (Fin 3) (Fin 3) ℤ) i j - C i j :=
        (Dvd.intro_left 3 (by rw [hNdef]; push_cast; ring) : ((d.natAbs : ℕ) : ℤ) ∣ (N : ℤ)).trans
          (hσCN i j)
      have := dvd_add h1 (hCd i j)
      simpa using this
    have hmap : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod d.natAbs)) σ = 1 := by
      apply Subtype.ext
      have := intCast_matrix_eq_of_dvd hσ1
      simpa using this
    have hmapinv : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod d.natAbs)) σ⁻¹ = 1 := by
      rw [map_inv, hmap, inv_one]
    have hmat : (Int.castRingHom (ZMod d.natAbs)).mapMatrix
        ((σ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) =
        (Int.castRingHom (ZMod d.natAbs)).mapMatrix 1 := by
      have := congrArg (fun S : Matrix.SpecialLinearGroup (Fin 3) (ZMod d.natAbs) =>
        (S : Matrix (Fin 3) (Fin 3) (ZMod d.natAbs))) hmapinv
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_one] at this
      rw [this, map_one]
    intro i j
    have := dvd_of_intCast_matrix_eq hmat i j
    exact Int.natAbs_dvd.mp (by simpa using this)

end TernaryPeriodPolynomials.HeckeCommutativity
