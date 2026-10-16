module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Reduction

@[expose] public section


/-!
# Lemma B.1: `G(w, C)` is well rounded for every minimum-one binary form `C`

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.3: "`G(w,C)` is positive definite; its minimum is one; the vectors `(1, -z*)` and
the two shortest vectors of `C` (in the `b, c` directions) have length one, so `G(w,C)` is well
rounded."

For a minimum-one well-rounded binary form `C` (`BinWR`) and every `w ∈ ℝ²`:

* `G(w, C)` is positive definite;
* every nonzero integral vector `(k, z)` has squared length `≥ 1`;
* there are integral vectors `(1, z₀)`, `(0, v₁)`, `(0, v₂)` of squared length exactly one,
  forming a basis of `ℤ³` (the determinant is `±1`): `G(w, C)` has three independent minimal
  vectors.

The proof reduces to `C = DᵗC(t)D` (`BinWR_reduce`) and transports the case `C(t)` of
`Geometry.lean` along the equivariance `pᵗ G(Dw, C(t)) p = G(w, DᵗC(t)D)`, `p = [[1,0],[0,D]]`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry

open Matrix

/-- Values of `G(w, DᵗCD)` on `(k, z)` equal the values of `G(Dw, C)` on `(k, Dz)`. -/
theorem Gmat_val_conj {C : Mat2} (hC : Cᵀ = C) (D E : IMat2) (hDE : D * E = 1)
    (hED : E * D = 1) (w : Vec2) (k : ℝ) (z : Vec2) :
    vec3 k z ⬝ᵥ (Gmat w ((castMat D)ᵀ * C * castMat D) *ᵥ vec3 k z) =
      vec3 k (castMat D *ᵥ z) ⬝ᵥ (Gmat (castMat D *ᵥ w) C *ᵥ vec3 k (castMat D *ᵥ z)) := by
  have h0 : intVec (0 : Fin 2 → ℤ) = 0 := by funext i; simp [intVec]
  have h := Gmat_equivariant hC D E hDE hED 0 1 (Or.inl rfl) (castMat D *ᵥ w) w
    (by simp [h0])
  rw [← h, quad_conj3, parab_vec]
  simp [h0]

theorem castMat_mulVec_eq_zero {D D' : IMat2} (h : D' * D = 1) {v : Vec2}
    (hv : castMat D *ᵥ v = 0) : v = 0 := by
  have hmul' : castMat D' * castMat D = 1 := by rw [← castMat_mul, h, castMat_one]
  have h' : castMat D' *ᵥ (castMat D *ᵥ v) = castMat D' *ᵥ 0 := by rw [hv]
  rwa [Matrix.mulVec_mulVec, hmul', Matrix.one_mulVec, Matrix.mulVec_zero] at h'

theorem mulVec_eq_zero_int {D D' : IMat2} (h : D' * D = 1) {z : Fin 2 → ℤ}
    (hz : D *ᵥ z = 0) : z = 0 := by
  have h' : D' *ᵥ (D *ᵥ z) = D' *ᵥ 0 := by rw [hz]
  rwa [Matrix.mulVec_mulVec, h, Matrix.one_mulVec, Matrix.mulVec_zero] at h'

/-- **`G(w,C)` is well rounded** for every minimum-one binary form `C`. -/
theorem Gmat_wellRounded {C : Mat2} (hC : BinWR C) (w : Vec2) :
    PosDefQ (Gmat w C) ∧
    (∀ (k : ℤ) (z : Fin 2 → ℤ), (k ≠ 0 ∨ z ≠ 0) →
      1 ≤ vec3 (k : ℝ) (intVec z) ⬝ᵥ (Gmat w C *ᵥ vec3 (k : ℝ) (intVec z))) ∧
    ∃ z₀ v₁ v₂ : Fin 2 → ℤ,
      vec3 1 (intVec z₀) ⬝ᵥ (Gmat w C *ᵥ vec3 1 (intVec z₀)) = 1 ∧
      vec3 0 (intVec v₁) ⬝ᵥ (Gmat w C *ᵥ vec3 0 (intVec v₁)) = 1 ∧
      vec3 0 (intVec v₂) ⬝ᵥ (Gmat w C *ᵥ vec3 0 (intVec v₂)) = 1 ∧
      ((!![1, 0, 0; z₀ 0, v₁ 0, v₂ 0; z₀ 1, v₁ 1, v₂ 1] : Matrix (Fin 3) (Fin 3) ℤ).det = 1 ∨
       (!![1, 0, 0; z₀ 0, v₁ 0, v₂ 0; z₀ 1, v₁ 1, v₂ 1] : Matrix (Fin 3) (Fin 3) ℤ).det = -1) := by
  obtain ⟨t, ht, D, D', h1, h2, rfl⟩ := BinWR_reduce hC
  have hCt : (Ct t) 1 0 = (Ct t) 0 1 := by simp [Ct]
  have hpsd : ∀ v, 0 ≤ quad (Ct t) v := quad_Ct_nonneg (by linarith [abs_nonneg t])
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Gmat_symm (castMat_symm (Ct_symm t) D) w, ?_⟩
    intro v hv
    have hv' : v = vec3 (v 0) ![v 1, v 2] := by
      funext i; fin_cases i <;> simp [vec3]
    rw [hv', Gmat_val_conj (Ct_symm t) D D' h1 h2]
    apply (Gmat_posDef ht (castMat D *ᵥ w)).2
    intro h0
    apply hv
    have h00 : v 0 = 0 := by simpa [vec3] using congrFun h0 0
    have hz : castMat D *ᵥ ![v 1, v 2] = 0 := by
      funext i
      have := congrFun h0 i.succ
      fin_cases i <;> simpa [vec3] using this
    have := castMat_mulVec_eq_zero h2 hz
    funext i
    fin_cases i
    · simpa using h00
    · simpa using congrFun this 0
    · simpa using congrFun this 1
  · intro k z hkz
    rw [Gmat_val_conj (Ct_symm t) D D' h1 h2, castMat_mulVec_intVec]
    apply Gmat_min_one hCt hpsd (Ct_min_one ht) (castMat D *ᵥ w)
    · have := deltaSq_Ct_le ht (castMat D *ᵥ w)
      have habs := abs_nonneg t
      have : 1 / (2 * (1 + |t|)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    · rcases hkz with hk | hz
      · exact Or.inl hk
      · exact Or.inr (fun h => hz (mulVec_eq_zero_int h2 h))
  · obtain ⟨z, hz1, hz2, hz3, -⟩ := Gmat_min_vectors ht (castMat D *ᵥ w)
    have hDD : D *ᵥ (D' *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    have hDe : ∀ e : Fin 2 → ℤ, D *ᵥ (D' *ᵥ e) = e := fun e => by
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    refine ⟨D' *ᵥ z, D' *ᵥ ![1, 0], D' *ᵥ ![0, 1], ?_, ?_, ?_, ?_⟩
    · rw [Gmat_val_conj (Ct_symm t) D D' h1 h2, castMat_mulVec_intVec, hDD]
      exact hz1
    · rw [Gmat_val_conj (Ct_symm t) D D' h1 h2, castMat_mulVec_intVec, hDe]
      have e : intVec (![1, 0] : Fin 2 → ℤ) = ![1, 0] := by
        funext i; fin_cases i <;> simp [intVec]
      rw [e]
      exact hz2
    · rw [Gmat_val_conj (Ct_symm t) D D' h1 h2, castMat_mulVec_intVec, hDe]
      have e : intVec (![0, 1] : Fin 2 → ℤ) = ![0, 1] := by
        funext i; fin_cases i <;> simp [intVec]
      rw [e]
      exact hz3
    · have hd : D.det * D'.det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
      have hd' : D'.det = 1 ∨ D'.det = -1 := Int.eq_one_or_neg_one_of_mul_eq_one' hd |>.elim
        (fun h => Or.inl h.2) (fun h => Or.inr h.2)
      have e : (!![1, 0, 0; (D' *ᵥ z) 0, (D' *ᵥ ![1, 0]) 0, (D' *ᵥ ![0, 1]) 0;
          (D' *ᵥ z) 1, (D' *ᵥ ![1, 0]) 1, (D' *ᵥ ![0, 1]) 1] : Matrix (Fin 3) (Fin 3) ℤ).det =
          D'.det := by
        simp [Matrix.det_fin_three, Matrix.det_fin_two, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two]
      rw [e]
      exact hd'

end TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry
