module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.LineFaces

@[expose] public section


/-!
# Every rational line cusp of `Γ(N)` is an integral one

Formalized by Claude Sonnet 5.5.
Paper: Appendix C, ("we use the same letters for rational
conjugates at the other cusps").

Line analogue of `SeedC3S4c.exists_face_of_rational_plane`.  The anti-transpose `rt M = (i,j) ↦ M(2-j, 2-i)` is an anti-automorphism
of matrices exchanging the line parabolic `Q = {M₁₀ = M₂₀ = 0}` with the plane parabolic `P = {M₂₀ = M₂₁ = 0}`, preserving `SL₃(ℤ)` and
`Γ(N)`, and carrying `Γ(N) ∩ Q(ℤ)` onto `Γ(N) ∩ P(ℤ)`.  The plane theorem for `(rt g)⁻¹` therefore gives the line theorem for `g`.
-/

open scoped MatrixGroups
open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaces

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c

/-- The anti-transpose of a `3 × 3` matrix: `rt M i j = M (2-j) (2-i)`. -/
def rt {R : Type*} (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => M j.rev i.rev

theorem rt_apply {R : Type*} (M : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) : rt M i j = M j.rev i.rev := rfl

theorem rt_mul {R : Type*} [CommRing R] (A B : Matrix (Fin 3) (Fin 3) R) : rt (A * B) = rt B * rt A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rt, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev, mul_comm]
  all_goals ring

theorem rt_one {R : Type*} [CommRing R] : rt (1 : Matrix (Fin 3) (Fin 3) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rt, Fin.rev]

theorem rt_rt {R : Type*} (M : Matrix (Fin 3) (Fin 3) R) : rt (rt M) = M := by
  ext i j
  simp [rt]

theorem det_rt {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) : (rt M).det = M.det := by
  have : rt M = (M.transpose).submatrix Fin.revPerm Fin.revPerm := by
    ext i j; rfl
  rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

theorem rt_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin 3) (Fin 3) R) :
    rt (M.map f) = (rt M).map f := rfl

/-- The anti-transpose on `SL₃(ℤ)`. -/
def rtSL (A : SL(3, ℤ)) : SL(3, ℤ) := ⟨rt (A : Matrix (Fin 3) (Fin 3) ℤ), by rw [det_rt]; exact A.2⟩

theorem coe_rtSL (A : SL(3, ℤ)) : ((rtSL A : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = rt A := rfl

theorem rtSL_mul (A B : SL(3, ℤ)) : rtSL (A * B) = rtSL B * rtSL A := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_rtSL, coe_rtSL, coe_rtSL, Matrix.SpecialLinearGroup.coe_mul, rt_mul]

theorem rtSL_one : rtSL 1 = 1 := by
  apply Subtype.ext
  rw [coe_rtSL, Matrix.SpecialLinearGroup.coe_one, rt_one]

theorem rtSL_rtSL (A : SL(3, ℤ)) : rtSL (rtSL A) = A := by
  apply Subtype.ext
  rw [coe_rtSL, coe_rtSL, rt_rt]

theorem rtSL_inv (A : SL(3, ℤ)) : rtSL A⁻¹ = (rtSL A)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← rtSL_mul, mul_inv_cancel, rtSL_one]

theorem rtSL_mem_gammaN {N : ℕ} {A : SL(3, ℤ)} (hA : A ∈ gammaN N) : rtSL A ∈ gammaN N := by
  rw [mem_gammaN] at hA ⊢
  intro i j
  have := hA j.rev i.rev
  simpa [coe_rtSL, rt, Matrix.one_apply, Fin.rev_inj, eq_comm] using this

theorem lineStab_iff_rtSL (A : SL(3, ℤ)) : A ∈ lineStab ↔ rtSL A ∈ planeStab := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨by simpa [coe_rtSL, rt, Fin.rev] using h2, by simpa [coe_rtSL, rt, Fin.rev] using h1,
      by simpa [coe_rtSL, rt, Fin.rev] using h0⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨by simpa [coe_rtSL, rt, Fin.rev] using h2, by simpa [coe_rtSL, rt, Fin.rev] using h1,
      by simpa [coe_rtSL, rt, Fin.rev] using h0⟩

theorem gammaNQ_iff_rtSL (N : ℕ) (A : SL(3, ℤ)) : A ∈ gammaNQ N ↔ rtSL A ∈ gammaNP N := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨rtSL_mem_gammaN h1, (lineStab_iff_rtSL A).1 h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (lineStab_iff_rtSL A).2 h2⟩
    have := rtSL_mem_gammaN h1
    rwa [rtSL_rtSL] at this

/-- The inverse anti-transpose of a rational invertible matrix: `(rt g)⁻¹`, with matrix `rt (g⁻¹)`. -/
def rtGL (g : GL (Fin 3) ℚ) : GL (Fin 3) ℚ where
  val := rt ((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)
  inv := rt (g : Matrix (Fin 3) (Fin 3) ℚ)
  val_inv := by
    rw [← rt_mul, ← Units.val_mul, mul_inv_cancel]
    exact rt_one
  inv_val := by
    rw [← rt_mul, ← Units.val_mul, inv_mul_cancel]
    exact rt_one

theorem rtGL_val (g : GL (Fin 3) ℚ) :
    ((rtGL g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) = rt ((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) := rfl

theorem rtGL_inv_val (g : GL (Fin 3) ℚ) :
    (((rtGL g)⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) = rt (g : Matrix (Fin 3) (Fin 3) ℚ) := rfl

/-- Membership in the rational line parabolic `Q(ℚ)`: first column `(*, 0, 0)ᵗ`. -/
def InQQ (M : Matrix (Fin 3) (Fin 3) ℚ) : Prop := M 1 0 = 0 ∧ M 2 0 = 0

theorem inQQ_iff_inPQ_rt (M : Matrix (Fin 3) (Fin 3) ℚ) : InQQ M ↔ ConvergenceC4.InPQ (rt M) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa [rt, Fin.rev] using h2, by simpa [rt, Fin.rev] using h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa [rt, Fin.rev] using h2, by simpa [rt, Fin.rev] using h1⟩

/-- **Every rational line cusp is an integral one (line version).** For `N ≥ 3` and every rational line
`g Q g⁻¹`, `g ∈ GL₃(ℚ)`, there is an integral change of basis `h ∈ SL₃(ℤ)` such that the stabilizer of the line in `Γ(N)` is the line
group `Γ_{h⁻¹Qh}` (`gammaNQAt N h`). -/
theorem exists_lineFace_of_rational_line (N : ℕ) [NeZero N] (hN : 3 ≤ N) (g : GL (Fin 3) ℚ) :
    ∃ h : SL(3, ℤ), ∀ p ∈ gammaN N,
      InQQ (((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) *
          ((p : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
          ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) ↔ p ∈ gammaNQAt N h := by
  obtain ⟨h', hh', -⟩ := exists_face_of_rational_plane N hN (rtGL g)
  refine ⟨(rtSL h')⁻¹, fun p hp => ?_⟩
  have hp' : rtSL p ∈ gammaN N := rtSL_mem_gammaN hp
  have key := hh' (rtSL p) hp'
  rw [inQQ_iff_inPQ_rt]
  have e : rt (((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) *
      ((p : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
      ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) =
      (((rtGL g)⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) *
        (((rtSL p : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
        ((rtGL g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) := by
    rw [rtGL_inv_val, rtGL_val, coe_rtSL, ← rt_map, rt_mul, rt_mul]
    simp only [Matrix.mul_assoc]
  rw [e, key, mem_gammaNPAt, mem_gammaNQAt, gammaNQ_iff_rtSL]
  have : rtSL (((rtSL h')⁻¹) * p * ((rtSL h')⁻¹)⁻¹) = h' * rtSL p * h'⁻¹ := by
    rw [inv_inv, rtSL_mul, rtSL_mul, rtSL_inv, rtSL_rtSL]
    simp [mul_assoc]
  rw [this]

end TernaryPeriodPolynomials.Argument.GammaNFaces
