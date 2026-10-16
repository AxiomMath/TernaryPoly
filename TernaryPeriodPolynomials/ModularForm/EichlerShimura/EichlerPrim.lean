module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.LevelTwo

@[expose] public section


open MvPolynomial Matrix
open scoped MatrixGroups

/-!
# The Eichler primitive in coefficient coordinates

For a cusp form `f` of weight `n + 3`, the normalized Eichler primitive
`P(z) = ∑_j G_j(z) C(n+1, j) (-1)^{n+1-j} X₁^j X₀^{n+1-j}` (`eichlerPoly` of the library's moment
primitives `momentPrim`) is written in the monomial coefficient coordinates of D's `SymRep`
(`eichPrim`). It is holomorphic with derivative `f(z) (zX₁ - X₀)^{n+1}`, the last column of the Hodge
frame (`hasDerivAt_eichPrim`), and transforms by `P(δ z) = ρ(δ) P(z) + c_f(δ)` with `c_f` the
holomorphic period cocycle of `ESSpan` (`eichlerPoly_mob`, `eichPrim_mob`). These identify the
periods of the holomorphic part of a harmonic representative with `holCocycle f` in the Assembly of
the Eichler–Shimura route.

Written by Claude Opus 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.EichlerPrim

open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame

variable {Λ : Subgroup (GL (Fin 2) ℝ)} [Λ.HasDetOne] {n : ℕ} (F : CuspForm Λ ((n + 3 : ℕ) : ℤ))

/-- The transformation law of the Eichler primitive: `P(γz) = γ·P(z) + c(γ)`. -/
theorem eichlerPoly_mob {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Λ) {z : ℂ} (hz : 0 < z.im) :
    eichlerPoly n (momentPrim Λ n F) (mob γ z) =
      bind₁ (invCoordPoly γ) (eichlerPoly n (momentPrim Λ n F) z) +
        eichlerCocycle n (momentPrim Λ n F) γ := by
  have hdet : γ.det = 1 := Subgroup.HasDetOne.det_eq hγ
  apply MvPolynomial.funext
  intro v
  have hmod : ∀ w : ℂ, 0 < w.im → cuspH Λ n F (mob γ w) = dnm γ w ^ (n + 3) * cuspH Λ n F w :=
    fun w hw => modular_of_slashInvariant Λ (n + 3) F γ hγ w hw
  have hF : ∀ (v : Fin 2 → ℂ) (w : ℂ), 0 < w.im →
      HasDerivAt (fun u => eval v (eichlerPoly n (momentPrim Λ n F) u))
        (binaryIntegrand n (cuspH Λ n F) v w) w :=
    fun v w hw => eichlerPoly_hasDerivAt n _ _ (fun j u hu => momentPrim_hasDerivAt Λ n F j u hu) v hw
  have hI : (0 : ℝ) < Complex.I.im := by simp
  have hc := primitive_defect_const n (cuspH Λ n F) γ hdet hmod
    (fun v w => eval v (eichlerPoly n (momentPrim Λ n F) w)) hF v hz hI
  have hcoc := eval_eichlerCocycle n (momentPrim Λ n F) (momentPrim_zero Λ n F) γ v
  rw [map_add, ← eval_bind₁_invCoordPoly] at *
  unfold periodConst at hcoc
  rw [hcoc]
  linear_combination hc


omit [Λ.HasDetOne] in
theorem coords_eichlerPoly (G : ℕ → ℂ → ℂ) (w : ℂ) (i : Fin (n + 1 + 1)) :
    coords (n + 1) (eichlerPoly n G w) i =
      G i w * ((n + 1).choose i : ℂ) * (-1) ^ (n + 1 - i) := by
  rw [coords_eq_dehom (n + 1) (eichlerPoly_isHomogeneous n G w)]
  have : dehom (eichlerPoly n G w) = ∑ j ∈ Finset.range (n + 2),
      Polynomial.C (G j w * ((n + 1).choose j : ℂ) * (-1) ^ (n + 1 - j)) * Polynomial.X ^ j := by
    simp [eichlerPoly, dehom, map_sum]
  rw [this, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, i.2]

theorem coords_linPow (z : ℂ) (i : Fin (n + 1 + 1)) :
    coords (n + 1) ((C z * X 1 - X 0) ^ (n + 1) : MvPolynomial (Fin 2) ℂ) i =
      (-1) ^ (n + 1 - i) * ((n + 1).choose i : ℂ) * z ^ (i : ℕ) := by
  have hh : ((C z * X 1 - X 0) ^ (n + 1) : MvPolynomial (Fin 2) ℂ).IsHomogeneous (n + 1) := by
    have h1 : (C z * X 1 - X 0 : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
      ((isHomogeneous_C_mul_X z 1)).sub (isHomogeneous_X ℂ 0)
    simpa using h1.pow (n + 1)
  rw [coords_eq_dehom (n + 1) hh]
  have : dehom ((C z * X 1 - X 0) ^ (n + 1) : MvPolynomial (Fin 2) ℂ) =
      (Polynomial.C z * Polynomial.X - 1) ^ (n + 1) := by
    simp [dehom]
  rw [this, coeff_lin_pow]

/-- The Eichler primitive as a coefficient vector. -/
def eichPrim (z : ℂ) : Fin (n + 1 + 1) → ℂ := coords (n + 1) (eichlerPoly n (momentPrim Λ n F) z)

/-- The holomorphic derivative of the Eichler primitive is `F(z) (zX₁ - X₀)^{n+1}`. -/
theorem hasDerivAt_eichPrim {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (eichPrim F)
      (cuspH Λ n F z • coords (n + 1) ((C z * X 1 - X 0) ^ (n + 1) : MvPolynomial (Fin 2) ℂ)) z := by
  rw [hasDerivAt_pi]
  intro i
  have h := ((momentPrim_hasDerivAt Λ n F i z hz).mul_const ((n + 1).choose i : ℂ)).mul_const
    ((-1 : ℂ) ^ (n + 1 - i))
  have e : (fun w => eichPrim F w i) =
      fun w => momentPrim Λ n F i w * ((n + 1).choose i : ℂ) * (-1) ^ (n + 1 - i) := by
    funext w; exact coords_eichlerPoly _ w i
  rw [e]
  refine h.congr_deriv ?_
  rw [Pi.smul_apply, coords_linPow, smul_eq_mul]
  ring


section SL

variable {Λ₀ : Subgroup SL(2, ℤ)} (f : CuspForm (LamGL Λ₀) ((n + 3 : ℕ) : ℤ))

theorem partition_mob_eq_mob (δ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    TernaryPeriodPolynomials.Argument.ESFoundations.Partition.mob δ z =
      mob (Matrix.SpecialLinearGroup.mapGL ℝ δ) z := by
  rw [TernaryPeriodPolynomials.Argument.ESFoundations.Partition.mob_eq δ hz, mob]
  simp [Matrix.SpecialLinearGroup.mapGL]

/-- **Transformation law of the Eichler primitive** in coefficient coordinates:
`P(δ z) = ρ(δ) P(z) + c_f(δ)`. -/
theorem eichPrim_mob (δ : Λ₀) {z : ℂ} (hz : 0 < z.im) :
    eichPrim f (TernaryPeriodPolynomials.Argument.ESFoundations.Partition.mob δ z) =
      symRep (n + 1) δ *ᵥ eichPrim f z + coords (n + 1) (eichlerForm f δ.1).1 := by
  rw [partition_mob_eq_mob _ hz, eichPrim, eichlerPoly_mob f (Subgroup.mem_map_of_mem _ δ.2) hz,
    coords_add]
  congr 1
  exact (symRepGL_mulVec (n + 1) _ (eichlerPoly_isHomogeneous n _ z)).symm


/-- The antiholomorphic Eichler primitive: the coefficientwise conjugate. -/
def antiPrim (z : ℂ) : Fin (n + 1 + 1) → ℂ := fun i => starRingEnd ℂ (eichPrim f z i)

theorem coords_map_conj (P : MvPolynomial (Fin 2) ℂ) (i : Fin (n + 1 + 1)) :
    coords (n + 1) (MvPolynomial.map (starRingEnd ℂ) P) i = starRingEnd ℂ (coords (n + 1) P i) := by
  simp [coords, MvPolynomial.coeff_map]

/-- **Transformation law of the antiholomorphic primitive**:
`P̄(δ z) = ρ(δ) P̄(z) + c̄_f(δ)`, the antiholomorphic period cocycle of `ESSpan`. -/
theorem antiPrim_mob (δ : Λ₀) {z : ℂ} (hz : 0 < z.im) :
    antiPrim f (TernaryPeriodPolynomials.Argument.ESFoundations.Partition.mob δ z) =
      symRep (n + 1) δ *ᵥ antiPrim f z +
        coords (n + 1) (MvPolynomial.map (starRingEnd ℂ) (eichlerForm f δ.1).1) := by
  have h := eichlerPoly_mob f (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) δ.2) hz
  have hc := congrArg (MvPolynomial.map (starRingEnd ℂ)) h
  rw [map_add, map_conj_bind_invCoordPoly] at hc
  funext i
  simp only [antiPrim, eichPrim]
  rw [partition_mob_eq_mob _ hz, ← coords_map_conj, hc, coords_add, Pi.add_apply]
  congr 1
  rw [← symRepGL_mulVec (n + 1) _ ((eichlerPoly_isHomogeneous n _ z).map _)]
  simp only [Matrix.mulVec, dotProduct]
  congr 1

end SL

end TernaryPeriodPolynomials.Argument.ESFoundations.EichlerPrim
