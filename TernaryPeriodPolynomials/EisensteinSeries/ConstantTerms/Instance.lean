module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Equivariance
public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Consumer

@[expose] public section


/-!
# Proposition C.4: the instance `Γ = Γ(N)`

The hypothesis `LeviIn Γ Λ` of the convergence and equivariance theorems says that the Levi block
of every element of the integral plane stabilizer `Γ ∩ P(ℤ)` lies in the group `Λ` for which the
cusp form is modular. For the principal congruence subgroups `Γ = Γ(N)` of `SL₃(ℤ)`
(the paper's neat normal subgroup of level divisible by three) it is a theorem: with
`Λ_N = Γ₂(N)` (the image in `GL₂(ℝ)`), `leviIn_gammaN` proves it, and `mem_leviGroup_iff` shows
that `Λ_N` is exactly the Levi projection of `Γ ∩ P(ℤ)`. For `N ≥ 3` the integral plane
stabilizer `Γ(N) ∩ P(ℤ)` is `Γ(N) ∩ P(ℚ)` (`gammaN_inf_rationalPlane`). The group `Γ(N)` is the
preimage of the project's `IntegralGL3Congruence.principal N`: it is normal (so normal in `K` and
`K†`), contained in `K` when `3 ∣ N`, and torsion-free when `3 ∣ N`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped MatrixGroups
open TernaryPoly.IntegralGL3Congruence CongruenceSubgroup Matrix

/-- The principal congruence subgroup `Γ(N) ⊂ SL₃(ℤ)`, the preimage of the project's
`IntegralGL3Congruence.principal N ⊂ GL₃(ℤ)`. -/
def gammaN (N : ℕ) : Subgroup SL(3, ℤ) :=
  (principal N).comap (Matrix.SpecialLinearGroup.toGL : SL(3, ℤ) →* _)

theorem mem_gammaN {N : ℕ} {γ : SL(3, ℤ)} :
    γ ∈ gammaN N ↔ ∀ i j, (N : ℤ) ∣ (γ : Matrix (Fin 3) (Fin 3) ℤ) i j -
      (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
  unfold gammaN
  rw [Subgroup.mem_comap, mem_principal_iff]
  rfl

instance gammaN_normal (N : ℕ) : (gammaN N).Normal := by
  unfold gammaN
  infer_instance

theorem entry_eq_of_mem_gammaN {N : ℕ} {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N) (i j : Fin 3) :
    (((γ : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod N) =
      (((1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod N) := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr (mem_gammaN.1 hγ i j)
  rwa [Int.cast_sub, sub_eq_zero] at this

/-- For `N ≥ 3`, an element of `Γ(N)` lying in a rational parabolic (bottom row `(0, 0, c)`) has
`c = 1`: it lies in the plane stabilizer. -/
theorem mem_planeStab_of_gammaN {N : ℕ} (hN : 3 ≤ N) {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N)
    (h0 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0) (h1 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0) :
    γ ∈ planeStab := by
  refine ⟨h0, h1, ?_⟩
  have hdet : (γ : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := γ.2
  rw [Matrix.det_fin_three, h0, h1] at hdet
  have hu : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 2 *
      ((γ : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 1 -
        (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 1 * (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 0) = 1 := by
    linear_combination hdet
  rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hu) with h | h
  · exact h
  · exfalso
    have hd := mem_gammaN.1 hγ 2 2
    rw [h] at hd
    have h2 : (N : ℤ) ∣ 2 := by
      have := dvd_neg.mpr hd
      simpa using this
    have := Int.le_of_dvd (by norm_num) h2
    omega

/-- The arithmetic group `Λ_N ⊂ GL₂(ℝ)` of the binary cusp forms: the image of the principal
congruence subgroup `Γ₂(N) ⊂ SL₂(ℤ)`. -/
abbrev leviGroup (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- The determinant-one binary matrix cut out by the Levi block of a plane-stabilizer element. -/
def leviBlock (γ : SL(3, ℤ)) (hγ : γ ∈ planeStab) : SL(2, ℤ) :=
  ⟨!![(γ : Matrix (Fin 3) (Fin 3) ℤ) 0 0, (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 1;
      (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 0, (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 1], by
    obtain ⟨h0, h1, h2⟩ := hγ
    have hdet : (γ : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := γ.2
    rw [Matrix.det_fin_three, h0, h1, h2] at hdet
    rw [Matrix.det_fin_two_of]
    linear_combination hdet⟩

theorem coe_mapGL_leviBlock (γ : SL(3, ℤ)) (hγ : γ ∈ planeStab) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ (leviBlock γ hγ) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = topBlock (realMat γ) := by
  ext a b
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  fin_cases a <;> fin_cases b <;> rfl

theorem leviBlock_mem_Gamma {N : ℕ} {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N) (hs : γ ∈ planeStab) :
    leviBlock γ hs ∈ Gamma N := by
  rw [Gamma_mem]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [leviBlock] using entry_eq_of_mem_gammaN hγ 0 0
  · simpa [leviBlock] using entry_eq_of_mem_gammaN hγ 0 1
  · simpa [leviBlock] using entry_eq_of_mem_gammaN hγ 1 0
  · simpa [leviBlock] using entry_eq_of_mem_gammaN hγ 1 1

/-- **Compatibility of the cusp group.** The Levi block of every element of `Γ(N) ∩ P(ℤ)` lies in
`Λ_N = Γ₂(N)`: this is the hypothesis `LeviIn` of the convergence theorem, proved here for the
principal congruence subgroups. -/
theorem leviIn_gammaN (N : ℕ) : LeviIn (gammaN N) (leviGroup N) := by
  intro γ hγ hs
  exact ⟨_, Subgroup.mem_map_of_mem _ (leviBlock_mem_Gamma hγ hs), coe_mapGL_leviBlock γ hs⟩

/-- The block-diagonal element `diag(A, 1) ∈ SL₃(ℤ)`. -/
def blockDiag (A : SL(2, ℤ)) : SL(3, ℤ) :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1, 0;
      (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1, 0; 0, 0, 1], by
    have hA : (A : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := A.2
    rw [Matrix.det_fin_two] at hA
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_fin_const]
    linear_combination hA⟩

theorem blockDiag_mem_planeStab (A : SL(2, ℤ)) : blockDiag A ∈ planeStab :=
  ⟨by simp [blockDiag], by simp [blockDiag], by simp [blockDiag]⟩

theorem blockDiag_mem_gammaN {N : ℕ} {A : SL(2, ℤ)} (hA : A ∈ Gamma N) : blockDiag A ∈ gammaN N := by
  rw [Gamma_mem] at hA
  rw [mem_gammaN]
  have d : ∀ x y : ℤ, (x : ZMod N) = (y : ZMod N) → (N : ℤ) ∣ x - y := fun x y h =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by rw [Int.cast_sub, h, sub_self])
  intro i j
  fin_cases i <;> fin_cases j <;> simp [blockDiag]
  · exact d _ 1 (by simpa using hA.1)
  · simpa using d _ 0 (by simpa using hA.2.1)
  · simpa using d _ 0 (by simpa using hA.2.2.1)
  · exact d _ 1 (by simpa using hA.2.2.2)

theorem topBlock_blockDiag (A : SL(2, ℤ)) :
    topBlock (realMat (blockDiag A)) =
      ((Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext a b
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  fin_cases a <;> fin_cases b <;> simp [blockDiag, topBlock, realMat, Matrix.SpecialLinearGroup.map_apply_coe]

/-- **`Λ_N` is exactly the Levi projection of `Γ_P`.** For `Γ = Γ(N)`, a binary matrix `g` lies in
`Λ_N = Γ₂(N)` iff it is the determinant-one Levi block of an element of
`Γ(N) ∩ P(ℤ)`; the paper's `Λ_P` is `Γ₂(N)`. -/
theorem mem_leviGroup_iff (N : ℕ) (g : GL (Fin 2) ℝ) :
    g ∈ leviGroup N ↔ ∃ γ ∈ gammaN N, γ ∈ planeStab ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) = topBlock (realMat γ) := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨blockDiag A, blockDiag_mem_gammaN hA, blockDiag_mem_planeStab A,
      (topBlock_blockDiag A).symm⟩
  · rintro ⟨γ, hγ, hs, hg⟩
    obtain ⟨g', hg', hg'e⟩ := leviIn_gammaN N γ hγ hs
    have : g = g' := Units.ext (hg.trans hg'e.symm)
    exact this ▸ hg'

/-- For `N ≥ 3` the stabilizer `Γ(N) ∩ P(ℚ)` of the rational plane is `Γ(N) ∩ P(ℤ)`, the
subgroup `planeStab` with bottom row `(0, 0, 1)`: the paper's `Γ_P` is the group the series
is summed over. -/
theorem gammaN_inf_rationalPlane {N : ℕ} (hN : 3 ≤ N) {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N) :
    γ ∈ planeStab ↔ (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧ (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => mem_planeStab_of_gammaN hN hγ h.1 h.2⟩

/-- `Γ(N)` is a subgroup of `K = {g : ℓ g = ℓ (mod 3)}` when `3 ∣ N`. -/
theorem toGL_mem_K_of_mem_gammaN {N : ℕ} (h3 : 3 ∣ N) {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N) :
    (Matrix.SpecialLinearGroup.toGL γ) ∈ TernaryPoly.ModThreeGoodAction.K := by
  refine principalThree_le_K ?_
  rw [mem_principal_iff]
  intro i j
  exact dvd_trans (by exact_mod_cast h3) (mem_gammaN.1 hγ i j)

/-- Level divisible by three: `Γ(N)` is torsion-free (hence neat in the sense of the project). -/
theorem gammaN_torsionFree {N : ℕ} (h3 : 3 ∣ N) {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N)
    (hfin : IsOfFinOrder γ) : γ = 1 := by
  have h := principalThree_finiteOrder_eq_one (Matrix.SpecialLinearGroup.toGL γ) (by
    rw [mem_principal_iff]
    intro i j
    exact dvd_trans (by exact_mod_cast h3) (mem_gammaN.1 hγ i j))
    (Matrix.SpecialLinearGroup.toGL.isOfFinOrder hfin)
  have := congrArg (fun u : GL (Fin 3) ℤ => (u : Matrix (Fin 3) (Fin 3) ℤ)) h
  exact Subtype.ext this

end TernaryPeriodPolynomials.Argument.ConvergenceC4
