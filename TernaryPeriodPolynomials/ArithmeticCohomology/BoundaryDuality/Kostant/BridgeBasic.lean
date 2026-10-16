module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.Swap
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Parabolic
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Levi

@[expose] public section


/-!
# Basic facts for the level-one bridge at the good line

The good line `L₁ = ⟨e₃⟩` has the radical lattice `latL1 = {I + 3x E₃₁ + 3y E₃₂}`, which is the
good-line radical lattice `lowerRadicalLattice` of `RadicalH1Levi`, and the Levi group `GL₂(ℤ)`
embedded as `diag(γ, 1)` (`leviHom`).  This module collects:

* `latL1_hom`: the lattice parametrization of the torus cycle is `lowerRadicalLattice`;
* `leviHom`: the Levi embedding, its values on `S` and `T`, its membership in the stabilizer of
  `L₁`, and the normalization of the lattice by the Levi group (`levi_inv_conj_lower`);
* `invT`: the inverse transpose of `GL₂(ℤ)`, with `φ (diag(γ, 1)) = diag(γ^{-T}, 1)` for the level
  involution `φ` (`dualInvolution_leviHom`);
* the independence of the coefficient representation from the character on determinant-one
  elements (`rho_radical_eq`), and the sign by which the twisted Levi action differs from the
  untwisted one;
* the equality of the actions `Sym^d ⊗ det^e` and `Sym^d ⊗ det^{e'}` of `GL₂(ℤ)` when `e - e'` is
  even (`homogeneousAction_even_twist`), which is how the dual coordinate is brought to the module
  prescribed by the parabolic duality.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (GL2Z toGL)

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
  (embedZ embedZ_apply uL1 zuL1_val zS_val zT₀_val zS zT₀ zg₂ zg₂_val zg₂_inv_val L₁ S T₀)

/-! ### The radical lattice -/

/-- The lattice of the good line is the good-line radical lattice. -/
theorem uL1_eq (x y : ℤ) : uL1 x y = lowerRadicalLattice (Multiplicative.ofAdd (x, y)) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uL1, embedZ_apply, zuL1_val, lowerRadicalLattice, lowerPlaneUnipotent]

/-- The parametrization of the lattice `latL1` is `lowerRadicalLattice`. -/
theorem latL1_hom : latL1.hom = lowerRadicalLattice := by
  apply MonoidHom.ext
  intro p
  change uL1 p.toAdd.1 p.toAdd.2 = _
  rw [uL1_eq]
  simp

/-- The radical lattice elements lie in `latL1`. -/
theorem lower_mem_sub (p : RadicalLattice) : lowerRadicalLattice p ∈ latL1.sub :=
  ⟨p, by rw [latL1_hom]⟩

/-- The elements of `latL1` are the radical lattice elements. -/
theorem exists_lower_of_mem_sub {u : RationalGL3} (hu : u ∈ latL1.sub) :
    ∃ p : RadicalLattice, lowerRadicalLattice p = u := by
  obtain ⟨p, hp⟩ := hu
  exact ⟨p, by rw [← hp, latL1_hom]⟩

/-! ### The Levi embedding -/

/-- The Levi embedding `GL₂(ℤ) → GL₃(ℚ)`, `γ ↦ diag(γ, 1)`. -/
def leviHom : GL2Z →* RationalGL3 :=
  (GeneralLinearGroup.map (Int.castRingHom ℚ)).comp planeLeviOneHom

theorem leviHom_eq (γ : GL2Z) : leviHom γ = arithmeticLevi γ := rfl

/-- The Levi embedding sends `S` to the matrix `S` of the good line. -/
theorem leviHom_S : leviHom (toGL ModularGroup.S) = S := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviHom, planeLeviOneHom, planeLevi, planeBlock, toGL, ModularGroup.coe_S, S,
      embedZ_apply, zS_val]

/-- The Levi embedding sends `T` to the matrix `T₀` of the good line. -/
theorem leviHom_T : leviHom (toGL ModularGroup.T) = T₀ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviHom, planeLeviOneHom, planeLevi, planeBlock, toGL, ModularGroup.coe_T, T₀,
      embedZ_apply, zT₀_val]

/-- The Levi embedding lies in the stabilizer of the good line in the level. -/
theorem leviHom_mem_level (γ : GL2Z) : leviHom γ ∈ levelStabilizer L₁ :=
  L2Matrices.mem_levelStabilizer_line (zg := planeLeviOneHom γ) (zr := zg₂)
    (L2Matrices.embedZ_mem_rationalLevel _ 0 0 (by simp [planeLeviOneHom, planeLevi, planeBlock])
      (by simp [planeLeviOneHom, planeLevi, planeBlock])
      (by simp [planeLeviOneHom, planeLevi, planeBlock]))
    (by
      simp only [Units.val_mul, zg₂_inv_val, zg₂_val]
      simp [Matrix.mul_apply, Fin.sum_univ_three, planeLeviOneHom, planeLevi, planeBlock])
    (by
      simp only [Units.val_mul, zg₂_inv_val, zg₂_val]
      simp [Matrix.mul_apply, Fin.sum_univ_three, planeLeviOneHom, planeLevi, planeBlock])

/-- The Levi element conjugates the lattice: `k⁻¹ u(p) k = u(p · γ)`. -/
theorem levi_inv_conj_lower (γ : GL2Z) (p : RadicalLattice) :
    (leviHom γ)⁻¹ * lowerRadicalLattice p * leviHom γ =
      lowerRadicalLattice (lowerLeviLatticeInput γ p) := by
  have h := lowerLeviLatticeInput_conjugation γ p
  rw [leviHom_eq, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact h

/-- The inverse Levi element normalizes the lattice: `k⁻¹ u k ∈ latL1`. -/
theorem levi_inv_normalizes (γ : GL2Z) : ∀ u ∈ latL1.sub, (leviHom γ)⁻¹ * u * leviHom γ ∈ latL1.sub := by
  intro u hu
  obtain ⟨p, rfl⟩ := exists_lower_of_mem_sub hu
  rw [levi_inv_conj_lower]
  exact lower_mem_sub _

/-- The Levi element normalizes the lattice: `k u k⁻¹ ∈ latL1`. -/
theorem levi_normalizes (γ : GL2Z) : ∀ u ∈ latL1.sub, leviHom γ * u * (leviHom γ)⁻¹ ∈ latL1.sub := by
  intro u hu
  have h := levi_inv_normalizes γ⁻¹ u hu
  rwa [map_inv, inv_inv] at h

/-! ### The inverse transpose of `GL₂(ℤ)` -/

/-- The inverse transpose `γ ↦ (γ⁻¹)ᵀ` of `GL₂(ℤ)`. -/
def invT (γ : GL2Z) : GL2Z :=
  ⟨(γ⁻¹ : GL2Z).val.transpose, γ.val.transpose, by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one], by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

/-- The matrix of `γ * (invT γ)ᵀ` is the identity. -/
theorem mul_invT_transpose (γ : GL2Z) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((invT γ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)ᵀ = 1 := by
  change (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)ᵀᵀ = 1
  rw [Matrix.transpose_transpose, Units.mul_inv]

/-- The inverse transpose of a Levi element is the Levi element of the inverse transpose. -/
theorem inverseTranspose_leviHom (γ : GL2Z) :
    inverseTranspose (leviHom γ) = leviHom (invT γ) := by
  apply Units.ext
  change (((leviHom γ)⁻¹ : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ).transpose =
    ((leviHom (invT γ) : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ)
  rw [← map_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviHom, planeLeviOneHom, planeLevi, planeBlock, invT]

/-- The level involution of a Levi element is the Levi element of the inverse transpose. -/
theorem dualInvolution_leviHom (γ : GL2Z) : dualInvolution (leviHom γ) = leviHom (invT γ) := by
  have hL : ((levelScale : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      Matrix.diagonal ![1, 1, 3] := rfl
  have hLi : (((levelScale⁻¹ : RationalGL3)) : Matrix (Fin 3) (Fin 3) ℚ) =
      Matrix.diagonal ![1, 1, 1 / 3] := rfl
  rw [dualInvolution_apply, inverseTranspose_leviHom]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hL, hLi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, leviHom, planeLeviOneHom, planeLevi,
      planeBlock]

/-- The determinant of the inverse transpose equals the determinant. -/
theorem det_invT (γ : GL2Z) :
    (((GeneralLinearGroup.det (invT γ) : ℤˣ)) : ℤ) = (((GeneralLinearGroup.det γ : ℤˣ)) : ℤ) := by
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply]
  change ((γ⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)ᵀ.det = _
  rw [Matrix.det_transpose, ← GeneralLinearGroup.val_det_apply, ← GeneralLinearGroup.val_det_apply,
    map_inv, Int.units_inv_eq_self]

/-! ### Coefficients -/

/-- On determinant-one elements the coefficient representation does not depend on the
character. -/
theorem detSign_eq_one_of_det {χ : RankOneCharacter} {g : RationalGL3}
    (hg : GeneralLinearGroup.det g = 1) : Twisted.detSign χ g = 1 := by
  rw [Twisted.detSign, MonoidHom.comp_apply, componentCharacter, MonoidHom.comp_apply,
    MonoidHom.comp_apply, det_map_eq_one (algebraMap ℚ ℝ) hg, map_one, map_one]

/-- On determinant-one elements the coefficient representation does not depend on the
character. -/
theorem rho_radical_eq (n : ℕ) (χ : RankOneCharacter) {g : RationalGL3}
    (hg : GeneralLinearGroup.det g = 1) :
    rationalCoefficientComponent n χ g = rationalCoefficientComponent n trivialCharacter g := by
  rw [Twisted.rho_eq_detSign_smul, detSign_eq_one_of_det hg, one_smul]

theorem det_lowerRadicalLattice (p : RadicalLattice) :
    GeneralLinearGroup.det (lowerRadicalLattice p) = 1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply]
  simp [lowerRadicalLattice, lowerPlaneUnipotent, Matrix.det_fin_three]

theorem det_upperRadicalLattice (p : RadicalLattice) :
    GeneralLinearGroup.det (upperRadicalLattice p) = 1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply]
  simp [upperRadicalLattice, planeUnipotent, Matrix.det_fin_three]

/-- The radical lattice acts on the coefficients independently of the character. -/
theorem rho_lower_eq (n : ℕ) (χ : RankOneCharacter) (p : RadicalLattice) :
    rationalCoefficientComponent n χ (lowerRadicalLattice p) =
      (lowerRadicalLatticeRep n).ρ p := by
  rw [lowerRadicalLatticeRep_rho]
  exact rho_radical_eq n χ (det_lowerRadicalLattice p)

/-- The level involution of the radical lattice acts independently of the character. -/
theorem rho_dual_lower_eq (n : ℕ) (χ : RankOneCharacter) (p : RadicalLattice) :
    rationalCoefficientComponent n χ (dualInvolution (lowerRadicalLattice p)) =
      (upperRadicalLatticeRep n).ρ p⁻¹ := by
  have h : dualInvolution (lowerRadicalLattice p) = upperRadicalLattice p⁻¹ := by
    have h1 := dualInvolution_lowerRadicalLattice_mul p
    rw [mul_eq_one_iff_eq_inv] at h1
    rw [h1, ← map_inv]
  rw [h, upperRadicalLatticeRep_rho]
  exact rho_radical_eq n χ (det_upperRadicalLattice _)

/-! ### Even twists of the binary action -/

theorem det_map_complex (γ : GL2Z) :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) : ℂˣ) : ℂ) =
      (((GeneralLinearGroup.det γ : ℤˣ) : ℤ) : ℂ) := by
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply,
    GeneralLinearGroup.val_map_apply]
  exact (RingHom.map_det (Int.castRingHom ℂ) (γ : Matrix (Fin 2) (Fin 2) ℤ)).symm

/-- The actions `Sym^d ⊗ det^e` and `Sym^d ⊗ det^{e'}` of `GL₂(ℤ)` agree when `e - e'` is even. -/
theorem homogeneousAction_even_twist (d : ℕ) (e e' : ℤ) (h : Even (e - e')) (γ : GL2Z) :
    Binary.homogeneousAction d e (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) =
      Binary.homogeneousAction d e' (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  rw [Binary.homogeneousAction_coe, Binary.homogeneousAction_coe, Binary.action_apply,
    Binary.action_apply]
  congr 1
  change ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) : ℂˣ) : ℂ) ^ e =
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) : ℂˣ) : ℂ) ^ e'
  rw [det_map_complex]
  obtain ⟨k, hk⟩ := h
  have he : e = e' + (k + k) := by omega
  rcases Int.units_eq_one_or (GeneralLinearGroup.det γ) with hd | hd
  · rw [hd]
    simp
  · rw [hd, he]
    have hn : (((-1 : ℤˣ) : ℤ) : ℂ) = -1 := by simp
    have hev : Even (k + k) := ⟨k, rfl⟩
    rw [hn, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hev.neg_one_zpow, mul_one]

/-- The good-line radical action as an endomorphism of the space of forms. -/
abbrev rhoLow (n : ℕ) (p : RadicalLattice) : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n :=
  (lowerRadicalLatticeRep n).ρ p

/-- The identity-plane radical action as an endomorphism of the space of forms. -/
abbrev rhoUp (n : ℕ) (p : RadicalLattice) : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n :=
  (upperRadicalLatticeRep n).ρ p

/-- The value of an identity-plane radical cocycle, as a form. -/
abbrev wv (n : ℕ) (w : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) (p : RadicalLattice) :
    HomogeneousPoly n :=
  w p

/-- A form, viewed as an element of the good-line radical representation. -/
abbrev asLow (n : ℕ) (x : HomogeneousPoly n) : lowerRadicalLatticeRep n := x

/-- A form, viewed as an element of the identity-plane radical representation. -/
abbrev asUp (n : ℕ) (x : HomogeneousPoly n) : upperRadicalLatticeRep n := x

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
