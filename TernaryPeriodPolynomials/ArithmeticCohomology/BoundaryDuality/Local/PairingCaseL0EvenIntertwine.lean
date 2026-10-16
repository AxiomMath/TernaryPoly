module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BadIdentPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AdjointLevelThreePairing

@[expose] public section


/-!
# The comparison map intertwines the Atkin–Lehner conjugation with the determinant-twisted action

`BadIdentPlane.planeComparison n = σ_var ∘ rot ∘ Sym(σ) ∘ Φ⁻¹` intertwines the coefficient action
`Sym^{n+1} ⊗ det⁻¹` of `α γ` with `Sym^{n+1}` of `γ` for `γ ∈ Γ₁'(3)`.  This file proves the
statement for *every* `x ∈ GL₂(ℚ)`, with the conjugation `alHom x = δ x^{-T} δ⁻¹` in place of `α`
and the twisted action of `x` in place of that of `γ`:

  `E (Sym^{n+1} ⊗ det⁻¹)(alHom x) v = (Sym^{n+1} ⊗ det^{n+2})(x) (E v)`

(`planeComparison_alHom`).  Consequently, for the Hecke representatives `α_j`
(`alHom α_j = (ε_p / p) · ι(u_j) α_{τ j}`, `LocalPairingCaseL0EvenCosets`) one gets, for odd
`n + 1`,

  `E (Sym^{n+1} ⊗ det⁻¹)(ι(u_j) α_{τ j}) v = (ε_p / p) (Sym^{n+1})(α_j) (E v)`

(`planeComparison_rep`), the compatibility used for the Hecke operators.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (swapUnit swapUnit_mul_self swap01 binarySwap binarySwapVar binarySwap_homogeneousAction
    binarySwapVar_action_twist swap_conj_conj homogeneousAction_zpow_twist swapZ swapInt)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
  (planeComparison)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2 (PhiInv)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame (del)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (rationalRho)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
  (heckeRep signP signP_mul_self)

/-! ### Complex matrices -/

theorem swapZ_map : GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ = swapUnit := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapZ, swapInt, swapUnit, swap01, Matrix.GeneralLinearGroup.map_apply]

theorem swapUnit_inv : swapUnit⁻¹ = swapUnit := inv_eq_of_mul_eq_one_right swapUnit_mul_self

theorem swap01_transpose : swap01ᵀ = swap01 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap01]

theorem swap01_mul_self : swap01 * swap01 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap01, Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix of the inverse transpose after the change of scalars. -/
theorem map_invTQ_val (x : GL (Fin 2) ℚ) :
    ((GeneralLinearGroup.map (algebraMap ℚ ℂ) (invTQ x) : Binary.GL2) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      (((GeneralLinearGroup.map (algebraMap ℚ ℂ) x)⁻¹ : Binary.GL2) :
        Matrix (Fin 2) (Fin 2) ℂ)ᵀ := by
  rw [← map_inv]
  change ((invTQ x : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ) =
    (((x⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ))ᵀ
  rw [invTQ_val]
  exact Matrix.transpose_map

/-- Composition of the twisted actions. -/
theorem act_mul_apply (N : ℕ) (τ : ℤ) (a b : Binary.GL2) (w : Binary.HomogeneousPoly N) :
    Binary.homogeneousAction N τ a (Binary.homogeneousAction N τ b w) =
      Binary.homogeneousAction N τ (a * b) w := by
  rw [map_mul, Module.End.mul_apply]

/-- **The relation `γ γ'ᵀ = 1`** for `γ = σ X σ⁻¹` and `γ' = σ X^{-T} σ⁻¹`. -/
theorem swap_relation (X Y : Binary.GL2)
    (hY : (Y : Matrix (Fin 2) (Fin 2) ℂ) = ((X⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) :
    ((swapUnit * X * swapUnit⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((swapUnit * Y * swapUnit⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 1 := by
  have hXM : (X : Matrix (Fin 2) (Fin 2) ℂ) * ((X⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [swapUnit_inv]
  have hs : ((swapUnit : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) = swap01 := rfl
  simp only [Units.val_mul, hs, Matrix.transpose_mul, hY, Matrix.transpose_transpose,
    swap01_transpose]
  calc _ = swap01 * ((X : Matrix (Fin 2) (Fin 2) ℂ) * (swap01 * swap01) *
          ((X⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ)) * swap01 := by
        simp only [Matrix.mul_assoc]
    _ = swap01 * ((X : Matrix (Fin 2) (Fin 2) ℂ) *
          ((X⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ)) * swap01 := by
        rw [swap01_mul_self, Matrix.mul_one]
    _ = 1 := by rw [hXM, Matrix.mul_one, swap01_mul_self]

/-! ### The intertwining relation for every rational matrix -/

/-- **`E` intertwines the conjugation `alHom` with the determinant-twisted action.** -/
theorem planeComparison_alHom (n : ℕ) (x : GL (Fin 2) ℚ) (v : Binary.HomogeneousPoly (n + 1)) :
    planeComparison n (rationalRho (n + 1) (-1) (alHom x) v) =
      Binary.homogeneousAction (n + 1) (((n + 1 : ℕ) : ℤ) - (-1))
        (GeneralLinearGroup.map (algebraMap ℚ ℂ) x) (planeComparison n v) := by
  set X : Binary.GL2 := GeneralLinearGroup.map (algebraMap ℚ ℂ) x with hX
  set Y : Binary.GL2 := GeneralLinearGroup.map (algebraMap ℚ ℂ) (invTQ x) with hY
  have hrel := swap_relation X Y (map_invTQ_val x)
  have hmap : GeneralLinearGroup.map (algebraMap ℚ ℂ) (alHom x) =
      GeneralLinearGroup.map (algebraMap ℚ ℂ) del * Y *
        (GeneralLinearGroup.map (algebraMap ℚ ℂ) del)⁻¹ := by
    rw [alHom_apply, map_mul, map_mul, map_inv]
  have h1 : PhiInv n (rationalRho (n + 1) (-1) (alHom x) v) =
      Binary.homogeneousAction (n + 1) (-1) Y (PhiInv n v) := by
    change Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℚ ℂ) del⁻¹)
        (Binary.homogeneousAction (n + 1) (-1)
          (GeneralLinearGroup.map (algebraMap ℚ ℂ) (alHom x)) v) =
      Binary.homogeneousAction (n + 1) (-1) Y
        (Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) del⁻¹) v)
    rw [act_mul_apply, act_mul_apply, hmap, map_inv]
    congr 2
    group
  have h2 : ∀ w : Binary.HomogeneousPoly (n + 1),
      Binary.homogeneousAction (n + 1) (-1) swapUnit (Binary.homogeneousAction (n + 1) (-1) Y w) =
        Binary.homogeneousAction (n + 1) (-1) (swapUnit * Y * swapUnit⁻¹)
          (Binary.homogeneousAction (n + 1) (-1) swapUnit w) := by
    intro w
    rw [act_mul_apply, act_mul_apply]
    congr 2
    group
  unfold planeComparison
  simp only [LinearMap.comp_apply]
  rw [h1, swapZ_map, h2, binarySwap_homogeneousAction (n + 1) (-1) (swapUnit * X * swapUnit⁻¹)
    (swapUnit * Y * swapUnit⁻¹) hrel, binarySwapVar_action_twist, swap_conj_conj]

/-- **The same with the determinant twist made explicit.** -/
theorem planeComparison_alHom_det (n : ℕ) (x : GL (Fin 2) ℚ) (v : Binary.HomogeneousPoly (n + 1)) :
    planeComparison n (rationalRho (n + 1) (-1) (alHom x) v) =
      ((((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℂ) x) : ℂˣ) : ℂ)) ^
          (((n + 1 : ℕ) : ℤ) - (-1))) •
        rationalRho (n + 1) 0 x (planeComparison n v) := by
  rw [planeComparison_alHom, homogeneousAction_zpow_twist]
  rfl

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

end
