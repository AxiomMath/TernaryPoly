module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.Levi

@[expose] public section


/-!
# The rotation intertwines the Levi actions at the identity plane and the good line

The Kostant pairing of the good line pairs `Sym^{n+1}` (acted on by `m ∈ GL₂(ℤ)` through
`homogeneousAction (n+1) 0`) with `Sym^{n+1}` (acted on by `m' = m^{-T}` through
`homogeneousAction (n+1) (-1)`).  The rotation `rot : g(x, y) ↦ g(-y, x)` of binary forms turns this
into a pairing of two modules on which the *same* matrix acts:

  `rot ∘ (γ' ⋆_τ) = (γ ⋆_{N-τ}) ∘ rot`     for `γ γ'ᵀ = 1`    (`binarySwap_homogeneousAction`),

so on `swappedUpperCoordinate` the Levi element `m` acts through `homogeneousAction (n+1) (n+2)`
(`swappedUpperCoordinate_levi`).  By `goodLineKostant_eq_binaryPairing` the Kostant pairing is
`(n+1)!` times `binaryPairing (n+1)` of the two coordinates, which is semi-invariant with
determinant character `det^{0 + (n+2) - (n+1)} = det` (`BinaryPairing.binaryPairing_homogeneousAction`).
The proof of the intertwining uses only the perfectness of the pairings, not polynomial identities.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open MvPolynomial GeneralEisenstein Matrix
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

/-- The rotation `g(x, y) ↦ g(-y, x)` of binary forms is injective. -/
theorem binarySwap_injective (N : ℕ) : Function.Injective (binarySwap N) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  apply binApolar_right_eq_zero
  intro f
  rw [binApolar_eq_binaryPairing, hg, map_zero, mul_zero]

/-- The rotation `g(x, y) ↦ g(-y, x)` of binary forms as a linear equivalence. -/
def binarySwapEquiv (N : ℕ) : Binary.HomogeneousPoly N ≃ₗ[ℂ] Binary.HomogeneousPoly N :=
  LinearEquiv.ofInjectiveEndo (binarySwap N) (binarySwap_injective N)

/-- **The rotation intertwines the Levi actions.**  If `γ γ'ᵀ = 1` then
`rot (γ' ⋆_τ g) = γ ⋆_{N-τ} (rot g)`. -/
theorem binarySwap_homogeneousAction (N : ℕ) (τ : ℤ) (γ γ' : Binary.GL2)
    (h : (γ : Matrix (Fin 2) (Fin 2) ℂ) * (γ' : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 1)
    (g : Binary.HomogeneousPoly N) :
    binarySwap N (Binary.homogeneousAction N τ γ' g) =
      Binary.homogeneousAction N ((N : ℤ) - τ) γ (binarySwap N g) := by
  have hdet : ((GeneralLinearGroup.det γ : ℂˣ) : ℂ) * ((GeneralLinearGroup.det γ' : ℂˣ) : ℂ) = 1 := by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply]
    exact h1
  have hd : ((GeneralLinearGroup.det γ' : ℂˣ) : ℂ) = (((GeneralLinearGroup.det γ : ℂˣ) : ℂ))⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  have hN : (N.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  apply sub_eq_zero.mp
  apply BinaryPairing.binaryPairing_right_eq_zero N
  intro v
  obtain ⟨f, rfl⟩ : ∃ f, Binary.homogeneousAction N 0 γ f = v :=
    ⟨Binary.homogeneousAction N 0 γ⁻¹ v, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
  have t1 : BinaryPairing.binaryPairing N (Binary.homogeneousAction N 0 γ f)
      (binarySwap N (Binary.homogeneousAction N τ γ' g)) =
      ((GeneralLinearGroup.det γ' : ℂˣ) : ℂ) ^ τ * BinaryPairing.binaryPairing N f (binarySwap N g) := by
    have e1 := binApolar_eq_binaryPairing N (Binary.homogeneousAction N 0 γ f)
      (Binary.homogeneousAction N τ γ' g)
    have e2 := binApolar_homogeneousAction N 0 τ γ γ' h f g
    have e3 := binApolar_eq_binaryPairing N f g
    rw [e2, e3] at e1
    apply mul_left_cancel₀ hN
    rw [← e1, zpow_zero]
    ring
  have t2 : BinaryPairing.binaryPairing N (Binary.homogeneousAction N 0 γ f)
      (Binary.homogeneousAction N ((N : ℤ) - τ) γ (binarySwap N g)) =
      ((GeneralLinearGroup.det γ : ℂˣ) : ℂ) ^ (-τ) * BinaryPairing.binaryPairing N f (binarySwap N g) := by
    rw [BinaryPairing.binaryPairing_homogeneousAction]
    have e : (0 : ℤ) + ((N : ℤ) - τ) - (N : ℤ) = -τ := by ring
    rw [e]
  rw [map_sub, t1, t2, hd, _root_.inv_zpow', sub_self]

/-- **The identity-plane coordinate transported by the rotation**: a linear equivalence
`H¹(U^φ, V) ≅ Sym^{n+1}` on which the Levi elements act through the same matrices as on the
good-line coordinate. -/
def swappedUpperCoordinate (n : ℕ) :
    groupCohomology.H1 (upperRadicalLatticeRep n) ≃ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (upperRadicalH1Coordinate n).trans (binarySwapEquiv (n + 1))

/-- The transported coordinate in terms of the rotation. -/
theorem swappedUpperCoordinate_apply (n : ℕ) (c' : groupCohomology.H1 (upperRadicalLatticeRep n)) :
    swappedUpperCoordinate n c' = binarySwap (n + 1) (upperRadicalH1Coordinate n c') := rfl

/-- **The Levi element `m` acts on the transported identity-plane coordinate through
`Sym^{n+1} ⊗ det^{n+2}`**, when the identity-plane Levi element is `m'` with `m m'ᵀ = 1`. -/
theorem swappedUpperCoordinate_levi (n : ℕ) (m m' : GeneralLinearGroup (Fin 2) ℤ)
    (h : (m : Matrix (Fin 2) (Fin 2) ℤ) * (m' : Matrix (Fin 2) (Fin 2) ℤ)ᵀ = 1)
    (c' : groupCohomology.H1 (upperRadicalLatticeRep n)) :
    swappedUpperCoordinate n (upperRadicalH1Levi n m' c') =
      Binary.homogeneousAction (n + 1) ((n : ℤ) + 2) (GeneralLinearGroup.map (Int.castRingHom ℂ) m)
        (swappedUpperCoordinate n c') := by
  change binarySwap (n + 1) (upperRadicalH1Coordinate n (upperRadicalH1Levi n m' c')) =
    Binary.homogeneousAction (n + 1) ((n : ℤ) + 2) (GeneralLinearGroup.map (Int.castRingHom ℂ) m)
      (binarySwap (n + 1) (upperRadicalH1Coordinate n c'))
  have e : (((n + 1 : ℕ) : ℤ) - (-1)) = (n : ℤ) + 2 := by
    push_cast
    ring
  rw [upperRadicalH1Coordinate_equivariant,
    binarySwap_homogeneousAction _ (-1) _ _ (map_mul_transpose m m' h), e]

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
