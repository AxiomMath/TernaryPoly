module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Swap.Comparison
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.PerfectEven
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.PerfectOdd
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.PlaneZeroDegree
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingNondegenerate

@[expose] public section


/-!
# Perfectness of the cochain plane pairing `⟨ , ⟩_P`

By the swap relation `⟨B, A⟩_Q = a ⟨A, B⟩_P` with `a = ±1` (`Swap.Comparison.facePairing_swap`), the left
and right kernels of `facePairingP n` are the right and left kernels of `facePairing n`. The latter
pairing is perfect for every `n` (`facePairing_perfect_allQ`, which covers `n = 0` where both spaces of
inner classes vanish), hence so is `facePairingP n`, for every `n`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Swap

/-- **`ar:eq:facepair` for `R = Q`, both arguments, every `n`** (proof-level copy of the export). -/
theorem facePairing_perfect_allQ (n : ℕ) :
    (∀ b : innerClasses n .line, (∀ ξ : innerClasses n .plane, facePairing n b ξ = 0) → b = 0) ∧
      ∀ ξ : innerClasses n .plane, (∀ b : innerClasses n .line, facePairing n b ξ = 0) → ξ = 0 := by
  refine ⟨fun b h => facePairing_left_nondegenerate n b h, fun ξ h => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact facePairing_right_nondegenerate_zero ξ h
  · rcases Nat.even_or_odd n with heven | hodd
    · exact facePairing_right_nondegenerate_even n hn heven ξ h
    · exact facePairing_right_nondegenerate_odd n hn hodd ξ h

/-- **The left kernel of `⟨ , ⟩_P` is zero, for every `n`.** -/
theorem facePairingP_left_nondegenerate (n : ℕ) (A : innerClasses n .plane)
    (h : ∀ B : innerClasses n .line, facePairingP n A B = 0) : A = 0 := by
  obtain ⟨a, -, hswap⟩ := exists_swap_relation
  refine (facePairing_perfect_allQ n).2 A fun b => ?_
  exact (hswap n A b).trans (by rw [h b, mul_zero])

/-- **The right kernel of `⟨ , ⟩_P` is zero, for every `n`.** -/
theorem facePairingP_right_nondegenerate (n : ℕ) (B : innerClasses n .line)
    (h : ∀ A : innerClasses n .plane, facePairingP n A B = 0) : B = 0 := by
  obtain ⟨a, -, hswap⟩ := exists_swap_relation
  refine (facePairing_perfect_allQ n).1 B fun ξ => ?_
  exact (hswap n ξ B).trans (by rw [h ξ, mul_zero])

/-- **`ar:eq:facepair` for `R = P`, both arguments, every `n`.** -/
theorem facePairingP_perfect_all (n : ℕ) :
    (∀ A : innerClasses n .plane, (∀ B : innerClasses n .line, facePairingP n A B = 0) → A = 0) ∧
      ∀ B : innerClasses n .line, (∀ A : innerClasses n .plane, facePairingP n A B = 0) → B = 0 :=
  ⟨fun A h => facePairingP_left_nondegenerate n A h, fun B h => facePairingP_right_nondegenerate n B h⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Swap
