module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingNondegenerate

@[expose] public section


/-!
# From the zero left kernel to the zero right kernel by a dimension count

The face pairing `facePairing n : innerClasses n .line → innerClasses n .plane → ℂ` has zero left
kernel for every `n` (`facePairing_left_nondegenerate`). If the two spaces are finite dimensional of
the same dimension, the induced map `innerClasses n .line → (innerClasses n .plane)^*` is injective
between spaces of equal dimension, hence bijective, and then the right kernel is zero as well
(`facePairing_right_nondegenerate_of_finrank_eq`). Thus the right-kernel statement of
`ar:eq:facepair` is reduced to the equality `dim 𝒞_Q(E) = dim 𝒞_Q(E*)` of the dimensions of the
two inner spaces.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- **Linear algebra:** a bilinear form between finite-dimensional spaces of equal dimension with
zero left kernel has zero right kernel. -/
theorem right_kernel_zero_of_left_injective {A B : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]
    (f : A →ₗ[ℂ] B →ₗ[ℂ] ℂ) (hleft : Function.Injective f)
    (hdim : Module.finrank ℂ A = Module.finrank ℂ B) (y : B) (hy : ∀ x : A, f x y = 0) : y = 0 := by
  have hd : Module.finrank ℂ A = Module.finrank ℂ (Module.Dual ℂ B) := by
    rw [hdim, Subspace.dual_finrank_eq]
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hleft
  refine (Module.forall_dual_apply_eq_zero_iff ℂ y).mp fun φ => ?_
  obtain ⟨x, rfl⟩ := hsurj φ
  exact hy x

/-- **Perfectness from the left kernel and equal dimensions.** -/
theorem facePairing_perfect_of_finrank_eq (n : ℕ)
    [FiniteDimensional ℂ (innerClasses n .line)] [FiniteDimensional ℂ (innerClasses n .plane)]
    (hdim : Module.finrank ℂ (innerClasses n .line) = Module.finrank ℂ (innerClasses n .plane)) :
    ∀ ξ : innerClasses n .plane, (∀ b : innerClasses n .line, facePairing n b ξ = 0) → ξ = 0 := by
  intro ξ hξ
  have hinj : Function.Injective (facePairing n) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact facePairing_left_nondegenerate n b fun η => by
      rw [hb]; rfl
  exact right_kernel_zero_of_left_injective (facePairing n) hinj hdim ξ hξ

end TernaryPeriodPolynomials.Argument.FacePairingFull
