module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.PerfectOdd
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelThree

@[expose] public section



/-!
# The literal per-face pairings `⟨ , ⟩_F : 𝒞_F(E) × 𝒞_F(E*) → ℂ` are perfect

By `Face/BadLineParabolic`, `GoodPlaneParabolic`, `BadPlaneParabolic` and
`PerfectOdd.parabolicToGoodLine_bijective`, the mixed cuspidal groups of the four reference faces are the
parabolic cohomology groups
* good line `𝒞_gl(E) = parabolicH1 (Sym^{n+1})`, identity plane `𝒞_bp(E) = parabolicH1 (Sym^{n+1} ⊗ det⁻¹)`
  (level one, odd `n`; both zero for even `n`),
* bad line `𝒞_bl(E) = parabolicH1 (Γ₁'(3), Sym^{n+1})`, good plane `𝒞_gp(E) = parabolicH1 (Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`
  (level three, all `n`).
The face pairing of a face of type `Q` with the dual face is the parabolic cup pairing of the library
(`parabolicPairing`, built from the classical apolar pairing of binary forms and Petersson-type
parabolic Poincaré duality). This file proves that each of these block pairings is perfect in both
arguments: the left kernel is zero by the library's parabolic Poincaré duality, and the right kernel
is zero because the two parabolic spaces have equal finite dimension (the exact dimension formulas at
level three, the parabolic duality in both orders at level one).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
open TernaryPeriodPolynomials.BoundaryDuality
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticRepresentation CrossedH1)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- A bilinear form on finite-dimensional spaces with zero left kernel and `dim B ≤ dim A` has zero
right kernel. -/
theorem right_kernel_zero_of_left_injective_of_finrank_le {A B : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]
    (f : A →ₗ[ℂ] B →ₗ[ℂ] ℂ) (hleft : Function.Injective f)
    (hdim : Module.finrank ℂ B ≤ Module.finrank ℂ A) (y : B) (hy : ∀ x : A, f x y = 0) : y = 0 := by
  have h1 := LinearMap.finrank_le_finrank_of_injective hleft
  rw [Subspace.dual_finrank_eq] at h1
  exact right_kernel_zero_of_left_injective f hleft (le_antisymm h1 hdim) y hy

/-- **Level one (good line × identity plane), odd `n`: the parabolic pairing is perfect.** -/
theorem levelOne_pairing_perfect (n : ℕ) (hodd : Odd n) :
    let P := LevelOne.parabolicPairing
      (LevelOne.twistedPairing_arithmeticBinaryRep (n + 1) 0 (-1) hodd.add_one (by
        obtain ⟨k, hk⟩ := hodd
        exact ⟨-(k : ℤ) - 2, by push_cast; omega⟩))
    (∀ x, (∀ y, P x y = 0) → x = 0) ∧ (∀ y, (∀ x, P x y = 0) → y = 0) := by
  intro P
  have f0 := finiteDimensional_parabolicH1 (n + 1) 0
  have f1 := finiteDimensional_parabolicH1 (n + 1) (-1)
  have hleft : Function.Injective P := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact LevelOne.arithmeticBinaryRep_left_nondegenerate (n + 1) 0 (-1) hodd.add_one (by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨-(k : ℤ) - 2, by push_cast; omega⟩) x (fun y => by rw [hx]; rfl)
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · exact hleft (by ext y; simpa using hx y)
  · exact right_kernel_zero_of_left_injective_of_finrank_le P hleft
      (finrank_parabolic_neg_le n hodd) y hy

theorem finiteDimensional_parabolicCrossedH1 (m : ℕ) (hm : 0 < m) (e : ℤ) :
    FiniteDimensional ℂ (LevelThree.parabolicCrossedH1 (levelRep m e)) := by
  have h : FiniteDimensional ℂ (CrossedH1 (levelRep m e)) :=
    TernaryPeriodPolynomials.LevelThree.ParabolicBounds.level_H1_finiteDimensional e hm
  exact FiniteDimensional.finiteDimensional_submodule _

/-- The two level-three parabolic spaces `Sym^{n+1}` and `Sym^{n+1} ⊗ det⁻¹` have equal dimension
(exact dimension formula). -/
theorem finrank_levelThree_parabolic_eq (n : ℕ) :
    Module.finrank ℂ (LevelThree.parabolicCrossedH1 (levelRep (n + 1) 0)) =
      Module.finrank ℂ (LevelThree.parabolicCrossedH1 (levelRep (n + 1) (-1))) := by
  have h0 := TernaryPeriodPolynomials.LevelThree.ExactLevel.finrank_level_parabolicH1_eq
    (m := n + 1) (e := 0) (by omega)
  have h1 := TernaryPeriodPolynomials.LevelThree.ExactLevel.finrank_level_parabolicH1_eq
    (m := n + 1) (e := -1) (by omega)
  rw [← LevelThree.parabolicCrossedH1_eq] at h0 h1
  omega

/-- **Level three (bad line × good plane), odd `n`: the parabolic pairing is perfect.** -/
theorem levelThree_pairing_perfect_odd (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    let P := LevelThree.parabolicPairing
      (LevelThree.twistedPairing_levelRep (n + 1) 0 (-1) (by
        obtain ⟨k, hk⟩ := hodd
        exact ⟨-(k : ℤ) - 2, by push_cast; omega⟩))
    (∀ x, (∀ y, P x y = 0) → x = 0) ∧ (∀ y, (∀ x, P x y = 0) → y = 0) := by
  intro P
  have f0 := finiteDimensional_parabolicCrossedH1 (n + 1) (by omega) 0
  have f1 := finiteDimensional_parabolicCrossedH1 (n + 1) (by omega) (-1)
  have hleft : Function.Injective P := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact LevelThree.levelRep_left_nondegenerate (n + 1) 0 (-1) (by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨-(k : ℤ) - 2, by push_cast; omega⟩) x (fun y => by rw [hx]; rfl)
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · exact hleft (by ext y; simpa using hx y)
  · exact right_kernel_zero_of_left_injective_of_finrank_le P hleft
      (finrank_levelThree_parabolic_eq n).ge y hy

/-- **Level three (bad line × good plane), even `n`: the parabolic pairing is perfect.** -/
theorem levelThree_pairing_perfect_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    let P := LocalPairingCaseL0Even.badGoodPairingEven heven
    (∀ x, (∀ y, P x y = 0) → x = 0) ∧ (∀ y, (∀ x, P x y = 0) → y = 0) := by
  intro P
  have f0 : FiniteDimensional ℂ (LevelThree.parabolicCrossedH1 (binaryArithmeticRepresentation n)) :=
    finiteDimensional_parabolicCrossedH1 (n + 1) (by omega) 0
  have f1 := finiteDimensional_parabolicCrossedH1 (n + 1) (by omega) (-1)
  have hleft : Function.Injective P := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact LocalPairingCaseL0Even.badGoodPairingEven_left_nondegenerate heven x
      (fun y => by rw [hx]; rfl)
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · exact hleft (by ext y; simpa using hx y)
  · exact right_kernel_zero_of_left_injective_of_finrank_le P hleft
      (finrank_levelThree_parabolic_eq n).ge y hy

end TernaryPeriodPolynomials.Argument.FacePairingFull
