module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.DualJ.Jmath
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Model
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Apolar

@[expose] public section


/-!
# The coefficient identification: `E ∘ ȷ` is the dual of `E` after the fixed change of coordinates by `w`

Paper: `ȷ` "pulls `E` back to its dual, after the fixed linear change of coefficient coordinates by `J`".
For every representation `ρ` of `GL₃(ℚ)`, the fixed linear map `ρ(w)`, `w = J a⁻¹` (`DualJ.jmathConj`), intertwines the
model's dual system `ρ ∘ φ` (`Dual.dualRep ρ`) with the pullback `ρ ∘ ȷ` (`coefficient_intertwines`). For the
coefficient system `E = Sym^n` the apolar pairing `B` (`dualPairing`), invariant for `(ρ, ρ ∘ φ)`, becomes the
pairing `B_J(v, u) = B(v, ρ(w)⁻¹ u)` which is invariant for `(ρ, ρ ∘ ȷ)` (`dualPairingJ_invariant`) and nondegenerate
(`dualPairingJ_nondegenerate`): the pullback `E ∘ ȷ` is the dual of `E`, via the explicit coordinate change `ρ(w)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem rep_comm (R : Representation ℂ RationalGL3 W) (a b c d : RationalGL3) (h : a * b = c * d)
    (v : W) : R a (R b v) = R c (R d v) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, h]

/-- **The coefficient identification.** `ρ(w) : (V, ρ ∘ φ) → (V, ρ ∘ ȷ)` is `GL₃(ℚ)`-equivariant. -/
theorem coefficient_intertwines (ρ : Representation ℂ RationalGL3 W) (g : RationalGL3) (v : W) :
    ρ (jmath g) (ρ jmathConj v) = ρ jmathConj (dualRep ρ g v) := by
  change ρ (jmath g) (ρ jmathConj v) = ρ jmathConj (ρ (dualInvolution g) v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, jmath_eq_conj]
  congr 2
  group

/-- The coordinate change is invertible. -/
theorem coefficient_cancel (ρ : Representation ℂ RationalGL3 W) (v : W) :
    ρ jmathConj⁻¹ (ρ jmathConj v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- The pairing `B_J(v, u) = B(v, ρ(w)⁻¹ u)` between `E` and `E ∘ ȷ`. -/
def dualPairingJ (n : ℕ) (χ : RankOneCharacter) :
    HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ :=
  (dualPairing n).compl₂ (rationalCoefficientComponent n χ jmathConj⁻¹)

theorem dualPairingJ_apply (n : ℕ) (χ : RankOneCharacter) (v u : HomogeneousPoly n) :
    dualPairingJ n χ v u = dualPairing n v (rationalCoefficientComponent n χ jmathConj⁻¹ u) := rfl

/-- **`E ∘ ȷ` is dual to `E` for `B_J`.** -/
theorem dualPairingJ_invariant (n : ℕ) (χ : RankOneCharacter) (g : RationalGL3)
    (v u : HomogeneousPoly n) :
    dualPairingJ n χ (rationalCoefficientComponent n χ g v)
      (rationalCoefficientComponent n χ (jmath g) u) = dualPairingJ n χ v u := by
  rw [dualPairingJ_apply, dualPairingJ_apply]
  have h : rationalCoefficientComponent n χ jmathConj⁻¹
      (rationalCoefficientComponent n χ (jmath g) u) =
      rationalCoefficientComponent n χ (dualInvolution g)
        (rationalCoefficientComponent n χ jmathConj⁻¹ u) := by
    apply rep_comm
    rw [jmath_eq_conj]
    group
  rw [h]
  exact dualPairing_invariant n χ g v _

theorem dualPairingJ_nondegenerate (n : ℕ) (χ : RankOneCharacter) (v : HomogeneousPoly n)
    (h : ∀ u, dualPairingJ n χ v u = 0) : v = 0 := by
  refine dualPairing_nondegenerate v fun u => ?_
  have := h (rationalCoefficientComponent n χ jmathConj u)
  rwa [dualPairingJ_apply, coefficient_cancel] at this

end TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ
