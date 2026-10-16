module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDBinaryPLModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIndexTwo

@[expose] public section


/-!
# The dual system of a perfect twisted pairing is the contragredient twisted by the orientation character

Formalized by Claude Sonnet 5.5.

For a perfect pairing `B : V × W → ℂ` of finite-dimensional representations `ρ`, `ρ'` of a group `Γ` with
`B (ρ g v, ρ' g w) = s(g) B (v, w)` for a function `s : Γ → ℂ` (a sign character: `1` on `SL₂`, the orientation character `-1` on the
reflection), the map `Φ : W → V^∨`, `w ↦ B(·, w)` is a linear isomorphism and
`Φ (ρ' g w) = s(g) · (Φ w) ∘ ρ(g⁻¹)`: `ρ'` is the contragredient of `ρ` twisted by `s` (`contragredient_equivariance`).  So the
Poincare-Lefschetz statements for `Setup ι ρ ρ' B ...` ARE statements about the literal contragredient `E*` of the binary Levi
system `E` (with the orientation sign), the only freedom being the sign character `s`, which is the determinant on `GL₂(ℤ)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL

open TernaryPeriodPolynomials.BoundaryDuality
open TripleModel LinearDuality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality (IndexTwo)

section Contragredient

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {ρ : Representation ℂ G V}
  {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- **The dual system is the dual space**: `w ↦ B(·, w)` is a linear isomorphism `W ≃ V^∨` for a perfect pairing. -/
def pairingDual (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0) :
    W ≃ₗ[ℂ] Module.Dual ℂ V :=
  LinearEquiv.ofBijective B.flip
    ⟨(injective_iff_map_eq_zero _).2 fun w hw => hR w fun v => LinearMap.congr_fun hw v,
      fun f => by
        obtain ⟨w, hw⟩ := exists_pairing_right hL hR f
        exact ⟨w, LinearMap.ext fun v => (hw v).symm⟩⟩

theorem pairingDual_apply (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (w : W) (v : V) : pairingDual hL hR w v = B v w := rfl

/-- **`ρ'` is the contragredient of `ρ` twisted by `s`**: `Φ (ρ' g w) = s(g) · Φ(w) ∘ ρ(g⁻¹)`. -/
theorem contragredient_equivariance (hL : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hR : ∀ w, (∀ v, B v w = 0) → w = 0) (s : G → ℂ)
    (hs : ∀ g v w, B (ρ g v) (ρ' g w) = s g * B v w) (g : G) (w : W) :
    pairingDual hL hR (ρ' g w) = s g • (pairingDual hL hR w).comp (ρ g⁻¹) := by
  refine LinearMap.ext fun v => ?_
  have h := hs g (ρ g⁻¹ v) w
  rw [rep_apply_inv ρ] at h
  rw [pairingDual_apply, h]
  simp [pairingDual_apply]

end Contragredient

section OrientationCharacter

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] {ι : N →* Γ} {ε : Γ} {σ : N →* N} {ρ : Representation ℂ Γ V}
  {ρ' : Representation ℂ Γ W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

open Classical in
/-- **The orientation character of an index-two situation**: `1` on the subgroup, `-1` on the other coset. -/
def orientationSign (ι : N →* Γ) (g : Γ) : ℂ := if ∃ n, ι n = g then 1 else -1

theorem orientationSign_ι (ι : N →* Γ) (n : N) : orientationSign ι (ι n) = 1 := by
  unfold orientationSign
  rw [ite_eq_left ⟨n, rfl⟩]

theorem orientationSign_ιε (H : IndexTwo ι ε σ) (n : N) : orientationSign ι (ι n * ε) = -1 := by
  unfold orientationSign
  rw [ite_eq_right]
  rintro ⟨m, hm⟩
  exact H.not_mul_mem n m hm.symm

/-- **A `Γ'`-invariant-up-to-orientation pairing transforms by the orientation character.**  A pairing which is invariant under the
subgroup and changes sign under the reflection satisfies `B (ρ g v, ρ' g w) = s(g) B (v, w)` with `s` the orientation character:
the dual system of such a pairing is the contragredient twisted by the orientation sign. -/
theorem pairing_orientation (H : IndexTwo ι ε σ)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w)
    (hodd : ∀ v w, B (ρ ε v) (ρ' ε w) = (-1 : ℂ) * B v w) (g : Γ) (v : V) (w : W) :
    B (ρ g v) (ρ' g w) = orientationSign ι g * B v w := by
  rcases H.cover g with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · rw [orientationSign_ι, hinv, one_mul]
  · rw [orientationSign_ιε H, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hinv, hodd]

end OrientationCharacter

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL
