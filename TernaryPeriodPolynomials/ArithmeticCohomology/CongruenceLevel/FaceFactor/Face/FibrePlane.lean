module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.FibreGeneric
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.FaceOrbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.PlaneSelfGroup

@[expose] public section


/-!
# Regrouping the plane faces of `Γ(M)` over the plane faces of `Γ(N)`

Formalized by Claude Sonnet 5.5.

The plane analogue of `FaceFibreLine`: `planeFaces_regroup`, for `3 ≤ N ∣ M` and any function `Φ` on the plane faces of `Γ(N)`,
`∑_{i ∈ plane faces of Γ(M)} [P_N : P_M] · Φ(i mod Γ(N)) = [Γ(N) : Γ(M)] · ∑_{j ∈ plane faces of Γ(N)} Φ(j)`,
with `[P_N : P_M] = (gammaNPAt M h).relIndex (gammaNPAt N h)` independent of `h` (`gammaNPAt_relIndex_eq`).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceFibre

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.FrameInvariance
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3

/-- The index of the plane group of `h⁻¹ P h` at level `M` in that at level `N` is the index of `planeBorel ⊓ Γ(M)` in `planeBorel ⊓ Γ(N)`, independent of `h`. -/
theorem gammaNPAt_relIndex_eq {N M : ℕ} (hN : 3 ≤ N) (hM : 3 ≤ M) (h : SL(3, ℤ)) :
    (gammaNPAt M h).relIndex (gammaNPAt N h) = (gammaN M ⊓ planeBorel).relIndex (gammaN N ⊓ planeBorel) := by
  rw [← gammaNP_eq_inf N hN, ← gammaNP_eq_inf M hM]
  have hc : Function.Surjective (MulAut.conj h).toMonoidHom := (MulAut.conj h).surjective
  change ((gammaNP M).comap (MulAut.conj h).toMonoidHom).relIndex ((gammaNP N).comap (MulAut.conj h).toMonoidHom) = _
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hc]

theorem planeFaces_regroup {N M : ℕ} [NeZero N] [NeZero M] (hN : 3 ≤ N) (hNM : N ∣ M) (Φ : PlaneFaces N → ℂ) :
    ∑ i : PlaneFaces M, (((gammaNPAt M (planeFaceRepr i)).relIndex (gammaNPAt N (planeFaceRepr i)) : ℕ) : ℂ) *
        Φ (Quotient.mk (planeFaceSetoid N) (planeFaceRepr i)) =
      (((gammaN M).relIndex (gammaN N) : ℕ) : ℂ) * ∑ j : PlaneFaces N, Φ j := by
  have hle : gammaN M ≤ gammaN N := fun γ hγ => by
    rw [mem_gammaN] at hγ ⊢
    exact fun i j => (Int.natCast_dvd_natCast.mpr hNM).trans (hγ i j)
  have hM : 3 ≤ M := hN.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hNM)
  have : (gammaN N).FiniteIndex := inferInstance
  have : (gammaN M).FiniteIndex := inferInstance
  have hrel : ∀ i : PlaneFaces M, ((gammaNPAt M (planeFaceRepr i)).relIndex (gammaNPAt N (planeFaceRepr i)) : ℕ) =
      (gammaN M ⊓ planeBorel).relIndex (gammaN N ⊓ planeBorel) := fun i => gammaNPAt_relIndex_eq hN hM _
  simp_rw [hrel, ← Finset.mul_sum]
  refine face_sum (F := PlaneFaces N) (F' := PlaneFaces M) planeBorel (gammaN N) (gammaN M) hle
    (fun h => (Quotient.mk (planeFaceSetoid N) h : PlaneFaces N))
    (fun h => (Quotient.mk (planeFaceSetoid M) h : PlaneFaces M))
    (fun a b => ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩)
    (fun a b => ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩)
    Quotient.mk_surjective Quotient.mk_surjective
    (fun i => Quotient.mk (planeFaceSetoid N) (planeFaceRepr i)) ?_ Φ
  intro h
  have hr : (planeFaceSetoid M).r h (planeFaceRepr (Quotient.mk (planeFaceSetoid M) h)) :=
    (planeFaceSetoid M).iseqv.symm (Quotient.mk_out (s := planeFaceSetoid M) h)
  obtain ⟨q, hq, γ, hγ, hrep⟩ := hr
  exact (Quotient.sound (show (planeFaceSetoid N).r h _ from ⟨q, hq, γ, hle hγ, hrep⟩)).symm

end TernaryPeriodPolynomials.Argument.FaceFibre
