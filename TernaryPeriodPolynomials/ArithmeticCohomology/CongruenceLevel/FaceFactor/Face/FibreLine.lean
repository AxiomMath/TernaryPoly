module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.FibreGeneric
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.FaceOrbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineSelfGroup

@[expose] public section


/-!
# Regrouping the line faces of `Γ(M)` over the line faces of `Γ(N)`

Formalized by Claude Sonnet 5.5.

`lineFaces_regroup`: for `3 ≤ N ∣ M` and any function `Φ` on the faces of `Γ(N)`,
`∑_{i ∈ faces of Γ(M)} [P_N : P_M] · Φ(i mod Γ(N)) = [Γ(N) : Γ(M)] · ∑_{j ∈ faces of Γ(N)} Φ(j)`,
where `[P_N : P_M] = (gammaNQAt M h).relIndex (gammaNQAt N h)` is the index of the line group of `h⁻¹ Q h` at level `M` in that at level `N`, independent of `h` (`gammaNQAt_relIndex_eq`).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceFibre

open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.FrameInvariance
open TernaryPeriodPolynomials.Argument.ConvergenceC4

/-- The index of the line group of `h⁻¹ Q h` at level `M` in that at level `N` is the index of `lineBorel ⊓ Γ(M)` in `lineBorel ⊓ Γ(N)`, independent of `h`. -/
theorem gammaNQAt_relIndex_eq {N M : ℕ} (hN : 3 ≤ N) (hM : 3 ≤ M) (h : SL(3, ℤ)) :
    (gammaNQAt M h).relIndex (gammaNQAt N h) = (gammaN M ⊓ lineBorel).relIndex (gammaN N ⊓ lineBorel) := by
  rw [← gammaNQ_eq_inf N hN, ← gammaNQ_eq_inf M hM]
  have hc : Function.Surjective (MulAut.conj h).toMonoidHom := (MulAut.conj h).surjective
  change ((gammaNQ M).comap (MulAut.conj h).toMonoidHom).relIndex ((gammaNQ N).comap (MulAut.conj h).toMonoidHom) = _
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hc]

theorem lineFaces_regroup {N M : ℕ} [NeZero N] [NeZero M] (hN : 3 ≤ N) (hNM : N ∣ M) (Φ : LineFaces N → ℂ) :
    ∑ i : LineFaces M, (((gammaNQAt M i.rep).relIndex (gammaNQAt N i.rep) : ℕ) : ℂ) *
        Φ (LineFaces.mk i.rep) =
      (((gammaN M).relIndex (gammaN N) : ℕ) : ℂ) * ∑ j : LineFaces N, Φ j := by
  have hle : gammaN M ≤ gammaN N := fun γ hγ => by
    rw [mem_gammaN] at hγ ⊢
    exact fun i j => (Int.natCast_dvd_natCast.mpr hNM).trans (hγ i j)
  have hM : 3 ≤ M := hN.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hNM)
  have : (gammaN N).FiniteIndex := inferInstance
  have : (gammaN M).FiniteIndex := inferInstance
  have hrel : ∀ i : LineFaces M, ((gammaNQAt M i.rep).relIndex (gammaNQAt N i.rep) : ℕ) =
      (gammaN M ⊓ lineBorel).relIndex (gammaN N ⊓ lineBorel) := fun i => gammaNQAt_relIndex_eq hN hM i.rep
  simp_rw [hrel, ← Finset.mul_sum]
  refine face_sum lineBorel (gammaN N) (gammaN M) hle (LineFaces.mk (N := N)) (LineFaces.mk (N := M))
    (fun a b => ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩)
    (fun a b => ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩)
    Quotient.mk_surjective Quotient.mk_surjective (fun i => LineFaces.mk (N := N) i.rep) ?_ Φ
  intro h
  obtain ⟨q, hq, γ, hγ, hrep⟩ := LineFaces.rel_rep (N := M) h
  exact (Quotient.sound (show (lineFaceSetoid N).r h _ from ⟨q, hq, γ, hle hγ, hrep⟩)).symm

end TernaryPeriodPolynomials.Argument.FaceFibre
