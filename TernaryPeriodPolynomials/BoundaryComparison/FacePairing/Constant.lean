module

public import TernaryPeriodPolynomials.BoundaryComparison.LemmaC2Geometric
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.FacePairing

@[expose] public section


/-!
# The glue constant `c` of `ar:eq:facepair` is canonical

Formalized by Claude Sonnet 5.5.

`Statements.LemmaC2Geometric.facePairing_geometric` gives a nonzero constant `c` with `r (c⁻¹ ⟨b, ξ⟩_Q) = ⟨b, ξ⟩^{geo}_Q`,
`r ((-c)⁻¹ ⟨ξ, b⟩_P) = ⟨ξ, b⟩^{geo}_P` for the geometric (Poincare-duality) pairings of the lifts, which are defined by
the library's `geoPairingBoundary` alone.  Here:

* `exists_nonzero_facePairing`: the line face pairing is not identically zero (at `n = 6` the inner line classes contain the
  `2`-dimensional bad-line cuspidal space, and the pairing is perfect);
* `glueConstant_unique`: **the constant `c` is uniquely determined** by the geometric line pairing: any two nonzero constants satisfying
  the comparison `r (c⁻¹ ⟨b, ξ⟩_Q) = ⟨b, ξ⟩^{geo}_Q` for all `n`, `r`, `b`, `ξ` coincide.  Thus `c` does not depend on the comparison
  map `Ψ`, the spanning cycle `Ω` of the boundary, or any other auxiliary choice made in its construction; it is an invariant of the
  model pairing and the library's Poincare duality of `∂M`;
* `planeConstant_unique`, `planeConstant_eq_neg`: the constant of the plane face is `-c` (the relative orientation of the two faces is fixed, not a choice),
  and it is also unique.

What is NOT determined: the VALUE of `c` (its absolute value and sign relative to the orientation of the library's choice-made
boundary fundamental class, which is a rational generator fixed through a choice (`zeroReducedHomologyIso`)).  `c` is multiplied
by `μ` when the fundamental class is rescaled by `μ`, so a canonical value requires the integral/geometric orientation of the boundary
(`Proofs/Lemma33/Geometric`: `fundamentalClassGeo = d5 • fundamentalClass`) together with an integral normalization of the model
cycle `Ω` of the cone, which is not available.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.FacePairingConstant

open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.Statements.LemmaC2Geometric
open TernaryPeriodPolynomials.Argument.Statements.FacePairing
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

/-- Inner line classes are nonzero for `n = 6`. -/
theorem exists_nonzero_innerLine : ∃ b : innerClasses 6 .line, b ≠ 0 := by
  obtain ⟨e1⟩ := innerClasses_line_equiv_cuspidal 6
  obtain ⟨e2⟩ := locallyInner_equiv_cuspidal_badLine 6 GeneralEisenstein.trivialCharacter
  have hdim := finrank_badLine_locallyInner 6 (by norm_num)
  have hpos : 0 < Module.finrank ℂ (locallyInnerClasses 6 GeneralEisenstein.trivialCharacter .line standardBadLine) := by
    have : (6 + 3) / 3 = 3 := by norm_num
    omega
  have := Module.finite_of_finrank_pos hpos
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  refine ⟨e1.symm (0, e2 x), fun h => hx ?_⟩
  have h0 : e1 (e1.symm (0, e2 x)) = e1 0 := congrArg e1 h
  have h1 := (e1.apply_symm_apply (0, e2 x)).symm.trans (h0.trans e1.map_zero)
  have h2 : e2 x = 0 := congrArg Prod.snd h1
  exact (LinearEquiv.map_eq_zero_iff e2).1 h2

theorem exists_nonzero_facePairing_of (b : innerClasses 6 .line) (hb : b ≠ 0) :
    ∃ (n : ℕ) (b : innerClasses n .line) (ξ : innerClasses n .plane), facePairing n b ξ ≠ 0 := by
  have : ∃ ξ : innerClasses 6 .plane, facePairing 6 b ξ ≠ 0 := by
    by_contra hc
    apply hb
    apply (facePairing_perfect_all 6).1 b
    intro ξ
    by_contra hξ
    exact hc ⟨ξ, hξ⟩
  exact this.elim (fun ξ hξ => ⟨6, b, ξ, hξ⟩)

/-- **The line face pairing is not identically zero.** -/
theorem exists_nonzero_facePairing :
    ∃ (n : ℕ) (b : innerClasses n .line) (ξ : innerClasses n .plane), facePairing n b ξ ≠ 0 :=
  exists_nonzero_innerLine.elim exists_nonzero_facePairing_of

theorem exists_nonzero_facePairingP_of (b : innerClasses 6 .line) (hb : b ≠ 0) :
    ∃ (n : ℕ) (ξ : innerClasses n .plane) (b : innerClasses n .line), Plane.facePairingP n ξ b ≠ 0 := by
  have : ∃ ξ : innerClasses 6 .plane, Plane.facePairingP 6 ξ b ≠ 0 := by
    by_contra hc
    apply hb
    apply (facePairingP_perfect_all 6).2 b
    intro ξ
    by_contra hξ
    exact hc ⟨ξ, hξ⟩
  exact this.elim (fun ξ hξ => ⟨6, ξ, b, hξ⟩)

theorem exists_nonzero_facePairingP :
    ∃ (n : ℕ) (ξ : innerClasses n .plane) (b : innerClasses n .line), Plane.facePairingP n ξ b ≠ 0 :=
  exists_nonzero_innerLine.elim exists_nonzero_facePairingP_of

/-- **The glue constant is unique.** If two constants `c, c'` both compare the model line pairing with the geometric
(Poincare-duality) pairing, `r (c⁻¹ ⟨b, ξ⟩_Q) = ⟨b, ξ⟩^{geo}_Q` and likewise for `c'`, then `c = c'`. -/
theorem glueConstant_unique {c c' : ℂ}
    (h : ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line) (ξ : innerClasses n .plane),
      r (c⁻¹ * facePairing n b ξ) = geoLinePairing n r b ξ)
    (h' : ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line) (ξ : innerClasses n .plane),
      r (c'⁻¹ * facePairing n b ξ) = geoLinePairing n r b ξ) : c = c' :=
  exists_nonzero_facePairing.elim (fun n hn => hn.elim (fun b hb => hb.elim (fun ξ hne => by
    have h0 : (c⁻¹ - c'⁻¹) * facePairing n b ξ = 0 :=
      (Module.forall_dual_apply_eq_zero_iff ℚ ((c⁻¹ - c'⁻¹) * facePairing n b ξ)).1 (fun r => by
        rw [sub_mul, map_sub, h n r b ξ, h' n r b ξ, sub_self])
    have : c⁻¹ - c'⁻¹ = 0 := (mul_eq_zero.1 h0).resolve_right hne
    exact inv_injective (sub_eq_zero.1 this))))

/-- **The plane constant is unique as well** (it is `-c` for the line constant `c`, `facePairing_geometric`). -/
theorem planeConstant_unique {c c' : ℂ}
    (h : ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane) (b : innerClasses n .line),
      r (c⁻¹ * Plane.facePairingP n ξ b) = geoPlanePairing n r ξ b)
    (h' : ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane) (b : innerClasses n .line),
      r (c'⁻¹ * Plane.facePairingP n ξ b) = geoPlanePairing n r ξ b) : c = c' :=
  exists_nonzero_facePairingP.elim (fun n hn => hn.elim (fun ξ hξ => hξ.elim (fun b hne => by
    have h0 : (c⁻¹ - c'⁻¹) * Plane.facePairingP n ξ b = 0 :=
      (Module.forall_dual_apply_eq_zero_iff ℚ ((c⁻¹ - c'⁻¹) * Plane.facePairingP n ξ b)).1 (fun r => by
        rw [sub_mul, map_sub, h n r ξ b, h' n r ξ b, sub_self])
    have : c⁻¹ - c'⁻¹ = 0 := (mul_eq_zero.1 h0).resolve_right hne
    exact inv_injective (sub_eq_zero.1 this))))

/-- **The relative orientation of the two faces is fixed**: the line constant `c` and the plane constant `c_P` of the
geometric comparison satisfy `c_P = -c`. -/
theorem planeConstant_eq_neg {c cP : ℂ}
    (h : ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line) (ξ : innerClasses n .plane),
      r (c⁻¹ * facePairing n b ξ) = geoLinePairing n r b ξ)
    (hP : ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane) (b : innerClasses n .line),
      r (cP⁻¹ * Plane.facePairingP n ξ b) = geoPlanePairing n r ξ b) :
    cP = -c :=
  facePairing_geometric.elim (fun _ hc0 =>
    (planeConstant_unique hP hc0.2.2).trans (congrArg Neg.neg (glueConstant_unique h hc0.2.1).symm))

end TernaryPeriodPolynomials.Argument.Statements.FacePairingConstant
