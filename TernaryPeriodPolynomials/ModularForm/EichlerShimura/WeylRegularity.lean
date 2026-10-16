module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.Strong

@[expose] public section


/-!
# Local regularity of weak solutions of the Hodge system (Weyl's lemma)

Foundation file of the unconditional Eichler--Shimura route.  All the work is in `ESFoundations/Weyl/`:

* `Weyl.WeakDeriv`, `Weyl.Mollify`, `Weyl.MollifyL2`, `Weyl.Garding`, `Weyl.L2Limit`,
  `Weyl.OneStep`, `Weyl.Bootstrap`, `Weyl.SupBound`, `Weyl.Continuous`, `Weyl.Smooth`,
  `Weyl.Main`, `Weyl.Dirac`: Weyl's lemma for first order Dirac-type systems in the plane, by
  mollifiers, Gårding's identity `‖∇φ‖₂ = ‖P φ‖₂` and a bootstrap through the iterated weak Sobolev
  spaces (no Fourier analysis);
* `Weyl.Pair`, `Weyl.Coclosed`, `Weyl.System`, `Weyl.Strong`: the weakly closed and co-closed system
  `∂₀ b = ∂₁ a`, `∂₀ (H a) + ∂₁ (H b) = 0` for a smooth field `H` of invertible symmetric operators.

The statements to use are `weyl_regularity_dirac` and `weyl_regularity_closed_coclosed`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations

open MeasureTheory
open scoped ContDiff InnerProductSpace

/-- **Weyl's lemma for Dirac-type systems in the plane.**  A locally square integrable weak solution
`u : ℂ → X` of `P₀ ∂₀ u + P₁ ∂₁ u + Q u = 0` on an open set `U`, where `P₀, P₁` are symmetric
involutions that anticommute and `Q` is a smooth field of linear maps, agrees almost everywhere on
`U` with a function that is smooth on `U`.  The hypothesis `h` is the weak form
`∑ⱼ Pⱼ (∫ ∂ⱼφ • u) = ∫ φ • Q z (u z)` (equal to `- ∫ φ • (P · ∂u)` after integration by parts, so it
says `P · ∂u + Q u = 0`; note the sign of `Q`). -/
theorem weyl_regularity_dirac {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {P : Fin 2 → X →L[ℝ] X} (hP : Weyl.DiracPair P) {U : Set ℂ}
    (hU : IsOpen U) {Q : ℂ → X →L[ℝ] X} (hQ : ContDiffOn ℝ ∞ Q U) {u : ℂ → X}
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ U → MemLp u 2 (volume.restrict K))
    (h : ∀ φ : ℂ → ℝ, Weyl.IsTest φ → tsupport φ ⊆ U →
      ∑ j, P j (∫ z, fderiv ℝ φ z (Weyl.dir j) • u z) = ∫ z, φ z • Q z (u z)) :
    ∃ w : ℂ → X, ContDiffOn ℝ ∞ w U ∧ u =ᵐ[volume.restrict U] w :=
  Weyl.weyl_dirac hP hU hQ hu h

/-- **Weyl's lemma for weakly closed and co-closed pairs.**  Let `H` be a smooth field of invertible
symmetric operators on an open set `U ⊆ ℂ` and let `a, b : ℂ → E` be locally square integrable with
`∂₀ b = ∂₁ a` and `∂₀ (H a) + ∂₁ (H b) = 0` in the weak sense (the co-closed equation is tested
against all smooth compactly supported `E`-valued `φ`).  Then `a, b` agree almost everywhere with
smooth `a', b'`, which satisfy both equations pointwise. -/
theorem weyl_regularity_closed_coclosed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} {Hm : ℂ → E →L[ℝ] E} (hH : Weyl.HField U Hm)
    {a b : ℂ → E}
    (ha : ∀ K : Set ℂ, IsCompact K → K ⊆ U → MemLp a 2 (volume.restrict K))
    (hb : ∀ K : Set ℂ, IsCompact K → K ⊆ U → MemLp b 2 (volume.restrict K))
    (hcl : ∀ ψ : ℂ → ℝ, Weyl.IsTest ψ → tsupport ψ ⊆ U →
      ∫ z, fderiv ℝ ψ z (Weyl.dir 0) • b z = ∫ z, fderiv ℝ ψ z (Weyl.dir 1) • a z)
    (hco : ∀ φ : ℂ → E, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, (⟪fderiv ℝ φ z (Weyl.dir 0), Hm z (a z)⟫_ℝ +
        ⟪fderiv ℝ φ z (Weyl.dir 1), Hm z (b z)⟫_ℝ) = 0) :
    ∃ a' b' : ℂ → E, ContDiffOn ℝ ∞ a' U ∧ ContDiffOn ℝ ∞ b' U ∧
      a =ᵐ[volume.restrict U] a' ∧ b =ᵐ[volume.restrict U] b' ∧
      (∀ z ∈ U, fderiv ℝ b' z (Weyl.dir 0) = fderiv ℝ a' z (Weyl.dir 1)) ∧
      (∀ z ∈ U, fderiv ℝ (fun z => Hm z (a' z)) z (Weyl.dir 0) +
        fderiv ℝ (fun z => Hm z (b' z)) z (Weyl.dir 1) = 0) :=
  Weyl.weyl_closed_coclosed_strong hH ha hb hcl hco

end TernaryPeriodPolynomials.Argument.ESFoundations
