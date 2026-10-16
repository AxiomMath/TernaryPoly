module

public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.Main
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.FibreLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.FibrePlane

@[expose] public section


/-!
# The literal Stokes lemma at `Γ(N)` from `Γ(M)`, `M = lcm(N,6)`: the wrapper (B3)

Formalized by Claude Sonnet 5.5.

`RestrictionIdent N M n hN hM`: the two restriction identities of the descent (the `LevelDescent`): there are restriction maps `R`, `R'` of the global classes of `Γ(N)` to those of `Γ(M)` preserving zero flag restrictions such that,
for every frame `h`, the canonical pairing of the restrictions at the line (plane) group of `h` is `[Γ_h(N) : Γ_h(M)]` times the pairing at level `N`.
`stokesGammaNLiteral_of_restriction`: Stokes at level `M` (`6 ∣ M`, from Step 2) and these identities, summed with the regrouping of the faces of `Γ(M)` over the faces of `Γ(N)` (`lineFaces_regroup`, `planeFaces_regroup`) and the frame invariance at
level `N`, give the literal Stokes lemma at level `N` (the same factor `[Γ(N) : Γ(M)]` on both sides).
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FaceFibre

/-- **The restriction identities of the descent** `Γ(M) ≤ Γ(N)`. -/
def RestrictionIdent (N M n : ℕ) [NeZero N] [NeZero M] (hN : 3 ≤ N) (hM : 3 ≤ M) : Prop :=
  ∃ (R : groupCohomology.H2 (gammaNRepAll N n) → groupCohomology.H2 (gammaNRepAll M n))
    (R' : groupCohomology.H2 (gammaNRepAllDual N n) → groupCohomology.H2 (gammaNRepAllDual M n))
    (hR : ∀ a, ZeroFlags N n a → ZeroFlags M n (R a))
    (hR' : ∀ b, ZeroFlagsRep (gammaNRepAll N n).ρ.dual b → ZeroFlagsRep (gammaNRepAll M n).ρ.dual (R' b)),
    (∀ a (ha : ZeroFlags N n a) b (hb : ZeroFlagsRep (gammaNRepAll N n).ρ.dual b) (h : SL(3, ℤ)),
      canAtClass M h n hM (R a) (hR a ha) (R' b) (hR' b hb) =
        (((gammaNQAt M h).relIndex (gammaNQAt N h) : ℕ) : ℂ) * canAtClass N h n hN a ha b hb) ∧
    (∀ a (ha : ZeroFlags N n a) b (hb : ZeroFlagsRep (gammaNRepAll N n).ρ.dual b) (h : SL(3, ℤ)),
      canAtClassP M h n hM (R a) (hR a ha) (R' b) (hR' b hb) =
        (((gammaNPAt M h).relIndex (gammaNPAt N h) : ℕ) : ℂ) * canAtClassP N h n hN a ha b hb)

/-- **The wrapper (B3)**: the literal Stokes lemma at `Γ(N)` from Step 2 at level `M` and the restriction identities. -/
theorem stokesGammaNLiteral_of_restriction {N M n : ℕ} [NeZero N] [NeZero M] (hN : 3 ≤ N) (hM : 3 ≤ M) (hNM : N ∣ M)
    (h6 : 6 ∣ M) (S2 : Step2 M n hM) (hRes : RestrictionIdent N M n hN hM) : StokesGammaNLiteral N n hN := by
  obtain ⟨R, R', hR, hR', hL, hP⟩ := hRes
  intro a ha b hb
  have hS := stokes_literal_level h6 hM S2 (R a) (hR a ha) (R' b) (hR' b hb)
  have S1 := FrameInvariance.frameInvarianceLine N n hN
  have S1P := FrameInvariance.frameInvariancePlane N n hN
  -- frame-independence at level N, packaged as functions on the faces of Γ(N)
  have eL : ∀ i : LineFaces M, canAtClass N i.rep n hN a ha b hb =
      canAtClass N (LineFaces.mk (N := N) i.rep).rep n hN a ha b hb := by
    intro i
    obtain ⟨q, hq, γ, hγ, hr⟩ := LineFaces.rel_rep (N := N) i.rep
    have hr' : (LineFaces.mk (N := N) i.rep).rep = q * i.rep * γ := hr
    rw [hr', S1 a ha b hb i.rep q γ hq hγ]
  have eP : ∀ i : PlaneFaces M, canAtClassP N (planeFaceRepr i) n hN a ha b hb =
      canAtClassP N (planeFaceRepr (Quotient.mk (planeFaceSetoid N) (planeFaceRepr i))) n hN a ha b hb := by
    intro i
    obtain ⟨q, hq, γ, hγ, hr⟩ := PlaneFaces_rel_rep N (planeFaceRepr i)
    have hr' : planeFaceRepr (Quotient.mk (planeFaceSetoid N) (planeFaceRepr i)) = q * planeFaceRepr i * γ := hr
    rw [hr', S1P a ha b hb _ q γ hq hγ]
  have rL := lineFaces_regroup hN hNM (fun j => canAtClass N j.rep n hN a ha b hb)
  have rP := planeFaces_regroup hN hNM (fun j => canAtClassP N (planeFaceRepr j) n hN a ha b hb)
  have hSL : ∑ i : LineFaces M, canAtClass M i.rep n hM (R a) (hR a ha) (R' b) (hR' b hb) =
      ∑ i : LineFaces M, (((gammaNQAt M i.rep).relIndex (gammaNQAt N i.rep) : ℕ) : ℂ) *
        canAtClass N (LineFaces.mk (N := N) i.rep).rep n hN a ha b hb :=
    Finset.sum_congr rfl fun i _ => by rw [hL a ha b hb i.rep, eL i]
  have hSP : ∑ i : PlaneFaces M, canAtClassP M (planeFaceRepr i) n hM (R a) (hR a ha) (R' b) (hR' b hb) =
      ∑ i : PlaneFaces M, (((gammaNPAt M (planeFaceRepr i)).relIndex (gammaNPAt N (planeFaceRepr i)) : ℕ) : ℂ) *
        canAtClassP N (planeFaceRepr (Quotient.mk (planeFaceSetoid N) (planeFaceRepr i))) n hN a ha b hb :=
    Finset.sum_congr rfl fun i _ => by rw [hP a ha b hb (planeFaceRepr i), eP i]
  rw [hSL, hSP, rL, rP] at hS
  have hidx : ((((gammaN M).relIndex (gammaN N) : ℕ)) : ℂ) ≠ 0 := by
    have : (gammaN M).FiniteIndex := inferInstance
    have h1 : (gammaN M).IsFiniteRelIndex ⊤ := Subgroup.isFiniteRelIndex_top_iff.2 inferInstance
    have h2 : (gammaN M).IsFiniteRelIndex (gammaN N) := Subgroup.isFiniteRelIndex_of_le_right (H := gammaN M) (K := gammaN N) (L := ⊤) le_top
    exact Nat.cast_ne_zero.mpr (Subgroup.relIndex_ne_zero)
  have h2 : (((gammaN M).relIndex (gammaN N) : ℕ) : ℂ) *
      ((planeFaceOrientationSign : ℂ) * ∑ j : PlaneFaces N, canAtClassP N (planeFaceRepr j) n hN a ha b hb +
        (lineFaceOrientationSign : ℂ) * ∑ j : LineFaces N, canAtClass N j.rep n hN a ha b hb) = 0 := by
    linear_combination hS
  exact (mul_eq_zero.1 h2).resolve_left hidx

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
