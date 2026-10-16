module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine4
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.BaseSumZeroFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Bridge

@[expose] public section


/-!
# (B_L): the joint restriction image of the line stabilizers is the sum-zero hyperplane

Formalized by Claude Sonnet 5.5.

For every choice of frames `F`, `LineImageSumZero flagH3Data F` holds: given `x` with zero sum over the flag orbits above each line orbit `a`, the additive function `φ_a` on `Γ(6)` with the prescribed cusp values
(`baseSumZero`, S2/S3: the cusp values of homomorphisms `Γ(6) → ℚ` fill the sum-zero hyperplane), the cusps being in bijection with the flag orbits above `a` (`cuspMap_injective`, `cuspMap_surjective`),
gives the class `lineClass a φ_a`, whose transport to the flag group of `o` has `λ = -432 φ_a(posPar(cusp of o))` (`lineTransport_lam`).
-/

open scoped MatrixGroups
open CongruenceSubgroup CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPeriodPolynomials.Argument.FlagH3

open Classical in
theorem exists_phi_line (F : ConjFrames) (x : labelOrbits Γ6 Flag → ℚ)
    (hx : ∀ a : labelOrbits Γ6 Line, ∑ o ∈ Finset.univ.filter (fun o => flagLineOrbit o = a), x o = 0)
    (a : labelOrbits Γ6 Line) :
    ∃ φ : Gamma 6 → ℚ, (∀ s t, φ (s * t) = φ s + φ t) ∧
      ∀ o, flagLineOrbit o = a → φ (posParSL (qVec (qOf o (F.γL o)))) = -x o / 432 := by
  let _ : Fintype {o : labelOrbits Γ6 Flag // flagLineOrbit o = a} := Fintype.ofFinite _
  have hbij : Function.Bijective (fun i : {o : labelOrbits Γ6 Flag // flagLineOrbit o = a} =>
      (Quotient.mk cuspSetoid (cuspVec F i.1) : Cusp6)) := by
    constructor
    · intro i j hij
      exact Subtype.ext (cuspMap_injective F i.1 j.1 (i.2.trans j.2.symm) (Quotient.exact hij))
    · intro c
      induction c using Quotient.inductionOn with
      | h v =>
        obtain ⟨o, ho, hrel⟩ := cuspMap_surjective F a v
        exact ⟨⟨o, ho⟩, Quotient.sound hrel⟩
  have hsum : ∑ i : {o : labelOrbits Γ6 Flag // flagLineOrbit o = a}, (-x i.1 / 432) = 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun o => flagLineOrbit o = a)) (fun o => by simp) (fun o => -x o / 432)]
    simp only [neg_div, Finset.sum_neg_distrib, ← Finset.sum_div, hx a]
    simp
  obtain ⟨φ, hφ, hval⟩ := baseSumZero (fun i : {o : labelOrbits Γ6 Flag // flagLineOrbit o = a} => cuspVec F i.1) hbij
    (fun i => -x i.1 / 432) hsum
  exact ⟨φ, hφ, fun o ho => hval ⟨o, ho⟩⟩

open Classical in
/-- **(B_L) is true**: the joint restriction image of the line stabilizers in the flag groups over one line orbit is the sum-zero hyperplane, in the classes `G_F`. -/
theorem lineImageSumZero (F : ConjFrames) : LineImageSumZero flagH3Data F := by
  intro x hx
  choose φ hφ hval using exists_phi_line F x hx
  refine ⟨fun a => lineClass a (φ a) (hφ a), fun o => ?_⟩
  apply flagLam_injective o.out
  rw [lineTransport_lam o (F.γL o) (F.hL o) (φ _) (hφ _), hval _ o rfl, map_smul, flagH3Data_G, flagLam_flagGen]
  simp
  ring

end TernaryPeriodPolynomials.Argument.GammaNStokes
