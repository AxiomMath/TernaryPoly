module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ShapiroProduct

@[expose] public section


/-!
# Vanishing of the cohomology of a permutation resolution from that of the stabilizers, in every degree

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.EquivariantSingularSmall

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

/-- The `n`-th cohomology of a product of cochain complexes of rational vector spaces vanishes if that of every factor does. -/
theorem isZero_homology_productComplex {I : Type} (C : I → CochainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (h : ∀ i, IsZero ((C i).homology n)) : IsZero ((Family.productComplex C).homology n) := by
  have hex : ∀ i, (C i).ExactAt n := fun i => (HomologicalComplex.exactAt_iff_isZero_homology (C i) n).2 (h i)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' _ ((ComplexShape.up ℕ).prev n) n ((ComplexShape.up ℕ).next n) rfl rfl,
    ShortComplex.moduleCat_exact_iff]
  intro a ha
  have hi : ∀ i, ∃ b : (C i).X ((ComplexShape.up ℕ).prev n), ((C i).d _ n).hom b = a i := by
    intro i
    have := (HomologicalComplex.exactAt_iff' (C i) ((ComplexShape.up ℕ).prev n) n ((ComplexShape.up ℕ).next n) rfl rfl).1 (hex i)
    rw [ShortComplex.moduleCat_exact_iff] at this
    exact this (a i) (congrFun ha i)
  choose b hb using hi
  exact ⟨b, funext hb⟩

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] (v₀ : V)
  (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (W : Rep.{0} ℚ Γ)

include v₀ hfree in
/-- **Vanishing of the degree-`n` cohomology of a permutation resolution** from the vanishing of the degree-`n` cohomology of the stabilizers of the orbit
representatives: `H^n(Hom_Γ(prodComplex Γ V Z, W)) = 0` if `H^n(Stab o, W) = 0` for all orbits `o`. -/
theorem isZero_homCochains_prod (n : ℕ)
    (h : ∀ o : labelOrbits Γ Z, IsZero (groupCohomology (Rep.res (stabilizer Γ o.out).subtype W) n)) :
    IsZero ((homCochains (prodComplex Γ V Z) W).homology n) := by
  let κ := stabToProd (Z := Z) v₀ hfree
  have hq : QuasiIso (homPullback κ W) :=
    homPullback_quasiIso_of_homotopyEquiv
      (comparison (stabilizerResolution Γ Z) (prodResolution Γ V Z v₀ hfree)) W
  have : QuasiIsoAt (homPullback κ W) n := inferInstance
  have e1 := isoOfQuasiIsoAt (homPullback κ W) n
  have e2 := HomologicalComplex.homologyMapIso (fullShapiroIso Γ Z W) n
  have hfac : ∀ o : labelOrbits Γ Z, IsZero
      ((homCochains (Rep.barResolution ℚ (stabilizer Γ o.out)).complex
        (Rep.res (stabilizer Γ o.out).subtype W)).homology n) :=
    fun o => (h o).of_iso (gisoBar (Rep.res (stabilizer Γ o.out).subtype W) n).symm
  have hprod := isZero_homology_productComplex (fun o : labelOrbits Γ Z =>
    homCochains (Rep.barResolution ℚ (stabilizer Γ o.out)).complex (Rep.res (stabilizer Γ o.out).subtype W)) n hfac
  exact (hprod.of_iso e2).of_iso e1

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
