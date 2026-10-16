module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.SeedPassageFace
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NConstantTerms

@[expose] public section


/-!
# CMP-8 (3a, 3b): seed classes up to values on the upper half plane, and the face seed classes as transports

* `etaForm_congr`, `seedClass_congr`, `seedConjClass_congr`: the primitive `η`, the class of the seed and the class of the antiholomorphic seed of a function `h`
  depend on `h` only through its values on the upper half plane (the seed parameters see `h` only at `τ(x)`, `x` in the face).
* `faceSeedKerClass_val`, `faceSeedConjKerClass_val`: the classes of S3's/the `seedBoundary` at a face `h` are the `(conjP N h, faceMor N n h)`-transports of the complexified
  classes `complexifyG (cuspSeedClass f)`, `complexifyG (cuspSeedConjClass f)` at the standard plane.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3.Psi
open TernaryPoly.SmoothLocalDeRham TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

noncomputable section
namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

/-- The 1-form `η` of the seed depends on `h` only through its values on the upper half plane. -/
theorem etaForm_congr (n : ℕ) (h h' : ℂ → ℂ) (hh : DifferentiableOn ℂ h upperSet)
    (hh' : DifferentiableOn ℂ h' upperSet) (hhh : ∀ z : ℂ, 0 < z.im → h z = h' z) :
    etaForm h hh n = etaForm h' hh' n := by
  apply Form.ext
  intro x hx
  unfold etaForm
  rw [restrictForm_apply _ _ hx, restrictForm_apply _ _ hx]
  unfold etaRaw psiVal
  have e : (fun a => sPar h a x) = fun a => sPar h' a x := by
    funext a
    fin_cases a <;> simp [sPar, hhh _ (faceTau_im hx)]
  rw [e]

variable {G : Type} [Group G] (D : PlaneData G) (n : ℕ) (h h' : ℂ → ℂ) (Gm Gm' : ℕ → ℂ → ℂ)
  (hh : DifferentiableOn ℂ h upperSet) (hh' : DifferentiableOn ℂ h' upperSet)
  (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
  (hG' : ∀ j z, 0 < z.im → HasDerivAt (Gm' j) (h' z * z ^ j) z)
  (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im → h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z)
  (hmod' : ∀ g : G, ∀ z : ℂ, 0 < z.im → h' (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h' z)
  (hhh : ∀ z : ℂ, 0 < z.im → h z = h' z)

include hhh in
/-- **The class of the seed depends on `h` only through its values on the upper half plane.** -/
theorem seedClass_congr : D.seedClass h n Gm hh hG hmod = D.seedClass h' n Gm' hh' hG' hmod' := by
  have hinv : D.seedInv h n Gm hh hG hmod = D.seedInv h' n Gm' hh' hG' hmod' := by
    apply Subtype.ext
    change d _ 1 (etaForm h hh n) = d _ 1 (etaForm h' hh' n)
    rw [etaForm_congr n h h' hh hh' hhh]
  rw [← D.deRhamClass_seedInv h n Gm hh hG hmod, ← D.deRhamClass_seedInv h' n Gm' hh' hG' hmod', hinv]

include hhh in
/-- The same for the antiholomorphic seed. -/
theorem seedConjClass_congr : D.seedConjClass h n Gm hh hG hmod = D.seedConjClass h' n Gm' hh' hG' hmod' := by
  have hinv : D.seedConjInv h n Gm hh hG hmod = D.seedConjInv h' n Gm' hh' hG' hmod' := by
    apply Subtype.ext
    change twForm _ 2 (d _ 1 (etaForm h hh n)) = twForm _ 2 (d _ 1 (etaForm h' hh' n))
    rw [etaForm_congr n h h' hh hh' hhh]
  rw [← D.deRhamClass_seedConjInv h n Gm hh hG hmod, ← D.deRhamClass_seedConjInv h' n Gm' hh' hG' hmod', hinv]

section FaceSeed

open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.FormSeedBridge
  TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ)

theorem faceSeedKerClass_val (h : SL(3, ℤ)) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    ((faceSeedKerClass N h n f).1 : groupCohomology.H2 (faceRep N h n)) =
      (groupCohomology.map (conjP N h).toMonoidHom (faceMor N n h) 2).hom
        (complexifyG N n (cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f))) := by
  rw [complexifyG_cuspSeedClass]
  rfl

theorem faceSeedConjKerClass_val (h : SL(3, ℤ)) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    ((faceSeedConjKerClass N h n f).1 : groupCohomology.H2 (faceRep N h n)) =
      (groupCohomology.map (conjP N h).toMonoidHom (faceMor N n h) 2).hom
        (complexifyG N n (cuspSeedConjClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f))) := by
  rw [complexifyG_cuspSeedConjClass]
  rfl


end FaceSeed

end TernaryPeriodPolynomials.Argument.KDaggerComparison
