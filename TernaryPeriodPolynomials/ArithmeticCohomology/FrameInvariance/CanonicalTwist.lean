module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CuspConjStmt
public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.FaceCan

@[expose] public section


/-!
# The canonical face pairing under a twisted isomorphism of extensions

Formalized by Claude Sonnet 5.5.

`facePairingCan_twist` (assuming `CuspConjNat N hN`): let `X : ext₂ ≅ ext₁` be a twisted isomorphism of extensions of `Γ(N)` by the radical lattice, with radical map `φ`, Levi map `α` = conjugation by `A ∈ GL₂(ℤ)`
(`GLConj`), and `T : ρ₁ ≃ ρ₂` a coefficient isomorphism.  Then the canonical (cup-form normalised) pairings satisfy
`B₂ (Ξ̃ x) (Ξ̃' y) = det(φ) · det(A) · B₁ x y`.  The factor `det φ` is the orientation of the radical lattice (Koszul pairing) and `det A` the orientation of the modular curve (cup form); for the frames of
a face their product is `1`.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPoly.RankTwoAugmentedFrames

variable {N : ℕ} (hN : 3 ≤ N) {E₁ E₂ : Type} [Group E₁] [Group E₂]
  {ext₁ : GroupExtension RadicalLattice E₁ (Gamma N)} {ext₂ : GroupExtension RadicalLattice E₂ (Gamma N)}
  (X : TwistEquiv ext₂ ext₁) (s₁ : ext₁.Splitting) (s₂ : ext₂.Splitting)
  (ρ₁ : Rep ℂ E₁) (ρ₂ : Rep ℂ E₂) (T : ρ₁ ≃ₗ[ℂ] ρ₂)
  (hT : ∀ (g : E₂) (v : ρ₁), T (ρ₁.ρ (X.θ g) v) = ρ₂.ρ g (T v))

/-- The Levi-module map `M₁ → M₂` as a linear map between the Levi modules. -/
def leviMap : splitRadicalH1Representation s₁ ρ₁ →ₗ[ℂ] splitRadicalH1Representation s₂ ρ₂ :=
  radXi X ρ₁ ρ₂ T hT

theorem leviMap_equiv (l : Gamma N) (v : splitRadicalH1Representation s₁ ρ₁) :
    leviMap X s₁ s₂ ρ₁ ρ₂ T hT ((splitRadicalH1Representation s₁ ρ₁).ρ (X.α l) v) =
      (splitRadicalH1Representation s₂ ρ₂).ρ l (leviMap X s₁ s₂ ρ₁ ρ₂ T hT v) :=
  radXi_levi X ρ₁ ρ₂ T hT s₁ s₂ l v

variable [FiniteDimensional ℂ ρ₁] [FiniteDimensional ℂ ρ₂]

/-- The Levi-module map for the contragredient coefficient modules. -/
def leviMapDual : splitRadicalH1Representation s₁ (dualRepG ρ₁) →ₗ[ℂ] splitRadicalH1Representation s₂ (dualRepG ρ₂) :=
  radXi X (dualRepG ρ₁) (dualRepG ρ₂) (dualEquiv ρ₁ ρ₂ T) (hTdual X ρ₁ ρ₂ T hT)

omit [FiniteDimensional ℂ ρ₁] [FiniteDimensional ℂ ρ₂] in
theorem leviMapDual_equiv (l : Gamma N) (v : splitRadicalH1Representation s₁ (dualRepG ρ₁)) :
    leviMapDual X s₁ s₂ ρ₁ ρ₂ T hT ((splitRadicalH1Representation s₁ (dualRepG ρ₁)).ρ (X.α l) v) =
      (splitRadicalH1Representation s₂ (dualRepG ρ₂)).ρ l (leviMapDual X s₁ s₂ ρ₁ ρ₂ T hT v) :=
  radXi_levi X (dualRepG ρ₁) (dualRepG ρ₂) (dualEquiv ρ₁ ρ₂ T) (hTdual X ρ₁ ρ₂ T hT) s₁ s₂ l v

variable (hdet₁ : ∀ A, radDet (splitRadicalInput s₁ A) = 1) (hdet₂ : ∀ A, radDet (splitRadicalInput s₂ A) = 1)
  (A : IntegralGL) (hA : GLConj hN X.α A)

/-- **The canonical face pairing under a twisted isomorphism of extensions** (the orientation signs `det φ` of the radical and `det A` of the modular curve appear explicitly). -/
theorem facePairingCan_twist (hconj : CuspConjNat N hN)
    (x : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s₁ ρ₁))
    (y : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s₁ (dualRepG ρ₁))) :
    facePairingCan hN s₂ hdet₂ ρ₂
        (cuspXi hN X.α A hA _ _ (leviMap X s₁ s₂ ρ₁ ρ₂ T hT) (leviMap_equiv X s₁ s₂ ρ₁ ρ₂ T hT) x)
        (cuspXi hN X.α A hA _ _ (leviMapDual X s₁ s₂ ρ₁ ρ₂ T hT) (leviMapDual_equiv X s₁ s₂ ρ₁ ρ₂ T hT) y) =
      (radDet X.φ.toMonoidHom : ℂ) * ((A.val.det : ℤ) : ℂ) * facePairingCan hN s₁ hdet₁ ρ₁ x y := by
  have : FiniteDimensional ℂ (splitRadicalH1Representation s₁ ρ₁) := finiteDimensional_H1 (Rep.res ext₁.inl ρ₁)
  have : FiniteDimensional ℂ (splitRadicalH1Representation s₁ (dualRepG ρ₁)) :=
    finiteDimensional_H1 (Rep.res ext₁.inl (dualRepG ρ₁))
  have : FiniteDimensional ℂ (splitRadicalH1Representation s₂ ρ₂) := finiteDimensional_H1 (Rep.res ext₂.inl ρ₂)
  have : FiniteDimensional ℂ (splitRadicalH1Representation s₂ (dualRepG ρ₂)) :=
    finiteDimensional_H1 (Rep.res ext₂.inl (dualRepG ρ₂))
  refine hconj X.α A hA _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (isCupPairing_facePairingCan hN s₁ hdet₁ ρ₁) (isCupPairing_facePairingCan hN s₂ hdet₂ ρ₂)
    (leviMap X s₁ s₂ ρ₁ ρ₂ T hT) (leviMapDual X s₁ s₂ ρ₁ ρ₂ T hT) (leviMap_equiv X s₁ s₂ ρ₁ ρ₂ T hT)
    (leviMapDual_equiv X s₁ s₂ ρ₁ ρ₂ T hT) _ (fun v w => ?_) x y
  exact radPairing_xi X ρ₁ ρ₂ T hT v w

end TernaryPeriodPolynomials.Argument.FrameInvariance
