module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EdgeSurjIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PAHecke

@[expose] public section


/-!
# The twisted identity-plane binary edge is surjective

For a rank-one character `χ` with `χ(-1_∞) = -1` and odd `n > 0`, the identity-plane stabilizer
`Λ₀ = U ⋊ GL₂(ℤ)` acts on `V_χ = Sym^n(ℂ³) ⊗ χ ∘ det`; the radical acts as in the untwisted case and
the Levi element `diag(m, 1)` acts by `det m` times the untwisted action.  The gradient section
`Q ↦ (∂₀ Q, ∂₁ Q)` of the radical cohomology is therefore equivariant for `Sym^{n+1} ⊗ det⁰`, the twist
`det m` appearing on both sides.  As in the untwisted case, the mixed two-cocycle of `ℓ ↦ σ(c ℓ)`
realises every one-cocycle `c` of `GL₂(ℤ)` with values in `Sym^{n+1} ⊗ det⁰`, so the twisted binary
edge `H²(Λ₀, V_χ) → H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁰)` is surjective, hence bijective
(`edgeH2T_surjective`, `edgeH2T_bijective`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjSplit
open TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjIdentity

namespace TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjTwisted

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Twisted
open PlaneCoordinates IdentityPlaneCosets IdentityPlaneCoordinate AmbientHecke

variable (n : ℕ) (χ : RankOneCharacter) (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)

/-- The gradient section with values in the radical cocycles of the twisted representation. -/
def twistedSection : arithmeticBinaryRep (n + 1) 0 →ₗ[ℂ]
    groupCohomology.cocycles₁ (Rep.res identityPlaneExtension.inl (identityPlaneCoefficientRepT n χ)) :=
  (cocycleFromUpperT n χ).comp (cocycleSection n)

include hχ in
/-- The twisted section intertwines `Sym^{n+1} ⊗ det⁰` with the split Levi action. -/
theorem twistedSection_equivariant (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (polynomial : arithmeticBinaryRep (n + 1) 0) :
    twistedSection n χ ((arithmeticBinaryRep (n + 1) 0).ρ matrix polynomial) =
      splitRadicalCocycleAction identityPlaneSplitting (identityPlaneCoefficientRepT n χ) matrix
        (twistedSection n χ polynomial) := by
  have action := cocycleToUpperT_splitAction n χ hχ matrix (twistedSection n χ polynomial)
  rw [show cocycleToUpperT n χ (twistedSection n χ polynomial) = cocycleSection n polynomial from
    cocycleToUpperT_fromUpper n χ (cocycleSection n polynomial)] at action
  have twist : cocycleSection n (Binary.homogeneousAction (n + 1) 0
        (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) polynomial) =
      (((GeneralLinearGroup.det matrix : ℤˣ) : ℤ) : ℂ) •
        upperRadicalCocycleLevi n matrix (cocycleSection n polynomial) := by
    exact (congrArg (cocycleSection n)
      (homogeneousAction_zero_twist_apply (n + 1) matrix polynomial)).trans
      ((map_smul (cocycleSection n) _ _).trans
        (congrArg (fun x => (((GeneralLinearGroup.det matrix : ℤˣ) : ℤ) : ℂ) • x)
          (cocycleSection_levi n matrix polynomial)))
  apply groupCohomology.cocycles₁_ext
  intro radical
  exact (congrArg (fun cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep n) => cycle radical)
    (action.trans twist.symm)).symm

/-- The relative two-cocycle of `Λ₀` (twisted coefficients) realising a binary one-cocycle. -/
def twistedRelative (cycle : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0)) :
    relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ) :=
  sectionRelative identityPlaneSplitting (identityPlaneCoefficientRepT n χ) (arithmeticBinaryRep (n + 1) 0)
    (twistedSection n χ) (twistedSection_equivariant n χ hχ) cycle

/-- **The twisted binary edge cocycle of `twistedRelative c` is `c`.** -/
theorem identityPlaneBinaryEdgeCycleT_twistedRelative
    (cycle : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0)) :
    identityPlaneBinaryEdgeCycleT n χ hχ (twistedRelative n χ hχ cycle) = cycle := by
  apply groupCohomology.cocycles₁_ext
  intro matrix
  exact (identityPlaneBinaryEdgeCycleT_apply n χ hχ (twistedRelative n χ hχ cycle) matrix).trans
    ((congrArg (fun radicalCycle => upperRadicalCocycleCoordinate n (cocycleToUpperT n χ radicalCycle))
      (splitEdgeCycle_sectionRelative identityPlaneSplitting (identityPlaneCoefficientRepT n χ)
        (arithmeticBinaryRep (n + 1) 0) (twistedSection n χ) (twistedSection_equivariant n χ hχ)
        cycle matrix)).trans
      ((congrArg (upperRadicalCocycleCoordinate n)
        (cocycleToUpperT_fromUpper n χ (cocycleSection n (cycle matrix)))).trans
        (coordinate_cocycleSection n (cycle matrix))))

variable (hn : 0 < n) (hodd : Odd n)

/-- **The full twisted binary edge `H²(Λ₀, V_χ) → H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁰)` is surjective.** -/
theorem identityPlaneFullBinaryEdgeT_surjective :
    Function.Surjective (identityPlaneFullBinaryEdgeT n χ hχ hn hodd) := by
  intro target
  obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (arithmeticBinaryRep (n + 1) 0) target
  exact ⟨_, (identityPlaneFullBinaryEdgeT_relative n χ hχ hn hodd (twistedRelative n χ hχ cycle)).trans
    (congrArg (groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0))
      (identityPlaneBinaryEdgeCycleT_twistedRelative n χ hχ cycle))⟩

/-- **The twisted binary edge on the ambient `H²(Λ₀, V_χ)` is surjective.** -/
theorem edgeH2T_surjective : Function.Surjective (edgeH2T n χ hχ hn hodd) := by
  intro target
  obtain ⟨source, equality⟩ := identityPlaneFullBinaryEdgeT_surjective n χ hχ hn hodd target
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective (identityPlaneCoefficientRepT n χ) source
  refine ⟨classOf Λ₀ (ρT n χ) (liftCocycle (identityPlaneCosets ⟨2, Nat.prime_two⟩) (ρT n χ) cycle), ?_⟩
  rw [edgeH2T_classOf, identityPlaneAmbientBinaryEdgeT_apply]
  exact (congrArg (fun lifted => identityPlaneFullBinaryEdgeT n χ hχ hn hodd
      (groupCohomology.H2π (identityPlaneCoefficientRepT n χ) lifted))
    (ambientCocycleToGroup_lift (identityPlaneCosets ⟨2, Nat.prime_two⟩) (ρT n χ) cycle)).trans equality

/-- **The twisted binary edge on the ambient `H²(Λ₀, V_χ)` is bijective.** -/
theorem edgeH2T_bijective : Function.Bijective (edgeH2T n χ hχ hn hodd) :=
  ⟨edgeH2T_injective n χ hχ hn hodd, edgeH2T_surjective n χ hχ hn hodd⟩

/-- The twisted binary edge as a linear equivalence
`H²(Λ₀, Sym^n ⊗ χ ∘ det) ≃ H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁰)`. -/
def edgeH2TEquiv : H2 Λ₀ (ρT n χ) ≃ₗ[ℂ] groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0) :=
  LinearEquiv.ofBijective (edgeH2T n χ hχ hn hodd) (edgeH2T_bijective n χ hχ hn hodd)

theorem edgeH2TEquiv_apply (x : H2 Λ₀ (ρT n χ)) :
    edgeH2TEquiv n χ hχ hn hodd x = edgeH2T n χ hχ hn hodd x := rfl

end TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjTwisted
