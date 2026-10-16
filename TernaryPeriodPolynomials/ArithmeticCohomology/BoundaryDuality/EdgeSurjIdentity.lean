module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EdgeSurjSplit
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneHecke

@[expose] public section


/-!
# The identity-plane binary edge is surjective

Let `Λ₀ = U ⋊ GL₂(ℤ)` be the arithmetic stabilizer of the identity plane, `U ≅ ℤ²` its radical and
`V = Sym^n(ℂ³)` (odd `n > 0`, trivial character).  The radical one-cocycles are identified with
closed pairs `(p₀, p₁)` of degree-`n` forms (`∂₀ p₁ = ∂₁ p₀`), and the radical cohomology with
`Sym^{n+1} ⊗ det⁻¹` through `(p₀, p₁) ↦ (n+1)⁻¹ (X₀ p₀ + X₁ p₁)|_{X₂ = 0}`.

The gradient `Q ↦ (∂₀ Q, ∂₁ Q)` of a binary form of degree `n + 1` is a closed pair with coordinate
`Q` (Euler), and it is exactly `GL₂`-equivariant at the level of cocycles.  It is therefore an
equivariant cocycle-level section `σ : Sym^{n+1} ⊗ det⁻¹ → Z¹(U, V)` of the radical cohomology, and
for every one-cocycle `c` of `GL₂(ℤ)` the mixed two-cocycle of the strict family `ℓ ↦ σ(c ℓ)` has
binary edge cocycle exactly `c`.  Consequently the binary edge
`H²(Λ₀, V) → H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` is surjective, hence (being injective) bijective, both on
group cohomology and on the ambient homogeneous model `H2 Λ₀ (ρn n)` (`edgeH2_surjective`,
`edgeH2_bijective`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjSplit

namespace TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjIdentity

open TernaryPeriodPolynomials.Spectral
open PlaneCoordinates IdentityPlaneCosets IdentityPlaneCoordinate AmbientHecke

variable (n : ℕ)

/-- The gradient of a binary form, as a closed plane-radical pair. -/
def gradientCycle : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] planeRadicalCycles n where
  toFun polynomial := ⟨binaryGradientPair polynomial, binaryGradientPair_closed polynomial⟩
  map_add' first second := by
    apply Subtype.ext
    funext coordinate
    apply Subtype.ext
    change pderiv coordinate.castSucc (binaryPolynomialLift (first.val + second.val)) =
      pderiv coordinate.castSucc (binaryPolynomialLift first.val) +
        pderiv coordinate.castSucc (binaryPolynomialLift second.val)
    rw [map_add, map_add]
  map_smul' scalar polynomial := by
    apply Subtype.ext
    funext coordinate
    apply Subtype.ext
    change pderiv coordinate.castSucc (binaryPolynomialLift (scalar • polynomial.val)) =
      scalar • pderiv coordinate.castSucc (binaryPolynomialLift polynomial.val)
    rw [map_smul, Derivation.map_smul]

/-- The gradient pair is equivariant for the Levi action on closed pairs. -/
theorem gradientCycle_levi (matrix : Binary.GL2) (polynomial : Binary.HomogeneousPoly (n + 1)) :
    planeRadicalCycleLevi n matrix (gradientCycle n polynomial) =
      gradientCycle n (Binary.homogeneousAction (n + 1) (-1) matrix polynomial) := by
  apply Subtype.ext
  funext coordinate
  apply Subtype.ext
  change planeRadicalLeviPair matrix
      (fun index => pderiv index.castSucc (binaryPolynomialLift polynomial.val)) coordinate =
    pderiv coordinate.castSucc (binaryPolynomialLift (Binary.action (-1) matrix polynomial.val))
  exact planeRadicalLeviPair_gradient matrix polynomial.val coordinate

/-- The cocycle-level section `Q ↦ σ(Q)` of the upper radical cohomology. -/
def cocycleSection :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] groupCohomology.cocycles₁ (upperRadicalLatticeRep n) :=
  (upperRadicalCocycleEquiv n).symm.toLinearMap.comp (gradientCycle n)

theorem toInfinitesimal_cocycleSection (polynomial : Binary.HomogeneousPoly (n + 1)) :
    upperRadicalCocycleToInfinitesimal n (cocycleSection n polynomial) = gradientCycle n polynomial :=
  (upperRadicalCocycleEquiv n).apply_symm_apply (gradientCycle n polynomial)

/-- The section is a section of the binary coordinate. -/
theorem coordinate_cocycleSection (polynomial : Binary.HomogeneousPoly (n + 1)) :
    upperRadicalCocycleCoordinate n (cocycleSection n polynomial) = polynomial := by
  change planeRadicalCycleCoordinate n
    (upperRadicalCocycleToInfinitesimal n (cocycleSection n polynomial)) = polynomial
  rw [toInfinitesimal_cocycleSection]
  exact planeRadicalCoordinate_gradient polynomial

/-- The section is equivariant at the level of cocycles. -/
theorem cocycleSection_levi (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (polynomial : Binary.HomogeneousPoly (n + 1)) :
    cocycleSection n (Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) polynomial) =
      upperRadicalCocycleLevi n matrix (cocycleSection n polynomial) := by
  apply (upperRadicalCocycleEquiv n).injective
  change upperRadicalCocycleToInfinitesimal n (cocycleSection n _) =
    upperRadicalCocycleToInfinitesimal n (upperRadicalCocycleLevi n matrix (cocycleSection n polynomial))
  rw [upperRadicalCocycleToInfinitesimal_equivariant, toInfinitesimal_cocycleSection,
    toInfinitesimal_cocycleSection, gradientCycle_levi]

/-- The section as a map into the radical cocycles of the identity-plane extension. -/
def identitySection : arithmeticBinaryRep (n + 1) (-1) →ₗ[ℂ]
    groupCohomology.cocycles₁ (Rep.res identityPlaneExtension.inl (identityPlaneCoefficientRep n)) :=
  cocycleSection n

/-- The section intertwines the binary action with the split Levi action on radical cocycles. -/
theorem identitySection_equivariant (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (polynomial : arithmeticBinaryRep (n + 1) (-1)) :
    identitySection n ((arithmeticBinaryRep (n + 1) (-1)).ρ matrix polynomial) =
      splitRadicalCocycleAction identityPlaneSplitting (identityPlaneCoefficientRep n) matrix
        (identitySection n polynomial) :=
  (cocycleSection_levi n matrix polynomial).trans
    (identityPlaneSplitCocycleAction n matrix (cocycleSection n polynomial)).symm

/-- The relative two-cocycle of `Λ₀` realising a binary one-cocycle. -/
def identityRelative (cycle : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1))) :
    relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n) :=
  sectionRelative identityPlaneSplitting (identityPlaneCoefficientRep n) (arithmeticBinaryRep (n + 1) (-1))
    (identitySection n) (identitySection_equivariant n) cycle

/-- **The binary edge cocycle of `identityRelative c` is `c`.** -/
theorem identityPlaneBinaryEdgeCycle_identityRelative
    (cycle : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1))) :
    identityPlaneBinaryEdgeCycle n (identityRelative n cycle) = cycle := by
  apply groupCohomology.cocycles₁_ext
  intro matrix
  exact (identityPlaneBinaryEdgeCycle_apply n (identityRelative n cycle) matrix).trans
    ((congrArg (upperRadicalCocycleCoordinate n)
      (splitEdgeCycle_sectionRelative identityPlaneSplitting (identityPlaneCoefficientRep n)
        (arithmeticBinaryRep (n + 1) (-1)) (identitySection n) (identitySection_equivariant n)
        cycle matrix)).trans (coordinate_cocycleSection n (cycle matrix)))

variable (hn : 0 < n) (hodd : Odd n)

/-- **The full binary edge `H²(Λ₀, V) → H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` is surjective.** -/
theorem identityPlaneFullBinaryEdge_surjective :
    Function.Surjective (identityPlaneFullBinaryEdge n hn hodd) := by
  intro target
  obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (arithmeticBinaryRep (n + 1) (-1)) target
  exact ⟨_, (identityPlaneFullBinaryEdge_relative n hn hodd (identityRelative n cycle)).trans
    (congrArg (groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)))
      (identityPlaneBinaryEdgeCycle_identityRelative n cycle))⟩

/-- **The binary edge on the ambient `H²(Λ₀, V)` is surjective.** -/
theorem edgeH2_surjective : Function.Surjective (IdentityPlaneHecke.edgeH2 n hn hodd) := by
  intro target
  obtain ⟨source, equality⟩ := identityPlaneFullBinaryEdge_surjective n hn hodd target
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective (identityPlaneCoefficientRep n) source
  refine ⟨classOf Λ₀ (ρn n) (liftCocycle (identityPlaneCosets ⟨2, Nat.prime_two⟩) (ρn n) cycle), ?_⟩
  rw [IdentityPlaneHecke.edgeH2_classOf, identityPlaneAmbientBinaryEdge_apply]
  exact (congrArg (fun lifted => identityPlaneFullBinaryEdge n hn hodd
      (groupCohomology.H2π (identityPlaneCoefficientRep n) lifted))
    (ambientCocycleToGroup_lift (identityPlaneCosets ⟨2, Nat.prime_two⟩) (ρn n) cycle)).trans equality

/-- **The binary edge on the ambient `H²(Λ₀, V)` is bijective.** -/
theorem edgeH2_bijective : Function.Bijective (IdentityPlaneHecke.edgeH2 n hn hodd) :=
  ⟨IdentityPlaneHecke.edgeH2_injective n hn hodd, edgeH2_surjective n hn hodd⟩

/-- The binary edge as a linear equivalence
`H²(Λ₀, Sym^n) ≃ H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`. -/
def edgeH2Equiv : H2 Λ₀ (ρn n) ≃ₗ[ℂ] groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1)) :=
  LinearEquiv.ofBijective (IdentityPlaneHecke.edgeH2 n hn hodd) (edgeH2_bijective n hn hodd)

theorem edgeH2Equiv_apply (x : H2 Λ₀ (ρn n)) :
    edgeH2Equiv n hn hodd x = IdentityPlaneHecke.edgeH2 n hn hodd x := rfl

end TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjIdentity
