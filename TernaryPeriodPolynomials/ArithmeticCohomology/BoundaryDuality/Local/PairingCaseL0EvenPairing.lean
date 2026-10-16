module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenAlpha
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BadIdentPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AdjointLevelThreePairing

@[expose] public section


/-!
# The bad-line / good-plane pairing in even degree

For even `n` the untwisted coefficients `Sym^{n+1}` of `Γ₁'(3)` pair with themselves
(`twistedPairing_binaryArithmeticRepresentation`): the parabolic cup pairing `P` of
`H¹(Γ₁'(3), Sym^{n+1})` with itself.  The good-plane edge of the local cohomology, however, lands in
`H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`.  The identification of the bridge cocycle `badX'` of the dual
coordinate (`BadIdentPlane.badX'_apply`) is `badX' γ = - E (e (α γ))` for the good-plane edge
cocycle
`e`, where `α` is the cusp-exchanging involution of `Γ₁'(3)` and `E = planeComparison n` the
equivariant isomorphism of the coefficients.  Hence the pairing of the bad-line Levi class with the
good-plane edge is `P` composed with the *transport* `[e] ↦ [γ ↦ - E (e (α γ))]`, a linear
isomorphism between the crossed `H¹`s preserving the parabolic classes.

* `transportCocycles`, `transportH1`: the transport along a multiplicative `a : G → G` and an
  equivariant `E` (generic);
* `planeTransportPar`: the transport restricted to parabolic classes, surjective onto the parabolic
  classes of `Sym^{n+1}`;
* `badGoodPairingEven`: the pairing `P ∘ (1 × transport)` of `H¹_par(Γ₁'(3), Sym^{n+1})` with
  `H¹_par(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`, left nondegenerate;
* `BadGoodHeckeAdjointEven`: **the Hecke adjointness hypothesis for even `n`**, the exact analogue
  of `AdjointLevelThreePairing.BadGoodHeckeAdjoint` (`⟨T_p x, y⟩ = p⁻¹ ⟨x, T_p y⟩` for all primes
  `p ≠ 3`), with the pairing `badGoodPairingEven`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

section Concrete

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossed parabolicCrossedH1 parabolicPairing mem_parabolicCrossed_of_mem
    twistedPairing_binaryArithmeticRepresentation
    binaryArithmeticRepresentation_left_nondegenerate)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
  (alpha planeComparison planeComparison_intertwines act_swap_involutive parabolic_pullback)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (binarySwap binarySwapVar binarySwap_injective binarySwapVar_involutive swapZ)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2
  (Phi PhiInv Phi_PhiInv)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelThree
  (LevelThreeParabolicAdjoint levelThreeKappa)

variable {n : ℕ}

/-- The comparison map of the coefficients is injective. -/
theorem planeComparison_injective (n : ℕ) : Function.Injective (planeComparison n) := by
  have h1 : Function.Injective (binarySwapVar (n + 1)) :=
    Function.LeftInverse.injective (g := ⇑(binarySwapVar (n + 1)))
      (binarySwapVar_involutive (n + 1))
  have h2 : Function.Injective (binarySwap (n + 1)) := binarySwap_injective (n + 1)
  have h3 : Function.Injective (Binary.homogeneousAction (n + 1) (-1)
      (GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ)) :=
    Function.LeftInverse.injective
      (g := ⇑(Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ))) (act_swap_involutive n)
  have h4 : Function.Injective (PhiInv n) :=
    Function.LeftInverse.injective (g := ⇑(Phi n)) (Phi_PhiInv n)
  unfold planeComparison
  simp only [LinearMap.coe_comp]
  exact h1.comp (h2.comp (h3.comp h4))

/-- The comparison map of the coefficients as a linear equivalence. -/
def planeComparisonEquiv (n : ℕ) :
    Binary.HomogeneousPoly (n + 1) ≃ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  LinearEquiv.ofInjectiveEndo (planeComparison n) (planeComparison_injective n)

/-- The inverse comparison is equivariant for the swapped roles of the two coefficient systems. -/
theorem planeComparison_symm_intertwines (heven : Even n) (γ : binaryArithmeticLevel)
    (w : Binary.HomogeneousPoly (n + 1)) :
    (planeComparisonEquiv n).symm (binaryArithmeticRepresentation n (alpha γ) w) =
      levelRep (n + 1) (-1) γ ((planeComparisonEquiv n).symm w) := by
  obtain ⟨v, rfl⟩ := (planeComparisonEquiv n).surjective w
  rw [LinearEquiv.symm_apply_apply]
  have h := planeComparison_intertwines n heven (alpha γ) v
  rw [alpha_alpha] at h
  have h' : (planeComparisonEquiv n) (levelRep (n + 1) (-1) γ v) =
      binaryArithmeticRepresentation n (alpha γ) ((planeComparisonEquiv n) v) := h
  rw [← h', LinearEquiv.symm_apply_apply]

/-- **The transport from the good-plane coefficients to the bad-line coefficients.** -/
def planeTransportH1 (heven : Even n) :
    CrossedH1 (levelRep (n + 1) (-1)) →ₗ[ℂ] CrossedH1 (binaryArithmeticRepresentation n) :=
  transportH1 (levelRep (n + 1) (-1)) (binaryArithmeticRepresentation n) alpha alpha_mul
    (planeComparison n) (planeComparison_intertwines n heven)

/-- **The inverse transport.** -/
def planeTransportBackH1 (heven : Even n) :
    CrossedH1 (binaryArithmeticRepresentation n) →ₗ[ℂ] CrossedH1 (levelRep (n + 1) (-1)) :=
  transportH1 (binaryArithmeticRepresentation n) (levelRep (n + 1) (-1)) alpha alpha_mul
    (planeComparisonEquiv n).symm.toLinearMap (planeComparison_symm_intertwines heven)

/-- The transport sends parabolic classes to parabolic classes. -/
theorem planeTransportH1_mem (heven : Even n) {x : CrossedH1 (levelRep (n + 1) (-1))}
    (hx : x ∈ parabolicCrossedH1 (levelRep (n + 1) (-1))) :
    planeTransportH1 heven x ∈ parabolicCrossedH1 (binaryArithmeticRepresentation n) := by
  have hx' : x ∈ (parabolicCrossed (levelRep (n + 1) (-1))).map
      (crossedBoundaries (levelRep (n + 1) (-1))).mkQ := hx
  obtain ⟨e, he, rfl⟩ := Submodule.mem_map.mp hx'
  have hT : transportCocycles (levelRep (n + 1) (-1)) (binaryArithmeticRepresentation n) alpha
      alpha_mul (planeComparison n) (planeComparison_intertwines n heven) e ∈
        parabolicCrossed (binaryArithmeticRepresentation n) :=
    parabolic_pullback (levelRep (n + 1) (-1)) (binaryArithmeticRepresentation n)
      (planeComparison n) (planeComparison_intertwines n heven) e he _
      (fun γ => transportCocycles_apply _ _ alpha alpha_mul _ _ e γ)
  have h1 : (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ
      (transportCocycles (levelRep (n + 1) (-1)) (binaryArithmeticRepresentation n) alpha
        alpha_mul (planeComparison n) (planeComparison_intertwines n heven) e) ∈
      parabolicCrossedH1 (binaryArithmeticRepresentation n) := Submodule.mem_map_of_mem hT
  exact h1

/-- The inverse transport sends parabolic classes to parabolic classes. -/
theorem planeTransportBackH1_mem (heven : Even n)
    {x : CrossedH1 (binaryArithmeticRepresentation n)}
    (hx : x ∈ parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
    planeTransportBackH1 heven x ∈ parabolicCrossedH1 (levelRep (n + 1) (-1)) := by
  have hx' : x ∈ (parabolicCrossed (binaryArithmeticRepresentation n)).map
      (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ := hx
  obtain ⟨e, he, rfl⟩ := Submodule.mem_map.mp hx'
  have hT : transportCocycles (binaryArithmeticRepresentation n) (levelRep (n + 1) (-1)) alpha
      alpha_mul (planeComparisonEquiv n).symm.toLinearMap (planeComparison_symm_intertwines heven)
      e ∈ parabolicCrossed (levelRep (n + 1) (-1)) :=
    parabolic_pullback (binaryArithmeticRepresentation n) (levelRep (n + 1) (-1))
      (planeComparisonEquiv n).symm.toLinearMap (planeComparison_symm_intertwines heven) e he _
      (fun γ => transportCocycles_apply _ _ alpha alpha_mul _ _ e γ)
  have h1 : (crossedBoundaries (levelRep (n + 1) (-1))).mkQ
      (transportCocycles (binaryArithmeticRepresentation n) (levelRep (n + 1) (-1)) alpha
        alpha_mul (planeComparisonEquiv n).symm.toLinearMap
        (planeComparison_symm_intertwines heven) e) ∈
      parabolicCrossedH1 (levelRep (n + 1) (-1)) := Submodule.mem_map_of_mem hT
  exact h1

/-- **The transport on parabolic classes.** -/
def planeTransportPar (heven : Even n) :
    parabolicCrossedH1 (levelRep (n + 1) (-1)) →ₗ[ℂ]
      parabolicCrossedH1 (binaryArithmeticRepresentation n) :=
  (planeTransportH1 heven).restrict fun _ hx => planeTransportH1_mem heven hx

/-- The underlying class of the parabolic transport. -/
theorem planeTransportPar_coe (heven : Even n) (x : parabolicCrossedH1 (levelRep (n + 1) (-1))) :
    ((planeTransportPar heven x : parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
      CrossedH1 (binaryArithmeticRepresentation n)) =
      planeTransportH1 heven (x : CrossedH1 (levelRep (n + 1) (-1))) :=
  LinearMap.coe_restrict_apply _ x

/-- The forward transport undoes the inverse transport. -/
theorem planeTransportH1_back (heven : Even n) (x : CrossedH1 (binaryArithmeticRepresentation n)) :
    planeTransportH1 heven (planeTransportBackH1 heven x) = x := by
  obtain ⟨e, rfl⟩ := Submodule.mkQ_surjective _ x
  change (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ
    (transportCocycles (levelRep (n + 1) (-1)) (binaryArithmeticRepresentation n) alpha
      alpha_mul (planeComparison n) (planeComparison_intertwines n heven)
      (transportCocycles (binaryArithmeticRepresentation n) (levelRep (n + 1) (-1)) alpha
        alpha_mul (planeComparisonEquiv n).symm.toLinearMap
        (planeComparison_symm_intertwines heven) e)) = _
  rw [transportCocycles_transportCocycles (binaryArithmeticRepresentation n)
    (levelRep (n + 1) (-1)) alpha alpha_mul alpha_alpha (planeComparisonEquiv n).symm.toLinearMap
    (planeComparison n) (planeComparison_symm_intertwines heven)
    (planeComparison_intertwines n heven)
    (fun v => (planeComparisonEquiv n).apply_symm_apply v) e]

/-- **The parabolic transport is surjective onto the parabolic classes of `Sym^{n+1}`.** -/
theorem planeTransportPar_surjective (heven : Even n) :
    Function.Surjective (planeTransportPar heven) := fun y =>
  ⟨⟨planeTransportBackH1 heven (y : CrossedH1 (binaryArithmeticRepresentation n)),
    planeTransportBackH1_mem heven y.2⟩, Subtype.ext (planeTransportH1_back heven y)⟩

/-- **The Lefschetz pairing of the bad-line Levi with the good-plane Levi in even degree**: the
parabolic cup pairing of `H¹_par(Γ₁'(3), Sym^{n+1})` with itself, composed with the transport of the
good-plane coefficients `Sym^{n+1} ⊗ det⁻¹`. -/
def badGoodPairingEven (heven : Even n) :
    parabolicCrossedH1 (binaryArithmeticRepresentation n) →ₗ[ℂ]
      parabolicCrossedH1 (levelRep (n + 1) (-1)) →ₗ[ℂ] ℂ :=
  (parabolicPairing (twistedPairing_binaryArithmeticRepresentation n heven)).compl₂
    (planeTransportPar heven)

/-- The value of the even pairing on parabolic classes. -/
theorem badGoodPairingEven_apply (heven : Even n)
    (x : parabolicCrossedH1 (binaryArithmeticRepresentation n))
    (y : parabolicCrossedH1 (levelRep (n + 1) (-1))) :
    badGoodPairingEven heven x y =
      parabolicPairing (twistedPairing_binaryArithmeticRepresentation n heven) x
        (planeTransportPar heven y) := rfl

/-- **Left nondegeneracy of the even pairing**: a parabolic class of the bad-line Levi cohomology
pairing to zero with every parabolic class of the good-plane Levi cohomology is zero. -/
theorem badGoodPairingEven_left_nondegenerate (heven : Even n)
    (x : parabolicCrossedH1 (binaryArithmeticRepresentation n))
    (h : ∀ y : parabolicCrossedH1 (levelRep (n + 1) (-1)), badGoodPairingEven heven x y = 0) :
    x = 0 := by
  refine binaryArithmeticRepresentation_left_nondegenerate n heven x fun cl' => ?_
  obtain ⟨y, rfl⟩ := planeTransportPar_surjective heven cl'
  exact h y

/-- **The Hecke adjointness hypothesis for even `n`** (the analogue of
`AdjointLevelThreePairing.BadGoodHeckeAdjoint`, which is stated for odd `n`): for every prime
`p ≠ 3`, `⟨T_p x, y⟩ = p⁻¹ ⟨x, T_p y⟩` for the pairing `badGoodPairingEven` of the parabolic classes
of `H¹(Γ₁'(3), Sym^{n+1})` with those of `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`. -/
def BadGoodHeckeAdjointEven (heven : Even n) : Prop :=
  LevelThreeParabolicAdjoint n (badGoodPairingEven heven) levelThreeKappa

end Concrete

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

end
