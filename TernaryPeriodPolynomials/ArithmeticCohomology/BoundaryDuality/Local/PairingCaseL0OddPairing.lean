module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenAlpha
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BadIdentPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadOdd
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AdjointLevelThreePairing

@[expose] public section



/-!
# The bad-line / good-plane pairing in odd degree

For odd `n` the coefficients `Sym^{n+1}` of the bad-line Levi and `Sym^{n+1} ⊗ det⁻¹` of the
good-plane Levi pair directly (`AdjointLevelThreePairing.badGoodPairing`).  The good-plane edge of
the local cohomology lands in `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` in the coordinates of the reference
good plane, whereas the Levi cocycle of the dual plane of the bad line, which enters the local value,
is its *transport* along the cusp-exchanging involution `α` of `Γ₁'(3)` and the comparison map `E`
of the coefficients (`BadIdentPlane.badXOdd'_apply`): `badXOdd' γ = - E (e (α γ))` for the
good-plane edge cocycle `e`.

* `thetaH1`: the transport `[e] ↦ [γ ↦ - E (e (α γ))]` of `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` to itself
  (an instance of the generic transport of `LocalPairingCaseL0OddTransport`), an injective linear
  map which preserves the parabolic classes and is onto them (`thetaPar_surjective`);
* `badGoodPairingOdd`: the pairing `badGoodPairing ∘ (1 × transport)` of the parabolic classes of
  the bad-line Levi with those of the good-plane Levi, left nondegenerate;
* `BadGoodHeckeAdjointOdd`: **the Hecke adjointness hypothesis for odd `n`**, the exact analogue of
  `AdjointLevelThreePairing.BadGoodHeckeAdjoint` for the pairing `badGoodPairingOdd`
  (`⟨T_p x, y⟩ = p⁻¹ ⟨x, T_p y⟩`), and `badGoodHeckeAdjointOdd_of_commute`, which derives it from
  `BadGoodHeckeAdjoint` and the commutation `ThetaHeckeCommute` of the transport with the Hecke
  operators `T_p`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd

open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddTransport
  (transportH1 transportH1_injective transportH1_surjective_on transportH1_qcls
    transportCocycles)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even
  (alpha_mul alpha_alpha)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossed parabolicCrossedH1 mem_parabolicCrossed_of_mem)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
  (alpha planeComparison planeComparison_intertwines_odd parabolic_pullback act_swap_involutive)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (binarySwap binarySwapVar binarySwap_injective binarySwapVar_involutive swapZ)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2 (Phi PhiInv Phi_PhiInv)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (levelHecke)
open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelThree
  (badGoodPairing BadGoodHeckeAdjoint LevelThreeParabolicAdjoint levelThreeKappa parabolicHecke
    parabolicHecke_coe)
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLevi (IsHeckeAdjoint)

variable {n : ℕ}

section Alpha

/-- **The cusp-exchanging involution `α` of `Γ₁'(3)` as a group endomorphism.** -/
def alphaHom : binaryArithmeticLevel →* binaryArithmeticLevel :=
  MonoidHom.mk' alpha alpha_mul

theorem alphaHom_apply (γ : binaryArithmeticLevel) : alphaHom γ = alpha γ := rfl

theorem alphaHom_surjective : Function.Surjective alphaHom :=
  fun γ => ⟨alpha γ, alpha_alpha γ⟩

end Alpha

section Comparison

/-- The negative of the comparison map of the coefficients. -/
def planeNeg (n : ℕ) :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  -planeComparison n

theorem planeNeg_apply (v : Binary.HomogeneousPoly (n + 1)) :
    planeNeg n v = -planeComparison n v := rfl

/-- The comparison map of the coefficients is injective. -/
theorem planeComparison_injective (n : ℕ) : Function.Injective (planeComparison n) := by
  have h1 : Function.Injective (binarySwapVar (n + 1)) :=
    Function.LeftInverse.injective (g := ⇑(binarySwapVar (n + 1)))
      (binarySwapVar_involutive (n + 1))
  have h2 : Function.Injective (binarySwap (n + 1)) := binarySwap_injective (n + 1)
  have h3 : Function.Injective (Binary.homogeneousAction (n + 1) (-1)
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ)) :=
    Function.LeftInverse.injective
      (g := ⇑(Binary.homogeneousAction (n + 1) (-1)
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ))) (act_swap_involutive n)
  have h4 : Function.Injective (PhiInv n) :=
    Function.LeftInverse.injective (g := ⇑(Phi n)) (Phi_PhiInv n)
  unfold planeComparison
  simp only [LinearMap.coe_comp]
  exact h1.comp (h2.comp (h3.comp h4))

theorem planeNeg_injective (n : ℕ) : Function.Injective (planeNeg n) := by
  intro x y h
  apply planeComparison_injective n
  exact neg_injective h

theorem planeNeg_surjective (n : ℕ) : Function.Surjective (planeNeg n) :=
  LinearMap.injective_iff_surjective.mp (planeNeg_injective n)

/-- **The negated comparison map intertwines** the coefficients `Sym^{n+1} ⊗ det⁻¹` at `α γ` and
at `γ`. -/
theorem planeNeg_intertwines (hodd : Odd n) (γ : binaryArithmeticLevel)
    (v : Binary.HomogeneousPoly (n + 1)) :
    planeNeg n (levelRep (n + 1) (-1) (alphaHom γ) v) =
      levelRep (n + 1) (-1) γ (planeNeg n v) := by
  rw [planeNeg_apply, planeNeg_apply, alphaHom_apply, planeComparison_intertwines_odd n hodd γ v,
    map_neg]

end Comparison

section Transport

/-- **The transport of the good-plane Levi cohomology** `[e] ↦ [γ ↦ - E (e (α γ))]`. -/
def thetaH1 (hodd : Odd n) :
    CrossedH1 (levelRep (n + 1) (-1)) →ₗ[ℂ] CrossedH1 (levelRep (n + 1) (-1)) :=
  transportH1 (levelRep (n + 1) (-1)) alphaHom (planeNeg n) (planeNeg_intertwines hodd)

theorem thetaH1_injective (hodd : Odd n) : Function.Injective (thetaH1 hodd) :=
  transportH1_injective (levelRep (n + 1) (-1)) alphaHom (planeNeg n) (planeNeg_intertwines hodd)
    (planeNeg_injective n) (planeNeg_surjective n) alphaHom_surjective

/-- The transport of the class of a cocycle is the class of the transported cocycle. -/
theorem transportH1_mkQ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (a : G →* G) (E : V →ₗ[ℂ] V)
    (hE : ∀ γ v, E (ρ (a γ) v) = ρ γ (E v)) (c : crossedCocycles ρ) :
    transportH1 ρ a E hE ((crossedBoundaries ρ).mkQ c) =
      (crossedBoundaries ρ).mkQ (transportCocycles ρ a E hE c) :=
  transportH1_qcls ρ a E hE c

/-- The transport preserves the image of a submodule of cocycles that it preserves (generic). -/
theorem transportH1_map_mem {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (a : G →* G) (E : V →ₗ[ℂ] V)
    (hE : ∀ γ v, E (ρ (a γ) v) = ρ γ (E v)) (P : Submodule ℂ (crossedCocycles ρ))
    (hP : ∀ e ∈ P, transportCocycles ρ a E hE e ∈ P) {x : CrossedH1 ρ}
    (hx : x ∈ P.map (crossedBoundaries ρ).mkQ) :
    transportH1 ρ a E hE x ∈ P.map (crossedBoundaries ρ).mkQ := by
  obtain ⟨e, he, rfl⟩ := Submodule.mem_map.mp hx
  rw [transportH1_mkQ]
  exact Submodule.mem_map_of_mem (hP e he)

/-- The transport sends parabolic classes to parabolic classes. -/
theorem thetaH1_mem (hodd : Odd n) {x : CrossedH1 (levelRep (n + 1) (-1))}
    (hx : x ∈ parabolicCrossedH1 (levelRep (n + 1) (-1))) :
    thetaH1 hodd x ∈ parabolicCrossedH1 (levelRep (n + 1) (-1)) :=
  transportH1_map_mem (levelRep (n + 1) (-1)) alphaHom (planeNeg n) (planeNeg_intertwines hodd)
    (parabolicCrossed (levelRep (n + 1) (-1)))
    (fun e he => parabolic_pullback (levelRep (n + 1) (-1)) (levelRep (n + 1) (-1))
      (planeComparison n) (planeComparison_intertwines_odd n hodd) e he
      (transportCocycles (levelRep (n + 1) (-1)) alphaHom (planeNeg n)
        (planeNeg_intertwines hodd) e) (fun _ => rfl)) hx

/-- **The transport on parabolic classes.** -/
def thetaPar (hodd : Odd n) :
    parabolicCrossedH1 (levelRep (n + 1) (-1)) →ₗ[ℂ]
      parabolicCrossedH1 (levelRep (n + 1) (-1)) :=
  (thetaH1 hodd).restrict fun _ hx => thetaH1_mem hodd hx

theorem thetaPar_coe (hodd : Odd n) (x : parabolicCrossedH1 (levelRep (n + 1) (-1))) :
    ((thetaPar hodd x : parabolicCrossedH1 (levelRep (n + 1) (-1))) :
      CrossedH1 (levelRep (n + 1) (-1))) =
      thetaH1 hodd (x : CrossedH1 (levelRep (n + 1) (-1))) := rfl

/-- **The transport is onto the parabolic classes.** -/
theorem thetaPar_surjective (hodd : Odd n) : Function.Surjective (thetaPar hodd) := by
  have : FiniteDimensional ℂ (CrossedH1 (levelRep (n + 1) (-1))) :=
    TernaryPeriodPolynomials.LevelThree.ParabolicBounds.level_H1_finiteDimensional
      (-1) (Nat.succ_pos n)
  have hfin : Module.Finite ℂ (parabolicCrossedH1 (levelRep (n + 1) (-1))) :=
    FiniteDimensional.finiteDimensional_submodule _
  intro y
  have hsurj := transportH1_surjective_on (levelRep (n + 1) (-1)) alphaHom (planeNeg n)
    (planeNeg_intertwines hodd) (thetaH1_injective hodd)
    (parabolicCrossedH1 (levelRep (n + 1) (-1))) (fun _ hx => thetaH1_mem hodd hx) y.1 y.2
  obtain ⟨x, hx, hxy⟩ := hsurj
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

end Transport

section Pairing

/-- **The Lefschetz pairing of the bad-line Levi with the good-plane Levi in the coordinates of the
reference good plane** (odd `n`): `badGoodPairing` composed with the transport. -/
def badGoodPairingOdd (hodd : Odd n) :
    parabolicCrossedH1 (binaryArithmeticRepresentation n) →ₗ[ℂ]
      parabolicCrossedH1 (levelRep (n + 1) (-1)) →ₗ[ℂ] ℂ :=
  (badGoodPairing hodd).compl₂ (thetaPar hodd)

theorem badGoodPairingOdd_apply (hodd : Odd n)
    (x : parabolicCrossedH1 (binaryArithmeticRepresentation n))
    (y : parabolicCrossedH1 (levelRep (n + 1) (-1))) :
    badGoodPairingOdd hodd x y = badGoodPairing hodd x (thetaPar hodd y) := rfl

/-- **Left nondegeneracy of the transported pairing.** -/
theorem badGoodPairingOdd_left_nondegenerate (hodd : Odd n)
    (x : parabolicCrossedH1 (binaryArithmeticRepresentation n))
    (h : ∀ y : parabolicCrossedH1 (levelRep (n + 1) (-1)), badGoodPairingOdd hodd x y = 0) :
    x = 0 := by
  refine TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree.badLine_left_nondegenerate
    hodd x fun cl' => ?_
  obtain ⟨y, rfl⟩ := thetaPar_surjective hodd cl'
  exact h y

/-- **The Hecke adjointness hypothesis for odd `n`**: for every prime `p ≠ 3`,
`⟨T_p x, y⟩ = p⁻¹ ⟨x, T_p y⟩` for the pairing `badGoodPairingOdd` of the parabolic classes of
`H¹(Γ₁'(3), Sym^{n+1})` with those of `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`. -/
def BadGoodHeckeAdjointOdd (hodd : Odd n) : Prop :=
  LevelThreeParabolicAdjoint n (badGoodPairingOdd hodd) levelThreeKappa

/-- **The transport commutes with the level-three Hecke operators `T_p`** of
`H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` (the Hecke operators commute with the Atkin–Lehner-type
involution `α`). -/
def ThetaHeckeCommute (hodd : Odd n) : Prop :=
  ∀ (p : Nat.Primes) (hp3 : p.val ≠ 3) (y : CrossedH1 (levelRep (n + 1) (-1))),
    thetaH1 hodd (levelHecke (n + 1) (-1) p hp3 y) = levelHecke (n + 1) (-1) p hp3 (thetaH1 hodd y)

/-- **The odd adjointness in the reference coordinates follows from the standard one** and the
commutation of the transport with the Hecke operators. -/
theorem badGoodHeckeAdjointOdd_of_commute (hodd : Odd n) (hcomm : ThetaHeckeCommute hodd)
    (hadj : BadGoodHeckeAdjoint hodd) : BadGoodHeckeAdjointOdd hodd := by
  intro p hp3 x y
  have h1 := hadj p hp3 x (thetaPar hodd y)
  have h2 : thetaPar hodd (parabolicHecke (n + 1) (-1) p hp3 y) =
      parabolicHecke (n + 1) (-1) p hp3 (thetaPar hodd y) := by
    apply Subtype.ext
    rw [thetaPar_coe, parabolicHecke_coe, parabolicHecke_coe, thetaPar_coe]
    exact hcomm p hp3 _
  rw [badGoodPairingOdd_apply, badGoodPairingOdd_apply, h2]
  exact h1

end Pairing

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd

end
