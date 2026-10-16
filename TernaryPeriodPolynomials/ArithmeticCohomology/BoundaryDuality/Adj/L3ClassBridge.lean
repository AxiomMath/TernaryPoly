module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Value
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AdjointLevelThreeHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointLevi

@[expose] public section


/-!
# From cocycle-level to class-level Hecke adjointness, generically

The class-level step of the adjointness of the parabolic cup pairing of `Γ₁'(3)` is purely
formal: it does not involve the binary-form representations.  This file proves it for arbitrary
finite-type `ℂ`-representations `ρ`, `ρ'` of `Γ₁'(3)`, a `TwistedPairing` datum, and abstract Hecke
data (functions `H`, `H'` on crossed homomorphisms representing endomorphisms `T`, `T'` of the
parabolic classes), so that no term of the proof mentions `levelRep m e`, the coset index, or the
Hecke cocycle.  The specialisation to `levelRep` is then a single application of the generic
statement with all implicit arguments named.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3ClassBridge

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
open TernaryPeriodPolynomials.BoundaryDuality.AdjL3
open GeneralEisenstein
open TripleModel LinearDuality CocycleBridge EpsilonSplit

section Generic

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ binaryArithmeticLevel V} {ρ' : Representation ℂ binaryArithmeticLevel W}
  {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- **Normalized representatives.**  A parabolic class of `H¹(Γ₁'(3), ρ)` has a representative
which is a parabolic crossed homomorphism vanishing at `L`. -/
theorem exists_normalized_rep (ρ : Representation ℂ binaryArithmeticLevel V)
    (c : parabolicCrossedH1 ρ) :
    ∃ x : crossedCocycles ρ, x ∈ parabolicCrossed ρ ∧ (crossedBoundaries ρ).mkQ x = c.1 ∧
      x.1 (lower 1) = 0 := by
  obtain ⟨x0, hx0, hx0c⟩ := Submodule.mem_map.mp c.2
  obtain ⟨_, u, hu⟩ := (mem_parabolicCrossed_iff ρ x0).mp hx0
  have h0 : (crossedBoundaries ρ).mkQ (crossedBoundary ρ u) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨u, rfl⟩
  have hc : (crossedBoundaries ρ).mkQ (x0 - crossedBoundary ρ u) = c.1 := by
    rw [map_sub, h0, sub_zero, hx0c]
  refine ⟨x0 - crossedBoundary ρ u, mem_parabolicCrossed_of_mem ρ (hc ▸ c.2), hc, ?_⟩
  change x0.1 (lower 1) - (ρ (lower 1) u - u) = 0
  rw [hu, sub_self]

/-- A parabolic crossed homomorphism of `Γ₁'(3)` takes a coboundary value at `T` on `Γ₁(3)`. -/
theorem cobAt_T (z : crossedCocycles ρ) (hz : z ∈ parabolicCrossed ρ) :
    CobAt (ρ.comp core.subtype) (fun n : core => z.1 (core.subtype n)) coreT := by
  obtain ⟨⟨u, hu⟩, -⟩ := (mem_parabolicCrossed_iff ρ z).mp hz
  exact CobAt.of_eq hu

/-- A parabolic crossed homomorphism of `Γ₁'(3)` takes a coboundary value at `L` on `Γ₁(3)`. -/
theorem cobAt_L (z : crossedCocycles ρ) (hz : z ∈ parabolicCrossed ρ) :
    CobAt (ρ.comp core.subtype) (fun n : core => z.1 (core.subtype n)) coreL := by
  obtain ⟨-, ⟨u, hu⟩⟩ := (mem_parabolicCrossed_iff ρ z).mp hz
  exact CobAt.of_eq hu

/-- A parabolic crossed homomorphism of `Γ₁'(3)` takes a coboundary value at `T`. -/
theorem cobAt_upper (z : crossedCocycles ρ) (hz : z ∈ parabolicCrossed ρ) :
    CobAt ρ z.1 (upper 1) := by
  obtain ⟨⟨u, hu⟩, -⟩ := (mem_parabolicCrossed_iff ρ z).mp hz
  exact CobAt.of_eq hu

/-- A parabolic crossed homomorphism of `Γ₁'(3)` has a primitive triple on `Γ₁(3)`. -/
theorem exists_primitive_restr (z : crossedCocycles ρ) (hz : z ∈ parabolicCrossed ρ) :
    ∃ v : V × V × V, IsPrimitive (ρ.comp core.subtype) coreT coreL⁻¹
      (fun n : core => z.1 (core.subtype n)) v :=
  exists_primitive_of_cusps (isCocycle_comp (isCocycle_crossed ρ z) core.subtype)
    (cobAt_T z hz) (cobAt_L z hz)

/-- The value of the parabolic pairing of a class `c₁` against a class `c₂`, computed on
parabolic representatives `z`, `z'` of the classes. -/
theorem pairing_rep (P : TwistedPairing ρ ρ' B) (c₁ : parabolicCrossedH1 ρ)
    (c₂ : parabolicCrossedH1 ρ') (z : crossedCocycles ρ) (z' : crossedCocycles ρ')
    (hz : (crossedBoundaries ρ).mkQ z = c₁.1) (hz' : (crossedBoundaries ρ').mkQ z' = c₂.1)
    (hzP : z ∈ parabolicCrossed ρ) (hzP' : z' ∈ parabolicCrossed ρ') {v : V × V × V}
    (hv : IsPrimitive (ρ.comp core.subtype) coreT coreL⁻¹ (fun n : core => z.1 (core.subtype n))
      v) :
    parabolicPairing P c₁ c₂ =
      cupFormula B (ρ'.comp core.subtype) coreT coreL⁻¹ (fun n : core => z.1 (core.subtype n))
        (fun n : core => z'.1 (core.subtype n)) v := by
  obtain ⟨c₁v, h₁⟩ := c₁
  obtain ⟨c₂v, h₂⟩ := c₂
  have e1 : c₁v = (crossedBoundaries ρ).mkQ z := hz.symm
  have e2 : c₂v = (crossedBoundaries ρ').mkQ z' := hz'.symm
  subst e1 e2
  exact parabolicPairing_apply P z z' hzP hzP' hv

/-- **The generic class-level adjointness.**  Let `T`, `T'` be endomorphisms of the parabolic
classes represented by maps `H`, `H'` on the crossed homomorphisms (`hT`, `hT'`: whenever `x`
represents `c`, `H x` is parabolic and represents `T c`).  If the cup formulas of parabolic
representatives normalized at `L` are related by `κ` (`hcore`, the shape of `CoreAdjoint`), then
`T` and `T'` are `κ`-adjoint for the parabolic pairing. -/
theorem pairing_hecke_generic (P : TwistedPairing ρ ρ' B)
    (H : crossedCocycles ρ → crossedCocycles ρ) (H' : crossedCocycles ρ' → crossedCocycles ρ')
    (T : Module.End ℂ (parabolicCrossedH1 ρ)) (T' : Module.End ℂ (parabolicCrossedH1 ρ'))
    (hT : ∀ (x : crossedCocycles ρ) (c : parabolicCrossedH1 ρ),
      (crossedBoundaries ρ).mkQ x = c.1 →
        H x ∈ parabolicCrossed ρ ∧ (T c).1 = (crossedBoundaries ρ).mkQ (H x))
    (hT' : ∀ (y : crossedCocycles ρ') (c : parabolicCrossedH1 ρ'),
      (crossedBoundaries ρ').mkQ y = c.1 →
        H' y ∈ parabolicCrossed ρ' ∧ (T' c).1 = (crossedBoundaries ρ').mkQ (H' y))
    (κ : ℂ)
    (hcore : ∀ (x : crossedCocycles ρ) (y : crossedCocycles ρ'),
      x ∈ parabolicCrossed ρ → y ∈ parabolicCrossed ρ' → H x ∈ parabolicCrossed ρ →
      H' y ∈ parabolicCrossed ρ' → x.1 (lower 1) = 0 → y.1 (lower 1) = 0 →
      ∀ (v w : V × V × V),
      IsPrimitive (ρ.comp core.subtype) coreT coreL⁻¹
        (fun n : core => (H x).1 (core.subtype n)) v →
      IsPrimitive (ρ.comp core.subtype) coreT coreL⁻¹ (fun n : core => x.1 (core.subtype n)) w →
      cupFormula B (ρ'.comp core.subtype) coreT coreL⁻¹
          (fun n : core => (H x).1 (core.subtype n)) (fun n : core => y.1 (core.subtype n)) v =
        κ * cupFormula B (ρ'.comp core.subtype) coreT coreL⁻¹
          (fun n : core => x.1 (core.subtype n)) (fun n : core => (H' y).1 (core.subtype n)) w)
    (c : parabolicCrossedH1 ρ) (c' : parabolicCrossedH1 ρ') :
    parabolicPairing P (T c) c' = κ * parabolicPairing P c (T' c') := by
  obtain ⟨x, hxP, hxc, hxL⟩ := exists_normalized_rep ρ c
  obtain ⟨y, hyP, hyc, hyL⟩ := exists_normalized_rep ρ' c'
  obtain ⟨hHxP, hTx⟩ := hT x c hxc
  obtain ⟨hHyP, hTy⟩ := hT' y c' hyc
  obtain ⟨v, hv⟩ := exists_primitive_restr (H x) hHxP
  obtain ⟨w, hw⟩ := exists_primitive_restr x hxP
  rw [pairing_rep P (T c) c' (H x) y hTx.symm hyc hHxP hyP hv,
    pairing_rep P c (T' c') x (H' y) hxc hTy.symm hxP hHyP hw]
  exact hcore x y hxP hyP hHxP hHyP hxL hyL v w hv hw

/-- The generic adjointness, as `IsHeckeAdjoint` for the parabolic pairing. -/
theorem isHeckeAdjoint_generic (P : TwistedPairing ρ ρ' B)
    (H : crossedCocycles ρ → crossedCocycles ρ) (H' : crossedCocycles ρ' → crossedCocycles ρ')
    (T : Module.End ℂ (parabolicCrossedH1 ρ)) (T' : Module.End ℂ (parabolicCrossedH1 ρ'))
    (hT : ∀ (x : crossedCocycles ρ) (c : parabolicCrossedH1 ρ),
      (crossedBoundaries ρ).mkQ x = c.1 →
        H x ∈ parabolicCrossed ρ ∧ (T c).1 = (crossedBoundaries ρ).mkQ (H x))
    (hT' : ∀ (y : crossedCocycles ρ') (c : parabolicCrossedH1 ρ'),
      (crossedBoundaries ρ').mkQ y = c.1 →
        H' y ∈ parabolicCrossed ρ' ∧ (T' c).1 = (crossedBoundaries ρ').mkQ (H' y))
    (κ : ℂ)
    (hcore : ∀ (x : crossedCocycles ρ) (y : crossedCocycles ρ'),
      x ∈ parabolicCrossed ρ → y ∈ parabolicCrossed ρ' → H x ∈ parabolicCrossed ρ →
      H' y ∈ parabolicCrossed ρ' → x.1 (lower 1) = 0 → y.1 (lower 1) = 0 →
      ∀ (v w : V × V × V),
      IsPrimitive (ρ.comp core.subtype) coreT coreL⁻¹
        (fun n : core => (H x).1 (core.subtype n)) v →
      IsPrimitive (ρ.comp core.subtype) coreT coreL⁻¹ (fun n : core => x.1 (core.subtype n)) w →
      cupFormula B (ρ'.comp core.subtype) coreT coreL⁻¹
          (fun n : core => (H x).1 (core.subtype n)) (fun n : core => y.1 (core.subtype n)) v =
        κ * cupFormula B (ρ'.comp core.subtype) coreT coreL⁻¹
          (fun n : core => x.1 (core.subtype n)) (fun n : core => (H' y).1 (core.subtype n)) w) :
    HeckeAdjointLevi.IsHeckeAdjoint (parabolicPairing P) T T' κ :=
  fun c c' => pairing_hecke_generic P H H' T T' hT hT' κ hcore c c'

end Generic

section Level

open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (rationalRho
  level_compat crossedHeckeCocycles levelHecke_mk)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep coreRep)

/-- The Hecke cocycle of `Γ₁'(3)` for a crossed homomorphism `x`. -/
abbrev heckeCocycle (m : ℕ) (e : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (x : crossedCocycles (levelRep m e)) : crossedCocycles (levelRep m e) :=
  crossedHeckeCocycles (levelCosets p hp3) (rationalRho m e) (levelRep m e)
    (level_compat m e) levelEmbed_injective x

/-- `coreRep m e` is the restriction of `levelRep m e` to `Γ₁(3)`. -/
theorem coreRep_eq (m : ℕ) (e : ℤ) : coreRep m e = (levelRep m e).comp core.subtype := rfl

/-- The Hecke cocycle of a crossed homomorphism represents the image of its class under
`parabolicHecke`, and is parabolic. -/
theorem parabolicHecke_rep (m : ℕ) (e : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (x : crossedCocycles (levelRep m e)) (c : parabolicCrossedH1 (levelRep m e))
    (hxc : (crossedBoundaries (levelRep m e)).mkQ x = c.1) :
    heckeCocycle m e p hp3 x ∈ parabolicCrossed (levelRep m e) ∧
      (AdjointLevelThree.parabolicHecke m e p hp3 c).1 =
        (crossedBoundaries (levelRep m e)).mkQ (heckeCocycle m e p hp3 x) := by
  have hc : (AdjointLevelThree.parabolicHecke m e p hp3 c).1 =
      (crossedBoundaries (levelRep m e)).mkQ (heckeCocycle m e p hp3 x) := by
    rw [AdjointLevelThree.parabolicHecke_coe, ← hxc]
    exact levelHecke_mk m e p hp3 x
  refine ⟨mem_parabolicCrossed_of_mem _ ?_, hc⟩
  rw [← hc]
  exact (AdjointLevelThree.parabolicHecke m e p hp3 c).2

/-- **`CoreAdjoint` for the restrictions of normalized parabolic representatives**, in the shape
required by `pairing_hecke_generic`. -/
theorem cup_eq_of_core {m : ℕ} {e e' : ℤ} {p : Nat.Primes} {hp3 : p.val ≠ 3} {κ : ℂ}
    (hcore : CoreAdjoint m e e' p hp3 κ) (x : crossedCocycles (levelRep m e))
    (y : crossedCocycles (levelRep m e')) (hxP : x ∈ parabolicCrossed (levelRep m e))
    (hyP : y ∈ parabolicCrossed (levelRep m e'))
    (hHyP : heckeCocycle m e' p hp3 y ∈ parabolicCrossed (levelRep m e'))
    (hxL : x.1 (lower 1) = 0) (hyL : y.1 (lower 1) = 0)
    (v w : Binary.HomogeneousPoly m × Binary.HomogeneousPoly m × Binary.HomogeneousPoly m)
    (hv : IsPrimitive ((levelRep m e).comp core.subtype) coreT coreL⁻¹
      (fun n : core => (heckeCocycle m e p hp3 x).1 (core.subtype n)) v)
    (hw : IsPrimitive ((levelRep m e).comp core.subtype) coreT coreL⁻¹
      (fun n : core => x.1 (core.subtype n)) w) :
    cupFormula (BinaryPairing.binaryPairing m) ((levelRep m e').comp core.subtype) coreT coreL⁻¹
        (fun n : core => (heckeCocycle m e p hp3 x).1 (core.subtype n))
        (fun n : core => y.1 (core.subtype n)) v =
      κ * cupFormula (BinaryPairing.binaryPairing m) ((levelRep m e').comp core.subtype) coreT
        coreL⁻¹ (fun n : core => x.1 (core.subtype n))
        (fun n : core => (heckeCocycle m e' p hp3 y).1 (core.subtype n)) w :=
  hcore ⟨x.1, y.1, x.2, y.2, cobAt_upper x hxP, cobAt_upper y hyP, hxL, hyL⟩ hv hw
    (cobAt_L (heckeCocycle m e' p hp3 y) hHyP)

/-- **The Hecke adjointness of the parabolic cup pairing of `Γ₁'(3)`**, given the adjointness
statement `CoreAdjoint` for the cup formulas of `Γ₁(3)`. -/
theorem parabolicPairing_hecke_of_core' (m : ℕ) (e e' : ℤ) (hodd : Odd (e + e' - (m : ℤ)))
    (p : Nat.Primes) (hp3 : p.val ≠ 3) (κ : ℂ) (hcore : CoreAdjoint m e e' p hp3 κ)
    (c : parabolicCrossedH1 (levelRep m e)) (c' : parabolicCrossedH1 (levelRep m e')) :
    ParabolicDuality.LevelThree.parabolicPairing
        (ParabolicDuality.LevelThree.twistedPairing_levelRep m e e' hodd)
        (AdjointLevelThree.parabolicHecke m e p hp3 c) c' =
      κ * ParabolicDuality.LevelThree.parabolicPairing
        (ParabolicDuality.LevelThree.twistedPairing_levelRep m e e' hodd)
        c (AdjointLevelThree.parabolicHecke m e' p hp3 c') :=
  pairing_hecke_generic (ρ := levelRep m e) (ρ' := levelRep m e')
    (B := BinaryPairing.binaryPairing m) (twistedPairing_levelRep m e e' hodd)
    (heckeCocycle m e p hp3) (heckeCocycle m e' p hp3)
    (AdjointLevelThree.parabolicHecke m e p hp3) (AdjointLevelThree.parabolicHecke m e' p hp3)
    (fun x c hxc => by
      obtain ⟨h1, h2⟩ := parabolicHecke_rep m e p hp3 x c hxc
      exact ⟨h1, h2⟩)
    (fun y c hyc => by
      obtain ⟨h1, h2⟩ := parabolicHecke_rep m e' p hp3 y c hyc
      exact ⟨h1, h2⟩)
    κ
    (fun x y hxP hyP _ hHyP hxL hyL v w hv hw =>
      cup_eq_of_core hcore x y hxP hyP hHyP hxL hyL v w hv hw)
    c c'

/-- **The parabolic Hecke operator `T_p` of `Γ₁'(3)` is `κ`-adjoint for the parabolic cup
pairing**, given the adjointness statement `CoreAdjoint` of `Γ₁(3)`. -/
theorem isHeckeAdjoint_of_core' (m : ℕ) (e e' : ℤ) (hodd : Odd (e + e' - (m : ℤ)))
    (p : Nat.Primes) (hp3 : p.val ≠ 3) (κ : ℂ) (hcore : CoreAdjoint m e e' p hp3 κ) :
    HeckeAdjointLevi.IsHeckeAdjoint
      (ParabolicDuality.LevelThree.parabolicPairing
        (ParabolicDuality.LevelThree.twistedPairing_levelRep m e e' hodd))
      (AdjointLevelThree.parabolicHecke m e p hp3) (AdjointLevelThree.parabolicHecke m e' p hp3)
      κ :=
  fun c c' => parabolicPairing_hecke_of_core' m e e' hodd p hp3 κ hcore c c'

end Level

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3ClassBridge

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossedH1)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)

/-- **The Hecke adjointness of the parabolic cup pairing of `Γ₁'(3)`**, given the adjointness
statement `CoreAdjoint` for the cup formulas of `Γ₁(3)`. -/
theorem parabolicPairing_hecke_of_core' (m : ℕ) (e e' : ℤ) (hodd : Odd (e + e' - (m : ℤ)))
    (p : Nat.Primes) (hp3 : p.val ≠ 3) (κ : ℂ) (hcore : CoreAdjoint m e e' p hp3 κ)
    (c : parabolicCrossedH1 (levelRep m e)) (c' : parabolicCrossedH1 (levelRep m e')) :
    ParabolicDuality.LevelThree.parabolicPairing
        (ParabolicDuality.LevelThree.twistedPairing_levelRep m e e' hodd)
        (AdjointLevelThree.parabolicHecke m e p hp3 c) c' =
      κ * ParabolicDuality.LevelThree.parabolicPairing
        (ParabolicDuality.LevelThree.twistedPairing_levelRep m e e' hodd)
        c (AdjointLevelThree.parabolicHecke m e' p hp3 c') :=
  AdjL3ClassBridge.parabolicPairing_hecke_of_core' m e e' hodd p hp3 κ hcore c c'

/-- **The parabolic Hecke operator `T_p` of `Γ₁'(3)` is `κ`-adjoint for the parabolic cup
pairing**, given the adjointness statement `CoreAdjoint` of `Γ₁(3)`. -/
theorem isHeckeAdjoint_of_core' (m : ℕ) (e e' : ℤ) (hodd : Odd (e + e' - (m : ℤ)))
    (p : Nat.Primes) (hp3 : p.val ≠ 3) (κ : ℂ) (hcore : CoreAdjoint m e e' p hp3 κ) :
    HeckeAdjointLevi.IsHeckeAdjoint
      (ParabolicDuality.LevelThree.parabolicPairing
        (ParabolicDuality.LevelThree.twistedPairing_levelRep m e e' hodd))
      (AdjointLevelThree.parabolicHecke m e p hp3) (AdjointLevelThree.parabolicHecke m e' p hp3)
      κ :=
  AdjL3ClassBridge.isHeckeAdjoint_of_core' m e e' hodd p hp3 κ hcore

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
