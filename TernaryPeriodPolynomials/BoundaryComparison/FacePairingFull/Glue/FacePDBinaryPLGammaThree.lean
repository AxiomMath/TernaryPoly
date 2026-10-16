module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDBinaryPLElliptic
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDBinaryPLContragredient
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelThree

@[expose] public section


/-!
# The Poincare-Lefschetz instance for the binary Levi `Γ₁'(3)`

Formalized by Claude Sonnet 5.5.

`Γ₁'(3) = Γ₁(3) ⋊ ⟨ε⟩`, `Γ₁(3) = ⟨T, L⟩ ≅ ℤ * ℤ/3`; the three special elements are `a = T`, `g₂ = L⁻¹`, `g₃ = (T L⁻¹)⁻¹` (two cusps and
one cone point of order three).  For a perfect pairing `B` of two finite-dimensional representations of `Γ₁'(3)` which is
`Γ₁(3)`-invariant and `ε`-odd (`LevelThree.TwistedPairing`: the cup product of two classes of an oriented-orbifold group, the
orientation character of the reflection `ε` being the sign `-1`), `setup P` is a `Setup`:

* `H¹_c(Γ₁'(3), ρ)` is the cone of the restriction to the cyclic subgroups `⟨T⟩`, `⟨L⟩` (the elliptic slot is divided out),
  `j` forgets the primitives, `range_j` is the space of parabolic classes (`LevelThree.parabolicCrossedH1`);
* `imagePairing_eq`: the Lefschetz pairing of the images is the library's parabolic cup pairing (`LevelThree.parabolicPairing`);
* `imagePairing_left_nondegenerate`, `imagePairing_right_nondegenerate`: it is nondegenerate on both sides, the right-hand side
  by the left nondegeneracy for the dual system (`twistedFlip`), not by a dimension count.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL.GammaThree

open TernaryPeriodPolynomials.BoundaryDuality
open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators GammaOneThree
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL

section Model

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- **The crossed-homomorphism model** of `H¹(G, ρ)`: the crossed homomorphisms modulo coboundaries. -/
def crossedModel (ρ : Representation ℂ G V) : Model ρ (crossedCocycles ρ) (CrossedH1 ρ) where
  c := (crossedCocycles ρ).subtype
  f := (crossedBoundaries ρ).mkQ
  isCocycle := fun y => y.2
  inj := Subtype.val_injective
  surj := fun Z hZ => ⟨⟨Z, hZ⟩, rfl⟩
  ker := fun y => crossed_mkQ_eq_zero_iff ρ y
  fsurj := Submodule.mkQ_surjective _

end Model

section Setup

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ binaryArithmeticLevel V} {ρ' : Representation ℂ binaryArithmeticLevel W}
  {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- The ignored subspace: the fixed vectors of the cone point `(T L⁻¹)⁻¹`, the only special element of finite order. -/
def ellIgnored (ρ : Representation ℂ binaryArithmeticLevel V) : Submodule ℂ (V × V × V) :=
  (⊥ : Submodule ℂ V).prod ((⊥ : Submodule ℂ V).prod
    (fixedBy (ρ.comp core.subtype) (coreT * coreL⁻¹)⁻¹))

theorem ignoredFor_ell (hinv : ∀ n v w, B (ρ (core.subtype n) v) (ρ' (core.subtype n) w) = B v w) :
    IgnoredFor core.subtype ρ' B coreT coreL⁻¹ (ellIgnored ρ) := by
  refine ignoredFor_prod core.subtype ρ' B coreT coreL⁻¹ ⊥ ⊥ _ (fun Z' _ f hf => slot_bot B _ f hf)
    (fun Z' _ f hf => slot_bot B _ f hf) (fun Z' hZ' f hf => ?_)
  exact slot_torsion core.subtype ρ ρ' B hinv (coreT * coreL⁻¹)⁻¹ (k := 3) (by norm_num)
    (by rw [inv_pow, core_elliptic_cube, inv_one]) hZ' f hf

/-- **The Poincare-Lefschetz setup for `Γ₁'(3)`.** -/
def setup (P : TwistedPairing ρ ρ' B) :
    Setup core.subtype ρ ρ' B coreT coreL⁻¹ (crossedCocycles ρ) (CrossedH1 ρ) (crossedCocycles ρ')
      (CrossedH1 ρ') where
  hinv := fun n v w => P.special n v w
  M := crossedModel ρ
  M' := crossedModel ρ'
  F := ellIgnored ρ
  F' := ellIgnored ρ'
  hF := ignoredFor_ell (fun n v w => P.special n v w)
  hF' := ignoredFor_ell (ρ := ρ') (ρ' := ρ) (B := B.flip) (fun n w v => P.special n v w)

/-- The twisted pairing for the dual system. -/
theorem twistedFlip (P : TwistedPairing ρ ρ' B) : TwistedPairing ρ' ρ B.flip where
  left := fun w h => P.right w (fun v => h v)
  right := fun v h => P.left v (fun w => h w)
  special := fun g w v => P.special g v w
  odd := fun w v => P.odd v w

/-- **The image of `j : H¹_c(Γ₁'(3), ρ) → H¹(Γ₁'(3), ρ)` is the space of parabolic classes.** -/
theorem range_j (P : TwistedPairing ρ ρ' B) :
    LinearMap.range (setup P).j = parabolicCrossedH1 ρ :=
  (setup P).range_j

theorem range_j' (P : TwistedPairing ρ ρ' B) :
    LinearMap.range (setup P).j' = parabolicCrossedH1 ρ' :=
  (setup P).range_j'

/-- **The Lefschetz pairing of the images of compactly supported cohomology is the library's parabolic cup pairing.** -/
theorem imagePairing_eq (P : TwistedPairing ρ ρ' B) (x : LinearMap.range (setup P).j)
    (y : LinearMap.range (setup P).j') :
    (setup P).imagePairing x y =
      parabolicPairing P ((setup P).toParabolic x) ((setup P).toParabolic' y) :=
  (setup P).imagePairing_eq_parabolicPairing x y

/-- The image of `j` as the parabolic classes of the library. -/
def toParabolic (P : TwistedPairing ρ ρ' B) : LinearMap.range (setup P).j ≃ₗ[ℂ] parabolicCrossedH1 ρ :=
  LinearEquiv.ofEq _ _ (range_j P)

/-- The image of `j'` as the parabolic classes of the dual system. -/
def toParabolic' (P : TwistedPairing ρ ρ' B) : LinearMap.range (setup P).j' ≃ₗ[ℂ] parabolicCrossedH1 ρ' :=
  LinearEquiv.ofEq _ _ (range_j' P)

/-- **The Lefschetz pairing of the images is the library's parabolic cup pairing**, in terms of the parabolic classes
`parabolicCrossedH1`. -/
theorem imagePairing_eq' (P : TwistedPairing ρ ρ' B) (x : LinearMap.range (setup P).j)
    (y : LinearMap.range (setup P).j') :
    (setup P).imagePairing x y = parabolicPairing P (toParabolic P x) (toParabolic' P y) :=
  imagePairing_eq P x y

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- **Parabolic Poincare duality of `Γ₁'(3)` at the cochain level** (the library's left nondegeneracy). -/
theorem cochainND (P : TwistedPairing ρ ρ' B) :
    CochainNondegenerate core.subtype ρ ρ' B coreT coreL⁻¹ :=
  cochainNondegenerate_of_nd indexTwo ρ ρ' B coreT coreL⁻¹ (fun n v w => P.special n v w) (nlevelND P)

/-- **Left nondegeneracy** of the Lefschetz pairing of the images. -/
theorem imagePairing_left_nondegenerate (P : TwistedPairing ρ ρ' B) (x : LinearMap.range (setup P).j)
    (h : ∀ y : LinearMap.range (setup P).j', (setup P).imagePairing x y = 0) : x = 0 :=
  (setup P).imagePairing_left_nondegenerate P.left P.right (cochainND P) x h

/-- **Right nondegeneracy** of the Lefschetz pairing of the images. -/
theorem imagePairing_right_nondegenerate (P : TwistedPairing ρ ρ' B) (y : LinearMap.range (setup P).j')
    (h : ∀ x : LinearMap.range (setup P).j, (setup P).imagePairing x y = 0) : y = 0 :=
  (setup P).imagePairing_right_nondegenerate P.left P.right (cochainND (twistedFlip P)) y h

end Setup

section Orientation

open Matrix

/-- `ε` has determinant `-1`. -/
theorem det_reflection : GeneralLinearGroup.det (reflection : binaryArithmeticLevel).val = -1 := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, reflection, Matrix.det_fin_two_of]

/-- **The orientation character of `Γ₁'(3) ⊃ Γ₁(3)` is the determinant.** -/
theorem orientationSign_eq_det (g : binaryArithmeticLevel) :
    orientationSign core.subtype g = (((GeneralLinearGroup.det g.val : ℤˣ) : ℤ) : ℂ) := by
  rcases indexTwo.cover g with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · rw [orientationSign_ι]
    have h : GeneralLinearGroup.det (core.subtype n : binaryArithmeticLevel).val = 1 := det_core n
    rw [h]
    simp
  · rw [orientationSign_ιε indexTwo]
    have h : GeneralLinearGroup.det (core.subtype n * reflection : binaryArithmeticLevel).val = -1 := by
      rw [Subgroup.coe_mul, map_mul, det_reflection]
      have h1 : GeneralLinearGroup.det (core.subtype n : binaryArithmeticLevel).val = 1 := det_core n
      rw [h1]
      simp
    rw [h]
    simp

end Orientation

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL.GammaThree
