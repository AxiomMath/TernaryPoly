module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDBinaryPLGammaThree
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDBinaryPLGLTwo
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDBinaryPLContragredient
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.LiteralPairing

@[expose] public section


/-!
# The literal binary-Levi pairings of `eq:facepair` as Poincare-Lefschetz pairings of the images of compactly supported cohomology

Formalized by Claude Sonnet 5.5.

For the reference faces the binary Levi coefficient systems are `Sym^{n+1} ⊗ det^e` of `GL₂(ℤ)` (good line, identity plane, `n` odd) and
`Sym^{n+1} ⊗ det^e` of `Γ₁'(3)` (bad line, good plane), paired by the classical apolar pairing `binaryPairing (n+1)`
(`LiteralPairing.levelOne_pairing_perfect`, `levelThree_pairing_perfect_odd`).  Here:

* `levelOne_setup`, `levelThree_setup`: the Poincare-Lefschetz setup (compactly supported cohomology `H¹_c`, `j`, `j'`, `PD`, `PD'`) of
  these coefficient systems;
* `levelOne_imagePairing_eq`, `levelThree_imagePairing_eq`: the Lefschetz pairing of the images `Im j × Im j'` is the library's parabolic cup
  pairing of `LiteralPairing` (the pairing of the faces);
* `levelOne_imagePairing_nondegenerate`, `levelThree_imagePairing_nondegenerate`: it is nondegenerate in both arguments (the
  annihilator of either image is the kernel of the transpose map), from the left parabolic Poincare duality of the library applied to the
  system and to its dual;
* `levelOne_dual_is_contragredient`: the dual system `Sym^{n+1} ⊗ det^{-1}` is the contragredient of `Sym^{n+1}` twisted by the
  determinant (the orientation sign), `Φ (ρ' g w) = det(g) · Φ(w) ∘ ρ(g⁻¹)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL.Literal

open CategoryTheory
open TernaryPeriodPolynomials.BoundaryDuality
open TripleModel LinearDuality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL

section LevelOne

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne

theorem hodd_twist (n : ℕ) (hodd : Odd n) : Odd ((0 : ℤ) + (-1) - ((n + 1 : ℕ) : ℤ)) := by
  obtain ⟨k, hk⟩ := hodd
  exact ⟨-(k : ℤ) - 2, by push_cast; omega⟩

/-- The twisted pairing of the good line (`Sym^{n+1}`) with the identity plane (`Sym^{n+1} ⊗ det⁻¹`). -/
theorem levelOne_twisted (n : ℕ) (hodd : Odd n) :
    TwistedPairing (arithmeticBinaryRep (n + 1) 0) (arithmeticBinaryRep (n + 1) (-1))
      (BinaryPairing.binaryPairing (n + 1)) :=
  twistedPairing_arithmeticBinaryRep (n + 1) 0 (-1) hodd.add_one (hodd_twist n hodd)

theorem levelOne_central (n : ℕ) (hodd : Odd n) (v : arithmeticBinaryRep (n + 1) 0) :
    (arithmeticBinaryRep (n + 1) 0).ρ (toGL (ModularGroup.S * ModularGroup.S)) v = v :=
  arithmeticBinaryRep_central (n + 1) hodd.add_one 0 v

/-- **The Poincare-Lefschetz setup of the good line / identity plane (level one, `n` odd).** -/
def levelOne_setup (n : ℕ) (hodd : Odd n) :=
  GLTwo.setup (levelOne_twisted n hodd)

/-- **The Lefschetz pairing of the images is the literal parabolic cup pairing of the faces, level one.** -/
theorem levelOne_imagePairing_eq (n : ℕ) (hodd : Odd n) (x : LinearMap.range (levelOne_setup n hodd).j)
    (y : LinearMap.range (levelOne_setup n hodd).j') :
    (levelOne_setup n hodd).imagePairing x y =
      parabolicPairing (levelOne_twisted n hodd)
        ((levelOne_setup n hodd).toParabolic x) ((levelOne_setup n hodd).toParabolic' y) :=
  GLTwo.imagePairing_eq _ x y

/-- **Level one: the pairing between the images of compactly supported cohomology is nondegenerate on both sides.** -/
theorem levelOne_imagePairing_nondegenerate (n : ℕ) (hodd : Odd n) :
    (∀ x : LinearMap.range (levelOne_setup n hodd).j,
      (∀ y, (levelOne_setup n hodd).imagePairing x y = 0) → x = 0) ∧
    ∀ y : LinearMap.range (levelOne_setup n hodd).j',
      (∀ x, (levelOne_setup n hodd).imagePairing x y = 0) → y = 0 :=
  ⟨fun x h => GLTwo.imagePairing_left_nondegenerate _ x h,
    fun y h => GLTwo.imagePairing_right_nondegenerate _ (levelOne_central n hodd) y h⟩

/-- **The dual system of the good line / identity plane is the contragredient twisted by the determinant**: the transpose of
`ρ'(g)` for the perfect pairing `binaryPairing (n+1)` is `det(g) · ρ(g⁻¹)`, i.e. `⟨v, ρ'(g) w⟩ = det(g) ⟨ρ(g⁻¹) v, w⟩` for all
`g ∈ GL₂(ℤ)`; with the perfectness of the pairing (`(levelOne_twisted n hodd).left/right`, and `pairingDual` for the isomorphism
`Sym^{n+1} ⊗ det⁻¹ ≃ (Sym^{n+1})^∨`) this says `ρ' ≅ ρ^∨ ⊗ det`. -/
theorem levelOne_dual_is_contragredient (n : ℕ) (hodd : Odd n) (g : GL2Z)
    (v : arithmeticBinaryRep (n + 1) 0) (w : arithmeticBinaryRep (n + 1) (-1)) :
    BinaryPairing.binaryPairing (n + 1) v ((arithmeticBinaryRep (n + 1) (-1)).ρ g w) =
      ((g.val.det : ℤ) : ℂ) *
        BinaryPairing.binaryPairing (n + 1) ((arithmeticBinaryRep (n + 1) 0).ρ g⁻¹ v) w := by
  have h := pairing_orientation indexTwo (fun m v w => (levelOne_twisted n hodd).special m v w)
    (levelOne_twisted n hodd).odd g ((arithmeticBinaryRep (n + 1) 0).ρ g⁻¹ v) w
  rw [GLTwo.orientationSign_eq_det] at h
  have e : (arithmeticBinaryRep (n + 1) 0).ρ g ((arithmeticBinaryRep (n + 1) 0).ρ g⁻¹ v) = v :=
    rep_apply_inv (arithmeticBinaryRep (n + 1) 0).ρ g v
  exact (congrArg (fun x => BinaryPairing.binaryPairing (n + 1) x
    ((arithmeticBinaryRep (n + 1) (-1)).ρ g w)) e.symm).trans h

end LevelOne

section LevelThree

open Matrix
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic Helpers

theorem levelThree_twisted (n : ℕ) (hodd : Odd n) :
    TwistedPairing (levelRep (n + 1) 0) (levelRep (n + 1) (-1)) (BinaryPairing.binaryPairing (n + 1)) :=
  twistedPairing_levelRep (n + 1) 0 (-1) (by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨-(k : ℤ) - 2, by push_cast; omega⟩)

/-- **The Poincare-Lefschetz setup of the bad line / good plane (level three, `n` odd).** -/
def levelThree_setup (n : ℕ) (hodd : Odd n) :=
  GammaThree.setup (levelThree_twisted n hodd)

/-- **The Lefschetz pairing of the images is the literal parabolic cup pairing of the faces, level three.** -/
theorem levelThree_imagePairing_eq (n : ℕ) (hodd : Odd n) (x : LinearMap.range (levelThree_setup n hodd).j)
    (y : LinearMap.range (levelThree_setup n hodd).j') :
    (levelThree_setup n hodd).imagePairing x y =
      parabolicPairing (levelThree_twisted n hodd)
        ((levelThree_setup n hodd).toParabolic x) ((levelThree_setup n hodd).toParabolic' y) :=
  GammaThree.imagePairing_eq _ x y

/-- **Level three: the pairing between the images of compactly supported cohomology is nondegenerate on both sides.** -/
theorem levelThree_imagePairing_nondegenerate (n : ℕ) (hodd : Odd n) :
    (∀ x : LinearMap.range (levelThree_setup n hodd).j,
      (∀ y, (levelThree_setup n hodd).imagePairing x y = 0) → x = 0) ∧
    ∀ y : LinearMap.range (levelThree_setup n hodd).j',
      (∀ x, (levelThree_setup n hodd).imagePairing x y = 0) → y = 0 :=
  ⟨fun x h => GammaThree.imagePairing_left_nondegenerate _ x h,
    fun y h => GammaThree.imagePairing_right_nondegenerate _ y h⟩

/-- **The dual system of the bad line / good plane is the contragredient twisted by the determinant**: the transpose of `ρ'(g)` for the
perfect pairing `binaryPairing (n+1)` is `det(g) · ρ(g⁻¹)` for all `g ∈ Γ₁'(3)`. -/
theorem levelThree_dual_is_contragredient (n : ℕ) (hodd : Odd n) (g : binaryArithmeticLevel)
    (v : GeneralEisenstein.Binary.HomogeneousPoly (n + 1)) (w : GeneralEisenstein.Binary.HomogeneousPoly (n + 1)) :
    BinaryPairing.binaryPairing (n + 1) v (levelRep (n + 1) (-1) g w) =
      (((GeneralLinearGroup.det g.val : ℤˣ) : ℤ) : ℂ) *
        BinaryPairing.binaryPairing (n + 1) (levelRep (n + 1) 0 g⁻¹ v) w := by
  have h := pairing_orientation indexTwo
    (fun m v w => (levelThree_twisted n hodd).special m v w) (levelThree_twisted n hodd).odd g
    (levelRep (n + 1) 0 g⁻¹ v) w
  rw [GammaThree.orientationSign_eq_det] at h
  have e : levelRep (n + 1) 0 g (levelRep (n + 1) 0 g⁻¹ v) = v :=
    rep_apply_inv (levelRep (n + 1) 0) g v
  exact (congrArg (fun x => BinaryPairing.binaryPairing (n + 1) x (levelRep (n + 1) (-1) g w))
    e.symm).trans h

end LevelThree

section LevelThreeEven

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic Helpers
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

/-- The twisted pairing of the bad-line coefficients `Sym^{n+1}` with themselves (`n` even). -/
theorem levelThree_even_twisted (n : ℕ) (heven : Even n) :
    TwistedPairing (binaryArithmeticRepresentation n) (binaryArithmeticRepresentation n)
      (BinaryPairing.binaryPairing (n + 1)) :=
  twistedPairing_binaryArithmeticRepresentation n heven

/-- **The Poincare-Lefschetz setup of the bad line (level three, `n` even).** -/
abbrev levelThree_even_setup (n : ℕ) (heven : Even n) :=
  GammaThree.setup (levelThree_even_twisted n heven)

/-- **The even bad-line / good-plane pairing is the Lefschetz pairing of the images composed with the transport of the good-plane
coefficients**: `badGoodPairingEven x y` is the pairing of the images of compactly supported cohomology (with the true `j`) of the
bad-line classes `x` and of the transported plane classes `T y` (`planeTransportPar`, the transport along the cusp-exchanging involution
and the coefficient comparison).  The transport itself is not re-derived here. -/
theorem badGoodPairingEven_eq_imagePairing (n : ℕ) (heven : Even n)
    (x : parabolicCrossedH1 (binaryArithmeticRepresentation n))
    (y : parabolicCrossedH1 (levelRep (n + 1) (-1))) :
    badGoodPairingEven heven x y =
      (levelThree_even_setup n heven).imagePairing
        ((GammaThree.toParabolic (levelThree_even_twisted n heven)).symm x)
        ((GammaThree.toParabolic' (levelThree_even_twisted n heven)).symm (planeTransportPar heven y)) := by
  have h := GammaThree.imagePairing_eq' (levelThree_even_twisted n heven)
    ((GammaThree.toParabolic (levelThree_even_twisted n heven)).symm x)
    ((GammaThree.toParabolic' (levelThree_even_twisted n heven)).symm (planeTransportPar heven y))
  have e1 := (GammaThree.toParabolic (levelThree_even_twisted n heven)).apply_symm_apply x
  have e2 := (GammaThree.toParabolic' (levelThree_even_twisted n heven)).apply_symm_apply
    (planeTransportPar heven y)
  have e := congrArg₂ (fun a b => parabolicPairing (levelThree_even_twisted n heven) a b)
    e1.symm e2.symm
  exact (badGoodPairingEven_apply heven x y).trans (e.trans h.symm)

end LevelThreeEven

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL.Literal
