module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.Pairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.PerfectOdd
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.LiteralPairing

@[expose] public section



/-!
# The literal dictionary is an isomorphism onto the parabolic spaces

For `n > 0` the dictionary maps of `Literal.Dict`/`Literal.OddGood` are bijective onto the parabolic cohomology
of the reference faces:
* even `n`: `badLineParabolic : 𝒞(line) ≃ parabolicCrossedH1 (Sym^{n+1})` and
  `goodPlaneParabolic : 𝒞(plane) ≃ parabolicCrossedH1 (Sym^{n+1} ⊗ det⁻¹)` (`*_bijective_even`);
* odd `n`: `(badLineParabolic, goodLineParabolic) : 𝒞(line) ≃ P_bl × P_gl` and
  `(goodPlaneParabolic, badPlaneParabolic) : 𝒞(plane) ≃ P_gp × P_bp` (`lineDictionaryOdd_bijective`,
  `planeDictionaryOdd_bijective`).
Injectivity is obtained from the comparison theorems and the nondegeneracy of the cochain pairing
(a class with zero dictionary image pairs to zero against everything); surjectivity from the exact dimension
count of `PerfectOdd`/`PerfectEven` (`finrank_parabolicBL`, `finrank_parabolicGP`, `parabolicToGoodLine_bijective`).
Together with `Pairing` this says the cochain pairings are, under an explicit isomorphism, the literal per-face
parabolic pairings with the nonzero constants `±(n+1)!/3`, `(n+1)!`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.BoundaryDuality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossedH1 parabolicCrossedH1_eq)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even (badGoodPairingEven)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne (parabolicH1)
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag cuspFlag_good_iff)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

variable {n : ℕ}

theorem finrank_parabolicBL (hn : 0 < n) :
    Module.finrank ℂ (parabolicCrossedH1 (binaryArithmeticRepresentation n)) + 1 = (n + 3) / 3 := by
  have h := TernaryPeriodPolynomials.LevelThree.ExactLevel.finrank_level_parabolicH1_eq
    (m := n + 1) (e := 0) (by omega)
  rw [← parabolicCrossedH1_eq] at h
  have e : (n + 1 + 2) / 3 = (n + 3) / 3 := by omega
  rw [e] at h
  exact h

theorem finrank_parabolicGP (hn : 0 < n) :
    Module.finrank ℂ (parabolicCrossedH1 (levelRep (n + 1) (-1))) + 1 = (n + 3) / 3 := by
  have h := TernaryPeriodPolynomials.LevelThree.ExactLevel.finrank_level_parabolicH1_eq
    (m := n + 1) (e := -1) (by omega)
  rw [← parabolicCrossedH1_eq] at h
  have e : (n + 1 + 2) / 3 = (n + 3) / 3 := by omega
  rw [e] at h
  exact h

theorem badLineParabolic_injective_even (hn : 0 < n) (heven : Even n) :
    Function.Injective (badLineParabolic hn) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro b hb
  refine facePairing_left_nondegenerate n b fun ξ => ?_
  refine (facePairing_even_literal hn heven b ξ).trans ?_
  rw [hb, map_zero, LinearMap.zero_apply, mul_zero]

theorem badLineParabolic_bijective_even (hn : 0 < n) (heven : Even n) :
    Function.Bijective (badLineParabolic hn) := by
  have f1 := finiteDimensional_innerClasses_line_even n hn heven
  have f2 : FiniteDimensional ℂ (parabolicCrossedH1 (binaryArithmeticRepresentation n)) :=
    finiteDimensional_parabolicCrossedH1 (n + 1) (by omega) 0
  have hdim : Module.finrank ℂ (innerClasses n .line) =
      Module.finrank ℂ (parabolicCrossedH1 (binaryArithmeticRepresentation n)) := by
    have a := finrank_innerClasses_line_even n hn heven
    have b := finrank_parabolicBL hn
    omega
  exact ⟨badLineParabolic_injective_even hn heven,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (badLineParabolic_injective_even hn heven)⟩

theorem goodPlaneParabolic_injective_even (hn : 0 < n) (heven : Even n) :
    Function.Injective (goodPlaneParabolic hn) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ξ hξ
  refine facePairing_right_nondegenerate_even n hn heven ξ fun b => ?_
  refine (facePairing_even_literal hn heven b ξ).trans ?_
  rw [hξ, map_zero, mul_zero]

theorem goodPlaneParabolic_bijective_even (hn : 0 < n) (heven : Even n) :
    Function.Bijective (goodPlaneParabolic hn) := by
  have f1 := finiteDimensional_innerClasses_plane_even n hn heven
  have f2 := finiteDimensional_parabolicCrossedH1 (n + 1) (by omega) (-1)
  have hdim : Module.finrank ℂ (innerClasses n .plane) =
      Module.finrank ℂ (parabolicCrossedH1 (levelRep (n + 1) (-1))) := by
    have a := finrank_innerClasses_plane_even n hn heven
    have b := finrank_parabolicGP hn
    omega
  exact ⟨goodPlaneParabolic_injective_even hn heven,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (goodPlaneParabolic_injective_even hn heven)⟩

/-- The odd-`n` line dictionary into the product of the two parabolic spaces. -/
def lineDictionaryOdd (hn : 0 < n) :
    innerClasses n .line →ₗ[ℂ] parabolicCrossedH1 (binaryArithmeticRepresentation n) ×
      parabolicH1 (arithmeticBinaryRep (n + 1) 0) :=
  (badLineParabolic hn).prod (goodLineParabolic hn)

/-- The odd-`n` plane dictionary into the product of the two parabolic spaces. -/
def planeDictionaryOdd (hn : 0 < n) (hodd : Odd n) :
    innerClasses n .plane →ₗ[ℂ] parabolicCrossedH1 (levelRep (n + 1) (-1)) ×
      parabolicH1 (arithmeticBinaryRep (n + 1) (-1)) :=
  (goodPlaneParabolic hn).prod (badPlaneParabolic hn hodd)

/-- The odd-`n` literal expression, as a function of the four dictionary classes. -/
def literalOdd (hodd : Odd n)
    (x : parabolicCrossedH1 (binaryArithmeticRepresentation n))
    (p : parabolicCrossedH1 (levelRep (n + 1) (-1)))
    (y : parabolicH1 (arithmeticBinaryRep (n + 1) 0))
    (q : parabolicH1 (arithmeticBinaryRep (n + 1) (-1))) : ℂ :=
  (-((n + 1).factorial : ℂ) / 3) * LocalPairingCaseL0Odd.badGoodPairingOdd hodd x p +
    ((n + 1).factorial : ℂ) *
      ParabolicDuality.LevelOne.parabolicPairing
        (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd) y q

theorem facePairing_eq_literalOdd (hn : 0 < n) (hodd : Odd n) (b : innerClasses n .line)
    (ξ : innerClasses n .plane) :
    facePairing n b ξ = literalOdd hodd (badLineParabolic hn b) (goodPlaneParabolic hn ξ)
      (goodLineParabolic hn b) (badPlaneParabolic hn hodd ξ) :=
  facePairing_odd_literal hn hodd b ξ

theorem literalOdd_zero_left (hodd : Odd n)
    (p : parabolicCrossedH1 (levelRep (n + 1) (-1))) (q : parabolicH1 (arithmeticBinaryRep (n + 1) (-1))) :
    literalOdd hodd 0 p 0 q = 0 := by
  simp [literalOdd]

theorem literalOdd_zero_right (hodd : Odd n)
    (x : parabolicCrossedH1 (binaryArithmeticRepresentation n))
    (y : parabolicH1 (arithmeticBinaryRep (n + 1) 0)) :
    literalOdd hodd x 0 y 0 = 0 := by
  simp [literalOdd]

theorem lineDictionaryOdd_injective (hn : 0 < n) (hodd : Odd n) :
    Function.Injective (lineDictionaryOdd hn) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro b hb
  have h1 : badLineParabolic hn b = 0 := congrArg Prod.fst hb
  have h2 : goodLineParabolic hn b = 0 := congrArg Prod.snd hb
  refine facePairing_left_nondegenerate n b fun ξ => ?_
  have e2 := congrArg₂ (fun x y => literalOdd hodd x (goodPlaneParabolic hn ξ) y
    (badPlaneParabolic hn hodd ξ)) h1 h2
  exact ((facePairing_eq_literalOdd hn hodd b ξ).trans e2).trans (literalOdd_zero_left hodd _ _)

theorem planeDictionaryOdd_injective (hn : 0 < n) (hodd : Odd n) :
    Function.Injective (planeDictionaryOdd hn hodd) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ξ hξ
  have h1 : goodPlaneParabolic hn ξ = 0 := congrArg Prod.fst hξ
  have h2 : badPlaneParabolic hn hodd ξ = 0 := congrArg Prod.snd hξ
  refine facePairing_right_nondegenerate_odd n hn hodd ξ fun b => ?_
  have e2 := congrArg₂ (fun p q => literalOdd hodd (badLineParabolic hn b) p
    (goodLineParabolic hn b) q) h1 h2
  exact ((facePairing_eq_literalOdd hn hodd b ξ).trans e2).trans (literalOdd_zero_right hodd _ _)

theorem lineDictionaryOdd_bijective (hn : 0 < n) (hodd : Odd n) :
    Function.Bijective (lineDictionaryOdd hn) := by
  have hg : GoodFlag .line goodLineFlag := goodLineFlag_good
  have hb : ¬ GoodFlag .line standardBadLine := Face.standardBadLine_not_good
  have fgl := finiteDimensional_goodLine_locallyInner n hn
  have fbl : FiniteDimensional ℂ (locallyInnerClasses n trivialCharacter .line standardBadLine) :=
    finiteDimensional_badLine_locallyInner n hn
  have f1 := finiteDimensional_innerClasses_line_odd n hn
  have f2 : FiniteDimensional ℂ (parabolicCrossedH1 (binaryArithmeticRepresentation n)) :=
    finiteDimensional_parabolicCrossedH1 (n + 1) (by omega) 0
  have f3 := finiteDimensional_parabolicH1 (n + 1) 0
  let : Module.Free ℂ (locallyInnerClasses n trivialCharacter .line goodLineFlag) :=
    Module.Free.of_divisionRing ℂ _
  let : Module.Free ℂ (locallyInnerClasses n trivialCharacter .line standardBadLine) :=
    Module.Free.of_divisionRing ℂ _
  have eline := (innerClassesEquivLocal n goodLineFlag standardBadLine hg hb).finrank_eq
  rw [Module.finrank_prod] at eline
  have dbl := finrank_badLine_locallyInner n hn
  have dgl := (LinearEquiv.ofBijective (parabolicToGoodLine n hn)
    (parabolicToGoodLine_bijective n hn hodd)).finrank_eq
  have pbl := finrank_parabolicBL hn
  have hdim : Module.finrank ℂ (innerClasses n .line) =
      Module.finrank ℂ (parabolicCrossedH1 (binaryArithmeticRepresentation n) ×
        parabolicH1 (arithmeticBinaryRep (n + 1) 0)) := by
    rw [Module.finrank_prod]
    omega
  exact ⟨lineDictionaryOdd_injective hn hodd,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (lineDictionaryOdd_injective hn hodd)⟩

theorem planeDictionaryOdd_bijective (hn : 0 < n) (hodd : Odd n) :
    Function.Bijective (planeDictionaryOdd hn hodd) := by
  have hgp : GoodFlag .plane (cuspFlag .plane true) := (cuspFlag_good_iff .plane true).mpr rfl
  have hbp : ¬ GoodFlag .plane (cuspFlag .plane false) :=
    fun h => absurd ((cuspFlag_good_iff .plane false).mp h) (by decide)
  have fgp := finiteDimensional_goodPlane_locallyInner n hn
  have fbp := finiteDimensional_badPlane_locallyInner n hn hodd
  have f1 := finiteDimensional_innerClasses_plane_odd n hn hodd
  have f2 : FiniteDimensional ℂ (parabolicCrossedH1 (levelRep (n + 1) (-1))) :=
    finiteDimensional_parabolicCrossedH1 (n + 1) (by omega) (-1)
  have f3 := finiteDimensional_parabolicH1 (n + 1) (-1)
  have free1 : Module.Free ℂ (parabolicCrossedH1 (levelRep (n + 1) (-1))) :=
    Module.Free.of_divisionRing ℂ _
  have free2 : Module.Free ℂ (parabolicH1 (arithmeticBinaryRep (n + 1) (-1))) :=
    Module.Free.of_divisionRing ℂ _
  have free3 : Module.Free ℂ (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true)) :=
    Module.Free.of_divisionRing ℂ _
  have free4 : Module.Free ℂ (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false)) :=
    Module.Free.of_divisionRing ℂ _
  have free5 : Module.Free ℂ (innerClasses n .plane) := Module.Free.of_divisionRing ℂ _
  have eplane :=
    (innerClassesEquivLocal n (cuspFlag .plane true) (cuspFlag .plane false) hgp hbp).finrank_eq
  rw [Module.finrank_prod] at eplane
  have dgp := finrank_goodPlane_locallyInner n hn
  have dbp := (badPlaneLocallyInnerEquivParabolic n hn hodd).finrank_eq
  have pgp := finrank_parabolicGP hn
  have hdim : Module.finrank ℂ (innerClasses n .plane) =
      Module.finrank ℂ (parabolicCrossedH1 (levelRep (n + 1) (-1)) ×
        parabolicH1 (arithmeticBinaryRep (n + 1) (-1))) := by
    rw [Module.finrank_prod]
    omega
  exact ⟨planeDictionaryOdd_injective hn hodd,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (planeDictionaryOdd_injective hn hodd)⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Literal
