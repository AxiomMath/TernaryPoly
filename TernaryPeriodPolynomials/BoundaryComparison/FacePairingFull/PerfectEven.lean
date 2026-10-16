module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.RightNondegenerate
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.GoodPlaneParabolic
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.BadPlaneParabolic
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.BadLineParabolic
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineVacuityEven

@[expose] public section



/-!
# The face pairing is perfect for even `n` (both kernels)

For even `n > 0` the line inner space is the bad-line cuspidal group alone (the good-line group
vanishes by `cuspRes_line_false_ne_zero_of_even`) and the plane inner space is the good-plane
cuspidal group alone (the identity-plane cohomology vanishes). Both have the exact dimension
`⌊(n + 3)/3⌋ - 1` (`finrank_badLine_locallyInner`, `finrank_goodPlane_locallyInner`), so the zero left
kernel (`facePairing_left_nondegenerate`) gives the zero right kernel
(`facePairing_right_nondegenerate_even`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face
open TernaryPeriodPolynomials.Argument.FacePairing

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- For even `n` there are no locally inner classes at the good line. -/
theorem goodLine_locallyInner_eq_bot_of_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    locallyInnerClasses n trivialCharacter .line (cuspFlag .line true) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨b, hb⟩ := innerToLocal_surjective n (cuspFlag .line true) (cuspFlag .line false)
    ((cuspFlag_good_iff .line true).mpr rfl)
    (fun h => absurd ((cuspFlag_good_iff .line false).mp h) (by decide)) (⟨x, hx⟩, 0)
  have h1 : cuspRes n trivialCharacter .line true b.val = x := congrArg (fun p => p.1.val) hb
  have h0 : cuspRes n trivialCharacter .line false b.val = 0 := congrArg (fun p => p.2.val) hb
  have hb0 : b.val = 0 := by
    by_contra hne
    exact cuspRes_line_false_ne_zero_of_even hn heven b.property hne h0
  rw [← h1, hb0, map_zero]

theorem finiteDimensional_badLine_locallyInner (n : ℕ) (hn : 0 < n) :
    FiniteDimensional ℂ (locallyInnerClasses n trivialCharacter .line (cuspFlag .line false)) := by
  have h0 : FiniteDimensional ℂ (CrossedH1 (binaryArithmeticRepresentation n)) :=
    TernaryPeriodPolynomials.LevelThree.ParabolicBounds.level_H1_finiteDimensional
      (m := n + 1) 0 (by omega)
  have h1 : Module.Finite ℂ
      (TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree.parabolicCrossedH1
        (binaryArithmeticRepresentation n)) :=
    FiniteDimensional.finiteDimensional_submodule _
  exact Module.Finite.equiv (badLineLocallyInnerEquivParabolic n hn).symm

theorem finiteDimensional_goodPlane_locallyInner (n : ℕ) (hn : 0 < n) :
    FiniteDimensional ℂ (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true)) := by
  have h0 := TernaryPeriodPolynomials.LevelThree.ParabolicBounds.level_H1_finiteDimensional
    (m := n + 1) (-1) (by omega)
  have h1 : Module.Finite ℂ (TernaryPeriodPolynomials.LevelThree.TwoGenerator.parabolicH1
      (TernaryPeriodPolynomials.LevelThree.ParabolicBounds.levelRep (n + 1) (-1))
      (upper 1) (lower 1)) :=
    Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  exact Module.Finite.equiv (goodPlaneLocallyInnerEquivParabolic n hn).symm

/-- For even `n`, the line inner space is the bad-line cuspidal group. -/
theorem finrank_innerClasses_line_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    Module.finrank ℂ (innerClasses n .line) + 1 = (n + 3) / 3 := by
  have h1 : GoodFlag .line (cuspFlag .line true) := (cuspFlag_good_iff .line true).mpr rfl
  have h2 : ¬ GoodFlag .line (cuspFlag .line false) :=
    fun h => absurd ((cuspFlag_good_iff .line false).mp h) (by decide)
  let e := innerClassesEquivLocal n (cuspFlag .line true) (cuspFlag .line false) h1 h2
  have freeGood : Module.Free ℂ (locallyInnerClasses n trivialCharacter .line (cuspFlag .line true)) :=
    Module.Free.of_divisionRing ℂ _
  have freeBad : Module.Free ℂ (locallyInnerClasses n trivialCharacter .line (cuspFlag .line false)) :=
    Module.Free.of_divisionRing ℂ _
  have := finiteDimensional_badLine_locallyInner n hn
  have : Subsingleton (locallyInnerClasses n trivialCharacter .line (cuspFlag .line true)) :=
    (Submodule.subsingleton_iff_eq_bot).mpr (goodLine_locallyInner_eq_bot_of_even n hn heven)
  have hbad : Module.finrank ℂ (locallyInnerClasses n trivialCharacter .line (cuspFlag .line false)) + 1
      = (n + 3) / 3 := finrank_badLine_locallyInner n hn
  rw [e.finrank_eq, Module.finrank_prod, Module.finrank_zero_of_subsingleton, zero_add]
  exact hbad

/-- For even `n`, the plane inner space is the good-plane cuspidal group. -/
theorem finrank_innerClasses_plane_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    Module.finrank ℂ (innerClasses n .plane) + 1 = (n + 3) / 3 := by
  have h1 : GoodFlag .plane (cuspFlag .plane true) := (cuspFlag_good_iff .plane true).mpr rfl
  have h2 : ¬ GoodFlag .plane (cuspFlag .plane false) :=
    fun h => absurd ((cuspFlag_good_iff .plane false).mp h) (by decide)
  let e := innerClassesEquivLocal n (cuspFlag .plane true) (cuspFlag .plane false) h1 h2
  have freeGood : Module.Free ℂ (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true)) :=
    Module.Free.of_divisionRing ℂ _
  have freeBad : Module.Free ℂ (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false)) :=
    Module.Free.of_divisionRing ℂ _
  have := finiteDimensional_goodPlane_locallyInner n hn
  have : Subsingleton (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false)) :=
    (Submodule.subsingleton_iff_eq_bot).mpr (badPlane_locallyInner_eq_bot_of_even n hn heven)
  have hgood := finrank_goodPlane_locallyInner n hn
  rw [e.finrank_eq, Module.finrank_prod, Module.finrank_zero_of_subsingleton (R := ℂ)
    (M := locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false)), add_zero]
  exact hgood

theorem finiteDimensional_innerClasses_line_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    FiniteDimensional ℂ (innerClasses n .line) := by
  have h1 : GoodFlag .line (cuspFlag .line true) := (cuspFlag_good_iff .line true).mpr rfl
  have h2 : ¬ GoodFlag .line (cuspFlag .line false) :=
    fun h => absurd ((cuspFlag_good_iff .line false).mp h) (by decide)
  have := finiteDimensional_badLine_locallyInner n hn
  have : Subsingleton (locallyInnerClasses n trivialCharacter .line (cuspFlag .line true)) :=
    (Submodule.subsingleton_iff_eq_bot).mpr (goodLine_locallyInner_eq_bot_of_even n hn heven)
  exact Module.Finite.equiv
    (innerClassesEquivLocal n (cuspFlag .line true) (cuspFlag .line false) h1 h2).symm

theorem finiteDimensional_innerClasses_plane_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    FiniteDimensional ℂ (innerClasses n .plane) := by
  have h1 : GoodFlag .plane (cuspFlag .plane true) := (cuspFlag_good_iff .plane true).mpr rfl
  have h2 : ¬ GoodFlag .plane (cuspFlag .plane false) :=
    fun h => absurd ((cuspFlag_good_iff .plane false).mp h) (by decide)
  have := finiteDimensional_goodPlane_locallyInner n hn
  have : Subsingleton (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false)) :=
    (Submodule.subsingleton_iff_eq_bot).mpr (badPlane_locallyInner_eq_bot_of_even n hn heven)
  exact Module.Finite.equiv
    (innerClassesEquivLocal n (cuspFlag .plane true) (cuspFlag .plane false) h1 h2).symm

/-- **The face pairing has zero right kernel for even `n`.** -/
theorem facePairing_right_nondegenerate_even (n : ℕ) (hn : 0 < n) (heven : Even n)
    (ξ : innerClasses n .plane) (h : ∀ b : innerClasses n .line, facePairing n b ξ = 0) :
    ξ = 0 := by
  have := finiteDimensional_innerClasses_line_even n hn heven
  have := finiteDimensional_innerClasses_plane_even n hn heven
  have hdim : Module.finrank ℂ (innerClasses n .line) = Module.finrank ℂ (innerClasses n .plane) := by
    have a := finrank_innerClasses_line_even n hn heven
    have b := finrank_innerClasses_plane_even n hn heven
    omega
  exact facePairing_perfect_of_finrank_eq n hdim ξ h

end TernaryPeriodPolynomials.Argument.FacePairingFull
