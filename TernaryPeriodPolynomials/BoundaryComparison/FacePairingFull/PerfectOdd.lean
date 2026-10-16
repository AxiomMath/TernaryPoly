module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.PerfectEven
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.GoodLineLowerBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelOne

@[expose] public section



/-!
# The face pairing is perfect for odd `n` (both kernels)

For odd `n > 0` the line inner space is `𝒞_good-line ⊕ 𝒞_bad-line` and the plane inner space
`𝒞_good-plane ⊕ 𝒞_identity-plane`. The two level-three blocks have equal exact dimension
(`finrank_badLine_locallyInner`, `finrank_goodPlane_locallyInner`). At level one the identity plane
is `parabolicH1 (Sym^{n+1} ⊗ det⁻¹)` (`badPlaneLocallyInnerEquivParabolic`), the good line contains a
copy of `parabolicH1 (Sym^{n+1})` (`parabolicToGoodLine`, the Hochschild-Serre realization), and the
parabolic Poincaré duality (`arithmeticBinaryRep_left_nondegenerate` for `(e, e') = (-1, 0)`) gives
`dim parabolicH1 (Sym^{n+1} ⊗ det⁻¹) ≤ dim parabolicH1 (Sym^{n+1})`. Hence
`dim 𝒞(plane) ≤ dim 𝒞(line)`; the zero left kernel gives the reverse inequality, so the dimensions
agree and the right kernel is zero (`facePairing_right_nondegenerate_odd`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (parabolicH1 parabolicPairing twistedPairing_arithmeticBinaryRep)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face
open TernaryPeriodPolynomials.Argument.FacePairing

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

theorem finiteDimensional_parabolicH1 (m : ℕ) (e : ℤ) :
    FiniteDimensional ℂ (parabolicH1 (arithmeticBinaryRep m e)) := by
  have h : FiniteDimensional ℂ (groupCohomology.H1 (arithmeticBinaryRep m e)) :=
    TernaryPeriodPolynomials.Spectral.LevelOneESDimension.arithmeticH1_finiteDimensional
      m e
  exact FiniteDimensional.finiteDimensional_submodule _

/-- Parabolic duality: `dim parabolicH1 (Sym^{n+1} ⊗ det⁻¹) ≤ dim parabolicH1 (Sym^{n+1})`. -/
theorem finrank_parabolic_neg_le (n : ℕ) (hodd : Odd n) :
    Module.finrank ℂ (parabolicH1 (arithmeticBinaryRep (n + 1) (-1))) ≤
      Module.finrank ℂ (parabolicH1 (arithmeticBinaryRep (n + 1) 0)) := by
  have hm : Even (n + 1) := hodd.add_one
  have hodd' : Odd ((-1 : ℤ) + 0 - ((n + 1 : ℕ) : ℤ)) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨-(k : ℤ) - 2, by push_cast; omega⟩
  have hfin := finiteDimensional_parabolicH1 (n + 1) 0
  have hinj : Function.Injective
      (parabolicPairing (twistedPairing_arithmeticBinaryRep (n + 1) (-1) 0 hm hodd')) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro cl h
    exact TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne.arithmeticBinaryRep_left_nondegenerate
      (n + 1) (-1) 0 hm hodd' cl (fun cl' => by rw [h]; rfl)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Subspace.dual_finrank_eq] at this

theorem finiteDimensional_goodLine_locallyInner (n : ℕ) (hn : 0 < n) :
    FiniteDimensional ℂ (locallyInnerClasses n trivialCharacter .line goodLineFlag) := by
  have h := finiteDimensional_glAction n hn
  exact Module.Finite.equiv (goodLineLocallyInnerEquiv n trivialCharacter).symm

theorem finiteDimensional_badPlane_locallyInner (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    FiniteDimensional ℂ (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false)) := by
  have h := finiteDimensional_parabolicH1 (n + 1) (-1)
  exact Module.Finite.equiv (badPlaneLocallyInnerEquivParabolic n hn hodd).symm

/-- For odd `n`, `dim 𝒞(plane) ≤ dim 𝒞(line)`. -/
theorem finrank_plane_le_line_odd (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    Module.finrank ℂ (innerClasses n .plane) ≤ Module.finrank ℂ (innerClasses n .line) := by
  have hg : GoodFlag .line goodLineFlag := goodLineFlag_good
  have hb : ¬ GoodFlag .line standardBadLine := Face.standardBadLine_not_good
  have hgp : GoodFlag .plane (cuspFlag .plane true) := (cuspFlag_good_iff .plane true).mpr rfl
  have hbp : ¬ GoodFlag .plane (cuspFlag .plane false) :=
    fun h => absurd ((cuspFlag_good_iff .plane false).mp h) (by decide)
  have fgl := finiteDimensional_goodLine_locallyInner n hn
  have fbl : FiniteDimensional ℂ (locallyInnerClasses n trivialCharacter .line standardBadLine) :=
    finiteDimensional_badLine_locallyInner n hn
  have fgp := finiteDimensional_goodPlane_locallyInner n hn
  have fbp := finiteDimensional_badPlane_locallyInner n hn hodd
  have freeGL : Module.Free ℂ (locallyInnerClasses n trivialCharacter .line goodLineFlag) :=
    Module.Free.of_divisionRing ℂ _
  have freeBL : Module.Free ℂ (locallyInnerClasses n trivialCharacter .line standardBadLine) :=
    Module.Free.of_divisionRing ℂ _
  have freeGP : Module.Free ℂ (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true)) :=
    Module.Free.of_divisionRing ℂ _
  have freeBP : Module.Free ℂ (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false)) :=
    Module.Free.of_divisionRing ℂ _
  have eline := (innerClassesEquivLocal n goodLineFlag standardBadLine hg hb).finrank_eq
  have eplane :=
    (innerClassesEquivLocal n (cuspFlag .plane true) (cuspFlag .plane false) hgp hbp).finrank_eq
  rw [Module.finrank_prod] at eline eplane
  have dbl := finrank_badLine_locallyInner n hn
  have dgp := finrank_goodPlane_locallyInner n hn
  have dbp := (badPlaneLocallyInnerEquivParabolic n hn hodd).finrank_eq
  have lower : Module.finrank ℂ (parabolicH1 (arithmeticBinaryRep (n + 1) 0)) ≤
      Module.finrank ℂ (locallyInnerClasses n trivialCharacter .line goodLineFlag) :=
    LinearMap.finrank_le_finrank_of_injective (parabolicToGoodLine_injective n hn)
  have dual := finrank_parabolic_neg_le n hodd
  omega

theorem finiteDimensional_innerClasses_line_odd (n : ℕ) (hn : 0 < n) :
    FiniteDimensional ℂ (innerClasses n .line) := by
  have fgl := finiteDimensional_goodLine_locallyInner n hn
  have fbl : FiniteDimensional ℂ (locallyInnerClasses n trivialCharacter .line standardBadLine) :=
    finiteDimensional_badLine_locallyInner n hn
  exact Module.Finite.equiv
    (innerClassesEquivLocal n goodLineFlag standardBadLine goodLineFlag_good
      Face.standardBadLine_not_good).symm

theorem finiteDimensional_innerClasses_plane_odd (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    FiniteDimensional ℂ (innerClasses n .plane) := by
  have fgp := finiteDimensional_goodPlane_locallyInner n hn
  have fbp := finiteDimensional_badPlane_locallyInner n hn hodd
  exact Module.Finite.equiv
    (innerClassesEquivLocal n (cuspFlag .plane true) (cuspFlag .plane false)
      ((cuspFlag_good_iff .plane true).mpr rfl)
      (fun h => absurd ((cuspFlag_good_iff .plane false).mp h) (by decide))).symm

/-- **Odd `n`: the line and plane inner spaces have the same dimension.** -/
theorem finrank_innerClasses_eq_odd (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    Module.finrank ℂ (innerClasses n .line) = Module.finrank ℂ (innerClasses n .plane) := by
  have fline := finiteDimensional_innerClasses_line_odd n hn
  have fplane := finiteDimensional_innerClasses_plane_odd n hn hodd
  have hinj : Function.Injective (facePairing n) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact facePairing_left_nondegenerate n b fun η => by
      rw [hb]; rfl
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Subspace.dual_finrank_eq] at h1
  exact le_antisymm h1 (finrank_plane_le_line_odd n hn hodd)

/-- **Odd `n`: the realization of parabolic classes at the good line is a bijection**, so the
locally inner classes at the good line are exactly `parabolicH1 (Sym^{n+1})`. -/
theorem parabolicToGoodLine_bijective (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    Function.Bijective (parabolicToGoodLine n hn) := by
  have hg : GoodFlag .line goodLineFlag := goodLineFlag_good
  have hb : ¬ GoodFlag .line standardBadLine := Face.standardBadLine_not_good
  have hgp : GoodFlag .plane (cuspFlag .plane true) := (cuspFlag_good_iff .plane true).mpr rfl
  have hbp : ¬ GoodFlag .plane (cuspFlag .plane false) :=
    fun h => absurd ((cuspFlag_good_iff .plane false).mp h) (by decide)
  have fgl := finiteDimensional_goodLine_locallyInner n hn
  have fbl : FiniteDimensional ℂ (locallyInnerClasses n trivialCharacter .line standardBadLine) :=
    finiteDimensional_badLine_locallyInner n hn
  have fgp := finiteDimensional_goodPlane_locallyInner n hn
  have fbp := finiteDimensional_badPlane_locallyInner n hn hodd
  have freeGL : Module.Free ℂ (locallyInnerClasses n trivialCharacter .line goodLineFlag) :=
    Module.Free.of_divisionRing ℂ _
  have freeBL : Module.Free ℂ (locallyInnerClasses n trivialCharacter .line standardBadLine) :=
    Module.Free.of_divisionRing ℂ _
  have freeGP : Module.Free ℂ (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true)) :=
    Module.Free.of_divisionRing ℂ _
  have freeBP : Module.Free ℂ (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false)) :=
    Module.Free.of_divisionRing ℂ _
  have freePH : Module.Free ℂ (parabolicH1 (arithmeticBinaryRep (n + 1) 0)) :=
    Module.Free.of_divisionRing ℂ _
  have eline := (innerClassesEquivLocal n goodLineFlag standardBadLine hg hb).finrank_eq
  have eplane :=
    (innerClassesEquivLocal n (cuspFlag .plane true) (cuspFlag .plane false) hgp hbp).finrank_eq
  rw [Module.finrank_prod] at eline eplane
  have dbl := finrank_badLine_locallyInner n hn
  have dgp := finrank_goodPlane_locallyInner n hn
  have dbp := (badPlaneLocallyInnerEquivParabolic n hn hodd).finrank_eq
  have lower : Module.finrank ℂ (parabolicH1 (arithmeticBinaryRep (n + 1) 0)) ≤
      Module.finrank ℂ (locallyInnerClasses n trivialCharacter .line goodLineFlag) :=
    LinearMap.finrank_le_finrank_of_injective (parabolicToGoodLine_injective n hn)
  have dual := finrank_parabolic_neg_le n hodd
  have heq := finrank_innerClasses_eq_odd n hn hodd
  have hfin := finiteDimensional_parabolicH1 (n + 1) 0
  have hdim : Module.finrank ℂ (parabolicH1 (arithmeticBinaryRep (n + 1) 0)) =
      Module.finrank ℂ (locallyInnerClasses n trivialCharacter .line goodLineFlag) := by
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (parabolicToGoodLine_injective n hn) |> fun hs => ⟨parabolicToGoodLine_injective n hn, hs⟩

/-- **The face pairing has zero right kernel for odd `n`.** -/
theorem facePairing_right_nondegenerate_odd (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (ξ : innerClasses n .plane) (h : ∀ b : innerClasses n .line, facePairing n b ξ = 0) :
    ξ = 0 := by
  have fline := finiteDimensional_innerClasses_line_odd n hn
  have fplane := finiteDimensional_innerClasses_plane_odd n hn hodd
  have hinj : Function.Injective (facePairing n) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact facePairing_left_nondegenerate n b fun η => by
      rw [hb]; rfl
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Subspace.dual_finrank_eq] at h1
  have h2 := finrank_plane_le_line_odd n hn hodd
  exact facePairing_perfect_of_finrank_eq n (le_antisymm h1 h2) ξ h

end TernaryPeriodPolynomials.Argument.FacePairingFull
