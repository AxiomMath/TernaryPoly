module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.BadLineEdge

@[expose] public section


/-!
# The potentials of the line source at the bad line

At the identity frame (the flag `cuspFlag .line false = mk 1`) the line source at rational vertices
is the cup product of the two potentials

* `bdA E x = α(iwALine x) 1`, the Levi potential,
* `bdL x = lineRadical (iwPLine x)`, the radical potential,

evaluated on the real image of the vertex `x`.  On the stabilizer `ΛB = {R(x, ±1, A)}` of the bad
line they satisfy the hypotheses of the edge computation `bd_classOf_ne_zero_of_cup`:

* the Levi potential vanishes on the radical `Ux v` and equals `α(A) 1` at `Lm A`
  (`bdA_Ux`, `bdA_Lm`), because the Levi cocycle vanishes on the orthogonal group;
* the radical potential satisfies `bdL (Ux v · g) = lam v + ρ(Ux v) ∘ bdL g` (`bdL_Ux_mul`), since
  the line unipotent acts trivially on binary forms.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCosets (icast)
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed)
open TernaryPeriodPolynomials.LevelThree.BadLineCoordinates (ΛB)
open TernaryPeriodPolynomials.LevelThree.BadLineCosets (Mel_val R_congr)
open TernaryPeriodPolynomials.LevelThree.BadLineTransitions (Ux Lm)
open TernaryPeriodPolynomials.LevelThree.BadLinePairs (R_zero Ux_eq_unipotent)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets (levelEmbed levelEmbed_apply)

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The real image of a rational matrix. -/
local notation "ratReal" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

variable {n : ℕ}

/-! ## Iwasawa factors of the identity -/

theorem bd_iwPLine_one : iwPLine (1 : RealGL3) = 1 := by
  apply Subtype.ext
  exact iwasawaB_one

theorem bd_iwALine_one : iwALine (1 : RealGL3) = 1 := by
  unfold iwALine
  rw [bd_iwPLine_one]
  exact lineLeviBlockHom.map_one

/-- **The Levi cocycle along the Iwasawa factor of an element of the line parabolic.** -/
theorem bd_alpha_iwALine {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n)
    (p : lineParabolic ℝ) : E.α (iwALine p.1) 1 = E.α (lineLeviBlock p) 1 := by
  have h := alpha_iwALine_mul E p (1 : RealGL3) 1
  have h1 : E.α (iwALine (1 : RealGL3)) = fun _ => 0 := by
    rw [bd_iwALine_one]
    exact funext (dl_alpha_one E)
  rw [mul_one, h1] at h
  rw [h]
  simp [binaryCohomologicalAction]

/-! ## The real images of the radical and Levi elements -/

theorem bd_ratReal_Ux (v : ℤ × ℤ) :
    ratReal ((Ux v : ΛB) : RationalGL3) = (dlUnipotent (v.1 : ℝ) (v.2 : ℝ)).1 := by
  rw [Ux_eq_unipotent]
  change Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (lineUnipotent (v.1 : ℚ) (v.2 : ℚ)) =
    lineUnipotent (v.1 : ℝ) (v.2 : ℝ)
  rw [map_lineUnipotent']
  simp

theorem bd_Lm_val (A : binaryArithmeticLevel) :
    ((Lm A : ΛB) : RationalGL3) = lineLevi 1 (levelEmbed A) := by
  rw [Lm, Mel_val, ← R_zero]
  exact R_congr (by simp [icast]) (by simp) rfl

theorem bd_ratReal_Lm (A : binaryArithmeticLevel) :
    ratReal ((Lm A : ΛB) : RationalGL3) =
      (dlLevi (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val)).1 := by
  rw [bd_Lm_val, TernaryPeriodPolynomials.SourceConstruction.map_lineLevi]
  have h1 : Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (levelEmbed A) =
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val := by
    apply Units.ext
    ext i j
    simp [levelEmbed_apply, integralEmbed, Matrix.GeneralLinearGroup.map_apply]
  rw [h1]
  simp [dlLevi]

/-! ## The potentials -/

/-- **The Levi potential of the line source at the bad line.** -/
def bdA {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n) (x : RationalGL3) :
    Binary.HomogeneousPoly (n + 1) :=
  E.α (iwALine (ratReal x)) 1

/-- **The radical potential of the line source at the bad line.** -/
def bdL (n : ℕ) (x : RationalGL3) :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n :=
  lineRadical n trivialCharacter (iwPLine (ratReal x))

theorem bdA_one {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n) : bdA E 1 = 0 := by
  unfold bdA
  rw [dl_ratReal_one, bd_iwALine_one]
  exact dl_alpha_one E 1

theorem bdA_Ux {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n) (v : ℤ × ℤ) :
    bdA E ((Ux v : ΛB) : RationalGL3) = 0 := by
  unfold bdA
  rw [bd_ratReal_Ux, bd_alpha_iwALine, dlUnipotent_block]
  exact dl_alpha_one E 1

theorem bdA_Lm {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n)
    (A : binaryArithmeticLevel) :
    bdA E ((Lm A : ΛB) : RationalGL3) =
      E.α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 := by
  unfold bdA
  rw [bd_ratReal_Lm, bd_alpha_iwALine, dlLevi_block]

/-- **The Levi potential does not see the radical lattice.** -/
theorem bdA_radical {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n) :
    BadLeviRadical n (bdA E) := fun v => by
  rw [bdA_Ux, bdA_one]

/-- **The cocycle law of the radical potential along the radical lattice.** -/
theorem bdL_radical (n : ℕ) : BadRadicalLaw n (bdL n) := by
  intro v g Q
  have hr : ratReal (((Ux v : ΛB) : RationalGL3) * g) =
      (dlUnipotent (v.1 : ℝ) (v.2 : ℝ)).1 * ratReal g := by
    rw [map_mul, bd_ratReal_Ux]
  have hρ : ρn n ((Ux v : ΛB) : RationalGL3) =
      realCoefficientComponent n trivialCharacter (dlUnipotent (v.1 : ℝ) (v.2 : ℝ)).1 := by
    show realCoefficientComponent n trivialCharacter (ratReal ((Ux v : ΛB) : RationalGL3)) = _
    rw [bd_ratReal_Ux]
  unfold bdL bdLam
  rw [hr, lineRadical_iwPLine_mul trivialCharacter (dlUnipotent (v.1 : ℝ) (v.2 : ℝ)) (ratReal g) Q,
    dlUnipotent_star_inv, hρ]

end TernaryPeriodPolynomials.SourceConstruction
