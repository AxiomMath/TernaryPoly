module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.BadLinePotential
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Identity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Real
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceCoordinate

@[expose] public section


/-!
# The bad-line coordinate of the level-three line source: vanishing forces a Levi coboundary

For a level-three sign-twisted Levi cocycle datum `E : LineLeviCocycleData3` (lifts fixed only by the
bad-line level) the level-three line source `lineSource3 D E` has, at the identity adele and rational
vertices, the same cup product of potentials as the spherical one, with Levi potential
`bdA3 E x = E.α (iwALine x) 1` and the same radical potential `bdL`.  Hence the edge computation of
`DetectBadLineEdge` applies verbatim: if the bad-line Shapiro coordinate of a cocycle evaluating
`lineSource3 D E` vanishes, then the Levi values `A ↦ (n + 1) E.α(A) 1` on `Γ₁'(3)` form a coboundary
`A w - w` (`lineSource3_badLine_levi_coboundary`).  Consequently the bad-line coordinate of
`w ↦ lineSource3 D (E w)` is injective as soon as `w ↦ [A ↦ E_w.α(A) 1]` is injective on
`H¹(Γ₁'(3), Sym^{n+1})` (`lineSource3_badLine_coordinate_eq_zero_imp`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag)
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspRes)
open TernaryPeriodPolynomials.LevelThree.BadLineCoordinates (ΛB)
open TernaryPeriodPolynomials.LevelThree.BadLineTransitions (Ux Lm)
open TernaryPeriodPolynomials.Separation (sourceCoordinate sourceCoordinate_apply)
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
  (sourceCocycles evaluatedSource_realizes)

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The real image of a rational matrix. -/
local notation "ratReal" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

variable {n : ℕ}

/-! ## The Levi potential of a level-three datum -/

/-- **The Levi potential of the level-three line source at the bad line.** -/
def bdA3 {σ : CuspidalRepresentation} (E : LineLeviCocycleData3 σ n) (x : RationalGL3) :
    Binary.HomogeneousPoly (n + 1) :=
  E.α (iwALine (ratReal x)) 1

theorem bd3_alpha_one {σ : CuspidalRepresentation} (E : LineLeviCocycleData3 σ n)
    (x : BinaryAdelicGL) : E.α 1 x = 0 :=
  E.orth 1 (by simp) x

/-- The Levi cocycle along the Iwasawa factor of an element of the line parabolic. -/
theorem bd3_alpha_iwALine {σ : CuspidalRepresentation} (E : LineLeviCocycleData3 σ n)
    (p : lineParabolic ℝ) : E.α (iwALine p.1) 1 = E.α (lineLeviBlock p) 1 := by
  have h := alpha_iwALine_mul3 E p (1 : RealGL3) 1
  have h1 : E.α (iwALine (1 : RealGL3)) = fun _ => 0 := by
    rw [bd_iwALine_one]
    exact funext (bd3_alpha_one E)
  rw [mul_one, h1] at h
  rw [h]
  simp [binaryCohomologicalAction]

theorem bdA3_one {σ : CuspidalRepresentation} (E : LineLeviCocycleData3 σ n) : bdA3 E 1 = 0 := by
  unfold bdA3
  rw [dl_ratReal_one, bd_iwALine_one]
  exact bd3_alpha_one E 1

theorem bdA3_Ux {σ : CuspidalRepresentation} (E : LineLeviCocycleData3 σ n) (v : ℤ × ℤ) :
    bdA3 E ((Ux v : ΛB) : RationalGL3) = 0 := by
  unfold bdA3
  rw [bd_ratReal_Ux, bd3_alpha_iwALine, dlUnipotent_block]
  exact bd3_alpha_one E 1

theorem bdA3_Lm {σ : CuspidalRepresentation} (E : LineLeviCocycleData3 σ n)
    (A : binaryArithmeticLevel) :
    bdA3 E ((Lm A : ΛB) : RationalGL3) =
      E.α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 := by
  unfold bdA3
  rw [bd_ratReal_Lm, bd3_alpha_iwALine, dlLevi_block]

/-- The Levi potential does not see the radical lattice. -/
theorem bdA3_radical {σ : CuspidalRepresentation} (E : LineLeviCocycleData3 σ n) :
    BadLeviRadical n (bdA3 E) := fun v => by
  rw [bdA3_Ux, bdA3_one]

/-! ## The level-three line source at the identity -/

/-- **The level-three line source at the identity adele and rational vertices is the cup product of
the potentials of the bad line.** -/
theorem bd3_lineSource (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (hchi : D.chi = trivialCharacter) (x : Fin 3 → RationalGL3) :
    lineSource3 D E (fun i => ratReal (x i)) (rationalGroup ((1 : RationalGL3)⁻¹)) =
      (bdL n (x 2) - bdL n (x 1)) (bdA3 E (x 1) - bdA3 E (x 0)) := by
  have hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1 := by
    intro u
    rw [hchi]
    rfl
  have h1 : rationalGroup ((1 : RationalGL3)⁻¹) = 1 := by simp
  rw [h1, lineSource3_identity D E hχ, hchi]
  rfl

/-- **An evaluated level-three line source represents the cup product of the potentials.** -/
theorem bd3_represents (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (hchi : D.chi = trivialCharacter)
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)}
    (hz : Evaluates D .line (lineSource3 D E) z) (g h : ΛB) :
    z.val.val ![1, g.val, g.val * h.val] (QuotientGroup.mk 1) =
      (bdL n (g.val * h.val) - bdL n g.val) (bdA3 E g.val - bdA3 E 1) :=
  (hz ![1, g.val, g.val * h.val] 1).trans
    (bd3_lineSource D E hchi ![1, g.val, g.val * h.val])

/-! ## A vanishing coordinate forces a Levi coboundary -/

/-- **If the bad-line Shapiro coordinate of a stratum class representing the cup product of the
level-three potentials vanishes, the Levi values form a coboundary on `Γ₁'(3)`.** -/
theorem bd3_levi_coboundary (χ : RankOneCharacter) (hχ : χ = trivialCharacter) (pos : 0 < n)
    {σ : CuspidalRepresentation} (E : LineLeviCocycleData3 σ n)
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line))
    (hrep : ∀ g h : ΛB, z.val.val ![1, g.val, g.val * h.val] (QuotientGroup.mk 1) =
      (bdL n (g.val * h.val) - bdL n g.val) (bdA3 E g.val - bdA3 E 1))
    (h0 : cuspRes n χ .line false
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z) =
        0) :
    ∃ w : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) • (bdA3 E ((Lm A : ΛB) : RationalGL3) - bdA3 E 1) =
        binaryArithmeticRepresentation n A w - w := by
  subst hχ
  by_contra hδ
  let C : cocycles ΛB (ρn n) :=
    fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (cuspFlag .line false) z
  have hne : classOf ΛB (ρn n) C ≠ 0 :=
    bd_classOf_ne_zero_of_cup pos C (bdA3 E) (bdL n) (fun g h => hrep g h) (bdA3_radical E)
      (bdL_radical n) hδ
  exact hne h0

/-- **For the level-three line source, vanishing bad-line coordinate means the Levi period cocycle
`A ↦ E.α(A) 1` is a coboundary of `Γ₁'(3)` in `Sym^{n+1}` (up to the factor `n + 1`).** -/
theorem lineSource3_badLine_levi_coboundary (D : InducingData n)
    (E : LineLeviCocycleData3 D.cusp n) (hchi : D.chi = trivialCharacter) (pos : 0 < n)
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)}
    (hz : Evaluates D .line (lineSource3 D E) z)
    (h0 : cuspRes n D.chi .line false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z) = 0) :
    ∃ w : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) • E.α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        binaryArithmeticRepresentation n A w - w := by
  obtain ⟨w, hw⟩ := bd3_levi_coboundary D.chi hchi pos E z (bd3_represents D E hchi hz) h0
  refine ⟨w, fun A => ?_⟩
  have h := hw A
  rw [bdA3_Lm, bdA3_one, sub_zero] at h
  exact h

/-- **Injectivity of the bad-line coordinate of the level-three line sources, reduced to the
injectivity of the Levi period class on `Γ₁'(3)`.**  For a family `E` of level-three Levi cocycle data
indexed by `W`, if the vanishing of the class of `A ↦ (n + 1) (E w).α(A) 1` in `H¹(Γ₁'(3), Sym^{n+1})`
forces `w = 0` (`hper`), then `w` is determined by the bad-line coordinate of `lineSource3 D (E w)`. -/
theorem lineSource3_badLine_coordinate_eq_zero_imp {W : Type*} [Zero W] (D : InducingData n)
    (hchi : D.chi = trivialCharacter) (pos : 0 < n)
    (E : W → LineLeviCocycleData3 D.cusp n)
    (hper : ∀ w : W, (∃ w₀ : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) • (E w).α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        binaryArithmeticRepresentation n A w₀ - w₀) → w = 0)
    (hsrc : ∀ w : W, IsSourceCocycle D .line (lineSource3 D (E w))) (w : W)
    (h0 : sourceCoordinate D .line false ⟨lineSource3 D (E w), hsrc w⟩ = 0) : w = 0 := by
  apply hper w
  rw [sourceCoordinate_apply] at h0
  exact lineSource3_badLine_levi_coboundary D (E w) hchi pos
    (evaluatedSource_realizes D .line ⟨lineSource3 D (E w), hsrc w⟩) h0

/-- **The bad-line coordinate of the level-three line sources is injective** on a linear family
`Φ : W → sourceCocycles D .line`, `Φ w = lineSource3 D (E w)`, as soon as the Levi period class of
`E w` on `Γ₁'(3)` determines `w` (`hper`). -/
theorem lineSource3_badLine_coordinate_injective {W : Type*} [AddCommGroup W] [Module ℂ W]
    (D : InducingData n) (hchi : D.chi = trivialCharacter) (pos : 0 < n)
    (E : W → LineLeviCocycleData3 D.cusp n)
    (hsrc : ∀ w : W, IsSourceCocycle D .line (lineSource3 D (E w)))
    (Φ : W →ₗ[ℂ] sourceCocycles D .line) (hΦ : ∀ w, (Φ w).val = lineSource3 D (E w))
    (hper : ∀ w : W, (∃ w₀ : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) • (E w).α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        binaryArithmeticRepresentation n A w₀ - w₀) → w = 0) :
    Function.Injective (sourceCoordinate D .line false ∘ₗ Φ) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  have hΦw : Φ w = ⟨lineSource3 D (E w), hsrc w⟩ := Subtype.ext (hΦ w)
  apply lineSource3_badLine_coordinate_eq_zero_imp D hchi pos E hper hsrc w
  rw [← hΦw]
  exact hw

end TernaryPeriodPolynomials.SourceConstruction
