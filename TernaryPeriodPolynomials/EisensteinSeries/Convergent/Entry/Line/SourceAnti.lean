module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.SourcePackage
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.SourceAnti
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.AntiCommute
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceReal
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Line
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerTwLift

@[expose] public section


/-!
# The line source of the symmetrized twisted Eichler cocycle: holomorphic part plus reflected part

Line analogue of `PlaneSourceAnti`.  `Λ = diag(1,-1,1) = lineLevi 1 J` is the reflection in the line Levi; the sign twist
of `lineStar` (`θ(Λ) = det J = -1`, `lineTheta_lamP_inv`) cancels the minus sign of the antiholomorphic half of
`eichlerNormalTw`, so the radical law `lineRadical_J` turns the reflected half into a holomorphic-type source at `Λ g_∞`
(`lineSourceAt_decomp`, `coeff_lineSourceAt_eichlerTw`).

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The line Levi lift `diag(1, J) = diag(1, -1, 1)` of the reflection `J`. -/
def lamL : RealGL3 := GeneralEisenstein.Adelic.lineLevi 1 UpperHalfPlane.J

/-- The reflection as an element of the line parabolic. -/
def lamP : GeneralEisenstein.Adelic.lineParabolic ℝ := ⟨lamL, GeneralEisenstein.Adelic.lineLevi_mem 1 UpperHalfPlane.J⟩

theorem lamP_val : lamP.1 = lamL := rfl

theorem lamL_val : (lamL.val : Mat3) = lamM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lamL, lamM, GeneralEisenstein.Adelic.lineLevi_val, UpperHalfPlane.J]

theorem lamL_mul_self : lamL * lamL = 1 := by
  apply Units.ext
  rw [Units.val_mul, lamL_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lamM, Matrix.mul_apply, Fin.sum_univ_three]

theorem lamL_inv : lamL⁻¹ = lamL := by
  rw [inv_eq_iff_mul_eq_one]; exact lamL_mul_self

theorem lineLeviBlock_lamP : lineLeviBlock lamP = UpperHalfPlane.J :=
  lineLeviBlock_levi 1 UpperHalfPlane.J

theorem lineRadical_lamP (n : ℕ) (χ : RankOneCharacter) : lineRadical n χ lamP = 0 :=
  lineRadical_levi_eq_zero n χ 1 UpperHalfPlane.J

theorem det_map_J :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) UpperHalfPlane.J) : ℂˣ) : ℂ) = -1 := by
  rw [GeneralLinearGroup.val_det_apply]
  have h := RingHom.map_det (algebraMap ℝ ℂ) (UpperHalfPlane.J : BinaryRealGL).val
  rw [det_upperJ] at h
  simpa using h.symm

theorem lineTheta_lamP_inv (χ : RankOneCharacter) (hc : ∀ g : RealGL3, componentCharacter χ g = 1) :
    lineTheta χ lamP⁻¹ = -1 := by
  have e : lineLeviBlock lamP⁻¹ = (lineLeviBlock lamP)⁻¹ := lineLeviBlockHom.map_inv lamP
  have hJ : (UpperHalfPlane.J : BinaryRealGL)⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one]; exact upperJ_mul_self
  have hcorner : (lamP⁻¹).1.val 0 0 = 1 := by
    have : (lamP⁻¹).1 = lamL := by
      show lamL⁻¹ = lamL
      exact lamL_inv
    rw [this, lamL_val]; simp [lamM]
  rw [lineTheta_apply, hc, e, lineLeviBlock_lamP, hJ, hcorner, det_map_J]
  simp

theorem lineStar_lamP_inv (n : ℕ) (χ : RankOneCharacter) (hc : ∀ g : RealGL3, componentCharacter χ g = 1)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    lineStar χ (n + 1) lamP⁻¹ (binaryCoefficient n UpperHalfPlane.J Q) = -Q := by
  have e : lineLeviBlock lamP⁻¹ = (lineLeviBlock lamP)⁻¹ := lineLeviBlockHom.map_inv lamP
  show lineTheta χ lamP⁻¹ •
      Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock lamP⁻¹))
        (binaryCoefficient n UpperHalfPlane.J Q) = -Q
  have hT : binaryCoefficient n UpperHalfPlane.J Q = Binary.homogeneousAction (n + 1) (-1)
      (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock lamP)) Q := by
    rw [lineLeviBlock_lamP]; rfl
  rw [lineTheta_lamP_inv χ hc, hT, e, _root_.map_inv, ← Module.End.mul_apply, ← map_mul,
    _root_.inv_mul_cancel, map_one, Module.End.one_apply]
  exact neg_one_smul ℂ Q

/-- **The radical law for the line reflection.** -/
theorem lineRadical_J (n : ℕ) (χ : RankOneCharacter) (hc : ∀ g : RealGL3, componentCharacter χ g = 1)
    (Y : RealGL3) (Q : Binary.HomogeneousPoly (n + 1)) :
    lineRadical n χ (iwPLine Y) (binaryCoefficient n UpperHalfPlane.J Q) =
      -realCoefficientComponent n χ lamL⁻¹ (lineRadical n χ (iwPLine (lamL * Y)) Q) := by
  have h := lineRadical_iwPLine_mul (n := n) χ lamP (lamL * Y) (binaryCoefficient n UpperHalfPlane.J Q)
  rw [lamP_val, ← mul_assoc, lamL_mul_self, one_mul, lineRadical_lamP, LinearMap.zero_apply, zero_add,
    lineStar_lamP_inv n χ hc, map_neg, map_neg] at h
  rw [lamL_inv]
  exact h

theorem eichlerHolomorphic_J_iwALine (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (Y : RealGL3)
    (h : BinaryAdelicGL) :
    eichlerHolomorphic n F (UpperHalfPlane.J * iwALine Y) h =
      eichlerHolomorphic n F (iwALine (lamL * Y)) h := by
  obtain ⟨k, hk, he⟩ := lineLeviBlock_iwPLine_mul lamP Y
  rw [lineLeviBlock_lamP, lamP_val] at he
  rw [← he, eichlerHolomorphic_eq_smul, eichlerHolomorphic_eq_smul]
  unfold basePoint
  rw [mul_smul, orthogonal_smul_I k hk]

theorem alpha_decomp_tw {σ : CuspidalRepresentation} (n : ℕ) (E : LineLeviCocycleData σ n)
    (F : BinaryAdelicGL → ℂ → ℂ) (hE : ∀ A, E.α A = eichlerNormalTw n F A) (A : BinaryRealGL)
    (x : BinaryAdelicGL) :
    E.α A x = eichlerHolomorphic n F A x -
      binaryCoefficient n UpperHalfPlane.J (eichlerHolomorphic n F (UpperHalfPlane.J * A)
        (x * atInfinity UpperHalfPlane.J)) := by
  have h1 : eichlerNormalTw n F A x = eichlerTwisted n F A x := by
    unfold eichlerNormalTw eichlerTwisted eichlerHolomorphic eichlerAntiholomorphic
    rw [smul_sub]
  rw [hE, h1, eichlerTwisted_eq, Pi.sub_apply]
  congr 1
  exact binaryAmbientRepresentation_apply_of_unimodular (by rw [det_upperJ]; norm_num) _ _

/-- **The line source splits into a holomorphic part at `g_∞` and a holomorphic-type part at `Λ g_∞`**
(`Λ = diag(1,-1,1)`), for the symmetrized twisted Eichler cocycle. -/
theorem lineSourceAt_decomp (n : ℕ) (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (F : BinaryAdelicGL → ℂ → ℂ) (hE : ∀ A, E.α A = eichlerNormalTw n F A)
    (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) :
    (lineSourceAt D E y g x : HomogeneousPoly n) =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        (holInnerLine n D.chi (cFLine D g) (fun A => eichlerHolomorphic n F A (x * bFLine g))
          (fun i => realGroup g * y i)) +
      realCoefficientComponent n D.chi (lamL * realGroup g)⁻¹
        (holInnerLine n D.chi (cFLine D g)
          (fun A => eichlerHolomorphic n F A (x * bFLine g * atInfinity UpperHalfPlane.J))
          (fun i => (lamL * realGroup g) * y i)) := by
  set gR : RealGL3 := realGroup g with hgR
  set c : ℂ := cFLine D g with hcdef
  set Y : Fin 3 → RealGL3 := fun i => gR * y i with hY
  have hα : ∀ i, E.α (iwALine (Y i)) (x * bFLine g) =
      eichlerHolomorphic n F (iwALine (Y i)) (x * bFLine g) -
        binaryCoefficient n UpperHalfPlane.J (eichlerHolomorphic n F (iwALine (lamL * Y i))
          (x * bFLine g * atInfinity UpperHalfPlane.J)) := by
    intro i
    rw [alpha_decomp_tw n E F hE, eichlerHolomorphic_J_iwALine]
  set Qh : Binary.HomogeneousPoly (n + 1) := c • (eichlerHolomorphic n F (iwALine (Y 1)) (x * bFLine g) -
    eichlerHolomorphic n F (iwALine (Y 0)) (x * bFLine g)) with hQh
  set Q' : Binary.HomogeneousPoly (n + 1) := c • (eichlerHolomorphic n F (iwALine (lamL * Y 1))
    (x * bFLine g * atInfinity UpperHalfPlane.J) - eichlerHolomorphic n F (iwALine (lamL * Y 0))
    (x * bFLine g * atInfinity UpperHalfPlane.J)) with hQ'
  have hQ : c • (E.α (iwALine (Y 1)) (x * bFLine g) - E.α (iwALine (Y 0)) (x * bFLine g)) =
      Qh - binaryCoefficient n UpperHalfPlane.J Q' := by
    rw [hα 1, hα 0, hQh, hQ', map_smul, map_sub]
    simp only [smul_sub]
    abel
  have hsrc : (lineSourceAt D E y g x : HomogeneousPoly n) = realCoefficientComponent n D.chi gR⁻¹
      ((lineRadical n D.chi (iwPLine (Y 2)) - lineRadical n D.chi (iwPLine (Y 1)))
        (c • (E.α (iwALine (Y 1)) (x * bFLine g) - E.α (iwALine (Y 0)) (x * bFLine g)))) := rfl
  have hε : (realCoefficientComponent n D.chi gR⁻¹) ((lineRadical n D.chi (iwPLine (Y 2)) -
      lineRadical n D.chi (iwPLine (Y 1))) (-binaryCoefficient n UpperHalfPlane.J Q')) =
      realCoefficientComponent n D.chi (lamL * gR)⁻¹ (holInnerLine n D.chi c
        (fun A => eichlerHolomorphic n F A (x * bFLine g * atInfinity UpperHalfPlane.J))
        (fun i => (lamL * gR) * y i)) := by
    have hY' : ∀ i, lamL * Y i = (lamL * gR) * y i := fun i => by simp only [hY, mul_assoc]
    have hR : ∀ i, lineRadical n D.chi (iwPLine (Y i)) (binaryCoefficient n UpperHalfPlane.J Q') =
        -realCoefficientComponent n D.chi lamL⁻¹ (lineRadical n D.chi (iwPLine (lamL * Y i)) Q') :=
      fun i => lineRadical_J n D.chi hc (Y i) Q'
    have key : (lineRadical n D.chi (iwPLine (Y 2)) - lineRadical n D.chi (iwPLine (Y 1)))
        (-binaryCoefficient n UpperHalfPlane.J Q') = realCoefficientComponent n D.chi lamL⁻¹
        (holInnerLine n D.chi c
          (fun A => eichlerHolomorphic n F A (x * bFLine g * atInfinity UpperHalfPlane.J))
          (fun i => (lamL * gR) * y i)) := by
      have hh : holInnerLine n D.chi c
          (fun A => eichlerHolomorphic n F A (x * bFLine g * atInfinity UpperHalfPlane.J))
          (fun i => (lamL * gR) * y i) =
          (lineRadical n D.chi (iwPLine (lamL * Y 2)) - lineRadical n D.chi (iwPLine (lamL * Y 1))) Q' := by
        simp only [holInnerLine, hY', hQ']
      rw [hh, map_neg, LinearMap.sub_apply, LinearMap.sub_apply, hR 2, hR 1, map_sub]
      abel
    rw [key, ← Module.End.mul_apply, ← map_mul, ← _root_.mul_inv_rev]
  have e1 : ((lineRadical n D.chi (iwPLine (Y 2)) - lineRadical n D.chi (iwPLine (Y 1)))
      (Qh - binaryCoefficient n UpperHalfPlane.J Q')) =
      holInnerLine n D.chi c (fun A => eichlerHolomorphic n F A (x * bFLine g)) Y +
        (lineRadical n D.chi (iwPLine (Y 2)) - lineRadical n D.chi (iwPLine (Y 1)))
          (-binaryCoefficient n UpperHalfPlane.J Q') := by
    rw [sub_eq_add_neg, LinearMap.map_add]
    rfl
  rw [hsrc, hQ, e1, map_add, hε]

/-- **The line source of the symmetrized twisted Eichler cocycle, coefficientwise**: holomorphic part at `g_∞`
plus holomorphic-type part at `Λ g_∞` (`Λ = diag(1,-1,1)`, datum `x · b_F · J`), each the line integral cochain
`lineIntG` minus its boundary combination. -/
theorem coeff_lineSourceAt_eichlerTw (n : ℕ) (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (F : BinaryAdelicGL → ℂ → ℂ) (hE : ∀ A, E.α A = eichlerNormalTw n F A)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
    (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
    (hχ : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) (κ : Fin 3 →₀ ℕ) :
    ((lineSourceAt D E y g x : HomogeneousPoly n) : Poly).coeff κ =
      (lineIntG n (fun z => (-1) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) * (cFLine D g * 2⁻¹ * F (x * bFLine g) z))
          (realGroup g).val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ -
        ∑ ν ∈ degSet n, (SeedC3.rho ((realGroup g).val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
          bdryCoeffLine (eichlerDatum n F holomorphic (x * bFLine g) (cFLine D g)) ν
            (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2))) +
      (lineIntG n (fun z => (-1) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) *
            (cFLine D g * 2⁻¹ * F (x * bFLine g * atInfinity UpperHalfPlane.J) z))
          (lamL * realGroup g).val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ -
        ∑ ν ∈ degSet n, (SeedC3.rho ((lamL * realGroup g).val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
          bdryCoeffLine (eichlerDatum n F holomorphic (x * bFLine g * atInfinity UpperHalfPlane.J) (cFLine D g)) ν
            (gramOf ((lamL * realGroup g) * y 0)) (gramOf ((lamL * realGroup g) * y 1))
            (gramOf ((lamL * realGroup g) * y 2))) := by
  rw [lineSourceAt_decomp n D E F hE hc y g x, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  congr 1
  · exact coeff_holLineSource_bridge n D.chi hχ (cFLine D g) (fun A => eichlerHolomorphic n F A (x * bFLine g))
      (realGroup g) y _ (eichlerDatum n F holomorphic (x * bFLine g) (cFLine D g))
      (eichlerDatum_hpot n F holomorphic (x * bFLine g) (cFLine D g))
      (continuousOn_const.mul (holomorphic _).continuousOn) κ
  · exact coeff_holLineSource_bridge n D.chi hχ (cFLine D g)
      (fun A => eichlerHolomorphic n F A (x * bFLine g * atInfinity UpperHalfPlane.J))
      (lamL * realGroup g) y _
      (eichlerDatum n F holomorphic (x * bFLine g * atInfinity UpperHalfPlane.J) (cFLine D g))
      (eichlerDatum_hpot n F holomorphic _ (cFLine D g))
      (continuousOn_const.mul (holomorphic _).continuousOn) κ

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
