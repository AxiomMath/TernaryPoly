module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.SourcePackage
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceReal
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.NormalCocycle

@[expose] public section


/-!
# The plane source of the symmetrized Eichler cocycle: holomorphic part plus reflected part

For `E.α = eichlerNormal n F` (holomorphic part plus the `J`-reflected antiholomorphic part), the library's
`planeSourceAt D E y g x` splits as the holomorphic-part source at `g_∞` plus a holomorphic-type source at
`ε g_∞` (`ε = diag(-1,1,1)`, adelic datum `x · b_F(g) · J_∞`); this uses the radical law for the reflection
(`planeRadical_J`) and `eichlerHolomorphic_J_iwA`. Each half is then the plane integral cochain `planeIntG` minus a
boundary combination (`coeff_planeSourceAt_eichler`, via `coeff_holSource_bridge`).

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The Levi lift `diag(J, 1) = diag(-1, 1, 1)` of the reflection `J`. -/
def epsJ : RealGL3 := GeneralEisenstein.Adelic.planeLevi UpperHalfPlane.J 1

/-- The reflection as an element of the plane parabolic. -/
def epsP : planeParabolic ℝ := ⟨epsJ, GeneralEisenstein.Adelic.planeLevi_mem UpperHalfPlane.J 1⟩

theorem leviBlock_epsP : leviBlock epsP = UpperHalfPlane.J := leviBlock_planeLevi _ _

theorem epsP_val : epsP.1 = epsJ := rfl

theorem leviStar_epsP_inv (n : ℕ) (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) (Q : Binary.HomogeneousPoly (n + 1)) :
    leviStar χ (n + 1) epsP⁻¹ Q = binaryCoefficient n UpperHalfPlane.J Q := by
  have e : leviBlock epsP⁻¹ = (leviBlock epsP)⁻¹ := leviBlockHom.map_inv epsP
  show componentCharacter χ (epsP⁻¹).1 •
      Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock epsP⁻¹)) Q = _
  rw [hc, one_smul, e, leviBlock_epsP]
  have hJ : (UpperHalfPlane.J : BinaryRealGL)⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one]; exact upperJ_mul_self
  rw [hJ]
  rfl

/-- **The radical law for the reflection.** -/
theorem planeRadical_J (n : ℕ) (χ : RankOneCharacter) (hc : ∀ g : RealGL3, componentCharacter χ g = 1)
    (Y : RealGL3) (Q : Binary.HomogeneousPoly (n + 1)) :
    planeRadical n χ (iwP Y) (binaryCoefficient n UpperHalfPlane.J Q) =
      realCoefficientComponent n χ epsJ⁻¹ (planeRadical n χ (iwP (epsJ * Y)) Q) := by
  have h := planeRadical_iwP_mul (n := n) χ epsP Y Q
  rw [epsP_val] at h
  have h0 : planeRadical n χ epsP = 0 := planeRadical_levi_eq_zero n χ UpperHalfPlane.J 1
  rw [h0, LinearMap.zero_apply, zero_add, leviStar_epsP_inv n χ hc] at h
  rw [h]
  have : realCoefficientComponent n χ epsJ⁻¹ (realCoefficientComponent n χ epsJ
      (planeRadical n χ (iwP Y) (binaryCoefficient n UpperHalfPlane.J Q))) =
      planeRadical n χ (iwP Y) (binaryCoefficient n UpperHalfPlane.J Q) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [this]

theorem eichlerHolomorphic_J_iwA (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (Y : RealGL3) (h : BinaryAdelicGL) :
    eichlerHolomorphic n F (UpperHalfPlane.J * iwA Y) h = eichlerHolomorphic n F (iwA (epsJ * Y)) h := by
  obtain ⟨k, hk, he⟩ := leviBlock_iwP_mul epsP Y
  rw [leviBlock_epsP] at he
  rw [← he, eichlerHolomorphic_eq_smul, eichlerHolomorphic_eq_smul]
  unfold basePoint
  rw [mul_smul, orthogonal_smul_I k hk]
  rfl

theorem alpha_decomp {σ : CuspidalRepresentation} (n : ℕ) (E : LeviCocycleData σ n) (F : BinaryAdelicGL → ℂ → ℂ)
    (hE : ∀ A, E.α A = eichlerNormal n F A) (A : BinaryRealGL) (x : BinaryAdelicGL) :
    E.α A x = eichlerHolomorphic n F A x +
      binaryCoefficient n UpperHalfPlane.J (eichlerHolomorphic n F (UpperHalfPlane.J * A)
        (x * atInfinity UpperHalfPlane.J)) := by
  rw [hE, eichlerNormal_eq_add, eichlerAntiholomorphic_eq]
  congr 1
  exact binaryAmbientRepresentation_apply_of_unimodular (by rw [det_upperJ]; norm_num) _ _

/-- **The plane source splits into a holomorphic part at `g_∞` and a holomorphic-type part at `ε g_∞`**
(`ε = diag(-1,1,1)`), for the symmetrized Eichler cocycle. -/
theorem planeSourceAt_decomp (n : ℕ) (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (F : BinaryAdelicGL → ℂ → ℂ) (hE : ∀ A, E.α A = eichlerNormal n F A)
    (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) :
    (planeSourceAt D E y g x : HomogeneousPoly n) =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        (holInner n D.chi (cF D g) (fun A => eichlerHolomorphic n F A (x * bF g))
          (fun i => realGroup g * y i)) +
      realCoefficientComponent n D.chi (epsJ * realGroup g)⁻¹
        (holInner n D.chi (cF D g)
          (fun A => eichlerHolomorphic n F A (x * bF g * atInfinity UpperHalfPlane.J))
          (fun i => (epsJ * realGroup g) * y i)) := by
  set gR : RealGL3 := realGroup g with hgR
  set c : ℂ := cF D g with hcdef
  set Y : Fin 3 → RealGL3 := fun i => gR * y i with hY
  have hα : ∀ i, E.α (iwA (Y i)) (x * bF g) =
      eichlerHolomorphic n F (iwA (Y i)) (x * bF g) +
        binaryCoefficient n UpperHalfPlane.J (eichlerHolomorphic n F (iwA (epsJ * Y i))
          (x * bF g * atInfinity UpperHalfPlane.J)) := by
    intro i
    rw [alpha_decomp n E F hE, eichlerHolomorphic_J_iwA]
  set Qh : Binary.HomogeneousPoly (n + 1) := c • (eichlerHolomorphic n F (iwA (Y 1)) (x * bF g) -
    eichlerHolomorphic n F (iwA (Y 0)) (x * bF g)) with hQh
  set Q' : Binary.HomogeneousPoly (n + 1) := c • (eichlerHolomorphic n F (iwA (epsJ * Y 1))
    (x * bF g * atInfinity UpperHalfPlane.J) - eichlerHolomorphic n F (iwA (epsJ * Y 0))
    (x * bF g * atInfinity UpperHalfPlane.J)) with hQ'
  have hQ : c • (E.α (iwA (Y 1)) (x * bF g) - E.α (iwA (Y 0)) (x * bF g)) =
      Qh + binaryCoefficient n UpperHalfPlane.J Q' := by
    rw [hα 1, hα 0, hQh, hQ', map_smul, map_sub, ← smul_add]
    congr 1
    abel
  have hsrc : (planeSourceAt D E y g x : HomogeneousPoly n) = realCoefficientComponent n D.chi gR⁻¹
      ((planeRadical n D.chi (iwP (Y 2)) - planeRadical n D.chi (iwP (Y 1)))
        (c • (E.α (iwA (Y 1)) (x * bF g) - E.α (iwA (Y 0)) (x * bF g)))) := rfl
  have hε : (realCoefficientComponent n D.chi gR⁻¹) ((planeRadical n D.chi (iwP (Y 2)) -
      planeRadical n D.chi (iwP (Y 1))) (binaryCoefficient n UpperHalfPlane.J Q')) =
      realCoefficientComponent n D.chi (epsJ * gR)⁻¹ (holInner n D.chi c
        (fun A => eichlerHolomorphic n F A (x * bF g * atInfinity UpperHalfPlane.J))
        (fun i => (epsJ * gR) * y i)) := by
    have hY' : ∀ i, epsJ * Y i = (epsJ * gR) * y i := fun i => by simp only [hY, mul_assoc]
    rw [LinearMap.sub_apply, planeRadical_J n D.chi hc, planeRadical_J n D.chi hc, ← map_sub,
      ← LinearMap.sub_apply, _root_.mul_inv_rev, map_mul, Module.End.mul_apply]
    simp only [holInner, hY', hQ']
  have e1 : ((planeRadical n D.chi (iwP (Y 2)) - planeRadical n D.chi (iwP (Y 1)))
      (Qh + binaryCoefficient n UpperHalfPlane.J Q')) =
      holInner n D.chi c (fun A => eichlerHolomorphic n F A (x * bF g)) Y +
        (planeRadical n D.chi (iwP (Y 2)) - planeRadical n D.chi (iwP (Y 1)))
          (binaryCoefficient n UpperHalfPlane.J Q') := LinearMap.map_add _ _ _
  rw [hsrc, hQ, e1, map_add, hε]

/-- The vector potential of the holomorphic half of the Eichler normal form (times a scalar `c`). -/
def eichlerDatum (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) (h : BinaryAdelicGL) (c : ℂ) :
    PotentialDatum n (fun z => c * 2⁻¹ * F h z) where
  A z j := c * 2⁻¹ * (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F z h)
  hasDeriv z hz j := by
    have := (hasDerivAt_coord_eichlerPeriod F holomorphic hz h j).const_mul (c * 2⁻¹)
    refine this.congr_deriv ?_
    simp only [pointCoord]
    ring

theorem eichlerDatum_hpot (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) (h : BinaryAdelicGL) (c : ℂ)
    (A : BinaryRealGL) (j : Fin (n + 2)) :
    (eichlerDatum n F holomorphic h c).A (basePoint A) j =
      c * (binaryWeightBasis (n + 1)).coord j (eichlerHolomorphic n F A h) := by
  simp only [eichlerDatum, eichlerHolomorphic, map_smul, smul_eq_mul]
  ring

/-- **The plane source of the symmetrized Eichler cocycle, coefficientwise**: holomorphic part at `g_∞` plus
holomorphic-type part at `ε g_∞` (`ε = diag(-1,1,1)`, datum `x·b_F·J`), each equal to the corresponding plane integral
cochain minus its boundary combination. -/
theorem coeff_planeSourceAt_eichler (n : ℕ) (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (F : BinaryAdelicGL → ℂ → ℂ) (hE : ∀ A, E.α A = eichlerNormal n F A)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
    (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
    (hχ : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) (κ : Fin 3 →₀ ℕ) :
    ((planeSourceAt D E y g x : HomogeneousPoly n) : Poly).coeff κ =
      (planeIntG n (fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) * (cF D g * 2⁻¹ * F (x * bF g) z))
          (realGroup g).val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ -
        ∑ ν ∈ degSet n, (SeedC3.rho ((realGroup g).val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
          bdryCoeff (eichlerDatum n F holomorphic (x * bF g) (cF D g)) ν
            (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2))) +
      (planeIntG n (fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) *
            (cF D g * 2⁻¹ * F (x * bF g * atInfinity UpperHalfPlane.J) z))
          (epsJ * realGroup g).val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ -
        ∑ ν ∈ degSet n, (SeedC3.rho ((epsJ * realGroup g).val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
          bdryCoeff (eichlerDatum n F holomorphic (x * bF g * atInfinity UpperHalfPlane.J) (cF D g)) ν
            (gramOf ((epsJ * realGroup g) * y 0)) (gramOf ((epsJ * realGroup g) * y 1))
            (gramOf ((epsJ * realGroup g) * y 2))) := by
  rw [planeSourceAt_decomp n D E F hE hc y g x, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  congr 1
  · exact coeff_holSource_bridge n D.chi hχ (cF D g) (fun A => eichlerHolomorphic n F A (x * bF g))
      (realGroup g) y _ (eichlerDatum n F holomorphic (x * bF g) (cF D g))
      (eichlerDatum_hpot n F holomorphic (x * bF g) (cF D g))
      (continuousOn_const.mul (holomorphic _).continuousOn) κ
  · exact coeff_holSource_bridge n D.chi hχ (cF D g)
      (fun A => eichlerHolomorphic n F A (x * bF g * atInfinity UpperHalfPlane.J))
      (epsJ * realGroup g) y _ (eichlerDatum n F holomorphic (x * bF g * atInfinity UpperHalfPlane.J) (cF D g))
      (eichlerDatum_hpot n F holomorphic _ (cF D g))
      (continuousOn_const.mul (holomorphic _).continuousOn) κ

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
