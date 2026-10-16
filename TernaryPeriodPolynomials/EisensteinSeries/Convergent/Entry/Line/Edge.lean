module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.SourceAnti
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Edge
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RiemannCup
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.FromEdge
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.AntiCommute
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.PolyIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CochainEntry
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RationalNorm
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceFinal

@[expose] public section


/-!
# The edge cochain of the line source (R-b, line side)

Line analogue of `PlaneEdge`.  For the symmetrized twisted Eichler datum, `lineSource D E` is the line integral cochain
`cSigma` minus the coboundary of the edge cochain `lineEdge` (`cSigma_sub_lineSource`); the laws of `lineEdge` follow from
those of `lineSource` through Riemann sums (`tendsto_srcCupL`), and `sourceToSummand_cSigma_eq_lineSource` states that
`cSigma` and `lineSource` define the same class.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The coefficients of a line-type source are the line cup at the Gram matrices of the vertices, mixed by the
coefficients of `ρ(g_∞⁻¹)`. -/
theorem coeff_holInnerLine_cup (n : ℕ) (χ : RankOneCharacter)
    (hχ : ∀ t : ℝˣ, χ.toMonoidHom (realAdeleUnit t) = 1) (c : ℂ)
    (α : BinaryRealGL → Binary.HomogeneousPoly (n + 1)) (gR : RealGL3) (y : Fin 3 → RealGL3)
    (F : ℂ → ℂ) (P : PotentialDatum n F)
    (hpot : ∀ (A : BinaryRealGL) (j : Fin (n + 2)), P.A (basePoint A) j =
      c * (binaryWeightBasis (n + 1)).coord j (α A)) (κ : Fin 3 →₀ ℕ) :
    ((realCoefficientComponent n χ gR⁻¹
        (holInnerLine n χ c α (fun i => gR * y i)) : HomogeneousPoly n) : Poly).coeff κ =
      ∑ ν ∈ degSet n, cupCoeffLine P ν (gramOf (gR * y 0)) (gramOf (gR * y 1)) (gramOf (gR * y 2)) *
        (SeedC3.rho (gR.val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ := by
  set Y : Fin 3 → RealGL3 := fun i => gR * y i with hY
  set Γ' : Fin 3 → Mat3 := fun i => gramOf (Y i) with hΓ'
  set Q : Binary.HomogeneousPoly (n + 1) := c • (α (iwALine (Y 1)) - α (iwALine (Y 0))) with hQ
  set Φ : HomogeneousPoly n := (lineRadical n χ (iwPLine (Y 2)) - lineRadical n χ (iwPLine (Y 1))) Q with hΦ
  have hsrc : realCoefficientComponent n χ gR⁻¹ (holInnerLine n χ c α (fun i => gR * y i)) =
      realCoefficientComponent n χ gR⁻¹ Φ := rfl
  have hcoordQ : ∀ j, (binaryWeightBasis (n + 1)).coord j Q = P.aFunLine (Γ' 1) j - P.aFunLine (Γ' 0) j := by
    intro j
    have h1 : P.aFunLine (Γ' 1) j = c * (binaryWeightBasis (n + 1)).coord j (α (iwALine (Y 1))) := by
      rw [← hpot]
      exact (congrArg (fun z => P.A z j) (lineTauG_gramOf (Y 1))).trans (by rfl)
    have h0 : P.aFunLine (Γ' 0) j = c * (binaryWeightBasis (n + 1)).coord j (α (iwALine (Y 0))) := by
      rw [← hpot]
      exact (congrArg (fun z => P.A z j) (lineTauG_gramOf (Y 0))).trans (by rfl)
    rw [h1, h0, hQ]
    simp only [map_smul, map_sub, smul_eq_mul]
    ring
  have hΦc : ∀ ν, (Φ : Poly).coeff ν = cupCoeffLine P ν (Γ' 0) (Γ' 1) (Γ' 2) := by
    intro ν
    rw [hΦ, LinearMap.sub_apply, Submodule.coe_sub, MvPolynomial.coeff_sub, coeff_lineRadical_expand,
      coeff_lineRadical_expand, ← Finset.sum_sub_distrib, cupCoeffLine]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcoordQ]
    simp only [hΓ']
    ring
  rw [hsrc, rcc_inv_eq_rho n χ hχ gR]
  rw [coeff_rho_eq_sum _ n _ (fun m' hm' => coeff_eq_zero_of_sum_ne
      ((MvPolynomial.mem_homogeneousSubmodule n _).mp Φ.2) m' hm') κ]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [hΦc ν]

section LineEdge

variable {n : ℕ} (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
  (hol : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})

/-- The potential of the holomorphic half (line side). -/
def lineP1 (g : AdelicGL) : PotentialDatum n (fun z => cFLine D g * 2⁻¹ * F (1 * bFLine g) z) :=
  eichlerDatum n F hol (1 * bFLine g) (cFLine D g)

/-- The potential of the reflected half (line side, adele `b_F J_∞`). -/
def lineP2 (g : AdelicGL) :
    PotentialDatum n (fun z => cFLine D g * 2⁻¹ * F (1 * bFLine g * atInfinity UpperHalfPlane.J) z) :=
  eichlerDatum n F hol (1 * bFLine g * atInfinity UpperHalfPlane.J) (cFLine D g)

/-- The line cup of a potential and the radical at three Gram matrices, mixed by `ρ(M)⁻¹`. -/
def cupAtL {F' : ℂ → ℂ} (P : PotentialDatum n F') (M : Mat3) (Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) : ℂ :=
  ∑ ν ∈ degSet n, cupCoeffLine P ν Γ₀ Γ₁ Γ₂ * (SeedC3.rho M⁻¹ (MvPolynomial.monomial ν 1)).coeff κ

/-- The line edge integral of a potential and the radical between two Gram matrices, mixed by `ρ(M)⁻¹`. -/
def edgeAtL {F' : ℂ → ℂ} (P : PotentialDatum n F') (M : Mat3) (Γa Γb : Mat3) (κ : Fin 3 →₀ ℕ) : ℂ :=
  ∑ ν ∈ degSet n, cupEdge (PotentialDatum.dotPairing (n + 2)) P.aFunLine (lFunLine n ν) Γa Γb *
    (SeedC3.rho M⁻¹ (MvPolynomial.monomial ν 1)).coeff κ

/-- The reflection of a Gram matrix by `Λ = diag(1,-1,1)`. -/
def lamGram (Γ : Mat3) : Mat3 := lamM * Γ * lamM.transpose

/-- The coefficient `κ` of the line source at three Gram matrices (holomorphic part plus reflected part). -/
def srcCupL (g : AdelicGL) (Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) : ℂ :=
  cupAtL (lineP1 D F hol g) (realGroup g).val Γ₀ Γ₁ Γ₂ κ +
  cupAtL (lineP2 D F hol g) (lamL * realGroup g).val (lamGram Γ₀) (lamGram Γ₁) (lamGram Γ₂) κ

/-- The coefficient `κ` of the line edge cochain (holomorphic part plus reflected part). -/
def srcEdgeL (g : AdelicGL) (Γa Γb : Mat3) (κ : Fin 3 →₀ ℕ) : ℂ :=
  edgeAtL (lineP1 D F hol g) (realGroup g).val Γa Γb κ +
  edgeAtL (lineP2 D F hol g) (lamL * realGroup g).val (lamGram Γa) (lamGram Γb) κ

theorem gramOf_lam_mul (Y : RealGL3) : gramOf (lamL * Y) = lamGram (gramOf Y) := by
  rw [gramOf_mul, lamL_val]; rfl

theorem coeff_lineSourceAt_srcCupL (E : LineLeviCocycleData D.cusp n)
    (hE : ∀ A, E.α A = eichlerNormalTw n F A)
    (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
    (hχ : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (κ : Fin 3 →₀ ℕ) :
    ((lineSourceAt D E y g 1 : HomogeneousPoly n) : Poly).coeff κ =
      srcCupL D F hol g (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1))
        (gramOf (realGroup g * y 2)) κ := by
  rw [lineSourceAt_decomp n D E F hE hc y g 1, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    coeff_holInnerLine_cup n D.chi hχ (cFLine D g) (fun A => eichlerHolomorphic n F A (1 * bFLine g))
      (realGroup g) y _ (lineP1 D F hol g) (eichlerDatum_hpot n F hol (1 * bFLine g) (cFLine D g)) κ,
    coeff_holInnerLine_cup n D.chi hχ (cFLine D g)
      (fun A => eichlerHolomorphic n F A (1 * bFLine g * atInfinity UpperHalfPlane.J))
      (lamL * realGroup g) y _ (lineP2 D F hol g)
      (eichlerDatum_hpot n F hol (1 * bFLine g * atInfinity UpperHalfPlane.J) (cFLine D g)) κ]
  have e : ∀ k, gramOf ((lamL * realGroup g) * y k) = lamGram (gramOf (realGroup g * y k)) := fun k => by
    rw [mul_assoc, gramOf_lam_mul]
  rw [e 0, e 1, e 2]
  rfl

theorem posDef_lamGram {Γ : Mat3} (h : Γ.PosDef) : (lamGram Γ).PosDef :=
  posDef_congr h (by simpa [lamL_val] using det_ne_zero_realGL3 lamL)

theorem lamGram_segment (Γa Γb : Mat3) (t : ℝ) :
    lamGram (Γa + t • (Γb - Γa)) = lamGram Γa + t • (lamGram Γb - lamGram Γa) := by
  unfold lamGram
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

theorem segment_mem_lineDomain {Γa Γb : Mat3} (ha : Γa.PosDef) (hb : Γb.PosDef) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : Γa + t • (Γb - Γa) ∈ lineDomain :=
  cholDomain_subset_lineDomain (posDef_transpose (segment_posDef ha hb ht))
    (posDef_mem_cholDomain (segment_posDef ha hb ht))

theorem cupCoeffLine_eq_dot {F' : ℂ → ℂ} (P : PotentialDatum n F') (ν : Fin 3 →₀ ℕ) (Γ₀ Γ₁ Γ₂ : Mat3) :
    cupCoeffLine P ν Γ₀ Γ₁ Γ₂ = PotentialDatum.dotPairing (n + 2) (P.aFunLine Γ₁ - P.aFunLine Γ₀)
      (lFunLine n ν Γ₂ - lFunLine n ν Γ₁) := by
  rw [PotentialDatum.dotPairing_apply]
  rfl

theorem tendsto_cupAtL {F' : ℂ → ℂ} (P : PotentialDatum n F') (M : Mat3) {Γa Γb : Mat3} (ha : Γa.PosDef)
    (hb : Γb.PosDef) (κ : Fin 3 →₀ ℕ) :
    Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      cupAtL P M Γa (Γa + ((i : ℝ) / N) • (Γb - Γa)) (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) κ)
      Filter.atTop (nhds (edgeAtL P M Γa Γb κ)) := by
  unfold cupAtL edgeAtL
  simp_rw [Finset.sum_comm (s := Finset.range _) (t := degSet n)]
  refine tendsto_finsetSum _ fun ν _ => ?_
  simp_rw [← Finset.sum_mul]
  refine Filter.Tendsto.mul_const _ ?_
  simp_rw [cupCoeffLine_eq_dot]
  exact tendsto_cupEdge (PotentialDatum.dotPairing (n + 2)) P.aFunLine (lFunLine n ν) lineDomain isOpen_lineDomain
    (P.contDiffOn_aFunLine.continuousOn)
    ((contDiffOn_lFunLine n ν).of_le (by simp)) Γa Γb (fun t ht => segment_mem_lineDomain ha hb ht)

theorem tendsto_srcCupL (g : AdelicGL) {Γa Γb : Mat3} (ha : Γa.PosDef) (hb : Γb.PosDef) (κ : Fin 3 →₀ ℕ) :
    Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      srcCupL D F hol g Γa (Γa + ((i : ℝ) / N) • (Γb - Γa)) (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) κ)
      Filter.atTop (nhds (srcEdgeL D F hol g Γa Γb κ)) := by
  unfold srcCupL srcEdgeL
  simp_rw [Finset.sum_add_distrib]
  refine Filter.Tendsto.add (tendsto_cupAtL (lineP1 D F hol g) _ ha hb κ) ?_
  simp_rw [lamGram_segment]
  exact tendsto_cupAtL (lineP2 D F hol g) _ (posDef_lamGram ha) (posDef_lamGram hb) κ

theorem bdry_sumL {F' : ℂ → ℂ} (P : PotentialDatum n F') (M : Mat3) (Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) :
    ∑ ν ∈ degSet n, (SeedC3.rho M⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
      bdryCoeffLine P ν Γ₀ Γ₁ Γ₂ =
    edgeAtL P M Γ₁ Γ₂ κ - edgeAtL P M Γ₀ Γ₂ κ + edgeAtL P M Γ₀ Γ₁ κ := by
  unfold edgeAtL bdryCoeffLine
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_comm]

theorem bFLine_atInfinity_comm (g : AdelicGL) :
    1 * bFLine g * atInfinity UpperHalfPlane.J = atInfinity UpperHalfPlane.J * bFLine g := by
  rw [one_mul]
  exact atFinite_mul_atInfinity_comm _ _

section Laws

variable (E : LineLeviCocycleData D.cusp n) (hE : ∀ A, E.α A = eichlerNormalTw n F A)
  (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)

include hE hc hχ

/-- Right invariance of the cup under the finite level. -/
theorem srcCupL_level (k : finiteLevel) (g : AdelicGL) {Γ₀ Γ₁ Γ₂ : Mat3} (h₀ : Γ₀.PosDef) (h₁ : Γ₁.PosDef)
    (h₂ : Γ₂.PosDef) (κ : Fin 3 →₀ ℕ) :
    srcCupL D F hol (g * atFinite k.val) Γ₀ Γ₁ Γ₂ κ = srcCupL D F hol g Γ₀ Γ₁ Γ₂ κ := by
  obtain ⟨y, e₀, e₁, e₂⟩ := exists_vertices (realGroup g) h₀ h₁ h₂
  have hχ' : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1 := character_real_eq_one D.chi hχ
  have A := coeff_lineSourceAt_srcCupL D F hol E hE hc hχ' y g κ
  have B := coeff_lineSourceAt_srcCupL D F hol E hE hc hχ' y (g * atFinite k.val) κ
  rw [realGroup_mul_atFinite, e₀, e₁, e₂] at B
  rw [e₀, e₁, e₂] at A
  rw [← A, ← B, lineSourceAt_level D E hχ g k y 1]

/-- Invariance of the cup under the rational line parabolic. -/
theorem srcCupL_parabolic (p : RationalGL3) (hp : p ∈ parabolic Side.line) (g : AdelicGL) {Γ₀ Γ₁ Γ₂ : Mat3}
    (h₀ : Γ₀.PosDef) (h₁ : Γ₁.PosDef) (h₂ : Γ₂.PosDef) (κ : Fin 3 →₀ ℕ) :
    srcCupL D F hol (rationalGroup p * g)
      ((realGroup (rationalGroup p)).val * Γ₀ * (realGroup (rationalGroup p)).val.transpose)
      ((realGroup (rationalGroup p)).val * Γ₁ * (realGroup (rationalGroup p)).val.transpose)
      ((realGroup (rationalGroup p)).val * Γ₂ * (realGroup (rationalGroup p)).val.transpose) κ =
    srcCupL D F hol g Γ₀ Γ₁ Γ₂ κ := by
  obtain ⟨y, e₀, e₁, e₂⟩ := exists_vertices (realGroup g) h₀ h₁ h₂
  have hχ' : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1 := character_real_eq_one D.chi hχ
  have A := coeff_lineSourceAt_srcCupL D F hol E hE hc hχ' y g κ
  have B := coeff_lineSourceAt_srcCupL D F hol E hE hc hχ' y (rationalGroup p * g) κ
  rw [e₀, e₁, e₂] at A
  have hg : ∀ k, gramOf (realGroup (rationalGroup p * g) * y k) =
      (realGroup (rationalGroup p)).val * gramOf (realGroup g * y k) *
        (realGroup (rationalGroup p)).val.transpose := by
    intro k
    rw [map_mul, mul_assoc, gramOf_mul]
  rw [hg 0, hg 1, hg 2, e₀, e₁, e₂] at B
  rw [← A, ← B]
  have hS := lineSource_isSourceCocycle D E hχ
  have := RationalComparison.source_parabolicInvariant D RationalNorm.rational_norm Side.line
    (lineSource D E) hS p hp y (g)
  exact congrArg (fun P : HomogeneousPoly n => (P : Poly).coeff κ) this

/-- The line source is the polynomial with the cup coefficients. -/
theorem lineSourceAt_eq_ofCoeffs (y : Fin 3 → RealGL3) (g : AdelicGL) :
    lineSourceAt D E y g 1 = ofCoeffs n (srcCupL D F hol g (gramOf (realGroup g * y 0))
      (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2))) := by
  have hχ' : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1 := character_real_eq_one D.chi hχ
  conv_lhs => rw [eq_ofCoeffs n (lineSourceAt D E y g 1)]
  congr 1
  funext κ
  exact coeff_lineSourceAt_srcCupL D F hol E hE hc hχ' y g κ

/-- Covariance of the cup under `GL₃(ℝ)`. -/
theorem srcCupL_cov (h : RealGL3) (g : AdelicGL) {Γ₀ Γ₁ Γ₂ : Mat3} (h₀ : Γ₀.PosDef) (h₁ : Γ₁.PosDef)
    (h₂ : Γ₂.PosDef) :
    ofCoeffs n (srcCupL D F hol g Γ₀ Γ₁ Γ₂) =
      realCoefficientComponent n D.chi h (ofCoeffs n (srcCupL D F hol (g * atInfinity h) Γ₀ Γ₁ Γ₂)) := by
  obtain ⟨y, e₀, e₁, e₂⟩ := exists_vertices (realGroup g * h) h₀ h₁ h₂
  have hS := lineSource_isSourceCocycle D E hχ
  have key := hS.2.2.1 h y g
  have hz : ∀ k, gramOf (realGroup g * (h * y k)) = gramOf ((realGroup g * h) * y k) := fun k => by
    rw [mul_assoc]
  have A := lineSourceAt_eq_ofCoeffs D F hol E hE hc hχ (fun i => h * y i) g
  have B := lineSourceAt_eq_ofCoeffs D F hol E hE hc hχ y (g * atInfinity h)
  rw [realGroup_mul_atInfinity, e₀, e₁, e₂] at B
  simp only [hz, e₀, e₁, e₂] at A
  change lineSourceAt D E (fun i => h * y i) g 1 = _ at key
  rw [← A, ← B]
  exact key

end Laws


theorem srcEdgeL_congr (g g' : AdelicGL) {Γa Γb Γa' Γb' : Mat3} (ha : Γa.PosDef) (hb : Γb.PosDef)
    (ha' : Γa'.PosDef) (hb' : Γb'.PosDef) (κ : Fin 3 →₀ ℕ)
    (hcup : ∀ N : ℕ, ∀ i < N,
      srcCupL D F hol g' Γa' (Γa' + ((i : ℝ) / N) • (Γb' - Γa')) (Γa' + (((i : ℝ) + 1) / N) • (Γb' - Γa')) κ =
      srcCupL D F hol g Γa (Γa + ((i : ℝ) / N) • (Γb - Γa)) (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) κ) :
    srcEdgeL D F hol g' Γa' Γb' κ = srcEdgeL D F hol g Γa Γb κ := by
  refine tendsto_nhds_unique (tendsto_srcCupL D F hol g' ha' hb' κ) ?_
  refine (tendsto_srcCupL D F hol g ha hb κ).congr fun N => ?_
  exact (Finset.sum_congr rfl fun i hi => (hcup N i (Finset.mem_range.mp hi)).symm)


/-- The edge cochain of the line source. -/
def lineEdge (y : Fin 2 → RealGL3) (g : AdelicGL) : HomogeneousPoly n :=
  ofCoeffs n (srcEdgeL D F hol g (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)))


theorem lineEdge_coeff (y : Fin 2 → RealGL3) (g : AdelicGL) (κ : Fin 3 →₀ ℕ) :
    ((lineEdge D F hol y g : HomogeneousPoly n) : Poly).coeff κ =
      if κ.degree = n then srcEdgeL D F hol g (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)) κ
      else 0 := coeff_ofCoeffs n _ κ


section EdgeLaws

variable (E : LineLeviCocycleData D.cusp n) (hE : ∀ A, E.α A = eichlerNormalTw n F A)
  (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)

include hol hE hc hχ


theorem lineEdge_level (k : finiteLevel) (y : Fin 2 → RealGL3) (g : AdelicGL) :
    lineEdge D F hol y (g * atFinite k.val) = lineEdge D F hol y g := by
  unfold lineEdge
  rw [realGroup_mul_atFinite]
  congr 1
  funext κ
  have ha := posDef_gramOf (realGroup g * y 0)
  have hb := posDef_gramOf (realGroup g * y 1)
  refine srcEdgeL_congr D F hol _ _ ha hb ha hb κ (fun N i hi => ?_)
  obtain ⟨m0, m1⟩ := seg_mem N i hi
  exact srcCupL_level D F hol E hE hc hχ k g ha (segment_posDef ha hb m0) (segment_posDef ha hb m1) κ


theorem lineEdge_parabolic (p : RationalGL3) (hp : p ∈ parabolic Side.line) (y : Fin 2 → RealGL3)
    (g : AdelicGL) : lineEdge D F hol y (rationalGroup p * g) = lineEdge D F hol y g := by
  unfold lineEdge
  have hg : ∀ k, gramOf (realGroup (rationalGroup p * g) * y k) =
      (realGroup (rationalGroup p)).val * gramOf (realGroup g * y k) *
        (realGroup (rationalGroup p)).val.transpose := by
    intro k
    rw [map_mul, mul_assoc, gramOf_mul]
  rw [hg 0, hg 1]
  congr 1
  funext κ
  have ha := posDef_gramOf (realGroup g * y 0)
  have hb := posDef_gramOf (realGroup g * y 1)
  refine srcEdgeL_congr D F hol _ _ ha hb (posDef_congr ha (det_ne_zero_realGL3 _))
    (posDef_congr hb (det_ne_zero_realGL3 _)) κ (fun N i hi => ?_)
  obtain ⟨m0, m1⟩ := seg_mem N i hi
  rw [conj_segment, conj_segment]
  exact srcCupL_parabolic D F hol E hE hc hχ p hp g ha (segment_posDef ha hb m0) (segment_posDef ha hb m1) κ




theorem lineEdge_cov (h : RealGL3) (y : Fin 2 → RealGL3) (g : AdelicGL) :
    lineEdge D F hol (fun i => h * y i) g =
      realCoefficientComponent n D.chi h (lineEdge D F hol y (g * atInfinity h)) := by
  unfold lineEdge
  have hg : ∀ k, gramOf (realGroup g * (h * y k)) = gramOf (realGroup (g * atInfinity h) * y k) := fun k => by
    rw [realGroup_mul_atInfinity, mul_assoc]
  simp only [hg]
  have ha := posDef_gramOf (realGroup (g * atInfinity h) * y 0)
  have hb := posDef_gramOf (realGroup (g * atInfinity h) * y 1)
  set Γa := gramOf (realGroup (g * atInfinity h) * y 0)
  set Γb := gramOf (realGroup (g * atInfinity h) * y 1)
  set Λ := realCoefficientComponent n D.chi h
  refine ofCoeffs_linear Λ _ _ (fun κ hκ => ?_)
  have hcup : ∀ N i : ℕ, i < N → srcCupL D F hol g Γa (Γa + ((i : ℝ) / N) • (Γb - Γa))
      (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) κ = ∑ ν ∈ degMonomials n,
      srcCupL D F hol (g * atInfinity h) Γa (Γa + ((i : ℝ) / N) • (Γb - Γa))
        (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) ν *
        ((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ := by
    intro N i hi
    obtain ⟨m0, m1⟩ := seg_mem N i hi
    exact coeffs_of_ofCoeffs_linear Λ _ _ (srcCupL_cov D F hol E hE hc hχ h g ha (segment_posDef ha hb m0)
      (segment_posDef ha hb m1)) κ hκ
  have hlim := tendsto_finsetSum (degMonomials n) fun ν _ =>
    (tendsto_srcCupL D F hol (g * atInfinity h) ha hb ν).mul_const
      (((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ)
  have hlim' : Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      srcCupL D F hol g Γa (Γa + ((i : ℝ) / N) • (Γb - Γa)) (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) κ)
      Filter.atTop (nhds (∑ ν ∈ degMonomials n, srcEdgeL D F hol (g * atInfinity h) Γa Γb ν *
        ((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ)) := by
    refine hlim.congr fun N => ?_
    calc _ = ∑ ν ∈ degMonomials n, ∑ i ∈ Finset.range N,
          srcCupL D F hol (g * atInfinity h) Γa (Γa + ((i : ℝ) / N) • (Γb - Γa))
            (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) ν *
            ((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ := by
          simp_rw [Finset.sum_mul]
      _ = ∑ i ∈ Finset.range N, ∑ ν ∈ degMonomials n,
          srcCupL D F hol (g * atInfinity h) Γa (Γa + ((i : ℝ) / N) • (Γb - Γa))
            (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) ν *
            ((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i hi => (hcup N i (Finset.mem_range.mp hi)).symm
  exact tendsto_nhds_unique (tendsto_srcCupL D F hol g ha hb κ) hlim'


theorem coeff_lineSourceAt_edge (y : Fin 3 → RealGL3) (g : AdelicGL) (κ : Fin 3 →₀ ℕ) :
    ((lineSourceAt D E y g 1 : HomogeneousPoly n) : Poly).coeff κ =
      cSigmaCoeff n D F y g κ -
        (srcEdgeL D F hol g (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2)) κ -
          srcEdgeL D F hol g (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 2)) κ +
          srcEdgeL D F hol g (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)) κ) := by
  have hχ' : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1 := character_real_eq_one D.chi hχ
  rw [coeff_lineSourceAt_eichlerTw n D E F hE hol hc hχ' y g 1 κ]
  have e : ∀ k, gramOf ((lamL * realGroup g) * y k) = lamGram (gramOf (realGroup g * y k)) := fun k => by
    rw [mul_assoc, gramOf_lam_mul]
  rw [e 0, e 1, e 2]
  have hp2 : lineHolData n D F g (atInfinity UpperHalfPlane.J) =
      fun z => (-1) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) *
        (cFLine D g * 2⁻¹ * F (1 * bFLine g * atInfinity UpperHalfPlane.J) z) := by
    funext z; unfold lineHolData; rw [bFLine_atInfinity_comm]
  have hmul : (lamL * realGroup g).val = lamM * (realGroup g).val := by
    rw [Units.val_mul, lamL_val]
  have b1 : ∑ ν ∈ degSet n, (SeedC3.rho ((realGroup g).val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
      bdryCoeffLine (eichlerDatum n F hol (1 * bFLine g) (cFLine D g)) ν (gramOf (realGroup g * y 0))
        (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2)) =
      edgeAtL (lineP1 D F hol g) (realGroup g).val (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2)) κ -
        edgeAtL (lineP1 D F hol g) (realGroup g).val (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 2)) κ +
        edgeAtL (lineP1 D F hol g) (realGroup g).val (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)) κ :=
    bdry_sumL (lineP1 D F hol g) (realGroup g).val _ _ _ κ
  have b2 : ∑ ν ∈ degSet n, (SeedC3.rho ((lamL * realGroup g).val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
      bdryCoeffLine (eichlerDatum n F hol (1 * bFLine g * atInfinity UpperHalfPlane.J) (cFLine D g)) ν
        (lamGram (gramOf (realGroup g * y 0))) (lamGram (gramOf (realGroup g * y 1)))
        (lamGram (gramOf (realGroup g * y 2))) =
      edgeAtL (lineP2 D F hol g) (lamL * realGroup g).val (lamGram (gramOf (realGroup g * y 1)))
          (lamGram (gramOf (realGroup g * y 2))) κ -
        edgeAtL (lineP2 D F hol g) (lamL * realGroup g).val (lamGram (gramOf (realGroup g * y 0)))
          (lamGram (gramOf (realGroup g * y 2))) κ +
        edgeAtL (lineP2 D F hol g) (lamL * realGroup g).val (lamGram (gramOf (realGroup g * y 0)))
          (lamGram (gramOf (realGroup g * y 1))) κ :=
    bdry_sumL (lineP2 D F hol g) (lamL * realGroup g).val _ _ _ κ
  have hp1 : lineHolData n D F g 1 = fun z => (-1) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) *
      (cFLine D g * 2⁻¹ * F (1 * bFLine g) z) := rfl
  unfold cSigmaCoeff srcEdgeL
  rw [hp1, hp2, ← hmul, b1, b2]
  ring

theorem cSigma_sub_lineSource (y : Fin 3 → RealGL3) (g : AdelicGL) :
    cSigma n D F y g - lineSource D E y g =
      lineEdge D F hol ![y 1, y 2] g - lineEdge D F hol ![y 0, y 2] g + lineEdge D F hol ![y 0, y 1] g := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro κ
  simp only [Submodule.coe_sub, Submodule.coe_add, MvPolynomial.coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    cSigma, lineEdge_coeff, coeff_ofCoeffs]
  by_cases hκ : κ.degree = n
  · simp only [ite_eq_left hκ]
    have h := coeff_lineSourceAt_edge D F hol E hE hc hχ y g κ
    have h' : ((lineSource D E y g : HomogeneousPoly n) : Poly).coeff κ =
        ((lineSourceAt D E y g 1 : HomogeneousPoly n) : Poly).coeff κ := rfl
    rw [h', h]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp only [ite_eq_right hκ]
    have h0 : ((lineSource D E y g : HomogeneousPoly n) : Poly).coeff κ = 0 :=
      ((MvPolynomial.mem_homogeneousSubmodule n _).mp (lineSource D E y g).2).coeff_eq_zero hκ
    rw [h0]
    ring

theorem sourceToSummand_cSigma_eq_lineSource
    (hSig : IsSourceCocycle D Side.line (fun y g => cSigma n D F y g)) :
    SourceQuotient.sourceToSummand D Side.line ⟨fun y g => cSigma n D F y g, hSig⟩ =
      SourceQuotient.sourceToSummand D Side.line ⟨lineSource D E, lineSource_isSourceCocycle D E hχ⟩ :=
  sourceToSummand_eq_of_edge D Side.line _ _ hSig (lineSource_isSourceCocycle D E hχ)
    (lineEdge D F hol)
    (fun y g => cSigma_sub_lineSource D F hol E hE hc hχ y g)
    (fun h y g => lineEdge_cov D F hol E hE hc hχ h y g)
    (fun k y g => lineEdge_level D F hol E hE hc hχ k y g)
    (fun p hp y g => lineEdge_parabolic D F hol E hE hc hχ p hp y g)

end EdgeLaws

end LineEdge

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
