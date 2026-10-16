module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.SourceAnti
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RiemannCup
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.FromEdge
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.AntiCommute
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.PolyIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CochainEntry
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RationalNorm
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceFinal

@[expose] public section


/-!
# The edge cochain of the plane source (R-b, plane side)

For the symmetrized Eichler datum, the plane source `planeSource D E` is the integral cochain `cOmega` minus the
coboundary of the edge cochain `planeEdge` (`cOmega_sub_planeSource`), where `planeEdge y g` has coefficients
`srcEdge`, the edge integral `cupEdge` of the potentials and the radical along the Gram segment (holomorphic part plus
reflected part).  The invariance laws of `planeEdge` (covariance, finite level, rational plane parabolic) are
derived from the library's laws of `planeSource` through Riemann sums: the Riemann sums of the cup along the Gram
segment converge to the edge integral (`tendsto_srcCup`) and each term is a value of the plane source at a suitable
triple of vertices (`coeff_planeSourceAt_srcCup`, `exists_vertices`).  With `sourceToSummand_eq_of_edge` this gives
`sourceToSummand_cOmega_eq_planeSource`: `cOmega` and `planeSource` define the same class.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The coefficients of a plane-type source are the cup at the Gram matrices of the vertices, mixed by the coefficients
of `ρ(g_∞⁻¹)`. -/
theorem coeff_holInner_cup (n : ℕ) (χ : RankOneCharacter)
    (hχ : ∀ t : ℝˣ, χ.toMonoidHom (realAdeleUnit t) = 1) (c : ℂ)
    (α : BinaryRealGL → Binary.HomogeneousPoly (n + 1)) (gR : RealGL3) (y : Fin 3 → RealGL3)
    (F : ℂ → ℂ) (P : PotentialDatum n F)
    (hpot : ∀ (A : BinaryRealGL) (j : Fin (n + 2)), P.A (basePoint A) j =
      c * (binaryWeightBasis (n + 1)).coord j (α A)) (κ : Fin 3 →₀ ℕ) :
    ((realCoefficientComponent n χ gR⁻¹
        (holInner n χ c α (fun i => gR * y i)) : HomogeneousPoly n) : Poly).coeff κ =
      ∑ ν ∈ degSet n, cupCoeff P ν (gramOf (gR * y 0)) (gramOf (gR * y 1)) (gramOf (gR * y 2)) *
        (SeedC3.rho (gR.val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ := by
  set Y : Fin 3 → RealGL3 := fun i => gR * y i with hY
  set Γ' : Fin 3 → Mat3 := fun i => gramOf (Y i) with hΓ'
  set Q : Binary.HomogeneousPoly (n + 1) := c • (α (iwA (Y 1)) - α (iwA (Y 0))) with hQ
  set Φ : HomogeneousPoly n := (planeRadical n χ (iwP (Y 2)) - planeRadical n χ (iwP (Y 1))) Q with hΦ
  have hsrc : realCoefficientComponent n χ gR⁻¹ (holInner n χ c α (fun i => gR * y i)) =
      realCoefficientComponent n χ gR⁻¹ Φ := rfl
  have hcoordQ : ∀ j, (binaryWeightBasis (n + 1)).coord j Q = P.aFun (Γ' 1) j - P.aFun (Γ' 0) j := by
    intro j
    have h1 : P.aFun (Γ' 1) j = c * (binaryWeightBasis (n + 1)).coord j (α (iwA (Y 1))) := by
      rw [← hpot]
      exact (congrArg (fun z => P.A z j) (basePoint_iwA (Y 1))).symm
    have h0 : P.aFun (Γ' 0) j = c * (binaryWeightBasis (n + 1)).coord j (α (iwA (Y 0))) := by
      rw [← hpot]
      exact (congrArg (fun z => P.A z j) (basePoint_iwA (Y 0))).symm
    rw [h1, h0, hQ]
    simp only [map_smul, map_sub, smul_eq_mul]
    ring
  have hΦc : ∀ ν, (Φ : Poly).coeff ν = cupCoeff P ν (Γ' 0) (Γ' 1) (Γ' 2) := by
    intro ν
    rw [hΦ, LinearMap.sub_apply, Submodule.coe_sub, MvPolynomial.coeff_sub, coeff_planeRadical_expand,
      coeff_planeRadical_expand, ← Finset.sum_sub_distrib, cupCoeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcoordQ]
    simp only [hΓ', gramOf]
    ring
  rw [hsrc, rcc_inv_eq_rho n χ hχ gR]
  rw [coeff_rho_eq_sum _ n _ (fun m' hm' => coeff_eq_zero_of_sum_ne
      ((MvPolynomial.mem_homogeneousSubmodule n _).mp Φ.2) m' hm') κ]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [hΦc ν]

/-- A linear endomorphism applied to a polynomial with prescribed coefficients, coefficientwise. -/
theorem ofCoeffs_linear {n : ℕ} (Λ : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n) (f f' : (Fin 3 →₀ ℕ) → ℂ)
    (hff : ∀ κ : Fin 3 →₀ ℕ, κ.degree = n →
      f κ = ∑ ν ∈ degMonomials n, f' ν * ((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ) :
    ofCoeffs n f = Λ (ofCoeffs n f') := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro κ
  rw [coeff_ofCoeffs]
  by_cases hκ : κ.degree = n
  · rw [ite_eq_left hκ, hff κ hκ, coeff_linear]
    refine Finset.sum_congr rfl fun ν hν => ?_
    rw [coeff_ofCoeffs, ite_eq_left (mem_degMonomials.mp hν)]
  · rw [ite_eq_right hκ]
    exact ((MvPolynomial.mem_homogeneousSubmodule n _).mp (Λ (ofCoeffs n f')).2).coeff_eq_zero hκ |>.symm

theorem coeffs_of_ofCoeffs_linear {n : ℕ} (Λ : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n)
    (f f' : (Fin 3 →₀ ℕ) → ℂ) (h : ofCoeffs n f = Λ (ofCoeffs n f')) (κ : Fin 3 →₀ ℕ)
    (hκ : κ.degree = n) :
    f κ = ∑ ν ∈ degMonomials n, f' ν * ((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ := by
  have := congrArg (fun P : HomogeneousPoly n => (P : Poly).coeff κ) h
  rw [coeff_ofCoeffs, ite_eq_left hκ, coeff_linear] at this
  rw [this]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [coeff_ofCoeffs, ite_eq_left (mem_degMonomials.mp hν)]

section PlaneEdge

variable {n : ℕ} (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
  (hol : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})

/-- The potential of the holomorphic half. -/
def planeP1 (g : AdelicGL) : PotentialDatum n (fun z => cF D g * 2⁻¹ * F (1 * bF g) z) :=
  eichlerDatum n F hol (1 * bF g) (cF D g)

/-- The potential of the reflected half (adele `b_F J_∞`). -/
def planeP2 (g : AdelicGL) :
    PotentialDatum n (fun z => cF D g * 2⁻¹ * F (1 * bF g * atInfinity UpperHalfPlane.J) z) :=
  eichlerDatum n F hol (1 * bF g * atInfinity UpperHalfPlane.J) (cF D g)

/-- The cup of a potential and the radical at three Gram matrices, mixed by `ρ(M)⁻¹`. -/
def cupAt {F' : ℂ → ℂ} (P : PotentialDatum n F') (M : Mat3) (Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) : ℂ :=
  ∑ ν ∈ degSet n, cupCoeff P ν Γ₀ Γ₁ Γ₂ * (SeedC3.rho M⁻¹ (MvPolynomial.monomial ν 1)).coeff κ

/-- The edge integral of a potential and the radical between two Gram matrices, mixed by `ρ(M)⁻¹`. -/
def edgeAt {F' : ℂ → ℂ} (P : PotentialDatum n F') (M : Mat3) (Γa Γb : Mat3) (κ : Fin 3 →₀ ℕ) : ℂ :=
  ∑ ν ∈ degSet n, cupEdge (PotentialDatum.dotPairing (n + 2)) P.aFun (lFun n ν) Γa Γb *
    (SeedC3.rho M⁻¹ (MvPolynomial.monomial ν 1)).coeff κ

/-- The reflection of a Gram matrix by `ε = diag(-1,1,1)`. -/
def epsGram (Γ : Mat3) : Mat3 := epsJ.val * Γ * epsJ.val.transpose

/-- The coefficient `κ` of the plane source at three Gram matrices (coefficientwise cup, holomorphic part plus
reflected part). -/
def srcCup (g : AdelicGL) (Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) : ℂ :=
  cupAt (planeP1 D F hol g) (realGroup g).val Γ₀ Γ₁ Γ₂ κ +
  cupAt (planeP2 D F hol g) (epsJ * realGroup g).val (epsGram Γ₀) (epsGram Γ₁) (epsGram Γ₂) κ

/-- The coefficient `κ` of the edge cochain (holomorphic part plus reflected part). -/
def srcEdge (g : AdelicGL) (Γa Γb : Mat3) (κ : Fin 3 →₀ ℕ) : ℂ :=
  edgeAt (planeP1 D F hol g) (realGroup g).val Γa Γb κ +
  edgeAt (planeP2 D F hol g) (epsJ * realGroup g).val (epsGram Γa) (epsGram Γb) κ

theorem gramOf_eps_mul (Y : RealGL3) : gramOf (epsJ * Y) = epsGram (gramOf Y) := gramOf_mul epsJ Y

theorem coeff_planeSourceAt_srcCup (E : LeviCocycleData D.cusp n) (hE : ∀ A, E.α A = eichlerNormal n F A)
    (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
    (hχ : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (κ : Fin 3 →₀ ℕ) :
    ((planeSourceAt D E y g 1 : HomogeneousPoly n) : Poly).coeff κ =
      srcCup D F hol g (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1))
        (gramOf (realGroup g * y 2)) κ := by
  rw [planeSourceAt_decomp n D E F hE hc y g 1, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    coeff_holInner_cup n D.chi hχ (cF D g) (fun A => eichlerHolomorphic n F A (1 * bF g)) (realGroup g) y
      _ (planeP1 D F hol g) (eichlerDatum_hpot n F hol (1 * bF g) (cF D g)) κ,
    coeff_holInner_cup n D.chi hχ (cF D g)
      (fun A => eichlerHolomorphic n F A (1 * bF g * atInfinity UpperHalfPlane.J))
      (epsJ * realGroup g) y _ (planeP2 D F hol g)
      (eichlerDatum_hpot n F hol (1 * bF g * atInfinity UpperHalfPlane.J) (cF D g)) κ]
  have e : ∀ k, gramOf ((epsJ * realGroup g) * y k) = epsGram (gramOf (realGroup g * y k)) := fun k => by
    rw [mul_assoc, gramOf_eps_mul]
  rw [e 0, e 1, e 2]
  rfl


theorem exists_gram_rep {Γ : Mat3} (hΓ : Γ.PosDef) : ∃ Y : RealGL3, gramOf Y = Γ := by
  obtain ⟨hs, hD, hdet⟩ := posDef_mem_cholDomain hΓ
  have hq : (cholLine Γ).det ≠ 0 := (cholLine_det_pos hs hD hdet).ne'
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (cholLine Γ) hq, ?_⟩
  show cholLine Γ * (cholLine Γ).transpose = Γ
  exact cholLine_mul_transpose Γ (posDef_transpose hΓ) hs hD hdet

theorem segment_posDef {Γa Γb : Mat3} (ha : Γa.PosDef) (hb : Γb.PosDef) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (Γa + t • (Γb - Γa)).PosDef := by
  have := posDef_affTri ha hb hb (p := (t, 0)) ⟨ht.1, le_rfl, by simpa using ht.2⟩
  simpa [affTri] using this

theorem segment_mem_gramDomain {Γa Γb : Mat3} (ha : Γa.PosDef) (hb : Γb.PosDef) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : Γa + t • (Γb - Γa) ∈ gramDomain :=
  cholDomain_subset_gramDomain (posDef_transpose (segment_posDef ha hb ht))
    (posDef_mem_cholDomain (segment_posDef ha hb ht))

theorem epsGram_segment (Γa Γb : Mat3) (t : ℝ) :
    epsGram (Γa + t • (Γb - Γa)) = epsGram Γa + t • (epsGram Γb - epsGram Γa) := by
  unfold epsGram
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

theorem posDef_epsGram {Γ : Mat3} (h : Γ.PosDef) : (epsGram Γ).PosDef :=
  posDef_congr h (det_ne_zero_realGL3 epsJ)

theorem cupCoeff_eq_dot {F' : ℂ → ℂ} (P : PotentialDatum n F') (ν : Fin 3 →₀ ℕ) (Γ₀ Γ₁ Γ₂ : Mat3) :
    cupCoeff P ν Γ₀ Γ₁ Γ₂ = PotentialDatum.dotPairing (n + 2) (P.aFun Γ₁ - P.aFun Γ₀)
      (lFun n ν Γ₂ - lFun n ν Γ₁) := by
  rw [PotentialDatum.dotPairing_apply]
  rfl

theorem tendsto_cupAt {F' : ℂ → ℂ} (P : PotentialDatum n F') (M : Mat3) {Γa Γb : Mat3} (ha : Γa.PosDef)
    (hb : Γb.PosDef) (κ : Fin 3 →₀ ℕ) :
    Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      cupAt P M Γa (Γa + ((i : ℝ) / N) • (Γb - Γa)) (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) κ)
      Filter.atTop (nhds (edgeAt P M Γa Γb κ)) := by
  unfold cupAt edgeAt
  simp_rw [Finset.sum_comm (s := Finset.range _) (t := degSet n)]
  refine tendsto_finsetSum _ fun ν _ => ?_
  simp_rw [← Finset.sum_mul]
  refine Filter.Tendsto.mul_const _ ?_
  simp_rw [cupCoeff_eq_dot]
  exact tendsto_cupEdge (PotentialDatum.dotPairing (n + 2)) P.aFun (lFun n ν) gramDomain isOpen_gramDomain
    (P.contDiffOn_aFun.continuousOn)
    ((contDiffOn_lFun n ν).of_le (by simp)) Γa Γb (fun t ht => segment_mem_gramDomain ha hb ht)


theorem tendsto_srcCup (g : AdelicGL) {Γa Γb : Mat3} (ha : Γa.PosDef) (hb : Γb.PosDef) (κ : Fin 3 →₀ ℕ) :
    Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      srcCup D F hol g Γa (Γa + ((i : ℝ) / N) • (Γb - Γa)) (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) κ)
      Filter.atTop (nhds (srcEdge D F hol g Γa Γb κ)) := by
  unfold srcCup srcEdge
  simp_rw [Finset.sum_add_distrib]
  refine Filter.Tendsto.add (tendsto_cupAt (planeP1 D F hol g) _ ha hb κ) ?_
  simp_rw [epsGram_segment]
  exact tendsto_cupAt (planeP2 D F hol g) _ (posDef_epsGram ha) (posDef_epsGram hb) κ

theorem exists_vertices (gR : RealGL3) {Γ₀ Γ₁ Γ₂ : Mat3} (h₀ : Γ₀.PosDef) (h₁ : Γ₁.PosDef) (h₂ : Γ₂.PosDef) :
    ∃ y : Fin 3 → RealGL3, gramOf (gR * y 0) = Γ₀ ∧ gramOf (gR * y 1) = Γ₁ ∧ gramOf (gR * y 2) = Γ₂ := by
  obtain ⟨Y₀, e₀⟩ := exists_gram_rep h₀
  obtain ⟨Y₁, e₁⟩ := exists_gram_rep h₁
  obtain ⟨Y₂, e₂⟩ := exists_gram_rep h₂
  refine ⟨![gR⁻¹ * Y₀, gR⁻¹ * Y₁, gR⁻¹ * Y₂], ?_, ?_, ?_⟩ <;>
    simp [e₀, e₁, e₂]

section Laws

variable (E : LeviCocycleData D.cusp n) (hE : ∀ A, E.α A = eichlerNormal n F A)
  (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)

include hE hc hχ

/-- Right invariance of the cup under the finite level. -/
theorem srcCup_level (k : finiteLevel) (g : AdelicGL) {Γ₀ Γ₁ Γ₂ : Mat3} (h₀ : Γ₀.PosDef) (h₁ : Γ₁.PosDef)
    (h₂ : Γ₂.PosDef) (κ : Fin 3 →₀ ℕ) :
    srcCup D F hol (g * atFinite k.val) Γ₀ Γ₁ Γ₂ κ = srcCup D F hol g Γ₀ Γ₁ Γ₂ κ := by
  obtain ⟨y, e₀, e₁, e₂⟩ := exists_vertices (realGroup g) h₀ h₁ h₂
  have hχ' : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1 := character_real_eq_one D.chi hχ
  have A := coeff_planeSourceAt_srcCup D F hol E hE hc hχ' y g κ
  have B := coeff_planeSourceAt_srcCup D F hol E hE hc hχ' y (g * atFinite k.val) κ
  rw [realGroup_mul_atFinite, e₀, e₁, e₂] at B
  rw [e₀, e₁, e₂] at A
  rw [← A, ← B, planeSourceAt_level D E hχ g k y 1]

/-- Invariance of the cup under the rational plane parabolic. -/
theorem srcCup_parabolic (p : RationalGL3) (hp : p ∈ parabolic Side.plane) (g : AdelicGL) {Γ₀ Γ₁ Γ₂ : Mat3}
    (h₀ : Γ₀.PosDef) (h₁ : Γ₁.PosDef) (h₂ : Γ₂.PosDef) (κ : Fin 3 →₀ ℕ) :
    srcCup D F hol (rationalGroup p * g)
      ((realGroup (rationalGroup p)).val * Γ₀ * (realGroup (rationalGroup p)).val.transpose)
      ((realGroup (rationalGroup p)).val * Γ₁ * (realGroup (rationalGroup p)).val.transpose)
      ((realGroup (rationalGroup p)).val * Γ₂ * (realGroup (rationalGroup p)).val.transpose) κ =
    srcCup D F hol g Γ₀ Γ₁ Γ₂ κ := by
  obtain ⟨y, e₀, e₁, e₂⟩ := exists_vertices (realGroup g) h₀ h₁ h₂
  have hχ' : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1 := character_real_eq_one D.chi hχ
  have A := coeff_planeSourceAt_srcCup D F hol E hE hc hχ' y g κ
  have B := coeff_planeSourceAt_srcCup D F hol E hE hc hχ' y (rationalGroup p * g) κ
  rw [e₀, e₁, e₂] at A
  have hg : ∀ k, gramOf (realGroup (rationalGroup p * g) * y k) =
      (realGroup (rationalGroup p)).val * gramOf (realGroup g * y k) *
        (realGroup (rationalGroup p)).val.transpose := by
    intro k
    rw [map_mul, mul_assoc, gramOf_mul]
  rw [hg 0, hg 1, hg 2, e₀, e₁, e₂] at B
  rw [← A, ← B]
  have hS := planeSource_isSourceCocycle D E hχ
  have := RationalComparison.source_parabolicInvariant D RationalNorm.rational_norm Side.plane
    (planeSource D E) hS p hp y (g)
  exact congrArg (fun P : HomogeneousPoly n => (P : Poly).coeff κ) this

/-- The plane source is the polynomial with the cup coefficients. -/
theorem planeSourceAt_eq_ofCoeffs (y : Fin 3 → RealGL3) (g : AdelicGL) :
    planeSourceAt D E y g 1 = ofCoeffs n (srcCup D F hol g (gramOf (realGroup g * y 0))
      (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2))) := by
  have hχ' : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1 := character_real_eq_one D.chi hχ
  conv_lhs => rw [eq_ofCoeffs n (planeSourceAt D E y g 1)]
  congr 1
  funext κ
  exact coeff_planeSourceAt_srcCup D F hol E hE hc hχ' y g κ

/-- Covariance of the cup under `GL₃(ℝ)`. -/
theorem srcCup_cov (h : RealGL3) (g : AdelicGL) {Γ₀ Γ₁ Γ₂ : Mat3} (h₀ : Γ₀.PosDef) (h₁ : Γ₁.PosDef)
    (h₂ : Γ₂.PosDef) :
    ofCoeffs n (srcCup D F hol g Γ₀ Γ₁ Γ₂) =
      realCoefficientComponent n D.chi h (ofCoeffs n (srcCup D F hol (g * atInfinity h) Γ₀ Γ₁ Γ₂)) := by
  obtain ⟨y, e₀, e₁, e₂⟩ := exists_vertices (realGroup g * h) h₀ h₁ h₂
  have hS := planeSource_isSourceCocycle D E hχ
  have key := hS.2.2.1 h y g
  have hz : ∀ k, gramOf (realGroup g * (h * y k)) = gramOf ((realGroup g * h) * y k) := fun k => by
    rw [mul_assoc]
  have A := planeSourceAt_eq_ofCoeffs D F hol E hE hc hχ (fun i => h * y i) g
  have B := planeSourceAt_eq_ofCoeffs D F hol E hE hc hχ y (g * atInfinity h)
  rw [realGroup_mul_atInfinity, e₀, e₁, e₂] at B
  simp only [hz, e₀, e₁, e₂] at A
  change planeSourceAt D E (fun i => h * y i) g 1 = _ at key
  rw [← A, ← B]
  exact key

end Laws

theorem seg_mem (N i : ℕ) (hi : i < N) :
    ((i : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 ∧ ((i : ℝ) + 1) / N ∈ Set.Icc (0 : ℝ) 1) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hi)
  have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  exact ⟨⟨by positivity, (div_le_one hN).mpr (by linarith)⟩, ⟨by positivity, (div_le_one hN).mpr hi'⟩⟩

theorem srcEdge_congr (g g' : AdelicGL) {Γa Γb Γa' Γb' : Mat3} (ha : Γa.PosDef) (hb : Γb.PosDef)
    (ha' : Γa'.PosDef) (hb' : Γb'.PosDef) (κ : Fin 3 →₀ ℕ)
    (hcup : ∀ N : ℕ, ∀ i < N,
      srcCup D F hol g' Γa' (Γa' + ((i : ℝ) / N) • (Γb' - Γa')) (Γa' + (((i : ℝ) + 1) / N) • (Γb' - Γa')) κ =
      srcCup D F hol g Γa (Γa + ((i : ℝ) / N) • (Γb - Γa)) (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) κ) :
    srcEdge D F hol g' Γa' Γb' κ = srcEdge D F hol g Γa Γb κ := by
  refine tendsto_nhds_unique (tendsto_srcCup D F hol g' ha' hb' κ) ?_
  refine (tendsto_srcCup D F hol g ha hb κ).congr fun N => ?_
  exact (Finset.sum_congr rfl fun i hi => (hcup N i (Finset.mem_range.mp hi)).symm)

/-- The edge cochain of the plane source. -/
def planeEdge (y : Fin 2 → RealGL3) (g : AdelicGL) : HomogeneousPoly n :=
  ofCoeffs n (srcEdge D F hol g (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)))

theorem conj_segment (M Γa Γb : Mat3) (t : ℝ) :
    M * Γa * M.transpose + t • (M * Γb * M.transpose - M * Γa * M.transpose) =
      M * (Γa + t • (Γb - Γa)) * M.transpose := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

theorem bdry_sum {F' : ℂ → ℂ} (P : PotentialDatum n F') (M : Mat3) (Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) :
    ∑ ν ∈ degSet n, (SeedC3.rho M⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
      bdryCoeff P ν Γ₀ Γ₁ Γ₂ =
    edgeAt P M Γ₁ Γ₂ κ - edgeAt P M Γ₀ Γ₂ κ + edgeAt P M Γ₀ Γ₁ κ := by
  unfold edgeAt bdryCoeff
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_comm]

theorem bF_atInfinity_comm (g : AdelicGL) :
    1 * bF g * atInfinity UpperHalfPlane.J = atInfinity UpperHalfPlane.J * bF g := by
  rw [one_mul]
  exact atFinite_mul_atInfinity_comm _ _

theorem planeEdge_coeff (y : Fin 2 → RealGL3) (g : AdelicGL) (κ : Fin 3 →₀ ℕ) :
    ((planeEdge D F hol y g : HomogeneousPoly n) : Poly).coeff κ =
      if κ.degree = n then srcEdge D F hol g (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)) κ
      else 0 := coeff_ofCoeffs n _ κ

section EdgeLaws

variable (E : LeviCocycleData D.cusp n) (hE : ∀ A, E.α A = eichlerNormal n F A)
  (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)

include hol hE hc hχ

theorem planeEdge_level (k : finiteLevel) (y : Fin 2 → RealGL3) (g : AdelicGL) :
    planeEdge D F hol y (g * atFinite k.val) = planeEdge D F hol y g := by
  unfold planeEdge
  rw [realGroup_mul_atFinite]
  congr 1
  funext κ
  have ha := posDef_gramOf (realGroup g * y 0)
  have hb := posDef_gramOf (realGroup g * y 1)
  refine srcEdge_congr D F hol _ _ ha hb ha hb κ (fun N i hi => ?_)
  obtain ⟨m0, m1⟩ := seg_mem N i hi
  exact srcCup_level D F hol E hE hc hχ k g ha (segment_posDef ha hb m0) (segment_posDef ha hb m1) κ

theorem planeEdge_parabolic (p : RationalGL3) (hp : p ∈ parabolic Side.plane) (y : Fin 2 → RealGL3)
    (g : AdelicGL) : planeEdge D F hol y (rationalGroup p * g) = planeEdge D F hol y g := by
  unfold planeEdge
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
  refine srcEdge_congr D F hol _ _ ha hb (posDef_congr ha (det_ne_zero_realGL3 _))
    (posDef_congr hb (det_ne_zero_realGL3 _)) κ (fun N i hi => ?_)
  obtain ⟨m0, m1⟩ := seg_mem N i hi
  rw [conj_segment, conj_segment]
  exact srcCup_parabolic D F hol E hE hc hχ p hp g ha (segment_posDef ha hb m0) (segment_posDef ha hb m1) κ



theorem planeEdge_cov (h : RealGL3) (y : Fin 2 → RealGL3) (g : AdelicGL) :
    planeEdge D F hol (fun i => h * y i) g =
      realCoefficientComponent n D.chi h (planeEdge D F hol y (g * atInfinity h)) := by
  unfold planeEdge
  have hg : ∀ k, gramOf (realGroup g * (h * y k)) = gramOf (realGroup (g * atInfinity h) * y k) := fun k => by
    rw [realGroup_mul_atInfinity, mul_assoc]
  simp only [hg]
  have ha := posDef_gramOf (realGroup (g * atInfinity h) * y 0)
  have hb := posDef_gramOf (realGroup (g * atInfinity h) * y 1)
  set Γa := gramOf (realGroup (g * atInfinity h) * y 0)
  set Γb := gramOf (realGroup (g * atInfinity h) * y 1)
  set Λ := realCoefficientComponent n D.chi h
  refine ofCoeffs_linear Λ _ _ (fun κ hκ => ?_)
  have hcup : ∀ N i : ℕ, i < N → srcCup D F hol g Γa (Γa + ((i : ℝ) / N) • (Γb - Γa))
      (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) κ = ∑ ν ∈ degMonomials n,
      srcCup D F hol (g * atInfinity h) Γa (Γa + ((i : ℝ) / N) • (Γb - Γa))
        (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) ν *
        ((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ := by
    intro N i hi
    obtain ⟨m0, m1⟩ := seg_mem N i hi
    exact coeffs_of_ofCoeffs_linear Λ _ _ (srcCup_cov D F hol E hE hc hχ h g ha (segment_posDef ha hb m0)
      (segment_posDef ha hb m1)) κ hκ
  have hlim := tendsto_finsetSum (degMonomials n) fun ν _ =>
    (tendsto_srcCup D F hol (g * atInfinity h) ha hb ν).mul_const
      (((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ)
  have hlim' : Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      srcCup D F hol g Γa (Γa + ((i : ℝ) / N) • (Γb - Γa)) (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) κ)
      Filter.atTop (nhds (∑ ν ∈ degMonomials n, srcEdge D F hol (g * atInfinity h) Γa Γb ν *
        ((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ)) := by
    refine hlim.congr fun N => ?_
    calc _ = ∑ ν ∈ degMonomials n, ∑ i ∈ Finset.range N,
          srcCup D F hol (g * atInfinity h) Γa (Γa + ((i : ℝ) / N) • (Γb - Γa))
            (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) ν *
            ((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ := by
          simp_rw [Finset.sum_mul]
      _ = ∑ i ∈ Finset.range N, ∑ ν ∈ degMonomials n,
          srcCup D F hol (g * atInfinity h) Γa (Γa + ((i : ℝ) / N) • (Γb - Γa))
            (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) ν *
            ((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i hi => (hcup N i (Finset.mem_range.mp hi)).symm
  exact tendsto_nhds_unique (tendsto_srcCup D F hol g ha hb κ) hlim'

theorem coeff_planeSourceAt_edge (y : Fin 3 → RealGL3) (g : AdelicGL) (κ : Fin 3 →₀ ℕ) :
    ((planeSourceAt D E y g 1 : HomogeneousPoly n) : Poly).coeff κ =
      cOmegaCoeff n D F y g κ -
        (srcEdge D F hol g (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2)) κ -
          srcEdge D F hol g (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 2)) κ +
          srcEdge D F hol g (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)) κ) := by
  have hχ' : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1 := character_real_eq_one D.chi hχ
  rw [coeff_planeSourceAt_eichler n D E F hE hol hc hχ' y g 1 κ]
  have e : ∀ k, gramOf ((epsJ * realGroup g) * y k) = epsGram (gramOf (realGroup g * y k)) := fun k => by
    rw [mul_assoc, gramOf_eps_mul]
  rw [e 0, e 1, e 2]
  have hp2 : planeHolData n D F g (atInfinity UpperHalfPlane.J) =
      fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) *
        (cF D g * 2⁻¹ * F (1 * bF g * atInfinity UpperHalfPlane.J) z) := by
    funext z; unfold planeHolData; rw [bF_atInfinity_comm]
  have hmul : (epsJ * realGroup g).val = epsJ.val * (realGroup g).val := Units.val_mul _ _
  have b1 : ∑ ν ∈ degSet n, (SeedC3.rho ((realGroup g).val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
      bdryCoeff (eichlerDatum n F hol (1 * bF g) (cF D g)) ν (gramOf (realGroup g * y 0))
        (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2)) =
      edgeAt (planeP1 D F hol g) (realGroup g).val (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2)) κ -
        edgeAt (planeP1 D F hol g) (realGroup g).val (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 2)) κ +
        edgeAt (planeP1 D F hol g) (realGroup g).val (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)) κ :=
    bdry_sum (planeP1 D F hol g) (realGroup g).val _ _ _ κ
  have b2 : ∑ ν ∈ degSet n, (SeedC3.rho ((epsJ * realGroup g).val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
      bdryCoeff (eichlerDatum n F hol (1 * bF g * atInfinity UpperHalfPlane.J) (cF D g)) ν
        (epsGram (gramOf (realGroup g * y 0))) (epsGram (gramOf (realGroup g * y 1)))
        (epsGram (gramOf (realGroup g * y 2))) =
      edgeAt (planeP2 D F hol g) (epsJ * realGroup g).val (epsGram (gramOf (realGroup g * y 1)))
          (epsGram (gramOf (realGroup g * y 2))) κ -
        edgeAt (planeP2 D F hol g) (epsJ * realGroup g).val (epsGram (gramOf (realGroup g * y 0)))
          (epsGram (gramOf (realGroup g * y 2))) κ +
        edgeAt (planeP2 D F hol g) (epsJ * realGroup g).val (epsGram (gramOf (realGroup g * y 0)))
          (epsGram (gramOf (realGroup g * y 1))) κ :=
    bdry_sum (planeP2 D F hol g) (epsJ * realGroup g).val _ _ _ κ
  unfold cOmegaCoeff srcEdge
  have hp1 : planeHolData n D F g 1 = fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) *
      (cF D g * 2⁻¹ * F (1 * bF g) z) := rfl
  rw [hp1, hp2, ← hmul, b1, b2]
  ring

/-- **The plane source is the integral cochain minus the coboundary of the edge cochain** (as polynomials). -/
theorem cOmega_sub_planeSource (y : Fin 3 → RealGL3) (g : AdelicGL) :
    cOmega n D F y g - planeSource D E y g =
      planeEdge D F hol ![y 1, y 2] g - planeEdge D F hol ![y 0, y 2] g + planeEdge D F hol ![y 0, y 1] g := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro κ
  simp only [Submodule.coe_sub, Submodule.coe_add, MvPolynomial.coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    cOmega, planeEdge_coeff, coeff_ofCoeffs]
  by_cases hκ : κ.degree = n
  · simp only [ite_eq_left hκ]
    have h := coeff_planeSourceAt_edge D F hol E hE hc hχ y g κ
    have h' : ((planeSource D E y g : HomogeneousPoly n) : Poly).coeff κ =
        ((planeSourceAt D E y g 1 : HomogeneousPoly n) : Poly).coeff κ := rfl
    rw [h', h]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp only [ite_eq_right hκ]
    have h0 : ((planeSource D E y g : HomogeneousPoly n) : Poly).coeff κ = 0 :=
      ((MvPolynomial.mem_homogeneousSubmodule n _).mp (planeSource D E y g).2).coeff_eq_zero hκ
    rw [h0]
    ring

theorem sourceToSummand_cOmega_eq_planeSource
    (hRa : IsSourceCocycle D Side.plane (fun y g => cOmega n D F y g)) :
    SourceQuotient.sourceToSummand D Side.plane ⟨fun y g => cOmega n D F y g, hRa⟩ =
      SourceQuotient.sourceToSummand D Side.plane ⟨planeSource D E, planeSource_isSourceCocycle D E hχ⟩ :=
  sourceToSummand_eq_of_edge D Side.plane _ _ hRa (planeSource_isSourceCocycle D E hχ)
    (planeEdge D F hol)
    (fun y g => cOmega_sub_planeSource D F hol E hE hc hχ y g)
    (fun h y g => planeEdge_cov D F hol E hE hc hχ h y g)
    (fun k y g => planeEdge_level D F hol E hE hc hχ k y g)
    (fun p hp y g => planeEdge_parabolic D F hol E hE hc hχ p hp y g)

end EdgeLaws

end PlaneEdge

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
