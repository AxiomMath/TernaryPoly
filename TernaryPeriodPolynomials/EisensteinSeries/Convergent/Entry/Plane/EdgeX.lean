module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Edge
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.LiftSmooth

@[expose] public section


/-!
# The edge cochain and the plane integral cochain at a general binary adele

Generalization of `Entry/PlaneEdge` from the binary adele `1` to a general `x`: `srcCupX`, `srcEdgeX`, `planeEdgeX`,
the transfer lemma `srcEdgeX_transfer` (a cup law passes to the edge cochain through Riemann sums), the **translation
law** of the edge cochain under the real parabolic and the finite parabolic (`srcEdgeX_translate`,
`planeEdgeX_translate`, from the library's `planeSourceAt_translate`), the decomposition
`cOmegaAt - planeSourceAt = δ planeEdgeX` (`cOmegaAt_sub_planeSourceAt`) and the translation law of the plane integral
cochain itself (`cOmegaAt_translate`).

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

section PlaneEdgeX

variable {n : ℕ} (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
  (hol : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})

/-- The potential of the holomorphic half at a general binary adele `x`. -/
def planeP1x (g : AdelicGL) (x : BinaryAdelicGL) : PotentialDatum n (fun z => cF D g * 2⁻¹ * F (x * bF g) z) :=
  eichlerDatum n F hol (x * bF g) (cF D g)

/-- The potential of the reflected half at a general binary adele `x`. -/
def planeP2x (g : AdelicGL) (x : BinaryAdelicGL) :
    PotentialDatum n (fun z => cF D g * 2⁻¹ * F (x * bF g * atInfinity UpperHalfPlane.J) z) :=
  eichlerDatum n F hol (x * bF g * atInfinity UpperHalfPlane.J) (cF D g)

/-- The cup of the plane source at a general binary adele. -/
def srcCupX (g : AdelicGL) (x : BinaryAdelicGL) (Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) : ℂ :=
  cupAt (planeP1x D F hol g x) (realGroup g).val Γ₀ Γ₁ Γ₂ κ +
  cupAt (planeP2x D F hol g x) (epsJ * realGroup g).val (epsGram Γ₀) (epsGram Γ₁) (epsGram Γ₂) κ

/-- The edge cochain at a general binary adele. -/
def srcEdgeX (g : AdelicGL) (x : BinaryAdelicGL) (Γa Γb : Mat3) (κ : Fin 3 →₀ ℕ) : ℂ :=
  edgeAt (planeP1x D F hol g x) (realGroup g).val Γa Γb κ +
  edgeAt (planeP2x D F hol g x) (epsJ * realGroup g).val (epsGram Γa) (epsGram Γb) κ

theorem srcCupX_one (g : AdelicGL) (Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) :
    srcCupX D F hol g 1 Γ₀ Γ₁ Γ₂ κ = srcCup D F hol g Γ₀ Γ₁ Γ₂ κ := rfl

theorem srcEdgeX_one (g : AdelicGL) (Γa Γb : Mat3) (κ : Fin 3 →₀ ℕ) :
    srcEdgeX D F hol g 1 Γa Γb κ = srcEdge D F hol g Γa Γb κ := rfl

theorem coeff_planeSourceAt_srcCupX (E : LeviCocycleData D.cusp n) (hE : ∀ A, E.α A = eichlerNormal n F A)
    (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
    (hχ : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) (κ : Fin 3 →₀ ℕ) :
    ((planeSourceAt D E y g x : HomogeneousPoly n) : Poly).coeff κ =
      srcCupX D F hol g x (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1))
        (gramOf (realGroup g * y 2)) κ := by
  rw [planeSourceAt_decomp n D E F hE hc y g x, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    coeff_holInner_cup n D.chi hχ (cF D g) (fun A => eichlerHolomorphic n F A (x * bF g)) (realGroup g) y
      _ (planeP1x D F hol g x) (eichlerDatum_hpot n F hol (x * bF g) (cF D g)) κ,
    coeff_holInner_cup n D.chi hχ (cF D g)
      (fun A => eichlerHolomorphic n F A (x * bF g * atInfinity UpperHalfPlane.J))
      (epsJ * realGroup g) y _ (planeP2x D F hol g x)
      (eichlerDatum_hpot n F hol (x * bF g * atInfinity UpperHalfPlane.J) (cF D g)) κ]
  have e : ∀ k, gramOf ((epsJ * realGroup g) * y k) = epsGram (gramOf (realGroup g * y k)) := fun k => by
    rw [mul_assoc, gramOf_eps_mul]
  rw [e 0, e 1, e 2]
  rfl

theorem tendsto_srcCupX (g : AdelicGL) (x : BinaryAdelicGL) {Γa Γb : Mat3} (ha : Γa.PosDef) (hb : Γb.PosDef)
    (κ : Fin 3 →₀ ℕ) :
    Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      srcCupX D F hol g x Γa (Γa + ((i : ℝ) / N) • (Γb - Γa)) (Γa + (((i : ℝ) + 1) / N) • (Γb - Γa)) κ)
      Filter.atTop (nhds (srcEdgeX D F hol g x Γa Γb κ)) := by
  unfold srcCupX srcEdgeX
  simp_rw [Finset.sum_add_distrib]
  refine Filter.Tendsto.add (tendsto_cupAt (planeP1x D F hol g x) _ ha hb κ) ?_
  simp_rw [epsGram_segment]
  exact tendsto_cupAt (planeP2x D F hol g x) _ (posDef_epsGram ha) (posDef_epsGram hb) κ

/-- **Transfer of a cup law to the edge cochain.**  If the cup at `(g', x)` on the `P`-congruent vertices is `s` times
the cup at `(g, x')`, so is the edge cochain. -/
theorem srcEdgeX_transfer (g g' : AdelicGL) (x x' : BinaryAdelicGL) (P : Mat3) (hP : P.det ≠ 0) (s : ℂ)
    (hcup : ∀ {Γ₀ Γ₁ Γ₂ : Mat3}, Γ₀.PosDef → Γ₁.PosDef → Γ₂.PosDef → ∀ κ,
      srcCupX D F hol g' x (P * Γ₀ * Pᵀ) (P * Γ₁ * Pᵀ) (P * Γ₂ * Pᵀ) κ = s * srcCupX D F hol g x' Γ₀ Γ₁ Γ₂ κ)
    {Γa Γb : Mat3} (ha : Γa.PosDef) (hb : Γb.PosDef) (κ : Fin 3 →₀ ℕ) :
    srcEdgeX D F hol g' x (P * Γa * Pᵀ) (P * Γb * Pᵀ) κ = s * srcEdgeX D F hol g x' Γa Γb κ := by
  have h1 := tendsto_srcCupX D F hol g' x (posDef_congr ha hP) (posDef_congr hb hP) κ
  have h2 := (tendsto_srcCupX D F hol g x' ha hb κ).const_mul s
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨m0, m1⟩ := seg_mem N i (Finset.mem_range.mp hi)
  rw [conj_segment, conj_segment]
  rw [← hcup ha (segment_posDef ha hb m0) (segment_posDef ha hb m1) κ]


section Translate

variable (E : LeviCocycleData D.cusp n) (hE : ∀ A, E.α A = eichlerNormal n F A)
  (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)

include hE hc hχ

/-- **The translation law of the cup.** -/
theorem srcCupX_translate (g g' : AdelicGL) (p : planeParabolic ℝ) (f : FiniteGL)
    (hf : f ∈ planeParabolic FiniteAdeles) (hr : realGroup g' = p.1 * realGroup g)
    (hfin : finiteGroup g' = f * finiteGroup g) (x : BinaryAdelicGL) {Γ₀ Γ₁ Γ₂ : Mat3} (h₀ : Γ₀.PosDef)
    (h₁ : Γ₁.PosDef) (h₂ : Γ₂.PosDef) (κ : Fin 3 →₀ ℕ) :
    srcCupX D F hol g' x (p.1.val * Γ₀ * p.1.valᵀ) (p.1.val * Γ₁ * p.1.valᵀ) (p.1.val * Γ₂ * p.1.valᵀ) κ =
      (normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) *
          finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf) *
        srcCupX D F hol g (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p))) Γ₀ Γ₁ Γ₂ κ := by
  obtain ⟨y, e₀, e₁, e₂⟩ := exists_vertices (realGroup g) h₀ h₁ h₂
  have hχ' : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1 := character_real_eq_one D.chi hχ
  have A := coeff_planeSourceAt_srcCupX D F hol E hE hc hχ' y g
    (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p))) κ
  have B := coeff_planeSourceAt_srcCupX D F hol E hE hc hχ' y g' x κ
  have hg : ∀ k, gramOf (realGroup g' * y k) = p.1.val * gramOf (realGroup g * y k) * p.1.valᵀ := by
    intro k
    rw [hr, mul_assoc, gramOf_mul]
  rw [hg 0, hg 1, hg 2, e₀, e₁, e₂] at B
  rw [e₀, e₁, e₂] at A
  rw [← A, ← B, planeSourceAt_translate D E hχ g g' p f hf hr hfin y x]
  rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]

/-- **The translation law of the edge cochain.** -/
theorem srcEdgeX_translate (g g' : AdelicGL) (p : planeParabolic ℝ) (f : FiniteGL)
    (hf : f ∈ planeParabolic FiniteAdeles) (hr : realGroup g' = p.1 * realGroup g)
    (hfin : finiteGroup g' = f * finiteGroup g) (x : BinaryAdelicGL) {Γa Γb : Mat3} (ha : Γa.PosDef)
    (hb : Γb.PosDef) (κ : Fin 3 →₀ ℕ) :
    srcEdgeX D F hol g' x (p.1.val * Γa * p.1.valᵀ) (p.1.val * Γb * p.1.valᵀ) κ =
      (normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) *
          finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf) *
        srcEdgeX D F hol g (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p))) Γa Γb κ :=
  srcEdgeX_transfer D F hol g g' x _ p.1.val (det_ne_zero_realGL3 p.1) _
    (fun h₀ h₁ h₂ κ => srcCupX_translate D F hol E hE hc hχ g g' p f hf hr hfin x h₀ h₁ h₂ κ) ha hb κ


/-- The edge cochain of the plane source at a general binary adele. -/
def planeEdgeX (y : Fin 2 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) : HomogeneousPoly n :=
  ofCoeffs n (srcEdgeX D F hol g x (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)))

omit hE hc hχ in
theorem planeEdgeX_one (y : Fin 2 → RealGL3) (g : AdelicGL) :
    planeEdgeX D F hol y g 1 = planeEdge D F hol y g := rfl

theorem planeEdgeX_translate (y : Fin 2 → RealGL3) (g g' : AdelicGL) (p : planeParabolic ℝ) (f : FiniteGL)
    (hf : f ∈ planeParabolic FiniteAdeles) (hr : realGroup g' = p.1 * realGroup g)
    (hfin : finiteGroup g' = f * finiteGroup g) (x : BinaryAdelicGL) :
    planeEdgeX D F hol y g' x =
      (normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) *
          finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf) •
        planeEdgeX D F hol y g (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p))) := by
  unfold planeEdgeX
  have hg : ∀ k, gramOf (realGroup g' * y k) = p.1.val * gramOf (realGroup g * y k) * p.1.valᵀ := by
    intro k
    rw [hr, mul_assoc, gramOf_mul]
  rw [hg 0, hg 1]
  apply Subtype.ext
  apply MvPolynomial.ext
  intro κ
  rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul, coeff_ofCoeffs, coeff_ofCoeffs]
  by_cases hκ : κ.degree = n
  · rw [ite_eq_left hκ, ite_eq_left hκ]
    exact srcEdgeX_translate D F hol E hE hc hχ g g' p f hf hr hfin x (posDef_gramOf _) (posDef_gramOf _) κ
  · rw [ite_eq_right hκ, ite_eq_right hκ, mul_zero]

end Translate

/-- The plane integral cochain at a general binary adele, as a homogeneous polynomial. -/
def cOmegaAt (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) : HomogeneousPoly n :=
  ofCoeffs n (cOmegaCoeffAt n D F y g x)

theorem cOmegaAt_one (y : Fin 3 → RealGL3) (g : AdelicGL) : cOmegaAt D F y g 1 = cOmega n D F y g := by
  unfold cOmegaAt cOmega
  rw [show cOmegaCoeffAt n D F y g 1 = cOmegaCoeff n D F y g from funext (cOmegaCoeffAt_one n D F y g)]

section Decomp

variable (E : LeviCocycleData D.cusp n) (hE : ∀ A, E.α A = eichlerNormal n F A)
  (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)

include hol hE hc hχ

theorem coeff_planeSourceAt_edgeX (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) (κ : Fin 3 →₀ ℕ) :
    ((planeSourceAt D E y g x : HomogeneousPoly n) : Poly).coeff κ =
      cOmegaCoeffAt n D F y g x κ -
        (srcEdgeX D F hol g x (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2)) κ -
          srcEdgeX D F hol g x (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 2)) κ +
          srcEdgeX D F hol g x (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)) κ) := by
  have hχ' : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1 := character_real_eq_one D.chi hχ
  rw [coeff_planeSourceAt_eichler n D E F hE hol hc hχ' y g x κ]
  have e : ∀ k, gramOf ((epsJ * realGroup g) * y k) = epsGram (gramOf (realGroup g * y k)) := fun k => by
    rw [mul_assoc, gramOf_eps_mul]
  rw [e 0, e 1, e 2]
  have hmul : (epsJ * realGroup g).val = epsJ.val * (realGroup g).val := Units.val_mul _ _
  have b1 : ∑ ν ∈ degSet n, (SeedC3.rho ((realGroup g).val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
      bdryCoeff (eichlerDatum n F hol (x * bF g) (cF D g)) ν (gramOf (realGroup g * y 0))
        (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2)) =
      edgeAt (planeP1x D F hol g x) (realGroup g).val (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2)) κ -
        edgeAt (planeP1x D F hol g x) (realGroup g).val (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 2)) κ +
        edgeAt (planeP1x D F hol g x) (realGroup g).val (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)) κ :=
    bdry_sum (planeP1x D F hol g x) (realGroup g).val _ _ _ κ
  have b2 : ∑ ν ∈ degSet n, (SeedC3.rho ((epsJ * realGroup g).val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
      bdryCoeff (eichlerDatum n F hol (x * bF g * atInfinity UpperHalfPlane.J) (cF D g)) ν
        (epsGram (gramOf (realGroup g * y 0))) (epsGram (gramOf (realGroup g * y 1)))
        (epsGram (gramOf (realGroup g * y 2))) =
      edgeAt (planeP2x D F hol g x) (epsJ * realGroup g).val (epsGram (gramOf (realGroup g * y 1)))
          (epsGram (gramOf (realGroup g * y 2))) κ -
        edgeAt (planeP2x D F hol g x) (epsJ * realGroup g).val (epsGram (gramOf (realGroup g * y 0)))
          (epsGram (gramOf (realGroup g * y 2))) κ +
        edgeAt (planeP2x D F hol g x) (epsJ * realGroup g).val (epsGram (gramOf (realGroup g * y 0)))
          (epsGram (gramOf (realGroup g * y 1))) κ :=
    bdry_sum (planeP2x D F hol g x) (epsJ * realGroup g).val _ _ _ κ
  have hp2 : planeHolData n D F g (x * atInfinity UpperHalfPlane.J) =
      fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) *
        (cF D g * 2⁻¹ * F (x * bF g * atInfinity UpperHalfPlane.J) z) := by
    funext z; unfold planeHolData
    have e : x * atInfinity UpperHalfPlane.J * bF g = x * bF g * atInfinity UpperHalfPlane.J := by
      rw [mul_assoc, ← bF_comm_atInfinityJ g, ← mul_assoc]
    rw [e]
  have hp1 : planeHolData n D F g x = fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) *
      (cF D g * 2⁻¹ * F (x * bF g) z) := rfl
  unfold cOmegaCoeffAt srcEdgeX
  rw [hp1, hp2, ← hmul, b1, b2]
  ring

theorem cOmegaAt_sub_planeSourceAt (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) :
    cOmegaAt D F y g x - planeSourceAt D E y g x =
      planeEdgeX D F hol ![y 1, y 2] g x - planeEdgeX D F hol ![y 0, y 2] g x +
        planeEdgeX D F hol ![y 0, y 1] g x := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro κ
  simp only [Submodule.coe_sub, Submodule.coe_add, MvPolynomial.coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    cOmegaAt, planeEdgeX, coeff_ofCoeffs]
  by_cases hκ : κ.degree = n
  · simp only [ite_eq_left hκ]
    have h := coeff_planeSourceAt_edgeX D F hol E hE hc hχ y g x κ
    rw [h]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp only [ite_eq_right hκ]
    have h0 : ((planeSourceAt D E y g x : HomogeneousPoly n) : Poly).coeff κ = 0 :=
      ((MvPolynomial.mem_homogeneousSubmodule n _).mp (planeSourceAt D E y g x).2).coeff_eq_zero hκ
    rw [h0]
    ring

/-- **The translation law of the plane integral cochain.** -/
theorem cOmegaAt_translate (y : Fin 3 → RealGL3) (g g' : AdelicGL) (p : planeParabolic ℝ) (f : FiniteGL)
    (hf : f ∈ planeParabolic FiniteAdeles) (hr : realGroup g' = p.1 * realGroup g)
    (hfin : finiteGroup g' = f * finiteGroup g) (x : BinaryAdelicGL) :
    cOmegaAt D F y g' x =
      (normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) *
          finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf) •
        cOmegaAt D F y g (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p))) := by
  have d1 := cOmegaAt_sub_planeSourceAt D F hol E hE hc hχ y g' x
  have d2 := cOmegaAt_sub_planeSourceAt D F hol E hE hc hχ y g
    (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p)))
  have t0 := planeSourceAt_translate D E hχ g g' p f hf hr hfin y x
  have t1 := planeEdgeX_translate D F hol E hE hc hχ ![y 1, y 2] g g' p f hf hr hfin x
  have t2 := planeEdgeX_translate D F hol E hE hc hχ ![y 0, y 2] g g' p f hf hr hfin x
  have t3 := planeEdgeX_translate D F hol E hE hc hχ ![y 0, y 1] g g' p f hf hr hfin x
  set s := (normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) *
          finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf) with hs
  have : cOmegaAt D F y g' x = planeSourceAt D E y g' x + (planeEdgeX D F hol ![y 1, y 2] g' x -
      planeEdgeX D F hol ![y 0, y 2] g' x + planeEdgeX D F hol ![y 0, y 1] g' x) := by
    rw [← d1]; abel
  have h2 : cOmegaAt D F y g (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p))) =
      planeSourceAt D E y g (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p))) +
      (planeEdgeX D F hol ![y 1, y 2] g (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p))) -
        planeEdgeX D F hol ![y 0, y 2] g (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p))) +
        planeEdgeX D F hol ![y 0, y 1] g (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p)))) := by
    rw [← d2]; abel
  rw [this, h2, t0, t1, t2, t3]
  simp only [smul_add, smul_sub]

end Decomp


end PlaneEdgeX

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
