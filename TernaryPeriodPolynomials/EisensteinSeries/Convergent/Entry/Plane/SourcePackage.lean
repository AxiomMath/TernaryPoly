module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.TCommute
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.IwasawaChart
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CupSeed
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.JointContinuity

@[expose] public section


/-!
# The plane source as the integral cochain minus a coboundary

`coeff_planeSourceAt_bridge`: for a vector potential `P` (a `PotentialDatum`) which reproduces the Levi cocycle
`E.α` (times the finite scalar `c_F`) at the points `basePoint A`, the coefficient `κ` of the library's
`planeSourceAt D E y g x` equals the plane integral cochain `planeIntG` of the seed `ω_h`,
`h = (-1)ⁿ (n+1) F`, over the Gram triangle `[y₀y₀ᵀ, y₁y₁ᵀ, y₂y₂ᵀ]` at the group element `g_∞`, minus the finite
combination (coefficients of `ρ(g_∞⁻¹)`) of the edge-cochain boundary terms (`bdryCoeff`).
Ingredients: `coeff_planeRadical_expand`, `basePoint_iwA`, `rcc_inv_eq_rho`, `plane_cup_bridge`.

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

theorem cholDomain_subset_gramDomain {P : Mat3} (hP : Pᵀ = P) (hd : P ∈ cholDomain) : P ∈ gramDomain := by
  obtain ⟨hs, hD, hdet⟩ := hd
  have hqP : cholLine P * (cholLine P)ᵀ = P := cholLine_mul_transpose P hP hs hD hdet
  have hq : (cholLine P).det ≠ 0 := (cholLine_det_pos hs hD hdet).ne'
  rw [← hqP]
  exact gram_mem_gramDomain _ hq

/-- The coefficients of the plane radical on an arbitrary binary form, expanded in the weight basis. -/
theorem coeff_planeRadical_expand (n : ℕ) (χ : RankOneCharacter) (y : RealGL3)
    (Q : Binary.HomogeneousPoly (n + 1)) (ν : Fin 3 →₀ ℕ) :
    (planeRadical n χ (iwP y) Q : Poly).coeff ν =
      ∑ j, (binaryWeightBasis (n + 1)).coord j Q * lFun n ν (y.val * y.val.transpose) j := by
  rw [coeff_planeRadical_iwP]
  have hQ : Q = ∑ j, (binaryWeightBasis (n + 1)).coord j Q • binaryWeightBasis (n + 1) j := by
    simp only [Module.Basis.coord_apply]
    exact (Module.Basis.sum_repr _ _).symm
  conv_lhs => rw [hQ]
  rw [radicalCoeff_sum_smul]
  rfl

theorem rcc_inv_eq_rho (n : ℕ) (χ : RankOneCharacter)
    (hχ : ∀ t : ℝˣ, χ.toMonoidHom (realAdeleUnit t) = 1) (g : RealGL3) (P : HomogeneousPoly n) :
    ((realCoefficientComponent n χ g⁻¹ P : HomogeneousPoly n) : Poly) =
      SeedC3.rho (g.val)⁻¹ (P : Poly) := by
  rw [realCoefficientComponent_inv_val n χ hχ g P, rho_eq_C_mul_substitute]
  have hu : IsUnit g.val.det := isUnit_iff_ne_zero.mpr (det_ne_zero_realGL3 g)
  rw [Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_inv,
    Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rfl

/-- The Gram matrix of a real matrix. -/
def gramOf (y : RealGL3) : Mat3 := y.val * y.val.transpose

theorem posDef_gramOf (y : RealGL3) : (gramOf y).PosDef := posDef_gram (det_ne_zero_realGL3 y)

theorem gramOf_mul (g y : RealGL3) : gramOf (g * y) = g.val * gramOf y * g.val.transpose := by
  unfold gramOf
  rw [Units.val_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- The cup of the potential and the radical at three Gram matrices (coefficient `ν`). -/
def cupCoeff {n : ℕ} {F : ℂ → ℂ} (P : PotentialDatum n F) (ν : Fin 3 →₀ ℕ) (G₀ G₁ G₂ : Mat3) : ℂ :=
  ∑ j, (P.aFun G₁ j - P.aFun G₀ j) * (lFun n ν G₂ j - lFun n ν G₁ j)

/-- The edge-cochain boundary term of the bridge (coefficient `ν`). -/
def bdryCoeff {n : ℕ} {F : ℂ → ℂ} (P : PotentialDatum n F) (ν : Fin 3 →₀ ℕ) (G₀ G₁ G₂ : Mat3) : ℂ :=
  cupEdge (PotentialDatum.dotPairing (n + 2)) P.aFun (lFun n ν) G₁ G₂ - cupEdge (PotentialDatum.dotPairing (n + 2)) P.aFun (lFun n ν) G₀ G₂ +
    cupEdge (PotentialDatum.dotPairing (n + 2)) P.aFun (lFun n ν) G₀ G₁

/-- The inner polynomial of a plane-type source with potential `α` and finite scalar `c`:
`(R(Y₂) - R(Y₁)) (c (α(A(Y₁)) - α(A(Y₀))))`. -/
def holInner (n : ℕ) (χ : RankOneCharacter) (c : ℂ) (α : BinaryRealGL → Binary.HomogeneousPoly (n + 1))
    (Y : Fin 3 → RealGL3) : HomogeneousPoly n :=
  (planeRadical n χ (iwP (Y 2)) - planeRadical n χ (iwP (Y 1))) (c • (α (iwA (Y 1)) - α (iwA (Y 0))))

/-- **A plane-type source cochain, coefficient `κ`, is the integral cochain minus the coboundary of the edge
cochain** (potential `α` reproduced by the vector potential `P`). -/
theorem coeff_holSource_bridge (n : ℕ) (χ : RankOneCharacter)
    (hχ : ∀ t : ℝˣ, χ.toMonoidHom (realAdeleUnit t) = 1) (c : ℂ)
    (α : BinaryRealGL → Binary.HomogeneousPoly (n + 1)) (gR : RealGL3) (y : Fin 3 → RealGL3)
    (F : ℂ → ℂ) (P : PotentialDatum n F)
    (hpot : ∀ (A : BinaryRealGL) (j : Fin (n + 2)), P.A (basePoint A) j =
      c * (binaryWeightBasis (n + 1)).coord j (α A))
    (hF : ContinuousOn F {z : ℂ | 0 < z.im}) (κ : Fin 3 →₀ ℕ) :
    ((realCoefficientComponent n χ gR⁻¹
        (holInner n χ c α (fun i => gR * y i)) : HomogeneousPoly n) : Poly).coeff κ =
      planeIntG n (fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) * F z) gR.val
        (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ -
      ∑ ν ∈ degSet n, (SeedC3.rho (gR.val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
        bdryCoeff P ν (gramOf (gR * y 0)) (gramOf (gR * y 1)) (gramOf (gR * y 2)) := by
  set Y : Fin 3 → RealGL3 := fun i => gR * y i with hY
  set Γ' : Fin 3 → Mat3 := fun i => gramOf (Y i) with hΓ'
  have hpd : ∀ i, (Γ' i).PosDef := fun i => posDef_gramOf _
  have hcond := affTri_mem_cholDomain (hpd 0) (hpd 1) (hpd 2)
  have hdom : ∀ p ∈ stdTriangle, affTri (Γ' 0) (Γ' 1) (Γ' 2) p ∈ gramDomain := fun p hp =>
    cholDomain_subset_gramDomain (posDef_transpose (posDef_affTri (hpd 0) (hpd 1) (hpd 2) hp)) (hcond p hp)
  have hs : ∀ i, (Γ' i)ᵀ = Γ' i := fun i => posDef_transpose (hpd i)
  -- the inner polynomial of the plane source
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
  -- the plane source coefficient
  have hlhs : ((realCoefficientComponent n χ gR⁻¹
        (holInner n χ c α (fun i => gR * y i)) : HomogeneousPoly n) : Poly).coeff κ =
      ∑ ν ∈ degSet n, (Φ : Poly).coeff ν *
        (SeedC3.rho (gR.val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ := by
    rw [hsrc, rcc_inv_eq_rho n χ hχ gR]
    exact coeff_rho_eq_sum _ n _ (fun m' hm' => coeff_eq_zero_of_sum_ne
      ((MvPolynomial.mem_homogeneousSubmodule n _).mp Φ.2) m' hm') κ
  have hbr := fun ν => P.plane_cup_bridge ν (Γ' 0) (Γ' 1) (Γ' 2) (hs 0) (hs 1) (hs 2) hdom
  -- the integral cochain, expanded
  set hh : ℂ → ℂ := fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) * F z with hhdef
  have hQ1 : Γ' 1 - Γ' 0 = gR.val * (gramOf (y 1) - gramOf (y 0)) * gR.val.transpose := by
    simp only [hΓ', hY, gramOf_mul, Matrix.mul_sub, Matrix.sub_mul]
  have hQ2 : Γ' 2 - Γ' 0 = gR.val * (gramOf (y 2) - gramOf (y 0)) * gR.val.transpose := by
    simp only [hΓ', hY, gramOf_mul, Matrix.mul_sub, Matrix.sub_mul]
  have hP : ∀ p, gR.val * affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) p * gR.val.transpose =
      affTri (Γ' 0) (Γ' 1) (Γ' 2) p := by
    intro p
    simp only [hΓ', hY, gramOf_mul]
    rw [affTri_congr]
  have hint : planeIntG n hh gR.val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ =
      ∑ ν ∈ degSet n, (∫ p in stdTriangle, (formPair (seedForm n hh)
        (affTri (Γ' 0) (Γ' 1) (Γ' 2) p) (Γ' 1 - Γ' 0) (Γ' 2 - Γ' 0)).coeff ν) *
          (SeedC3.rho (gR.val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ := by
    unfold planeIntG twPull
    simp_rw [hP, ← hQ1, ← hQ2]
    refine integral_coeff_rho _ n _ _ (fun p => isHomogeneous_formPair_seed n hh _ _ _) (fun ν => ?_) κ
    have hc : ContinuousOn (fun p : ℝ × ℝ => (formPair (seedForm n hh)
        (affTri (Γ' 0) (Γ' 1) (Γ' 2) p) (Γ' 1 - Γ' 0) (Γ' 2 - Γ' 0)).coeff ν) stdTriangle := by
      have hhc : ContinuousOn hh {z : ℂ | 0 < z.im} := by
        simp only [hhdef]
        exact continuousOn_const.mul hF
      have hQs1 : (Γ' 1 - Γ' 0)ᵀ = Γ' 1 - Γ' 0 := by rw [Matrix.transpose_sub, hs 1, hs 0]
      have hQs2 : (Γ' 2 - Γ' 0)ᵀ = Γ' 2 - Γ' 0 := by rw [Matrix.transpose_sub, hs 2, hs 0]
      exact continuousOn_coeff_formPair_comp n hh hhc _ _ _ (continuous_affTri (Γ' 0) (Γ' 1) (Γ' 2)).continuousOn
        continuousOn_const continuousOn_const
        (fun p hp => ⟨hdom p hp, posDef_transpose (posDef_affTri (hpd 0) (hpd 1) (hpd 2) hp), hQs1, hQs2⟩) ν
    exact hc.integrableOn_compact isCompact_stdTriangle
  rw [hlhs, hint]
  simp_rw [hΦc]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [hbr ν]
  unfold cupCoeff bdryCoeff
  ring


/-- **The plane source cochain, coefficient `κ`, is the integral cochain minus the coboundary of the edge
cochain** (holomorphic part of the potential). -/
theorem coeff_planeSourceAt_bridge (n : ℕ) (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) (F : ℂ → ℂ) (P : PotentialDatum n F)
    (hpot : ∀ (A : BinaryRealGL) (j : Fin (n + 2)), P.A (basePoint A) j =
      cF D g * (binaryWeightBasis (n + 1)).coord j (E.α A (x * bF g)))
    (hF : ContinuousOn F {z : ℂ | 0 < z.im}) (κ : Fin 3 →₀ ℕ) :
    ((planeSourceAt D E y g x : HomogeneousPoly n) : Poly).coeff κ =
      planeIntG n (fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) * F z) (realGroup g).val
        (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ -
      ∑ ν ∈ degSet n, (SeedC3.rho ((realGroup g).val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
        bdryCoeff P ν (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1)) (gramOf (realGroup g * y 2)) :=
  coeff_holSource_bridge n D.chi hχ (cF D g) (fun A => E.α A (x * bF g)) (realGroup g) y F P hpot hF κ

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
