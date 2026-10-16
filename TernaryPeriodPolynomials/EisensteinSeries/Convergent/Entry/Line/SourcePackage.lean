module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.SourcePackage
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.CupSeed
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.PairEq
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceData

@[expose] public section


/-!
# The line source as the line integral cochain minus a coboundary

Line analogue of `PlaneSourcePackage`: the Iwasawa factor of `y` gives the line chart coordinates of `y yᵀ`
(`lineChart_iwasawa`: `w = (b₀₁/b₁₁, (b₀₂b₁₁ - b₀₁b₁₂)/(b₁₁b₂₂))`, `τ = (b₁₁ i + b₁₂)/b₂₂ = basePoint (iwALine y)`), the radical
coordinates are `lrC = (w₂, -w₁)` (`lrC_iwPLine`), hence the coefficients of `lineRadical n χ (iwPLine y)` on a binary
form are `∑ⱼ coordⱼ · lFunLine` (`coeff_lineRadical_expand`).  `coeff_lineSourceAt_bridge`: for a potential `P`
reproducing the sign-twisted Levi cocycle, the coefficient `κ` of `lineSourceAt D E y g x` is the line integral
cochain `lineIntG` of the line seed `σ_h`, `h = (-1)^{n+1}(n+1)F`, minus the boundary combination of the edge
cochain.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses TernaryPeriodPolynomials.AnalyticClasses.EdgeExplicit

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

section Upper

variable (B : Mat3) (h10 : B 1 0 = 0) (h20 : B 2 0 = 0) (h21 : B 2 1 = 0)

include h10 h20 h21

theorem lineD_upper : lineD (B * B.transpose) = (B 1 1 * B 2 2) ^ 2 := by
  obtain ⟨e22, e02, e12, e00, e01, e11⟩ := gram_upper_entries B h10 h20 h21
  have e21 : (B * B.transpose) 2 1 = B 1 2 * B 2 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, h20, h21]; ring
  unfold lineD
  rw [e11, e22, e12, e21]
  ring

theorem lineChart_upper (h22 : B 2 2 ≠ 0) (h11 : B 1 1 ≠ 0) :
    lineChart (B * B.transpose) 0 = B 0 1 / B 1 1 ∧
    lineChart (B * B.transpose) 1 = (B 0 2 * B 1 1 - B 0 1 * B 1 2) / (B 1 1 * B 2 2) := by
  obtain ⟨e22, e02, e12, e00, e01, e11⟩ := gram_upper_entries B h10 h20 h21
  have e21 : (B * B.transpose) 2 1 = B 1 2 * B 2 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, h20, h21]; ring
  have e10 : (B * B.transpose) 1 0 = B 0 1 * B 1 1 + B 0 2 * B 1 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, h10]; ring
  have hD := lineD_upper B h10 h20 h21
  set G : Mat3 := B * B.transpose with hG
  have c0 : lineChart G 0 = (G 0 1 * G 2 2 - G 0 2 * G 2 1) / lineD G := rfl
  have c1 : lineChart G 1 = (G 0 2 * G 1 1 - G 0 1 * G 1 2) / lineD G := rfl
  constructor
  · rw [c0, hD, e01, e22, e02, e21]
    field_simp
    ring
  · rw [c1, hD, e02, e11, e01, e12]
    field_simp
    ring

end Upper

theorem lineChart_iwasawa (y : RealGL3) :
    lineChart (gramOf y) 0 = (iwasawaB y).val 0 1 / (iwasawaB y).val 1 1 ∧
    lineChart (gramOf y) 1 = ((iwasawaB y).val 0 2 * (iwasawaB y).val 1 1 -
      (iwasawaB y).val 0 1 * (iwasawaB y).val 1 2) / ((iwasawaB y).val 1 1 * (iwasawaB y).val 2 2) ∧
    lineChart (gramOf y) 2 = (iwasawaB y).val 1 2 / (iwasawaB y).val 2 2 ∧
    lineChart (gramOf y) 3 = (iwasawaB y).val 1 1 / (iwasawaB y).val 2 2 := by
  obtain ⟨h10, h20, h21⟩ := iwasawaB_zero_entries y
  obtain ⟨-, -, -, p00, p11, p22⟩ := iwasawaB_upper y
  have hG : gramOf y = (iwasawaB y).val * (iwasawaB y).val.transpose := (iwasawaB_gram y).symm
  rw [hG]
  obtain ⟨c0, c1⟩ := lineChart_upper _ h10 h20 h21 p22.ne' p11.ne'
  obtain ⟨e22, e02, e12, -, -, -⟩ := gram_upper_entries _ h10 h20 h21
  have hD := lineD_upper _ h10 h20 h21
  refine ⟨c0, c1, ?_, ?_⟩
  · have : lineChart ((iwasawaB y).val * (iwasawaB y).val.transpose) 2 =
        ((iwasawaB y).val * (iwasawaB y).val.transpose) 1 2 / ((iwasawaB y).val * (iwasawaB y).val.transpose) 2 2 := by
      rw [lineChart_eq]; rfl
    rw [this, e12, e22]
    field_simp
  · have : lineChart ((iwasawaB y).val * (iwasawaB y).val.transpose) 3 =
        Real.sqrt (lineD ((iwasawaB y).val * (iwasawaB y).val.transpose)) /
          ((iwasawaB y).val * (iwasawaB y).val.transpose) 2 2 := by
      rw [lineChart_eq]; rfl
    rw [this, hD, e22, Real.sqrt_sq (by positivity)]
    field_simp

theorem lineTauG_gramOf (y : RealGL3) : lineTauG (gramOf y) = basePoint (iwALine y) := by
  obtain ⟨h10, h20, h21⟩ := iwasawaB_zero_entries y
  obtain ⟨-, -, -, p00, p11, p22⟩ := iwasawaB_upper y
  obtain ⟨-, -, c2, c3⟩ := lineChart_iwasawa y
  have hdet : 0 < (iwALine y).val.det := by
    rw [Matrix.det_fin_two, iwALine_val, iwALine_val, iwALine_val, iwALine_val]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, h21]
    nlinarith
  unfold basePoint lineTauG
  rw [coe_smul_I_of_upper hdet (by rw [iwALine_val]; simpa using h21), c2, c3]
  simp only [iwALine_val, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  push_cast
  field_simp
  ring

theorem lrC_iwPLine (y : RealGL3) :
    lrC0 (iwPLine y) = lineChart (gramOf y) 1 ∧ lrC1 (iwPLine y) = -lineChart (gramOf y) 0 := by
  obtain ⟨h10, h20, h21⟩ := iwasawaB_zero_entries y
  obtain ⟨-, -, -, p00, p11, p22⟩ := iwasawaB_upper y
  obtain ⟨c0, c1, -, -⟩ := lineChart_iwasawa y
  have hB : (iwPLine y).1.val = (iwasawaB y).val := rfl
  constructor
  · rw [c1, lrC0, lrDet, hB, h21]
    field_simp
    ring
  · rw [c0, lrC1, lrDet, hB, h21]
    field_simp
    ring

theorem derCoeff_expand (n : ℕ) (k : Fin 2) (ν : Fin 3 →₀ ℕ) (Q : Binary.HomogeneousPoly (n + 1)) :
    derCoeff n k ν Q = ∑ j, (binaryWeightBasis (n + 1)).coord j Q * cDer n k ν j := by
  have hQ : Q = ∑ j, (binaryWeightBasis (n + 1)).coord j Q • binaryWeightBasis (n + 1) j := by
    simp only [Module.Basis.coord_apply]
    exact (Module.Basis.sum_repr _ _).symm
  conv_lhs => rw [hQ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, cDer]

theorem coeff_lineRadical_expand (n : ℕ) (χ : RankOneCharacter) (y : RealGL3)
    (Q : Binary.HomogeneousPoly (n + 1)) (ν : Fin 3 →₀ ℕ) :
    (lineRadical n χ (iwPLine y) Q : Poly).coeff ν =
      ∑ j, (binaryWeightBasis (n + 1)).coord j Q * lFunLine n ν (gramOf y) j := by
  obtain ⟨h0, h1⟩ := lrC_iwPLine y
  rw [coe_lineRadical]
  have : (rename (Fin.succ : Fin 2 → Fin 3)
      (lrVecDeriv (algebraMap ℝ ℂ (lrC0 (iwPLine y))) (algebraMap ℝ ℂ (lrC1 (iwPLine y))) (Q : Binary.Poly))).coeff ν =
      (lrC0 (iwPLine y) : ℂ) * derCoeff n 0 ν Q + (lrC1 (iwPLine y) : ℂ) * derCoeff n 1 ν Q := by
    simp only [lrVecDeriv, map_add, map_mul, rename_C, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul,
      derCoeff_apply]
    rfl
  rw [this, derCoeff_expand, derCoeff_expand, h0, h1]
  simp only [lFunLine, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

theorem continuousOn_lineT (a : Fin 5) :
    ContinuousOn (fun x : Mat3 × Mat3 => lineT x.1 x.2 a) (lineDomain ×ˢ Set.univ) := by
  have hfd : ContinuousOn (fderiv ℝ (fun G : Mat3 => lineChart G a)) lineDomain :=
    (contDiffOn_lineChart a).continuousOn_fderiv_of_isOpen isOpen_lineDomain (by simp)
  exact ContinuousOn.clm_apply (hfd.comp continuousOn_fst (fun x hx => hx.1)) continuousOn_snd

theorem coeff_lineSeedLinear_pow (G : Mat3) (n : ℕ) (ν : Fin 3 →₀ ℕ) :
    ((MvPolynomial.C (lineTauG G) * MvPolynomial.X 2 - MvPolynomial.X 1 : Poly) ^ n).coeff ν =
      if ν.sum (fun _ k => k) = n then
        (ν.multinomial : ℂ) * ((0 : ℂ) ^ (ν 0) * (-1 : ℂ) ^ (ν 1) * lineTauG G ^ (ν 2)) else 0 := by
  have hform : (MvPolynomial.C (lineTauG G) * MvPolynomial.X 2 - MvPolynomial.X 1 : Poly) =
      MvPolynomial.C (0 : ℂ) * MvPolynomial.X 0 + MvPolynomial.C (-1 : ℂ) * MvPolynomial.X 1 +
        MvPolynomial.C (lineTauG G) * MvPolynomial.X 2 := by
    simp only [map_zero, zero_mul, zero_add, map_neg, map_one]
    ring
  rw [hform, coeff_linForm_pow]

theorem continuousOn_coeff_lineFormPair (n : ℕ) (h : ℂ → ℂ)
    (hh : ContinuousOn h {z : ℂ | 0 < z.im}) (ν : Fin 3 →₀ ℕ) :
    ContinuousOn (fun x : Mat3 × Mat3 × Mat3 =>
      (lineFormPair (lineSeedForm n h) x.1 x.2.1 x.2.2).coeff ν)
      {x | x.1 ∈ lineDomain} := by
  set S : Set (Mat3 × Mat3 × Mat3) := {x | x.1 ∈ lineDomain} with hS
  have hG : ∀ x ∈ S, x.1 ∈ lineDomain := fun x hx => hx
  have hτ : ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => lineTauG x.1) S :=
    contDiffOn_lineTauG.continuousOn.comp continuousOn_fst hG
  have hT1 : ∀ a : Fin 5, ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => lineT x.1 x.2.1 a) S := by
    intro a
    exact (continuousOn_lineT a).comp (continuousOn_fst.prodMk (continuous_fst.comp continuous_snd).continuousOn)
      (fun x hx => ⟨hx, Set.mem_univ _⟩)
  have hT2 : ∀ a : Fin 5, ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => lineT x.1 x.2.2 a) S := by
    intro a
    exact (continuousOn_lineT a).comp (continuousOn_fst.prodMk (continuous_snd.comp continuous_snd).continuousOn)
      (fun x hx => ⟨hx, Set.mem_univ _⟩)
  have hhτ : ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => h (lineTauG x.1)) S :=
    hh.comp hτ (fun x hx => lineTauG_im_pos (hG x hx))
  have hre : ∀ a : Fin 5, ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => (lineT x.1 x.2.1 a : ℂ)) S :=
    fun a => Complex.continuous_ofReal.comp_continuousOn (hT1 a)
  have hre' : ∀ a : Fin 5, ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => (lineT x.1 x.2.2 a : ℂ)) S :=
    fun a => Complex.continuous_ofReal.comp_continuousOn (hT2 a)
  have hc : ContinuousOn (fun x : Mat3 × Mat3 × Mat3 => h (lineTauG x.1) *
      ((lineTauG x.1 * (lineT x.1 x.2.1 0 : ℂ) + (lineT x.1 x.2.1 1 : ℂ)) *
          ((lineT x.1 x.2.2 2 : ℂ) + Complex.I * (lineT x.1 x.2.2 3 : ℂ)) -
        (lineTauG x.1 * (lineT x.1 x.2.2 0 : ℂ) + (lineT x.1 x.2.2 1 : ℂ)) *
          ((lineT x.1 x.2.1 2 : ℂ) + Complex.I * (lineT x.1 x.2.1 3 : ℂ)))) S :=
    hhτ.mul ((((hτ.mul (hre 0)).add (hre 1)).mul ((hre' 2).add (continuousOn_const.mul (hre' 3)))).sub
      (((hτ.mul (hre' 0)).add (hre' 1)).mul ((hre 2).add (continuousOn_const.mul (hre 3)))))
  have hfun : (fun x : Mat3 × Mat3 × Mat3 => (lineFormPair (lineSeedForm n h) x.1 x.2.1 x.2.2).coeff ν) =
      fun x => h (lineTauG x.1) *
        ((lineTauG x.1 * (lineT x.1 x.2.1 0 : ℂ) + (lineT x.1 x.2.1 1 : ℂ)) *
            ((lineT x.1 x.2.2 2 : ℂ) + Complex.I * (lineT x.1 x.2.2 3 : ℂ)) -
          (lineTauG x.1 * (lineT x.1 x.2.2 0 : ℂ) + (lineT x.1 x.2.2 1 : ℂ)) *
            ((lineT x.1 x.2.1 2 : ℂ) + Complex.I * (lineT x.1 x.2.1 3 : ℂ))) *
        (if ν.sum (fun _ k => k) = n then
          (ν.multinomial : ℂ) * ((0 : ℂ) ^ (ν 0) * (-1 : ℂ) ^ (ν 1) * lineTauG x.1 ^ (ν 2)) else 0) := by
    funext x
    rw [lineFormPair_lineSeedForm, MvPolynomial.coeff_C_mul, coeff_lineSeedLinear_pow]
  rw [hfun]
  refine hc.mul ?_
  split_ifs
  · exact continuousOn_const.mul ((continuousOn_const.mul continuousOn_const).mul (hτ.pow _))
  · exact continuousOn_const

theorem cholDomain_subset_lineDomain {P : Mat3} (hP : Pᵀ = P) (hd : P ∈ cholDomain) : P ∈ lineDomain := by
  obtain ⟨hs, hD, hdet⟩ := hd
  have hqP : cholLine P * (cholLine P)ᵀ = P := cholLine_mul_transpose P hP hs hD hdet
  have hq : (cholLine P).det ≠ 0 := (cholLine_det_pos hs hD hdet).ne'
  rw [← hqP]
  exact gram_mem_lineDomain _ hq

/-- The cup of the line potential and the line radical at three Gram matrices (coefficient `ν`). -/
def cupCoeffLine {n : ℕ} {F : ℂ → ℂ} (P : PotentialDatum n F) (ν : Fin 3 →₀ ℕ) (G₀ G₁ G₂ : Mat3) : ℂ :=
  ∑ j, (P.aFunLine G₁ j - P.aFunLine G₀ j) * (lFunLine n ν G₂ j - lFunLine n ν G₁ j)

/-- The edge-cochain boundary term of the line bridge (coefficient `ν`). -/
def bdryCoeffLine {n : ℕ} {F : ℂ → ℂ} (P : PotentialDatum n F) (ν : Fin 3 →₀ ℕ) (G₀ G₁ G₂ : Mat3) : ℂ :=
  cupEdge (PotentialDatum.dotPairing (n + 2)) P.aFunLine (lFunLine n ν) G₁ G₂ -
    cupEdge (PotentialDatum.dotPairing (n + 2)) P.aFunLine (lFunLine n ν) G₀ G₂ +
    cupEdge (PotentialDatum.dotPairing (n + 2)) P.aFunLine (lFunLine n ν) G₀ G₁

/-- The inner polynomial of a line-type source: radical difference applied to the scaled difference of
the Levi cocycle values at the Iwasawa factors. -/
def holInnerLine (n : ℕ) (χ : RankOneCharacter) (c : ℂ) (α : BinaryRealGL → Binary.HomogeneousPoly (n + 1))
    (Y : Fin 3 → RealGL3) : HomogeneousPoly n :=
  (lineRadical n χ (iwPLine (Y 2)) - lineRadical n χ (iwPLine (Y 1))) (c • (α (iwALine (Y 1)) - α (iwALine (Y 0))))

/-- **A line-type source cochain, coefficient `κ`, is the line integral cochain minus the coboundary of the edge
cochain** (potential `α` reproduced by the vector potential `P`). -/
theorem coeff_holLineSource_bridge (n : ℕ) (χ : RankOneCharacter)
    (hχ : ∀ t : ℝˣ, χ.toMonoidHom (realAdeleUnit t) = 1) (c : ℂ)
    (α : BinaryRealGL → Binary.HomogeneousPoly (n + 1)) (gR : RealGL3) (y : Fin 3 → RealGL3)
    (F : ℂ → ℂ) (P : PotentialDatum n F)
    (hpot : ∀ (A : BinaryRealGL) (j : Fin (n + 2)), P.A (basePoint A) j =
      c * (binaryWeightBasis (n + 1)).coord j (α A))
    (hF : ContinuousOn F {z : ℂ | 0 < z.im}) (κ : Fin 3 →₀ ℕ) :
    ((realCoefficientComponent n χ gR⁻¹
        (holInnerLine n χ c α (fun i => gR * y i)) : HomogeneousPoly n) : Poly).coeff κ =
      lineIntG n (fun z => (-1) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) * F z) gR.val
        (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ -
      ∑ ν ∈ degSet n, (SeedC3.rho (gR.val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
        bdryCoeffLine P ν (gramOf (gR * y 0)) (gramOf (gR * y 1)) (gramOf (gR * y 2)) := by
  set Y : Fin 3 → RealGL3 := fun i => gR * y i with hY
  set Γ' : Fin 3 → Mat3 := fun i => gramOf (Y i) with hΓ'
  have hpd : ∀ i, (Γ' i).PosDef := fun i => posDef_gramOf _
  have hcond := affTri_mem_cholDomain (hpd 0) (hpd 1) (hpd 2)
  have hdom : ∀ p ∈ stdTriangle, affTri (Γ' 0) (Γ' 1) (Γ' 2) p ∈ lineDomain := fun p hp =>
    cholDomain_subset_lineDomain (posDef_transpose (posDef_affTri (hpd 0) (hpd 1) (hpd 2) hp)) (hcond p hp)
  have hs : ∀ i, (Γ' i)ᵀ = Γ' i := fun i => posDef_transpose (hpd i)
  set Q : Binary.HomogeneousPoly (n + 1) := c • (α (iwALine (Y 1)) - α (iwALine (Y 0))) with hQ
  set Φ : HomogeneousPoly n := (lineRadical n χ (iwPLine (Y 2)) - lineRadical n χ (iwPLine (Y 1))) Q
    with hΦ
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
  have hlhs : ((realCoefficientComponent n χ gR⁻¹
        (holInnerLine n χ c α (fun i => gR * y i)) : HomogeneousPoly n) : Poly).coeff κ =
      ∑ ν ∈ degSet n, (Φ : Poly).coeff ν *
        (SeedC3.rho (gR.val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ := by
    rw [hsrc, rcc_inv_eq_rho n χ hχ gR]
    exact coeff_rho_eq_sum _ n _ (fun m' hm' => coeff_eq_zero_of_sum_ne
      ((MvPolynomial.mem_homogeneousSubmodule n _).mp Φ.2) m' hm') κ
  have hbr := fun ν => P.line_cup_bridge ν (Γ' 0) (Γ' 1) (Γ' 2) hdom
  set hh : ℂ → ℂ := fun z => (-1) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) * F z with hhdef
  have hQ1 : Γ' 1 - Γ' 0 = gR.val * (gramOf (y 1) - gramOf (y 0)) * gR.val.transpose := by
    simp only [hΓ', hY, gramOf_mul, Matrix.mul_sub, Matrix.sub_mul]
  have hQ2 : Γ' 2 - Γ' 0 = gR.val * (gramOf (y 2) - gramOf (y 0)) * gR.val.transpose := by
    simp only [hΓ', hY, gramOf_mul, Matrix.mul_sub, Matrix.sub_mul]
  have hP : ∀ p, gR.val * affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) p * gR.val.transpose =
      affTri (Γ' 0) (Γ' 1) (Γ' 2) p := by
    intro p
    simp only [hΓ', hY, gramOf_mul]
    rw [affTri_congr]
  have hint : lineIntG n hh gR.val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ =
      ∑ ν ∈ degSet n, (∫ p in stdTriangle, (lineFormPair (lineSeedForm n hh)
        (affTri (Γ' 0) (Γ' 1) (Γ' 2) p) (Γ' 1 - Γ' 0) (Γ' 2 - Γ' 0)).coeff ν) *
          (SeedC3.rho (gR.val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ := by
    unfold lineIntG twPullLine
    simp_rw [hP, ← hQ1, ← hQ2]
    refine integral_coeff_rho _ n _ _ (fun p => isHomogeneous_lineFormPair_seed n hh _ _ _) (fun ν => ?_) κ
    have hhc : ContinuousOn hh {z : ℂ | 0 < z.im} := by
      simp only [hhdef]
      exact continuousOn_const.mul hF
    have hc : ContinuousOn (fun p : ℝ × ℝ => (lineFormPair (lineSeedForm n hh)
        (affTri (Γ' 0) (Γ' 1) (Γ' 2) p) (Γ' 1 - Γ' 0) (Γ' 2 - Γ' 0)).coeff ν) stdTriangle := by
      have h1 := continuousOn_coeff_lineFormPair n hh hhc ν
      have hA : ContinuousOn (fun p : ℝ × ℝ => (affTri (Γ' 0) (Γ' 1) (Γ' 2) p, Γ' 1 - Γ' 0, Γ' 2 - Γ' 0))
          stdTriangle :=
        (continuous_affTri (Γ' 0) (Γ' 1) (Γ' 2)).continuousOn.prodMk (continuousOn_const.prodMk continuousOn_const)
      have hmap : Set.MapsTo (fun p : ℝ × ℝ => (affTri (Γ' 0) (Γ' 1) (Γ' 2) p, Γ' 1 - Γ' 0, Γ' 2 - Γ' 0))
          stdTriangle {x : Mat3 × Mat3 × Mat3 | x.1 ∈ lineDomain} := fun p hp => hdom p hp
      have hC := h1.comp hA hmap
      simpa only [Function.comp_def] using hC
    exact hc.integrableOn_compact isCompact_stdTriangle
  rw [hlhs, hint]
  simp_rw [hΦc]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [hbr ν]
  unfold cupCoeffLine bdryCoeffLine
  ring

/-- **The line source cochain, coefficient `κ`, is the line integral cochain minus the coboundary of the edge
cochain** (potential `P` reproducing the sign-twisted Levi cocycle). -/
theorem coeff_lineSourceAt_bridge (n : ℕ) (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ t : ℝˣ, D.chi.toMonoidHom (realAdeleUnit t) = 1)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) (F : ℂ → ℂ) (P : PotentialDatum n F)
    (hpot : ∀ (A : BinaryRealGL) (j : Fin (n + 2)), P.A (basePoint A) j =
      cFLine D g * (binaryWeightBasis (n + 1)).coord j (E.α A (x * bFLine g)))
    (hF : ContinuousOn F {z : ℂ | 0 < z.im}) (κ : Fin 3 →₀ ℕ) :
    ((lineSourceAt D E y g x : HomogeneousPoly n) : Poly).coeff κ =
      lineIntG n (fun z => (-1) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) * F z) (realGroup g).val
        (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ -
      ∑ ν ∈ degSet n, (SeedC3.rho ((realGroup g).val)⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
        bdryCoeffLine P ν (gramOf (realGroup g * y 0)) (gramOf (realGroup g * y 1))
          (gramOf (realGroup g * y 2)) :=
  coeff_holLineSource_bridge n D.chi hχ (cFLine D g) (fun A => E.α A (x * bFLine g)) (realGroup g) y F P hpot hF κ

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
