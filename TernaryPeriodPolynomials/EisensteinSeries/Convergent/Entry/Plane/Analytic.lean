module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Stokes
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.ParamAnalytic
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.OrbitIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.BridgeAnalytic

@[expose] public section


/-!
# Real analyticity of the boundary integrals of the plane seed

The functions entering the boundary integrals `J_ν` of `Entry/PlaneStokes` are real analytic on the Gram domain:
`gramPlaneTau`, `lFun`, `pointCoord ∘ gramPlaneTau`, `planeDTau` (jointly in the base point and the direction), hence
the coefficient `Kfun`.  `analyticAt_JgenInt`: for an orbit-type function `O : ℂ → G` analytic on the upper half plane
(`G` a complex Banach space), the boundary integral `JgenInt O n μ x y = ∫₀¹ K_μ(γ(t), y-x) • O(τ(γ(t))) dt` along the
Gram segment is jointly real analytic in `(x, y)` at all pairs of positive definite matrices (by
`analyticAt_param_integral`).

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory Set MvPolynomial Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem analyticAt_of_contDiffOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E} (hs : IsOpen s)
    (h : ContDiffOn ℝ ⊤ f s) {x : E} (hx : x ∈ s) : AnalyticAt ℝ f x :=
  (h.contDiffAt (hs.mem_nhds hx)).analyticAt

theorem analyticAt_gramPlaneTau {G : Mat3} (hG : G ∈ gramDomain) : AnalyticAt ℝ gramPlaneTau G :=
  analyticAt_of_contDiffOn isOpen_gramDomain contDiffOn_gramPlaneTau hG

theorem analyticAt_lFun (n : ℕ) (μ : Fin 3 →₀ ℕ) {G : Mat3} (hG : G ∈ gramDomain) :
    AnalyticAt ℝ (lFun n μ) G :=
  analyticAt_of_contDiffOn isOpen_gramDomain (contDiffOn_lFun n μ) hG

theorem analyticAt_pointCoord (n : ℕ) (j : Fin (n + 2)) (z : ℂ) :
    AnalyticAt ℝ (fun w : ℂ => pointCoord n w j) z :=
  (binaryPointPower_functional_analytic (n + 1)
    ((binaryWeightBasis (n + 1)).coord j) z).restrictScalars


theorem contDiffOn_schurDeriv (i j : Fin 3) :
    ContDiffOn ℝ ⊤ (fun x : Mat3 × Mat3 => schurDeriv x.1 x.2 i j) {x | 0 < x.1 2 2} := by
  have h22 : ∀ x ∈ {x : Mat3 × Mat3 | 0 < x.1 2 2}, x.1 2 2 ≠ 0 := fun x hx => hx.ne'
  have e : ∀ (a b : Fin 3), ContDiff ℝ ⊤ (fun x : Mat3 × Mat3 => x.1 a b) := fun a b => by fun_prop
  have d : ∀ (a b : Fin 3), ContDiff ℝ ⊤ (fun x : Mat3 × Mat3 => x.2 a b) := fun a b => by fun_prop
  unfold schurDeriv
  refine ((d i j).contDiffOn.sub ?_).add ?_
  · exact ((((d i 2).mul (e j 2)).add ((e i 2).mul (d j 2))).contDiffOn).div (e 2 2).contDiffOn h22
  · exact ((((e i 2).mul (e j 2)).mul (d 2 2)).contDiffOn).div ((e 2 2).pow 2).contDiffOn
      (fun x hx => pow_ne_zero 2 (h22 x hx))

theorem analyticAt_planeDTau {G : Mat3} (hG : G ∈ gramDomain) (D : Mat3) :
    AnalyticAt ℝ (fun x : Mat3 × Mat3 => planeDTau x.1 x.2) (G, D) := by
  set S : Set (Mat3 × Mat3) := {x | x.1 ∈ gramDomain} with hS
  have hSo : IsOpen S := isOpen_gramDomain.preimage continuous_fst
  have hmem : (G, D) ∈ S := hG
  have cG : ∀ f : Mat3 → ℂ, ContDiffOn ℝ ⊤ f gramDomain → ContDiffOn ℝ ⊤ (fun x : Mat3 × Mat3 => f x.1) S :=
    fun f hf => hf.comp contDiff_fst.contDiffOn (fun x hx => hx)
  have hτ : ContDiffOn ℝ ⊤ (fun x : Mat3 × Mat3 => gramPlaneTau x.1) S := cG _ contDiffOn_gramPlaneTau
  have hdet : ContDiffOn ℝ ⊤ (fun G : Mat3 => (gramSchur G).det) gramDomain := by
    simp only [Matrix.det_fin_two]
    exact ((contDiffOn_gramSchur 0 0).mul (contDiffOn_gramSchur 1 1)).sub
      ((contDiffOn_gramSchur 0 1).mul (contDiffOn_gramSchur 1 0))
  have hsq : ContDiffOn ℝ ⊤ (fun G : Mat3 => Real.sqrt (gramSchur G).det) gramDomain :=
    hdet.sqrt (fun G hG => hG.2.2.ne')
  have hsqinv : ContDiffOn ℝ ⊤ (fun x : Mat3 × Mat3 => ((1 / (2 * Real.sqrt (gramSchur x.1).det) : ℝ) : ℂ)) S := by
    refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
    have hs1 : ContDiffOn ℝ ⊤ (fun x : Mat3 × Mat3 => Real.sqrt (gramSchur x.1).det) S :=
      hsq.comp contDiff_fst.contDiffOn (fun x hx => hx)
    refine contDiffOn_const.div (contDiffOn_const.mul hs1) ?_
    intro x hx
    have : 0 < Real.sqrt (gramSchur x.1).det := Real.sqrt_pos.mpr hx.2.2
    positivity
  have hsd : ∀ i j : Fin 2, ContDiffOn ℝ ⊤ (fun x : Mat3 × Mat3 => ((schurDeriv2 x.1 x.2 i j : ℝ) : ℂ)) S := by
    intro i j
    refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
    exact (contDiffOn_schurDeriv i.castSucc j.castSucc).mono (fun x hx => hx.1)
  have hall : ContDiffOn ℝ ⊤ (fun x : Mat3 × Mat3 => planeDTau x.1 x.2) S := by
    have e : ∀ x : Mat3 × Mat3, x ∈ S → planeDTau x.1 x.2 = Complex.I * ((1 / (2 * Real.sqrt (gramSchur x.1).det) : ℝ) : ℂ) *
        (((schurDeriv2 x.1 x.2 0 0 : ℝ) : ℂ) - 2 * gramPlaneTau x.1 * ((schurDeriv2 x.1 x.2 0 1 : ℝ) : ℂ) +
          gramPlaneTau x.1 ^ 2 * ((schurDeriv2 x.1 x.2 1 1 : ℝ) : ℂ)) := by
      intro x hx
      have : 0 < Real.sqrt (gramSchur x.1).det := Real.sqrt_pos.mpr hx.2.2
      unfold planeDTau
      push_cast
      rw [div_eq_mul_one_div, one_div]
    refine ContDiffOn.congr ?_ e
    exact (contDiffOn_const.mul hsqinv).mul
      (((hsd 0 0).sub ((contDiffOn_const.mul hτ).mul (hsd 0 1))).add ((hτ.pow 2).mul (hsd 1 1)))
  exact analyticAt_of_contDiffOn hSo hall hmem


theorem analyticAt_Kfun (n : ℕ) (μ : Fin 3 →₀ ℕ) {G : Mat3} (hG : G ∈ gramDomain) (D : Mat3) :
    AnalyticAt ℝ (fun x : Mat3 × Mat3 => Kfun n μ x.1 x.2) (G, D) := by
  have hfst : AnalyticAt ℝ (fun x : Mat3 × Mat3 => x.1) (G, D) := analyticAt_fst
  have hτ : AnalyticAt ℝ (fun x : Mat3 × Mat3 => gramPlaneTau x.1) (G, D) :=
    (analyticAt_gramPlaneTau hG).comp_of_eq hfst rfl
  have hl : ∀ j, AnalyticAt ℝ (fun x : Mat3 × Mat3 => lFun n μ x.1 j) (G, D) := fun j =>
    ((analyticAt_pi_iff.mp (analyticAt_lFun n μ hG)) j).comp_of_eq hfst rfl
  have hp : ∀ j, AnalyticAt ℝ (fun x : Mat3 × Mat3 => pointCoord n (gramPlaneTau x.1) j) (G, D) := fun j =>
    (analyticAt_pointCoord n j _).comp_of_eq hτ rfl
  unfold Kfun
  exact (Finset.analyticAt_fun_sum _ (fun j _ => (hp j).mul (hl j))).mul (analyticAt_planeDTau hG D)

section JInt

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [CompleteSpace G]

/-- The generic boundary integral of an `G`-valued orbit-type function `O` along the Gram segment `x → y`. -/
def JgenInt (O : ℂ → G) (n : ℕ) (μ : Fin 3 →₀ ℕ) (x y : Mat3) : G :=
  ∫ t in (0 : ℝ)..1, Kfun n μ (x + t • (y - x)) (y - x) • O (gramPlaneTau (x + t • (y - x)))

theorem segment_mem_gramDomain' {x y : Mat3} (hx : x.PosDef) (hy : y.PosDef) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (y - x) ∈ gramDomain := by
  have := posDef_affTri hx hy hy (p := (t, 0)) ⟨ht.1, le_rfl, by simpa using ht.2⟩
  have h2 : (x + t • (y - x)).PosDef := by simpa [affTri] using this
  exact cholDomain_subset_gramDomain (posDef_transpose h2) (posDef_mem_cholDomain h2)

theorem analyticAt_segment_map (s : ℝ) (x y : Mat3) :
    AnalyticAt ℝ (fun p : ℝ × (Mat3 × Mat3) => p.2.1 + p.1 • (p.2.2 - p.2.1)) (s, (x, y)) := by
  have : ContDiff ℝ ⊤ (fun p : ℝ × (Mat3 × Mat3) => p.2.1 + p.1 • (p.2.2 - p.2.1)) := by fun_prop
  exact this.contDiffAt.analyticAt

theorem analyticAt_segment_dir (s : ℝ) (x y : Mat3) :
    AnalyticAt ℝ (fun p : ℝ × (Mat3 × Mat3) => p.2.2 - p.2.1) (s, (x, y)) := by
  have : ContDiff ℝ ⊤ (fun p : ℝ × (Mat3 × Mat3) => p.2.2 - p.2.1) := by fun_prop
  exact this.contDiffAt.analyticAt

theorem analyticAt_segment_Kfun (n : ℕ) (μ : Fin 3 →₀ ℕ) (s : ℝ) (x y : Mat3)
    (hmem : x + s • (y - x) ∈ gramDomain) :
    AnalyticAt ℝ (fun p : ℝ × (Mat3 × Mat3) =>
      Kfun n μ (p.2.1 + p.1 • (p.2.2 - p.2.1)) (p.2.2 - p.2.1)) (s, (x, y)) := by
  have h := AnalyticAt.comp_of_eq (analyticAt_Kfun n μ hmem (y - x))
    ((analyticAt_segment_map s x y).prod (analyticAt_segment_dir s x y)) rfl
  exact h

theorem analyticAt_segment_tau (s : ℝ) (x y : Mat3) (hmem : x + s • (y - x) ∈ gramDomain) :
    AnalyticAt ℝ (fun p : ℝ × (Mat3 × Mat3) => gramPlaneTau (p.2.1 + p.1 • (p.2.2 - p.2.1)))
      (s, (x, y)) := by
  have h := AnalyticAt.comp_of_eq (analyticAt_gramPlaneTau hmem) (analyticAt_segment_map s x y) rfl
  exact h

theorem analyticAt_JgenInt (O : ℂ → G) (hO : ∀ z : ℂ, 0 < z.im → AnalyticAt ℝ O z) (n : ℕ)
    (μ : Fin 3 →₀ ℕ) {x y : Mat3} (hx : x.PosDef) (hy : y.PosDef) :
    AnalyticAt ℝ (fun q : Mat3 × Mat3 => JgenInt O n μ q.1 q.2) (x, y) := by
  unfold JgenInt
  refine analyticAt_param_integral (fun p : ℝ × (Mat3 × Mat3) =>
    Kfun n μ (p.2.1 + p.1 • (p.2.2 - p.2.1)) (p.2.2 - p.2.1) •
      O (gramPlaneTau (p.2.1 + p.1 • (p.2.2 - p.2.1)))) (x, y) (fun s hs => ?_)
  have hmem : x + s • (y - x) ∈ gramDomain := segment_mem_gramDomain' hx hy hs
  have hOτ : AnalyticAt ℝ (fun p : ℝ × (Mat3 × Mat3) => O (gramPlaneTau (p.2.1 + p.1 • (p.2.2 - p.2.1))))
      (s, (x, y)) := by
    have h := AnalyticAt.comp_of_eq (hO _ (gramPlaneTau_im_pos_of_domain hmem))
      (analyticAt_segment_tau s x y hmem) rfl
    exact h
  exact (analyticAt_segment_Kfun n μ s x y hmem).smul hOτ

end JInt

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
