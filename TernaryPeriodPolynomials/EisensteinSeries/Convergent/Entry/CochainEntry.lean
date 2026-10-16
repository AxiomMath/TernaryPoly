module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.LevelStatements
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.TCommute
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Section
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Exchange
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.AdelicRearrange
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.AntiCommute
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.PolyIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.SourceAnti

@[expose] public section


/-!
# The archimedean entry at the level of cochains (ML4b, step (a))

For the symmetrized Eichler datum (holomorphic part plus `J`-reflected part) the plane and line **integral cochains**
`cOmega`, `cSigma` (coefficients `cOmegaCoeff`, `cSigmaCoeff`) are the sums of the Gram-triangle integrals of the seeds
`ω_h` at `g_∞` and at the reflected group element (`ε g_∞`, resp. `Λ g_∞`).  `standardIntegral_cOmega` computes the full
adelic standard integral `∫_{U(A)} c_Ω(w⁻¹ u g) du` of the plane cochain: split the radical into its real part and its
finite part (`integral_swapMid`), integrate the finite part first (the exchange lemma `planeIntG_exchange` and the finite
identity R-e `FiniteEntryIdentity`, giving `-r` times the plane cochain of the line datum, `inner_plane`), then the real
part (`tcommute`, `tcommute_anti`: `c_∞ = -2πi/(n+1)` times the line cochain).  Result:

`∫ c_Ω(w⁻¹ u g) du = (-r) · c_∞ · c_Σ(g) = r · 2πi/(n+1) · c_Σ(g)`.

Sign ledger: `h_plane = (-1)ⁿ (n+1) F`, `h_line = (-1)^{n+1} (n+1) F` for the same `F`, whence the extra minus sign.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.SourceConstruction

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem realGroup_weyl : realGroup (weyl : AdelicGL) = weyl := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realGroup, weyl]

theorem finiteGroup_weyl : finiteGroup (weyl : AdelicGL) = weyl := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finiteGroup, weyl]

theorem weyl_inv_mul_lineUnipotent_val (s t : ℝ) :
    ((weyl : GL3 ℝ)⁻¹ * lineUnipotent s t).val = entryFrame s t := by
  rw [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, lineUnipotent, upperUnipotent, entryFrame, Matrix.mul_apply, Fin.sum_univ_three]

theorem realGroup_entry (a b : Adeles) (g : AdelicGL) :
    (realGroup (weyl⁻¹ * lineUnipotent a b * g)).val = entryFrame a.1 b.1 * (realGroup g).val := by
  rw [map_mul, map_mul, map_inv, realGroup_weyl, realGroup_lineUnipotent, Units.val_mul]
  congr 1
  exact weyl_inv_mul_lineUnipotent_val a.1 b.1

theorem finiteGroup_entry (a b : Adeles) (g : AdelicGL) :
    finiteGroup (weyl⁻¹ * lineUnipotent a b * g) =
      finiteGroup (weyl⁻¹ * lineUnipotent ((0, a.2) : Adeles) ((0, b.2) : Adeles) * g) := by
  rw [map_mul, map_mul, map_mul, map_mul, map_inv, finiteGroup_weyl, finiteGroup_lineUnipotent,
    finiteGroup_lineUnipotent]
  rfl


/-! ## The integral cochains of the symmetrized Eichler datum -/

/-- The plane holomorphic datum `h = (-1)ⁿ (n+1) c_F(g) · ½ F(x · b_F(g))`. -/
def planeHolData (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (g : AdelicGL)
    (x : BinaryAdelicGL) (z : ℂ) : ℂ :=
  (-1) ^ n * ((n + 1 : ℕ) : ℂ) * (cF D g * 2⁻¹ * F (x * bF g) z)

/-- The line holomorphic datum `h = (-1)^{n+1} (n+1) c_F^{line}(g) · ½ F(x · b_F^{line}(g))`. -/
def lineHolData (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (g : AdelicGL)
    (x : BinaryAdelicGL) (z : ℂ) : ℂ :=
  (-1) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) * (cFLine D g * 2⁻¹ * F (x * bFLine g) z)

/-- The coefficient `κ` of the plane integral cochain: the holomorphic part at `g_∞` plus the reflected part at
`ε g_∞`, `ε = diag(-1,1,1)`. -/
def cOmegaCoeff (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (κ : Fin 3 →₀ ℕ) : ℂ :=
  planeIntG n (planeHolData n D F g 1) (realGroup g).val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ +
  planeIntG n (planeHolData n D F g (atInfinity UpperHalfPlane.J)) (epsJ.val * (realGroup g).val)
    (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ

/-- The coefficient `κ` of the line integral cochain: the holomorphic part at `g_∞` plus the reflected part at
`Λ g_∞`, `Λ = diag(1,-1,1)`. -/
def cSigmaCoeff (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (κ : Fin 3 →₀ ℕ) : ℂ :=
  lineIntG n (lineHolData n D F g 1) (realGroup g).val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ +
  lineIntG n (lineHolData n D F g (atInfinity UpperHalfPlane.J)) (lamM * (realGroup g).val)
    (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ

/-- The plane integral cochain, as a homogeneous polynomial. -/
def cOmega (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) : HomogeneousPoly n :=
  ofCoeffs n (cOmegaCoeff n D F y g)

/-- The line integral cochain, as a homogeneous polynomial. -/
def cSigma (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) : HomogeneousPoly n :=
  ofCoeffs n (cSigmaCoeff n D F y g)

theorem cOmegaCoeff_entry (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (a b : Adeles) (κ : Fin 3 →₀ ℕ) :
    cOmegaCoeff n D F y (weyl⁻¹ * lineUnipotent a b * g) κ =
      planeIntG n (planeHolData n D F (finiteEntryElement (a.2, b.2) g) 1)
        (entryFrame a.1 b.1 * (realGroup g).val) (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ +
      planeIntG n (planeHolData n D F (finiteEntryElement (a.2, b.2) g) (atInfinity UpperHalfPlane.J))
        (epsJ.val * (entryFrame a.1 b.1 * (realGroup g).val))
        (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ := by
  have hfin : ∀ x, planeHolData n D F (weyl⁻¹ * lineUnipotent a b * g) x =
      planeHolData n D F (finiteEntryElement (a.2, b.2) g) x := by
    intro x
    unfold planeHolData cF bF
    rw [finiteGroup_entry]
    rfl
  unfold cOmegaCoeff
  rw [realGroup_entry, hfin, hfin]

theorem planeHolData_eq (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (g : AdelicGL)
    (x : BinaryAdelicGL) :
    planeHolData n D F g x = fun z => ((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * (cF D g * F (x * bF g) z) := by
  funext z; unfold planeHolData; ring

theorem planeIntG_congr_on (n : ℕ) (h h' : ℂ → ℂ) {M : Mat3} (hM : M.det ≠ 0) {Γ₀ Γ₁ Γ₂ : Mat3}
    (p₀ : Γ₀.PosDef) (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) (hh : ∀ z : ℂ, 0 < z.im → h z = h' z)
    (κ : Fin 3 →₀ ℕ) : planeIntG n h M Γ₀ Γ₁ Γ₂ κ = planeIntG n h' M Γ₀ Γ₁ Γ₂ κ := by
  rw [planeIntG_eq_tau, planeIntG_eq_tau]
  refine setIntegral_congr_fun measurableSet_stdTriangle fun p hp => ?_
  simp only [hh _ (planeTauPt_mem M hM p₀ p₁ p₂ hp)]

/-- **The finite adelic integral of the plane integral cochain**, at a fixed real frame `G`: by R-e and the exchange
lemma it is `-r` times the plane integral cochain of the line datum (the plane datum carrying the finite weight `ι`). -/
theorem inner_plane (n : ℕ) (D : InducingData n) (ι ιL : AdelicGL → ℂ) (F : BinaryAdelicGL → ℂ → ℂ) (r : ℂ)
    (hRe : FiniteEntryIdentity D ι ιL F r) (g : AdelicGL) (hg : ιL g ≠ 0) (x : BinaryAdelicGL) (G : Mat3) (hG : G.det ≠ 0)
    {Γ₀ Γ₁ Γ₂ : Mat3} (p₀ : Γ₀.PosDef) (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) (κ : Fin 3 →₀ ℕ) :
    Integrable (fun v : FiniteAdeles × FiniteAdeles =>
      ι (finiteEntryElement v g) *
        planeIntG n (planeHolData n D F (finiteEntryElement v g) x) G Γ₀ Γ₁ Γ₂ κ)
      (finiteMeasure.prod finiteMeasure) ∧
    ∫ v : FiniteAdeles × FiniteAdeles, ι (finiteEntryElement v g) *
        planeIntG n (planeHolData n D F (finiteEntryElement v g) x) G Γ₀ Γ₁ Γ₂ κ
        ∂(finiteMeasure.prod finiteMeasure) =
      -r * planeIntG n (lineHolData n D F g x) G Γ₀ Γ₁ Γ₂ κ := by
  obtain ⟨hm, hd, hi⟩ := hRe g hg x
  set K0 : ℂ := (-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹ with hK0
  have hv : ∀ v z, ι (finiteEntryElement v g) * planeHolData n D F (finiteEntryElement v g) x z =
      K0 * (ι (finiteEntryElement v g) *
        (cF D (finiteEntryElement v g) * F (x * bF (finiteEntryElement v g)) z)) := by
    intro v z; unfold planeHolData; rw [hK0]; ring
  have hmeas : Measurable (fun w : (FiniteAdeles × FiniteAdeles) × {z : ℂ // 0 < z.im} =>
      ι (finiteEntryElement w.1 g) * planeHolData n D F (finiteEntryElement w.1 g) x w.2.1) := by
    simp_rw [hv]
    exact hm.const_mul K0
  have hdom : ∀ Z : Set ℂ, IsCompact Z → Z ⊆ {z : ℂ | 0 < z.im} →
      ∃ φ : FiniteAdeles × FiniteAdeles → ℝ, Integrable φ (finiteMeasure.prod finiteMeasure) ∧
        ∀ v, ∀ z ∈ Z, ‖ι (finiteEntryElement v g) * planeHolData n D F (finiteEntryElement v g) x z‖ ≤ φ v := by
    intro Z hZ hZH
    obtain ⟨φ, hφ, hb⟩ := hd Z hZ hZH
    refine ⟨fun v => ‖K0‖ * φ v, hφ.const_mul _, fun v z hz => ?_⟩
    rw [hv, norm_mul]
    exact mul_le_mul_of_nonneg_left (hb v z hz) (norm_nonneg _)
  obtain ⟨hI, hE⟩ := planeIntG_exchange (finiteMeasure.prod finiteMeasure) n
    (fun v z => ι (finiteEntryElement v g) * planeHolData n D F (finiteEntryElement v g) x z)
    G hG p₀ p₁ p₂ κ hmeas hdom
  have hscale : ∀ v, planeIntG n (fun z => ι (finiteEntryElement v g) *
      planeHolData n D F (finiteEntryElement v g) x z) G Γ₀ Γ₁ Γ₂ κ =
      ι (finiteEntryElement v g) * planeIntG n (planeHolData n D F (finiteEntryElement v g) x) G Γ₀ Γ₁ Γ₂ κ :=
    fun v => planeIntG_const_mul n _ _ G Γ₀ Γ₁ Γ₂ κ
  simp_rw [hscale] at hI hE
  refine ⟨hI, hE.trans ?_⟩
  have hfun : ∀ z : ℂ, 0 < z.im → ∫ v, ι (finiteEntryElement v g) *
      planeHolData n D F (finiteEntryElement v g) x z
      ∂(finiteMeasure.prod finiteMeasure) = (-r) * lineHolData n D F g x z := by
    intro z hz
    simp_rw [hv]
    rw [integral_const_mul, hi z hz]
    unfold lineHolData
    rw [pow_succ, hK0]
    push_cast
    ring
  rw [planeIntG_congr_on n _ (fun z => (-r) * lineHolData n D F g x z) hG p₀ p₁ p₂ hfun, planeIntG_const_mul]

theorem lineHolData_props (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ x, DifferentiableOn ℂ (F x) {z : ℂ | 0 < z.im})
    (decay : ∀ x, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖F x z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (g : AdelicGL) (x : BinaryAdelicGL) :
    DifferentiableOn ℂ (lineHolData n D F g x) {z : ℂ | 0 < z.im} ∧
    ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖lineHolData n D F g x z‖ ^ 2 * z.im ^ (n + 3) ≤ M := by
  set K : ℂ := (-1) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) * (cFLine D g * 2⁻¹) with hK
  have hl : ∀ z, lineHolData n D F g x z = K * F (x * bFLine g) z := by
    intro z; unfold lineHolData; rw [hK]; ring
  refine ⟨?_, ?_⟩
  · have := (holomorphic (x * bFLine g)).const_mul K
    exact this.congr fun z _ => hl z
  · obtain ⟨M, hM⟩ := decay (x * bFLine g)
    refine ⟨‖K‖ ^ 2 * M, fun z hz => ?_⟩
    rw [hl, norm_mul, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hM z hz) (sq_nonneg _)

/-- **The standard integral of the plane integral cochain** (cochain-level statement of the archimedean entry):
`∫_{U(A)} c_Ω(w⁻¹ u g) du = (-r) · c_∞ · c_Σ(g)`, `c_∞ = -2πi/(n+1)`, under the finite identity `FiniteEntryIdentity` (required at `g` only, `ιL g ≠ 0`). -/
theorem standardIntegral_cOmega (n : ℕ) (hn : 3 ≤ n) (D : InducingData n) (ι ιL : AdelicGL → ℂ)
    (hι : ∀ g g' : AdelicGL, finiteGroup g = finiteGroup g' → ι g = ι g') (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ x, DifferentiableOn ℂ (F x) {z : ℂ | 0 < z.im})
    (decay : ∀ x, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖F x z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (r : ℂ) (hRe : FiniteEntryIdentity D ι ιL F r) (y : Fin 3 → RealGL3) (g : AdelicGL) (hg : ιL g ≠ 0)
    (κ : Fin 3 →₀ ℕ)
    (hint : Integrable (fun u : Adeles × Adeles =>
      ι (weyl⁻¹ * lineUnipotent u.1 u.2 * g) * cOmegaCoeff n D F y (weyl⁻¹ * lineUnipotent u.1 u.2 * g) κ)
      radicalMeasure) :
    ∫ u : Adeles × Adeles, ι (weyl⁻¹ * lineUnipotent u.1 u.2 * g) *
      cOmegaCoeff n D F y (weyl⁻¹ * lineUnipotent u.1 u.2 * g) κ ∂radicalMeasure =
      (-r * (-2 * Real.pi * Complex.I / ((n : ℂ) + 1))) * cSigmaCoeff n D F y g κ := by
  have hpd : ∀ i, (gramOf (y i)).PosDef := fun i => posDef_gramOf _
  set gR : Mat3 := (realGroup g).val with hgR
  have hgdet : gR.det ≠ 0 := det_ne_zero_realGL3 _
  have hswap := integral_swapMid (volume : Measure ℝ) finiteMeasure (volume : Measure ℝ) finiteMeasure
    (fun u : Adeles × Adeles => ι (weyl⁻¹ * lineUnipotent u.1 u.2 * g) *
      cOmegaCoeff n D F y (weyl⁻¹ * lineUnipotent u.1 u.2 * g) κ) hint
  change ∫ u : Adeles × Adeles, ι (weyl⁻¹ * lineUnipotent u.1 u.2 * g) *
      cOmegaCoeff n D F y (weyl⁻¹ * lineUnipotent u.1 u.2 * g) κ
      ∂((volume.prod finiteMeasure).prod (volume.prod finiteMeasure)) = _ at hswap
  have hrad : (radicalMeasure : Measure (Adeles × Adeles)) =
      (volume.prod finiteMeasure).prod (volume.prod finiteMeasure) := rfl
  rw [hrad, hswap]
  -- the inner integral over the finite coordinates
  have hinner : ∀ x : ℝ × ℝ, ∫ w : FiniteAdeles × FiniteAdeles,
      ι (weyl⁻¹ * lineUnipotent ((x.1, w.1) : Adeles) ((x.2, w.2) : Adeles) * g) *
      cOmegaCoeff n D F y (weyl⁻¹ * lineUnipotent ((x.1, w.1) : Adeles) ((x.2, w.2) : Adeles) * g) κ
        ∂(finiteMeasure.prod finiteMeasure) =
      -r * (planeIntG n (lineHolData n D F g 1) (entryFrame x.1 x.2 * gR) (gramOf (y 0)) (gramOf (y 1))
          (gramOf (y 2)) κ +
        planeIntG n (lineHolData n D F g (atInfinity UpperHalfPlane.J)) (epsJ.val * (entryFrame x.1 x.2 * gR))
          (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ) := by
    intro x
    have hG : (entryFrame x.1 x.2 * gR).det ≠ 0 := by
      rw [Matrix.det_mul, entryFrame_det_eq]; simpa using hgdet
    have hεG : (epsJ.val * (entryFrame x.1 x.2 * gR)).det ≠ 0 := by
      rw [Matrix.det_mul]
      exact mul_ne_zero (det_ne_zero_realGL3 epsJ) hG
    obtain ⟨I1, E1⟩ := inner_plane n D ι ιL F r hRe g hg 1 _ hG (hpd 0) (hpd 1) (hpd 2) κ
    obtain ⟨I2, E2⟩ := inner_plane n D ι ιL F r hRe g hg (atInfinity UpperHalfPlane.J) _ hεG (hpd 0) (hpd 1) (hpd 2) κ
    have hιe : ∀ w : FiniteAdeles × FiniteAdeles,
        ι (weyl⁻¹ * lineUnipotent ((x.1, w.1) : Adeles) ((x.2, w.2) : Adeles) * g) =
          ι (finiteEntryElement w g) := fun w => hι _ _ (finiteGroup_entry _ _ _)
    simp_rw [cOmegaCoeff_entry, hιe, mul_add]
    rw [integral_add I1 I2, E1, E2]
  simp_rw [hinner]
  obtain ⟨hh1, M1, hM1⟩ := lineHolData_props n D F holomorphic decay g 1
  obtain ⟨hh2, M2, hM2⟩ := lineHolData_props n D F holomorphic decay g (atInfinity UpperHalfPlane.J)
  obtain ⟨hI1, hE1⟩ := tcommute n hn _ hh1 M1 hM1 gR hgdet _ _ _ (hpd 0) (hpd 1) (hpd 2) κ
  obtain ⟨hI2, hE2⟩ := tcommute_anti n hn _ hh2 M2 hM2 gR hgdet _ _ _ (hpd 0) (hpd 1) (hpd 2) κ
  rw [← Measure.volume_eq_prod, integral_const_mul, integral_add hI1 hI2, hE1, hE2]
  unfold cSigmaCoeff
  ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
