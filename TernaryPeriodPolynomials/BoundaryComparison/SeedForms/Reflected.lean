module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.SeedGram

@[expose] public section


/-!
# R1c: the reflected half of `cOmega` is the `ε`-conjugation transport of the seed cocycle of `H' = F(J · b_F(1))`

Formalized by Claude Sonnet 5.5.
Paper: Lemma C.3 and the finite reflection projection.

* `toPoly_realCoefficient`: `ρ(g)` on `HomogeneousPoly n` is the library's `rho g.val`, for every `g ∈ GL₃(ℝ)`.
* `epsConj`, `epsHom`, `eps_norm`: conjugation by `ε = diag(-1,1,1)` preserves `Γ_P = Γ(N) ∩ P(ℤ)` and `realLevel Γ_P`.
* `coeff_rho_gramCochainW_seed`, `reflCocycle`, `coeff_reflCocycle`: the reflected half `planeIntG n H' ε Δ(y) κ` is the coefficient of the
  homogeneous cocycle `(ε⁻¹ • F_{H'})(y) = ρ(ε)⁻¹ F_{H'}(ε y)` (`F_{H'}` the Gram-triangle cocycle of the seed).
* `cOmegaCoeff_one_eq_cocycle`: the model's `cOmega` at the identity plane is `K · (c_H + c_{H'}^ε)`.
* `bridge_reflCocycle`: the class of `c_{H'}^ε` in Mathlib's group cohomology is the `ε`-conjugation transport (`epsHom`, `epsRep`) of `complexifyG (seedClass H')`
  (uses that Gram matrices are invariant under right multiplication by the orthogonal `ε`, `gramOf_mul_eps`).
* `g5_levelOne`: the two statements together.
-/

open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeedBridge

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3.Psi
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.FormCochainBridge
  TernaryPeriodPolynomials.Argument.FormSeriesModel
  TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
  TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- `ρ(g)` on `HomogeneousPoly n` is the library's polynomial action `rho` of the matrix `g`. -/
theorem toPoly_realCoefficient (n : ℕ) (g : RealGL3) (q : HomogeneousPoly n) :
    ((realCoefficient n g q : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      rho g.val (q : MvPolynomial (Fin 3) ℂ) := by
  change ((GeneralEisenstein.action (-1)
    (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g)) (q : MvPolynomial (Fin 3) ℂ)) = _
  rw [GeneralEisenstein.action_apply]
  unfold rho GeneralEisenstein.substitute GeneralEisenstein.linearForm
  simp [GeneralEisenstein.determinantCharacter, Matrix.GeneralLinearGroup.map]
  have hd : ((g.val).map Complex.ofReal).det = ((g.val.det : ℝ) : ℂ) :=
    (RingHom.map_det Complex.ofRealHom g.val).symm
  rw [hd, MvPolynomial.smul_eq_C_mul]

theorem coeff_realCoefficient_inv (n : ℕ) (g : RealGL3) (Z : HomogeneousPoly n) (κ : Fin 3 →₀ ℕ) :
    ((realCoefficient n g⁻¹ Z : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ).coeff κ =
      (rho (g.val)⁻¹ (Z : MvPolynomial (Fin 3) ℂ)).coeff κ := by
  rw [toPoly_realCoefficient, Matrix.coe_units_inv]

section Eps

theorem epsJ_val : (epsJ.val : Matrix (Fin 3) (Fin 3) ℝ) = Matrix.diagonal ![-1, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [epsJ, GeneralEisenstein.Adelic.planeLevi, GeneralEisenstein.Adelic.planeBlock, UpperHalfPlane.J]

theorem epsJ_mul_self : epsJ * epsJ = 1 := by
  apply Units.ext
  rw [Units.val_mul, epsJ_val, Matrix.diagonal_mul_diagonal, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem epsJ_inv : epsJ⁻¹ = epsJ := inv_eq_of_mul_eq_one_right epsJ_mul_self

/-- Conjugation of `SL₃(ℤ)` by the reflection `diag(-1, 1, 1)`. -/
def epsConj (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix.SpecialLinearGroup (Fin 3) ℤ :=
  ⟨Matrix.diagonal ![-1, 1, 1] * (γ : Matrix (Fin 3) (Fin 3) ℤ) * Matrix.diagonal ![-1, 1, 1], by
    rw [Matrix.det_mul, Matrix.det_mul, γ.2]
    simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩

theorem epsConj_apply (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (i j : Fin 3) :
    (epsConj γ : Matrix (Fin 3) (Fin 3) ℤ) i j = (![-1, 1, 1] : Fin 3 → ℤ) i * γ i j * (![-1, 1, 1] : Fin 3 → ℤ) j := by
  change ((Matrix.diagonal ![-1, 1, 1] * (γ : Matrix (Fin 3) (Fin 3) ℤ) * Matrix.diagonal ![-1, 1, 1] :
    Matrix (Fin 3) (Fin 3) ℤ)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem epsConj_mem_gammaNP (N : ℕ) {γ : Matrix.SpecialLinearGroup (Fin 3) ℤ} (hγ : γ ∈ gammaNP N) :
    epsConj γ ∈ gammaNP N := by
  rw [gammaNP, Subgroup.mem_inf] at hγ ⊢
  obtain ⟨hN, h0, h1, h2⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_gammaN] at hN ⊢
    intro i j
    have := hN i j
    rw [epsConj_apply]
    fin_cases i <;> fin_cases j <;> simp at this ⊢ <;> exact this
  · rw [epsConj_apply]; simp [h0]
  · rw [epsConj_apply]; simp [h1]
  · rw [epsConj_apply]; simp [h2]

theorem mapGL_epsConj (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
    Matrix.SpecialLinearGroup.mapGL ℝ (epsConj γ) =
      epsJ⁻¹ * Matrix.SpecialLinearGroup.mapGL ℝ γ * epsJ := by
  rw [epsJ_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, mapGL_val, mapGL_val, epsJ_val]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [realMat, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
  rw [epsConj_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem epsConj_one : epsConj (1 : Matrix.SpecialLinearGroup (Fin 3) ℤ) = 1 := by
  apply Subtype.ext
  change Matrix.diagonal ![-1, 1, 1] * (1 : Matrix (Fin 3) (Fin 3) ℤ) * Matrix.diagonal ![-1, 1, 1] = 1
  rw [Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem epsConj_mul (γ δ : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
    epsConj (γ * δ) = epsConj γ * epsConj δ := by
  apply Subtype.ext
  have hE : Matrix.diagonal (![-1, 1, 1] : Fin 3 → ℤ) * Matrix.diagonal ![-1, 1, 1] = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  change Matrix.diagonal ![-1, 1, 1] * ((γ : Matrix (Fin 3) (Fin 3) ℤ) * (δ : Matrix (Fin 3) (Fin 3) ℤ)) *
      Matrix.diagonal ![-1, 1, 1] = (Matrix.diagonal ![-1, 1, 1] * (γ : Matrix (Fin 3) (Fin 3) ℤ) *
        Matrix.diagonal ![-1, 1, 1]) * (Matrix.diagonal ![-1, 1, 1] * (δ : Matrix (Fin 3) (Fin 3) ℤ) *
        Matrix.diagonal ![-1, 1, 1])
  calc _ = Matrix.diagonal ![-1, 1, 1] * (γ : Matrix (Fin 3) (Fin 3) ℤ) * 1 * (δ : Matrix (Fin 3) (Fin 3) ℤ) *
        Matrix.diagonal ![-1, 1, 1] := by simp [Matrix.mul_assoc]
    _ = _ := by rw [← hE]; simp only [Matrix.mul_assoc]

/-- Conjugation by the reflection `ε` on `Γ_P = Γ(N) ∩ P(ℤ)`. -/
def epsHom (N : ℕ) : ↥(gammaNP N) →* ↥(gammaNP N) where
  toFun γ := ⟨epsConj γ.1, epsConj_mem_gammaNP N γ.2⟩
  map_one' := Subtype.ext epsConj_one
  map_mul' γ δ := Subtype.ext (epsConj_mul γ.1 δ.1)

theorem eps_norm (N : ℕ) : ∀ m ∈ realLevel (gammaNP N), (epsJ⁻¹)⁻¹ * m * epsJ⁻¹ ∈ realLevel (gammaNP N) := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [inv_inv, epsJ_inv]
  refine ⟨epsConj γ, epsConj_mem_gammaNP N hγ, ?_⟩
  rw [mapGL_epsConj, epsJ_inv]


end Eps

section Seed

variable (N : ℕ) (n : ℕ) (h : ℂ → ℂ) (Gm : ℕ → ℂ → ℂ)
  (hh : DifferentiableOn ℂ h Psi.upperSet)
  (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
  (hmod : ∀ g : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
    h (mob ((gammaNPlaneData N).lam g) z) = dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) * h z)

/-- **The twisted Gram-triangle cochain at translated vertices**: for any `g ∈ GL₃(ℝ)`,
`coeff_κ (ρ(g⁻¹) F_h(g y)) = planeIntG n h g Δ(y) κ`. -/
theorem coeff_rho_gramCochainW_seed (g : RealGL3) (y : Fin 3 → RealGL3) (κ : Fin 3 →₀ ℕ) :
    ((realCoefficient n g⁻¹ (gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n)
        (seedCone N n h Gm hh hG hmod) (fun i => g * y i)) : HomogeneousPoly n) :
        MvPolynomial (Fin 3) ℂ).coeff κ =
      planeIntG n h g.val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ := by
  classical
  rw [planeIntG_eq_seedTri_gl]
  let Lℂ : Coef n →ₗ[ℂ] ℂ := ((MvPolynomial.lcoeff ℂ κ).comp (Submodule.subtype _)).comp
    (realCoefficient n g⁻¹ : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n)
  let L : Coef n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Lℂ.restrictScalars ℝ)
  have hL : ∀ z : Coef n, L z = ((realCoefficient n g⁻¹ z : HomogeneousPoly n) :
      MvPolynomial (Fin 3) ℂ).coeff κ := fun z => rfl
  set p0 := gramOf (g * y 0) with hp0
  set p1 := gramOf (g * y 1) with hp1
  set p2 := gramOf (g * y 2) with hp2
  have hc0 : p0 ∈ gramCone := gramOf_mem_gramCone _
  have hc1 : p1 ∈ gramCone := gramOf_mem_gramCone _
  have hc2 : p2 ∈ gramCone := gramOf_mem_gramCone _
  have hpt : ∀ q ∈ stdTriangle, affTri p0 p1 p2 q ∈ gramCone := fun q hq =>
    affTri_mem convex_gramCone hc0 hc1 hc2 hq
  have hint : IntegrableOn (fun q => (((seedCone N n h Gm hh hG hmod : Form (F := Coef n) gramCone 2) :
      RawForm Mat3 (Coef n) 2) (affTri p0 p1 p2 q)) ![p1 - p0, p2 - p0]) stdTriangle :=
    integrable_triInt convex_gramCone
      ((seedCone N n h Gm hh hG hmod : Form (F := Coef n) gramCone 2)) hc0 hc1 hc2
  rw [← hL]
  change L (∫ q in stdTriangle, (((seedCone N n h Gm hh hG hmod : Form (F := Coef n) gramCone 2) :
      RawForm Mat3 (Coef n) 2) (affTri p0 p1 p2 q)) ![p1 - p0, p2 - p0]) = _
  rw [← ContinuousLinearMap.integral_comp_comm L hint]
  refine setIntegral_congr_fun measurableSet_stdTriangle fun q hq => ?_
  have e1 : ∀ Z : Coef n, (((realCoefficient n g⁻¹ Z : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ)).coeff κ =
      (rho (g.val)⁻¹ (Coef.toPoly Z)).coeff κ := by
    intro Z
    exact coeff_realCoefficient_inv n g Z κ
  have e2 := seedCone_pair N n h Gm hh hG hmod (hpt q hq) (p1 - p0) (p2 - p0)
  exact (hL _).trans ((e1 _).trans (congrArg (fun P => (rho (g.val)⁻¹ P).coeff κ) e2))

open TernaryPeriodPolynomials.Argument.LevelTransfer in
/-- **The reflected half as a homogeneous cocycle**: the `ε`-conjugation transport `(ε⁻¹ • F)(y) = ρ(ε⁻¹) F(ε y)` of the seed cocycle of
`h`, a cocycle of `realLevel Γ_P` because `ε` normalizes `Γ_P`. -/
def reflCocycle : cocycles (realLevel (gammaNP N)) (GeneralEisenstein.realCoefficient n) :=
  actCocycle (GeneralEisenstein.realCoefficient n) epsJ⁻¹ (eps_norm N)
    (gramCocycleW (seedCone N n h Gm hh hG hmod) (rhoR_gammaNP N n))

/-- **R1c, coefficients**: the coefficient `κ` of the reflected cocycle is the library's `planeIntG n h ε Δ(y) κ`. -/
theorem coeff_reflCocycle (y : Fin 3 → RealGL3) (κ : Fin 3 →₀ ℕ) :
    ((((reflCocycle N n h Gm hh hG hmod).val.val y : HomogeneousPoly n)) : MvPolynomial (Fin 3) ℂ).coeff κ =
      planeIntG n h epsJ.val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ := by
  have h1 := coeff_rho_gramCochainW_seed N n h Gm hh hG hmod epsJ y κ
  have e : (reflCocycle N n h Gm hh hG hmod).val.val y =
      GeneralEisenstein.realCoefficient n epsJ⁻¹
        (gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n) (seedCone N n h Gm hh hG hmod)
          (fun i => epsJ * y i)) := by
    have := LevelTransfer.actFun_apply (GeneralEisenstein.realCoefficient n) epsJ⁻¹
      (fun x => (gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n) (seedCone N n h Gm hh hG hmod) x :
        HomogeneousPoly n)) y
    rw [inv_inv] at this
    exact this
  rw [e]
  exact h1

open TernaryPeriodPolynomials.Argument GeneralEisenstein.Adelic
  TernaryPeriodPolynomials.SourceConstruction in
/-- **R1c, cochain level.**  The plane integral cochain `cOmega n D F y 1` of the model at the identity plane is `K` times the value of the
homogeneous cocycle `c_H + (ε-transport of c_{H'})` of `realLevel Γ_P` (`H = F(1·b_F(1))`, `H' = F(J·b_F(1))`,
`K = (-1)ⁿ(n+1)c_F(1)/2`). -/
theorem cOmegaCoeff_one_eq_cocycle (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
    (Gm Gm' : ℕ → ℂ → ℂ)
    (hh : DifferentiableOn ℂ (F (1 * bF (1 : AdelicGL))) Psi.upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (F (1 * bF (1 : AdelicGL)) z * z ^ j) z)
    (hmod : ∀ g : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
      F (1 * bF (1 : AdelicGL)) (mob ((gammaNPlaneData N).lam g) z) =
        dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) * F (1 * bF (1 : AdelicGL)) z)
    (hh' : DifferentiableOn ℂ (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Psi.upperSet)
    (hG' : ∀ j z, 0 < z.im → HasDerivAt (Gm' j) (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL)) z * z ^ j) z)
    (hmod' : ∀ g : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
      F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL)) (mob ((gammaNPlaneData N).lam g) z) =
        dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) * F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL)) z)
    (y : Fin 3 → RealGL3) (κ : Fin 3 →₀ ℕ) :
    cOmegaCoeff n D F y 1 κ =
      (((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * cF D 1) *
        ((((gramCocycleW (seedCone N n (F (1 * bF (1 : AdelicGL))) Gm hh hG hmod) (rhoR_gammaNP N n) +
            reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Gm' hh' hG' hmod').val.val y :
            HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ).coeff κ) := by
  rw [cOmegaCoeff_one_eq N n Gm D F hh hG hmod y κ]
  congr 1
  have e : (realGroup (1 : AdelicGL)).val = 1 := by rw [map_one, Units.val_one]
  have h2 := coeff_reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Gm' hh' hG' hmod' y κ
  rw [e, mul_one]
  change _ + _ = (Coef.toPoly (gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n)
      (seedCone N n (F (1 * bF (1 : AdelicGL))) Gm hh hG hmod) y) +
    (((reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Gm' hh' hG' hmod').val.val y :
      HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ)).coeff κ
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h2]

theorem reflCocycle_apply' (y : Fin 3 → RealGL3) :
    (reflCocycle N n h Gm hh hG hmod).val.val y =
      GeneralEisenstein.realCoefficient n epsJ⁻¹
        (gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n) (seedCone N n h Gm hh hG hmod)
          (fun i => epsJ * y i)) := by
  have := LevelTransfer.actFun_apply (GeneralEisenstein.realCoefficient n) epsJ⁻¹
    (fun x => (gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n) (seedCone N n h Gm hh hG hmod) x :
      HomogeneousPoly n)) y
  rw [inv_inv] at this
  exact this

theorem reflCocycle_apply (y : Fin 3 → RealGL3) :
    (reflCocycle N n h Gm hh hG hmod).val.val y =
      GeneralEisenstein.realCoefficient n epsJ
        (gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n) (seedCone N n h Gm hh hG hmod)
          (fun i => epsJ * y i)) := by
  rw [reflCocycle_apply', epsJ_inv]

section ClassLevel

open TernaryPeriodPolynomials.Argument.LevelTransfer

omit hh hG hmod in

theorem rho_gammaNRep (g : ↥(gammaNP N)) (v : HomogeneousPoly n) :
    (gammaNRep N n).ρ g v = GeneralEisenstein.realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ g.1) v := by
  change GeneralEisenstein.realCoefficient n ((gammaNPlaneData N).sigma g) v = _
  rw [sigma_gammaNP]

omit hh hG hmod in
theorem eps_intertwine (g : ↥(gammaNP N)) (v : HomogeneousPoly n) :
    GeneralEisenstein.realCoefficient n epsJ
        (GeneralEisenstein.realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ (epsHom N g).1) v) =
      GeneralEisenstein.realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ g.1)
        (GeneralEisenstein.realCoefficient n epsJ v) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  change epsJ * Matrix.SpecialLinearGroup.mapGL ℝ (epsConj g.1) = _
  rw [mapGL_epsConj, epsJ_inv, ← mul_assoc, ← mul_assoc, epsJ_mul_self, one_mul]

/-- The `ε`-conjugation of `Γ_P` with coefficient map `ρ(ε)`, as a morphism of representations. -/
def epsRep : Rep.res (epsHom N) (gammaNRep N n) ⟶ gammaNRep N n :=
  Rep.ofHom ⟨(GeneralEisenstein.realCoefficient n epsJ : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n),
    fun g => LinearMap.ext fun v =>
      (congrArg (GeneralEisenstein.realCoefficient n epsJ) (rho_gammaNRep N n (epsHom N g) v)).trans
        ((eps_intertwine N n g v).trans (rho_gammaNRep N n g _).symm)⟩

end ClassLevel

section ClassLevel2

open TernaryPeriodPolynomials.Argument.LevelTransfer

theorem gramOf_mul_eps (y : RealGL3) : gramOf (y * epsJ) = gramOf y := by
  have h1 : epsJ.val * epsJ.val = 1 := by
    have := congrArg Units.val epsJ_mul_self
    rwa [Units.val_mul, Units.val_one] at this
  have h2 : (epsJ.val).transpose = epsJ.val := by
    rw [epsJ_val]; exact Matrix.diagonal_transpose _
  unfold gramOf
  rw [Units.val_mul, Matrix.transpose_mul, h2, Matrix.mul_assoc, ← Matrix.mul_assoc epsJ.val, h1,
    Matrix.one_mul]

theorem gramCochainW_eps_right (y : Fin 3 → RealGL3) (N n : ℕ) (ρ : Representation ℝ (gammaNP N) (Coef n))
    (W : ZigZag.invClosed isOpen_gramCone (coneAction (gammaNP N)) ρ) :
    gramCochainW (gammaNP N) n ρ W (fun i => y i * epsJ) = gramCochainW (gammaNP N) n ρ W y := by
  unfold gramCochainW
  simp only [gramOf_mul_eps]

variable [NeZero N]

theorem bridge_reflCocycle :
    (groupCohomology.map (realLevelHom (gammaNP N)) (repMorRealG N n) 2).hom
        (bridge (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N))
          (Submodule.Quotient.mk (reflCocycle N n h Gm hh hG hmod))) =
      (groupCohomology.map (epsHom N) (epsRep N n) 2).hom
        (complexifyG N n ((gammaNPlaneData N).seedClass h n Gm hh hG hmod)) := by
  rw [← bridge_gramCocycleW_seed N n h Gm hh hG hmod, bridge_mk, bridge_mk,
    groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply,
    groupCohomology.H2π_comp_map_apply]
  have hc : (groupCohomology.mapCocycles₂ (realLevelHom (gammaNP N)) (repMorRealG N n)).hom
      (bridgeCocycle (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N))
        (reflCocycle N n h Gm hh hG hmod)) =
      (groupCohomology.mapCocycles₂ (epsHom N) (epsRep N n)).hom
        ((groupCohomology.mapCocycles₂ (realLevelHom (gammaNP N)) (repMorRealG N n)).hom
          (bridgeCocycle (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N))
            (gramCocycleW (seedCone N n h Gm hh hG hmod) (rhoR_gammaNP N n)))) := by
    apply Subtype.ext
    funext p
    obtain ⟨a, b⟩ := p
    have hv : (fun i : Fin 3 => epsJ * (![1, Matrix.SpecialLinearGroup.mapGL ℝ a.1,
        Matrix.SpecialLinearGroup.mapGL ℝ a.1 * Matrix.SpecialLinearGroup.mapGL ℝ b.1] : Fin 3 → RealGL3) i * epsJ) =
        ![1, Matrix.SpecialLinearGroup.mapGL ℝ (epsHom N a).1,
          Matrix.SpecialLinearGroup.mapGL ℝ (epsHom N a).1 * Matrix.SpecialLinearGroup.mapGL ℝ (epsHom N b).1] := by
      funext i
      fin_cases i
      · simp [epsJ_mul_self]
      · change epsJ * Matrix.SpecialLinearGroup.mapGL ℝ a.1 * epsJ = Matrix.SpecialLinearGroup.mapGL ℝ (epsConj a.1)
        rw [mapGL_epsConj, epsJ_inv]
      · change epsJ * (Matrix.SpecialLinearGroup.mapGL ℝ a.1 * Matrix.SpecialLinearGroup.mapGL ℝ b.1) * epsJ =
          Matrix.SpecialLinearGroup.mapGL ℝ (epsConj a.1) * Matrix.SpecialLinearGroup.mapGL ℝ (epsConj b.1)
        rw [mapGL_epsConj, mapGL_epsConj, epsJ_inv]
        calc _ = epsJ * Matrix.SpecialLinearGroup.mapGL ℝ a.1 * 1 * Matrix.SpecialLinearGroup.mapGL ℝ b.1 * epsJ := by
              simp [mul_assoc]
          _ = _ := by rw [← epsJ_mul_self]; simp only [mul_assoc]
    have e1 := reflCocycle_apply N n h Gm hh hG hmod
      (![1, Matrix.SpecialLinearGroup.mapGL ℝ a.1,
        Matrix.SpecialLinearGroup.mapGL ℝ a.1 * Matrix.SpecialLinearGroup.mapGL ℝ b.1] : Fin 3 → RealGL3)
    have e2 := gramCochainW_eps_right
      (fun i => epsJ * (![1, Matrix.SpecialLinearGroup.mapGL ℝ a.1,
        Matrix.SpecialLinearGroup.mapGL ℝ a.1 * Matrix.SpecialLinearGroup.mapGL ℝ b.1] : Fin 3 → RealGL3) i)
      N n ((gammaNPlaneData N).rhoR n) (seedCone N n h Gm hh hG hmod)
    have L : ((groupCohomology.mapCocycles₂ (realLevelHom (gammaNP N)) (repMorRealG N n)).hom
        (bridgeCocycle (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N))
          (reflCocycle N n h Gm hh hG hmod)) : ↥(gammaNP N) × ↥(gammaNP N) → HomogeneousPoly n) (a, b) =
        (reflCocycle N n h Gm hh hG hmod).val.val
          ![1, Matrix.SpecialLinearGroup.mapGL ℝ a.1,
            Matrix.SpecialLinearGroup.mapGL ℝ a.1 * Matrix.SpecialLinearGroup.mapGL ℝ b.1] :=
      bridgeCocycle_apply (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N))
        (reflCocycle N n h Gm hh hG hmod) (realLevelHom (gammaNP N) a) (realLevelHom (gammaNP N) b)
    have R : ((groupCohomology.mapCocycles₂ (epsHom N) (epsRep N n)).hom
        ((groupCohomology.mapCocycles₂ (realLevelHom (gammaNP N)) (repMorRealG N n)).hom
          (bridgeCocycle (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N))
            (gramCocycleW (seedCone N n h Gm hh hG hmod) (rhoR_gammaNP N n)))) :
          ↥(gammaNP N) × ↥(gammaNP N) → HomogeneousPoly n) (a, b) =
        GeneralEisenstein.realCoefficient n epsJ
          (gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n) (seedCone N n h Gm hh hG hmod)
            ![1, Matrix.SpecialLinearGroup.mapGL ℝ (epsHom N a).1,
              Matrix.SpecialLinearGroup.mapGL ℝ (epsHom N a).1 *
                Matrix.SpecialLinearGroup.mapGL ℝ (epsHom N b).1]) :=
      congrArg (GeneralEisenstein.realCoefficient n epsJ)
        (bridgeCocycle_apply (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N))
          (gramCocycleW (seedCone N n h Gm hh hG hmod) (rhoR_gammaNP N n))
          (realLevelHom (gammaNP N) (epsHom N a)) (realLevelHom (gammaNP N) (epsHom N b)))
    exact L.trans (e1.trans (congrArg (GeneralEisenstein.realCoefficient n epsJ)
      (e2.symm.trans (congrArg (gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n)
        (seedCone N n h Gm hh hG hmod)) hv)))) |>.trans R.symm
  rw [hc]

end ClassLevel2

open TernaryPeriodPolynomials.Argument GeneralEisenstein.Adelic
  TernaryPeriodPolynomials.SourceConstruction
  TernaryPeriodPolynomials.Argument.LevelTransfer in
/-- **G5 at level one, complete up to the hypotheses on the scalar functions (holomorphic and reflected halves).**
For `H = F(1·b_F(1))`, `H' = F(J·b_F(1))` satisfying the seed hypotheses for `Γ_P = Γ(N) ∩ P(ℤ)`:
(1) the model's plane integral cochain at the identity plane is `K · (c_H + ε-transport of c_{H'})` on every `GL₃(ℝ)`-vertex triple
(`K = (-1)ⁿ(n+1)c_F(1)/2`), and (2) the class of that homogeneous cocycle, in Mathlib's `H²(Γ_P, E_n)_ℂ`, is
`[seed H] + ε_*[seed H']` where `ε_*` is conjugation by the reflection `ε = diag(-1,1,1)` with coefficient map `ρ(ε)`. -/
theorem g5_levelOne [NeZero N] (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
    (Gm Gm' : ℕ → ℂ → ℂ)
    (hh : DifferentiableOn ℂ (F (1 * bF (1 : AdelicGL))) Psi.upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (F (1 * bF (1 : AdelicGL)) z * z ^ j) z)
    (hmod : ∀ g : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
      F (1 * bF (1 : AdelicGL)) (mob ((gammaNPlaneData N).lam g) z) =
        dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) * F (1 * bF (1 : AdelicGL)) z)
    (hh' : DifferentiableOn ℂ (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Psi.upperSet)
    (hG' : ∀ j z, 0 < z.im → HasDerivAt (Gm' j) (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL)) z * z ^ j) z)
    (hmod' : ∀ g : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
      F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL)) (mob ((gammaNPlaneData N).lam g) z) =
        dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) * F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL)) z) :
    (∀ (y : Fin 3 → RealGL3) (κ : Fin 3 →₀ ℕ), cOmegaCoeff n D F y 1 κ =
      (((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * cF D 1) *
        ((((gramCocycleW (seedCone N n (F (1 * bF (1 : AdelicGL))) Gm hh hG hmod) (rhoR_gammaNP N n) +
            reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Gm' hh' hG' hmod').val.val y :
            HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ).coeff κ)) ∧
    (groupCohomology.map (realLevelHom (gammaNP N)) (repMorRealG N n) 2).hom
        (bridge (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N))
          (Submodule.Quotient.mk (gramCocycleW (seedCone N n (F (1 * bF (1 : AdelicGL))) Gm hh hG hmod) (rhoR_gammaNP N n) +
            reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Gm' hh' hG' hmod'))) =
      complexifyG N n ((gammaNPlaneData N).seedClass (F (1 * bF (1 : AdelicGL))) n Gm hh hG hmod) +
        (groupCohomology.map (epsHom N) (epsRep N n) 2).hom
          (complexifyG N n ((gammaNPlaneData N).seedClass (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) n Gm' hh' hG' hmod')) := by
  refine ⟨fun y κ => cOmegaCoeff_one_eq_cocycle N n D F Gm Gm' hh hG hmod hh' hG' hmod' y κ, ?_⟩
  rw [Submodule.Quotient.mk_add, map_add, map_add, bridge_gramCocycleW_seed, bridge_reflCocycle]

end Seed

end TernaryPeriodPolynomials.Argument.FormSeedBridge
