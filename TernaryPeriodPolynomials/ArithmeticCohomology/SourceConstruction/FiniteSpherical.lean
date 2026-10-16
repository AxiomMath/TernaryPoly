module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.ParabolicCompact
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Norm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Norm
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL

@[expose] public section


/-!
# The spherical finite part of a line-induced section

The finite line Iwasawa decomposition `GL₃(𝔸_f) = P_line(𝔸_f) · GL₃(Ẑ)` is obtained from the plane
one by the automorphism `g ↦ J (g⁻¹)ᵀ J` (`J` the antidiagonal permutation), which exchanges the two
parabolics and preserves `GL₃(Ẑ)`. For a character trivial on `Ẑ^×` and a `GL₂(Ẑ)`-fixed vector `v`,
`g = p k ↦ χ_f(corner p) |corner p|^a |det block p|^b · π(block p) v` is well defined, left
`P_line(𝔸_f)`-equivariant and right `GL₃(Ẑ)`-invariant (`finiteLineVector`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance
  (combineGL_mul atInfinity_mul atFinite_mul)

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## The exchange automorphism -/

section Exchange

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The antidiagonal permutation matrix. -/
def antiDiagonal : GeneralLinearGroup (Fin 3) R where
  val := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  inv := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem antiDiagonal_mul_self :
    (antiDiagonal : GeneralLinearGroup (Fin 3) R) * antiDiagonal = 1 := by
  apply Units.ext
  change (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) R) *
    !![0, 0, 1; 0, 1, 0; 1, 0, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- Inverse transpose. -/
def invTranspose (g : GeneralLinearGroup (Fin 3) R) : GeneralLinearGroup (Fin 3) R where
  val := g.invᵀ
  inv := g.valᵀ
  val_inv := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one]

theorem invTranspose_mul (g h : GeneralLinearGroup (Fin 3) R) :
    invTranspose (g * h) = invTranspose g * invTranspose h := by
  apply Units.ext
  change (h.inv * g.inv)ᵀ = g.invᵀ * h.invᵀ
  rw [Matrix.transpose_mul]

theorem invTranspose_invTranspose (g : GeneralLinearGroup (Fin 3) R) :
    invTranspose (invTranspose g) = g := by
  apply Units.ext
  change (g.valᵀ)ᵀ = g.val
  exact Matrix.transpose_transpose _

theorem invTranspose_antiDiagonal :
    invTranspose (antiDiagonal : GeneralLinearGroup (Fin 3) R) = antiDiagonal := by
  apply Units.ext
  change (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) R)ᵀ = !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem map_invTranspose (f : R →+* S) (g : GeneralLinearGroup (Fin 3) R) :
    GeneralLinearGroup.map f (invTranspose g) = invTranspose (GeneralLinearGroup.map f g) := by
  apply Units.ext
  ext i j
  rfl

theorem map_antiDiagonal (f : R →+* S) :
    GeneralLinearGroup.map f (antiDiagonal : GeneralLinearGroup (Fin 3) R) = antiDiagonal := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.val_map_apply]
  fin_cases i <;> fin_cases j <;> simp [antiDiagonal]

/-- The exchange automorphism `g ↦ J (g⁻¹)ᵀ J`. -/
def lineDual (g : GeneralLinearGroup (Fin 3) R) : GeneralLinearGroup (Fin 3) R :=
  antiDiagonal * invTranspose g * antiDiagonal

theorem lineDual_mul (g h : GeneralLinearGroup (Fin 3) R) :
    lineDual (g * h) = lineDual g * lineDual h := by
  unfold lineDual
  rw [invTranspose_mul]
  have hA : (antiDiagonal : GeneralLinearGroup (Fin 3) R) * antiDiagonal = 1 :=
    antiDiagonal_mul_self
  calc antiDiagonal * (invTranspose g * invTranspose h) * antiDiagonal
      = antiDiagonal * invTranspose g * (antiDiagonal * antiDiagonal) * invTranspose h *
          antiDiagonal := by rw [hA]; group
    _ = antiDiagonal * invTranspose g * antiDiagonal *
          (antiDiagonal * invTranspose h * antiDiagonal) := by group

theorem lineDual_lineDual (g : GeneralLinearGroup (Fin 3) R) : lineDual (lineDual g) = g := by
  unfold lineDual
  rw [invTranspose_mul, invTranspose_mul, invTranspose_invTranspose, invTranspose_antiDiagonal]
  have hA : (antiDiagonal : GeneralLinearGroup (Fin 3) R) * antiDiagonal = 1 :=
    antiDiagonal_mul_self
  calc antiDiagonal * (antiDiagonal * g * antiDiagonal) * antiDiagonal
      = (antiDiagonal * antiDiagonal) * g * (antiDiagonal * antiDiagonal) := by group
    _ = g := by rw [hA, one_mul, mul_one]

theorem map_lineDual (f : R →+* S) (g : GeneralLinearGroup (Fin 3) R) :
    GeneralLinearGroup.map f (lineDual g) = lineDual (GeneralLinearGroup.map f g) := by
  unfold lineDual
  rw [map_mul, map_mul, map_invTranspose, map_antiDiagonal]

/-- The exchange automorphism maps the plane parabolic into the line parabolic. -/
theorem lineDual_mem_lineParabolic {p : GeneralLinearGroup (Fin 3) R}
    (hp : p ∈ planeParabolic R) : lineDual p ∈ lineParabolic R := by
  have hinv := (planeParabolic R).inv_mem hp
  have h20 : (p.val)⁻¹ 2 0 = 0 := by rw [← Matrix.coe_units_inv]; exact hinv.1
  have h21 : (p.val)⁻¹ 2 1 = 0 := by rw [← Matrix.coe_units_inv]; exact hinv.2
  have hval : (lineDual p).val =
      (antiDiagonal : GeneralLinearGroup (Fin 3) R).val * p.invᵀ *
        (antiDiagonal : GeneralLinearGroup (Fin 3) R).val := rfl
  have hA : (antiDiagonal : GeneralLinearGroup (Fin 3) R).val = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  constructor
  · rw [hval, hA]
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, Matrix.transpose_apply, h21]
  · rw [hval, hA]
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, Matrix.transpose_apply, h20]

end Exchange

/-- **Finite line Iwasawa decomposition.** -/
theorem finiteLine_factorization (g : FiniteGL) :
    ∃ p : FiniteGL, p ∈ lineParabolic FiniteAdeles ∧
      ∃ k : GeneralLinearGroup (Fin 3) IntegralAdeles,
        g = p * GeneralLinearGroup.map integralEmbedding k := by
  obtain ⟨p, k, h⟩ :=
    TernaryPeriodPolynomials.SphericalDetection.Helpers.finiteGL_parabolic_compact_factorization
      (lineDual g)
  refine ⟨lineDual p.val, lineDual_mem_lineParabolic p.property, lineDual k, ?_⟩
  calc g = lineDual (lineDual g) := (lineDual_lineDual g).symm
    _ = lineDual (p.val * GeneralLinearGroup.map integralEmbedding k) := by rw [← h]
    _ = lineDual p.val * GeneralLinearGroup.map integralEmbedding (lineDual k) := by
      rw [lineDual_mul, map_lineDual]

/-! ## Levi projections of the line parabolic over a commutative ring -/

section Levi

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The rank-one corner of a line-parabolic element. -/
def lineCornerUnit (p : GeneralLinearGroup (Fin 3) R) (hp : p ∈ lineParabolic R) : Rˣ where
  val := p.val 0 0
  inv := p.inv 0 0
  val_inv := by
    have hinv := (lineParabolic R).inv_mem hp
    have h10 : p.inv 1 0 = 0 := hinv.1
    have h20 : p.inv 2 0 = 0 := hinv.2
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 0) p.val_inv
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, mul_zero, add_zero] at h
    simpa using h
  inv_val := by
    have h10 : p.val 1 0 = 0 := hp.1
    have h20 : p.val 2 0 = 0 := hp.2
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 0) p.inv_val
    simpa [Matrix.mul_apply, Fin.sum_univ_three, h10, h20] using h

/-- The `GL₂` block of a line-parabolic element. -/
def lineBlockGL (p : GeneralLinearGroup (Fin 3) R) (hp : p ∈ lineParabolic R) :
    GeneralLinearGroup (Fin 2) R where
  val := !![p.val 1 1, p.val 1 2; p.val 2 1, p.val 2 2]
  inv := !![p.inv 1 1, p.inv 1 2; p.inv 2 1, p.inv 2 2]
  val_inv := by
    have h10 : p.val 1 0 = 0 := hp.1
    have h20 : p.val 2 0 = 0 := hp.2
    have e := p.val_inv
    ext i j
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M i.succ j.succ) e
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, h10, h20,
        Matrix.one_apply] using h
  inv_val := by
    have hinv := (lineParabolic R).inv_mem hp
    have h10 : p.inv 1 0 = 0 := hinv.1
    have h20 : p.inv 2 0 = 0 := hinv.2
    have e := p.inv_val
    have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 1 1) e
    have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 1 2) e
    have h21 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 2 1) e
    have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 2 2) e
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, zero_mul, zero_add] at h11 h12 h21 h22
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h11
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h12
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h21
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h22

theorem lineCornerUnit_mul {p q : GeneralLinearGroup (Fin 3) R} (hp : p ∈ lineParabolic R)
    (hq : q ∈ lineParabolic R) :
    lineCornerUnit (p * q) ((lineParabolic R).mul_mem hp hq) =
      lineCornerUnit p hp * lineCornerUnit q hq := by
  have h10 : q.val 1 0 = 0 := hq.1
  have h20 : q.val 2 0 = 0 := hq.2
  apply Units.ext
  change (p.val * q.val) 0 0 = p.val 0 0 * q.val 0 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20]

theorem lineBlockGL_mul {p q : GeneralLinearGroup (Fin 3) R} (hp : p ∈ lineParabolic R)
    (hq : q ∈ lineParabolic R) :
    lineBlockGL (p * q) ((lineParabolic R).mul_mem hp hq) =
      lineBlockGL p hp * lineBlockGL q hq := by
  have h10 : p.val 1 0 = 0 := hp.1
  have h20 : p.val 2 0 = 0 := hp.2
  apply Units.ext
  change !![(p.val * q.val) 1 1, (p.val * q.val) 1 2; (p.val * q.val) 2 1, (p.val * q.val) 2 2] =
    !![p.val 1 1, p.val 1 2; p.val 2 1, p.val 2 2] * !![q.val 1 1, q.val 1 2; q.val 2 1, q.val 2 2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, h10, h20]

theorem lineCornerUnit_congr {p q : GeneralLinearGroup (Fin 3) R} (h : p = q)
    (hp : p ∈ lineParabolic R) (hq : q ∈ lineParabolic R) :
    lineCornerUnit p hp = lineCornerUnit q hq := by
  subst h
  rfl

theorem lineBlockGL_congr {p q : GeneralLinearGroup (Fin 3) R} (h : p = q)
    (hp : p ∈ lineParabolic R) (hq : q ∈ lineParabolic R) :
    lineBlockGL p hp = lineBlockGL q hq := by
  subst h
  rfl

theorem lineCornerUnit_map (f : R →+* S) (p : GeneralLinearGroup (Fin 3) R)
    (hp : p ∈ lineParabolic R) (hfp : GeneralLinearGroup.map f p ∈ lineParabolic S) :
    lineCornerUnit (GeneralLinearGroup.map f p) hfp = Units.map f.toMonoidHom (lineCornerUnit p hp) :=
  Units.ext rfl

theorem lineBlockGL_map (f : R →+* S) (p : GeneralLinearGroup (Fin 3) R)
    (hp : p ∈ lineParabolic R) (hfp : GeneralLinearGroup.map f p ∈ lineParabolic S) :
    lineBlockGL (GeneralLinearGroup.map f p) hfp = GeneralLinearGroup.map f (lineBlockGL p hp) := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.val_map_apply]
  fin_cases i <;> fin_cases j <;> rfl

end Levi

/-- An integral matrix whose finite image lies in the line parabolic lies in the integral line
parabolic. -/
theorem integral_mem_lineParabolic {k : GeneralLinearGroup (Fin 3) IntegralAdeles}
    (hk : GeneralLinearGroup.map integralEmbedding k ∈ lineParabolic FiniteAdeles) :
    k ∈ lineParabolic IntegralAdeles := by
  have h10 : integralEmbedding (k.val 1 0) = integralEmbedding 0 := by
    rw [map_zero]; exact hk.1
  have h20 : integralEmbedding (k.val 2 0) = integralEmbedding 0 := by
    rw [map_zero]; exact hk.2
  exact ⟨integralEmbedding_injective h10, integralEmbedding_injective h20⟩

/-! ## The finite factor -/

open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm (finiteAdeleUnit)

theorem finiteAdeleUnit_mul (s t : FiniteAdelesˣ) :
    finiteAdeleUnit (s * t) = finiteAdeleUnit s * finiteAdeleUnit t := by
  apply Units.ext
  change ((1 : ℝ), (s * t).val) = ((1 : ℝ) * 1, s.val * t.val)
  rw [one_mul, Units.val_mul]

theorem finiteAdeleUnit_integral (u : IntegralAdelesˣ) :
    finiteAdeleUnit (Units.map integralEmbedding.toMonoidHom u) = integralAdeleUnit u :=
  Units.ext rfl

/-- The finite part of the character and modulus of a line-induced section. -/
def finiteLineFactor (χ : RankOneCharacter) (a b : ℂ) (p : FiniteGL)
    (hp : p ∈ lineParabolic FiniteAdeles) : ℂ :=
  χ.toMonoidHom (finiteAdeleUnit (lineCornerUnit p hp)) *
    normPower (finiteAdeleUnit (lineCornerUnit p hp)) a *
    normPower (finiteAdeleUnit (GeneralLinearGroup.det (lineBlockGL p hp))) b

theorem finiteLineFactor_mul (χ : RankOneCharacter) (a b : ℂ) {p q : FiniteGL}
    (hp : p ∈ lineParabolic FiniteAdeles) (hq : q ∈ lineParabolic FiniteAdeles) :
    finiteLineFactor χ a b (p * q) ((lineParabolic FiniteAdeles).mul_mem hp hq) =
      finiteLineFactor χ a b p hp * finiteLineFactor χ a b q hq := by
  unfold finiteLineFactor
  rw [lineCornerUnit_mul hp hq, lineBlockGL_mul hp hq, map_mul, finiteAdeleUnit_mul,
    finiteAdeleUnit_mul, map_mul,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_mul,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_mul]
  ring

theorem finiteAdeleUnit_det_integral (B : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    finiteAdeleUnit (GeneralLinearGroup.det (GeneralLinearGroup.map integralEmbedding B)) =
      integralAdeleUnit (GeneralLinearGroup.det B) := by
  apply Units.ext
  change ((1 : ℝ), (B.val.map integralEmbedding).det) = ((1 : ℝ), integralEmbedding B.val.det)
  rw [RingHom.map_det]
  rfl

/-- The finite factor is trivial on integral line-parabolic elements when `χ` is trivial on
integral units. -/
theorem finiteLineFactor_integral (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {k : GeneralLinearGroup (Fin 3) IntegralAdeles} (hk : k ∈ lineParabolic IntegralAdeles)
    (hmap : GeneralLinearGroup.map integralEmbedding k ∈ lineParabolic FiniteAdeles) :
    finiteLineFactor χ a b (GeneralLinearGroup.map integralEmbedding k) hmap = 1 := by
  unfold finiteLineFactor
  rw [lineCornerUnit_map integralEmbedding k hk hmap, lineBlockGL_map integralEmbedding k hk hmap,
    finiteAdeleUnit_integral, finiteAdeleUnit_det_integral, hχ,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit]
  ring

theorem finiteLineFactor_one (χ : RankOneCharacter) (a b : ℂ)
    (h1 : (1 : FiniteGL) ∈ lineParabolic FiniteAdeles) : finiteLineFactor χ a b 1 h1 = 1 := by
  have hcorner : lineCornerUnit (1 : FiniteGL) h1 = 1 := Units.ext (by simp [lineCornerUnit])
  have hblock : lineBlockGL (1 : FiniteGL) h1 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lineBlockGL]
  have hunit : finiteAdeleUnit (1 : FiniteAdelesˣ) = 1 := Units.ext rfl
  unfold finiteLineFactor
  rw [hcorner, hblock, map_one, hunit, map_one]
  simp [normPower]

/-! ## The finite vector -/

variable (σ : CuspidalRepresentation)

/-- The `GL₂(Ẑ)`-fixed vectors. -/
def sphericalSubspace : Submodule ℂ σ.H where
  carrier := {v | ∀ k : GeneralLinearGroup (Fin 2) IntegralAdeles,
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) v = v}
  zero_mem' := by intro k; simp
  add_mem' {v w} hv hw := by intro k; simp [map_add, hv k, hw k]
  smul_mem' c v hv := by intro k; simp [map_smul, hv k]

/-- The parabolic part of the chosen finite line Iwasawa decomposition. -/
def finiteLineParabolic (g : FiniteGL) : FiniteGL := Classical.choose (finiteLine_factorization g)

theorem finiteLineParabolic_mem (g : FiniteGL) : finiteLineParabolic g ∈ lineParabolic FiniteAdeles :=
  (Classical.choose_spec (finiteLine_factorization g)).1

theorem finiteLineParabolic_spec (g : FiniteGL) : ∃ k : GeneralLinearGroup (Fin 3) IntegralAdeles,
    g = finiteLineParabolic g * GeneralLinearGroup.map integralEmbedding k :=
  (Classical.choose_spec (finiteLine_factorization g)).2

/-- The spherical finite part of a line-induced vector. -/
def finiteLineVector (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (v : σ.H) : σ.H :=
  finiteLineFactor χ a b (finiteLineParabolic g) (finiteLineParabolic_mem g) •
    σ.π (atFinite (lineBlockGL (finiteLineParabolic g) (finiteLineParabolic_mem g))) v

variable {σ}

/-- Changing the parabolic factor by an integral element does not change the value. -/
theorem lineValue_eq_of_integral (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) {p₁ p₂ : FiniteGL}
    (h₁ : p₁ ∈ lineParabolic FiniteAdeles) (h₂ : p₂ ∈ lineParabolic FiniteAdeles)
    (q : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (hsplit : p₁ = p₂ * GeneralLinearGroup.map integralEmbedding q) :
    finiteLineFactor χ a b p₁ h₁ • σ.π (atFinite (lineBlockGL p₁ h₁)) v =
      finiteLineFactor χ a b p₂ h₂ • σ.π (atFinite (lineBlockGL p₂ h₂)) v := by
  subst hsplit
  have hqmem : GeneralLinearGroup.map integralEmbedding q ∈ lineParabolic FiniteAdeles := by
    have h := (lineParabolic FiniteAdeles).mul_mem ((lineParabolic FiniteAdeles).inv_mem h₂) h₁
    rwa [inv_mul_cancel_left] at h
  have hqint : q ∈ lineParabolic IntegralAdeles := integral_mem_lineParabolic hqmem
  have hfac := finiteLineFactor_mul χ a b h₂ hqmem
  rw [finiteLineFactor_integral χ a b hχ hqint hqmem, mul_one] at hfac
  have hblk := lineBlockGL_mul h₂ hqmem
  rw [lineBlockGL_map integralEmbedding q hqint hqmem] at hblk
  rw [show finiteLineFactor χ a b (p₂ * GeneralLinearGroup.map integralEmbedding q) h₁ =
      finiteLineFactor χ a b (p₂ * GeneralLinearGroup.map integralEmbedding q)
        ((lineParabolic FiniteAdeles).mul_mem h₂ hqmem) from rfl, hfac,
    show lineBlockGL (p₂ * GeneralLinearGroup.map integralEmbedding q) h₁ =
      lineBlockGL (p₂ * GeneralLinearGroup.map integralEmbedding q)
        ((lineParabolic FiniteAdeles).mul_mem h₂ hqmem) from rfl, hblk,
    ← atFinite_mul, map_mul, Module.End.mul_apply, hv (lineBlockGL q hqint)]

/-- **Independence of the decomposition.** -/
theorem finiteLineVector_eq (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) {g p : FiniteGL} (hp : p ∈ lineParabolic FiniteAdeles)
    (k : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (hg : g = p * GeneralLinearGroup.map integralEmbedding k) :
    finiteLineVector σ χ a b g v =
      finiteLineFactor χ a b p hp • σ.π (atFinite (lineBlockGL p hp)) v := by
  obtain ⟨k₀, hk₀⟩ := finiteLineParabolic_spec g
  unfold finiteLineVector
  apply lineValue_eq_of_integral χ a b hχ hv (finiteLineParabolic_mem g) hp (k * k₀⁻¹)
  have h := hk₀.symm.trans hg
  rw [map_mul, map_inv, ← mul_assoc, ← h, mul_inv_cancel_right]

/-- **Left equivariance.** -/
theorem finiteLineVector_mul (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) {p : FiniteGL} (hp : p ∈ lineParabolic FiniteAdeles)
    (g : FiniteGL) :
    finiteLineVector σ χ a b (p * g) v =
      finiteLineFactor χ a b p hp • σ.π (atFinite (lineBlockGL p hp))
        (finiteLineVector σ χ a b g v) := by
  obtain ⟨k₀, hk₀⟩ := finiteLineParabolic_spec g
  have hp₀ := finiteLineParabolic_mem g
  rw [finiteLineVector_eq χ a b hχ hv ((lineParabolic FiniteAdeles).mul_mem hp hp₀) k₀
      (by rw [mul_assoc, ← hk₀]),
    finiteLineVector_eq χ a b hχ hv hp₀ k₀ hk₀, finiteLineFactor_mul χ a b hp hp₀,
    lineBlockGL_mul hp hp₀, ← atFinite_mul, map_mul, Module.End.mul_apply, map_smul, smul_smul]

/-- **Right `GL₃(Ẑ)`-invariance.** -/
theorem finiteLineVector_mul_integral (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) (g : FiniteGL)
    (k : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    finiteLineVector σ χ a b (g * GeneralLinearGroup.map integralEmbedding k) v =
      finiteLineVector σ χ a b g v := by
  obtain ⟨k₀, hk₀⟩ := finiteLineParabolic_spec g
  have hp₀ := finiteLineParabolic_mem g
  rw [finiteLineVector_eq χ a b hχ hv hp₀ (k₀ * k) (by rw [map_mul, ← mul_assoc, ← hk₀]),
    finiteLineVector_eq χ a b hχ hv hp₀ k₀ hk₀]

/-- Right invariance under the finite level. -/
theorem finiteLineVector_mul_level (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) (g : FiniteGL) (k : finiteLevel) :
    finiteLineVector σ χ a b (g * k.val) v = finiteLineVector σ χ a b g v := by
  obtain ⟨k', _, hk'⟩ := Subgroup.mem_map.mp k.property
  rw [← hk']
  exact finiteLineVector_mul_integral χ a b hχ hv g k'

/-- The value at an integral point. -/
theorem finiteLineVector_integral (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) (k : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    finiteLineVector σ χ a b (GeneralLinearGroup.map integralEmbedding k) v = v := by
  have h1 : (1 : FiniteGL) ∈ lineParabolic FiniteAdeles := (lineParabolic FiniteAdeles).one_mem
  rw [finiteLineVector_eq χ a b hχ hv h1 k (one_mul _).symm, finiteLineFactor_one, one_smul]
  have hblock : lineBlockGL (1 : FiniteGL) h1 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lineBlockGL]
  rw [hblock, TernaryPeriodPolynomials.SphericalDetection.Helpers.atFinite_one, map_one,
    Module.End.one_apply]

/-- Real translations commute with the finite part. -/
theorem atFinite_mul_atInfinity_comm {m : ℕ} (f : GeneralLinearGroup (Fin m) FiniteAdeles)
    (r : GeneralLinearGroup (Fin m) ℝ) : atFinite f * atInfinity r = atInfinity r * atFinite f := by
  change combineGL 1 f * combineGL r 1 = combineGL r 1 * combineGL 1 f
  rw [combineGL_mul, combineGL_mul, one_mul, one_mul, mul_one, mul_one]

theorem finiteLineVector_real (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (v : σ.H)
    (h : BinaryRealGL) :
    finiteLineVector σ χ a b g (σ.π (atInfinity h) v) =
      σ.π (atInfinity h) (finiteLineVector σ χ a b g v) := by
  unfold finiteLineVector
  rw [map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    atFinite_mul_atInfinity_comm]

theorem sphericalSubspace_real {v : σ.H} (hv : v ∈ sphericalSubspace σ) (h : BinaryRealGL) :
    σ.π (atInfinity h) v ∈ sphericalSubspace σ := by
  intro k
  rw [← Module.End.mul_apply, ← map_mul, atFinite_mul_atInfinity_comm, map_mul,
    Module.End.mul_apply, hv k]

theorem finiteLineVector_smooth (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) {v : σ.H}
    (hv : v ∈ σ.smooth) : finiteLineVector σ χ a b g v ∈ σ.smooth :=
  σ.smooth.smul_mem _ (σ.smooth_stable _ _ hv)

theorem finiteLineVector_add (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (v w : σ.H) :
    finiteLineVector σ χ a b g (v + w) =
      finiteLineVector σ χ a b g v + finiteLineVector σ χ a b g w := by
  unfold finiteLineVector
  rw [map_add, smul_add]

theorem finiteLineVector_smul (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (c : ℂ) (v : σ.H) :
    finiteLineVector σ χ a b g (c • v) = c • finiteLineVector σ χ a b g v := by
  unfold finiteLineVector
  rw [map_smul, smul_comm]

end TernaryPeriodPolynomials.SourceConstruction
