module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.FiniteSpherical

@[expose] public section


/-!
# The spherical finite part of a plane-induced section

The plane analogue of `FiniteSpherical`: with the finite plane Iwasawa decomposition
`GL₃(𝔸_f) = P_plane(𝔸_f) · GL₃(Ẑ)`, for a character trivial on `Ẑ^×` and a `GL₂(Ẑ)`-fixed vector `v`,
`g = p k ↦ χ_f(corner p) |corner p|^a |det block p|^b · π(block p) v` is well defined, left
`P_plane(𝔸_f)`-equivariant and right `GL₃(Ẑ)`-invariant (`finitePlaneVector`). Here the corner is the
`(2,2)` entry and the block the upper left `2 × 2` block.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance
  (combineGL_mul atInfinity_mul atFinite_mul)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm (finiteAdeleUnit)

namespace TernaryPeriodPolynomials.SourceConstruction

/-- **Finite plane Iwasawa decomposition.** -/
theorem finitePlane_factorization (g : FiniteGL) :
    ∃ p : FiniteGL, p ∈ planeParabolic FiniteAdeles ∧
      ∃ k : GeneralLinearGroup (Fin 3) IntegralAdeles,
        g = p * GeneralLinearGroup.map integralEmbedding k := by
  obtain ⟨p, k, h⟩ :=
    TernaryPeriodPolynomials.SphericalDetection.Helpers.finiteGL_parabolic_compact_factorization g
  exact ⟨p.val, p.property, k, h⟩

/-! ## Levi projections of the plane parabolic over a commutative ring -/

section Levi

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The rank-one corner of a plane-parabolic element. -/
def planeCornerUnit (p : GeneralLinearGroup (Fin 3) R) (hp : p ∈ planeParabolic R) : Rˣ where
  val := p.val 2 2
  inv := p.inv 2 2
  val_inv := by
    have h20 : p.val 2 0 = 0 := hp.1
    have h21 : p.val 2 1 = 0 := hp.2
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 2 2) p.val_inv
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h20, h21, zero_mul, zero_add] at h
    simpa using h
  inv_val := by
    have hinv := (planeParabolic R).inv_mem hp
    have h20 : p.inv 2 0 = 0 := hinv.1
    have h21 : p.inv 2 1 = 0 := hinv.2
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 2 2) p.inv_val
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h20, h21, zero_mul, zero_add] at h
    simpa using h

/-- The `GL₂` block of a plane-parabolic element. -/
def planeBlockGL (p : GeneralLinearGroup (Fin 3) R) (hp : p ∈ planeParabolic R) :
    GeneralLinearGroup (Fin 2) R where
  val := !![p.val 0 0, p.val 0 1; p.val 1 0, p.val 1 1]
  inv := !![p.inv 0 0, p.inv 0 1; p.inv 1 0, p.inv 1 1]
  val_inv := by
    have hinv := (planeParabolic R).inv_mem hp
    have h20 : p.inv 2 0 = 0 := hinv.1
    have h21 : p.inv 2 1 = 0 := hinv.2
    have e := p.val_inv
    have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 0) e
    have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 1) e
    have h10 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 1 0) e
    have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 1 1) e
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h20, h21, mul_zero, add_zero] at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h01
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h10
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h11
  inv_val := by
    have h20 : p.val 2 0 = 0 := hp.1
    have h21 : p.val 2 1 = 0 := hp.2
    have e := p.inv_val
    have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 0) e
    have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 1) e
    have h10 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 1 0) e
    have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 1 1) e
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h20, h21, mul_zero, add_zero] at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h01
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h10
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h11

theorem planeCornerUnit_mul {p q : GeneralLinearGroup (Fin 3) R} (hp : p ∈ planeParabolic R)
    (hq : q ∈ planeParabolic R) :
    planeCornerUnit (p * q) ((planeParabolic R).mul_mem hp hq) =
      planeCornerUnit p hp * planeCornerUnit q hq := by
  have h20 : p.val 2 0 = 0 := hp.1
  have h21 : p.val 2 1 = 0 := hp.2
  apply Units.ext
  change (p.val * q.val) 2 2 = p.val 2 2 * q.val 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, h20, h21]

theorem planeBlockGL_mul {p q : GeneralLinearGroup (Fin 3) R} (hp : p ∈ planeParabolic R)
    (hq : q ∈ planeParabolic R) :
    planeBlockGL (p * q) ((planeParabolic R).mul_mem hp hq) =
      planeBlockGL p hp * planeBlockGL q hq := by
  have h20 : q.val 2 0 = 0 := hq.1
  have h21 : q.val 2 1 = 0 := hq.2
  apply Units.ext
  change !![(p.val * q.val) 0 0, (p.val * q.val) 0 1; (p.val * q.val) 1 0, (p.val * q.val) 1 1] =
    !![p.val 0 0, p.val 0 1; p.val 1 0, p.val 1 1] * !![q.val 0 0, q.val 0 1; q.val 1 0, q.val 1 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, h20, h21]

theorem planeCornerUnit_congr {p q : GeneralLinearGroup (Fin 3) R} (h : p = q)
    (hp : p ∈ planeParabolic R) (hq : q ∈ planeParabolic R) :
    planeCornerUnit p hp = planeCornerUnit q hq := by
  subst h
  rfl

theorem planeBlockGL_congr {p q : GeneralLinearGroup (Fin 3) R} (h : p = q)
    (hp : p ∈ planeParabolic R) (hq : q ∈ planeParabolic R) :
    planeBlockGL p hp = planeBlockGL q hq := by
  subst h
  rfl

theorem planeCornerUnit_map (f : R →+* S) (p : GeneralLinearGroup (Fin 3) R)
    (hp : p ∈ planeParabolic R) (hfp : GeneralLinearGroup.map f p ∈ planeParabolic S) :
    planeCornerUnit (GeneralLinearGroup.map f p) hfp = Units.map f.toMonoidHom (planeCornerUnit p hp) :=
  Units.ext rfl

theorem planeBlockGL_map (f : R →+* S) (p : GeneralLinearGroup (Fin 3) R)
    (hp : p ∈ planeParabolic R) (hfp : GeneralLinearGroup.map f p ∈ planeParabolic S) :
    planeBlockGL (GeneralLinearGroup.map f p) hfp = GeneralLinearGroup.map f (planeBlockGL p hp) := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.val_map_apply]
  fin_cases i <;> fin_cases j <;> rfl

end Levi

/-- An integral matrix whose finite image lies in the plane parabolic lies in the integral plane
parabolic. -/
theorem integral_mem_planeParabolic {k : GeneralLinearGroup (Fin 3) IntegralAdeles}
    (hk : GeneralLinearGroup.map integralEmbedding k ∈ planeParabolic FiniteAdeles) :
    k ∈ planeParabolic IntegralAdeles := by
  have h20 : integralEmbedding (k.val 2 0) = integralEmbedding 0 := by
    rw [map_zero]; exact hk.1
  have h21 : integralEmbedding (k.val 2 1) = integralEmbedding 0 := by
    rw [map_zero]; exact hk.2
  exact ⟨integralEmbedding_injective h20, integralEmbedding_injective h21⟩

/-! ## The finite factor -/


/-- The finite part of the character and modulus of a plane-induced section. -/
def finitePlaneFactor (χ : RankOneCharacter) (a b : ℂ) (p : FiniteGL)
    (hp : p ∈ planeParabolic FiniteAdeles) : ℂ :=
  χ.toMonoidHom (finiteAdeleUnit (planeCornerUnit p hp)) *
    normPower (finiteAdeleUnit (planeCornerUnit p hp)) a *
    normPower (finiteAdeleUnit (GeneralLinearGroup.det (planeBlockGL p hp))) b

theorem finitePlaneFactor_mul (χ : RankOneCharacter) (a b : ℂ) {p q : FiniteGL}
    (hp : p ∈ planeParabolic FiniteAdeles) (hq : q ∈ planeParabolic FiniteAdeles) :
    finitePlaneFactor χ a b (p * q) ((planeParabolic FiniteAdeles).mul_mem hp hq) =
      finitePlaneFactor χ a b p hp * finitePlaneFactor χ a b q hq := by
  unfold finitePlaneFactor
  rw [planeCornerUnit_mul hp hq, planeBlockGL_mul hp hq, map_mul, finiteAdeleUnit_mul,
    finiteAdeleUnit_mul, map_mul,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_mul,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_mul]
  ring

/-- The finite factor is trivial on integral plane-parabolic elements when `χ` is trivial on
integral units. -/
theorem finitePlaneFactor_integral (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {k : GeneralLinearGroup (Fin 3) IntegralAdeles} (hk : k ∈ planeParabolic IntegralAdeles)
    (hmap : GeneralLinearGroup.map integralEmbedding k ∈ planeParabolic FiniteAdeles) :
    finitePlaneFactor χ a b (GeneralLinearGroup.map integralEmbedding k) hmap = 1 := by
  unfold finitePlaneFactor
  rw [planeCornerUnit_map integralEmbedding k hk hmap, planeBlockGL_map integralEmbedding k hk hmap,
    finiteAdeleUnit_integral, finiteAdeleUnit_det_integral, hχ,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit]
  ring

theorem finitePlaneFactor_one (χ : RankOneCharacter) (a b : ℂ)
    (h1 : (1 : FiniteGL) ∈ planeParabolic FiniteAdeles) : finitePlaneFactor χ a b 1 h1 = 1 := by
  have hcorner : planeCornerUnit (1 : FiniteGL) h1 = 1 := Units.ext (by simp [planeCornerUnit])
  have hblock : planeBlockGL (1 : FiniteGL) h1 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planeBlockGL]
  have hunit : finiteAdeleUnit (1 : FiniteAdelesˣ) = 1 := Units.ext rfl
  unfold finitePlaneFactor
  rw [hcorner, hblock, map_one, hunit, map_one]
  simp [normPower]

/-! ## The finite vector -/

variable (σ : CuspidalRepresentation)

/-- The parabolic part of the chosen finite plane Iwasawa decomposition. -/
def finitePlaneParabolic (g : FiniteGL) : FiniteGL := Classical.choose (finitePlane_factorization g)

theorem finitePlaneParabolic_mem (g : FiniteGL) : finitePlaneParabolic g ∈ planeParabolic FiniteAdeles :=
  (Classical.choose_spec (finitePlane_factorization g)).1

theorem finitePlaneParabolic_spec (g : FiniteGL) : ∃ k : GeneralLinearGroup (Fin 3) IntegralAdeles,
    g = finitePlaneParabolic g * GeneralLinearGroup.map integralEmbedding k :=
  (Classical.choose_spec (finitePlane_factorization g)).2

/-- The spherical finite part of a plane-induced vector. -/
def finitePlaneVector (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (v : σ.H) : σ.H :=
  finitePlaneFactor χ a b (finitePlaneParabolic g) (finitePlaneParabolic_mem g) •
    σ.π (atFinite (planeBlockGL (finitePlaneParabolic g) (finitePlaneParabolic_mem g))) v

variable {σ}

/-- Changing the parabolic factor by an integral element does not change the value. -/
theorem planeValue_eq_of_integral (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) {p₁ p₂ : FiniteGL}
    (h₁ : p₁ ∈ planeParabolic FiniteAdeles) (h₂ : p₂ ∈ planeParabolic FiniteAdeles)
    (q : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (hsplit : p₁ = p₂ * GeneralLinearGroup.map integralEmbedding q) :
    finitePlaneFactor χ a b p₁ h₁ • σ.π (atFinite (planeBlockGL p₁ h₁)) v =
      finitePlaneFactor χ a b p₂ h₂ • σ.π (atFinite (planeBlockGL p₂ h₂)) v := by
  subst hsplit
  have hqmem : GeneralLinearGroup.map integralEmbedding q ∈ planeParabolic FiniteAdeles := by
    have h := (planeParabolic FiniteAdeles).mul_mem ((planeParabolic FiniteAdeles).inv_mem h₂) h₁
    rwa [inv_mul_cancel_left] at h
  have hqint : q ∈ planeParabolic IntegralAdeles := integral_mem_planeParabolic hqmem
  have hfac := finitePlaneFactor_mul χ a b h₂ hqmem
  rw [finitePlaneFactor_integral χ a b hχ hqint hqmem, mul_one] at hfac
  have hblk := planeBlockGL_mul h₂ hqmem
  rw [planeBlockGL_map integralEmbedding q hqint hqmem] at hblk
  rw [show finitePlaneFactor χ a b (p₂ * GeneralLinearGroup.map integralEmbedding q) h₁ =
      finitePlaneFactor χ a b (p₂ * GeneralLinearGroup.map integralEmbedding q)
        ((planeParabolic FiniteAdeles).mul_mem h₂ hqmem) from rfl, hfac,
    show planeBlockGL (p₂ * GeneralLinearGroup.map integralEmbedding q) h₁ =
      planeBlockGL (p₂ * GeneralLinearGroup.map integralEmbedding q)
        ((planeParabolic FiniteAdeles).mul_mem h₂ hqmem) from rfl, hblk,
    ← atFinite_mul, map_mul, Module.End.mul_apply, hv (planeBlockGL q hqint)]

/-- **Independence of the decomposition.** -/
theorem finitePlaneVector_eq (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) {g p : FiniteGL} (hp : p ∈ planeParabolic FiniteAdeles)
    (k : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (hg : g = p * GeneralLinearGroup.map integralEmbedding k) :
    finitePlaneVector σ χ a b g v =
      finitePlaneFactor χ a b p hp • σ.π (atFinite (planeBlockGL p hp)) v := by
  obtain ⟨k₀, hk₀⟩ := finitePlaneParabolic_spec g
  unfold finitePlaneVector
  apply planeValue_eq_of_integral χ a b hχ hv (finitePlaneParabolic_mem g) hp (k * k₀⁻¹)
  have h := hk₀.symm.trans hg
  rw [map_mul, map_inv, ← mul_assoc, ← h, mul_inv_cancel_right]

/-- **Left equivariance.** -/
theorem finitePlaneVector_mul (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) {p : FiniteGL} (hp : p ∈ planeParabolic FiniteAdeles)
    (g : FiniteGL) :
    finitePlaneVector σ χ a b (p * g) v =
      finitePlaneFactor χ a b p hp • σ.π (atFinite (planeBlockGL p hp))
        (finitePlaneVector σ χ a b g v) := by
  obtain ⟨k₀, hk₀⟩ := finitePlaneParabolic_spec g
  have hp₀ := finitePlaneParabolic_mem g
  rw [finitePlaneVector_eq χ a b hχ hv ((planeParabolic FiniteAdeles).mul_mem hp hp₀) k₀
      (by rw [mul_assoc, ← hk₀]),
    finitePlaneVector_eq χ a b hχ hv hp₀ k₀ hk₀, finitePlaneFactor_mul χ a b hp hp₀,
    planeBlockGL_mul hp hp₀, ← atFinite_mul, map_mul, Module.End.mul_apply, map_smul, smul_smul]

/-- **Right `GL₃(Ẑ)`-invariance.** -/
theorem finitePlaneVector_mul_integral (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) (g : FiniteGL)
    (k : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    finitePlaneVector σ χ a b (g * GeneralLinearGroup.map integralEmbedding k) v =
      finitePlaneVector σ χ a b g v := by
  obtain ⟨k₀, hk₀⟩ := finitePlaneParabolic_spec g
  have hp₀ := finitePlaneParabolic_mem g
  rw [finitePlaneVector_eq χ a b hχ hv hp₀ (k₀ * k) (by rw [map_mul, ← mul_assoc, ← hk₀]),
    finitePlaneVector_eq χ a b hχ hv hp₀ k₀ hk₀]

/-- Right invariance under the finite level. -/
theorem finitePlaneVector_mul_level (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) (g : FiniteGL) (k : finiteLevel) :
    finitePlaneVector σ χ a b (g * k.val) v = finitePlaneVector σ χ a b g v := by
  obtain ⟨k', _, hk'⟩ := Subgroup.mem_map.mp k.property
  rw [← hk']
  exact finitePlaneVector_mul_integral χ a b hχ hv g k'

/-- The value at an integral point. -/
theorem finitePlaneVector_integral (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) (k : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    finitePlaneVector σ χ a b (GeneralLinearGroup.map integralEmbedding k) v = v := by
  have h1 : (1 : FiniteGL) ∈ planeParabolic FiniteAdeles := (planeParabolic FiniteAdeles).one_mem
  rw [finitePlaneVector_eq χ a b hχ hv h1 k (one_mul _).symm, finitePlaneFactor_one, one_smul]
  have hblock : planeBlockGL (1 : FiniteGL) h1 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planeBlockGL]
  rw [hblock, TernaryPeriodPolynomials.SphericalDetection.Helpers.atFinite_one, map_one,
    Module.End.one_apply]

theorem finitePlaneVector_real (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (v : σ.H)
    (h : BinaryRealGL) :
    finitePlaneVector σ χ a b g (σ.π (atInfinity h) v) =
      σ.π (atInfinity h) (finitePlaneVector σ χ a b g v) := by
  unfold finitePlaneVector
  rw [map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    atFinite_mul_atInfinity_comm]

theorem finitePlaneVector_smooth (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) {v : σ.H}
    (hv : v ∈ σ.smooth) : finitePlaneVector σ χ a b g v ∈ σ.smooth :=
  σ.smooth.smul_mem _ (σ.smooth_stable _ _ hv)

theorem finitePlaneVector_add (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (v w : σ.H) :
    finitePlaneVector σ χ a b g (v + w) =
      finitePlaneVector σ χ a b g v + finitePlaneVector σ χ a b g w := by
  unfold finitePlaneVector
  rw [map_add, smul_add]

theorem finitePlaneVector_smul (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (c : ℂ) (v : σ.H) :
    finitePlaneVector σ χ a b g (c • v) = c • finitePlaneVector σ χ a b g v := by
  unfold finitePlaneVector
  rw [map_smul, smul_comm]

end TernaryPeriodPolynomials.SourceConstruction
