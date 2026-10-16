module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Boundary
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.BinaryCoefficients
public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Levi
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-!
# The radical cocycle of the real plane parabolic

Let `ι : ℂ[x₀,x₁] → ℂ[x₀,x₁,x₂]` be the renaming `binaryEmbed`.  For `p` in the real plane
parabolic write `m(p) = planeLevi A_p d_p` for its Levi part and `u(p) = p · m(p)⁻¹` for its
unipotent part.  With `ρ = fullCoefficientComponent χ` the full-polynomial version of
`realCoefficientComponent` (`ρ(g) f = χ(g) det(g)⁻¹ f(g⁻¹ x)`):

* `leviStar` is the action `p ⋆ Q = χ(p) det(A_p)⁻¹ Q(A_p⁻¹ x)` of the parabolic on binary forms; it
  is characterised by `ι (p ⋆ Q) = d_p • ρ(m(p)) (ι Q)` (`binaryEmbed_leviStar`);
* `planeRadical n χ p Q` is the exact quotient by `x₂` of `ρ(u(p)) (ι Q) - ι Q`
  (`X2_mul_planeRadical`), a homogeneous polynomial of degree `n`;
* the cocycle identity `planeRadical (p₁ p₂) Q = planeRadical p₁ Q + ρ(p₁) (planeRadical p₂ (p₁⁻¹ ⋆ Q))`
  (`planeRadical_mul`), and `planeRadical` vanishes on the Levi subgroup.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open MvPolynomial Matrix GeneralEisenstein
open GeneralEisenstein.Adelic
  (InPlaneParabolic planeParabolic planeUnipotent planeLevi planeLevi_mem planeBlock planeBlock_mul
    inPlane_inv)

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## Small algebraic helpers -/

theorem rc_div_mul_self {a b : ℝ} (hb : b ≠ 0) : a / b * b = a := by field_simp

theorem rc_algebraMap_ne_zero {x : ℝ} (hx : x ≠ 0) : algebraMap ℝ ℂ x ≠ 0 := fun h =>
  hx ((algebraMap ℝ ℂ).injective (h.trans (map_zero (algebraMap ℝ ℂ)).symm))

theorem rc_scalar_aux {a : ℂ} (ha : a ≠ 0) (x y : ℂ) : x * y = a * (x * (y * a⁻¹)) := by
  linear_combination (-(x * y)) * mul_inv_cancel₀ ha

theorem X2_ne_zero : (X 2 : Poly) ≠ 0 := X_ne_zero 2

/-! ## The corner entry and the top-left block of a plane-parabolic element -/

theorem corner_mul_inv {g : RealGL3} (hg : InPlaneParabolic g) :
    g.val 2 2 * g.inv 2 2 = 1 := by
  have hr := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 2 2) g.mul_inv
  simpa [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2] using hr

theorem corner_ne_zero {g : RealGL3} (hg : InPlaneParabolic g) : g.val 2 2 ≠ 0 := by
  intro h
  have h1 := corner_mul_inv hg
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- The corner entry of a plane-parabolic element as a unit. -/
def cornerUnit (g : RealGL3) (hg : InPlaneParabolic g) : ℝˣ :=
  ⟨g.val 2 2, g.inv 2 2, corner_mul_inv hg, by rw [mul_comm]; exact corner_mul_inv hg⟩

/-- The corner entry `d_p`, as a homomorphism to the units. -/
def cornerHom : planeParabolic ℝ →* ℝˣ where
  toFun p := cornerUnit p.1 p.2
  map_one' := by
    apply Units.ext
    rfl
  map_mul' p q := by
    have hp : InPlaneParabolic p.1 := p.2
    apply Units.ext
    show (p.1 * q.1).val 2 2 = p.1.val 2 2 * q.1.val 2 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, hp.1, hp.2]

@[simp] theorem cornerHom_val (p : planeParabolic ℝ) :
    ((cornerHom p : ℝˣ) : ℝ) = p.1.val 2 2 := rfl

theorem corner_inv (p : planeParabolic ℝ) :
    (p⁻¹ : planeParabolic ℝ).1.val 2 2 = (p.1.val 2 2)⁻¹ := by
  have h : cornerHom p⁻¹ = (cornerHom p)⁻¹ := map_inv cornerHom p
  have h2 : ((cornerHom p⁻¹ : ℝˣ) : ℝ) = (((cornerHom p)⁻¹ : ℝˣ) : ℝ) :=
    congrArg (fun u : ℝˣ => (u : ℝ)) h
  rw [Units.val_inv_eq_inv_val] at h2
  exact h2

/-- The top-left `2 × 2` block of a `3 × 3` matrix. -/
def blockOf (g : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![g 0 0, g 0 1; g 1 0, g 1 1]

theorem blockOf_mul (g h : Matrix (Fin 3) (Fin 3) ℝ) (h20 : h 2 0 = 0) (h21 : h 2 1 = 0) :
    blockOf (g * h) = blockOf g * blockOf h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockOf, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h20, h21]

theorem blockOf_one : blockOf (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The top-left block of a plane-parabolic element, as a matrix. -/
def blockP (p : planeParabolic ℝ) : Matrix (Fin 2) (Fin 2) ℝ := blockOf p.1.val

theorem blockP_mul (p q : planeParabolic ℝ) : blockP (p * q) = blockP p * blockP q := by
  have hq : InPlaneParabolic q.1 := q.2
  exact blockOf_mul p.1.val q.1.val hq.1 hq.2

theorem blockP_one : blockP (1 : planeParabolic ℝ) = 1 := blockOf_one

theorem blockP_mul_inv (p : planeParabolic ℝ) : blockP p * blockP p⁻¹ = 1 := by
  rw [← blockP_mul, mul_inv_cancel, blockP_one]

theorem blockP_inv_mul (p : planeParabolic ℝ) : blockP p⁻¹ * blockP p = 1 := by
  rw [← blockP_mul, inv_mul_cancel, blockP_one]

/-- The top-left block `A_p ∈ GL₂(ℝ)` of a plane-parabolic element. -/
def leviBlock (p : planeParabolic ℝ) : GeneralLinearGroup (Fin 2) ℝ :=
  ⟨blockP p, blockP p⁻¹, blockP_mul_inv p, blockP_inv_mul p⟩

/-- `p ↦ A_p` is a homomorphism. -/
def leviBlockHom : planeParabolic ℝ →* GeneralLinearGroup (Fin 2) ℝ where
  toFun := leviBlock
  map_one' := Units.ext blockP_one
  map_mul' p q := Units.ext (blockP_mul p q)

theorem planeLevi_mul_real (A B : GeneralLinearGroup (Fin 2) ℝ) (d e : ℝˣ) :
    planeLevi (A * B) (d * e) = planeLevi A d * planeLevi B e :=
  Units.ext (planeBlock_mul A.val B.val d.val e.val)

/-- The Levi part `m(p) = planeLevi A_p d_p` of a plane-parabolic element. -/
def planeLeviPart (p : planeParabolic ℝ) : RealGL3 := planeLevi (leviBlock p) (cornerHom p)

theorem planeLeviPart_mul (p q : planeParabolic ℝ) :
    planeLeviPart (p * q) = planeLeviPart p * planeLeviPart q := by
  have h1 : leviBlock (p * q) = leviBlock p * leviBlock q := leviBlockHom.map_mul p q
  have h2 : cornerHom (p * q) = cornerHom p * cornerHom q := cornerHom.map_mul p q
  unfold planeLeviPart
  rw [h1, h2]
  exact planeLevi_mul_real _ _ _ _

/-- `p ↦ m(p)` is a homomorphism. -/
def planeLeviPartHom : planeParabolic ℝ →* RealGL3 :=
  MonoidHom.mk' planeLeviPart planeLeviPart_mul

theorem planeLeviPart_inv (p : planeParabolic ℝ) :
    planeLeviPart p⁻¹ = (planeLeviPart p)⁻¹ := map_inv planeLeviPartHom p

theorem planeLeviPart_val (p : planeParabolic ℝ) :
    (planeLeviPart p).val =
      !![p.1.val 0 0, p.1.val 0 1, 0; p.1.val 1 0, p.1.val 1 1, 0; 0, 0, p.1.val 2 2] := rfl

/-- The unipotent part `u(p) = planeUnipotent (p₀₂ / d) (p₁₂ / d)` of a plane-parabolic element. -/
def planeUnipotentPart (p : planeParabolic ℝ) : RealGL3 :=
  planeUnipotent (p.1.val 0 2 / p.1.val 2 2) (p.1.val 1 2 / p.1.val 2 2)

theorem planeUnipotentPart_val (p : planeParabolic ℝ) :
    (planeUnipotentPart p).val =
      !![1, 0, p.1.val 0 2 / p.1.val 2 2; 0, 1, p.1.val 1 2 / p.1.val 2 2; 0, 0, 1] := rfl

/-- The Iwasawa-type factorization `p = u(p) · m(p)`. -/
theorem planeUnipotentPart_mul_levi (p : planeParabolic ℝ) :
    planeUnipotentPart p * planeLeviPart p = p.1 := by
  have hp : InPlaneParabolic p.1 := p.2
  have hd : p.1.val 2 2 ≠ 0 := corner_ne_zero hp
  apply Units.ext
  rw [Units.val_mul, planeUnipotentPart_val, planeLeviPart_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hp.1, hp.2, rc_div_mul_self hd]

theorem planeUnipotentPart_eq (p : planeParabolic ℝ) :
    planeUnipotentPart p = p.1 * (planeLeviPart p)⁻¹ :=
  eq_mul_inv_of_mul_eq (planeUnipotentPart_mul_levi p)

theorem planeUnipotentPart_mul (p q : planeParabolic ℝ) :
    planeUnipotentPart (p * q) = p.1 * planeUnipotentPart q * (planeLeviPart p)⁻¹ := by
  rw [planeUnipotentPart_eq (p * q), planeUnipotentPart_eq q, planeLeviPart_mul, _root_.mul_inv_rev]
  simp only [Subgroup.coe_mul, mul_assoc]

theorem planeUnipotent_mem (s t : ℝ) : planeUnipotent s t ∈ planeParabolic ℝ := ⟨rfl, rfl⟩

theorem planeUnipotent_zero {R : Type*} [CommRing R] :
    planeUnipotent (0 : R) 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem planeUnipotentPart_levi (A : GeneralLinearGroup (Fin 2) ℝ) (d : ℝˣ) :
    planeUnipotentPart ⟨planeLevi A d, planeLevi_mem A d⟩ = 1 := by
  have h02 : (planeLevi A d).val 0 2 = 0 := rfl
  have h12 : (planeLevi A d).val 1 2 = 0 := rfl
  show planeUnipotent ((planeLevi A d).val 0 2 / (planeLevi A d).val 2 2)
    ((planeLevi A d).val 1 2 / (planeLevi A d).val 2 2) = 1
  rw [h02, h12, zero_div]
  exact planeUnipotent_zero

theorem planeUnipotentPart_unipotent (s t : ℝ) :
    planeUnipotentPart ⟨planeUnipotent s t, planeUnipotent_mem s t⟩ = planeUnipotent s t := by
  have h02 : (planeUnipotent s t).val 0 2 = s := rfl
  have h12 : (planeUnipotent s t).val 1 2 = t := rfl
  have h22 : (planeUnipotent s t).val 2 2 = 1 := rfl
  show planeUnipotent ((planeUnipotent s t).val 0 2 / (planeUnipotent s t).val 2 2)
    ((planeUnipotent s t).val 1 2 / (planeUnipotent s t).val 2 2) = planeUnipotent s t
  rw [h02, h12, h22, div_one, div_one]

/-! ## Determinants and coefficient maps of unipotent and Levi matrices -/

theorem det_planeUnipotent_gl {R : Type*} [CommRing R] (s t : R) :
    GeneralLinearGroup.det (planeUnipotent s t) = 1 := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, planeUnipotent, Matrix.det_fin_three]

theorem componentCharacter_planeUnipotent (χ : RankOneCharacter) (s t : ℝ) :
    componentCharacter χ (planeUnipotent s t) = 1 := by
  simp [componentCharacter, det_planeUnipotent_gl]

theorem componentCharacter_planeLeviPart (χ : RankOneCharacter) (p : planeParabolic ℝ) :
    componentCharacter χ (planeLeviPart p) = componentCharacter χ p.1 := by
  have hu : componentCharacter χ (planeUnipotentPart p) = 1 :=
    componentCharacter_planeUnipotent χ _ _
  calc componentCharacter χ (planeLeviPart p)
      = componentCharacter χ (planeUnipotentPart p) * componentCharacter χ (planeLeviPart p) := by
        rw [hu, one_mul]
    _ = componentCharacter χ p.1 := by rw [← map_mul, planeUnipotentPart_mul_levi]

theorem det_planeLevi {R : Type*} [CommRing R] (A : GeneralLinearGroup (Fin 2) R) (d : Rˣ) :
    GeneralLinearGroup.det (planeLevi A d) = GeneralLinearGroup.det A * d := by
  apply Units.ext
  rw [Units.val_mul, GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_two]
  show Matrix.det (planeBlock A.val d.val) = _
  rw [Matrix.det_fin_three]
  simp [planeBlock]; ring

/-- Complexification of a real unit. -/
def toComplexUnit (d : ℝˣ) : ℂˣ := Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) d

theorem toComplexUnit_val (d : ℝˣ) : ((toComplexUnit d : ℂˣ) : ℂ) = algebraMap ℝ ℂ (d : ℝ) := rfl

theorem map_planeUnipotent (φ : ℝ →+* ℂ) (s t : ℝ) :
    GeneralLinearGroup.map φ (planeUnipotent s t) = planeUnipotent (φ s) (φ t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeUnipotent, GeneralLinearGroup.map_apply]

theorem map_planeLevi (A : GeneralLinearGroup (Fin 2) ℝ) (d : ℝˣ) :
    GeneralLinearGroup.map (algebraMap ℝ ℂ) (planeLevi A d) =
      planeLevi (GeneralLinearGroup.map (algebraMap ℝ ℂ) A) (toComplexUnit d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi, planeBlock, GeneralLinearGroup.map_apply, toComplexUnit]

/-! ## The full-polynomial component representation -/

/-- `ρ(g) f = χ(g) det(g)⁻¹ f(g⁻¹ x)` on all polynomials: the full-polynomial version of
`realCoefficientComponent`. -/
def fullCoefficientComponent (χ : RankOneCharacter) : Representation ℂ RealGL3 Poly where
  toFun g := componentCharacter χ g • action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) g)
  map_one' := by simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change componentCharacter χ (g * h) •
        action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) (g * h)) v =
      componentCharacter χ g • action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) g)
        (componentCharacter χ h • action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) h) v)
    simp only [map_mul, Module.End.mul_apply, map_smul, smul_smul]

theorem fullCoefficientComponent_mul (χ : RankOneCharacter) (g h : RealGL3) (F : Poly) :
    fullCoefficientComponent χ (g * h) F =
      fullCoefficientComponent χ g (fullCoefficientComponent χ h F) := by
  rw [map_mul, Module.End.mul_apply]

theorem fullCoefficientComponent_one (χ : RankOneCharacter) (F : Poly) :
    fullCoefficientComponent χ 1 F = F := by
  rw [map_one, Module.End.one_apply]

theorem determinantCharacter_neg_one (g : GL3) :
    determinantCharacter (-1) g = ((GeneralLinearGroup.det g : ℂˣ) : ℂ)⁻¹ := by
  exact zpow_neg_one _

theorem fullCoefficientComponent_apply (χ : RankOneCharacter) (g : RealGL3) (F : Poly) :
    fullCoefficientComponent χ g F =
      (componentCharacter χ g *
          ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) g) : ℂˣ) : ℂ)⁻¹) •
        substitute ((GeneralLinearGroup.map (algebraMap ℝ ℂ) g)⁻¹ : GL3) F := by
  rw [mul_smul, ← determinantCharacter_neg_one]; rfl

theorem fullCoefficientComponent_homogeneous (χ : RankOneCharacter) (g : RealGL3) {F : Poly}
    {m : ℕ} (hF : F.IsHomogeneous m) : (fullCoefficientComponent χ g F).IsHomogeneous m := by
  show (componentCharacter χ g •
    action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) g) F).IsHomogeneous m
  rw [Algebra.smul_def]
  exact (action_homogeneous (-1) _ hF).C_mul _

theorem fullCoefficientComponent_planeUnipotent (χ : RankOneCharacter) (s t : ℝ) (F : Poly) :
    fullCoefficientComponent χ (planeUnipotent s t) F =
      substitute ((planeUnipotent (algebraMap ℝ ℂ s) (algebraMap ℝ ℂ t))⁻¹ : GL3) F := by
  rw [fullCoefficientComponent_apply, map_planeUnipotent, componentCharacter_planeUnipotent,
    det_planeUnipotent_gl]
  simp

theorem fullCoefficientComponent_planeLevi (χ : RankOneCharacter)
    (A : GeneralLinearGroup (Fin 2) ℝ) (d : ℝˣ) (F : Poly) :
    fullCoefficientComponent χ (planeLevi A d) F =
      (componentCharacter χ (planeLevi A d) *
          (((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) A) : ℂˣ) : ℂ)⁻¹ *
            ((toComplexUnit d : ℂˣ) : ℂ)⁻¹)) •
        substitute (planeLevi (GeneralLinearGroup.map (algebraMap ℝ ℂ) A) (toComplexUnit d)).inv
          F := by
  rw [fullCoefficientComponent_apply, map_planeLevi, det_planeLevi, Units.val_mul, mul_inv]; rfl

theorem fullCoefficientComponent_planeLeviPart (χ : RankOneCharacter) (p : planeParabolic ℝ)
    (F : Poly) :
    fullCoefficientComponent χ (planeLeviPart p) F =
      (componentCharacter χ p.1 *
          (((GeneralLinearGroup.det
              (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock p)) : ℂˣ) : ℂ)⁻¹ *
            ((toComplexUnit (cornerHom p) : ℂˣ) : ℂ)⁻¹)) •
        substitute (planeLevi (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock p))
          (toComplexUnit (cornerHom p))).inv F := by
  rw [← componentCharacter_planeLeviPart χ p]
  exact fullCoefficientComponent_planeLevi χ (leviBlock p) (cornerHom p) F

/-! ## Multiplication by `x₂` and the plane parabolic -/

theorem linearForm_two {N : Matrix (Fin 3) (Fin 3) ℂ} (h0 : N 2 0 = 0) (h1 : N 2 1 = 0) :
    linearForm N 2 = C (N 2 2) * X 2 := by
  simp [linearForm, Fin.sum_univ_three, h0, h1]

theorem X2_mul_smul_substitute {N : Matrix (Fin 3) (Fin 3) ℂ} {d : ℂ} (c : ℂ)
    (h0 : N 2 0 = 0) (h1 : N 2 1 = 0) (h2 : d * N 2 2 = 1) (F : Poly) :
    (X 2 : Poly) * (c • substitute N F) = d • (c • substitute N ((X 2 : Poly) * F)) := by
  have h : (C d * C (N 2 2) : Poly) = 1 := by rw [← C_mul, h2, C_1]
  rw [map_mul, substitute_X, linearForm_two h0 h1]
  simp only [smul_eq_C_mul]
  linear_combination (-(X 2 * C c * substitute N F)) * h

theorem mapInv_two_zero {g : RealGL3} (hg : InPlaneParabolic g) :
    ((GeneralLinearGroup.map (algebraMap ℝ ℂ) g)⁻¹ : GL3).val 2 0 = 0 := by
  exact (congrArg (algebraMap ℝ ℂ) (inPlane_inv hg).1).trans (map_zero _)

theorem mapInv_two_one {g : RealGL3} (hg : InPlaneParabolic g) :
    ((GeneralLinearGroup.map (algebraMap ℝ ℂ) g)⁻¹ : GL3).val 2 1 = 0 := by
  exact (congrArg (algebraMap ℝ ℂ) (inPlane_inv hg).2).trans (map_zero _)

theorem mapInv_two_two {g : RealGL3} (hg : InPlaneParabolic g) :
    algebraMap ℝ ℂ (g.val 2 2) * ((GeneralLinearGroup.map (algebraMap ℝ ℂ) g)⁻¹ : GL3).val 2 2
      = 1 := by
  have h := corner_mul_inv hg
  have h2 : ((GeneralLinearGroup.map (algebraMap ℝ ℂ) g)⁻¹ : GL3).val 2 2 =
      algebraMap ℝ ℂ (g.inv 2 2) := rfl
  rw [h2, ← map_mul, h, map_one]

/-- Multiplication by `x₂` commutes with `ρ(g)` up to the corner `d_g`, for `g` in the plane
parabolic. -/
theorem X2_mul_fullCoefficientComponent (χ : RankOneCharacter) {g : RealGL3}
    (hg : InPlaneParabolic g) (F : Poly) :
    (X 2 : Poly) * fullCoefficientComponent χ g F =
      algebraMap ℝ ℂ (g.val 2 2) • fullCoefficientComponent χ g ((X 2 : Poly) * F) := by
  rw [fullCoefficientComponent_apply, fullCoefficientComponent_apply]
  exact X2_mul_smul_substitute _ (mapInv_two_zero hg) (mapInv_two_one hg) (mapInv_two_two hg) F

/-! ## Unipotent substitutions fix `x₂` -/

theorem unipInv_val (s t : ℂ) :
    ((planeUnipotent s t)⁻¹ : GL3).val = !![1, 0, -s; 0, 1, -t; 0, 0, 1] := rfl

theorem substitute_unip_X0 (s t : ℂ) :
    substitute ((planeUnipotent s t)⁻¹ : GL3) (X 0) = X 0 - C s * X 2 := by
  rw [substitute_X, linearForm, unipInv_val, Fin.sum_univ_three]
  show C (1 : ℂ) * X 0 + C (0 : ℂ) * X 1 + C (-s) * X 2 = _
  simp only [map_one, map_zero, map_neg]
  ring

theorem substitute_unip_X1 (s t : ℂ) :
    substitute ((planeUnipotent s t)⁻¹ : GL3) (X 1) = X 1 - C t * X 2 := by
  rw [substitute_X, linearForm, unipInv_val, Fin.sum_univ_three]
  show C (0 : ℂ) * X 0 + C (1 : ℂ) * X 1 + C (-t) * X 2 = _
  simp only [map_one, map_zero, map_neg]
  ring

theorem substitute_unip_X2 (s t : ℂ) :
    substitute ((planeUnipotent s t)⁻¹ : GL3) (X 2) = X 2 := by
  rw [substitute_X, linearForm, unipInv_val, Fin.sum_univ_three]
  show C (0 : ℂ) * X 0 + C (0 : ℂ) * X 1 + C (1 : ℂ) * X 2 = _
  simp only [map_one, map_zero]
  ring

theorem unip_sub_mem (s t : ℂ) (F : Poly) :
    substitute ((planeUnipotent s t)⁻¹ : GL3) F - F ∈ Ideal.span {(X 2 : Poly)} := by
  have h0 : substitute ((planeUnipotent s t)⁻¹ : GL3) (X 0) - X 0 ∈ Ideal.span {(X 2 : Poly)} := by
    rw [Ideal.mem_span_singleton, substitute_unip_X0]
    exact Dvd.intro (-C s) (by ring)
  have h1 : substitute ((planeUnipotent s t)⁻¹ : GL3) (X 1) - X 1 ∈ Ideal.span {(X 2 : Poly)} := by
    rw [Ideal.mem_span_singleton, substitute_unip_X1]
    exact Dvd.intro (-C t) (by ring)
  have h2 : substitute ((planeUnipotent s t)⁻¹ : GL3) (X 2) - X 2 ∈ Ideal.span {(X 2 : Poly)} := by
    rw [substitute_unip_X2, sub_self]
    exact Ideal.zero_mem _
  have hX : ∀ i : Fin 3,
      substitute ((planeUnipotent s t)⁻¹ : GL3) (X i) - X i ∈ Ideal.span {(X 2 : Poly)} := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  induction F using MvPolynomial.induction_on with
  | C a =>
    have : substitute ((planeUnipotent s t)⁻¹ : GL3) (C a) = C a := by simp [substitute]
    rw [this, sub_self]
    exact Ideal.zero_mem _
  | add p q hp hq =>
    have : substitute ((planeUnipotent s t)⁻¹ : GL3) (p + q) - (p + q) =
        (substitute ((planeUnipotent s t)⁻¹ : GL3) p - p) +
          (substitute ((planeUnipotent s t)⁻¹ : GL3) q - q) := by
      rw [map_add]; ring
    rw [this]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    have : substitute ((planeUnipotent s t)⁻¹ : GL3) (p * X i) - p * X i =
        (substitute ((planeUnipotent s t)⁻¹ : GL3) p - p) *
            substitute ((planeUnipotent s t)⁻¹ : GL3) (X i) +
          p * (substitute ((planeUnipotent s t)⁻¹ : GL3) (X i) - X i) := by
      rw [map_mul]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ (hX i))

/-! ## Homogeneity of an exact quotient by `x₂` -/

theorem isHomogeneous_of_X_mul {n : ℕ} {R F : Poly} (h : (X 2 : Poly) * R = F)
    (hF : F.IsHomogeneous (n + 1)) : R.IsHomogeneous n := by
  classical
  intro d hd
  have h1 : ((X 2 : Poly) * R).coeff (d + Finsupp.single 2 1) ≠ 0 := by
    rw [coeff_X_mul']
    have hmem : (2 : Fin 3) ∈ (d + Finsupp.single 2 1).support := by
      rw [Finsupp.mem_support_iff]
      simp
    rw [ite_eq_left hmem, add_tsub_cancel_right]
    exact hd
  rw [h] at h1
  have h2 := hF h1
  rw [map_add] at h2
  have h3 : Finsupp.weight (1 : Fin 3 → ℕ) (Finsupp.single (2 : Fin 3) 1) = 1 := by
    simp [Finsupp.weight_single]
  omega

/-! ## The embedding of binary forms -/

/-- The embedding `ℂ[x₀, x₁] → ℂ[x₀, x₁, x₂]` of binary forms of degree `k`. -/
def binaryEmbed (k : ℕ) : Binary.HomogeneousPoly k →ₗ[ℂ] Poly :=
  (rename (Fin.castSucc : Fin 2 → Fin 3) : Binary.Poly →ₐ[ℂ] Poly).toLinearMap ∘ₗ
    Submodule.subtype _

theorem binaryEmbed_apply (k : ℕ) (Q : Binary.HomogeneousPoly k) :
    binaryEmbed k Q = rename (Fin.castSucc : Fin 2 → Fin 3) (Q : Binary.Poly) := rfl

theorem binaryEmbed_isHomogeneous (k : ℕ) (Q : Binary.HomogeneousPoly k) :
    (binaryEmbed k Q).IsHomogeneous k := by
  rw [binaryEmbed_apply]
  exact IsHomogeneous.rename_isHomogeneous (f := (Fin.castSucc : Fin 2 → Fin 3))
    ((MvPolynomial.mem_homogeneousSubmodule k _).mp Q.2)

/-! ## The Levi action `⋆` on binary forms -/

/-- The action `p ⋆ Q = χ(p) det(A_p)⁻¹ Q(A_p⁻¹ x)` of the plane parabolic on binary forms, through
its top-left block. -/
def leviStar (χ : RankOneCharacter) (k : ℕ) :
    Representation ℂ (planeParabolic ℝ) (Binary.HomogeneousPoly k) where
  toFun p := componentCharacter χ p.1 •
    Binary.homogeneousAction k (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock p))
  map_one' := by
    have h : leviBlock (1 : planeParabolic ℝ) = 1 := leviBlockHom.map_one
    simp [h]
  map_mul' p q := by
    have h : leviBlock (p * q) = leviBlock p * leviBlock q := leviBlockHom.map_mul p q
    apply LinearMap.ext
    intro v
    change componentCharacter χ (p * q).1 •
        Binary.homogeneousAction k (-1)
          (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock (p * q))) v =
      componentCharacter χ p.1 •
        Binary.homogeneousAction k (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock p))
          (componentCharacter χ q.1 •
            Binary.homogeneousAction k (-1)
              (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock q)) v)
    simp only [h, Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_smul, smul_smul]

theorem leviStar_one (χ : RankOneCharacter) (k : ℕ) : leviStar χ k 1 = 1 :=
  map_one (leviStar χ k)

theorem leviStar_mul (χ : RankOneCharacter) (k : ℕ) (p q : planeParabolic ℝ) :
    leviStar χ k (p * q) = leviStar χ k p * leviStar χ k q :=
  map_mul (leviStar χ k) p q

theorem leviStar_mul_apply (χ : RankOneCharacter) (k : ℕ) (p q : planeParabolic ℝ)
    (Q : Binary.HomogeneousPoly k) :
    leviStar χ k (p * q) Q = leviStar χ k p (leviStar χ k q Q) := by
  rw [leviStar_mul, Module.End.mul_apply]

theorem leviStar_one_apply (χ : RankOneCharacter) (k : ℕ) (Q : Binary.HomogeneousPoly k) :
    leviStar χ k 1 Q = Q := by
  rw [leviStar_one, Module.End.one_apply]

theorem coe_leviStar (χ : RankOneCharacter) (k : ℕ) (p : planeParabolic ℝ)
    (Q : Binary.HomogeneousPoly k) :
    ((leviStar χ k p Q : Binary.HomogeneousPoly k) : Binary.Poly) =
      componentCharacter χ p.1 •
        Binary.action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock p))
          (Q : Binary.Poly) := rfl

theorem binary_determinantCharacter_neg_one (A : Binary.GL2) :
    Binary.determinantCharacter (-1) A = ((GeneralLinearGroup.det A : ℂˣ) : ℂ)⁻¹ := by
  exact zpow_neg_one _

theorem binary_action_neg_one (A : Binary.GL2) (F : Binary.Poly) :
    Binary.action (-1) A F =
      ((GeneralLinearGroup.det A : ℂˣ) : ℂ)⁻¹ • Binary.substitute A.inv F := by
  rw [Binary.action_apply, binary_determinantCharacter_neg_one]; rfl

/-- Renaming commutes with block-diagonal substitution. -/
theorem rename_binary_substitute (A : Binary.GL2) (d : ℂˣ) (F : Binary.Poly) :
    rename (Fin.castSucc : Fin 2 → Fin 3) (Binary.substitute A.inv F) =
      substitute (planeLevi A d).inv (rename (Fin.castSucc : Fin 2 → Fin 3) F) := by
  have key : (rename (Fin.castSucc : Fin 2 → Fin 3) : Binary.Poly →ₐ[ℂ] Poly).comp
      (Binary.substitute A.inv) =
      (substitute (planeLevi A d).inv).comp
        (rename (Fin.castSucc : Fin 2 → Fin 3) : Binary.Poly →ₐ[ℂ] Poly) := by
    have h0 : rename (Fin.castSucc : Fin 2 → Fin 3) (Binary.substitute A.inv (X 0)) =
        substitute (planeLevi A d).inv (rename (Fin.castSucc : Fin 2 → Fin 3) (X 0)) := by
      rw [Binary.substitute_X, rename_X, substitute_X]
      simp only [Binary.linearForm, linearForm, Fin.sum_univ_two, Fin.sum_univ_three, map_add,
        map_mul, rename_C, rename_X]
      show C (A.inv 0 0) * X 0 + C (A.inv 0 1) * X 1 =
        C (A.inv 0 0) * X 0 + C (A.inv 0 1) * X 1 + C (0 : ℂ) * X 2
      rw [map_zero, zero_mul, add_zero]
    have h1 : rename (Fin.castSucc : Fin 2 → Fin 3) (Binary.substitute A.inv (X 1)) =
        substitute (planeLevi A d).inv (rename (Fin.castSucc : Fin 2 → Fin 3) (X 1)) := by
      rw [Binary.substitute_X, rename_X, substitute_X]
      simp only [Binary.linearForm, linearForm, Fin.sum_univ_two, Fin.sum_univ_three, map_add,
        map_mul, rename_C, rename_X]
      show C (A.inv 1 0) * X 0 + C (A.inv 1 1) * X 1 =
        C (A.inv 1 0) * X 0 + C (A.inv 1 1) * X 1 + C (0 : ℂ) * X 2
      rw [map_zero, zero_mul, add_zero]
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · exact h0
    · exact h1
  exact AlgHom.congr_fun key F

/-- The defining property of `⋆`: `ι (p ⋆ Q) = d_p • ρ(m(p)) (ι Q)`. -/
theorem binaryEmbed_leviStar (χ : RankOneCharacter) (k : ℕ) (p : planeParabolic ℝ)
    (Q : Binary.HomogeneousPoly k) :
    binaryEmbed k (leviStar χ k p Q) =
      algebraMap ℝ ℂ (p.1.val 2 2) •
        fullCoefficientComponent χ (planeLeviPart p) (binaryEmbed k Q) := by
  have hp : InPlaneParabolic p.1 := p.2
  have ha : algebraMap ℝ ℂ (p.1.val 2 2) ≠ 0 := rc_algebraMap_ne_zero (corner_ne_zero hp)
  have he : ((toComplexUnit (cornerHom p) : ℂˣ) : ℂ) = algebraMap ℝ ℂ (p.1.val 2 2) := rfl
  simp only [binaryEmbed_apply]
  rw [coe_leviStar, binary_action_neg_one, map_smul, map_smul,
    rename_binary_substitute _ (toComplexUnit (cornerHom p)),
    fullCoefficientComponent_planeLeviPart, he]
  simp only [smul_smul]
  congr 1
  exact rc_scalar_aux ha _ _

/-! ## The radical -/

theorem rho_planeUnipotentPart (χ : RankOneCharacter) (p : planeParabolic ℝ) (F : Poly) :
    fullCoefficientComponent χ (planeUnipotentPart p) F =
      substitute ((planeUnipotent (algebraMap ℝ ℂ (p.1.val 0 2 / p.1.val 2 2))
        (algebraMap ℝ ℂ (p.1.val 1 2 / p.1.val 2 2)))⁻¹ : GL3) F :=
  fullCoefficientComponent_planeUnipotent χ _ _ F

theorem exists_radical_poly (χ : RankOneCharacter) (p : planeParabolic ℝ) (F : Poly) :
    ∃ R : Poly, (X 2 : Poly) * R = fullCoefficientComponent χ (planeUnipotentPart p) F - F := by
  have h := unip_sub_mem (algebraMap ℝ ℂ (p.1.val 0 2 / p.1.val 2 2))
    (algebraMap ℝ ℂ (p.1.val 1 2 / p.1.val 2 2)) F
  rw [← rho_planeUnipotentPart χ p F] at h
  obtain ⟨R, hR⟩ := Ideal.mem_span_singleton.mp h
  exact ⟨R, hR.symm⟩

theorem exists_planeRadical (χ : RankOneCharacter) (n : ℕ) (p : planeParabolic ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    ∃ R : HomogeneousPoly n, (X 2 : Poly) * (R : Poly) =
      fullCoefficientComponent χ (planeUnipotentPart p) (binaryEmbed (n + 1) Q) -
        binaryEmbed (n + 1) Q := by
  obtain ⟨R, hR⟩ := exists_radical_poly χ p (binaryEmbed (n + 1) Q)
  refine ⟨⟨R, ?_⟩, hR⟩
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact isHomogeneous_of_X_mul hR
    ((fullCoefficientComponent_homogeneous χ _ (binaryEmbed_isHomogeneous (n + 1) Q)).sub
      (binaryEmbed_isHomogeneous (n + 1) Q))

/-- The chosen quotient by `x₂`, before linearity is established. -/
def radicalAt (χ : RankOneCharacter) (n : ℕ) (p : planeParabolic ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) : HomogeneousPoly n :=
  Classical.choose (exists_planeRadical χ n p Q)

theorem X2_mul_radicalAt (χ : RankOneCharacter) (n : ℕ) (p : planeParabolic ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    (X 2 : Poly) * (radicalAt χ n p Q : Poly) =
      fullCoefficientComponent χ (planeUnipotentPart p) (binaryEmbed (n + 1) Q) -
        binaryEmbed (n + 1) Q :=
  Classical.choose_spec (exists_planeRadical χ n p Q)

/-- The radical `R(p) Q`: the exact quotient by `x₂` of `ρ(u(p)) (ι Q) - ι Q`, a homogeneous
polynomial of degree `n`. -/
def planeRadical (n : ℕ) (χ : RankOneCharacter) (p : planeParabolic ℝ) :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n where
  toFun Q := radicalAt χ n p Q
  map_add' Q₁ Q₂ := by
    show radicalAt χ n p (Q₁ + Q₂) = radicalAt χ n p Q₁ + radicalAt χ n p Q₂
    apply Subtype.ext
    apply mul_left_cancel₀ (X2_ne_zero)
    have h1 := X2_mul_radicalAt χ n p (Q₁ + Q₂)
    have h2 := X2_mul_radicalAt χ n p Q₁
    have h3 := X2_mul_radicalAt χ n p Q₂
    rw [h1, Submodule.coe_add, mul_add, h2, h3]
    simp only [map_add]
    ring
  map_smul' c Q := by
    show radicalAt χ n p (c • Q) = c • radicalAt χ n p Q
    apply Subtype.ext
    apply mul_left_cancel₀ (X2_ne_zero)
    have h1 := X2_mul_radicalAt χ n p (c • Q)
    have h2 := X2_mul_radicalAt χ n p Q
    rw [h1, Submodule.coe_smul, mul_smul_comm, h2]
    simp only [map_smul, smul_sub]

/-- `x₂ · R(p) Q = ρ(u(p)) (ι Q) - ι Q`, where `u(p) = p · m(p)⁻¹` is the unipotent part. -/
theorem X2_mul_planeRadical (n : ℕ) (χ : RankOneCharacter) (p : planeParabolic ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    (X 2 : Poly) * (planeRadical n χ p Q : Poly) =
      fullCoefficientComponent χ (planeUnipotentPart p) (binaryEmbed (n + 1) Q) -
        binaryEmbed (n + 1) Q :=
  X2_mul_radicalAt χ n p Q

/-- The radical vanishes on the Levi subgroup. -/
theorem planeRadical_levi_eq_zero (n : ℕ) (χ : RankOneCharacter)
    (A : GeneralLinearGroup (Fin 2) ℝ) (d : ℝˣ) :
    planeRadical n χ ⟨planeLevi A d, planeLevi_mem A d⟩ = 0 := by
  apply LinearMap.ext
  intro Q
  apply Subtype.ext
  simp only [LinearMap.zero_apply, Submodule.coe_zero]
  apply mul_left_cancel₀ (X2_ne_zero)
  rw [X2_mul_planeRadical, planeUnipotentPart_levi]
  simp

/-- For `u = planeUnipotent s t`: `x₂ · R(u) Q = ρ(u) (ι Q) - ι Q`, i.e.
`R(u) Q = (ρ(u) (ι Q) - ι Q) / x₂ = ((ι Q)(u⁻¹ x) - (ι Q)(x)) / x₂`. -/
theorem X2_mul_planeRadical_unipotent (n : ℕ) (χ : RankOneCharacter) (s t : ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    (X 2 : Poly) *
        (planeRadical n χ ⟨planeUnipotent s t, planeUnipotent_mem s t⟩ Q : Poly) =
      fullCoefficientComponent χ (planeUnipotent s t) (binaryEmbed (n + 1) Q) -
        binaryEmbed (n + 1) Q := by
  rw [X2_mul_planeRadical, planeUnipotentPart_unipotent]

theorem coe_realCoefficientComponent (n : ℕ) (χ : RankOneCharacter) (g : RealGL3)
    (v : HomogeneousPoly n) :
    ((realCoefficientComponent n χ g v : HomogeneousPoly n) : Poly) =
      fullCoefficientComponent χ g (v : Poly) := rfl

/-- The cocycle identity for the radical, for the conjugation action
`(p · L)(Q) = ρ(p) (L (p⁻¹ ⋆ Q))` on `Hom(Q, V)`. -/
theorem planeRadical_mul (n : ℕ) (χ : RankOneCharacter) (p₁ p₂ : planeParabolic ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    planeRadical n χ (p₁ * p₂) Q =
      planeRadical n χ p₁ Q +
        realCoefficientComponent n χ p₁.1
          (planeRadical n χ p₂ (leviStar χ (n + 1) p₁⁻¹ Q)) := by
  have hp₁ : InPlaneParabolic p₁.1 := p₁.2
  have ha : algebraMap ℝ ℂ (p₁.1.val 2 2) ≠ 0 := rc_algebraMap_ne_zero (corner_ne_zero hp₁)
  apply Subtype.ext
  apply mul_left_cancel₀ (X2_ne_zero)
  have hA := X2_mul_planeRadical n χ (p₁ * p₂) Q
  have hB := X2_mul_planeRadical n χ p₁ Q
  have hD := X2_mul_planeRadical n χ p₂ (leviStar χ (n + 1) p₁⁻¹ Q)
  have hC := X2_mul_fullCoefficientComponent χ hp₁
    (planeRadical n χ p₂ (leviStar χ (n + 1) p₁⁻¹ Q) : Poly)
  have hE : binaryEmbed (n + 1) (leviStar χ (n + 1) p₁⁻¹ Q) =
      (algebraMap ℝ ℂ (p₁.1.val 2 2))⁻¹ •
        fullCoefficientComponent χ (planeLeviPart p₁)⁻¹ (binaryEmbed (n + 1) Q) := by
    rw [binaryEmbed_leviStar, corner_inv, planeLeviPart_inv, map_inv₀]
  have e1 : fullCoefficientComponent χ (planeUnipotentPart (p₁ * p₂)) (binaryEmbed (n + 1) Q) =
      fullCoefficientComponent χ p₁.1 (fullCoefficientComponent χ (planeUnipotentPart p₂)
        (fullCoefficientComponent χ (planeLeviPart p₁)⁻¹ (binaryEmbed (n + 1) Q))) := by
    rw [planeUnipotentPart_mul, fullCoefficientComponent_mul, fullCoefficientComponent_mul]
  have e2 : fullCoefficientComponent χ (planeUnipotentPart p₁) (binaryEmbed (n + 1) Q) =
      fullCoefficientComponent χ p₁.1
        (fullCoefficientComponent χ (planeLeviPart p₁)⁻¹ (binaryEmbed (n + 1) Q)) := by
    rw [planeUnipotentPart_eq, fullCoefficientComponent_mul]
  rw [Submodule.coe_add, coe_realCoefficientComponent, mul_add, hA, hB, hC, hD, hE]
  simp only [map_sub, map_smul]
  rw [smul_sub, smul_inv_smul₀ ha, smul_inv_smul₀ ha, e1, e2]
  ring

end TernaryPeriodPolynomials.SourceConstruction

end
