module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.CellPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerTwTangent

@[expose] public section


/-!
# The core of the sign-twisted plane source

For the odd quadratic character of conductor three the plane source is modified in
three places.  The spherical finite plane vector is replaced by the cell function `planeCell`
(`cFinC`, `bFinC`), the Levi cocycle satisfies the sign-twisted law
`α (g h) x = α g x + sgn det g • (g · α h) x` (`LeviCocycleDataTw`), and the component character is
`sgn ∘ det`, so that the transformation law of the real part acquires the factor `epsP p`, the sign
of the corner entry of the parabolic element `p`.  This file gives the twisted analogue of the
definitions and of the algebraic laws of `PlaneSourceData`, `PlaneSourceFinite`, `PlaneSourceReal`
and `PlaneSourceAlgebra`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Spectral.LevelOneNontrivial (ConductorThree)

namespace TernaryPeriodPolynomials.TwistedSource

/-- The sign-twisted `O(2)`-normalized analytic Levi cocycle of a cuspidal representation: a cocycle
for the action twisted by the sign of the determinant, with values in binary forms, vanishing on the
orthogonal group, whose coefficients are realizations of smooth spherical vectors depending
analytically on the real argument. -/
structure LeviCocycleDataTw (σ : CuspidalRepresentation) (n : ℕ) where
  α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)
  cocycle : ∀ g h x,
    α (g * h) x = α g x + signDet g • binaryCohomologicalAction n g (α h) x
  orth : ∀ k : BinaryRealGL, k.val.transpose * k.val = 1 → ∀ x, α k x = 0
  lift : (Fin 2 →₀ ℕ) → BinaryRealGL → σ.smooth
  lift_realize : ∀ μ g A, σ.realize (lift μ g) A = (α g A).val.coeff μ
  lift_smooth : ∀ μ, Smooth (fun x : Fin 1 → BinaryRealGL => (lift μ (x 0)).val)
  scalar_smooth : ∀ μ A, Smooth (fun x : Fin 1 → BinaryRealGL => (α (x 0) A).val.coeff μ)
  spherical : ∀ μ g, (lift μ g).val ∈ sphericalSubspace σ

section Defs

variable {n : ℕ}

open Classical in
/-- The `GL₂` block attached to a finite adele matrix on the cell `P_plane(𝔸_f) · K₁`: the block of
a chosen parabolic factor of `f`, and `1` at the cusp point and off the cell. -/
def bFinG (f : FiniteGL) : GeneralLinearGroup (Fin 2) FiniteAdeles :=
  if f = 1 then 1 else
    if h : InCell (planeParabolic FiniteAdeles) finiteLevel 1 f then
      planeBlockGL (Classical.choose h).1 (Classical.choose h).2
    else 1

open Classical in
/-- The finite scalar factor attached to a finite adele matrix on the cell: the plane factor of a
chosen parabolic factor of `f`, `1` at the cusp point and `0` off the cell. -/
def cFinC (D : InducingData n) (f : FiniteGL) : ℂ :=
  if f = 1 then 1 else
    if h : InCell (planeParabolic FiniteAdeles) finiteLevel 1 f then
      finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) (Classical.choose h).1 (Classical.choose h).2
    else 0

/-- The finite `GL₂` translation attached to a finite adele matrix on the cell. -/
def bFinC (f : FiniteGL) : BinaryAdelicGL := atFinite (bFinG f)

/-- The finite scalar factor attached to an adelic matrix. -/
def cFC (D : InducingData n) (g : AdelicGL) : ℂ := cFinC D (finiteGroup g)

/-- The finite `GL₂` translation attached to an adelic matrix. -/
def bFC (g : AdelicGL) : BinaryAdelicGL := bFinC (finiteGroup g)

/-- **The twisted plane source cochain**, at the `GL₂` adele `x`. -/
def planeSourceAtTw (D : InducingData n) (E : LeviCocycleDataTw D.cusp n) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (x : BinaryAdelicGL) : HomogeneousPoly n :=
  realCoefficientComponent n D.chi (realGroup g)⁻¹
    ((planeRadical n D.chi (iwP (realGroup g * y 2)) - planeRadical n D.chi (iwP (realGroup g * y 1)))
      (cFC D g • (E.α (iwA (realGroup g * y 1)) (x * bFC g) -
        E.α (iwA (realGroup g * y 0)) (x * bFC g))))

/-- **The twisted plane source cocycle.** -/
def planeSourceTw (D : InducingData n) (E : LeviCocycleDataTw D.cusp n) (y : Fin 3 → RealGL3)
    (g : AdelicGL) : HomogeneousPoly n :=
  planeSourceAtTw D E y g 1

/-- The sign of the corner entry of a real plane-parabolic element. -/
def epsP (p : planeParabolic ℝ) : ℂ := if 0 < p.1.val 2 2 then 1 else -1

end Defs

/-! ## The finite part on the cell -/

section Finite

variable {n : ℕ}

theorem cFinC_one (D : InducingData n) (_h3 : ConductorThree D.chi) : cFinC D 1 = 1 := by
  unfold cFinC
  exact ite_eq_left rfl

theorem bFinG_one : bFinG 1 = 1 := by
  unfold bFinG
  exact ite_eq_left rfl

theorem bFinC_one (D : InducingData n) (_h3 : ConductorThree D.chi) : bFinC 1 = 1 := by
  unfold bFinC
  rw [bFinG_one]
  exact ps_atFinite_one

theorem cFinC_of_cell (D : InducingData n) {f : FiniteGL} (hf : f ≠ 1)
    (h : InCell (planeParabolic FiniteAdeles) finiteLevel 1 f) :
    cFinC D f = finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) (Classical.choose h).1
      (Classical.choose h).2 := by
  unfold cFinC
  rw [ite_eq_right hf, dite_eq_left h]

theorem cFinC_of_not_cell (D : InducingData n) {f : FiniteGL} (hf : f ≠ 1)
    (h : ¬ InCell (planeParabolic FiniteAdeles) finiteLevel 1 f) : cFinC D f = 0 := by
  unfold cFinC
  rw [ite_eq_right hf, dite_eq_right h]

theorem bFinG_of_cell {f : FiniteGL} (hf : f ≠ 1)
    (h : InCell (planeParabolic FiniteAdeles) finiteLevel 1 f) :
    bFinG f = planeBlockGL (Classical.choose h).1 (Classical.choose h).2 := by
  unfold bFinG
  rw [ite_eq_right hf, dite_eq_left h]

theorem bFinG_of_not_cell {f : FiniteGL} (hf : f ≠ 1)
    (h : ¬ InCell (planeParabolic FiniteAdeles) finiteLevel 1 f) : bFinG f = 1 := by
  unfold bFinG
  rw [ite_eq_right hf, dite_eq_right h]

/-- The cell function is the scalar `cFinC` times the translation by `bFinC`, on spherical vectors. -/
theorem planeCell_eq_cFinC (D : InducingData n) (h3 : ConductorThree D.chi) (f : FiniteGL)
    {w : D.cusp.H} (hw : w ∈ sphericalSubspace D.cusp) :
    planeCell D.cusp D.chi 0 (((n : ℂ) + 3) / 2) f w = cFinC D f • D.cusp.π (bFinC f) w := by
  by_cases hf1 : f = 1
  · subst hf1
    rw [cFinC_one D h3, bFinC_one D h3, map_one, one_smul, Module.End.one_apply]
    exact planeCell_one D.cusp D.chi 0 (((n : ℂ) + 3) / 2) h3 hw
  · by_cases hcell : InCell (planeParabolic FiniteAdeles) finiteLevel 1 f
    · rw [cFinC_of_cell D hf1 hcell]
      unfold bFinC
      rw [bFinG_of_cell hf1 hcell]
      obtain ⟨k, hk, hg⟩ := Classical.choose_spec hcell
      unfold planeCell
      rw [cellMap_apply_of_eq (planeCellFixes D.cusp D.chi 0 (((n : ℂ) + 3) / 2) h3)
        (Classical.choose hcell) hk hg hw, planeFactorHom_apply]
    · rw [cFinC_of_not_cell D hf1 hcell, zero_smul]
      unfold planeCell
      rw [cellMap_eq_zero hcell, LinearMap.zero_apply]

theorem rz_cFinC (D : InducingData n) (h3 : ConductorThree D.chi) (f : FiniteGL)
    {v : D.cusp.H} (hv : v ∈ sphericalSubspace D.cusp) (hs : v ∈ D.cusp.smooth)
    (x : BinaryAdelicGL) :
    rz D.cusp (planeCell D.cusp D.chi 0 (((n : ℂ) + 3) / 2) f v) x =
      cFinC D f * rz D.cusp v (x * bFinC f) := by
  rw [planeCell_eq_cFinC D h3 f hv, rz_smul (D.cusp.smooth_stable _ _ hs), rz_pi hs]

theorem cFC_mul_atInfinity (D : InducingData n) (g : AdelicGL) (z : RealGL3) :
    cFC D (g * atInfinity z) = cFC D g := by
  unfold cFC
  rw [finiteGroup_mul_atInfinity]

theorem bFC_mul_atInfinity (g : AdelicGL) (z : RealGL3) :
    bFC (g * atInfinity z) = bFC g := by
  unfold bFC
  rw [finiteGroup_mul_atInfinity]

theorem bFinC_comm_atInfinity (f : FiniteGL) (z : BinaryRealGL) :
    bFinC f * atInfinity z = atInfinity z * bFinC f :=
  atFinite_mul_atInfinity_comm _ _

theorem rz_liftTw {σ : CuspidalRepresentation} (E : LeviCocycleDataTw σ n) (ν : Fin 2 →₀ ℕ)
    (h : BinaryRealGL) (x : BinaryAdelicGL) :
    rz σ (E.lift ν h).val x = (E.α h x).val.coeff ν := by
  rw [rz_of_mem (E.lift ν h).property]
  exact E.lift_realize ν h x

theorem twist_coeff_cell (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h3 : ConductorThree D.chi) (f : FiniteGL) (h : BinaryRealGL) (x : BinaryAdelicGL)
    (ν : Fin 2 →₀ ℕ) :
    cFinC D f * (E.α h (x * bFinC f)).val.coeff ν =
      rz D.cusp (planeCell D.cusp D.chi 0 (((n : ℂ) + 3) / 2) f (E.lift ν h).val) x := by
  rw [rz_cFinC D h3 f (E.spherical ν h) (E.lift ν h).property, rz_liftTw]

/-- **Left equivariance of the finite twist** under the finite plane parabolic. -/
theorem twist_left_cell (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h3 : ConductorThree D.chi) (f f' fp : FiniteGL) (hfp : fp ∈ planeParabolic FiniteAdeles)
    (hf' : f' = fp * f) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFinC D f' • E.α h (x * bFinC f') =
      finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) fp hfp •
        (cFinC D f • E.α h (x * atFinite (planeBlockGL fp hfp) * bFinC f)) := by
  subst hf'
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  have hv : (E.lift ν h).val ∈ D.cusp.smooth := (E.lift ν h).property
  have hsph := E.spherical ν h
  have hvf := planeCell_smooth D.cusp D.chi 0 (((n : ℂ) + 3) / 2) h3 hsph hv f
  have e1 := twist_coeff_cell D E h3 (fp * f) h x ν
  have e2 := twist_coeff_cell D E h3 f h (x * atFinite (planeBlockGL fp hfp)) ν
  have e3 : rz D.cusp (planeCell D.cusp D.chi 0 (((n : ℂ) + 3) / 2) (fp * f) (E.lift ν h).val)
        x =
      finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) fp hfp *
        rz D.cusp (planeCell D.cusp D.chi 0 (((n : ℂ) + 3) / 2) f (E.lift ν h).val)
          (x * atFinite (planeBlockGL fp hfp)) := by
    rw [planeCell_mul D.cusp D.chi 0 (((n : ℂ) + 3) / 2) h3 hsph hfp f,
      rz_smul (D.cusp.smooth_stable _ _ hvf), rz_pi hvf]
  rw [e1, e2, e3]

/-- **Right invariance of the finite twist** under the finite level. -/
theorem twist_level_cell (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h3 : ConductorThree D.chi) (f : FiniteGL) (k : finiteLevel) (h : BinaryRealGL)
    (x : BinaryAdelicGL) :
    cFinC D (f * k.val) • E.α h (x * bFinC (f * k.val)) = cFinC D f • E.α h (x * bFinC f) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [twist_coeff_cell D E h3 (f * k.val) h x ν, twist_coeff_cell D E h3 f h x ν,
    planeCell_level D.cusp D.chi 0 (((n : ℂ) + 3) / 2) h3 (E.spherical ν h) f k]

end Finite

/-! ## The sign of the component character -/

section Sign

theorem chi_real_sign (χ : RankOneCharacter) (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (t : ℝˣ) :
    χ.toMonoidHom (realAdeleUnit t) = if 0 < t.val then 1 else -1 := by
  by_cases hpos : 0 < t.val
  · rw [ite_eq_left hpos]
    exact χ.positiveReal t hpos
  · have hneg : t.val < 0 := lt_of_le_of_ne (not_lt.mp hpos) t.ne_zero
    have hdec : t = (-1) * (-t) := by rw [neg_mul, one_mul, neg_neg]
    have hpos' : 0 < (-t).val := by
      rw [Units.val_neg]
      exact neg_pos.mpr hneg
    have hmul := map_mul realUnitHom (-1 : ℝˣ) (-t)
    rw [← hdec] at hmul
    have hmul' : realAdeleUnit t = realAdeleUnit (-1) * realAdeleUnit (-t) := hmul
    rw [ite_eq_right hpos, hmul', map_mul, hodd, χ.positiveReal _ hpos', mul_one]

/-- For an odd character the component character is the sign of the determinant. -/
theorem componentCharacter_eq_sign {n : ℕ} (D : InducingData n)
    (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (g : RealGL3) :
    componentCharacter D.chi g = if 0 < (GeneralLinearGroup.det g).val then 1 else -1 :=
  chi_real_sign D.chi hodd (GeneralLinearGroup.det g)

theorem sign_det_inv (g : RealGL3) :
    (if 0 < (GeneralLinearGroup.det g⁻¹).val then (1 : ℂ) else -1) =
      if 0 < (GeneralLinearGroup.det g).val then 1 else -1 := by
  have hiff : 0 < (GeneralLinearGroup.det g⁻¹).val ↔ 0 < (GeneralLinearGroup.det g).val := by
    rw [_root_.map_inv, Units.val_inv_eq_inv_val, inv_pos]
  by_cases h : 0 < (GeneralLinearGroup.det g).val
  · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mp h'))]

/-- The determinant of a plane-parabolic element is the determinant of its block times its corner. -/
theorem det_leviBlock_mul_corner (p : planeParabolic ℝ) :
    (GeneralLinearGroup.det p.1).val =
      (GeneralLinearGroup.det (leviBlock p)).val * p.1.val 2 2 := by
  have h20 : p.1.val 2 0 = 0 := p.2.1
  have h21 : p.1.val 2 1 = 0 := p.2.2
  change p.1.val.det = (blockOf p.1.val).det * p.1.val 2 2
  rw [Matrix.det_fin_three, blockOf, Matrix.det_fin_two_of, h20, h21]
  ring

/-- The sign of the determinant of `p` is the sign of the determinant of its block times `epsP p`. -/
theorem sign_det_plane (p : planeParabolic ℝ) :
    (if 0 < (GeneralLinearGroup.det p.1).val then (1 : ℂ) else -1) =
      signDet (leviBlock p) * epsP p := by
  have hc : p.1.val 2 2 ≠ 0 := by
    intro h
    apply (GeneralLinearGroup.det p.1).ne_zero
    rw [det_leviBlock_mul_corner, h, mul_zero]
  have h := sign_ite_mul _ _ (GeneralLinearGroup.det (leviBlock p)).ne_zero hc
  rw [← det_leviBlock_mul_corner] at h
  exact h

end Sign

/-! ## The real law -/

section Real

variable {n : ℕ}

/-- **The twisted Levi cocycle along the Iwasawa factor.** -/
theorem alpha_iwA_mulTw {σ : CuspidalRepresentation} (E : LeviCocycleDataTw σ n)
    (p : planeParabolic ℝ) (y : RealGL3) (x : BinaryAdelicGL) :
    E.α (iwA (p.1 * y)) x =
      E.α (leviBlock p) x +
        signDet (leviBlock p) • binaryCohomologicalAction n (leviBlock p) (E.α (iwA y)) x := by
  obtain ⟨k, hk, he⟩ := leviBlock_iwP_mul p y
  have h1 : E.α (iwA (p.1 * y) * k) x = E.α (iwA (p.1 * y)) x := by
    rw [E.cocycle]
    have h0 : E.α k = fun _ => 0 := funext (E.orth k hk)
    rw [h0]
    simp [binaryCohomologicalAction]
  rw [← h1, he, E.cocycle]

theorem leviStar_binaryCoefficientTw (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = if 0 < (GeneralLinearGroup.det g).val then 1 else -1)
    (p : planeParabolic ℝ) (v : Binary.HomogeneousPoly (n + 1)) :
    leviStar χ (n + 1) p⁻¹ (binaryCoefficient n (leviBlock p) v) =
      (if 0 < (GeneralLinearGroup.det p.1).val then (1 : ℂ) else -1) • v := by
  have e : leviBlock p⁻¹ = (leviBlock p)⁻¹ := leviBlockHom.map_inv p
  have hs : componentCharacter χ (p⁻¹).1 =
      if 0 < (GeneralLinearGroup.det p.1).val then (1 : ℂ) else -1 :=
    (hc _).trans (sign_det_inv p.1)
  show componentCharacter χ (p⁻¹).1 •
      Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock p⁻¹))
        (Binary.homogeneousAction (n + 1) (-1)
          (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock p)) v) =
      (if 0 < (GeneralLinearGroup.det p.1).val then (1 : ℂ) else -1) • v
  rw [hs, e, _root_.map_inv, ← Module.End.mul_apply, ← map_mul, _root_.inv_mul_cancel,
    map_one, Module.End.one_apply]

/-- **The transformation law of the differenced potentials**, with the sign `epsP p`. -/
theorem planeCoreTw {σ : CuspidalRepresentation} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = if 0 < (GeneralLinearGroup.det g).val then 1 else -1)
    (E : LeviCocycleDataTw σ n) (p : planeParabolic ℝ) (u : Fin 3 → RealGL3) (t : BinaryAdelicGL)
    (c : ℂ) :
    (planeRadical n χ (iwP (p.1 * u 2)) - planeRadical n χ (iwP (p.1 * u 1)))
        (c • (E.α (iwA (p.1 * u 1)) t - E.α (iwA (p.1 * u 0)) t)) =
      realCoefficientComponent n χ p.1
        ((epsP p * c * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p)))
            (((n : ℂ) + 3) / 2)) •
          (planeRadical n χ (iwP (u 2)) - planeRadical n χ (iwP (u 1)))
            (E.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
              E.α (iwA (u 0)) (t * atInfinity (leviBlock p)))) := by
  have hdiff : E.α (iwA (p.1 * u 1)) t - E.α (iwA (p.1 * u 0)) t =
      (signDet (leviBlock p) *
          normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2)) •
        binaryCoefficient n (leviBlock p)
          (E.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
            E.α (iwA (u 0)) (t * atInfinity (leviBlock p))) := by
    rw [alpha_iwA_mulTw E p (u 1) t, alpha_iwA_mulTw E p (u 0) t]
    simp only [binaryCohomologicalAction, map_sub, smul_sub, mul_smul]
    abel
  have hstar : leviStar χ (n + 1) p⁻¹
      (c • (signDet (leviBlock p) *
          normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2)) •
        binaryCoefficient n (leviBlock p)
          (E.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
            E.α (iwA (u 0)) (t * atInfinity (leviBlock p)))) =
      (epsP p * c * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p)))
          (((n : ℂ) + 3) / 2)) •
        (E.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
          E.α (iwA (u 0)) (t * atInfinity (leviBlock p))) := by
    rw [map_smul, map_smul, leviStar_binaryCoefficientTw χ hc, sign_det_plane]
    simp only [smul_smul]
    congr 1
    linear_combination
      (c * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) *
        epsP p) * signDet_sq (leviBlock p)
  rw [hdiff, LinearMap.sub_apply, planeRadical_iwP_mul χ p (u 2), planeRadical_iwP_mul χ p (u 1),
    hstar]
  simp only [map_smul, map_sub, LinearMap.sub_apply, smul_sub]
  abel

/-- `planeCoreTw` for the vertices `w * y i`. -/
theorem planeCoreTw_w {σ : CuspidalRepresentation} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = if 0 < (GeneralLinearGroup.det g).val then 1 else -1)
    (E : LeviCocycleDataTw σ n) (p : planeParabolic ℝ) (w : RealGL3) (y : Fin 3 → RealGL3)
    (t : BinaryAdelicGL) (c : ℂ) :
    (planeRadical n χ (iwP (p.1 * (w * y 2))) - planeRadical n χ (iwP (p.1 * (w * y 1))))
        (c • (E.α (iwA (p.1 * (w * y 1))) t - E.α (iwA (p.1 * (w * y 0))) t)) =
      realCoefficientComponent n χ p.1
        ((epsP p * c * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p)))
            (((n : ℂ) + 3) / 2)) •
          (planeRadical n χ (iwP (w * y 2)) - planeRadical n χ (iwP (w * y 1)))
            (E.α (iwA (w * y 1)) (t * atInfinity (leviBlock p)) -
              E.α (iwA (w * y 0)) (t * atInfinity (leviBlock p)))) :=
  planeCoreTw χ hc E p (fun i => w * y i) t c

end Real

/-! ## The cup product form and the laws of the twisted plane source -/

section Laws

variable {n : ℕ}

theorem planeSourceAtTw_eq_cup (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    planeSourceAtTw D E y g a =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        (psCup (evalPair (Binary.HomogeneousPoly (n + 1)) (HomogeneousPoly n))
          (fun u : RealGL3 => cFC D g • E.α (iwA (realGroup g * u)) (a * bFC g))
          (fun u : RealGL3 => planeRadical n D.chi (iwP (realGroup g * u))) y) := by
  unfold planeSourceAtTw psCup
  rw [smul_sub]
  rfl

/-- **The cocycle condition of the twisted plane source.** -/
theorem planeSourceAtTw_cocycle (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (x : Fin 4 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    planeSourceAtTw D E ![x 1, x 2, x 3] g a - planeSourceAtTw D E ![x 0, x 2, x 3] g a +
      planeSourceAtTw D E ![x 0, x 1, x 3] g a - planeSourceAtTw D E ![x 0, x 1, x 2] g a = 0 := by
  have h := psCup_cocycle
    (evalPair (Binary.HomogeneousPoly (n + 1)) (HomogeneousPoly n))
    (fun u : RealGL3 => cFC D g • E.α (iwA (realGroup g * u)) (a * bFC g))
    (fun u : RealGL3 => planeRadical n D.chi (iwP (realGroup g * u))) x
  have h2 := congrArg (realCoefficientComponent n D.chi (realGroup g)⁻¹) h
  simp only [map_sub, map_add, _root_.map_zero] at h2
  simp only [planeSourceAtTw_eq_cup]
  exact h2

/-- **Equivariance of the twisted plane source** for the real group. -/
theorem planeSourceAtTw_equivariant (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h : RealGL3) (y : Fin 3 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    planeSourceAtTw D E (fun i => h * y i) g a =
      realCoefficientComponent n D.chi h (planeSourceAtTw D E y (g * atInfinity h) a) := by
  unfold planeSourceAtTw
  rw [realGroup_mul_atInfinity, cFC_mul_atInfinity, bFC_mul_atInfinity]
  simp only [mul_assoc]
  rw [rho_mul_inv_mul]

theorem twist_left_g_cell (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h3 : ConductorThree D.chi) (g g' : AdelicGL) (f : FiniteGL)
    (hf : f ∈ planeParabolic FiniteAdeles) (hfin : finiteGroup g' = f * finiteGroup g)
    (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFC D g' • E.α h (x * bFC g') =
      finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf •
        (cFC D g • E.α h (x * atFinite (planeBlockGL f hf) * bFC g)) :=
  twist_left_cell D E h3 (finiteGroup g) (finiteGroup g') f hf hfin h x

theorem sub_twist_cell (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h3 : ConductorThree D.chi) (g g' : AdelicGL) (f : FiniteGL)
    (hf : f ∈ planeParabolic FiniteAdeles) (hfin : finiteGroup g' = f * finiteGroup g)
    (h1 h0 : BinaryRealGL) (x : BinaryAdelicGL) :
    cFC D g' • (E.α h1 (x * bFC g') - E.α h0 (x * bFC g')) =
      (finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf * cFC D g) •
        (E.α h1 (x * atFinite (planeBlockGL f hf) * bFC g) -
          E.α h0 (x * atFinite (planeBlockGL f hf) * bFC g)) := by
  rw [smul_sub, twist_left_g_cell D E h3 g g' f hf hfin h1 x,
    twist_left_g_cell D E h3 g g' f hf hfin h0 x]
  simp only [smul_sub, smul_smul]

/-- **The general translation law of the twisted plane source.** -/
theorem planeSourceAtTw_translate (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h3 : ConductorThree D.chi) (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (g g' : AdelicGL) (p : planeParabolic ℝ) (f : FiniteGL)
    (hf : f ∈ planeParabolic FiniteAdeles) (hr : realGroup g' = p.1 * realGroup g)
    (hfin : finiteGroup g' = f * finiteGroup g) (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    planeSourceAtTw D E y g' x =
      (epsP p * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p)))
            (((n : ℂ) + 3) / 2) *
          finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf) •
        planeSourceAtTw D E y g (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p))) := by
  have hc := componentCharacter_eq_sign D hodd
  have hcomm : bFC g * atInfinity (leviBlock p) = atInfinity (leviBlock p) * bFC g :=
    bFinC_comm_atInfinity _ _
  have ht : x * atFinite (planeBlockGL f hf) * bFC g * atInfinity (leviBlock p) =
      x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p)) * bFC g := by
    simp only [mul_assoc, hcomm]
  have hu : ∀ i, p.1 * realGroup g * y i = p.1 * (realGroup g * y i) :=
    fun i => mul_assoc _ _ _
  unfold planeSourceAtTw
  rw [hr, hu 2, hu 1, hu 0, sub_twist_cell D E h3 g g' f hf hfin,
    planeCoreTw_w D.chi hc E p (realGroup g) y (x * atFinite (planeBlockGL f hf) * bFC g)
      (finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf * cFC D g), ht]
  simp only [map_smul, rho_inv_mul_rho, smul_smul]
  congr 1
  ring

/-- The twisted plane source at the identity. -/
theorem planeSourceTw_one (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h3 : ConductorThree D.chi) (y : Fin 3 → RealGL3) :
    planeSourceTw D E y 1 =
      (planeRadical n D.chi (iwP (y 2)) - planeRadical n D.chi (iwP (y 1)))
        (E.α (iwA (y 1)) 1 - E.α (iwA (y 0)) 1) := by
  unfold planeSourceTw planeSourceAtTw cFC bFC
  simp only [map_one, cFinC_one D h3, bFinC_one D h3, one_mul, inv_one, one_smul,
    Module.End.one_apply]

end Laws

end TernaryPeriodPolynomials.TwistedSource
