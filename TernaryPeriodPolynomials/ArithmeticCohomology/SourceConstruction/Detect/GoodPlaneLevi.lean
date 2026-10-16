module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Source
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge2
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.FinAvgLeviInvariance

@[expose] public section


/-!
# The Levi cocycle at the good plane: relation to the level-one period cocycle

For Levi cocycle data `E` (an `O(2)`-normalized analytic Levi cocycle of a spherical cuspidal
representation) and `δ = diag(1, 3)` (real image `gpDelta` of `del`), the potentials of the plane
source at the good-plane point are built from the values `E.α g (atInfinity δ)`.  This file proves the
algebra relating them to the level-one period cocycle `m ↦ E.α m 1`:

* `alpha_atInfinity_int`: a spherical Levi value does not see a real integral translate,
  `E.α h (atInfinity A) = E.α h 1` for `A ∈ GL₂(ℤ)` (automorphy and `GL₂(ẑ)`-invariance);
* `gp_levi_relation`: for `m ∈ Γ₁'(3)`, with `κ(m) = δ⁻¹ m δ`,
  `Φ (N • E.α κ(m) (atInfinity δ)) = E.α m 1 + (ρ m w₀ - w₀)`,  `w₀ = E.α δ 1`,
  where `Φ = Sym^{n+1}(δ)` and `N = |det δ|^{(n+3)/2}`.  This is the cocycle law for the products
  `δ κ(m) = m δ`; it exhibits the Levi potential at the good plane as the restriction of the
  level-one period cocycle to `Γ₁'(3)` up to the coboundary of `w₀`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame (del kap integralEmbed_kap)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2 (Phi)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed)
open TernaryPeriodPolynomials.AnalyticClasses
  (rationalAdele_intMatrix realLeviMatrix finiteLeviMatrix map_integralEmbedding_intCast)

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The real image of a rational matrix. -/
local notation "ratReal" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

/-! ## Functoriality of the base change of `GL` -/

theorem gp_map_map {k : ℕ} (A : GeneralLinearGroup (Fin k) ℚ) :
    GeneralLinearGroup.map (algebraMap ℝ ℂ) (GeneralLinearGroup.map (algebraMap ℚ ℝ) A) =
      GeneralLinearGroup.map (algebraMap ℚ ℂ) A := by
  have e : ∀ q : ℚ, algebraMap ℝ ℂ (algebraMap ℚ ℝ q) = algebraMap ℚ ℂ q := fun q =>
    congrArg (fun f : ℚ →+* ℂ => f q)
      (RingHom.ext_rat ((algebraMap ℝ ℂ).comp (algebraMap ℚ ℝ)) (algebraMap ℚ ℂ))
  apply Units.ext
  ext i j
  exact e (A.val i j)

theorem gp_map_map_int {k : ℕ} (A : GeneralLinearGroup (Fin k) ℤ) :
    GeneralLinearGroup.map (algebraMap ℝ ℂ) (GeneralLinearGroup.map (Int.castRingHom ℝ) A) =
      GeneralLinearGroup.map (Int.castRingHom ℂ) A := by
  have e : ∀ z : ℤ, algebraMap ℝ ℂ (Int.castRingHom ℝ z) = Int.castRingHom ℂ z := fun z =>
    congrArg (fun f : ℤ →+* ℂ => f z)
      (RingHom.ext_int ((algebraMap ℝ ℂ).comp (Int.castRingHom ℝ)) (Int.castRingHom ℂ))
  apply Units.ext
  ext i j
  exact e (A.val i j)

theorem gp_ratReal_integralEmbed (g : GeneralLinearGroup (Fin 2) ℤ) :
    ratReal (integralEmbed g) = GeneralLinearGroup.map (Int.castRingHom ℝ) g := by
  have e : ∀ z : ℤ, algebraMap ℚ ℝ (Int.castRingHom ℚ z) = Int.castRingHom ℝ z := fun z =>
    congrArg (fun f : ℤ →+* ℝ => f z)
      (RingHom.ext_int ((algebraMap ℚ ℝ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℝ))
  apply Units.ext
  ext i j
  exact e (g.val i j)

/-! ## Determinants of integral matrices -/

theorem gp_det_units (g : GeneralLinearGroup (Fin 2) ℤ) :
    (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1 ∨ (g : Matrix (Fin 2) (Fin 2) ℤ).det = -1 := by
  rcases Int.units_eq_one_or (GeneralLinearGroup.det g) with h | h
  · left
    have := congrArg Units.val h
    simpa [GeneralLinearGroup.val_det_apply] using this
  · right
    have := congrArg Units.val h
    simpa [GeneralLinearGroup.val_det_apply] using this

theorem gp_abs_det_int (m : GeneralLinearGroup (Fin 2) ℤ) :
    |(GeneralLinearGroup.map (Int.castRingHom ℝ) m).val.det| = 1 := by
  have h : (GeneralLinearGroup.map (Int.castRingHom ℝ) m).val.det = ((m.val.det : ℤ) : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) m.val).symm
  rcases gp_det_units m with hd | hd
  · rw [h, hd]
    simp
  · rw [h, hd]
    simp

/-- The idele norm of the determinant of a real integral matrix is `1`. -/
theorem gp_normPower_int (m : GeneralLinearGroup (Fin 2) ℤ) (z : ℂ) :
    normPower (GeneralLinearGroup.det
      (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) m))) z = 1 := by
  rw [normPower_det_atInfinity,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_realAdeleUnit]
  have hdet : ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℝ) m) : ℝˣ) : ℝ) =
      (GeneralLinearGroup.map (Int.castRingHom ℝ) m).val.det :=
    GeneralLinearGroup.val_det_apply _
  rw [hdet, gp_abs_det_int, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-! ## The matrices `δ`, `κ(m)`, `m` over the reals -/

/-- The real matrix `δ = diag(1, 3)`. -/
abbrev gpDelta : BinaryRealGL := ratReal del

/-- The real image of `κ(m) = δ⁻¹ m δ ∈ GL₂(ℤ)`. -/
abbrev gpKappa (m : binaryArithmeticLevel) : BinaryRealGL :=
  GeneralLinearGroup.map (Int.castRingHom ℝ) (kap m)

/-- The real image of `m ∈ Γ₁'(3) ⊆ GL₂(ℤ)`. -/
abbrev gpMu (m : binaryArithmeticLevel) : BinaryRealGL :=
  GeneralLinearGroup.map (Int.castRingHom ℝ) m.val

/-- The scalar `|det δ|^{(n+3)/2}` of the cocycle law at `δ`. -/
abbrev gpN (n : ℕ) : ℂ :=
  normPower (GeneralLinearGroup.det (atInfinity gpDelta)) (((n : ℂ) + 3) / 2)

theorem binaryCoefficient_gpDelta (n : ℕ) : binaryCoefficient n gpDelta = Phi n := by
  have h := congrArg (fun A => Binary.homogeneousAction (n + 1) (-1) A) (gp_map_map del)
  exact h

theorem binaryCoefficient_gpMu {n : ℕ} (m : binaryArithmeticLevel) :
    binaryCoefficient n (gpMu m) = levelRep (n + 1) (-1) m := by
  have h := congrArg (fun A => Binary.homogeneousAction (n + 1) (-1) A) (gp_map_map_int m.val)
  exact h

/-- `δ κ(m) = m δ`. -/
theorem gp_delta_comm (m : binaryArithmeticLevel) : gpDelta * gpKappa m = gpMu m * gpDelta := by
  have h := integralEmbed_kap m
  have h2 : del * integralEmbed (kap m) = integralEmbed m.val * del := by
    rw [h]
    group
  have h3 : ratReal (del * integralEmbed (kap m)) = ratReal (integralEmbed m.val * del) := by
    rw [h2]
  rw [map_mul, map_mul, gp_ratReal_integralEmbed, gp_ratReal_integralEmbed] at h3
  exact h3

/-! ## Spherical Levi values do not see real integral translates -/

section Spherical

variable {n : ℕ}

theorem realize_atInfinity_int (σ : CuspidalRepresentation) (v : σ.smooth)
    (hv : v.val ∈ sphericalSubspace σ) (A : GeneralLinearGroup (Fin 2) ℤ) :
    σ.realize v (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) A)) = σ.realize v 1 := by
  have fixed : (⟨σ.π (atFinite (finiteLeviMatrix A)) v.val, σ.smooth_stable _ _ v.property⟩ :
      σ.smooth) = v := by
    apply Subtype.ext
    change σ.π (atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) A)) v.val = v.val
    rw [← map_integralEmbedding_intCast]
    exact hv _
  have key : ∀ point : BinaryAdelicGL,
      σ.realize v (point * atFinite (finiteLeviMatrix A)) = σ.realize v point := by
    intro point
    rw [← σ.equivariant, fixed]
  have h1 := key (atInfinity (realLeviMatrix A))
  rw [← rationalAdele_intMatrix A] at h1
  have h2 := σ.leftRational (GeneralLinearGroup.map (Int.castRingHom ℚ) A) v 1
  rw [mul_one] at h2
  exact h1.symm.trans h2

/-- **A spherical Levi value does not see a real integral translate.** -/
theorem alpha_atInfinity_int {σ : CuspidalRepresentation} (E : LeviCocycleData σ n)
    (h : BinaryRealGL) (A : GeneralLinearGroup (Fin 2) ℤ) :
    E.α h (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) A)) = E.α h 1 := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  rw [← E.lift_realize ν h, ← E.lift_realize ν h]
  exact realize_atInfinity_int σ (E.lift ν h) (E.spherical ν h) A

end Spherical

/-! ## The Levi potential does not see the radical, and is the Levi cocycle on the Levi -/

section Potential

variable {n : ℕ}

/-- The real Levi element `diag(B, 1)` of the plane parabolic. -/
def gpLevi (B : BinaryRealGL) : planeParabolic ℝ := ⟨planeLevi B 1, planeLevi_mem B 1⟩

theorem gp_alpha_radical {σ : CuspidalRepresentation} (E : LeviCocycleData σ n)
    (r : RadicalLattice) (x : BinaryAdelicGL) :
    E.α (iwA (radicalUnipotent r).1) x = 0 := by
  have h := alpha_iwA_mul E (radicalUnipotent r) 1 x
  rw [mul_one] at h
  have hl : leviBlock (radicalUnipotent r) = 1 := leviBlock_planeUnipotent _ _
  rw [h, hl, alpha_iwA_one E, alpha_one E]
  simp [binaryCohomologicalAction]

theorem gp_alpha_levi {σ : CuspidalRepresentation} (E : LeviCocycleData σ n)
    (B : BinaryRealGL) (x : BinaryAdelicGL) :
    E.α (iwA (gpLevi B).1) x = E.α B x := by
  have h := alpha_iwA_mul E (gpLevi B) 1 x
  rw [mul_one] at h
  have hl : leviBlock (gpLevi B) = B := leviBlock_planeLevi B 1
  rw [h, hl, alpha_iwA_one E]
  simp [binaryCohomologicalAction]

end Potential

/-! ## The relation to the level-one period cocycle -/

section Relation

variable {n : ℕ}

/-- **The Levi cocycle at the good plane is the period cocycle on `Γ₁'(3)`**, up to the coboundary
of `w₀ = E.α δ 1`: for `m ∈ Γ₁'(3)`,
`Φ (N • E.α κ(m) (atInfinity δ)) = E.α m 1 + (ρ m w₀ - w₀)`. -/
theorem gp_levi_relation {σ : CuspidalRepresentation} (E : LeviCocycleData σ n)
    (m : binaryArithmeticLevel) :
    Phi n (gpN n • E.α (gpKappa m) (atInfinity gpDelta)) =
      E.α (gpMu m) 1 + (levelRep (n + 1) (-1) m (E.α gpDelta 1) - E.α gpDelta 1) := by
  have c1 := E.cocycle gpDelta (gpKappa m) 1
  have c2 := E.cocycle (gpMu m) gpDelta 1
  rw [gp_delta_comm m] at c1
  have e1 : binaryCohomologicalAction n gpDelta (E.α (gpKappa m)) 1 =
      Phi n (gpN n • E.α (gpKappa m) (atInfinity gpDelta)) := by
    unfold binaryCohomologicalAction
    rw [one_mul, binaryCoefficient_gpDelta, map_smul]
  have e2 : binaryCohomologicalAction n (gpMu m) (E.α gpDelta) 1 =
      levelRep (n + 1) (-1) m (E.α gpDelta 1) := by
    unfold binaryCohomologicalAction
    rw [gp_normPower_int m.val, one_smul, one_mul, alpha_atInfinity_int E gpDelta m.val,
      binaryCoefficient_gpMu]
  rw [e1] at c1
  rw [e2] at c2
  exact (eq_sub_of_add_eq' (c1.symm.trans c2)).trans (add_sub_assoc _ _ _)

end Relation

end TernaryPeriodPolynomials.SourceConstruction
