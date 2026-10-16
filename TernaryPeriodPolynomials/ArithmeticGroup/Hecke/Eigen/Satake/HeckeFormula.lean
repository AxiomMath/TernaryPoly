module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.Omega
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.LineTransfer

@[expose] public section


/-!
# Explicit Hecke eigenvalues of induced sections

For any choice of parabolic factorizations of the representatives of an away-from-three
correspondence, the Hecke sum of every plane (resp. line) induced section is the explicit
multiple `∑ᵣ cᵣ ω(Bᵣ)` of it, where `cᵣ` is the character/modulus weight of the Levi part and
`ω` the single-element `GL₂` Hecke scalar. These refine `plane_hecke_scalar` and
`line_hecke_scalar` (whose proofs are reused) by identifying the scalar.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.HeckeEigen

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {n : ℕ}

/-- The plane weight of a Levi part `(B, s)`. -/
def planeWeight (D : InducingData n) (s : Adelesˣ) (B : BinaryFiniteGL) : ℂ :=
  D.chi.toMonoidHom s * normPower s (-2 * inductionExponent .plane cohomologicalPoint) *
    normPower (GeneralLinearGroup.det (atFinite B)) (planeExp n) * omega D.cusp B

/-- The line weight of a Levi part `(d, A)`. -/
def lineWeight (D : InducingData n) (s : Adelesˣ) (B : BinaryFiniteGL) : ℂ :=
  D.chi.toMonoidHom s * normPower s (2 * inductionExponent .line cohomologicalPoint) *
    normPower (GeneralLinearGroup.det (atFinite B)) (lineExp n) * omega D.cusp B

/-- **Explicit plane eigenvalue.** -/
theorem plane_hecke_formula (D : InducingData n) (t : HeckeCorrespondence)
    (p : RationalGL3 → FiniteGL) (κ : RationalGL3 → finiteLevel)
    (aa ba : RationalGL3 → Adeles) (sa : RationalGL3 → Adelesˣ) (Bf : RationalGL3 → BinaryFiniteGL)
    (hp3 : ∀ r ∈ t.representatives, GeneralLinearGroup.map (finiteEvaluation placeThree) (p r) = 1)
    (hpκ : ∀ r ∈ t.representatives, rationalFinite r = p r * (κ r).val)
    (hdec : ∀ r ∈ t.representatives, atFinite (p r) =
      planeUnipotent (aa r) (ba r) * (planeLevi 1 (sa r) * planeLevi (atFinite (Bf r)) 1))
    (hBfaway : ∀ r ∈ t.representatives, Bf r ∈ awayGroup placeThree) :
    ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        (∑ r ∈ t.representatives, planeWeight D (sa r) (Bf r)) * f g := by
  classical
  let cst : RationalGL3 → ℂ := fun r => D.chi.toMonoidHom (sa r) *
    normPower (sa r) (-2 * inductionExponent .plane cohomologicalPoint) *
    normPower (GeneralLinearGroup.det (atFinite (Bf r))) (planeExp n)
  intro f hf g
  -- the vector-valued function
  let F : AdelicGL → D.cusp.H := fun h => (planeVec D f h : D.cusp.H)
  have F_level : ∀ h (k : finiteLevel), F (h * atFinite k.val) = F h := fun h k => by
    simp only [F, planeVec_level hf h k]
  have F_rep : ∀ h, ∀ r ∈ t.representatives,
      F (h * atFinite (rationalFinite r)) = F (h * atFinite (p r)) := by
    intro h r hr
    rw [hpκ r hr, ← HeckeTranslate.HeckeInvariance.atFinite_mul, ← mul_assoc, F_level]
  have F_par : ∀ h, ∀ r ∈ t.representatives,
      F (atFinite (p r) * h) = cst r • D.cusp.π (atFinite (Bf r)) (F h) := by
    intro h r hr
    simp only [F, cst]
    rw [hdec r hr, planeVec_parabolic_coe hf]
  have F_away : ∀ m ∈ awayLevel placeThree, ∀ h,
      D.cusp.π (atFinite m) (F h) = F (atFinite (planeLevi m 1) * h) := by
    intro m hm h
    simp only [F]
    rw [atFinite_planeLevi, planeVec_levi_coe hf, np_det_spherical hm.2, one_smul]
  -- decomposition of `g`
  obtain ⟨q, κg, hqk⟩ := finiteGL_parabolic_compact_factorization (finiteGroup g)
  obtain ⟨κ₃, κ', hκ⟩ := integral_split_three κg
  set y := atInfinity (realGroup g) * atFinite (finiteAtPlaceGL 3 placeThree κ₃) with hy
  have hycomm : ∀ x : FiniteGL, GeneralLinearGroup.map (finiteEvaluation placeThree) x = 1 →
      atFinite x * y = y * atFinite x := fun x hx => atFinite_commute_y _ κ₃ hx
  set X₀ := atFinite q.val * y
  have hg : g = X₀ * atFinite κ'.val := by
    conv_lhs => rw [gl3_real_finite g, hqk, hκ]
    rw [← HeckeTranslate.HeckeInvariance.atFinite_mul, ← HeckeTranslate.HeckeInvariance.atFinite_mul,
      ← mul_assoc (atInfinity (realGroup g)), ← HeckeTranslate.HeckeInvariance.atFinite_comm_atInfinity]
    simp only [X₀, y, mul_assoc]
  -- the fixed vector and its Hecke image
  set w := F y
  have hw : w ∈ fixedVectors D.cusp (awayLevelA placeThree) := by
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    change D.cusp.π (atFinite m) (F y) = F y
    rw [F_away m hm, hycomm _ (eval_planeLevi_one hm.1)]
    exact F_level y ⟨_, planeLevi_mem_finiteLevel hm⟩
  have hS : ∑ r ∈ t.representatives, cst r • D.cusp.π (atFinite (Bf r)) w =
      ∑ r ∈ t.representatives, F (y * atFinite (rationalFinite r)) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [F_rep y r hr, ← hycomm _ (hp3 r hr), F_par y r hr]
  have hSfix : (∑ r ∈ t.representatives, cst r • D.cusp.π (atFinite (Bf r)) w) ∈
      fixedVectors D.cusp (awayLevelA placeThree) := by
    rw [hS]
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    change D.cusp.π (atFinite m) _ = _
    rw [map_sum]
    have hterm : ∀ r ∈ t.representatives, D.cusp.π (atFinite m) (F (y * atFinite (rationalFinite r))) =
        F (y * atFinite (planeLevi m 1 * rationalFinite r)) := by
      intro r _
      rw [F_away m hm, ← mul_assoc, hycomm _ (eval_planeLevi_one hm.1), mul_assoc,
        HeckeTranslate.HeckeInvariance.atFinite_mul]
    rw [Finset.sum_congr rfl hterm]
    exact heckeSum_level t F (fun h k => F_level h k) y (planeLevi_mem_finiteLevel hm)
  have hSz := fixed_combination_omega D.cusp t.representatives cst Bf hBfaway w hw hSfix
  -- the quotient factor `atFinite q`
  obtain ⟨aq, bq, sq, Bq, hQ⟩ :=
    planeParabolic_exists_decomposition ⟨atFinite q.val, atFinite_mem_plane q.property⟩
  have hQ' : atFinite q.val = planeUnipotent aq bq * (planeLevi 1 sq * planeLevi Bq 1) :=
    Units.ext (congrArg Units.val hQ)
  set cQ := D.chi.toMonoidHom sq * normPower sq (-2 * inductionExponent .plane cohomologicalPoint) *
    normPower (GeneralLinearGroup.det Bq) (planeExp n)
  have F_Q : ∀ h, F (atFinite q.val * h) = cQ • D.cusp.π Bq (F h) := by
    intro h
    simp only [F]
    rw [hQ', planeVec_parabolic_coe hf]
  -- assemble
  have hsumv : ∑ r ∈ t.representatives, planeVec D f (X₀ * atFinite (rationalFinite r)) =
      (∑ r ∈ t.representatives, cst r * omega D.cusp (Bf r)) • planeVec D f X₀ := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_smul]
    change ∑ r ∈ t.representatives, F (X₀ * atFinite (rationalFinite r)) = (∑ r ∈ t.representatives, cst r * omega D.cusp (Bf r)) • F X₀
    have : ∀ r ∈ t.representatives, F (X₀ * atFinite (rationalFinite r)) =
        cQ • D.cusp.π Bq (F (y * atFinite (rationalFinite r))) := by
      intro r _
      rw [mul_assoc, F_Q]
    rw [Finset.sum_congr rfl this, ← Finset.smul_sum, ← map_sum, ← hS, hSz, map_smul, F_Q,
      smul_comm]
  have hgf : f g = f X₀ := by rw [hg, hf.2.1 κ']
  have hsum : ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
      ∑ r ∈ t.representatives, f (X₀ * atFinite (rationalFinite r)) := by
    have := heckeSum_level t f (fun h k => hf.2.1 k h) X₀ κ'.property
    rw [← this]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hg, mul_assoc, HeckeTranslate.HeckeInvariance.atFinite_mul]
  rw [hsum, hgf]
  simp only [planeVec_value hf]
  rw [← Finset.sum_apply, ← map_sum, hsumv, map_smul, Pi.smul_apply, smul_eq_mul]
  rfl

/-- **Explicit line eigenvalue.** -/
theorem line_hecke_formula (D : InducingData n) (t : HeckeCorrespondence)
    (p : RationalGL3 → FiniteGL) (κ : RationalGL3 → finiteLevel)
    (aa ba : RationalGL3 → Adeles) (sa : RationalGL3 → Adelesˣ) (Bf : RationalGL3 → BinaryFiniteGL)
    (hp3 : ∀ r ∈ t.representatives, GeneralLinearGroup.map (finiteEvaluation placeThree) (p r) = 1)
    (hpκ : ∀ r ∈ t.representatives, rationalFinite r = p r * (κ r).val)
    (hdec : ∀ r ∈ t.representatives, atFinite (p r) =
      lineUnipotent (aa r) (ba r) * (lineLevi (sa r) 1 * lineLevi 1 (atFinite (Bf r))))
    (hBfaway : ∀ r ∈ t.representatives, Bf r ∈ awayGroup placeThree) :
    ∀ f : AdelicGL → ℂ, IsInduced D .line cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        (∑ r ∈ t.representatives, lineWeight D (sa r) (Bf r)) * f g := by
  classical
  let cst : RationalGL3 → ℂ := fun r => D.chi.toMonoidHom (sa r) *
    normPower (sa r) (2 * inductionExponent .line cohomologicalPoint) *
    normPower (GeneralLinearGroup.det (atFinite (Bf r))) (lineExp n)
  intro f hf g
  -- the vector-valued function
  let F : AdelicGL → D.cusp.H := fun h => (lineVec D f h : D.cusp.H)
  have F_level : ∀ h (k : finiteLevel), F (h * atFinite k.val) = F h := fun h k => by
    simp only [F, lineVec_level hf h k]
  have F_rep : ∀ h, ∀ r ∈ t.representatives,
      F (h * atFinite (rationalFinite r)) = F (h * atFinite (p r)) := by
    intro h r hr
    rw [hpκ r hr, ← HeckeTranslate.HeckeInvariance.atFinite_mul, ← mul_assoc, F_level]
  have F_par : ∀ h, ∀ r ∈ t.representatives,
      F (atFinite (p r) * h) = cst r • D.cusp.π (atFinite (Bf r)) (F h) := by
    intro h r hr
    simp only [F, cst]
    rw [hdec r hr, lineVec_parabolic_coe hf]
  have F_away : ∀ m ∈ awayLevel placeThree, ∀ h,
      D.cusp.π (atFinite m) (F h) = F (atFinite (lineLevi 1 m) * h) := by
    intro m hm h
    simp only [F]
    rw [atFinite_lineLevi, lineVec_levi_coe hf, np_det_spherical hm.2, one_smul]
  -- decomposition of `g`
  obtain ⟨q, hqP, κg, hqk⟩ := finiteGL_line_compact_factorization (finiteGroup g)
  obtain ⟨κ₃, κ', hκ⟩ := integral_split_three κg
  set y := atInfinity (realGroup g) * atFinite (finiteAtPlaceGL 3 placeThree κ₃) with hy
  have hycomm : ∀ x : FiniteGL, GeneralLinearGroup.map (finiteEvaluation placeThree) x = 1 →
      atFinite x * y = y * atFinite x := fun x hx => atFinite_commute_y _ κ₃ hx
  set X₀ := atFinite q * y
  have hg : g = X₀ * atFinite κ'.val := by
    conv_lhs => rw [gl3_real_finite g, hqk, hκ]
    rw [← HeckeTranslate.HeckeInvariance.atFinite_mul, ← HeckeTranslate.HeckeInvariance.atFinite_mul,
      ← mul_assoc (atInfinity (realGroup g)), ← HeckeTranslate.HeckeInvariance.atFinite_comm_atInfinity]
    simp only [X₀, y, mul_assoc]
  -- the fixed vector and its Hecke image
  set w := F y
  have hw : w ∈ fixedVectors D.cusp (awayLevelA placeThree) := by
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    change D.cusp.π (atFinite m) (F y) = F y
    rw [F_away m hm, hycomm _ (eval_lineLevi_one hm.1)]
    exact F_level y ⟨_, lineLevi_mem_finiteLevel hm⟩
  have hS : ∑ r ∈ t.representatives, cst r • D.cusp.π (atFinite (Bf r)) w =
      ∑ r ∈ t.representatives, F (y * atFinite (rationalFinite r)) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [F_rep y r hr, ← hycomm _ (hp3 r hr), F_par y r hr]
  have hSfix : (∑ r ∈ t.representatives, cst r • D.cusp.π (atFinite (Bf r)) w) ∈
      fixedVectors D.cusp (awayLevelA placeThree) := by
    rw [hS]
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    change D.cusp.π (atFinite m) _ = _
    rw [map_sum]
    have hterm : ∀ r ∈ t.representatives, D.cusp.π (atFinite m) (F (y * atFinite (rationalFinite r))) =
        F (y * atFinite (lineLevi 1 m * rationalFinite r)) := by
      intro r _
      rw [F_away m hm, ← mul_assoc, hycomm _ (eval_lineLevi_one hm.1), mul_assoc,
        HeckeTranslate.HeckeInvariance.atFinite_mul]
    rw [Finset.sum_congr rfl hterm]
    exact heckeSum_level t F (fun h k => F_level h k) y (lineLevi_mem_finiteLevel hm)
  have hSz := fixed_combination_omega D.cusp t.representatives cst Bf hBfaway w hw hSfix
  -- the quotient factor `atFinite q`
  obtain ⟨aq, bq, sq, Bq, hQ'⟩ :=
    lineParabolic_exists_decomposition (atFinite q) (atFinite_mem_line hqP)
  set cQ := D.chi.toMonoidHom sq * normPower sq (2 * inductionExponent .line cohomologicalPoint) *
    normPower (GeneralLinearGroup.det Bq) (lineExp n)
  have F_Q : ∀ h, F (atFinite q * h) = cQ • D.cusp.π Bq (F h) := by
    intro h
    simp only [F]
    rw [hQ', lineVec_parabolic_coe hf]
  -- assemble
  have hsumv : ∑ r ∈ t.representatives, lineVec D f (X₀ * atFinite (rationalFinite r)) =
      (∑ r ∈ t.representatives, cst r * omega D.cusp (Bf r)) • lineVec D f X₀ := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_smul]
    change ∑ r ∈ t.representatives, F (X₀ * atFinite (rationalFinite r)) = (∑ r ∈ t.representatives, cst r * omega D.cusp (Bf r)) • F X₀
    have : ∀ r ∈ t.representatives, F (X₀ * atFinite (rationalFinite r)) =
        cQ • D.cusp.π Bq (F (y * atFinite (rationalFinite r))) := by
      intro r _
      rw [mul_assoc, F_Q]
    rw [Finset.sum_congr rfl this, ← Finset.smul_sum, ← map_sum, ← hS, hSz, map_smul, F_Q,
      smul_comm]
  have hgf : f g = f X₀ := by rw [hg, hf.2.1 κ']
  have hsum : ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
      ∑ r ∈ t.representatives, f (X₀ * atFinite (rationalFinite r)) := by
    have := heckeSum_level t f (fun h k => hf.2.1 k h) X₀ κ'.property
    rw [← this]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hg, mul_assoc, HeckeTranslate.HeckeInvariance.atFinite_mul]
  rw [hsum, hgf]
  simp only [lineVec_value hf]
  rw [← Finset.sum_apply, ← map_sum, hsumv, map_smul, Pi.smul_apply, smul_eq_mul]
  rfl

end TernaryPeriodPolynomials.HeckeEigen.Satake
