module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.PlaneTransfer
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.LineVectors
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.LineFactorization

@[expose] public section


/-!
# Away-from-three Hecke operators act by scalars on line-induced sections

The line analogue of `PlaneTransfer`, using the line Iwasawa decomposition from
`LineFactorization` and the line vectors from `LineVectors`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.RepresentationTheory

namespace TernaryPeriodPolynomials.HeckeEigen

theorem one_succ {R : Type*} [CommRing R] (i j : Fin 2) :
    (1 : Matrix (Fin 3) (Fin 3) R) i.succ j.succ = (1 : Matrix (Fin 2) (Fin 2) R) i j := by
  fin_cases i <;> fin_cases j <;> simp

theorem atFinite_mem_line {p : FiniteGL} (hp : p ∈ lineParabolic FiniteAdeles) :
    atFinite p ∈ lineParabolic Adeles := by
  obtain ⟨h1, h2⟩ := hp
  refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩
  · change (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 0 = 0; simp
  · exact h1
  · change (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 0 = 0; simp
  · exact h2

theorem lineLevi_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (d : Rˣ) (A : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.map φ (lineLevi d A) = lineLevi (Units.map φ d) (GeneralLinearGroup.map φ A) := by
  apply Units.ext
  change (lineLevi d A).val.map φ = _
  rw [lineLevi_val, lineLevi_val]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.map_apply]

theorem atFinite_lineLevi (m : BinaryFiniteGL) :
    atFinite (lineLevi 1 m) = lineLevi 1 (atFinite m) := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · change (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = ((lineLevi 1 (atFinite m)).val i j).1
    rw [lineLevi_val]
    fin_cases i <;> fin_cases j <;> simp [atFinite, combineGL, pairMatrix]
  · change (lineLevi 1 m).val i j = ((lineLevi 1 (atFinite m)).val i j).2
    rw [lineLevi_val, lineLevi_val]
    fin_cases i <;> fin_cases j <;> simp [atFinite, combineGL, pairMatrix]

theorem block_awayGroup_line {p : FiniteGL}
    (hp3 : GeneralLinearGroup.map (finiteEvaluation placeThree) p = 1)
    {a b : FiniteAdeles} {s : FiniteAdelesˣ} {B : BinaryFiniteGL}
    (hdec : p = lineUnipotent a b * (lineLevi s 1 * lineLevi 1 B)) :
    B ∈ awayGroup placeThree := by
  rw [mem_awayGroup]
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h := congrArg (fun z : GeneralLinearGroup (Fin 3) (placeThree.adicCompletion ℚ) =>
    z.val i.succ j.succ) hp3
  simp only [GeneralLinearGroup.map_apply] at h
  rw [hdec, lineDecomp_block] at h
  rw [GeneralLinearGroup.map_apply, h]
  exact one_succ i j

theorem block_atFinite_line {p : FiniteGL} {a b : FiniteAdeles} {s : FiniteAdelesˣ}
    {B : BinaryFiniteGL} (hdec : p = lineUnipotent a b * (lineLevi s 1 * lineLevi 1 B))
    {a' b' : Adeles} {s' : Adelesˣ} {B' : BinaryAdelicGL}
    (hdec' : (atFinite p).val = (lineUnipotent a' b' * (lineLevi s' 1 * lineLevi 1 B')).val) :
    B' = atFinite B := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [← lineDecomp_block a' b' s' B' i j, ← hdec']
  apply Prod.ext
  · change (1 : Matrix (Fin 3) (Fin 3) ℝ) i.succ j.succ = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
    exact one_succ i j
  · change p.val i.succ j.succ = B.val i j
    rw [hdec]; exact lineDecomp_block a b s B i j

theorem eval_lineLevi_one {m : BinaryFiniteGL} (hm : m ∈ awayGroup placeThree) :
    GeneralLinearGroup.map (finiteEvaluation placeThree) (lineLevi 1 m) = 1 := by
  rw [lineLevi_map, mem_awayGroup.mp hm, map_one]
  exact (lineLeviHom _).map_one

theorem lineLevi_mem_finiteLevel {m : BinaryFiniteGL} (hm : m ∈ awayLevel placeThree) :
    lineLevi 1 m ∈ finiteLevel := by
  apply finiteLevel_of_integral_of_three
  · obtain ⟨m₀, rfl⟩ := hm.2
    refine ⟨lineLevi 1 m₀, ?_⟩
    rw [lineLevi_map, map_one]
  · rw [(finiteThree_eq_one_iff _).mpr (eval_lineLevi_one hm.1)]
    exact ⟨1, by simp, by simp⟩

theorem lineUnipotent_zero : lineUnipotent (0 : Adeles) 0 = 1 :=
  (lineUnipotentHom Adeles).map_one

variable {n : ℕ} {D : InducingData n}

theorem lineVec_parabolic_coe {f : AdelicGL → ℂ} (hf : IsInduced D .line cohomologicalPoint f)
    (a b : Adeles) (s : Adelesˣ) (B : BinaryAdelicGL) (h : AdelicGL) :
    (lineVec D f (lineUnipotent a b * (lineLevi s 1 * lineLevi 1 B) * h) : D.cusp.H) =
      (D.chi.toMonoidHom s * normPower s (2 * inductionExponent .line cohomologicalPoint) *
        normPower (GeneralLinearGroup.det B) (lineExp n)) • D.cusp.π B (lineVec D f h) := by
  rw [lineVec_parabolic hf]
  rfl

theorem lineVec_levi_coe {f : AdelicGL → ℂ} (hf : IsInduced D .line cohomologicalPoint f)
    (B : BinaryAdelicGL) (h : AdelicGL) :
    (lineVec D f (lineLevi 1 B * h) : D.cusp.H) =
      normPower (GeneralLinearGroup.det B) (lineExp n) • D.cusp.π B (lineVec D f h) := by
  have hB : lineLevi 1 B = lineUnipotent 0 0 * (lineLevi 1 1 * lineLevi 1 B) := by
    rw [lineUnipotent_zero, lineLevi_one_one, one_mul, one_mul]
  rw [hB, lineVec_parabolic_coe hf, map_one, np_one, one_mul, one_mul]

/-- **Away-from-three Hecke sums act by one scalar on all line-induced sections.** -/
theorem line_hecke_scalar (D : InducingData n) (t : HeckeCorrespondence) (ht : AwayThree t) :
    ∃ μ : ℂ, ∀ f : AdelicGL → ℂ, IsInduced D .line cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) = μ * f g := by
  classical
  have hfac : ∀ r ∈ t.representatives, ∃ p : FiniteGL, ∃ κ : finiteLevel,
      p ∈ lineParabolic FiniteAdeles ∧
      GeneralLinearGroup.map (finiteEvaluation placeThree) p = 1 ∧
      rationalFinite r = p * κ.val := by
    intro r hr
    obtain ⟨p, κ, hpP, hp3, hpk⟩ :=
      finiteGL_line_level_factorization (rationalFinite r) (rep_local_level ht hr)
    exact ⟨p, κ, hpP, (finiteThree_eq_one_iff _).mp hp3, hpk⟩
  choose! p κ hpP hp3 hpκ using hfac
  have hdecf : ∀ r ∈ t.representatives, ∃ (a b : FiniteAdeles) (s : FiniteAdelesˣ)
      (B : BinaryFiniteGL), p r = lineUnipotent a b * (lineLevi s 1 * lineLevi 1 B) :=
    fun r hr => lineParabolic_exists_decomposition (p r) (hpP r hr)
  choose! af bf sf Bf hBf using hdecf
  have hdeca : ∀ r ∈ t.representatives, ∃ (a b : Adeles) (s : Adelesˣ) (B : BinaryAdelicGL),
      atFinite (p r) = lineUnipotent a b * (lineLevi s 1 * lineLevi 1 B) := fun r hr =>
    lineParabolic_exists_decomposition (atFinite (p r)) (atFinite_mem_line (hpP r hr))
  choose! aa ba sa Ba hBa using hdeca
  have hBaf : ∀ r ∈ t.representatives, Ba r = atFinite (Bf r) := fun r hr =>
    block_atFinite_line (hBf r hr) (congrArg Units.val (hBa r hr))
  have hBfaway : ∀ r ∈ t.representatives, Bf r ∈ awayGroup placeThree := fun r hr =>
    block_awayGroup_line (hp3 r hr) (hBf r hr)
  let cst : RationalGL3 → ℂ := fun r => D.chi.toMonoidHom (sa r) *
    normPower (sa r) (2 * inductionExponent .line cohomologicalPoint) *
    normPower (GeneralLinearGroup.det (Ba r)) (lineExp n)
  obtain ⟨z, hz⟩ := fixed_combination D.cusp t.representatives cst Bf hBfaway
  refine ⟨z, fun f hf g => ?_⟩
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
    rw [hBa r hr, lineVec_parabolic_coe hf, hBaf r hr]
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
  have hSz := hz w hw hSfix
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
      z • lineVec D f X₀ := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_smul]
    change ∑ r ∈ t.representatives, F (X₀ * atFinite (rationalFinite r)) = z • F X₀
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

end TernaryPeriodPolynomials.HeckeEigen
