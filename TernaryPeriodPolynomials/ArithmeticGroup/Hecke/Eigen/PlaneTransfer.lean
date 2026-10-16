module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.PlaneVectors

@[expose] public section


/-!
# Away-from-three Hecke operators act by scalars on plane-induced sections

For an `AwayThree` correspondence `t` with representatives `r`, the finite Hecke sum
`f ↦ (g ↦ ∑ᵣ f (g · r_f))` acts by one scalar on all plane-induced sections of `D`. The proof
transfers the sum, through Iwasawa decompositions away from three, to a combination of
compressions of `D.cusp` at level `GL₂(Ẑ^{(3)})`, which is scalar by the Gelfand-pair argument
(`RepresentationTheory.awayCombination_scalar`).

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.RepresentationTheory

namespace TernaryPeriodPolynomials.HeckeEigen

theorem planeDecomp_block {R : Type*} [CommRing R] (a b : R) (s : Rˣ)
    (B : GeneralLinearGroup (Fin 2) R) (i j : Fin 2) :
    (planeUnipotent a b * (planeLevi 1 s * planeLevi B 1)).val i.castSucc j.castSucc = B.val i j := by
  fin_cases i <;> fin_cases j <;>
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem one_castSucc {R : Type*} [CommRing R] (i j : Fin 2) :
    (1 : Matrix (Fin 3) (Fin 3) R) i.castSucc j.castSucc = (1 : Matrix (Fin 2) (Fin 2) R) i j := by
  fin_cases i <;> fin_cases j <;> simp

theorem atFinite_mem_plane {p : FiniteGL} (hp : p ∈ planeParabolic FiniteAdeles) :
    atFinite p ∈ planeParabolic Adeles := by
  obtain ⟨h1, h2⟩ := hp
  refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩
  · change (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 0 = 0; simp
  · exact h1
  · change (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 1 = 0; simp
  · exact h2

theorem planeLevi_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : GeneralLinearGroup (Fin 2) R) (d : Rˣ) :
    GeneralLinearGroup.map φ (planeLevi A d) = planeLevi (GeneralLinearGroup.map φ A) (Units.map φ d) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [planeLevi, planeBlock, GeneralLinearGroup.map_apply]

theorem atFinite_planeLevi (m : BinaryFiniteGL) :
    atFinite (planeLevi m 1) = planeLevi (atFinite m) 1 := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;>
    fin_cases i <;> fin_cases j <;>
    simp [atFinite, combineGL, pairMatrix, planeLevi, planeBlock]

/-- The `GL₂` block of a finite plane-parabolic element trivial at three is trivial at three. -/
theorem block_awayGroup {p : FiniteGL} (hp3 : GeneralLinearGroup.map (finiteEvaluation placeThree) p = 1)
    {a b : FiniteAdeles} {s : FiniteAdelesˣ} {B : BinaryFiniteGL}
    (hdec : p = planeUnipotent a b * (planeLevi 1 s * planeLevi B 1)) :
    B ∈ awayGroup placeThree := by
  rw [mem_awayGroup]
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h := congrArg (fun z : GeneralLinearGroup (Fin 3) (placeThree.adicCompletion ℚ) =>
    z.val i.castSucc j.castSucc) hp3
  simp only [GeneralLinearGroup.map_apply] at h
  rw [hdec, planeDecomp_block] at h
  rw [GeneralLinearGroup.map_apply, h]
  exact one_castSucc i j

/-- The adelic block of `atFinite p` is `atFinite` of the finite block. -/
theorem block_atFinite {p : FiniteGL} {a b : FiniteAdeles} {s : FiniteAdelesˣ} {B : BinaryFiniteGL}
    (hdec : p = planeUnipotent a b * (planeLevi 1 s * planeLevi B 1))
    {a' b' : Adeles} {s' : Adelesˣ} {B' : BinaryAdelicGL}
    (hdec' : (atFinite p).val = (planeUnipotent a' b' * (planeLevi 1 s' * planeLevi B' 1)).val) :
    B' = atFinite B := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [← planeDecomp_block a' b' s' B' i j, ← hdec']
  apply Prod.ext
  · change (1 : Matrix (Fin 3) (Fin 3) ℝ) i.castSucc j.castSucc = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
    exact one_castSucc i j
  · change p.val i.castSucc j.castSucc = B.val i j
    rw [hdec]; exact planeDecomp_block a b s B i j

theorem eval_planeLevi_one {m : BinaryFiniteGL} (hm : m ∈ awayGroup placeThree) :
    GeneralLinearGroup.map (finiteEvaluation placeThree) (planeLevi m 1) = 1 := by
  rw [planeLevi_map, mem_awayGroup.mp hm, map_one]
  exact (planeLeviHom _).map_one

theorem planeLevi_mem_finiteLevel {m : BinaryFiniteGL} (hm : m ∈ awayLevel placeThree) :
    planeLevi m 1 ∈ finiteLevel := by
  apply finiteLevel_of_integral_of_three
  · obtain ⟨m₀, rfl⟩ := hm.2
    refine ⟨planeLevi m₀ 1, ?_⟩
    rw [planeLevi_map, map_one]
  · rw [(finiteThree_eq_one_iff _).mpr (eval_planeLevi_one hm.1)]
    exact ⟨1, by simp, by simp⟩

theorem np_det_spherical {m : BinaryFiniteGL} (hm : m ∈ sphericalFinite) (z : ℂ) :
    normPower (GeneralLinearGroup.det (atFinite m)) z = 1 := by
  obtain ⟨m₀, rfl⟩ := hm
  exact np_of_norm_one (PlaneEisensteinContinuation.Norm.adeleNorm_det_integral m₀) z

/-- Elements trivial at three commute with `atInfinity g · atFinite z₃`, `z₃` supported at three. -/
theorem atFinite_commute_y (g : RealGL3) (κ₃ : GeneralLinearGroup (Fin 3) (placeThree.adicCompletion ℚ))
    {x : FiniteGL} (hx : GeneralLinearGroup.map (finiteEvaluation placeThree) x = 1) :
    atFinite x * (atInfinity g * atFinite (finiteAtPlaceGL 3 placeThree κ₃)) =
      atInfinity g * atFinite (finiteAtPlaceGL 3 placeThree κ₃) * atFinite x := by
  rw [← mul_assoc, HeckeTranslate.HeckeInvariance.atFinite_comm_atInfinity, mul_assoc,
    HeckeTranslate.HeckeInvariance.atFinite_mul, ← threePart_commute κ₃ hx,
    ← HeckeTranslate.HeckeInvariance.atFinite_mul, mul_assoc]

/-- A combination of `GL₂(𝔸_f^{(3)})`-translates sending a `GL₂(Ẑ^{(3)})`-fixed vector to a fixed
vector acts on it by a scalar independent of the vector. -/
theorem fixed_combination (σ : CuspidalRepresentation) {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (x : ι → BinaryFiniteGL) (hx : ∀ i ∈ S, x i ∈ awayGroup placeThree) :
    ∃ z : ℂ, ∀ w ∈ fixedVectors σ (awayLevelA placeThree),
      (∑ i ∈ S, c i • σ.π (atFinite (x i)) w) ∈ fixedVectors σ (awayLevelA placeThree) →
      ∑ i ∈ S, c i • σ.π (atFinite (x i)) w = z • w := by
  have hK' : ∀ k ∈ (⊥ : Subgroup BinaryAdelicGL), ∀ y ∈ awayGroupA placeThree, k * y = y * k := by
    intro k hk y _; rw [Subgroup.mem_bot.mp hk, one_mul, mul_one]
  obtain ⟨z, hz⟩ := awayCombination_scalar σ ⊥ hK' S c x hx
  refine ⟨z, fun w hw hsum => ?_⟩
  have hK : awayLevelA placeThree ⊔ ⊥ = awayLevelA placeThree := sup_bot_eq _
  have hw' : w ∈ fixedVectors σ (awayLevelA placeThree ⊔ ⊥) := by rw [hK]; exact hw
  have hsum' : (∑ i ∈ S, c i • σ.π (atFinite (x i)) w) ∈
      fixedVectors σ (awayLevelA placeThree ⊔ ⊥) := by rw [hK]; exact hsum
  have h := congrArg Subtype.val (hz ⟨w, hw'⟩)
  have hcoe : ((∑ i ∈ S, c i • compression σ (awayLevelA placeThree ⊔ ⊥) (atFinite (x i)))
      ⟨w, hw'⟩ : σ.H) = (fixedVectors σ (awayLevelA placeThree ⊔ ⊥)).starProjection
        (∑ i ∈ S, c i • σ.π (atFinite (x i)) w) := by
    rw [_root_.sum_apply, Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [_root_.smul_apply, Submodule.coe_smul, map_smul, compression_coe]
  rw [hcoe, Submodule.starProjection_eq_self_iff.mpr hsum'] at h
  exact h

theorem gl3_real_finite (g : AdelicGL) : g = atInfinity (realGroup g) * atFinite (finiteGroup g) := by
  rw [atInfinity, atFinite, HeckeTranslate.HeckeInvariance.combineGL_mul, mul_one, one_mul]
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;>
    simp [combineGL, pairMatrix, realGroup, finiteGroup, GeneralLinearGroup.map]

theorem planeUnipotent_zero : planeUnipotent (0 : Adeles) 0 = 1 :=
  (planeUnipotentHom Adeles).map_one

variable {n : ℕ} {D : InducingData n}

theorem planeVec_parabolic_coe {f : AdelicGL → ℂ} (hf : IsInduced D .plane cohomologicalPoint f)
    (a b : Adeles) (s : Adelesˣ) (B : BinaryAdelicGL) (h : AdelicGL) :
    (planeVec D f (planeUnipotent a b * (planeLevi 1 s * planeLevi B 1) * h) : D.cusp.H) =
      (D.chi.toMonoidHom s * normPower s (-2 * inductionExponent .plane cohomologicalPoint) *
        normPower (GeneralLinearGroup.det B) (planeExp n)) • D.cusp.π B (planeVec D f h) := by
  rw [planeVec_parabolic hf]
  rfl

theorem planeVec_levi_coe {f : AdelicGL → ℂ} (hf : IsInduced D .plane cohomologicalPoint f)
    (B : BinaryAdelicGL) (h : AdelicGL) :
    (planeVec D f (planeLevi B 1 * h) : D.cusp.H) =
      normPower (GeneralLinearGroup.det B) (planeExp n) • D.cusp.π B (planeVec D f h) := by
  have hB : planeLevi B 1 = planeUnipotent 0 0 * (planeLevi 1 1 * planeLevi B 1) := by
    rw [planeUnipotent_zero, planeLevi_one_one, one_mul, one_mul]
  rw [hB, planeVec_parabolic_coe hf, map_one, np_one, one_mul, one_mul]

/-- **Away-from-three Hecke sums act by one scalar on all plane-induced sections.** -/
theorem plane_hecke_scalar (D : InducingData n) (t : HeckeCorrespondence) (ht : AwayThree t) :
    ∃ μ : ℂ, ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) = μ * f g := by
  classical
  have hfac : ∀ r ∈ t.representatives, ∃ p : FiniteGL, ∃ κ : finiteLevel,
      p ∈ planeParabolic FiniteAdeles ∧
      GeneralLinearGroup.map (finiteEvaluation placeThree) p = 1 ∧
      rationalFinite r = p * κ.val := by
    intro r hr
    obtain ⟨p, κ, hp3, hpk⟩ :=
      finiteGL_plane_level_factorization (rationalFinite r) (rep_local_level ht hr)
    exact ⟨p.val, κ, p.property, (finiteThree_eq_one_iff _).mp hp3, hpk⟩
  choose! p κ hpP hp3 hpκ using hfac
  have hdecf : ∀ r ∈ t.representatives, ∃ (a b : FiniteAdeles) (s : FiniteAdelesˣ)
      (B : BinaryFiniteGL), p r = planeUnipotent a b * (planeLevi 1 s * planeLevi B 1) :=
    fun r hr => planeParabolic_exists_decomposition ⟨p r, hpP r hr⟩
  choose! af bf sf Bf hBf using hdecf
  have hdeca : ∀ r ∈ t.representatives, ∃ (a b : Adeles) (s : Adelesˣ) (B : BinaryAdelicGL),
      atFinite (p r) = planeUnipotent a b * (planeLevi 1 s * planeLevi B 1) := by
    intro r hr
    obtain ⟨a, b, s, B, h⟩ :=
      planeParabolic_exists_decomposition ⟨atFinite (p r), atFinite_mem_plane (hpP r hr)⟩
    exact ⟨a, b, s, B, Units.ext (congrArg Units.val h)⟩
  choose! aa ba sa Ba hBa using hdeca
  have hBaf : ∀ r ∈ t.representatives, Ba r = atFinite (Bf r) := fun r hr =>
    block_atFinite (hBf r hr) (congrArg Units.val (hBa r hr))
  have hBfaway : ∀ r ∈ t.representatives, Bf r ∈ awayGroup placeThree := fun r hr =>
    block_awayGroup (hp3 r hr) (hBf r hr)
  let cst : RationalGL3 → ℂ := fun r => D.chi.toMonoidHom (sa r) *
    normPower (sa r) (-2 * inductionExponent .plane cohomologicalPoint) *
    normPower (GeneralLinearGroup.det (Ba r)) (planeExp n)
  obtain ⟨z, hz⟩ := fixed_combination D.cusp t.representatives cst Bf hBfaway
  refine ⟨z, fun f hf g => ?_⟩
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
    rw [hBa r hr, planeVec_parabolic_coe hf, hBaf r hr]
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
  have hSz := hz w hw hSfix
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
      z • planeVec D f X₀ := by
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
  simp only [planeVec_value hf]
  rw [← Finset.sum_apply, ← map_sum, hsumv, map_smul, Pi.smul_apply, smul_eq_mul]

end TernaryPeriodPolynomials.HeckeEigen
