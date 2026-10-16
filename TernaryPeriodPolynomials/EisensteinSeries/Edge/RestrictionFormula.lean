module

public import TernaryPeriodPolynomials.EisensteinSeries.Edge.DefectChain
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.FlagExact
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.RestrictionAssembly

@[expose] public section


/-!
# The restriction formula from the analytic inputs

The defect cochain (restriction of the global Eisenstein cocycle minus the evaluated source of
the side) is exact at every integral flag representative: its flag component is the origin of the
defect translation family, which `ConstantTerm.engine_isCoboundary` (torus averaging) turns into a
coboundary from the regularity, covariance, periodicity and vanishing averages of `DefectChain`.
The Shapiro assembly and the existence of integral flag representatives then give the restriction
formula `restriction_formula`: the maximal-stratum coordinates of the global Eisenstein cocycle of
`c` are the classes of `c` and of `line`.

Original work by Claude Opus 5.5 (AxiomCode), generalizing AxiomCode's `ConstantTerm` chain (`FlagDefect`, `FlagExact`, `RestrictionAssembly`, `RestrictionFinal`).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein

open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

variable {n : ℕ}

section Flag

variable (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
  (c : SourceSpace.sourceCocycles D .plane) (cov : SourceRealCovariant D hol c)
  (line : SourceSpace.sourceCocycles D .line)

/-- The flag component of the defect cochain is the origin of the defect family. -/
theorem defectFamily_zero_eq (side : Side) (q : RationalGL3) (K : ℕ) (y : Fin 3 → RationalGL3) :
    defectFamily D hol c line side q K 0 y =
      (defectCochain D hol c cov line side).val y (QuotientGroup.mk q) := by
  have h1 : ConstantTerm.sideUnipotent side ((K : ℝ) * (0 : ℝ × ℝ).1)
      ((K : ℝ) * (0 : ℝ × ℝ).2) = 1 := by
    simp only [Prod.fst_zero, Prod.snd_zero, mul_zero]
    exact ConstantTerm.sideUnipotent_zero side
  have e1 : (restrictionCocycle n D.chi side (globalCocycle D hol c cov)).val.val y
      (QuotientGroup.mk q) =
        ConstantTerm.eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices y)
          (rationalGroup q⁻¹) := by
    change (globalCocycle D hol c cov).val.val y = _
    rw [globalCocycle_realizes, GlobalEisensteinCocycle.evaluatedSourceValue_eq_anchor D hol c y q]
    rfl
  have e2 : (SourceSpace.evaluatedSource D side (sideSource D c line side)).val.val y
      (QuotientGroup.mk q) =
        (sideSource D c line side).val (GlobalEisensteinCocycle.realVertices y)
          (rationalGroup q⁻¹) :=
    SourceSpace.evaluatedSource_realizes D side (sideSource D c line side) y q
  have hD : (defectCochain D hol c cov line side).val y (QuotientGroup.mk q) =
      (restrictionCocycle n D.chi side (globalCocycle D hol c cov)).val.val y
        (QuotientGroup.mk q) -
      (SourceSpace.evaluatedSource D side (sideSource D c line side)).val.val y
        (QuotientGroup.mk q) := rfl
  rw [hD, e1, e2]
  unfold defectFamily
  rw [h1, LineInductionLaws.atInfinity_one, one_mul]
  rfl

/-- The flag component of the defect cochain is equivariant for the stabilizer of the flag. -/
theorem defectCochain_stabilizer_equivariant (side : Side) (q : RationalGL3) :
    ConstantTerm.Equivariant
      (rationalLevel ⊓ MulAction.stabilizer RationalGL3 (QuotientGroup.mk q : Flags side))
      (rationalCoefficientComponent n D.chi)
      (fun y => (defectCochain D hol c cov line side).val y (QuotientGroup.mk q)) := by
  intro γ hγ x
  obtain ⟨hγL, hγS⟩ := Subgroup.mem_inf.mp hγ
  have h := (defectCochain D hol c cov line side).property ⟨γ, hγL⟩ x
  have h' := congrFun h (QuotientGroup.mk q)
  change _ = rationalCoefficientComponent n D.chi γ
    ((defectCochain D hol c cov line side).val x (γ⁻¹ • (QuotientGroup.mk q : Flags side))) at h'
  have hs : γ⁻¹ • (QuotientGroup.mk q : Flags side) = QuotientGroup.mk q := by
    rw [inv_smul_eq_iff]
    exact (MulAction.mem_stabilizer_iff.mp hγS).symm
  rw [hs] at h'
  exact h'

include cov in
/-- Covariance of the defect family under the stabilizer of an integral flag in the level. -/
theorem defectFamily_stabilizer_covariant (side : Side) (g : IntegralGL3) (γ : RationalGL3)
    (hγ : γ ∈ rationalLevel ⊓ MulAction.stabilizer RationalGL3
      (QuotientGroup.mk (integralRational g) : Flags side)) :
    ∃ A : ConstantTerm.GLTwo ℤ, ∀ (r : ℝ × ℝ) (y : Fin 3 → RationalGL3),
      defectFamily D hol c line side (integralRational g) 3 r (fun i => γ * y i) =
        rationalCoefficientComponent n D.chi γ
          (defectFamily D hol c line side (integralRational g) 3 (ConstantTerm.realAct A r) y) := by
  obtain ⟨hγL, hγS⟩ := Subgroup.mem_inf.mp hγ
  have hp : (integralRational g)⁻¹ * γ * integralRational g ∈ parabolic side := by
    have h2 : (QuotientGroup.mk (γ * integralRational g) : Flags side) =
        QuotientGroup.mk (integralRational g) :=
      MulAction.mem_stabilizer_iff.mp hγS
    have h3 := (parabolic side).inv_mem (QuotientGroup.eq.mp h2)
    simpa [mul_assoc] using h3
  have castEq : (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3) =
      integralRational g := rfl
  obtain ⟨A, hA⟩ := ConstantTerm.exists_levi_matrix side g γ hγL (by rw [castEq]; exact hp)
  rw [castEq] at hA
  refine ⟨A, fun r y => ?_⟩
  have hr : (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
        ((integralRational g)⁻¹ * γ * integralRational g))⁻¹ *
      ConstantTerm.sideUnipotent side (((3 : ℕ) : ℝ) * r.1) (((3 : ℕ) : ℝ) * r.2) *
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
        ((integralRational g)⁻¹ * γ * integralRational g) =
      ConstantTerm.sideUnipotent side (((3 : ℕ) : ℝ) * (ConstantTerm.realAct A r).1)
        (((3 : ℕ) : ℝ) * (ConstantTerm.realAct A r).2) := by
    rw [Nat.cast_ofNat]
    exact hA r
  exact defectFamily_levi D hol c cov line side (integralRational g) 3 γ hγL hp r
    (ConstantTerm.realAct A r) hr y

include cov in
/-- Shift covariance of the defect family along an adapted radical frame. -/
theorem defectFamily_frame_shift (side : Side) (g : IntegralGL3) (F : ConstantTerm.RadicalFrame)
    (hpoint : ∀ w : ℚ × ℚ, F.point w =
      (integralRational g) * ConstantTerm.sideUnipotent side (3 * w.1) (3 * w.2) *
        (integralRational g)⁻¹)
    (w : ℚ × ℚ) (r : ℝ × ℝ) (y : Fin 3 → RationalGL3) :
    defectFamily D hol c line side (integralRational g) 3 r (fun i => F.point w * y i) =
      rationalCoefficientComponent n D.chi (F.point w)
        (defectFamily D hol c line side (integralRational g) 3
          (r.1 + (w.1 : ℝ), r.2 + (w.2 : ℝ)) y) := by
  rw [hpoint w]
  have h := defectFamily_shift D hol c cov line side (integralRational g) 3 w r y
  simpa only [Nat.cast_ofNat] using h

/-- Periodicity of the defect family along the integral lattice of an adapted frame. -/
theorem defectFamily_frame_periodic (side : Side) (g : IntegralGL3) (F : ConstantTerm.RadicalFrame)
    (hpoint : ∀ w : ℚ × ℚ, F.point w =
      (integralRational g) * ConstantTerm.sideUnipotent side (3 * w.1) (3 * w.2) *
        (integralRational g)⁻¹)
    (hlat : ∀ K : ℕ, 0 < K → F.lattice (3 * K) ≤ rationalLevel ⊓ MulAction.stabilizer RationalGL3
      (QuotientGroup.mk (integralRational g) : Flags side))
    (r : ℝ × ℝ) (ℓ : ℤ × ℤ) (y : Fin 3 → RationalGL3) :
    defectFamily D hol c line side (integralRational g) 3 (r.1 + (ℓ.1 : ℝ), r.2 + (ℓ.2 : ℝ)) y =
      defectFamily D hol c line side (integralRational g) 3 r y := by
  have hmem : integralRational g * ConstantTerm.sideUnipotent side (((3 : ℕ) : ℚ) * (ℓ.1 : ℚ))
      (((3 : ℕ) : ℚ) * (ℓ.2 : ℚ)) * (integralRational g)⁻¹ ∈ rationalLevel := by
    have h1 : F.integral ℓ ∈ F.lattice 3 := F.integral_mem 3 ℓ
    have h2 : F.lattice 3 ≤ rationalLevel ⊓ MulAction.stabilizer RationalGL3
        (QuotientGroup.mk (integralRational g) : Flags side) := by
      simpa using hlat 1 one_pos
    have h3 := (Subgroup.mem_inf.mp (h2 h1)).1
    rw [F.integral_eq_point, hpoint] at h3
    simpa only [Nat.cast_ofNat] using h3
  exact defectFamily_periodic_int D hol c line side (integralRational g) 3 ℓ hmem r y

include cov in
/-- Levi covariance of the defect family along an adapted frame. -/
theorem defectFamily_frame_levi (side : Side) (g : IntegralGL3) (F : ConstantTerm.RadicalFrame)
    (hlevi_par : ∀ m : F.Levi,
      (integralRational g)⁻¹ * F.leviHom m * (integralRational g) ∈ parabolic side)
    (hlevi_conj : ∀ (m : F.Levi) (r : ℝ × ℝ),
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
        ((integralRational g)⁻¹ * F.leviHom m * (integralRational g)))⁻¹ *
        ConstantTerm.sideUnipotent side (3 * r.1) (3 * r.2) *
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          ((integralRational g)⁻¹ * F.leviHom m * (integralRational g)) =
      ConstantTerm.sideUnipotent side (3 * (ConstantTerm.realAct (F.leviMatrix m)⁻¹ r).1)
        (3 * (ConstantTerm.realAct (F.leviMatrix m)⁻¹ r).2))
    (m : F.Levi) (hm : F.leviHom m ∈ rationalLevel ⊓ MulAction.stabilizer RationalGL3
      (QuotientGroup.mk (integralRational g) : Flags side))
    (r : ℝ × ℝ) (y : Fin 3 → RationalGL3) :
    defectFamily D hol c line side (integralRational g) 3 r (fun i => F.leviHom m * y i) =
      rationalCoefficientComponent n D.chi (F.leviHom m)
        (defectFamily D hol c line side (integralRational g) 3
          (ConstantTerm.realAct (F.leviMatrix m)⁻¹ r) y) :=
  defectFamily_levi D hol c cov line side (integralRational g) 3 (F.leviHom m)
    (Subgroup.mem_inf.mp hm).1 (hlevi_par m) r (ConstantTerm.realAct (F.leviMatrix m)⁻¹ r)
    (by simpa only [Nat.cast_ofNat] using hlevi_conj m r) y

/-- **Exactness of the defect at an integral flag**, given an adapted radical frame. -/
theorem defect_flag_exact_of_frame (cont : EisensteinContinuous D hol)
    (planeCT : PlaneConstantTermAtEdge D hol) (lineCT : LineConstantTermAtEdge D hol c line)
    (side : Side) (g : IntegralGL3) (F : ConstantTerm.RadicalFrame)
    (hpoint : ∀ w : ℚ × ℚ, F.point w =
      (integralRational g) * ConstantTerm.sideUnipotent side (3 * w.1) (3 * w.2) *
        (integralRational g)⁻¹)
    (hunip : ∀ r : ℚ × ℚ, F.point r ∈ FlagExactness.conjUnitri (integralRational g))
    (hlat : ∀ K : ℕ, 0 < K → F.lattice (3 * K) ≤ rationalLevel ⊓ MulAction.stabilizer RationalGL3
      (QuotientGroup.mk (integralRational g) : Flags side))
    (hfin : ∀ K : ℕ, 0 < K → (F.lattice (3 * K)).relIndex (rationalLevel ⊓
      MulAction.stabilizer RationalGL3 (QuotientGroup.mk (integralRational g) : Flags side)) ≠ 0)
    (hlevi_par : ∀ m : F.Levi,
      (integralRational g)⁻¹ * F.leviHom m * (integralRational g) ∈ parabolic side)
    (hlevi_conj : ∀ (m : F.Levi) (r : ℝ × ℝ),
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
        ((integralRational g)⁻¹ * F.leviHom m * (integralRational g)))⁻¹ *
        ConstantTerm.sideUnipotent side (3 * r.1) (3 * r.2) *
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          ((integralRational g)⁻¹ * F.leviHom m * (integralRational g)) =
      ConstantTerm.sideUnipotent side (3 * (ConstantTerm.realAct (F.leviMatrix m)⁻¹ r).1)
        (3 * (ConstantTerm.realAct (F.leviMatrix m)⁻¹ r).2)) :
    ∃ P : cochains (rationalLevel ⊓ MulAction.stabilizer RationalGL3
        (QuotientGroup.mk (integralRational g) : Flags side)) (rationalCoefficientComponent n D.chi) 1,
      ∀ y : Fin 3 → RationalGL3,
        (differentialOne (rationalLevel ⊓ MulAction.stabilizer RationalGL3
          (QuotientGroup.mk (integralRational g) : Flags side))
          (rationalCoefficientComponent n D.chi) P).val y =
        (defectCochain D hol c cov line side).val y (QuotientGroup.mk (integralRational g)) := by
  have hΘ0 : ConstantTerm.Equivariant (rationalLevel ⊓ MulAction.stabilizer RationalGL3
        (QuotientGroup.mk (integralRational g) : Flags side))
      (rationalCoefficientComponent n D.chi)
      ((fun r => defectFamily D hol c line side (integralRational g) 3 r) 0) := by
    have e : ((fun r => defectFamily D hol c line side (integralRational g) 3 r) 0) =
        fun y => (defectCochain D hol c cov line side).val y
          (QuotientGroup.mk (integralRational g)) :=
      funext fun y => defectFamily_zero_eq D hol c cov line side (integralRational g) 3 y
    rw [e]
    exact defectCochain_stabilizer_equivariant D hol c cov line side (integralRational g)
  obtain ⟨P, hPeq, hcod⟩ := ConstantTerm.engine_isCoboundary D.chi F (integralRational g) hunip
    _ 3 hlat hfin (fun r => defectFamily D hol c line side (integralRational g) 3 r)
    (defectFamily_regularity D hol c line cont side (integralRational g) 3).1
    (defectFamily_regularity D hol c line cont side (integralRational g) 3).2
    (fun y μ => defectFamily_average_zero_Icc D hol c line cont planeCT lineCT side g y μ)
    hΘ0 (defectFamily_frame_shift D hol c cov line side g F hpoint)
    (defectFamily_frame_periodic D hol c line side g F hpoint hlat)
    (defectFamily_frame_levi D hol c cov line side g F hlevi_par hlevi_conj)
    (fun γ hγ => defectFamily_stabilizer_covariant D hol c cov line side g γ hγ)
    ConstantTerm.tendsto_gridSum_integral
  refine ⟨⟨P, fun γ x => hPeq γ.val γ.property x⟩, fun y => ?_⟩
  exact (congrFun hcod y).symm.trans
    (defectFamily_zero_eq D hol c cov line side (integralRational g) 3 y)

/-- **Exactness of the defect at every integral flag representative.** -/
theorem defect_flag_exact (cont : EisensteinContinuous D hol)
    (planeCT : PlaneConstantTermAtEdge D hol) (lineCT : LineConstantTermAtEdge D hol c line)
    (side : Side) (g : IntegralGL3) :
    ∃ P : cochains (rationalLevel ⊓ MulAction.stabilizer RationalGL3
        (QuotientGroup.mk (integralRational g) : Flags side))
        (rationalCoefficientComponent n D.chi) 1,
      ∀ y : Fin 3 → RationalGL3,
        (differentialOne (rationalLevel ⊓ MulAction.stabilizer RationalGL3
          (QuotientGroup.mk (integralRational g) : Flags side))
          (rationalCoefficientComponent n D.chi) P).val y =
        (defectCochain D hol c cov line side).val y (QuotientGroup.mk (integralRational g)) := by
  refine defect_flag_exact_of_frame D hol c cov line cont planeCT lineCT side g
    (ConstantTerm.sideFrame side g) ?_
    (fun r => ConstantTerm.sideFrame_radical_mem_conjUnitri side g r)
    (fun K _ => ConstantTerm.sideFrame_lattice_le side g (3 * K) (dvd_mul_right 3 K))
    (fun K hK => ConstantTerm.sideFrame_relIndex_ne_zero side g K hK)
    (fun m => ConstantTerm.sideFrame_levi_std_mem side g m) ?_
  · intro w
    cases side <;> rfl
  · intro m r
    cases side
    · exact ConstantTerm.planeFrame_levi_std_real g m r
    · exact ConstantTerm.lineFrame_levi_std_real g m r

/-- The defect cochain is the differential of an equivariant one-cochain. -/
theorem defectCochain_exact (cont : EisensteinContinuous D hol)
    (planeCT : PlaneConstantTermAtEdge D hol) (lineCT : LineConstantTermAtEdge D hol c line)
    (side : Side) :
    ∃ P : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side) 1,
      ∀ y, (differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) side) P).val y =
        (defectCochain D hol c cov line side).val y := by
  apply ConstantTerm.exists_primitive_of_stabilizers (rationalCoefficientComponent n D.chi)
    (Flags side) rationalLevel (defectCochain D hol c cov line side)
  intro x
  obtain ⟨g, rfl⟩ := ConstantTerm.exists_integral_representative side x
  exact defect_flag_exact D hol c cov line cont planeCT lineCT side g

/-- Equality of stratum classes from exactness of the defect cochain. -/
theorem stratum_class_eq (side : Side)
    (hexact : ∃ P : cochains rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) side) 1,
      ∀ y, (differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) side) P).val y =
        (defectCochain D hol c cov line side).val y) :
    classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side)
        (restrictionCocycle n D.chi side (globalCocycle D hol c cov)) =
      SourceSpace.sourceClass D side (sideSource D c line side) := by
  obtain ⟨P, hP⟩ := hexact
  change classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side)
      (restrictionCocycle n D.chi side (globalCocycle D hol c cov)) =
    classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side)
      (SourceSpace.evaluatedSource D side (sideSource D c line side))
  rw [← sub_eq_zero, ← map_sub]
  refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨P, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext y
  exact hP y

end Flag

/-- **The restriction formula**, from the four analytic inputs: the maximal-stratum coordinates of
the global Eisenstein cocycle of `c` are the classes of `c` and of `line`. -/
theorem restriction_formula (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (cont : EisensteinContinuous D hol) (planeCT : PlaneConstantTermAtEdge D hol)
    (c : SourceSpace.sourceCocycles D .plane) (cov : SourceRealCovariant D hol c)
    (line : SourceSpace.sourceCocycles D .line) (lineCT : LineConstantTermAtEdge D hol c line) :
    globalCoordinates n D.chi (globalCocycle D hol c cov) =
      (SourceSpace.sourceClass D .plane c, SourceSpace.sourceClass D .line line) :=
  Prod.ext
    (stratum_class_eq D hol c cov line .plane
      (defectCochain_exact D hol c cov line cont planeCT lineCT .plane))
    (stratum_class_eq D hol c cov line .line
      (defectCochain_exact D hol c cov line cont planeCT lineCT .line))

end TernaryPeriodPolynomials.EdgeEisenstein
