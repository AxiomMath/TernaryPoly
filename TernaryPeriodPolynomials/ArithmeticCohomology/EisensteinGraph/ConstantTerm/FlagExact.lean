module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.EngineGrid
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.DefectRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.DefectCovariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.DefectAverage
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.FlagDefect
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.RiemannGrid
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.LeviMatrices
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.FlagFrames

@[expose] public section


/-!
# Exactness of the defect at an integral flag, from a frame

For an integral flag representative `g` and a radical frame `F` adapted to `g` (radical points
`g u(3 w) g⁻¹`, Levi group acting through block matrices), the flag component of the defect cochain
is the differential of a one-cochain equivariant for the stabilizer of the flag in the arithmetic
level. The proof instantiates `engine_isCoboundary` for the defect translation family; the
regularity, covariance, periodicity and averaging inputs are those of `DefectRegularity`,
`DefectCovariance` and `DefectAverage`.

Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.FlagExactness

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

variable {n : ℕ}

/-- **Exactness of the defect at an integral flag**, given an adapted radical frame. -/
theorem defect_flag_exact_of_frame (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (g : IntegralGL3) (F : RadicalFrame)
    (hpoint : ∀ w : ℚ × ℚ, F.point w =
      (integralRational g) *
        sideUnipotent side (3 * w.1) (3 * w.2) *
        (integralRational g)⁻¹)
    (hunip : ∀ r : ℚ × ℚ, F.point r ∈
      conjUnitri (integralRational g))
    (hlat : ∀ K : ℕ, 0 < K → F.lattice (3 * K) ≤ rationalLevel ⊓ MulAction.stabilizer RationalGL3
      (QuotientGroup.mk (integralRational g) : Flags side))
    (hfin : ∀ K : ℕ, 0 < K → (F.lattice (3 * K)).relIndex (rationalLevel ⊓
      MulAction.stabilizer RationalGL3
        (QuotientGroup.mk (integralRational g) :
          Flags side)) ≠ 0)
    (hlevi_par : ∀ m : F.Levi,
      (integralRational g)⁻¹ * F.leviHom m *
        (integralRational g) ∈ parabolic side)
    (hlevi_conj : ∀ (m : F.Levi) (r : ℝ × ℝ),
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
        ((integralRational g)⁻¹ * F.leviHom m *
          (integralRational g)))⁻¹ *
        sideUnipotent side (3 * r.1) (3 * r.2) *
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          ((integralRational g)⁻¹ * F.leviHom m *
            (integralRational g)) =
      sideUnipotent side (3 * (realAct (F.leviMatrix m)⁻¹ r).1)
        (3 * (realAct (F.leviMatrix m)⁻¹ r).2)) :
    ∃ P : cochains (rationalLevel ⊓ MulAction.stabilizer RationalGL3
        (QuotientGroup.mk (integralRational g) :
          Flags side)) (rationalCoefficientComponent n D.chi) 1,
      ∀ y : Fin 3 → RationalGL3,
        (differentialOne (rationalLevel ⊓ MulAction.stabilizer RationalGL3
          (QuotientGroup.mk (integralRational g) :
            Flags side)) (rationalCoefficientComponent n D.chi) P).val y =
        (defectCochain large D hol c side).val y
          (QuotientGroup.mk (integralRational g)) := by
  classical
  set q : RationalGL3 := integralRational g
  set Γx := rationalLevel ⊓ MulAction.stabilizer RationalGL3 (QuotientGroup.mk q : Flags side)
  have hreg := defectFamily_regularity large D hol c side q 3
  have hΘ0 : Equivariant Γx (rationalCoefficientComponent n D.chi)
      ((fun r => defectFamily large D hol c side q 3 r) 0) := by
    have e : ((fun r => defectFamily large D hol c side q 3 r) 0) =
        fun y => (defectCochain large D hol c side).val y (QuotientGroup.mk q) :=
      funext fun y => defectFamily_zero_eq large D hol c side q 3 y
    rw [e]
    exact defectCochain_stabilizer_equivariant large D hol c side q
  have hshift : ∀ (w : ℚ × ℚ) (r : ℝ × ℝ) (y : Fin 3 → RationalGL3),
      defectFamily large D hol c side q 3 r (fun i => F.point w * y i) =
        rationalCoefficientComponent n D.chi (F.point w)
          (defectFamily large D hol c side q 3 (r.1 + (w.1 : ℝ), r.2 + (w.2 : ℝ)) y) := by
    intro w r y
    rw [hpoint w]
    have h := defectFamily_shift large D hol c side q 3 w r y
    simpa only [Nat.cast_ofNat] using h
  have hperiodic : ∀ (r : ℝ × ℝ) (ℓ : ℤ × ℤ) (y : Fin 3 → RationalGL3),
      defectFamily large D hol c side q 3 (r.1 + (ℓ.1 : ℝ), r.2 + (ℓ.2 : ℝ)) y =
        defectFamily large D hol c side q 3 r y := by
    intro r ℓ y
    have hmem : q * sideUnipotent side (((3 : ℕ) : ℚ) * (ℓ.1 : ℚ))
        (((3 : ℕ) : ℚ) * (ℓ.2 : ℚ)) * q⁻¹ ∈ rationalLevel := by
      have h1 : F.integral ℓ ∈ F.lattice 3 := F.integral_mem 3 ℓ
      have h2 : F.lattice 3 ≤ Γx := by simpa using hlat 1 one_pos
      have h3 := (Subgroup.mem_inf.mp (h2 h1)).1
      rw [F.integral_eq_point, hpoint] at h3
      simpa only [Nat.cast_ofNat] using h3
    exact defectFamily_periodic_int large D hol c side q 3 ℓ hmem r y
  have hcovF : ∀ m : F.Levi, F.leviHom m ∈ Γx → ∀ (r : ℝ × ℝ) (y : Fin 3 → RationalGL3),
      defectFamily large D hol c side q 3 r (fun i => F.leviHom m * y i) =
        rationalCoefficientComponent n D.chi (F.leviHom m)
          (defectFamily large D hol c side q 3 (realAct (F.leviMatrix m)⁻¹ r) y) := by
    intro m hm r y
    exact defectFamily_levi large D hol c side q 3 (F.leviHom m) (Subgroup.mem_inf.mp hm).1
      (hlevi_par m) r (realAct (F.leviMatrix m)⁻¹ r)
      (by simpa only [Nat.cast_ofNat] using hlevi_conj m r) y
  have hcov : ∀ γ ∈ Γx, ∃ A : GLTwo ℤ, ∀ (r : ℝ × ℝ) (y : Fin 3 → RationalGL3),
      defectFamily large D hol c side q 3 r (fun i => γ * y i) =
        rationalCoefficientComponent n D.chi γ
          (defectFamily large D hol c side q 3 (realAct A r) y) := by
    intro γ hγ
    obtain ⟨hγL, hγS⟩ := Subgroup.mem_inf.mp hγ
    have hp : q⁻¹ * γ * q ∈ parabolic side := by
      have h2 : (QuotientGroup.mk (γ * q) : Flags side) = QuotientGroup.mk q :=
        MulAction.mem_stabilizer_iff.mp hγS
      have h3 := (parabolic side).inv_mem (QuotientGroup.eq.mp h2)
      simpa [mul_assoc] using h3
    obtain ⟨A, hA⟩ := exists_levi_matrix side g γ hγL hp
    exact ⟨A, fun r y => defectFamily_levi large D hol c side q 3 γ hγL hp r (realAct A r)
      (hA r) y⟩
  have hmain := engine_isCoboundary D.chi F q hunip Γx 3 hlat hfin
    (fun r => defectFamily large D hol c side q 3 r) hreg.1 hreg.2
    (fun y μ => defectFamily_average_zero_Icc large D hol c side g y μ)
    hΘ0 hshift hperiodic hcovF hcov tendsto_gridSum_integral
  obtain ⟨P, hPeq, hcod⟩ := hmain
  refine ⟨⟨P, fun γ x => hPeq γ.val γ.property x⟩, fun y => ?_⟩
  exact (congrFun hcod y).symm.trans (defectFamily_zero_eq large D hol c side q 3 y)


/-- **Exactness of the defect at every integral flag representative.** -/
theorem defect_flag_exact (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (g : IntegralGL3) :
    ∃ P : cochains (rationalLevel ⊓ MulAction.stabilizer RationalGL3
        (QuotientGroup.mk (integralRational g) : Flags side))
        (rationalCoefficientComponent n D.chi) 1,
      ∀ y : Fin 3 → RationalGL3,
        (differentialOne (rationalLevel ⊓ MulAction.stabilizer RationalGL3
          (QuotientGroup.mk (integralRational g) : Flags side))
          (rationalCoefficientComponent n D.chi) P).val y =
        (defectCochain large D hol c side).val y
          (QuotientGroup.mk (integralRational g)) := by
  refine defect_flag_exact_of_frame large D hol c side g (sideFrame side g) ?_
    (fun r => sideFrame_radical_mem_conjUnitri side g r)
    (fun K _ => sideFrame_lattice_le side g (3 * K) (dvd_mul_right 3 K))
    (fun K hK => sideFrame_relIndex_ne_zero side g K hK)
    (fun m => sideFrame_levi_std_mem side g m) ?_
  · intro w
    cases side <;> rfl
  · intro m r
    cases side
    · exact planeFrame_levi_std_real g m r
    · exact lineFrame_levi_std_real g m r

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
