module

/-
Adapted geometric part of akopjan/HamSandwich, Apache-2.0.
Original: SphereOddDegree/AlgebraicTopology/SphereHomologyMVStep.lean.
-/
public import TernaryPeriodPolynomials.Topology.Rational.Sphere.Geometry

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalSphere
open Metric
variable (n : ℕ)

/-- The equatorial-projection map underlying `band → Sⁿ`: drop coordinate `0` and
normalize. -/
def fFun (x : Sphere (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (fun i => x.val i.succ / Real.sqrt (eqNormSq n x))

theorem fFun_mem {x : Sphere (n + 1)} (hx : x ∈ sphereBand n) :
    fFun n x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      simp +decide [ fFun, EuclideanSpace.norm_eq ];
      norm_num [ div_pow, Real.sq_sqrt ( show 0 ≤ eqNormSq n x from Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ];
      rw [ ← Finset.sum_div _ _ _, eqNormSq ];
      exact div_self <| ne_of_gt <| eqNormSq_pos n hx

theorem continuous_fFun_band :
    Continuous (fun x : ↥(sphereBand n) => (⟨fFun n x.val, fFun_mem n x.2⟩ : Sphere n)) := by
      refine' Continuous.subtype_mk _ _;
      refine' continuous_iff_continuousAt.mpr _;
      intro x
      have h_cont : ContinuousAt (fun x : EuclideanSpace ℝ (Fin (n + 2)) => (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (fun i => x i.succ / Real.sqrt (∑ i : Fin (n + 1), (x i.succ) ^ 2))) x.val := by
        refine' ContinuousAt.comp ( _ : ContinuousAt ( fun x : Fin ( n + 1 ) → ℝ => ( WithLp.equiv 2 ( Fin ( n + 1 ) → ℝ ) ).symm x ) _ ) _;
        · exact Continuous.continuousAt ( by continuity );
        · refine' tendsto_pi_nhds.mpr fun i => ContinuousAt.div _ _ _;
          · exact Continuous.continuousAt ( by exact continuous_apply _ |> Continuous.comp <| by continuity );
          · fun_prop;
          · exact ne_of_gt <| Real.sqrt_pos.mpr <| eqNormSq_pos n x.2;
      exact h_cont.tendsto.comp ( continuous_subtype_val.continuousAt.comp ( continuous_subtype_val.continuousAt ) )

/-- The continuous map `band → Sⁿ`. -/
def bandToSphere : C(↥(sphereBand n), Sphere n) :=
  ⟨fun x => ⟨fFun n x.val, fFun_mem n x.2⟩, continuous_fFun_band n⟩

/-- The inclusion map underlying `Sⁿ → band`: prepend a `0` coordinate. -/
def gFun (y : Sphere n) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (WithLp.equiv 2 (Fin (n + 2) → ℝ)).symm (Fin.cons 0 (fun i => y.val i))

theorem gFun_mem_sphere (y : Sphere n) :
    gFun n y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := by
      simp +decide [ gFun, EuclideanSpace.norm_eq ];
      convert y.2 using 1;
      rw [ mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq ] ; norm_num [ Fin.sum_univ_succ ]

theorem gFun_mem_band (y : Sphere n) :
    (⟨gFun n y, gFun_mem_sphere n y⟩ : Sphere (n + 1)) ∈ sphereBand n := by
      constructor <;> intro h <;> simp_all +decide;
      · injection h with h ; replace h := congr_arg ( fun z => z 0 ) h ; simp_all +decide [ gFun ];
        exact absurd h ( by erw [ PiLp.single_apply ] ; norm_num );
      · injection h with h ; have := congr_arg ( fun x => x 0 ) h ; norm_num [ southPole ] at this;
        simp +decide [ gFun, northVec ] at this

theorem continuous_gFun :
    Continuous (fun y : Sphere n =>
      (⟨⟨gFun n y, gFun_mem_sphere n y⟩, gFun_mem_band n y⟩ : ↥(sphereBand n))) := by
        refine' Continuous.subtype_mk ( Continuous.subtype_mk _ _ ) _;
        -- The function y ↦ Fin.cons 0 (fun i => y.val i) is continuous because it is a composition of continuous functions.
        have h_cont : Continuous (fun y : Sphere n => Fin.cons 0 (fun i => y.val i) : Sphere n → Fin (n + 2) → ℝ) := by
          refine' continuous_pi_iff.mpr _;
          intro i; induction i using Fin.inductionOn <;> simp_all +decide [ Fin.cons ] ;
          · exact continuous_const;
          · fun_prop;
        convert h_cont using 1;
        exact iff_of_true ( Continuous.comp ( by continuity ) h_cont ) h_cont

/-- The continuous map `Sⁿ → band`. -/
def sphereToBand : C(Sphere n, ↥(sphereBand n)) :=
  ⟨fun y => ⟨⟨gFun n y, gFun_mem_sphere n y⟩, gFun_mem_band n y⟩, continuous_gFun n⟩

theorem bandToSphere_comp_sphereToBand :
    (bandToSphere n).comp (sphereToBand n) = ContinuousMap.id (Sphere n) := by
      ext i; simp [bandToSphere, sphereToBand, fFun, gFun];
      rw [ eqNormSq_eq ] ; norm_num [ Fin.sum_univ_succ ]

/-- The straight-line-on-the-sphere homotopy from `sphereToBand ∘ bandToSphere` to the
identity of the band. -/
def bandHomotopyFun (p : unitInterval × ↥(sphereBand n)) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (1 - (p.1 : ℝ)) • ((sphereToBand n (bandToSphere n p.2)).val.val) + (p.1 : ℝ) • p.2.val.val

theorem bandHomotopyFun_ne_zero (p : unitInterval × ↥(sphereBand n)) :
    bandHomotopyFun n p ≠ 0 := by
      unfold bandHomotopyFun;
      obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), p.2.val.val i.succ ≠ 0 := by
        have h_pos : 0 < ∑ i : Fin (n + 1), (p.2.val.val i.succ) ^ 2 := by
          exact eqNormSq_pos n p.2.2;
        exact not_forall.mp fun h => h_pos.ne' <| Finset.sum_eq_zero fun i _ => by simp +decide [ h i ] ;
      intro h; have := congr_arg ( fun x => x i.succ ) h; norm_num [ hi, sphereToBand, bandToSphere, fFun, gFun ] at this;
      by_cases h : p.1.val = 0 <;> simp_all +decide [ div_eq_mul_inv ];
      · exact absurd this ( ne_of_gt ( Real.sqrt_pos.mpr ( eqNormSq_pos n p.2.2 ) ) );
      · exact hi ( by nlinarith [ show 0 < ( 1 - p.1.val ) * ( Real.sqrt ( eqNormSq n p.2.val ) ) ⁻¹ + p.1.val from by exact add_pos_of_nonneg_of_pos ( mul_nonneg ( sub_nonneg.2 <| p.1.2.2 ) <| inv_nonneg.2 <| Real.sqrt_nonneg _ ) <| lt_of_le_of_ne ( p.1.2.1 ) <| Ne.symm <| by aesop ] )

theorem bandHomotopy_mem_sphere (p : unitInterval × ↥(sphereBand n)) :
    (‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := by
        simp +decide [ norm_smul, bandHomotopyFun_ne_zero ]

theorem bandHomotopy_mem_band (p : unitInterval × ↥(sphereBand n)) :
    (⟨‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p, bandHomotopy_mem_sphere n p⟩ : Sphere (n + 1))
      ∈ sphereBand n := by
        obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), p.2.val.val i.succ ≠ 0 := by
          exact not_forall.mp fun h => absurd ( eqNormSq_pos n p.2.2 ) ( by simp +decide [ h, eqNormSq ] );
        have h_coord : (‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p) (Fin.succ i) ≠ 0 := by
          simp_all +decide [ bandHomotopyFun, sphereToBand, bandToSphere, fFun, gFun ];
          field_simp;
          rw [ div_eq_iff ] <;> norm_num [ hi ];
          · by_cases h : p.1.val = 0 <;> simp_all +decide [ div_eq_mul_inv ];
            · exact ne_of_gt <| Real.sqrt_pos.mpr <| eqNormSq_pos n p.2.2;
            · exact ne_of_gt ( add_pos_of_nonneg_of_pos ( mul_nonneg ( sub_nonneg.2 <| p.1.2.2 ) <| inv_nonneg.2 <| Real.sqrt_nonneg _ ) <| lt_of_le_of_ne ( p.1.2.1 ) <| Ne.symm <| by aesop );
          · exact bandHomotopyFun_ne_zero n p
        constructor <;> intro h <;> simp_all +decide;
        · injection h with h ; replace h := congr_arg ( fun z => z i.succ ) h ;
          simp_all +decide [ northVec ];
        · injection h with h ; replace h := congr_arg ( fun x => x ( Fin.succ i ) ) h ; simp_all +decide [ northVec ]

theorem continuous_bandHomotopy :
    Continuous (fun p : unitInterval × ↥(sphereBand n) =>
      (⟨⟨‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p, bandHomotopy_mem_sphere n p⟩,
        bandHomotopy_mem_band n p⟩ : ↥(sphereBand n))) := by
  have h : Continuous (bandHomotopyFun n) := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp
        ((sphereToBand n).continuous.comp ((bandToSphere n).continuous.comp continuous_snd))))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))
  exact (((h.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (bandHomotopyFun_ne_zero n p))).smul h).subtype_mk _).subtype_mk _

theorem bandHomotopy_zero (x : ↥(sphereBand n)) :
    (⟨⟨‖bandHomotopyFun n (0, x)‖⁻¹ • bandHomotopyFun n (0, x), bandHomotopy_mem_sphere n (0, x)⟩,
        bandHomotopy_mem_band n (0, x)⟩ : ↥(sphereBand n))
      = (sphereToBand n).comp (bandToSphere n) x := by
        -- Since $t = 0$, we have $bandHomotopyFun n (0, x) = gfx$ by definition.
        have h_bandHomotopy_zero : bandHomotopyFun n (0, x) = (sphereToBand n (bandToSphere n x)).val.val := by
          unfold bandHomotopyFun; norm_num [ sphereToBand, bandToSphere, fFun, gFun ] ;
        simp +decide [ h_bandHomotopy_zero ]

theorem bandHomotopy_one (x : ↥(sphereBand n)) :
    (⟨⟨‖bandHomotopyFun n (1, x)‖⁻¹ • bandHomotopyFun n (1, x), bandHomotopy_mem_sphere n (1, x)⟩,
        bandHomotopy_mem_band n (1, x)⟩ : ↥(sphereBand n))
      = ContinuousMap.id _ x := by
        norm_num [ bandHomotopyFun ]

/-- The homotopy `sphereToBand ∘ bandToSphere ≃ id`. -/
def bandHomotopy :
    ContinuousMap.Homotopy ((sphereToBand n).comp (bandToSphere n)) (ContinuousMap.id _) where
  toFun p := ⟨⟨‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p, bandHomotopy_mem_sphere n p⟩,
    bandHomotopy_mem_band n p⟩
  continuous_toFun := continuous_bandHomotopy n
  map_zero_left := bandHomotopy_zero n
  map_one_left := bandHomotopy_one n

/-- The equatorial band `Sⁿ⁺¹ \ {north, south}` is homotopy equivalent to `Sⁿ`. -/
def sphereBandHomotopyEquiv : ContinuousMap.HomotopyEquiv (sphereBand n) (Sphere n) where
  toFun := bandToSphere n
  invFun := sphereToBand n
  left_inv := ⟨bandHomotopy n⟩
  right_inv := bandToSphere_comp_sphereToBand n ▸ ContinuousMap.Homotopic.refl _


end TernaryPoly.RationalSphere
