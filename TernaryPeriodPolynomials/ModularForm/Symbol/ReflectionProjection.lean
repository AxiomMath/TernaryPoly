module

public import TernaryPeriodPolynomials.ModularForm.Symbol.Reflection

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspSymbol
open BinaryModularSymbol RankTwoAugmentedFrames

/-- Literal coefficient extension identifies integral and special-linear charts. -/
theorem integral_sl_toGL (γ : SL2) :
    integral (Matrix.SpecialLinearGroup.toGL γ)=slRational γ := by
  apply Units.ext
  rfl

/-- Every determinant-one integral matrix is an actual special-linear chart. -/
theorem integral_eq_slRational (g : IntegralGL) (hg : g.val.det=1) :
    ∃ γ : SL2,integral g=slRational γ := by
  refine ⟨⟨g.val,hg⟩,?_⟩
  apply Units.ext
  rfl

/-- Conjugation by reflection preserves the actual integral special-linear group. -/
theorem exists_sl_reflection_conjugate (γ : SL2) :
    ∃ δ : SL2,reflection*slRational γ*reflection=slRational δ := by
  let g := reflectionIntegral*Matrix.SpecialLinearGroup.toGL γ*reflectionIntegral
  have hd : g.val.det=1 := by
    change (reflectionIntegral.val*(Matrix.SpecialLinearGroup.toGL γ).val*reflectionIntegral.val).det=1
    rw [Matrix.det_mul,Matrix.det_mul,reflectionIntegral_det]
    change (-1 : ℤ)*γ.val.det*(-1)=1
    rw [γ.det_coe]
    norm_num
  obtain ⟨δ,hδ⟩ := integral_eq_slRational g hd
  refine ⟨δ,?_⟩
  simpa only [g,map_mul,integral_sl_toGL,reflection] using hδ

/-- The actual full integral general linear group has precisely the two special-linear cosets. -/
theorem integral_sl_or_reflection (g : IntegralGL) :
    ∃ γ : SL2,integral g=slRational γ ∨ integral g=reflection*slRational γ := by
  rcases Int.isUnit_iff.mp (Matrix.isUnits_det_units g) with hg|hg
  · obtain ⟨γ,hγ⟩ := integral_eq_slRational g hg
    exact ⟨γ,Or.inl hγ⟩
  · have hd : (reflectionIntegral*g).val.det=1 := by
      change (reflectionIntegral.val*g.val).det=1
      rw [Matrix.det_mul,reflectionIntegral_det,hg]
      norm_num
    obtain ⟨γ,hγ⟩ := integral_eq_slRational (reflectionIntegral*g) hd
    refine ⟨γ,Or.inr ?_⟩
    rw [map_mul] at hγ
    change reflection*integral g=slRational γ at hγ
    rw [←hγ,←mul_assoc,reflection_sq,one_mul]

/-- Reflection carries every special-linear fixed vector to another such vector. -/
theorem reflection_preserves_sl_fixed {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : Representation ℚ GL2 V) (v : V) (hv : ∀ γ : SL2,ρ (slRational γ) v=v)
    (γ : SL2) : ρ (slRational γ) (ρ reflection v)=ρ reflection v := by
  obtain ⟨δ,hδ⟩ := exists_sl_reflection_conjugate γ
  have he : slRational γ*reflection=reflection*slRational δ := by
    rw [←hδ,←mul_assoc,←mul_assoc,reflection_sq,one_mul]
  rw [←Module.End.mul_apply,←map_mul,he,map_mul,Module.End.mul_apply,hv]

/-- Averaging a special-linear fixed vector with its reflection gives a genuine full-level
integral-general-linear fixed vector. -/
theorem reflection_average_integral_fixed {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : Representation ℚ GL2 V) (v : V) (hv : ∀ γ : SL2,ρ (slRational γ) v=v)
    (g : IntegralGL) :
    ρ (integral g) ((1/2 : ℚ) • (v+ρ reflection v))=(1/2 : ℚ) • (v+ρ reflection v) := by
  have hs (γ : SL2) : ρ (slRational γ) (v+ρ reflection v)=v+ρ reflection v := by
    rw [map_add,hv,reflection_preserves_sl_fixed ρ v hv]
  have hr : ρ reflection (v+ρ reflection v)=v+ρ reflection v := by
    rw [map_add,←Module.End.mul_apply,←map_mul,reflection_sq,map_one,Module.End.one_apply,add_comm]
  obtain ⟨γ,hγ|hγ⟩ := integral_sl_or_reflection g
  · rw [hγ,map_smul,hs]
  · rw [hγ,map_mul,Module.End.mul_apply,map_smul,hs,map_smul,hr]

end TernaryPoly.BinaryCuspSymbol
