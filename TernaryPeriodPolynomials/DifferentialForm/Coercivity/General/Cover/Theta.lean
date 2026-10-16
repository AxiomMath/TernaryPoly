module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Cover.Conjugate
public import Mathlib.Topology.Instances.Matrix

@[expose] public section


/-!
# General coercivity: the Cartan involution

The Cartan involution `θ g = (g⁻¹)ᵀ` of `GL₃(ℝ)` is realised on the model `Space` by
`ι S = S⁻¹ / tr S⁻¹`, an involutive homeomorphism with `ι (g • S) = θ g • ι S`.  Consequently the
Cartan image of an admissible group is admissible.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Set Matrix TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering

/-- The Cartan involution `g ↦ (g⁻¹)ᵀ` of `GL₃(ℝ)`. -/
def thetaHom : RealGL →* RealGL where
  toFun g := ⟨(↑(g⁻¹) : Mat).transpose, (↑g : Mat).transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' g h := by
    apply Units.ext
    simp [_root_.mul_inv_rev, Matrix.transpose_mul]

theorem thetaHom_val (g : RealGL) :
    ((thetaHom g : RealGL) : Mat) = (↑(g⁻¹) : Mat).transpose := rfl

theorem thetaHom_inv_val (g : RealGL) : (↑((thetaHom g)⁻¹) : Mat) = (↑g : Mat).transpose := rfl

theorem thetaHom_thetaHom (g : RealGL) : thetaHom (thetaHom g) = g := by
  apply Units.ext
  rw [thetaHom_val, thetaHom_inv_val]
  exact Matrix.transpose_transpose _

theorem det_thetaHom_eq_one {g : RealGL} (hg : g.val.det = 1) : (thetaHom g).val.det = 1 := by
  rw [thetaHom_val, Matrix.det_transpose]
  have := congrArg Matrix.det (Units.inv_mul g)
  rw [Matrix.det_mul, hg, mul_one, Matrix.det_one] at this
  exact this

/-- The Cartan involution on the model `Space`. -/
def iota (S : Space) : Space :=
  ⟨normalize S.val⁻¹, normalize_mem _ S.property.1.inv⟩

theorem iota_val (S : Space) : (iota S).val = normalize S.val⁻¹ := rfl

private theorem inv_smul_eq {M : Mat} (hM : IsUnit M.det) {c : ℝ} (hc : c ≠ 0) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul,
    Matrix.mul_nonsing_inv _ hM]

theorem iota_iota (S : Space) : iota (iota S) = S := by
  apply Subtype.ext
  have hS : IsUnit S.val.det := (Matrix.isUnit_iff_isUnit_det _).mp S.property.1.isUnit
  have hinv : IsUnit S.val⁻¹.det := (Matrix.isUnit_iff_isUnit_det _).mp S.property.1.inv.isUnit
  have hc : S.val⁻¹.trace⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt S.property.1.inv.trace_pos)
  change normalize (normalize S.val⁻¹)⁻¹ = S.val
  rw [show normalize S.val⁻¹ = S.val⁻¹.trace⁻¹ • S.val⁻¹ from rfl, inv_smul_eq hinv hc,
    Matrix.nonsing_inv_nonsing_inv _ hS, normalize_smul _ (inv_ne_zero hc),
    normalize_of_trace_one _ S.property.2]

theorem spacePosDef (S : Space) : S.val.PosDef := S.property.1

theorem continuous_iota : Continuous iota := by
  apply Continuous.subtype_mk
  have hinv : Continuous fun S : Space => S.val⁻¹ := by
    have : (fun S : Space => S.val⁻¹) = fun S => (S.val.det)⁻¹ • S.val.adjugate := by
      funext S
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this]
    exact (continuous_subtype_val.matrix_det.inv₀ (fun S => ((Matrix.isUnit_iff_isUnit_det _).mp (spacePosDef S).isUnit).ne_zero)).smul
      continuous_subtype_val.matrix_adjugate
  exact (hinv.matrix_trace.inv₀ (fun S => (S.property.1.inv.trace_pos).ne')).smul hinv

/-- The Cartan involution as a homeomorphism of `Space`. -/
def iotaHomeo : Space ≃ₜ Space where
  toFun := iota
  invFun := iota
  left_inv := iota_iota
  right_inv := iota_iota
  continuous_toFun := continuous_iota
  continuous_invFun := continuous_iota

private theorem conj_inv_aux (G Gi S Si : Mat) (h1 : Gᵀ * Giᵀ = 1) (h2 : G * Gi = 1)
    (hSS : S * Si = 1) : (G * S * Gᵀ) * (Giᵀ * Si * Gi) = 1 := by
  calc (G * S * Gᵀ) * (Giᵀ * Si * Gi) = G * S * (Gᵀ * Giᵀ) * Si * Gi := by
        simp only [Matrix.mul_assoc]
    _ = G * (S * Si) * Gi := by
        rw [h1, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hSS, Matrix.mul_one, h2]

/-- The Cartan involution intertwines the congruence actions of `g` and `θ g`. -/
theorem iota_act (g : RealGL) (S : Space) : iota (act g S) = act (thetaHom g) (iota S) := by
  apply Subtype.ext
  have hS : IsUnit S.val.det := (Matrix.isUnit_iff_isUnit_det _).mp S.property.1.isUnit
  have hX : (conjugate g S.val).PosDef := conjugate_positive g S.val S.property.1
  have hXu : IsUnit (conjugate g S.val).det := (Matrix.isUnit_iff_isUnit_det _).mp hX.isUnit
  have hc : (conjugate g S.val).trace⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hX.trace_pos)
  have hd : S.val⁻¹.trace⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt S.property.1.inv.trace_pos)
  have hY : (conjugate g S.val)⁻¹ = conjugate (thetaHom g) S.val⁻¹ := by
    apply Matrix.inv_eq_right_inv
    have hs : star (thetaHom g).val = (↑(g⁻¹) : Mat) := Matrix.transpose_transpose _
    have hGG : (↑g : Mat).transpose * (↑(g⁻¹) : Mat).transpose = 1 := by
      rw [← Matrix.transpose_mul, Units.inv_mul g, Matrix.transpose_one]
    have hSS : S.val * S.val⁻¹ = 1 := Matrix.mul_nonsing_inv _ hS
    have e1 : conjugate g S.val = (↑g : Mat) * S.val * (↑g : Mat).transpose := rfl
    have e2 : conjugate (thetaHom g) S.val⁻¹ =
        (↑(g⁻¹) : Mat).transpose * S.val⁻¹ * (↑(g⁻¹) : Mat) := by
      change (thetaHom g).val * S.val⁻¹ * star (thetaHom g).val = _
      rw [hs]
      rfl
    rw [e1, e2]
    exact conj_inv_aux _ _ _ _ hGG (Units.mul_inv g) hSS
  change normalize (normalize (conjugate g S.val))⁻¹ =
    normalize (conjugate (thetaHom g) (normalize S.val⁻¹))
  rw [show normalize (conjugate g S.val) = (conjugate g S.val).trace⁻¹ • conjugate g S.val from rfl,
    inv_smul_eq hXu hc, hY, normalize_smul _ (inv_ne_zero hc),
    show normalize S.val⁻¹ = S.val⁻¹.trace⁻¹ • S.val⁻¹ from rfl, conjugate_smul, normalize_smul _ hd]

variable {Γ : Subgroup RealGL}

/-- The Cartan image of an admissible group is admissible. -/
theorem Admissible.theta (h : Admissible Γ) : Admissible (Γ.map thetaHom) where
  det_one := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact det_thetaHom_eq_one (h.det_one γ hγ)
  free := by
    rintro _ ⟨γ, hγ, rfl⟩ S hS
    have h1 : act γ (iota S) = iota S := by
      have := iota_act γ (iota S)
      rw [iota_iota, hS] at this
      have := congrArg iota this
      rwa [iota_iota] at this
    rw [h.free γ hγ _ h1, map_one]
  transporters C D hC hD := by
    have hC' : IsCompact (iota '' C) := hC.image continuous_iota
    have hD' : IsCompact (iota '' D) := hD.image continuous_iota
    have hf := (h.transporters _ _ hC' hD').image (fun x : Γ => thetaHom (x : RealGL))
    refine (hf.preimage (Subtype.val_injective.injOn)).subset ?_
    rintro ⟨_, γ, hγ, rfl⟩ ⟨_, ⟨S, hS, rfl⟩, hT⟩
    refine ⟨⟨γ, hγ⟩, ⟨act (γ : RealGL) (iota S), ⟨iota S, ⟨S, hS, rfl⟩, rfl⟩,
      ⟨act (thetaHom γ) S, hT, ?_⟩⟩, rfl⟩
    rw [iota_act, thetaHom_thetaHom]

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
