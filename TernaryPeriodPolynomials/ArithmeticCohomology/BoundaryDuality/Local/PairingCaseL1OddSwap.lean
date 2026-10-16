module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentSwap

@[expose] public section


/-!
# The swap pullback acts as `-1` on `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det^τ)`

The one-cocycle of the dual plane in the level-one bridge is the pullback `Z γ = - rot (F (invT γ))`
of a one-cocycle `F` of `GL₂(ℤ)` along the inverse transpose `invT γ = γ^{-T}`, followed by the
rotation `rot g(x, y) = g(-y, x)` (`ParabolicDualityIdentSwap`). The rotation is the action of
`S⁻¹ ∈ SL₂(ℤ)` on `Sym^{n+1} ⊗ det^τ` (`binarySwap_eq_rho`), and for `γ ∈ GL₂(ℤ)` the inverse
transpose is `S γ S⁻¹` up to the central element `-1 = S²` (`invT_mul_S`), which acts trivially on
even degree and has trivial cocycle value. Hence

  `Z γ = - F γ + (ρ(γ) - 1) w`,   `w = ρ(S⁻¹) F(S)`,

so `[Z] = -[F]` in `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det^τ)`, for every `τ` and odd `n`
(`swapPullback_projectH1_eq_neg`). In particular the pairing of the line class against the
identification of the dual plane class is the pairing against the plane edge class itself, with the
sign `-1`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (invT mul_invT_transpose binarySwap binarySwap_coe swapMatrix)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1OddSwap

/-! ### The rotation is the action of `S⁻¹` -/

theorem det_map_S_inv : ((GeneralLinearGroup.det
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (toGL ModularGroup.S⁻¹)) : ℂˣ) : ℂ) = 1 := by
  rw [GeneralLinearGroup.val_det_apply]
  simp [toGL, ModularGroup.coe_S, Matrix.det_fin_two]

theorem inv_map_S_inv : (((GeneralLinearGroup.map (Int.castRingHom ℂ)
    (toGL ModularGroup.S⁻¹))⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) = swapMatrix := by
  simp only [map_inv, inv_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMatrix, toGL, ModularGroup.coe_S]

/-- **The rotation `g(x, y) ↦ g(-y, x)` is the action of `S⁻¹`.** -/
theorem binarySwap_eq_rho (n : ℕ) (τ : ℤ) (v : arithmeticBinaryRep (n + 1) τ) :
    binarySwap (n + 1) v = (arithmeticBinaryRep (n + 1) τ).ρ (toGL ModularGroup.S⁻¹) v := by
  apply Subtype.ext
  show Binary.substitute swapMatrix (v : Binary.HomogeneousPoly (n + 1)).val =
    Binary.action τ (GeneralLinearGroup.map (Int.castRingHom ℂ) (toGL ModularGroup.S⁻¹))
      (v : Binary.HomogeneousPoly (n + 1)).val
  rw [Binary.action_apply, inv_map_S_inv]
  have h : Binary.determinantCharacter τ
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (toGL ModularGroup.S⁻¹)) = 1 := by
    show ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ)
      (toGL ModularGroup.S⁻¹)) : ℂˣ) : ℂ) ^ τ = 1
    rw [det_map_S_inv, _root_.one_zpow]
  rw [h, one_smul]

/-! ### The inverse transpose is conjugation by `S`, up to the center -/

/-- The matrix of `S²` is `-1`. -/
theorem toGL_S_mul_S_val : ((toGL (ModularGroup.S * ModularGroup.S) : GL2Z) :
    Matrix (Fin 2) (Fin 2) ℤ) = -1 := by
  rw [toGL_S_mul_S, GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `S⁴ = 1`. -/
theorem toGL_S_mul_S_mul_self :
    toGL (ModularGroup.S * ModularGroup.S) * toGL (ModularGroup.S * ModularGroup.S) = 1 := by
  apply Units.ext
  rw [Units.val_mul, toGL_S_mul_S_val]
  simp

/-- **The inverse transpose of `GL₂(ℤ)`**: `invT γ · S = S · γ`, or the same after multiplying
by the central element `-1 = S²` (the determinant of `γ` is `1` or `-1`). -/
theorem invT_mul_S (γ : GL2Z) :
    invT γ * toGL ModularGroup.S = toGL ModularGroup.S * γ ∨
      toGL (ModularGroup.S * ModularGroup.S) * invT γ * toGL ModularGroup.S =
        toGL ModularGroup.S * γ := by
  have h1 := mul_invT_transpose γ
  have hu : IsUnit (γ : Matrix (Fin 2) (Fin 2) ℤ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit
  obtain ⟨a, b, c, d, hγ⟩ : ∃ a b c d : ℤ,
      (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  obtain ⟨p, q, r, s, hB⟩ : ∃ p q r s : ℤ,
      ((invT γ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hγ, hB] at h1
  rw [hγ] at hu
  have e1 := congrFun (congrFun h1 0) 0
  have e2 := congrFun (congrFun h1 0) 1
  have e3 := congrFun (congrFun h1 1) 0
  have e4 := congrFun (congrFun h1 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3 e4
  rw [Matrix.det_fin_two_of] at hu
  rcases Int.isUnit_iff.mp hu with hd | hd
  · left
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Units.val_mul, toGL, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two, hγ, hB]
    · linear_combination a * e3 - c * e1 - q * hd
    · linear_combination d * e1 - b * e3 - p * hd
    · linear_combination a * e4 - c * e2 - s * hd
    · linear_combination -d * e2 + b * e4 + r * hd
  · right
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Units.val_mul, toGL, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two, hγ, hB]
    · linear_combination -a * e3 + c * e1 + q * hd
    · linear_combination -d * e1 + b * e3 + p * hd
    · linear_combination a * e4 - c * e2 - s * hd
    · linear_combination -d * e2 + b * e4 + r * hd

/-! ### Crossed homomorphisms -/

section Crossed

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  (f : G → V) (hf : ∀ g h, f (g * h) = f g + ρ g (f h))

include hf in
theorem crossed_one : f 1 = 0 := by
  have h := hf 1 1
  simpa using h

include hf in
/-- The value of a crossed homomorphism at a conjugate. -/
theorem crossed_conj (s γ : G) :
    f (s * γ * s⁻¹) = ρ s (f γ) + (f s - ρ (s * γ * s⁻¹) (f s)) := by
  have h1 := crossed_one ρ f hf
  have h2 := hf s s⁻¹
  rw [mul_inv_cancel, h1] at h2
  have h3 := hf γ s⁻¹
  have h4 := hf s (γ * s⁻¹)
  rw [mul_assoc, h4, h3, map_add]
  have h5 : ρ s (ρ γ (f s⁻¹)) = -ρ (s * γ * s⁻¹) (f s) := by
    have h6 : ρ s (f s⁻¹) = -f s := eq_neg_of_add_eq_zero_right h2.symm
    have h7 : ρ s (ρ γ (f s⁻¹)) = ρ (s * γ * s⁻¹) (ρ s (f s⁻¹)) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        inv_mul_cancel_right]
    rw [h7, h6, map_neg]
  rw [h5]
  simp only [mul_assoc]
  abel

end Crossed

/-! ### The swap pullback is `-1` on cohomology -/

/-- **The swap pullback acts as `-1` on `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det^τ)`**: if
`Z γ = - rot (F (invT γ))` for one-cocycles `F`, `Z`, then `[Z] = -[F]`. -/
theorem swapPullback_projectH1_eq_neg {n : ℕ} (hn : Odd n) (τ : ℤ)
    {F Z : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) τ)}
    (hZ : ∀ γ, Z γ = -binarySwap (n + 1) (F (invT γ))) :
    projectH1 (arithmeticBinaryRep (n + 1) τ) Z =
      -projectH1 (arithmeticBinaryRep (n + 1) τ) F := by
  have hF : ∀ g h, F (g * h) = F g + (arithmeticBinaryRep (n + 1) τ).ρ g (F h) := fun g h =>
    isCocycle_cocycleInclusion (arithmeticBinaryRep (n + 1) τ) F g h
  have hz1 : (arithmeticBinaryRep (n + 1) τ).ρ (toGL (ModularGroup.S * ModularGroup.S)) =
      LinearMap.id :=
    LinearMap.ext fun w => arithmeticBinaryRep_central (n + 1) hn.add_one τ w
  have hFz : F (toGL (ModularGroup.S * ModularGroup.S)) = 0 := by
    have h := hF (toGL (ModularGroup.S * ModularGroup.S)) (toGL (ModularGroup.S * ModularGroup.S))
    rw [toGL_S_mul_S_mul_self, crossed_one (arithmeticBinaryRep (n + 1) τ).ρ F hF, hz1] at h
    simp only [LinearMap.id_apply] at h
    have h2 : (2 : ℂ) • F (toGL (ModularGroup.S * ModularGroup.S)) = 0 := by
      rw [two_smul]
      exact h.symm
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hinvT : ∀ γ, F (invT γ) = F (toGL ModularGroup.S * γ * (toGL ModularGroup.S)⁻¹) := by
    intro γ
    rcases invT_mul_S γ with h | h
    · rw [eq_mul_inv_of_mul_eq h]
    · have h' : toGL (ModularGroup.S * ModularGroup.S) * invT γ =
          toGL ModularGroup.S * γ * (toGL ModularGroup.S)⁻¹ := eq_mul_inv_of_mul_eq h
      rw [← h', hF, hFz, hz1]
      simp
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← map_add, projectH1_eq_zero_iff]
  refine ⟨(arithmeticBinaryRep (n + 1) τ).ρ (toGL ModularGroup.S)⁻¹ (F (toGL ModularGroup.S)),
    fun γ => ?_⟩
  have e1 : ∀ x : arithmeticBinaryRep (n + 1) τ,
      (arithmeticBinaryRep (n + 1) τ).ρ (toGL ModularGroup.S)⁻¹
        ((arithmeticBinaryRep (n + 1) τ).ρ (toGL ModularGroup.S) x) = x := by
    intro x
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e2 : ∀ y : arithmeticBinaryRep (n + 1) τ,
      (arithmeticBinaryRep (n + 1) τ).ρ (toGL ModularGroup.S)⁻¹
        ((arithmeticBinaryRep (n + 1) τ).ρ (toGL ModularGroup.S * γ * (toGL ModularGroup.S)⁻¹) y) =
        (arithmeticBinaryRep (n + 1) τ).ρ γ
          ((arithmeticBinaryRep (n + 1) τ).ρ (toGL ModularGroup.S)⁻¹ y) := by
    intro y
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  change Z γ + F γ = _
  rw [hZ γ, binarySwap_eq_rho, map_inv, hinvT γ,
    crossed_conj (arithmeticBinaryRep (n + 1) τ).ρ F hF]
  simp only [map_add, map_sub, e1, e2]
  abel

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1OddSwap

end
