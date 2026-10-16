module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspidalCup
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.MixedCuspidal

@[expose] public section


/-!
# Transfer from Mathlib's `Γ(N) ≤ SL₂(ℤ)` to `Γ(N) ≤ GL₂(ℤ)`

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol CongruenceSubgroup
open scoped Classical MatrixGroups

section Equiv

variable {N : ℕ}

theorem toGL_mem_gammaNGL {γ : SL(2, ℤ)} : Matrix.SpecialLinearGroup.toGL γ ∈ gammaNGL N ↔ γ ∈ Gamma N := by
  rw [mem_gammaNGL, Gamma_mem]
  simp

theorem gammaN_det (hN : 3 ≤ N) (g : gammaNGL N) : ((g : IntegralGL).val).det = 1 := gammaN_isSL hN g.2

/-- The `SL₂(ℤ)` element of an element of `gammaNGL N` (`N ≥ 3`). -/
def toSL (hN : 3 ≤ N) (g : gammaNGL N) : SL(2, ℤ) := ⟨(g : IntegralGL).val, gammaN_det hN g⟩

theorem toSL_apply (hN : 3 ≤ N) (g : gammaNGL N) (i j : Fin 2) : (toSL hN g) i j = (g : IntegralGL).val i j := rfl

theorem toSL_mem (hN : 3 ≤ N) (g : gammaNGL N) : toSL hN g ∈ Gamma N := by
  have := mem_gammaNGL.mp g.2
  rw [Gamma_mem]
  simpa [toSL_apply] using this

/-- `Γ(N) ≤ SL₂(ℤ)` (Mathlib) is the group `gammaNGL N ≤ GL₂(ℤ)` for `N ≥ 3`. -/
def gammaEquiv (hN : 3 ≤ N) : Gamma N ≃* gammaNGL N where
  toFun γ := ⟨Matrix.SpecialLinearGroup.toGL γ.1, toGL_mem_gammaNGL.mpr γ.2⟩
  invFun g := ⟨toSL hN g, toSL_mem hN g⟩
  left_inv γ := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    simp [toSL_apply]
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [toSL_apply]
  map_mul' a b := by
    apply Subtype.ext
    simp

end Equiv


section Cusp

/-- The cusp `F · ∞` of a frame `F ∈ GL₂(ℚ)`. -/
def cuspOf (F : GL (Fin 2) ℚ) : RationalLine2 := lineAction F cusp1

theorem lineAction_cusp1_iff (h : GL (Fin 2) ℚ) :
    lineAction h cusp1 = cusp1 ↔ (h : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by
  have hv : ∀ v, (vectorAction h) v = (h : Matrix (Fin 2) (Fin 2) ℚ).mulVec v := fun v => by simp [vectorAction]
  have hmap : (lineAction h cusp1).val = Submodule.span ℚ {(h : Matrix (Fin 2) (Fin 2) ℚ).mulVec (rationalVector e1)} := by
    change Submodule.map (vectorAction h).toLinearMap (Submodule.span ℚ {rationalVector e1}) = _
    rw [Submodule.map_span, Set.image_singleton]
    simp only [LinearEquiv.coe_coe, hv]
  have he1 : rationalVector e1 = ![1, 0] := by
    funext i; fin_cases i <;> simp [rationalVector, e1]
  have hh : (h : Matrix (Fin 2) (Fin 2) ℚ).mulVec (rationalVector e1) = ![(h : Matrix (Fin 2) (Fin 2) ℚ) 0 0, (h : Matrix (Fin 2) (Fin 2) ℚ) 1 0] := by
    rw [he1]; funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  · intro h1
    have h2 : (lineAction h cusp1).val = Submodule.span ℚ {rationalVector e1} := congrArg Subtype.val h1
    rw [hmap, hh, he1] at h2
    have hmem : ![(h : Matrix (Fin 2) (Fin 2) ℚ) 0 0, (h : Matrix (Fin 2) (Fin 2) ℚ) 1 0] ∈ Submodule.span ℚ {(![1, 0] : Space)} := by
      rw [← h2]; exact Submodule.mem_span_singleton_self _
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have := congrFun hc 1
    simpa using this.symm
  · intro h10
    apply Subtype.ext
    show (lineAction h cusp1).val = Submodule.span ℚ {rationalVector e1}
    rw [hmap, hh, he1]
    have hdet : IsUnit (h : Matrix (Fin 2) (Fin 2) ℚ).det := Matrix.isUnits_det_units h
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    have h00 : (h : Matrix (Fin 2) (Fin 2) ℚ) 0 0 ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hdet; exact not_isUnit_zero hdet
    have : ![(h : Matrix (Fin 2) (Fin 2) ℚ) 0 0, (h : Matrix (Fin 2) (Fin 2) ℚ) 1 0] = (h : Matrix (Fin 2) (Fin 2) ℚ) 0 0 • (![1, 0] : Space) := by
      funext i; fin_cases i <;> simp [h10]
    rw [this, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr h00)]

theorem integral_toGL (γ : SL(2, ℤ)) : integral (Matrix.SpecialLinearGroup.toGL γ) = Matrix.SpecialLinearGroup.mapGL ℚ γ := by
  apply Units.ext
  ext i j
  simp [integral, Matrix.GeneralLinearGroup.map]

theorem toGL_smul_cuspOf_iff (γ : SL(2, ℤ)) (F : GL (Fin 2) ℚ) :
    (Matrix.SpecialLinearGroup.toGL γ : IntegralGL) • cuspOf F = cuspOf F ↔
      ((F⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ γ * F : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by
  rw [← lineAction_cusp1_iff]
  have e1 : (Matrix.SpecialLinearGroup.toGL γ : IntegralGL) • cuspOf F =
      lineAction (Matrix.SpecialLinearGroup.mapGL ℚ γ * F) cusp1 := by
    rw [cusp_smul_def, integral_toGL, cuspOf, ← lineAction_mul]
  rw [e1]
  unfold cuspOf
  constructor
  · intro h
    have := congrArg (lineAction F⁻¹) h
    rwa [← lineAction_mul, ← lineAction_mul, inv_mul_cancel, lineAction_one, ← mul_assoc] at this
  · intro h
    have := congrArg (lineAction F) h
    rw [← lineAction_mul] at this
    rw [show F * (F⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ γ * F) = Matrix.SpecialLinearGroup.mapGL ℚ γ * F by group] at this
    exact this

theorem exists_cuspOf (x : RationalLine2) : ∃ F : GL (Fin 2) ℚ, cuspOf F = x := by
  obtain ⟨g, -, hg⟩ := exists_sl_cusp x
  exact ⟨integral g, by rw [cuspOf]; exact hg⟩

end Cusp

section Theta

variable {N : ℕ}

open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace mem_cuspidalSubspace_π leviCuspStab mem_leviCuspStab_iff)

/-- The restriction of a `Γ(N) ≤ SL₂(ℤ)`-module to `gammaNGL N`, along `gammaEquiv`. -/
abbrev transRep (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) : Rep ℂ (gammaNGL N) :=
  Rep.of (V.ρ.comp (gammaEquiv hN).symm.toMonoidHom)

theorem transRep_ρ (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) (g : gammaNGL N) :
    (transRep hN V).ρ g = V.ρ ((gammaEquiv hN).symm g) := rfl

/-- `H¹(Γ(N), V) ≅ H¹(gammaNGL N, V)`. -/
def thetaIso (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) : groupCohomology V 1 ≅ groupCohomology (transRep hN V) 1 :=
  groupCohomology.mapIso (gammaEquiv hN) (LinearEquiv.refl ℂ V) (fun g => by
    ext v
    simp [transRep]) 1

theorem thetaIso_hom_π (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) (c : groupCohomology.cocycles₁ V) :
    ∃ c' : groupCohomology.cocycles₁ (transRep hN V),
      (∀ g, c'.1 g = c.1 ((gammaEquiv hN).symm g)) ∧
        (thetaIso hN V).hom.hom (groupCohomology.H1π V c) = groupCohomology.H1π (transRep hN V) c' := by
  unfold thetaIso
  rw [groupCohomology.mapIso_hom]
  rw [groupCohomology.H1π_comp_map_apply]
  refine ⟨_, fun g => ?_, rfl⟩
  rfl

theorem gammaEquiv_coe (hN : 3 ≤ N) (γ : Gamma N) :
    (((gammaEquiv hN γ : gammaNGL N)) : IntegralGL) = Matrix.SpecialLinearGroup.toGL γ.1 := rfl

theorem stab_iff (hN : 3 ≤ N) (F : GL (Fin 2) ℚ) (γ : Gamma N) :
    γ ∈ leviCuspStab (Gamma N) F ↔ (((gammaEquiv hN γ : gammaNGL N)) : IntegralGL) • cuspOf F = cuspOf F := by
  rw [mem_leviCuspStab_iff, gammaEquiv_coe, toGL_smul_cuspOf_iff]

/-- **Transfer of the cuspidal subspace**: under `H¹(Γ(N), V) ≅ H¹(gammaNGL N, V)` the literal cuspidal subspace (zero restriction at
every rational cusp of the binary Levi, `leviCuspStab`) corresponds to `cuspidalSub`. -/
theorem theta_mem_cuspidal_iff (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) (x : groupCohomology.H1 V) :
    x ∈ cuspidalSubspace (Gamma N) V ↔ (thetaIso hN V).hom.hom x ∈ cuspidalSub (transRep hN V) := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    obtain ⟨c', hc', hθ⟩ := thetaIso_hom_π hN V c
    rw [hθ, mem_cuspidalSubspace_π, mem_cuspidalSub_π]
    constructor
    · intro h x
      obtain ⟨F, rfl⟩ := exists_cuspOf x
      obtain ⟨u, hu⟩ := h F
      refine ⟨u, fun γ' hγ' => ?_⟩
      have hmem : (gammaEquiv hN).symm γ' ∈ leviCuspStab (Gamma N) F := by
        rw [stab_iff hN, MulEquiv.apply_symm_apply]
        exact hγ'
      have := hu ⟨(gammaEquiv hN).symm γ', hmem⟩
      rw [hc']
      exact this
    · intro h F
      obtain ⟨u, hu⟩ := h (cuspOf F)
      refine ⟨u, fun γ => ?_⟩
      have hmem := (stab_iff hN F γ.1).mp γ.2
      have := hu (gammaEquiv hN γ.1) hmem
      rw [hc', MulEquiv.symm_apply_apply] at this
      exact this

end Theta

section Final

variable {N : ℕ}

open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)

theorem exists_transport {X Y U W : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W] (B' : U →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hl : ∀ u, (∀ w, B' u w = 0) → u = 0) (hr : ∀ w, (∀ u, B' u w = 0) → w = 0)
    (φ : X ≃ₗ[ℂ] U) (ψ : Y ≃ₗ[ℂ] W) :
    ∃ B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ, (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      ∀ x y, B x y = B' (φ x) (ψ y) := by
  refine ⟨(B'.comp φ.toLinearMap).compl₂ ψ.toLinearMap, ?_, ?_, fun x y => rfl⟩
  · intro x hx
    apply φ.injective
    rw [map_zero]
    exact hl _ fun w => by simpa using hx (ψ.symm w)
  · intro y hy
    apply ψ.injective
    rw [map_zero]
    exact hr _ fun u => by simpa using hy (φ.symm u)

/-- The cuspidal subspace of Mathlib's `Γ(N)` as a module equivalent to `cuspidalSub` of the `GL₂(ℤ)`-model. -/
def cuspEquiv (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) : cuspidalSubspace (Gamma N) V ≃ₗ[ℂ] cuspidalSub (transRep hN V) :=
  LinearEquiv.ofSubmodules (thetaIso hN V).toLinearEquiv _ _ (by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (theta_mem_cuspidal_iff hN V x).mp hx
    · intro hz
      refine ⟨(thetaIso hN V).toLinearEquiv.symm z, ?_, by simp⟩
      change (thetaIso hN V).toLinearEquiv.symm z ∈ cuspidalSubspace (Gamma N) V
      rw [theta_mem_cuspidal_iff hN V]
      have h1 := (thetaIso hN V).toLinearEquiv.apply_symm_apply z
      rw [CategoryTheory.Iso.toLinearEquiv_apply] at h1
      rw [h1]
      exact hz)

/-- **Perfect pairing of the literal cuspidal groups of `Γ(N)`** (Mathlib's `CongruenceSubgroup.Gamma N`, `cuspidalSubspace`): for finite
dimensional `Γ(N)`-modules `V`, `V'` with a perfect invariant pairing, the cuspidal subspaces of `H¹` are perfectly paired. -/
theorem cuspidal_pairing_gammaN (hN : 3 ≤ N) (V V' : Rep ℂ (Gamma N)) [FiniteDimensional ℂ V] [FiniteDimensional ℂ V']
    (e : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hinv : ∀ (γ : Gamma N) v w, e (V.ρ γ v) (V'.ρ γ w) = e v w)
    (hL : ∀ v, (∀ w, e v w = 0) → v = 0) (hR : ∀ w, (∀ v, e v w = 0) → w = 0) :
    ∃ B : cuspidalSubspace (Gamma N) V →ₗ[ℂ] cuspidalSubspace (Gamma N) V' →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) := by
  let C : Coupling (transRep hN V).ρ (transRep hN V').ρ :=
    { e := e
      inv := fun γ v w => by
        have := hinv ((gammaEquiv hN).symm γ) v w
        exact this
      left := hL
      right := hR }
  obtain ⟨B', hl, hr, -⟩ := cuspidal_pairing_exists hN (transRep hN V) (transRep hN V') C
  obtain ⟨B, h1, h2, -⟩ := exists_transport B' hl hr (cuspEquiv hN V) (cuspEquiv hN V')
  exact ⟨B, h1, h2⟩

/-- **The pairing is skew**: the pairing of `(V, V')` and that of `(V', V)` are negatives of each other. -/
theorem cuspidal_pairing_gammaN_skew (hN : 3 ≤ N) (V V' : Rep ℂ (Gamma N)) [FiniteDimensional ℂ V] [FiniteDimensional ℂ V']
    (e : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hinv : ∀ (γ : Gamma N) v w, e (V.ρ γ v) (V'.ρ γ w) = e v w)
    (hL : ∀ v, (∀ w, e v w = 0) → v = 0) (hR : ∀ w, (∀ v, e v w = 0) → w = 0) :
    ∃ (B : cuspidalSubspace (Gamma N) V →ₗ[ℂ] cuspidalSubspace (Gamma N) V' →ₗ[ℂ] ℂ)
      (B' : cuspidalSubspace (Gamma N) V' →ₗ[ℂ] cuspidalSubspace (Gamma N) V →ₗ[ℂ] ℂ),
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      (∀ y, (∀ x, B' y x = 0) → y = 0) ∧ (∀ x, (∀ y, B' y x = 0) → x = 0) ∧
      ∀ x y, B x y = - B' y x := by
  let C : Coupling (transRep hN V).ρ (transRep hN V').ρ :=
    { e := e
      inv := fun γ v w => by
        have := hinv ((gammaEquiv hN).symm γ) v w
        exact this
      left := hL
      right := hR }
  obtain ⟨B1, B2, hl1, hr1, hl2, hr2, hsk⟩ := cuspidal_pairing_skew hN (transRep hN V) (transRep hN V') C
  let φ := cuspEquiv hN V
  let ψ := cuspEquiv hN V'
  refine ⟨(B1.comp φ.toLinearMap).compl₂ ψ.toLinearMap, (B2.comp ψ.toLinearMap).compl₂ φ.toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply φ.injective
    rw [map_zero]
    exact hl1 _ fun w => by simpa using hx (ψ.symm w)
  · intro y hy
    apply ψ.injective
    rw [map_zero]
    exact hr1 _ fun u => by simpa using hy (φ.symm u)
  · intro y hy
    apply ψ.injective
    rw [map_zero]
    exact hl2 _ fun w => by simpa using hy (φ.symm w)
  · intro x hx
    apply φ.injective
    rw [map_zero]
    exact hr2 _ fun u => by simpa using hx (ψ.symm u)
  · intro x y
    simpa using hsk (φ x) (ψ y)

end Final

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
