module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreLevelOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneHeckeH1

@[expose] public section


/-!
# Hecke adjointness of the parabolic cup pairing of `GL₂(ℤ)`

For `m` even and `e + e' - m` odd let `π` be the parabolic cup pairing of
`H¹(GL₂(ℤ), Sym^m ⊗ det^e)` with `H¹(GL₂(ℤ), Sym^m ⊗ det^{e'})` (the cup formula of the
restrictions to `SL₂(ℤ)` with the classical pairing of binary forms), and let `T_p` be the Hecke
operator of `GL₂(ℤ) diag(p, 1) GL₂(ℤ)`.  Then on parabolic classes

  `π (T_p x, y) = p^{e' - e} π (x, T_p y)`  (`parabolicPairing_arithmeticHecke`).

The parabolic classes have representatives vanishing at `T` (`exists_normalized_rep`); the
restriction of the Hecke cocycle to `SL₂(ℤ)` is the Hecke cocycle of `SL₂(ℤ)` with the same
representatives (`heckeCocycle_toGL`); the binary pairing satisfies
`B(g_W⁻¹ v, g_W w) = p^{e - e'} B(v, w)` for the Fricke-type element `g_W = α₀⁻¹ S`, because
`g_W² = -1/p` and `det g_W = 1/p` (`binaryPairing_gW`); and the cocycle-level adjointness of
`AdjCoreLevelOne` applies.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjCore

open scoped MatrixGroups
open Matrix TripleModel LinearDuality CocycleBridge EpsilonSplit
open GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne

section Binary

variable (p : Nat.Primes)

/-- The Fricke-type element `g_W` in `GL₂(ℂ)`. -/
abbrev gWC : GL (Fin 2) ℂ := GeneralLinearGroup.map (algebraMap ℚ ℂ) (gW p)

/-- `g_W² = -1/p` in `GL₂(ℂ)`. -/
theorem gWC_mul_gWC :
    gWC p * gWC p = GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 (-((p.val : ℕ) : ℂ)⁻¹)
        (neg_ne_zero.mpr (inv_ne_zero (Nat.cast_ne_zero.mpr p.property.ne_zero)))) := by
  show GeneralLinearGroup.map (algebraMap ℚ ℂ) (gW p) *
    GeneralLinearGroup.map (algebraMap ℚ ℂ) (gW p) = _
  rw [← map_mul, gW_mul_gW p, GeneralLinearGroup.map_scalar]
  congr 1
  apply Units.ext
  simp

/-- `det g_W = 1/p` in `GL₂(ℂ)`. -/
theorem val_det_gWC :
    ((Matrix.GeneralLinearGroup.det (gWC p) : ℂˣ) : ℂ) = ((p.val : ℕ) : ℂ)⁻¹ := by
  rw [GeneralLinearGroup.val_det_apply]
  change ((gW p : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ)).det = _
  rw [gW_val p]
  simp [Matrix.det_fin_two]

/-- **The binary pairing against the Fricke-type element**:
`B(g_W⁻¹ v, g_W w) = p^{e - e'} B(v, w)` for `m` even. -/
theorem binaryPairing_gW (m : ℕ) (hm : Even m) (e e' : ℤ) (v w : Binary.HomogeneousPoly m) :
    BinaryPairing.binaryPairing m (rationalRho m e (gW p)⁻¹ v) (rationalRho m e' (gW p) w) =
      ((p.val : ℕ) : ℂ) ^ (e - e') * BinaryPairing.binaryPairing m v w := by
  have hq : ((p.val : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  change BinaryPairing.binaryPairing m
    (Binary.homogeneousAction m e (GeneralLinearGroup.map (algebraMap ℚ ℂ) (gW p)⁻¹) v)
    (Binary.homogeneousAction m e' (gWC p) w) = _
  rw [map_inv]
  show BinaryPairing.binaryPairing m (Binary.homogeneousAction m e (gWC p)⁻¹ v)
    (Binary.homogeneousAction m e' (gWC p) w) = _
  have h1 := BinaryPairing.binaryPairing_homogeneousAction m e e' (gWC p)
    (Binary.homogeneousAction m e (gWC p)⁻¹ v) (Binary.homogeneousAction m e' (gWC p) w)
  rw [rep_apply_inv (Binary.homogeneousAction m e) (gWC p) v,
    ← rep_mul_apply (Binary.homogeneousAction m e') (gWC p) (gWC p) w, gWC_mul_gWC p,
    binary_homogeneous_action_scalar, map_smul, smul_eq_mul, val_det_gWC p, Units.val_mk0] at h1
  have hX : BinaryPairing.binaryPairing m (Binary.homogeneousAction m e (gWC p)⁻¹ v)
      (Binary.homogeneousAction m e' (gWC p) w) =
      ((p.val : ℕ) : ℂ) ^ (e + e' - (m : ℤ)) *
        (((-((p.val : ℕ) : ℂ)⁻¹) ^ (2 * e') * ((-((p.val : ℕ) : ℂ)⁻¹)⁻¹) ^ m) *
          BinaryPairing.binaryPairing m v w) := by
    rw [h1, ← mul_assoc, _root_.inv_zpow, mul_inv_cancel₀ (zpow_ne_zero _ hq), one_mul]
  rw [hX, Even.neg_zpow (even_two_mul e'), inv_neg, inv_inv, Even.neg_pow hm, _root_.inv_zpow',
    ← zpow_natCast, ← mul_assoc, ← mul_assoc, ← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 2
  ring

end Binary

section Classes

/-- **Parabolic classes have representatives vanishing at `T`.** -/
theorem exists_normalized_rep (M : Rep.{0, 0, 0} ℂ GL2Z) (c : groupCohomology.H1 M)
    (hc : c ∈ parabolicH1 M) :
    ∃ z : groupCohomology.cocycles₁ M, z ∈ parabolicCocycles M ∧ projectH1 M z = c ∧
      cocycleInclusion M z (toGL ModularGroup.T) = 0 := by
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hc
  obtain ⟨u, hu⟩ := (mem_parabolicCocycles_iff M z).mp hz
  obtain ⟨z₀, hz₀⟩ := exists_cocycle_of_isCocycle M
    (fun g => cocycleInclusion M z g - (M.ρ g u - u))
    (isCocycle_sub (isCocycle_cocycleInclusion M z) (isCocycle_boundary M.ρ u))
  have hT : cocycleInclusion M z₀ (toGL ModularGroup.T) = 0 := by
    rw [hz₀]
    simp only [hu, sub_self]
  refine ⟨z₀, (mem_parabolicCocycles_iff M z₀).mpr ⟨0, by rw [hT, map_zero, sub_zero]⟩, ?_, hT⟩
  have hd : projectH1 M (z - z₀) = 0 :=
    (projectH1_eq_zero_iff M (z - z₀)).mpr ⟨u, fun γ => by
      simp only [map_sub, Pi.sub_apply, hz₀]
      abel⟩
  rw [map_sub, sub_eq_zero] at hd
  exact hd.symm

variable (m : ℕ) (e : ℤ) (p : Nat.Primes)

/-- The Hecke cocycle of `GL₂(ℤ)` on the arithmetic binary forms. -/
abbrev arithmeticHeckeCocycle :
    groupCohomology.cocycles₁ (arithmeticBinaryRep m e) →ₗ[ℂ]
      groupCohomology.cocycles₁ (arithmeticBinaryRep m e) :=
  heckeCocycle (arithmeticCosets p) (arithmeticBinaryRep m e) (rationalRho m e)
    (arithmetic_compat m e) integralEmbed_injective

/-- **The restriction to `SL₂(ℤ)` of the Hecke cocycle of `GL₂(ℤ)`** is the Hecke cocycle of
`SL₂(ℤ)` of the restriction. -/
theorem heckeCocycle_toGL (z : groupCohomology.cocycles₁ (arithmeticBinaryRep m e))
    (n : SL(2, ℤ)) :
    cocycleInclusion (arithmeticBinaryRep m e) (arithmeticHeckeCocycle m e p z) (toGL n) =
      heckeFun (modularCosets p) (modularBinaryRep m e) (modularRho m e)
        (fun k => cocycleInclusion (arithmeticBinaryRep m e) z (toGL k)) n := by
  change ∑ j, rationalRho m e (binaryHeckeRepresentative p j)⁻¹
      (z (arithmeticDelta p (SpecialLinearGroup.toGL n) j)) =
    ∑ j, modularRho m e (binaryHeckeRepresentative p j)⁻¹
      (z (SpecialLinearGroup.toGL (modularDelta p n j)))
  simp only [toGL_modularDelta]
  rfl

/-- The class of the Hecke cocycle is the Hecke image of the class. -/
theorem projectH1_arithmeticHeckeCocycle (z : groupCohomology.cocycles₁ (arithmeticBinaryRep m e)) :
    arithmeticHecke m e p (projectH1 (arithmeticBinaryRep m e) z) =
      projectH1 (arithmeticBinaryRep m e) (arithmeticHeckeCocycle m e p z) :=
  heckeH1_H1π (arithmeticCosets p) (arithmeticBinaryRep m e) (rationalRho m e)
    (arithmetic_compat m e) integralEmbed_injective z

/-- The Hecke cocycle of a cocycle vanishing at `T` vanishes at `T`. -/
theorem arithmeticHeckeCocycle_T (z : groupCohomology.cocycles₁ (arithmeticBinaryRep m e))
    (hzT : cocycleInclusion (arithmeticBinaryRep m e) z (toGL ModularGroup.T) = 0) :
    cocycleInclusion (arithmeticBinaryRep m e) (arithmeticHeckeCocycle m e p z)
      (toGL ModularGroup.T) = 0 := by
  rw [heckeCocycle_toGL]
  exact heckeFun_T_eq_zero p (isCocycle_comp (isCocycle_cocycleInclusion _ z) toGL) hzT

/-- The Hecke cocycle of a cocycle vanishing at `T` is parabolic. -/
theorem arithmeticHeckeCocycle_mem (z : groupCohomology.cocycles₁ (arithmeticBinaryRep m e))
    (hzT : cocycleInclusion (arithmeticBinaryRep m e) z (toGL ModularGroup.T) = 0) :
    arithmeticHeckeCocycle m e p z ∈ parabolicCocycles (arithmeticBinaryRep m e) :=
  (mem_parabolicCocycles_iff _ _).mpr
    ⟨0, by rw [arithmeticHeckeCocycle_T m e p z hzT, map_zero, sub_zero]⟩

/-- A cocycle of `SL₂(ℤ)` vanishing at `T` has a primitive triple. -/
theorem exists_primitive_of_T_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ SL(2, ℤ) V} {z : SL(2, ℤ) → V} (hz : IsCocycle ρ z)
    (hzT : z ModularGroup.T = 0) :
    ∃ v : V × V × V, IsPrimitive ρ ModularGroup.S ModularGroup.T⁻¹ z v :=
  exists_primitive_of_cusp hz ⟨0, by rw [hzT, map_zero]⟩

end Classes

/-- **Hecke adjointness of the parabolic cup pairing of `GL₂(ℤ)`**: for `m` even and `e + e' - m`
odd, `π (T_p x, y) = p^{e' - e} π (x, T_p y)` on parabolic classes. -/
theorem parabolicPairing_arithmeticHecke (m : ℕ) (e e' : ℤ) (hm : Even m)
    (hodd : Odd (e + e' - (m : ℤ))) (p : Nat.Primes)
    (c : parabolicH1 (arithmeticBinaryRep m e)) (c' : parabolicH1 (arithmeticBinaryRep m e'))
    (hTc : arithmeticHecke m e p c ∈ parabolicH1 (arithmeticBinaryRep m e))
    (hTc' : arithmeticHecke m e' p c' ∈ parabolicH1 (arithmeticBinaryRep m e')) :
    parabolicPairing (twistedPairing_arithmeticBinaryRep m e e' hm hodd) ⟨_, hTc⟩ c' =
      ((p.val : ℕ) : ℂ) ^ (e' - e) *
        parabolicPairing (twistedPairing_arithmeticBinaryRep m e e' hm hodd) c ⟨_, hTc'⟩ := by
  set P := twistedPairing_arithmeticBinaryRep m e e' hm hodd with hP
  obtain ⟨z, hz, hzc, hzT⟩ := exists_normalized_rep (arithmeticBinaryRep m e) c.1 c.2
  obtain ⟨z', hz', hzc', hzT'⟩ := exists_normalized_rep (arithmeticBinaryRep m e') c'.1 c'.2
  have hH := arithmeticHeckeCocycle_mem m e p z hzT
  have hH' := arithmeticHeckeCocycle_mem m e' p z' hzT'
  have hx := isCocycle_comp (isCocycle_cocycleInclusion _ z) toGL
  have hy := isCocycle_comp (isCocycle_cocycleInclusion _ z') toGL
  have hHx := isCocycle_comp (isCocycle_cocycleInclusion _ (arithmeticHeckeCocycle m e p z)) toGL
  obtain ⟨v, hv⟩ := exists_primitive_of_T_eq_zero hHx (arithmeticHeckeCocycle_T m e p z hzT)
  obtain ⟨v₀, hv₀⟩ := exists_primitive_of_T_eq_zero hx hzT
  -- the left side
  have L : parabolicPairing P ⟨_, hTc⟩ c' =
      cupFormula (BinaryPairing.binaryPairing m)
        ((arithmeticBinaryRep m e').ρ.comp toGL) ModularGroup.S ModularGroup.T⁻¹
        (fun n => cocycleInclusion _ (arithmeticHeckeCocycle m e p z) (toGL n))
        (fun n => cocycleInclusion _ z' (toGL n)) v := by
    have e1 : (⟨_, hTc⟩ : parabolicH1 (arithmeticBinaryRep m e)) =
        ⟨projectH1 _ (arithmeticHeckeCocycle m e p z), Submodule.mem_map_of_mem hH⟩ :=
      Subtype.ext (by
        show arithmeticHecke m e p (c : groupCohomology.H1 (arithmeticBinaryRep m e)) = _
        rw [← hzc]
        exact projectH1_arithmeticHeckeCocycle m e p z)
    have e2 : c' = ⟨projectH1 _ z', Submodule.mem_map_of_mem hz'⟩ := Subtype.ext hzc'.symm
    rw [e1, e2]
    exact parabolicPairing_apply P _ z' hH hz' hv
  -- the right side
  have R : parabolicPairing P c ⟨_, hTc'⟩ =
      cupFormula (BinaryPairing.binaryPairing m)
        ((arithmeticBinaryRep m e').ρ.comp toGL) ModularGroup.S ModularGroup.T⁻¹
        (fun n => cocycleInclusion _ z (toGL n))
        (fun n => cocycleInclusion _ (arithmeticHeckeCocycle m e' p z') (toGL n)) v₀ := by
    have e3 : (⟨_, hTc'⟩ : parabolicH1 (arithmeticBinaryRep m e')) =
        ⟨projectH1 _ (arithmeticHeckeCocycle m e' p z'), Submodule.mem_map_of_mem hH'⟩ :=
      Subtype.ext (by
        show arithmeticHecke m e' p (c' : groupCohomology.H1 (arithmeticBinaryRep m e')) = _
        rw [← hzc']
        exact projectH1_arithmeticHeckeCocycle m e' p z')
    have e4 : c = ⟨projectH1 _ z, Submodule.mem_map_of_mem hz⟩ := Subtype.ext hzc.symm
    rw [e3, e4]
    exact parabolicPairing_apply P z _ hz hH' hv₀
  have hfun : (fun n => cocycleInclusion _ (arithmeticHeckeCocycle m e p z) (toGL n)) =
      heckeFun (modularCosets p) (modularBinaryRep m e) (modularRho m e)
        (fun n => cocycleInclusion _ z (toGL n)) := funext (heckeCocycle_toGL m e p z)
  have hfun' : (fun n => cocycleInclusion _ (arithmeticHeckeCocycle m e' p z') (toGL n)) =
      heckeFun (modularCosets p) (modularBinaryRep m e') (modularRho m e')
        (fun n => cocycleInclusion _ z' (toGL n)) := funext (heckeCocycle_toGL m e' p z')
  rw [hfun] at L hv
  rw [hfun'] at R
  have hinv : ∀ (n : SL(2, ℤ)) (a : modularBinaryRep m e) (b : modularBinaryRep m e'),
      BinaryPairing.binaryPairing m ((modularBinaryRep m e).ρ n a) ((modularBinaryRep m e').ρ n b) =
        BinaryPairing.binaryPairing m a b := fun n a b => P.special n a b
  have core := cupFormula_hecke_adjoint_core p (A := modularBinaryRep m e)
    (A' := modularBinaryRep m e') (modular_compat m e) (modular_compat m e') hinv
    (((p.val : ℕ) : ℂ) ^ (e - e')) (binaryPairing_gW p m hm e e') hx hzT hy hzT' hv hv₀
  have core' : cupFormula (BinaryPairing.binaryPairing m)
      ((arithmeticBinaryRep m e').ρ.comp toGL) ModularGroup.S ModularGroup.T⁻¹
        (fun n => cocycleInclusion _ z (toGL n))
        (heckeFun (modularCosets p) (modularBinaryRep m e') (modularRho m e')
          (fun n => cocycleInclusion _ z' (toGL n))) v₀ =
      ((p.val : ℕ) : ℂ) ^ (e - e') * cupFormula (BinaryPairing.binaryPairing m)
        ((arithmeticBinaryRep m e').ρ.comp toGL) ModularGroup.S ModularGroup.T⁻¹
        (heckeFun (modularCosets p) (modularBinaryRep m e) (modularRho m e)
          (fun n => cocycleInclusion _ z (toGL n)))
        (fun n => cocycleInclusion _ z' (toGL n)) v := core
  have hq : ((p.val : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  rw [L, R, core', ← mul_assoc, ← zpow_add₀ hq, show e' - e + (e - e') = 0 by ring, zpow_zero,
    one_mul]

end TernaryPeriodPolynomials.BoundaryDuality.AdjCore
