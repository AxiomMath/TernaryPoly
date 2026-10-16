module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Cob

@[expose] public section


/-!
# The cup formulas of the Hecke cocycles as sums of local terms on the stabilizer

Let `D = (x, y)` be a pair of normalized parabolic crossed homomorphisms (`Data`).  If `θ'` is a cup
primitive of `(x', y|_H)` on the stabilizer `H` of the base coset (`x'` the base cocycle of `x`),
`lhs_value` expresses the cup formula of `(T x, y)` as

  `(loc θ' (T^p) u₁ + loc θ' (r_∞ T r_∞⁻¹) u₂) - (loc θ' L u₃ + loc θ' (r_∞ L^p r_∞⁻¹) u₄)`;

if `θ''` is a cup primitive of `(x|_H, y')`, `rhs_value` expresses the cup formula of `(x, T y)` in
the same way.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets
open TernaryPeriodPolynomials.BoundaryDuality.AdjCore
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (rationalRho
  level_compat core_compat crossedHeckeFun_mem)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep coreRep)
open GeneralEisenstein
open TripleModel LinearDuality CocycleBridge EpsilonSplit

section Facts

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

theorem card_index : Fintype.card (SK p hp3).index = p.val + 1 := by
  change Fintype.card (Option (Fin p.val)) = _
  simp

theorem lastIdx_ne_none : (some (lastIdx p) : Option (Fin p.val)) ≠ none := Option.some_ne_none _

theorem tr_T_other (j : Option (Fin p.val)) (h1 : j ≠ some (lastIdx p)) (h2 : j ≠ none) :
    tr p hp3 coreT j = 1 := by
  cases j with
  | none => exact absurd rfl h2
  | some b =>
    apply tr_T_some
    have hb : b.val ≠ p.val - 1 := fun h => h1 (by rw [show b = lastIdx p from Fin.ext h])
    have := b.isLt
    omega

theorem rK_last : rK p hp3 (some (lastIdx p)) = coreT ^ (p.val - 1) :=
  rK_some_pow p hp3 (p.val - 1) (Nat.sub_lt p.property.pos one_pos)

theorem none_ne_J0 : (none : Option (Fin p.val)) ≠ J0 p := (Option.some_ne_none _).symm

end Facts

section Sums

variable {m : ℕ} {e e' : ℤ} (D : Data m e e') (p : Nat.Primes) (hp3 : p.val ≠ 3)

theorem xBase_isCocycle :
    IsCocycle ((coreRep m e).comp (HK p hp3).subtype) (xBase D p hp3) :=
  isCocycle_baseCocycle (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e))
    (rationalRho m e) (core_compat m e) coreEmbed_injective (isCocycle_restr m e D.hx)

theorem yBase_isCocycle :
    IsCocycle ((coreRep m e').comp (HK p hp3).subtype) (yBase D p hp3) :=
  isCocycle_baseCocycle (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e'))
    (rationalRho m e') (core_compat m e') coreEmbed_injective (isCocycle_restr m e' D.hy)

theorem xH_isCocycle : IsCocycle ((coreRep m e).comp (HK p hp3).subtype) (fun h : HK p hp3 => D.x h.1.1) :=
  ParabolicDuality.isCocycle_comp (isCocycle_restr m e D.hx) (HK p hp3).subtype

theorem yH_isCocycle :
    IsCocycle ((coreRep m e').comp (HK p hp3).subtype) (fun h : HK p hp3 => D.y h.1.1) :=
  ParabolicDuality.isCocycle_comp (isCocycle_restr m e' D.hy) (HK p hp3).subtype

/-- The cup primitive of `(T x, y)` built from the cup primitive `θ'` on `H`. -/
def LPrim (θ' : HK p hp3 → ℂ) : core → ℂ := fun g =>
  ∑ j, leftTerm (rK p hp3) (rK_spec p hp3) (Bm m) (coreRep m e') (xBase D p hp3) (restr D.y) θ' g j +
    Bm m (heckeCorrection (S := SK p hp3) (A := Rep.of (coreRep m e)) (J0 p) (rK p hp3)
      (rationalRho m e) (restr D.x)) (restr D.y g)

/-- The cup primitive of `(x, T y)` built from the cup primitive `θ''` on `H`. -/
def RPrim (θ'' : HK p hp3 → ℂ) : core → ℂ := fun g =>
  ∑ j, rightTerm (rK p hp3) (rK_spec p hp3) (Bm m) (restr D.x) (yBase D p hp3) θ'' g j -
    Bm m (restr D.x g) (coreRep m e' g (heckeCorrection (S := SK p hp3)
      (A := Rep.of (coreRep m e')) (J0 p) (rK p hp3) (rationalRho m e') (restr D.y)))

include D in
/-- **The cup formula of `(T x, y)`** as a sum of local terms of a cup primitive on `H`. -/
theorem lhs_value {θ' : HK p hp3 → ℂ}
    (hθ' : IsCupPrimitive (Bm m) ((coreRep m e').comp (HK p hp3).subtype) (xBase D p hp3)
      (fun h : HK p hp3 => D.y h.1.1) θ')
    {v : Binary.HomogeneousPoly m × Binary.HomogeneousPoly m × Binary.HomogeneousPoly m}
    (hv : IsPrimitive (coreRep m e) coreT coreL⁻¹ (hX D p hp3) v)
    {u₁ u₂ u₃ u₄ : Binary.HomogeneousPoly m}
    (hu₁ : xBase D p hp3 (TpK p hp3) = (coreRep m e (TpK p hp3).1 - 1) u₁)
    (hu₂ : xBase D p hp3 (tK2 p hp3) = (coreRep m e (tK2 p hp3).1 - 1) u₂)
    (hu₃ : xBase D p hp3 (LK p hp3) = (coreRep m e (LK p hp3).1 - 1) u₃)
    (hu₄ : xBase D p hp3 (tL2 p hp3) = (coreRep m e (tL2 p hp3).1 - 1) u₄) :
    cupFormula (Bm m) (coreRep m e') coreT coreL⁻¹ (hX D p hp3) (restr D.y) v =
      (localTerm (Bm m) θ' (fun h : HK p hp3 => D.y h.1.1) (TpK p hp3) u₁ +
        localTerm (Bm m) θ' (fun h : HK p hp3 => D.y h.1.1) (tK2 p hp3) u₂) -
      (localTerm (Bm m) θ' (fun h : HK p hp3 => D.y h.1.1) (LK p hp3) u₃ +
        localTerm (Bm m) θ' (fun h : HK p hp3 => D.y h.1.1) (tL2 p hp3) u₄) := by
  have hxc := isCocycle_restr m e D.hx
  have hyc := isCocycle_restr m e' D.hy
  have hΘ : IsCupPrimitive (Bm m) (coreRep m e') (hX D p hp3) (restr D.y) (LPrim D p hp3 θ') :=
    isCupPrimitive_heckeFun_left (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e))
      (A' := Rep.of (coreRep m e')) (B := Bm m) (rK p hp3) (rK_spec p hp3) (hinvK m e e')
      (rationalRho m e) (core_compat m e) coreEmbed_injective hxc hyc hθ'
  rw [cupFormula_core_eq (hinvK m e e') (isCocycle_hX D p hp3) hyc hΘ hv]
  obtain ⟨uy, huy⟩ := D.hyT
  have hT : localTerm (Bm m) (LPrim D p hp3 θ') (restr D.y) coreT v.1 =
      localTerm (Bm m) θ' (fun h : HK p hp3 => D.y h.1.1) (TpK p hp3) u₁ +
        localTerm (Bm m) θ' (fun h : HK p hp3 => D.y h.1.1) (tK2 p hp3) u₂ := by
    have hfun := heckeFun_two (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e))
      (rK p hp3) (rK_spec p hp3) (rationalRho m e) (core_compat m e) coreEmbed_injective hxc
      (g := coreT) (m := p.val - 1) (jl := some (lastIdx p)) (ji := none)
      (lastIdx_ne_none p) (tr_T_other p hp3) (rK_base p hp3) (next_T_last p hp3)
      (next_T_none p hp3) (rK_last p hp3) hu₁ hu₂
    rw [localTerm_eq_of_primitive (hinvK m e e') hv.1 hfun huy]
    exact heckeLeft_localTerm_two (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e))
      (A' := Rep.of (coreRep m e')) (B := Bm m) (rK p hp3) (rK_spec p hp3) (hinvK m e e')
      (rationalRho m e) (core_compat m e) coreEmbed_injective hxc hyc hθ'
      (lastIdx_ne_none p) (tr_T_other p hp3) (rK_base p hp3) (next_T_last p hp3)
      (next_T_none p hp3) (rK_last p hp3) hu₂
  have hL : localTerm (Bm m) (LPrim D p hp3 θ') (restr D.y) coreL v.2.1 =
      localTerm (Bm m) θ' (fun h : HK p hp3 => D.y h.1.1) (LK p hp3) u₃ +
        localTerm (Bm m) θ' (fun h : HK p hp3 => D.y h.1.1) (tL2 p hp3) u₄ :=
    heckeLeft_localTerm_cycle (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e))
      (A' := Rep.of (coreRep m e')) (B := Bm m) (rK p hp3) (rK_spec p hp3) (hinvK m e e')
      (rationalRho m e) p.property (card_index p hp3) hyc (xBase_isCocycle D p hp3) hθ' (g := coreL) D.hyL
      (next_L_iff p hp3) (next_Lpow p hp3) (none_ne_J0 p) hu₃ hu₄ v.2.1
  rw [hT, hL]

include D in
/-- **The cup formula of `(x, T y)`** as a sum of local terms of a cup primitive on `H`. -/
theorem rhs_value {θ'' : HK p hp3 → ℂ}
    (hθ'' : IsCupPrimitive (Bm m) ((coreRep m e').comp (HK p hp3).subtype)
      (fun h : HK p hp3 => D.x h.1.1) (yBase D p hp3) θ'')
    {w : Binary.HomogeneousPoly m × Binary.HomogeneousPoly m × Binary.HomogeneousPoly m}
    (hw : IsPrimitive (coreRep m e) coreT coreL⁻¹ (restr D.x) w)
    (hYL : CobAt (coreRep m e') (hY D p hp3) coreL) :
    cupFormula (Bm m) (coreRep m e') coreT coreL⁻¹ (restr D.x) (hY D p hp3) w =
      (localTerm (Bm m) θ'' (yBase D p hp3) (TpK p hp3) w.1 +
        localTerm (Bm m) θ'' (yBase D p hp3) (tK2 p hp3)
          (coreRep m e (rK p hp3 none) w.1 - restr D.x (rK p hp3 none))) -
      (localTerm (Bm m) θ'' (yBase D p hp3) (LK p hp3) (-restr D.x (rK p hp3 (J0 p))) +
        localTerm (Bm m) θ'' (yBase D p hp3) (tL2 p hp3) (-restr D.x (rK p hp3 none))) := by
  have hxc := isCocycle_restr m e D.hx
  have hyc := isCocycle_restr m e' D.hy
  have hΘ : IsCupPrimitive (Bm m) (coreRep m e') (restr D.x) (hY D p hp3) (RPrim D p hp3 θ'') :=
    isCupPrimitive_heckeFun_right (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e))
      (A' := Rep.of (coreRep m e')) (B := Bm m) (rK p hp3) (rK_spec p hp3) (hinvK m e e')
      (rationalRho m e') (core_compat m e') coreEmbed_injective hxc hyc hθ''
  rw [cupFormula_core_eq (hinvK m e e') hxc (isCocycle_hY D p hp3) hΘ hw]
  have hT : localTerm (Bm m) (RPrim D p hp3 θ'') (hY D p hp3) coreT w.1 =
      localTerm (Bm m) θ'' (yBase D p hp3) (TpK p hp3) w.1 +
        localTerm (Bm m) θ'' (yBase D p hp3) (tK2 p hp3)
          (coreRep m e (rK p hp3 none) w.1 - restr D.x (rK p hp3 none)) :=
    heckeRight_localTerm_two (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e))
      (A' := Rep.of (coreRep m e')) (B := Bm m) (rK p hp3) (rK_spec p hp3) (hinvK m e e')
      (rationalRho m e') (core_compat m e') coreEmbed_injective hxc hyc hθ''
      (lastIdx_ne_none p) (tr_T_other p hp3) (rK_last p hp3) hw.1
  obtain ⟨wy, hwy⟩ := hYL
  have hL : localTerm (Bm m) (RPrim D p hp3 θ'') (hY D p hp3) coreL w.2.1 =
      localTerm (Bm m) θ'' (yBase D p hp3) (LK p hp3) (-restr D.x (rK p hp3 (J0 p))) +
        localTerm (Bm m) θ'' (yBase D p hp3) (tL2 p hp3) (-restr D.x (rK p hp3 none)) :=
    heckeRight_localTerm_cycle (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e))
      (A' := Rep.of (coreRep m e')) (B := Bm m) (rK p hp3) (rK_spec p hp3) (hinvK m e e')
      (rationalRho m e') p.property (card_index p hp3) hxc (yBase_isCocycle D p hp3) hθ'' (g := coreL) D.hxL
      (next_L_iff p hp3) (next_Lpow p hp3) (none_ne_J0 p) hwy (primitive_of_inv hxc hw.2.1)
  rw [hT, hL]

end Sums

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
