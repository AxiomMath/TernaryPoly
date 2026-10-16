module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Cosets
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneCusps

@[expose] public section


/-!
# Splitting a sum over rational plane flags by `Γ(N)`-cusp orbits (`N ≥ 3`)

Formalized by Claude Sonnet 5.5.

* `flagCusp : Flags .plane → PlaneFaces N`: the cusp (face) of a rational plane.
* `flag_mem_orbit`, `cusp_unique`: every flag lies in the `Γ(N)`-orbit of `planeFlagAt (out x)` for exactly one `x : PlaneFaces N`.
* `tsum_flags_by_cusp`: `∑' F, f F = ∑ₓ ∑' F in the fiber of x, f F` for summable `f`.
* `stab_planeFlagAt_iff`: the stabilizer of `planeFlagAt h` in `Γ(N)` is `Γ_{h⁻¹Ph}` (`gammaNPAt N h`), for `N ≥ 3`.
* `fiberEquiv`: the fiber of `x` is `Γ(N) ⧸ Γ_{h_x⁻¹Ph_x}`, explicitly (`γ ↦ γ⁻¹`-translate of the plane; well defined and bijective by `stab_planeFlagAt_iff`, `flag_mem_orbit`).
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.SeedC3

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ)

/-- The face (cusp class) of a rational plane. -/
def flagCusp (F : Flags .plane) : PlaneFaces N :=
  Quotient.mk (planeFaceSetoid N) (Classical.choose (planeFlagAt_surjective F))

/-- `Γ(N)` acts on rational flags through `SL₃(ℤ) → GL₃(ℚ)`. -/
@[instance_reducible] def gammaFlagAction : MulAction (gammaN N) (Flags .plane) :=
  MulAction.compHom (Flags .plane) ((Matrix.SpecialLinearGroup.mapGL ℚ).comp (gammaN N).subtype)

theorem planeFlagAt_out_rel (F : Flags .plane) : planeFlagAt (Classical.choose (planeFlagAt_surjective F)) = F :=
  Classical.choose_spec (planeFlagAt_surjective F)

/-- **Every rational plane lies in the `Γ(N)`-orbit of the plane of its cusp representative.** -/
theorem flag_mem_orbit (F : Flags .plane) :
    ∃ γ ∈ gammaN N, F = Matrix.SpecialLinearGroup.mapGL ℚ γ • planeFlagAt (Quotient.out (flagCusp N F)) := by
  have hr : (planeFaceSetoid N).r (Quotient.out (flagCusp N F)) (Classical.choose (planeFlagAt_surjective F)) :=
    Quotient.mk_out (s := planeFaceSetoid N) (Classical.choose (planeFlagAt_surjective F))
  obtain ⟨γ, hγ, e⟩ := (planeFlagAt_orbit_iff N (Quotient.out (flagCusp N F))
    (Classical.choose (planeFlagAt_surjective F))).mpr hr
  exact ⟨γ, hγ, (planeFlagAt_out_rel F).symm.trans e⟩

/-- **The cusp of a flag in the orbit of `x`'s representative is `x`.** -/
theorem cusp_unique (F : Flags .plane) (x : PlaneFaces N) {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N)
    (e : F = Matrix.SpecialLinearGroup.mapGL ℚ γ • planeFlagAt (Quotient.out x)) : flagCusp N F = x := by
  have h1 := (planeFlagAt_orbit_iff N (Quotient.out x) (Classical.choose (planeFlagAt_surjective F))).mp
    ⟨γ, hγ, (planeFlagAt_out_rel F).trans e⟩
  have h2 : (planeFaceSetoid N).r (Quotient.out x) (Classical.choose (planeFlagAt_surjective F)) := h1
  exact (Quotient.sound (s := planeFaceSetoid N) h2).symm.trans (Quotient.out_eq x)

/-- **Fibrewise splitting of a sum over rational plane flags by cusp.** -/
theorem tsum_flags_by_cusp [Fintype (PlaneFaces N)] (f : Flags .plane → ℂ) (hf : Summable f) :
    ∑' F, f F = ∑ x : PlaneFaces N, ∑' F : {F : Flags .plane // flagCusp N F = x}, f F.1 := by
  let e := Equiv.sigmaFiberEquiv (flagCusp N)
  have hs : Summable (f ∘ e) := (e.summable_iff).mpr hf
  have h1 : ∀ x, Summable fun F : {F : Flags .plane // flagCusp N F = x} => f F.1 := fun x =>
    hs.sigma_factor x
  have h2 := hs.tsum_sigma' h1
  exact ((e.tsum_eq f).symm.trans h2).trans
    (tsum_fintype (fun x => ∑' F : {F : Flags .plane // flagCusp N F = x}, f F.1))


theorem smul_planeFlagAt (γ h : SL(3, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℚ γ • planeFlagAt h = planeFlagAt (h * γ⁻¹) := by
  change _ • (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) : Flags .plane) = QuotientGroup.mk _
  change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ γ * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) : Flags .plane) = _
  simp [map_inv, map_mul]

/-- **The stabilizer of the plane `h⁻¹⟨e₁,e₂⟩` in `Γ(N)` is the plane group `Γ_{h⁻¹Ph}`** (`N ≥ 3`). -/
theorem stab_planeFlagAt_iff (hN : 3 ≤ N) (h : SL(3, ℤ)) {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N) :
    Matrix.SpecialLinearGroup.mapGL ℚ γ • planeFlagAt h = planeFlagAt h ↔ γ ∈ gammaNPAt N h := by
  rw [smul_planeFlagAt, planeFlagAt_eq_iff]
  have hx : h * γ⁻¹ * h⁻¹ ∈ gammaN N := by
    have := (gammaN_normal N).conj_mem γ⁻¹ ((gammaN N).inv_mem hγ) h
    simpa [mul_assoc] using this
  constructor
  · intro hb
    have hs : h * γ⁻¹ * h⁻¹ ∈ planeStab := mem_planeStab_of_gammaN hN hx hb.1 hb.2
    have : h * γ * h⁻¹ = (h * γ⁻¹ * h⁻¹)⁻¹ := by group
    rw [mem_gammaNPAt, this]
    exact (gammaNP N).inv_mem ⟨hx, hs⟩
  · intro hp
    rw [mem_gammaNPAt] at hp
    have : h * γ⁻¹ * h⁻¹ = (h * γ * h⁻¹)⁻¹ := by group
    rw [this]
    exact planeBorel.inv_mem ⟨hp.2.1, hp.2.2.1⟩

/-- **The fibre of a cusp `x` is `Γ(N) / Γ_{h_x⁻¹Ph_x}`** (`N ≥ 3`): the rational planes of the cusp `x` are in bijection with the left cosets of the
plane group in `Γ(N)`. -/
def fiberEquiv (hN : 3 ≤ N) (x : PlaneFaces N) :
    (gammaN N ⧸ (gammaNPAt N (Quotient.out x)).subgroupOf (gammaN N)) ≃ {F : Flags .plane // flagCusp N F = x} :=
  Equiv.ofBijective
    (Quotient.lift (fun γ : gammaN N =>
        (⟨Matrix.SpecialLinearGroup.mapGL ℚ γ.1 • planeFlagAt (Quotient.out x),
          cusp_unique N _ x γ.2 rfl⟩ : {F : Flags .plane // flagCusp N F = x})) (by
      intro a b hab
      have h : a⁻¹ * b ∈ (gammaNPAt N (Quotient.out x)).subgroupOf (gammaN N) := QuotientGroup.leftRel_apply.mp hab
      have hh : (a⁻¹ * b).1 ∈ gammaNPAt N (Quotient.out x) := h
      have e := (stab_planeFlagAt_iff N hN (Quotient.out x) (a⁻¹ * b).2).mpr hh
      apply Subtype.ext
      change Matrix.SpecialLinearGroup.mapGL ℚ a.1 • planeFlagAt (Quotient.out x) =
        Matrix.SpecialLinearGroup.mapGL ℚ b.1 • planeFlagAt (Quotient.out x)
      have e' : Matrix.SpecialLinearGroup.mapGL ℚ (a⁻¹ * b).1 • planeFlagAt (Quotient.out x) = planeFlagAt (Quotient.out x) := e
      rw [show (a⁻¹ * b).1 = a.1⁻¹ * b.1 from rfl, map_mul, map_inv] at e'
      have := congrArg (fun F => Matrix.SpecialLinearGroup.mapGL ℚ a.1 • F) e'
      simp only [← mul_smul, mul_inv_cancel_left] at this
      exact this.symm)) (by
    constructor
    · intro p q
      induction p using Quotient.inductionOn with
      | _ a =>
        induction q using Quotient.inductionOn with
        | _ b =>
          intro hab
          have h0 : Matrix.SpecialLinearGroup.mapGL ℚ a.1 • planeFlagAt (Quotient.out x) =
              Matrix.SpecialLinearGroup.mapGL ℚ b.1 • planeFlagAt (Quotient.out x) := congrArg Subtype.val hab
          apply Quotient.sound
          refine QuotientGroup.leftRel_apply.mpr ?_
          change (a⁻¹ * b).1 ∈ gammaNPAt N (Quotient.out x)
          refine (stab_planeFlagAt_iff N hN (Quotient.out x) (a⁻¹ * b).2).mp ?_
          rw [show (a⁻¹ * b).1 = a.1⁻¹ * b.1 from rfl, map_mul, mul_smul, ← h0, ← mul_smul]
          simp
    · rintro ⟨F, hF⟩
      obtain ⟨γ, hγ, e⟩ := flag_mem_orbit N F
      rw [hF] at e
      exact ⟨Quotient.mk _ ⟨γ, hγ⟩, Subtype.ext e.symm⟩)

end TernaryPeriodPolynomials.Argument.FormClassK
