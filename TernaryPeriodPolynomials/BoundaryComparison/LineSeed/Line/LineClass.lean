module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.Datum

@[expose] public section


/-!
# The closed-form cocycle of the line seed (LS8)

With the moment primitives normalized by `G_j(i) = 0`, the zig-zag cochain of the line seed is `c(g,k) = θ_g(k·i)`, i.e.
`c(g,k) = Σ_j C(n,j)(-1)^{n-j} (v₀(g) G_{j+1}(k·i) + v₁(g) G_j(k·i)) ρ(g)(Z^j Y^{n-j})`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3.Psi

namespace LineData

variable {G : Type} [Group G] (D : LineData G) (h : ℂ → ℂ) (n : ℕ) (Gm : ℕ → ℂ → ℂ)

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- **The zig-zag cochain, pointwise**: `c(g,k) = θ_g(k x) + ρ(g)θ_k(x) - θ_{gk}(x)`. -/
theorem cochain_eval (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) (g k : G) {x : Face}
    (hx : x ∈ faceSet) :
    cochain (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
        (D.seedDatum h n Gm hh hG hmod) g k =
      D.thetaFun n Gm g (D.act k x) + D.rhoCoef n g (D.thetaFun n Gm k x) -
        D.thetaFun n Gm (g * k) x := by
  have e := c_cochain (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
    (D.seedDatum h n Gm hh hG hmod) g k
  have hax : D.act k x ∈ faceSet := D.act_mapsTo k hx
  have e2 := congrArg (fun w : Form (F := Coef n) faceSet 0 => (w : RawForm Face (Coef n) 0) x) e
  apply (zeroEquiv (E := Face) (F := Coef n)).injective
  simp only [deRhamConstant, constant, LinearMap.coe_mk, AddHom.coe_mk,
    ofFunction_apply _ _ hx] at e2
  have hsum : ∀ A B C : Form (F := Coef n) faceSet 0,
      ((A + B - C : Form (F := Coef n) faceSet 0) : RawForm Face (Coef n) 0) x =
        (A : RawForm Face (Coef n) 0) x + (B : RawForm Face (Coef n) 0) x -
          (C : RawForm Face (Coef n) 0) x := fun _ _ _ => rfl
  refine e2.trans ?_
  rw [hsum, pullForm_apply isOpen_faceSet D.action k _ hx, pullRaw_zero, twForm_apply]
  have t1 : ((D.seedDatum h n Gm hh hG hmod).θ g : RawForm Face (Coef n) 0) (D.action.act k x) =
      zeroEquiv (D.thetaFun n Gm g (D.act k x)) :=
    ofFunction_apply (D.thetaFun n Gm g) (D.thetaFun_contDiffOn h n Gm g hG) hax
  have t2 : ((D.seedDatum h n Gm hh hG hmod).θ k : RawForm Face (Coef n) 0) x =
      zeroEquiv (D.thetaFun n Gm k x) :=
    ofFunction_apply (D.thetaFun n Gm k) (D.thetaFun_contDiffOn h n Gm k hG) hx
  have t3 : ((D.seedDatum h n Gm hh hG hmod).θ (g * k) : RawForm Face (Coef n) 0) x =
      zeroEquiv (D.thetaFun n Gm (g * k) x) :=
    ofFunction_apply (D.thetaFun n Gm (g * k)) (D.thetaFun_contDiffOn h n Gm (g * k) hG) hx
  rw [t1, t2, t3]
  simp only [map_add, map_sub]
  congr 2

omit h in
theorem thetaFun_basePt (hG0 : ∀ j, Gm j Complex.I = 0) (g : G) :
    D.thetaFun n Gm g PlaneData.basePt = 0 := by
  simp [thetaFun, thetaScalar, PlaneData.faceTau_basePt, hG0]

omit h in
theorem faceTau_act_basePt (k : G) : faceTau (D.act k PlaneData.basePt) = mob (D.lam k) Complex.I := by
  rw [D.faceTau_act, PlaneData.faceTau_basePt]

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- **The closed-form cocycle of the line seed** (normalized primitives `G_j(i) = 0`): `c(g,k) = θ_g(k·i)`. -/
theorem toPoly_cochain (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z) (hG0 : ∀ j, Gm j Complex.I = 0)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) (g k : G) :
    Coef.toPoly (cochain (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
        (D.seedDatum h n Gm hh hG hmod) g k) =
      ∑ j ∈ Finset.range (n + 1),
        C ((n.choose j : ℂ) * (-1) ^ (n - j) *
            ((D.v g 0 : ℂ) * Gm (j + 1) (mob (D.lam k) Complex.I) +
              (D.v g 1 : ℂ) * Gm j (mob (D.lam k) Complex.I))) *
          rho (D.lmat g) (X 2 ^ j * X 1 ^ (n - j)) := by
  rw [D.cochain_eval h n Gm hh hG hmod g k PlaneData.basePt_mem, Coef.toPoly_sub, Coef.toPoly_add,
    D.thetaFun_basePt n Gm hG0 k, D.thetaFun_basePt n Gm hG0 (g * k), map_zero, Coef.toPoly_zero,
    add_zero, sub_zero, D.toPoly_thetaFun n Gm, faceTau_act_basePt]

end LineData

end TernaryPeriodPolynomials.Argument.LineSeed
