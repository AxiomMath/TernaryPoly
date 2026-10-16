module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Average

@[expose] public section


/-!
# The torus average as a linear map on invariant closed forms

`avForm_add`, `avForm_smul`: the average is `ℝ`-linear. `avInv hL` (for `hL : LatticeData D c`) is the
linear map `invClosed → invClosed` on the closed `D`-invariant forms of the face given by the torus
average (closed: `d_avForm`; invariant: `pullForm_avForm`).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory
open scoped ContDiff MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPoly.SmoothCoveringDeRham

variable (n : ℕ) (c : ℝ)

theorem avIntegrand_add (F F' : Form (F := Coef n) faceSet 2) (p : (Face × ℝ) × ℝ) :
    avIntegrand n c (F + F') p = avIntegrand n c F p + avIntegrand n c F' p := by
  simp [avIntegrand, map_add]

theorem avIntegrand_smul (r : ℝ) (F : Form (F := Coef n) faceSet 2) (p : (Face × ℝ) × ℝ) :
    avIntegrand n c (r • F) p = r • avIntegrand n c F p := by
  simp [avIntegrand, map_smul]

theorem iterIntegral_add {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    (g h : ℝ → ℝ → A) (hg : Continuous (Function.uncurry g)) (hh : Continuous (Function.uncurry h)) :
    (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, (g a b + h a b)) =
      (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, g a b) + ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, h a b := by
  have hin : ∀ (k : ℝ → ℝ → A), Continuous (Function.uncurry k) → ∀ a,
      IntervalIntegrable (fun b => k a b) volume 0 1 := fun k hk a =>
    (hk.comp (Continuous.prodMk_right a)).intervalIntegrable 0 1
  have hcont : ∀ (k : ℝ → ℝ → A), Continuous (Function.uncurry k) →
      Continuous fun a => ∫ b in (0:ℝ)..1, k a b := fun k hk =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hk 0 1
  have : (fun a : ℝ => ∫ b in (0:ℝ)..1, (g a b + h a b)) =
      fun a => (∫ b in (0:ℝ)..1, g a b) + ∫ b in (0:ℝ)..1, h a b := by
    funext a
    exact intervalIntegral.integral_add (hin g hg a) (hin h hh a)
  rw [this]
  exact intervalIntegral.integral_add ((hcont g hg).intervalIntegrable 0 1)
    ((hcont h hh).intervalIntegrable 0 1)

theorem continuous_avIntegrand_uncurry (F : Form (F := Coef n) faceSet 2) {x : Face}
    (hx : x ∈ faceSet) :
    Continuous (Function.uncurry fun a b : ℝ => avIntegrand n c F ((x, a), b)) := by
  have key : ∀ (f : (Face × ℝ) × ℝ → Face [⋀^Fin 2]→L[ℝ] Coef n),
      Continuous (fun t : Fin 2 → ℝ => f ((x, t 0), t 1)) →
        Continuous (Function.uncurry fun a b : ℝ => f ((x, a), b)) := fun f h =>
    h.comp (show Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ) by fun_prop)
  exact key (avIntegrand n c F) (avIntegrand_continuous n c F hx)

theorem avRaw_add (F F' : Form (F := Coef n) faceSet 2) {x : Face} (hx : x ∈ faceSet) :
    avRaw n c (F + F') x = avRaw n c F x + avRaw n c F' x := by
  unfold avRaw
  simp only [avIntegrand_add]
  exact iterIntegral_add (fun a b => avIntegrand n c F ((x, a), b))
    (fun a b => avIntegrand n c F' ((x, a), b)) (continuous_avIntegrand_uncurry n c F hx)
    (continuous_avIntegrand_uncurry n c F' hx)

theorem avRaw_smul (r : ℝ) (F : Form (F := Coef n) faceSet 2) (x : Face) :
    avRaw n c (r • F) x = r • avRaw n c F x := by
  unfold avRaw
  simp only [avIntegrand_smul, intervalIntegral.integral_smul]

theorem avForm_add (F F' : Form (F := Coef n) faceSet 2) :
    avForm n c (F + F') = avForm n c F + avForm n c F' := by
  apply Form.ext
  intro x hx
  rw [avForm_apply n c _ hx]
  change _ = ((avForm n c F : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x +
    ((avForm n c F' : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
  rw [avForm_apply n c _ hx, avForm_apply n c _ hx]
  exact avRaw_add n c F F' hx

theorem avForm_smul (r : ℝ) (F : Form (F := Coef n) faceSet 2) :
    avForm n c (r • F) = r • avForm n c F := by
  apply Form.ext
  intro x hx
  rw [avForm_apply n c _ hx]
  change _ = r • ((avForm n c F : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
  rw [avForm_apply n c _ hx]
  exact avRaw_smul n c r F x

section Invariant

variable {G : Type} [Group G] {D : PlaneData G} {c}

/-- **The torus average as a linear map on the invariant closed forms of the face**: for a plane
parabolic group with integral Levi blocks and radical lattice `cℤ²`, the average of a `D`-invariant
closed form is again a `D`-invariant closed form. -/
def avInv (hL : LatticeData D c) :
    ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n) →ₗ[ℝ]
      ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n) where
  toFun F := ⟨avForm n c F.1, d_avForm n c F.1 F.2.1, fun g => pullForm_avForm n hL F.1 F.2.2 g⟩
  map_add' F F' := Subtype.ext (avForm_add n c F.1 F'.1)
  map_smul' r F := Subtype.ext (avForm_smul n c r F.1)

theorem avInv_val (hL : LatticeData D c) (F : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) :
    ((avInv n hL F : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) :
      Form (F := Coef n) faceSet 2) = avForm n c F.1 := rfl

end Invariant

end TernaryPeriodPolynomials.Argument.EisensteinClass
