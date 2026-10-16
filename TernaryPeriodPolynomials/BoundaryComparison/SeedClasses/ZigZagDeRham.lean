module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ZigZagAlgebra
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.DeRham
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.PullbackAlgebra

@[expose] public section


/-!
# The Čech--de Rham zig-zag on a convex open set

Instantiation of `ZigZagAlgebra` by the library's smooth chart de Rham complex
(`TernaryPoly.SmoothLocalDeRham.Form`, `d`, with the Poincaré lemma on convex sets and the
constancy of closed 0-forms), for a group acting on the open convex set `s` by smooth maps, with
the coefficient module `F` a finite-dimensional real normed space carrying a representation `ρ`.

Formalized by Claude Sonnet 5.5.
-/

open Set
open scoped ContDiff Topology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
  TernaryPoly.SmoothSingularComparison

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A group action on an open set `s` by smooth maps. -/
structure Action (G : Type) [Group G] (s : Set E) where
  act : G → E → E
  smooth : ∀ g, ContDiffOn ℝ ∞ (act g) s
  mapsTo : ∀ g, MapsTo (act g) s s
  mul : ∀ g h, ∀ x ∈ s, act (g * h) x = act g (act h x)

variable {s : Set E} {G : Type} [Group G]

theorem pullRaw_indicator {n : ℕ} (f : E → E) (W : RawForm E F n) {x : E} (hx : f x ∈ s) :
    pullRaw f (s.indicator W) x = pullRaw f W x := by
  simp [pullRaw, hx]

theorem pullRaw_add {n : ℕ} (f : E → E) (w η : RawForm E F n) (x : E) :
    pullRaw f (w + η) x = pullRaw f w x + pullRaw f η x := by
  ext v
  simp [pullRaw]

theorem pullRaw_smul {n : ℕ} (f : E → E) (c : ℝ) (w : RawForm E F n) (x : E) :
    pullRaw f (c • w) x = c • pullRaw f w x := by
  ext v
  simp [pullRaw]

section Operators

variable [FiniteDimensional ℝ E]

/-- Pullback of chart forms by the action of `g`. -/
def pullForm (hs : IsOpen s) (A : Action G s) (g : G) (n : ℕ) :
    Form (F := F) s n →ₗ[ℝ] Form (F := F) s n where
  toFun w := restrictForm (F := F) s (pullRaw (A.act g) (w : RawForm E F n))
    (pullRaw_smooth hs (A.smooth g) (Form.smooth w) (A.mapsTo g))
  map_add' w η := by
    apply Form.ext
    intro x hx
    simp only [AddMemClass.coe_add, Pi.add_apply, restrictForm_apply (F := F) _ _ hx]
    exact pullRaw_add (F := F) (A.act g) _ _ x
  map_smul' c w := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply (F := F) _ _ hx, SetLike.val_smul, RingHom.id_apply,
      Pi.smul_apply]
    exact pullRaw_smul (F := F) (A.act g) c _ x

theorem pullForm_apply (hs : IsOpen s) (A : Action G s) (g : G) {n : ℕ} (w : Form (F := F) s n)
    {x : E} (hx : x ∈ s) :
    (pullForm hs A g n w : RawForm E F n) x = pullRaw (A.act g) (w : RawForm E F n) x :=
  restrictForm_apply (pullRaw (A.act g) (w : RawForm E F n))
    (pullRaw_smooth hs (A.smooth g) (Form.smooth w) (A.mapsTo g)) hx

/-- Coefficient twist of chart forms by a continuous linear endomorphism of `F`. -/
def twForm (L : F →L[ℝ] F) (n : ℕ) : Form (F := F) s n →ₗ[ℝ] Form (F := F) s n where
  toFun w := ⟨coefficientRaw L (w : RawForm E F n), coefficientRaw_smooth L (Form.smooth w), by
    intro x hx
    simp only [coefficientRaw, Form.outside w hx, map_zero]⟩
  map_add' w η := by
    apply Subtype.ext
    funext x
    simp only [coefficientRaw, AddMemClass.coe_add, Pi.add_apply, map_add]
  map_smul' c w := by
    apply Subtype.ext
    funext x
    simp only [coefficientRaw, SetLike.val_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

omit [FiniteDimensional ℝ E] in
theorem twForm_apply (L : F →L[ℝ] F) {n : ℕ} (w : Form (F := F) s n) (x : E) :
    (twForm L n w : RawForm E F n) x = coefficientFormMap L n ((w : RawForm E F n) x) := rfl

omit [FiniteDimensional ℝ E] in
theorem pullRaw_congr_at {n : ℕ} (f : E → E) {W₁ W₂ : RawForm E F n} {x : E}
    (h : W₁ (f x) = W₂ (f x)) : pullRaw f W₁ x = pullRaw f W₂ x := by
  simp [pullRaw, h]

omit [FiniteDimensional ℝ E] in
theorem diffAt_act (A : Action G s) (hs : IsOpen s) (g : G) {x : E} (hx : x ∈ s) :
    DifferentiableAt ℝ (A.act g) x :=
  (((A.smooth g) x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)

theorem d_pullForm (hs : IsOpen s) (A : Action G s) (g : G) {n : ℕ} (w : Form (F := F) s n) :
    d hs n (pullForm hs A g n w) = pullForm hs A g (n + 1) (d hs n w) := by
  apply Form.ext
  intro x hx
  rw [d_apply hs _ hx, pullForm_apply hs A g _ hx]
  have heq : (pullForm hs A g n w : RawForm E F n) =ᶠ[𝓝 x]
      pullRaw (A.act g) (w : RawForm E F n) := by
    filter_upwards [hs.mem_nhds hx] with y hy using pullForm_apply hs A g w hy
  rw [heq.extDeriv_eq]
  have hfx : A.act g x ∈ s := A.mapsTo g hx
  rw [extDeriv_pullRaw (((A.smooth g) x hx).contDiffAt (hs.mem_nhds hx))
    ((((Form.smooth w) _ hfx).contDiffAt (hs.mem_nhds hfx)).differentiableAt (by simp))]
  apply pullRaw_congr_at
  rw [d_apply hs w hfx]

omit [FiniteDimensional ℝ E] in
theorem d_twForm (hs : IsOpen s) (L : F →L[ℝ] F) {n : ℕ} (w : Form (F := F) s n) :
    d hs n (twForm L n w) = twForm L (n + 1) (d hs n w) := by
  apply Form.ext
  intro x hx
  rw [d_apply hs _ hx, twForm_apply, d_apply hs w hx]
  exact extDeriv_coefficientRaw L
    ((((Form.smooth w) x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp))

theorem pullForm_mul (hs : IsOpen s) (A : Action G s) (g h : G) {n : ℕ}
    (w : Form (F := F) s n) :
    pullForm hs A (g * h) n w = pullForm hs A h n (pullForm hs A g n w) := by
  apply Form.ext
  intro x hx
  have hhx : A.act h x ∈ s := A.mapsTo h hx
  rw [pullForm_apply hs A _ _ hx, pullForm_apply hs A h _ hx]
  rw [pullRaw_congr_at (A.act h) (W₂ := pullRaw (A.act g) (w : RawForm E F n))
    (pullForm_apply hs A g w hhx)]
  rw [pullRaw_comp _ (diffAt_act A hs g hhx) (diffAt_act A hs h hx)]
  apply pullRaw_eventuallyEq
  filter_upwards [hs.mem_nhds hx] with y hy using A.mul g h y hy

omit [FiniteDimensional ℝ E] in
theorem twForm_mul (L₁ L₂ : F →L[ℝ] F) {n : ℕ} (w : Form (F := F) s n) :
    twForm (L₁.comp L₂) n w = twForm L₁ n (twForm L₂ n w) := by
  apply Subtype.ext
  funext x
  ext v
  simp [twForm, coefficientRaw, coefficientFormMap]

theorem pullForm_twForm (hs : IsOpen s) (A : Action G s) (g : G) (L : F →L[ℝ] F) {n : ℕ}
    (w : Form (F := F) s n) :
    pullForm hs A g n (twForm L n w) = twForm L n (pullForm hs A g n w) := by
  apply Form.ext
  intro x hx
  rw [pullForm_apply hs A g _ hx, twForm_apply, pullForm_apply hs A g _ hx]
  have := congrFun (coefficientRaw_pullRaw L (A.act g) (w : RawForm E F n)) x
  exact this

omit [FiniteDimensional ℝ E] in
theorem pullRaw_zero (f : E → E) (a : RawForm E F 0) (x : E) : pullRaw f a x = a (f x) := by
  ext v
  simp only [pullRaw, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  exact Subsingleton.elim _ _

theorem pullForm_constant (hs : IsOpen s) (A : Action G s) (g : G) (c : F) :
    pullForm hs A g 0 (constant s c) = constant s c := by
  apply Form.ext
  intro x hx
  have hfx : A.act g x ∈ s := A.mapsTo g hx
  rw [pullForm_apply hs A g _ hx, pullRaw_zero]
  simp only [constant, ofFunction_apply _ _ hx, ofFunction_apply _ _ hfx]

omit [FiniteDimensional ℝ E] in
theorem twForm_constant (L : F →L[ℝ] F) (c : F) :
    twForm L 0 (constant s c) = constant s (L c) := by
  apply Form.ext
  intro x hx
  rw [twForm_apply]
  simp only [constant, ofFunction_apply _ _ hx]
  ext v
  simp [coefficientFormMap, zeroEquiv]

end Operators

section Instance

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [CompleteSpace F]

/-- The continuous linear action of `ρ g` on the coefficient space. -/
noncomputable def repCLM (ρ : Representation ℝ G F) (g : G) : F →L[ℝ] F :=
  LinearMap.toContinuousLinearMap (ρ g)

omit [CompleteSpace F] in
theorem repCLM_mul (ρ : Representation ℝ G F) (g h : G) :
    repCLM ρ (g * h) = (repCLM ρ g).comp (repCLM ρ h) := by
  ext v
  simp [repCLM]

/-- **The laws of the zig-zag hold for the smooth chart de Rham complex of a convex open set.** -/
theorem laws (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty) (A : Action G s)
    (ρ : Representation ℝ G F) :
    Laws ρ (d hs 0) (d hs 1) (fun g => pullForm hs A g 0) (fun g => pullForm hs A g 1)
      (fun g => pullForm hs A g 2) (fun g => twForm (repCLM ρ g) 0)
      (fun g => twForm (repCLM ρ g) 1) (fun g => twForm (repCLM ρ g) 2)
      (deRhamConstant s) where
  d_P0 g w := d_pullForm hs A g w
  d_T0 g w := d_twForm hs _ w
  d_P1 g w := d_pullForm hs A g w
  d_T1 g w := d_twForm hs _ w
  P0_mul g h w := pullForm_mul hs A g h w
  P1_mul g h w := pullForm_mul hs A g h w
  T0_mul g h w := by rw [repCLM_mul, twForm_mul]
  T1_mul g h w := by rw [repCLM_mul, twForm_mul]
  PT0 g h w := pullForm_twForm hs A g _ w
  PT1 g h w := pullForm_twForm hs A g _ w
  c_injective := deRhamConstant_injective hne
  d_c v := LinearMap.congr_fun (deRhamConstant_closed hs) v
  P_c g v := pullForm_constant hs A g v
  T_c g v := by
    change twForm (repCLM ρ g) 0 (constant s v) = constant s (ρ g v)
    rw [twForm_constant]
    simp [repCLM]
  const_of_closed w hw := by
    obtain ⟨v, hv⟩ := (closed_zero_iff_constant hs hc.isPreconnected w).mp hw
    exact ⟨v, hv⟩
  exact1 w hw := by
    have h := range_d_eq_ker_d (F := F) hs hc 0
    have : w ∈ LinearMap.ker (d hs 1 : Form (F := F) s 1 →ₗ[ℝ] Form (F := F) s 2) := hw
    rw [← h] at this
    exact this

omit [FiniteDimensional ℝ F] in
/-- Closed 2-forms are exact on a convex open set (the degree-2 Poincaré lemma). -/
theorem exact2 (hs : IsOpen s) (hc : Convex ℝ s) :
    ∀ om : Form (F := F) s 2, d hs 2 om = 0 → ∃ η : Form (F := F) s 1, d hs 1 η = om := by
  intro om hom
  have h := range_d_eq_ker_d (F := F) hs hc 1
  have : om ∈ LinearMap.ker (d hs 2 : Form (F := F) s 2 →ₗ[ℝ] Form (F := F) s 3) := hom
  rw [← h] at this
  exact this

end Instance

end TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

end
