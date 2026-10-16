module

public import TernaryPeriodPolynomials.DifferentialForm.CochainComparison.Affine

@[expose] public section


/-!
# The triangle cochain of a closed equivariant 2-form and the bridge to the de Rham class

Formalized by Claude Sonnet 5.5.
Paper: Appendix C (`ar:sec:stokes`, the cohomological restriction
identities and the comparison of the series class with the Gram-triangle cochain).

For a group `G` acting by affine maps on an open convex set `s` of a finite-dimensional real vector space (the case of
`GL₃` acting linearly on Gram matrices), a closed `ρ`-equivariant chart `2`-form `ω` has the **triangle cochain**
`F(y₀, y₁, y₂) = ∫_{[y₀x₀, y₁x₀, y₂x₀]} ω` (affine triangle with vertices the orbit points of a base point `x₀`).
Writing a zig-zag datum `(η, θ_g)` for `ω` (`dη = ω`, `dθ_g = g^*η - ρ(g)η`), Stokes on the affine triangle gives
`F(1, g, gh) = c(g,h) + (ρ(g)κ(h) - κ(gh) + κ(g))` with `c` the zig-zag cocycle and
`κ(g) = ∫_{[x₀, g x₀]} η - θ_g(x₀)`.  Consequently the triangle cochain is a cocycle and its class is the de Rham class
(`bridge_triangleCochain_eq_deRhamClass`).  No Stokes theorem for tetrahedra is needed.
-/

open Set MeasureTheory CategoryTheory groupCohomology
open scoped ContDiff Topology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormCochainBridge

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothSingularComparison
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

section Eval

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type} [Group G] {s : Set E}

theorem val0_eq (θ : Form (F := F) s 0) (x : E) : val0 θ x = (θ : RawForm E F 0) x 0 := rfl

theorem val0_add (θ θ' : Form (F := F) s 0) (x : E) : val0 (θ + θ') x = val0 θ x + val0 θ' x := by
  simp [val0_eq]

theorem val0_sub (θ θ' : Form (F := F) s 0) (x : E) : val0 (θ - θ') x = val0 θ x - val0 θ' x := by
  simp [val0_eq]

theorem val0_const (v : F) {x : E} (hx : x ∈ s) : val0 (deRhamConstant s v) x = v := by
  rw [val0_eq]
  change ((ofFunction (s := s) (fun _ => v) contDiffOn_const : Form (F := F) s 0) : RawForm E F 0) x 0 = v
  rw [ofFunction_apply _ _ hx]
  rfl

theorem val0_pull [FiniteDimensional ℝ E] (hs : IsOpen s) (A : ZigZag.Action G s) (g : G)
    (θ : Form (F := F) s 0) {x : E} (hx : x ∈ s) :
    val0 (ZigZag.pullForm hs A g 0 θ) x = val0 θ (A.act g x) := by
  rw [val0_eq, val0_eq, ZigZag.pullForm_apply hs A g θ hx, ZigZag.pullRaw_zero]

theorem val0_tw (ρ : Representation ℝ G F) [FiniteDimensional ℝ F] [CompleteSpace F] (g : G)
    (θ : Form (F := F) s 0) (x : E) :
    val0 (ZigZag.twForm (s := s) (ZigZag.repCLM ρ g) 0 θ) x = ρ g (val0 θ x) := by
  rw [val0_eq, val0_eq, ZigZag.twForm_apply]
  rfl

end Eval

section Bridge

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
  {G : Type} [Group G] {s : Set E}

/-- **The triangle cochain** `F(y₀, y₁, y₂) = ∫_{[y₀x₀, y₁x₀, y₂x₀]} ω` of a chart `2`-form. -/
def triangleCochain (A : ZigZag.Action G s) (w2 : RawForm E F 2) (x₀ : E) (y : Fin 3 → G) : F :=
  triInt w2 (A.act (y 0) x₀) (A.act (y 1) x₀) (A.act (y 2) x₀)

/-- The inhomogeneous cochain `(a, b) ↦ F(1, a, ab)` of the triangle cochain. -/
def inhomTriangle (A : ZigZag.Action G s) (w2 : RawForm E F 2) (x₀ : E) (a b : G) : F :=
  triangleCochain A w2 x₀ ![1, a, a * b]

variable (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty) (A : ZigZag.Action G s)
  (ρ : Representation ℝ G F)

/-- The edge function `e(g) = ∫_{[x₀, g x₀]} η`. -/
def edgeFun (η : Form (F := F) s 1) (x₀ : E) (g : G) : F := segInt (η : RawForm E F 1) x₀ (A.act g x₀)

/-- **Stokes identity for a zig-zag datum**: the triangle cochain is the zig-zag cocycle plus an explicit
coboundary. -/
theorem triangle_eq_cochain_add (𝔄 : AffineAction A) {w2 : Form (F := F) s 2}
    (D : ZigZag.Datum (d hs 0) (d hs 1) (fun g => ZigZag.pullForm hs A g 1)
      (fun g => ZigZag.twForm (ZigZag.repCLM ρ g) 1) w2) {x₀ : E} (hx₀ : x₀ ∈ s) (g h : G) :
    inhomTriangle A (w2 : RawForm E F 2) x₀ g h =
      ZigZag.cochain (ZigZag.laws hs hc hne A ρ) D g h +
        (ρ g (edgeFun A D.η x₀ h - val0 (D.θ h) x₀) - (edgeFun A D.η x₀ (g * h) - val0 (D.θ (g * h)) x₀) +
          (edgeFun A D.η x₀ g - val0 (D.θ g) x₀)) := by
  have hxg : ∀ g : G, A.act g x₀ ∈ s := fun g => A.mapsTo g hx₀
  have h1x : A.act 1 x₀ = x₀ := 𝔄.one x₀ hx₀
  have hmul : A.act (g * h) x₀ = A.act g (A.act h x₀) := A.mul g h x₀ hx₀
  have hw : (w2 : RawForm E F 2) = (d hs 1 D.η : RawForm E F 2) := by rw [D.dη]
  have key : segInt (D.η : RawForm E F 1) (A.act g x₀) (A.act (g * h) x₀) =
      ρ g (edgeFun A D.η x₀ h) + val0 (D.θ g) (A.act h x₀) - val0 (D.θ g) x₀ := by
    rw [hmul, ← segInt_pullForm 𝔄 hs hc g D.η hx₀ (hxg h)]
    have hp : ZigZag.pullForm hs A g 1 D.η =
        ZigZag.twForm (ZigZag.repCLM ρ g) 1 D.η + d hs 0 (D.θ g) := by
      have := D.dθ g
      rw [eq_sub_iff_add_eq] at this
      rw [← this]
      abel
    rw [hp, segInt_add hc _ _ hx₀ (hxg h), segInt_twForm hc _ _ hx₀ (hxg h),
      segInt_d_zero hs hc _ hx₀ (hxg h)]
    simp only [ZigZag.repCLM, edgeFun, LinearMap.coe_toContinuousLinearMap']
    abel
  have hcoch : ZigZag.cochain (ZigZag.laws hs hc hne A ρ) D g h =
      val0 (D.θ g) (A.act h x₀) + ρ g (val0 (D.θ h) x₀) - val0 (D.θ (g * h)) x₀ := by
    have e := congrArg (fun w => val0 w x₀) (ZigZag.c_cochain (ZigZag.laws hs hc hne A ρ) D g h)
    simp only [val0_const _ hx₀, val0_add, val0_sub, val0_pull hs A h _ hx₀, val0_tw] at e
    exact e
  unfold inhomTriangle triangleCochain
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [h1x, hw, triInt_d_one hs hc D.η hx₀ (hxg g) (hxg (g * h)), key, hcoch]
  simp only [edgeFun, map_sub]
  abel

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [CompleteSpace F] in
theorem coboundary_cocycle (κ : G → F) (g h j : G) :
    (ρ (g * h) (κ j) - κ (g * h * j) + κ (g * h)) + (ρ g (κ h) - κ (g * h) + κ g) =
      ρ g (ρ h (κ j) - κ (h * j) + κ h) + (ρ g (κ (h * j)) - κ (g * (h * j)) + κ g) := by
  simp only [map_mul, Module.End.mul_apply, map_add, map_sub, mul_assoc]
  abel

/-- **The triangle cochain of a closed equivariant form is a `2`-cocycle** of `G` with values in `ρ`
(Mathlib's inhomogeneous convention `(a, b) ↦ F(1, a, ab)`). -/
theorem isCocycle_inhomTriangle (hc : Convex ℝ s) (hne : s.Nonempty) (𝔄 : AffineAction A)
    (w2 : ZigZag.invClosed hs A ρ) {x₀ : E} (hx₀ : x₀ ∈ s) :
    (fun p : G × G => inhomTriangle A ((w2 : Form (F := F) s 2) : RawForm E F 2) x₀ p.1 p.2) ∈
      cocycles₂ (Rep.of ρ) := by
  obtain ⟨D⟩ := ZigZag.exists_datum_deRham hs hc hne A ρ w2
  rw [mem_cocycles₂_iff]
  intro g h j
  have e := fun a b => triangle_eq_cochain_add hs hc hne A ρ 𝔄 D hx₀ a b
  simp only [e]
  have hco := ZigZag.cochain_isCocycle (ZigZag.laws hs hc hne A ρ) D g h j
  set κ : G → F := fun g => edgeFun A D.η x₀ g - val0 (D.θ g) x₀ with hκ
  have hb := coboundary_cocycle (ρ := ρ) κ g h j
  calc _ = (ZigZag.cochain (ZigZag.laws hs hc hne A ρ) D (g * h) j +
          ZigZag.cochain (ZigZag.laws hs hc hne A ρ) D g h) +
          ((ρ (g * h) (κ j) - κ (g * h * j) + κ (g * h)) + (ρ g (κ h) - κ (g * h) + κ g)) := by
        simp only [hκ]; abel
    _ = (ρ g (ZigZag.cochain (ZigZag.laws hs hc hne A ρ) D h j) +
          ZigZag.cochain (ZigZag.laws hs hc hne A ρ) D g (h * j)) +
          (ρ g (ρ h (κ j) - κ (h * j) + κ h) + (ρ g (κ (h * j)) - κ (g * (h * j)) + κ g)) := by
        rw [hco, hb]
    _ = _ := by
        simp only [hκ, map_add, map_sub]; abel

/-- **Bridge: the class of the triangle cochain is the de Rham class** (`OB5`), for every closed equivariant `2`-form
on an open convex set with an affine action: `[F(1, a, ab)] = deRhamClass ω` in `H²(G, F)`. -/
theorem bridge_triangleCochain_eq_deRhamClass (𝔄 : AffineAction A) (w2 : ZigZag.invClosed hs A ρ)
    {x₀ : E} (hx₀ : x₀ ∈ s) :
    (H2π (Rep.of ρ)).hom ⟨_, isCocycle_inhomTriangle hs A ρ hc hne 𝔄 w2 hx₀⟩ =
      ZigZag.deRhamClass hs hc hne A ρ w2 := by
  obtain ⟨D⟩ := ZigZag.exists_datum_deRham hs hc hne A ρ w2
  rw [ZigZag.deRhamClass_eq hs hc hne A ρ w2 D]
  unfold ZigZag.zigzagClass
  rw [← sub_eq_zero, ← map_sub, H2π_eq_zero_iff]
  refine ⟨fun g => edgeFun A D.η x₀ g - val0 (D.θ g) x₀, ?_⟩
  funext p
  simp only [d₁₂_hom_apply]
  show _ = inhomTriangle A ((w2 : Form (F := F) s 2) : RawForm E F 2) x₀ p.1 p.2 -
    ZigZag.cochain (ZigZag.laws hs hc hne A ρ) D p.1 p.2
  rw [triangle_eq_cochain_add hs hc hne A ρ 𝔄 D hx₀ p.1 p.2]
  abel

end Bridge

section Homogeneous

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
  {G : Type} [Group G] {s : Set E}

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F] in
theorem affTri_mem (hc : Convex ℝ s) {p₀ p₁ p₂ : E} (h₀ : p₀ ∈ s) (h₁ : p₁ ∈ s) (h₂ : p₂ ∈ s)
    {q : ℝ × ℝ} (hq : q ∈ stdTriangle) : affTri p₀ p₁ p₂ q ∈ s := by
  obtain ⟨a, b⟩ := q
  obtain ⟨ha, hb, hab⟩ := hq
  have : affTri p₀ p₁ p₂ (a, b) = (1 - a - b) • p₀ + a • p₁ + b • p₂ := by
    simp only [affTri]; module
  rw [this]
  have key := hc.sum_mem (t := Finset.univ) (w := ![1 - a - b, a, b]) (z := ![p₀, p₁, p₂])
    (by intro i _; fin_cases i <;> simp <;> linarith) (by simp [Fin.sum_univ_three]; ring)
    (by intro i _; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_three] using key

omit [FiniteDimensional ℝ F] in
/-- Change of variables for an affine action: the triangle integral of the pullback is the triangle integral over the
image triangle. -/
theorem triInt_pullForm (hs : IsOpen s) (hc : Convex ℝ s) {A : ZigZag.Action G s} (𝔄 : AffineAction A) (g : G)
    (w2 : Form (F := F) s 2) {p₀ p₁ p₂ : E} (h₀ : p₀ ∈ s) (h₁ : p₁ ∈ s) (h₂ : p₂ ∈ s) :
    triInt (ZigZag.pullForm hs A g 2 w2 : RawForm E F 2) p₀ p₁ p₂ =
      triInt (w2 : RawForm E F 2) (A.act g p₀) (A.act g p₁) (A.act g p₂) := by
  unfold triInt
  refine setIntegral_congr_fun measurableSet_stdTriangle (fun q hq => ?_)
  have hqs := affTri_mem hc h₀ h₁ h₂ hq
  rw [ZigZag.pullForm_apply hs A g w2 hqs]
  simp only [pullRaw, ContinuousAlternatingMap.compContinuousLinearMap_apply, 𝔄.fderiv_act]
  have hq' : affTri (A.act g p₀) (A.act g p₁) (A.act g p₂) q = A.act g (affTri p₀ p₁ p₂ q) := by
    simp only [affTri, 𝔄.act_eq, map_add, map_smul, map_sub]
    module
  rw [hq']
  congr 1
  funext i
  fin_cases i <;> simp [𝔄.lin_sub]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [CompleteSpace F] in
theorem integrable_triInt (hc : Convex ℝ s) (w2 : Form (F := F) s 2) {p₀ p₁ p₂ : E} (h₀ : p₀ ∈ s)
    (h₁ : p₁ ∈ s) (h₂ : p₂ ∈ s) :
    IntegrableOn (fun q => (w2 : RawForm E F 2) (affTri p₀ p₁ p₂ q) ![p₁ - p₀, p₂ - p₀]) stdTriangle := by
  apply ContinuousOn.integrableOn_compact isCompact_stdTriangle
  have h1 : ContinuousOn (fun q => (w2 : RawForm E F 2) (affTri p₀ p₁ p₂ q)) stdTriangle :=
    (Form.smooth w2).continuousOn.comp (continuous_affTri p₀ p₁ p₂).continuousOn
      (fun q hq => affTri_mem hc h₀ h₁ h₂ hq)
  exact (ContinuousAlternatingMap.apply ℝ E F ![p₁ - p₀, p₂ - p₀]).continuous.comp_continuousOn h1

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem triInt_twForm (hc : Convex ℝ s) (L : F →L[ℝ] F) (w2 : Form (F := F) s 2) {p₀ p₁ p₂ : E}
    (h₀ : p₀ ∈ s) (h₁ : p₁ ∈ s) (h₂ : p₂ ∈ s) :
    triInt (ZigZag.twForm (s := s) L 2 w2 : RawForm E F 2) p₀ p₁ p₂ =
      L (triInt (w2 : RawForm E F 2) p₀ p₁ p₂) := by
  unfold triInt
  rw [← ContinuousLinearMap.integral_comp_comm L (integrable_triInt hc w2 h₀ h₁ h₂)]
  refine setIntegral_congr_fun measurableSet_stdTriangle (fun q _ => ?_)
  simp [ZigZag.twForm_apply]

/-- **Equivariance of the triangle cochain**: `F(g y) = ρ(g) F(y)` for an invariant form. -/
theorem triangleCochain_equivariant (hs : IsOpen s) (hc : Convex ℝ s) {A : ZigZag.Action G s}
    (𝔄 : AffineAction A) (ρ : Representation ℝ G F) (w2 : ZigZag.invClosed hs A ρ) {x₀ : E} (hx₀ : x₀ ∈ s)
    (g : G) (y : Fin 3 → G) :
    triangleCochain A ((w2 : Form (F := F) s 2) : RawForm E F 2) x₀ (fun i => g * y i) =
      ρ g (triangleCochain A ((w2 : Form (F := F) s 2) : RawForm E F 2) x₀ y) := by
  unfold triangleCochain
  have hm : ∀ i, A.act (g * y i) x₀ = A.act g (A.act (y i) x₀) := fun i => A.mul g (y i) x₀ hx₀
  simp only [hm]
  have hy : ∀ i, A.act (y i) x₀ ∈ s := fun i => A.mapsTo (y i) hx₀
  rw [← triInt_pullForm hs hc 𝔄 g _ (hy 0) (hy 1) (hy 2), w2.2.2 g,
    triInt_twForm hc _ _ (hy 0) (hy 1) (hy 2)]
  rfl

omit [FiniteDimensional ℝ F] in
/-- Stokes for a closed `2`-form on the vertices of any affine triangle: the triangle integral is the coboundary
of an edge cochain. -/
theorem exists_edge_cochain (hs : IsOpen s) (hc : Convex ℝ s) (w2 : Form (F := F) s 2) (hw : d hs 2 w2 = 0) :
    ∃ η : Form (F := F) s 1, d hs 1 η = w2 := ZigZag.exact2 hs hc w2 hw

omit [FiniteDimensional ℝ F] in
/-- **The triangle cochain of a closed `2`-form is a homogeneous `2`-cocycle** (no equivariance needed): the alternating
sum over the four faces of a tetrahedron of orbit points vanishes. -/
theorem triangleCochain_isCocycle (hs : IsOpen s) (hc : Convex ℝ s) (A : ZigZag.Action G s)
    (w2 : Form (F := F) s 2) (hw : d hs 2 w2 = 0) {x₀ : E} (hx₀ : x₀ ∈ s) (x : Fin 4 → G) :
    triangleCochain A (w2 : RawForm E F 2) x₀ ![x 1, x 2, x 3] -
        triangleCochain A (w2 : RawForm E F 2) x₀ ![x 0, x 2, x 3] +
        triangleCochain A (w2 : RawForm E F 2) x₀ ![x 0, x 1, x 3] -
        triangleCochain A (w2 : RawForm E F 2) x₀ ![x 0, x 1, x 2] = 0 := by
  obtain ⟨η, hη⟩ := exists_edge_cochain hs hc w2 hw
  have hp : ∀ i, A.act (x i) x₀ ∈ s := fun i => A.mapsTo (x i) hx₀
  have key : ∀ a b c : Fin 4, triangleCochain A (w2 : RawForm E F 2) x₀ ![x a, x b, x c] =
      segInt (η : RawForm E F 1) (A.act (x b) x₀) (A.act (x c) x₀) -
        segInt (η : RawForm E F 1) (A.act (x a) x₀) (A.act (x c) x₀) +
        segInt (η : RawForm E F 1) (A.act (x a) x₀) (A.act (x b) x₀) := by
    intro a b c
    unfold triangleCochain
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [← hη]
    exact triInt_d_one hs hc η (hp a) (hp b) (hp c)
  rw [key, key, key, key]
  abel

end Homogeneous

end TernaryPeriodPolynomials.Argument.FormCochainBridge
