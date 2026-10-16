module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.AveragePreserves

@[expose] public section


/-!
# The torus average preserves the de Rham class, for an arbitrary unipotent radical action (generalization of `deRhamClass_avInv`)

Formalized by Claude Sonnet 5.5.

the `deRhamClass_avInv` is stated for a `PlaneData` whose coefficient representation is `ρ(plm g)` and whose radical acts by `trL n`.  The line radical
`Nℤ²` of `Q` acts on `E_n` by `ρ(u(s,t))`, a DIFFERENT unipotent representation of `ℝ²`.  `TwistData` records exactly what the proof uses:
a coefficient representation `ρ'` of the group, a unipotent representation `σ` of `ℝ²`, the Levi integrality, the intertwining `σ(λ_g u) ρ'(g) = ρ'(g) σ(u)` and the
realization of the lattice `cℤ²` in the group with `ρ'(ν) = σ(c k)`.  Then `Av F` is a closed `ρ'`-invariant form and has the same class as `F`
(`deRhamClass_avInvT`).  All the generic lemmas (`exists_normalized_primitive`, `avFormS_pullForm`, `avFormS_twForm`, `const_eq_zero_of_avFormS`, ...) are reused.
-/

open ContinuousAlternatingMap Set MeasureTheory CategoryTheory groupCohomology
open scoped ContDiff MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

open TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPoly.SmoothCoveringDeRham

/-- The data used by the averaging argument: a coefficient representation, a unipotent radical action and their compatibilities. -/
structure TwistData {G : Type} [Group G] (D : PlaneData G) (n : ℕ) (c : ℝ) where
  ρ' : Representation ℝ G (Coef n)
  σ : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n)
  uni : UniRep σ
  levi : ∀ g : G, ∃ A : SL(2, ℤ), (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) =
    (A : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)
  hint : ∀ (g : G) (u : Fin 2 → ℝ), (σ ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec u)).comp
      (ZigZag.repCLM ρ' g) = (ZigZag.repCLM ρ' g).comp (σ u)
  lattice : ∀ k : Fin 2 → ℤ, ∃ ν : G, (D.lam ν : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∧
    D.w ν = c • intVec k ∧ ZigZag.repCLM ρ' ν = σ (c • intVec k)

namespace TwistData

variable {G : Type} [Group G] {D : PlaneData G} {n : ℕ} {c : ℝ} (T : TwistData D n c)

/-- A lattice element acts on invariant forms as a translation with coefficient `σ(u)`. -/
theorem pull_lattice (ν : G) (hν : (D.lam ν : Matrix (Fin 2) (Fin 2) ℝ) = 1) (u : Fin 2 → ℝ)
    (hu : D.w ν = u) (hrep : ZigZag.repCLM T.ρ' ν = T.σ u) {k : ℕ} (F : Form (F := Coef n) faceSet k)
    (hF : ZigZag.pullForm isOpen_faceSet D.action ν k F =
      ZigZag.twForm (ZigZag.repCLM T.ρ' ν) k F) :
    ZigZag.pullForm isOpen_faceSet trPD.action (Multiplicative.ofAdd u) k F =
      ZigZag.twForm (T.σ u) k F := by
  have hact : ∀ x ∈ faceSet, D.action.act ν x = trPD.action.act (Multiplicative.ofAdd u) x := by
    intro x hx
    change D.act ν x = trPD.act (Multiplicative.ofAdd u) x
    rw [trPD_act]
    funext i
    fin_cases i
    · simp [PlaneData.act, hν, hu, faceTau]
    · simp [PlaneData.act, hν, hu, faceTau]
    · simp [PlaneData.act, hν, faceTau, mob]
    · simp [PlaneData.act, hν, faceTau, mob]
  rw [← pullForm_congr_actK D.action trPD.action ν (Multiplicative.ofAdd u) hact, hF, hrep]

/-- An invariant form is lattice equivariant for `σ`. -/
theorem eqvS_of_invariant {k : ℕ} {F : Form (F := Coef n) faceSet k}
    (hF : ∀ g, ZigZag.pullForm isOpen_faceSet D.action g k F =
      ZigZag.twForm (ZigZag.repCLM T.ρ' g) k F) : EqvS T.σ c F := by
  rw [eqvS_iff_pull]
  intro m
  obtain ⟨ν, hν1, hν2, hν3⟩ := T.lattice m
  exact T.pull_lattice ν hν1 _ hν2 hν3 F (hF ν)

/-- The Levi-twisted radical action. -/
def sg (g : G) : (Fin 2 → ℝ) → (Coef n →L[ℝ] Coef n) :=
  fun v => T.σ ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec v)

theorem uni_sg (g : G) : UniRep (T.sg g) := T.uni.comp_mulVec _

theorem sg_mul (g h : G) (v : Fin 2 → ℝ) :
    T.sg (g * h) v = T.sg g ((D.lam h : Matrix (Fin 2) (Fin 2) ℝ).mulVec v) := by
  unfold sg
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem sg_funext_mul (g h : G) :
    T.sg (g * h) = fun v => T.sg g ((D.lam h : Matrix (Fin 2) (Fin 2) ℝ).mulVec v) :=
  funext (T.sg_mul g h)

theorem intertwine_sg (g h : G) (u : Fin 2 → ℝ) :
    (T.sg (g * h) u).comp (ZigZag.repCLM T.ρ' g) = (ZigZag.repCLM T.ρ' g).comp (T.sg h u) := by
  rw [sg_mul]
  exact T.hint g _

/-- **The average of an invariant form is invariant** (C1 and C2 of S6, with the Levi-twisted radical action). -/
theorem pullForm_avFormS (F : Form (F := Coef n) faceSet 2)
    (hF : ∀ g, ZigZag.pullForm isOpen_faceSet D.action g 2 F =
      ZigZag.twForm (ZigZag.repCLM T.ρ' g) 2 F) (g : G) :
    ZigZag.pullForm isOpen_faceSet D.action g 2 (avFormS T.uni.smooth c F) =
      ZigZag.twForm (ZigZag.repCLM T.ρ' g) 2 (avFormS T.uni.smooth c F) := by
  obtain ⟨A, hA⟩ := T.levi g
  have hE : EqvS T.σ c F := T.eqvS_of_invariant hF
  have h1 := avFormS_pullForm D T.uni g A hA (σ' := T.sg g) (fun v => rfl) (T.uni_sg g).smooth hE
  have h2 := avFormS_twForm (c := c) (σ := T.σ) (σ' := T.sg g) T.uni.smooth (T.uni_sg g).smooth
    (ZigZag.repCLM T.ρ' g) (fun u => T.hint g u) F
  rw [← h1, hF g, h2]

/-- **The average of an invariant closed form is an invariant closed form.** -/
def avInvT (F : ZigZag.invClosed isOpen_faceSet D.action T.ρ') :
    ZigZag.invClosed isOpen_faceSet D.action T.ρ' :=
  ⟨avFormS T.uni.smooth c F.1, by
    rw [d_avFormS_comm T.uni.smooth c, F.2.1]
    exact (avLin (k := 3) T.uni.smooth c).map_zero, fun g =>
    T.pullForm_avFormS F.1 F.2.2 g⟩

theorem avInvT_val (F : ZigZag.invClosed isOpen_faceSet D.action T.ρ') :
    ((T.avInvT F : ZigZag.invClosed isOpen_faceSet D.action T.ρ') : Form (F := Coef n) faceSet 2) =
      avFormS T.uni.smooth c F.1 := rfl

/-- **The torus average does not change the de Rham class** (arbitrary unipotent radical action). -/
theorem deRhamClass_avInvT (hc : c ≠ 0) (F : ZigZag.invClosed isOpen_faceSet D.action T.ρ') :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action T.ρ' (T.avInvT F) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action T.ρ' F := by
  have hU : UniRep T.σ := T.uni
  have hFE : EqvS T.σ c (F : Form (F := Coef n) faceSet 2) := T.eqvS_of_invariant F.2.2
  have hom : (((T.avInvT F - F : ZigZag.invClosed isOpen_faceSet D.action T.ρ')) :
      Form (F := Coef n) faceSet 2) = avFormS hU.smooth c F.1 - F.1 := by
    rw [Submodule.coe_sub, avInvT_val]
  obtain ⟨Ξ, hΞE, hΞA, hΞd⟩ := exists_normalized_primitive (k := 1) hU hc
    (F : Form (F := Coef n) faceSet 2) F.2.1 hFE
  have hinv : ∀ g, ZigZag.pullForm isOpen_faceSet D.action g 2 (avFormS hU.smooth c F.1 - F.1) =
      ZigZag.twForm (ZigZag.repCLM T.ρ' g) 2 (avFormS hU.smooth c F.1 - F.1) := by
    intro g
    have := (T.avInvT F - F).2.2 g
    rwa [hom] at this
  let ζ : G → Form (F := Coef n) faceSet 1 := fun g =>
    ZigZag.twForm (ZigZag.repCLM T.ρ' g) 1 Ξ - ZigZag.pullForm isOpen_faceSet D.action g 1 Ξ
  have hζd : ∀ g, d isOpen_faceSet 1 (ζ g) = 0 := by
    intro g
    simp only [ζ, map_sub]
    rw [ZigZag.d_twForm isOpen_faceSet, ZigZag.d_pullForm isOpen_faceSet, hΞd, hinv g, sub_self]
  have hint : ∀ g u, (T.sg g u).comp (ZigZag.repCLM T.ρ' g) =
      (ZigZag.repCLM T.ρ' g).comp (T.σ u) := fun g u => T.hint g u
  have hζE : ∀ g, EqvS (T.sg g) c (ζ g) := by
    intro g
    obtain ⟨A, hA⟩ := T.levi g
    exact eqvS_sub (eqvS_twForm_of_intertwine hΞE _ (hint g)) (eqvS_pullForm D g A hA hΞE)
  have hζA : ∀ g, avFormS (T.uni_sg g).smooth c (ζ g) = 0 := by
    intro g
    obtain ⟨A, hA⟩ := T.levi g
    have h1 := avFormS_pullForm D hU g A hA (σ' := T.sg g) (fun v => rfl)
      (T.uni_sg g).smooth hΞE
    have h2 := avFormS_twForm (c := c) (σ := T.σ) (σ' := T.sg g) hU.smooth
      (T.uni_sg g).smooth (ZigZag.repCLM T.ρ' g) (hint g) Ξ
    have hsub : avFormS (T.uni_sg g).smooth c (ζ g) =
        avFormS (T.uni_sg g).smooth c (ZigZag.twForm (ZigZag.repCLM T.ρ' g) 1 Ξ) -
          avFormS (T.uni_sg g).smooth c (ZigZag.pullForm isOpen_faceSet D.action g 1 Ξ) :=
      (avLin (k := 1) (T.uni_sg g).smooth c).map_sub _ _
    rw [hsub, h1, h2, hΞA]
    simp
  have hθ : ∀ g, ∃ θ : Form (F := Coef n) faceSet 0, EqvS (T.sg g) c θ ∧
      avFormS (T.uni_sg g).smooth c θ = 0 ∧
      d isOpen_faceSet 0 θ = ZigZag.pullForm isOpen_faceSet D.action g 1 Ξ -
        ZigZag.twForm (ZigZag.repCLM T.ρ' g) 1 Ξ := by
    intro g
    obtain ⟨Y, hYE, hYA, hYd⟩ := exists_normalized_primitive (k := 0) (T.uni_sg g) hc (ζ g)
      (hζd g) (hζE g)
    refine ⟨Y, hYE, hYA, ?_⟩
    rw [hYd, hζA g, zero_sub]
    simp only [ζ, neg_sub]
  choose θ hθE hθA hθd using hθ
  have hom' : d isOpen_faceSet 1 Ξ = ((T.avInvT F - F :
      ZigZag.invClosed isOpen_faceSet D.action T.ρ') : Form (F := Coef n) faceSet 2) := by
    rw [hom]; exact hΞd
  let Dat : ZigZag.Datum (d isOpen_faceSet 0) (d isOpen_faceSet 1)
      (fun g => ZigZag.pullForm isOpen_faceSet D.action g 1)
      (fun g => ZigZag.twForm (ZigZag.repCLM T.ρ' g) 1)
      ((T.avInvT F - F : ZigZag.invClosed isOpen_faceSet D.action T.ρ') :
        Form (F := Coef n) faceSet 2) := ⟨Ξ, θ, hom', hθd⟩
  have hcoc : ∀ g h, ZigZag.pullForm isOpen_faceSet D.action h 0 (θ g) +
      ZigZag.twForm (ZigZag.repCLM T.ρ' g) 0 (θ h) - θ (g * h) = 0 := by
    intro g h
    obtain ⟨v, hv⟩ := ZigZag.defect_const (ZigZag.laws isOpen_faceSet convex_faceSet
      faceSet_nonempty D.action T.ρ') Dat g h
    have hv' : ZigZag.pullForm isOpen_faceSet D.action h 0 (θ g) +
        ZigZag.twForm (ZigZag.repCLM T.ρ' g) 0 (θ h) - θ (g * h) =
        constant faceSet v := hv
    obtain ⟨Ah, hAh⟩ := T.levi h
    have t1 : EqvS (T.sg (g * h)) c (ZigZag.pullForm isOpen_faceSet D.action h 0 (θ g)) := by
      rw [T.sg_funext_mul g h]
      exact eqvS_pullForm D h Ah hAh (hθE g)
    have t2 : EqvS (T.sg (g * h)) c
        (ZigZag.twForm (ZigZag.repCLM T.ρ' g) 0 (θ h)) :=
      eqvS_twForm_of_intertwine (hθE h) _ (T.intertwine_sg g h)
    have hE : EqvS (T.sg (g * h)) c (constant faceSet v : Form (F := Coef n) faceSet 0) := by
      rw [← hv']
      exact eqvS_sub (t1.add t2) (hθE (g * h))
    have a1 : avFormS (T.uni_sg (g * h)).smooth c
        (ZigZag.pullForm isOpen_faceSet D.action h 0 (θ g)) = 0 := by
      have := avFormS_pullForm D (T.uni_sg g) h Ah hAh (σ' := T.sg (g * h))
        (T.sg_mul g h) (T.uni_sg (g * h)).smooth (hθE g)
      rw [this, hθA g]
      simp
    have a2 : avFormS (T.uni_sg (g * h)).smooth c
        (ZigZag.twForm (ZigZag.repCLM T.ρ' g) 0 (θ h)) = 0 := by
      have := avFormS_twForm (c := c) (σ := T.sg h) (σ' := T.sg (g * h))
        (T.uni_sg h).smooth (T.uni_sg (g * h)).smooth (ZigZag.repCLM T.ρ' g)
        (T.intertwine_sg g h) (θ h)
      rw [this, hθA h]
      simp
    have hAv : avFormS (T.uni_sg (g * h)).smooth c
        (constant faceSet v : Form (F := Coef n) faceSet 0) = 0 := by
      rw [← hv']
      have hs := (avLin (k := 0) (T.uni_sg (g * h)).smooth c).map_sub
        (ZigZag.pullForm isOpen_faceSet D.action h 0 (θ g) +
          ZigZag.twForm (ZigZag.repCLM T.ρ' g) 0 (θ h)) (θ (g * h))
      have ha := (avLin (k := 0) (T.uni_sg (g * h)).smooth c).map_add
        (ZigZag.pullForm isOpen_faceSet D.action h 0 (θ g))
        (ZigZag.twForm (ZigZag.repCLM T.ρ' g) 0 (θ h))
      change avFormS (T.uni_sg (g * h)).smooth c _ = avFormS (T.uni_sg (g * h)).smooth c _ -
        avFormS (T.uni_sg (g * h)).smooth c _ at hs
      change avFormS (T.uni_sg (g * h)).smooth c _ = avFormS (T.uni_sg (g * h)).smooth c _ +
        avFormS (T.uni_sg (g * h)).smooth c _ at ha
      rw [hs, ha, a1, a2, hθA (g * h)]
      simp
    rw [hv']
    exact const_eq_zero_of_avFormS (T.uni_sg (g * h)) hc v hE hAv
  have hzero := deRhamClass_eq_zero_of_cocycle_datum isOpen_faceSet convex_faceSet
    faceSet_nonempty D.action T.ρ' (T.avInvT F - F) Ξ θ hom' hθd hcoc
  have hsub := (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action
    T.ρ').map_sub (T.avInvT F) F
  rw [hsub] at hzero
  exact sub_eq_zero.mp hzero

end TwistData

end TernaryPeriodPolynomials.Argument.FormClassK
