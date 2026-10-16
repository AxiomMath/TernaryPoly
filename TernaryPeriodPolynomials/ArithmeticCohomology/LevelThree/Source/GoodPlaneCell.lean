module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.FiniteSphericalPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationPlaneLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Basic

@[expose] public section


/-!
# The finite part of a source at the good plane: the cell `P_plane(𝔸_f) · w · K₁`

The good plane is the cusp `(.plane, true)`; its reference frame is the permutation `w = (e₂ e₃)`,
an involution, so the cusp point `w⁻¹` is `w` itself.  A plane-induced section with a prescribed
level-three value at `w` is built at the finite places on the cell `P_plane(𝔸_f) · w · K₁`
(`K₁ = finiteLevel`) and extended by zero:
```
goodPlaneVector σ χ a b (p w k) v = χ_f(corner p) |corner p|^a |det block p|^b · π(block p) v.
```
`P_plane(𝔸_f) ∩ w K₁ w` consists of integral plane-parabolic matrices `w κ w` (`κ ∈ K₁`) whose `GL₂`
block has second row `(κ₂₀, κ₂₂) ≡ (0, 1)` modulo three (`planeParabolic_goodLevel_decomp`): the
block fixes `v ∈ levelThreeValues σ`, and the corner is an integral unit, killed by `χ` (trivial on
`Ẑ^×`, cf. the obstruction O1).  The vector is left `P_plane(𝔸_f)`-equivariant
(`goodPlaneVector_mul`), right `K₁`-invariant (`goodPlaneVector_mul_level`), equal to `v` at the
frame (`goodPlaneVector_frame`), zero off the cell, linear in `v`, smooth-valued on smooth vectors
and commutes with real translations of `v`.

This is the good-plane counterpart of the bad-line cell `badLineVector`
(`SourceConstruction.BadLineFinite`) and uses SC's plane Levi projections and finite factor
(`SourceConstruction.FiniteSphericalPlane`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance (atFinite_mul)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.MultiplicityOne
open TernaryPeriodPolynomials.Separation
  (PlaneLeviLevel goodPlaneFrameR goodPlaneFrameR_val goodPlaneFrameR_inv)

namespace TernaryPeriodPolynomials.LevelThreeSource

/-! ## The good-plane frame and the level -/

/-- The finite good-plane frame `w = (e₂ e₃)`. -/
def goodPlaneFrameF : FiniteGL :=
  GeneralLinearGroup.map integralEmbedding (goodPlaneFrameR IntegralAdeles)

theorem goodPlaneFrameF_inv : goodPlaneFrameF⁻¹ = goodPlaneFrameF := by
  rw [goodPlaneFrameF, ← map_inv, goodPlaneFrameR_inv]

/-- The last row of an integral element of the finite level reduces to `e₃` modulo three. -/
theorem reduction_lastRow_of_mem_comap {κ : GeneralLinearGroup (Fin 3) IntegralAdeles}
    (hκ : κ ∈ rowStabilizer.comap (GeneralLinearGroup.map integralReduction)) (j : Fin 3) :
    integralReduction (κ.val 2 j) = lastRow j := by
  have hrow : lastRow ᵥ* (GeneralLinearGroup.map integralReduction κ).val = lastRow := hκ
  rw [TernaryPeriodPolynomials.Spectral.CuspOrbits.lastRow_vecMul] at hrow
  have hj := congrFun hrow j
  simp only [GeneralLinearGroup.map_apply] at hj
  exact hj

/-- An element of the plane parabolic lying in `w K₁ w` is the image of an integral element of the
plane parabolic whose `GL₂` block lies in the level-three Levi level. -/
theorem planeParabolic_goodLevel_decomp {r k : FiniteGL} (hr : r ∈ planeParabolic FiniteAdeles)
    (hk : k ∈ finiteLevel) (hrk : r = goodPlaneFrameF * k * goodPlaneFrameF) :
    ∃ (c : GeneralLinearGroup (Fin 3) IntegralAdeles) (hc : c ∈ planeParabolic IntegralAdeles),
      r = GeneralLinearGroup.map integralEmbedding c ∧ PlaneLeviLevel (planeBlockGL c hc) := by
  obtain ⟨κ, hκ, hκk⟩ := Subgroup.mem_map.mp hk
  have hcr : GeneralLinearGroup.map integralEmbedding
      (goodPlaneFrameR IntegralAdeles * κ * goodPlaneFrameR IntegralAdeles) = r := by
    rw [map_mul, map_mul, hκk, hrk]
    rfl
  have hmap : GeneralLinearGroup.map integralEmbedding
      (goodPlaneFrameR IntegralAdeles * κ * goodPlaneFrameR IntegralAdeles) ∈
        planeParabolic FiniteAdeles := by
    rw [hcr]
    exact hr
  have hc := integral_mem_planeParabolic hmap
  refine ⟨_, hc, hcr.symm, ?_⟩
  have h0 := reduction_lastRow_of_mem_comap hκ 0
  have h2 := reduction_lastRow_of_mem_comap hκ 2
  have e10 : (goodPlaneFrameR IntegralAdeles * κ * goodPlaneFrameR IntegralAdeles).val 1 0 =
      κ.val 2 0 := by
    rw [Units.val_mul, Units.val_mul, goodPlaneFrameR_val]
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]
  have e11 : (goodPlaneFrameR IntegralAdeles * κ * goodPlaneFrameR IntegralAdeles).val 1 1 =
      κ.val 2 2 := by
    rw [Units.val_mul, Units.val_mul, goodPlaneFrameR_val]
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]
  refine ⟨?_, ?_⟩
  · rw [GeneralLinearGroup.map_apply]
    change integralReduction
      ((goodPlaneFrameR IntegralAdeles * κ * goodPlaneFrameR IntegralAdeles).val 1 0) = 0
    rw [e10]
    simpa [lastRow] using h0
  · rw [GeneralLinearGroup.map_apply]
    change integralReduction
      ((goodPlaneFrameR IntegralAdeles * κ * goodPlaneFrameR IntegralAdeles).val 1 1) = 1
    rw [e11]
    simpa [lastRow] using h2

theorem finitePlaneFactor_goodLevel (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1) {r k : FiniteGL}
    (hr : r ∈ planeParabolic FiniteAdeles) (hk : k ∈ finiteLevel)
    (hrk : r = goodPlaneFrameF * k * goodPlaneFrameF) :
    finitePlaneFactor χ a b r hr = 1 := by
  obtain ⟨c, hc, hrc, _⟩ := planeParabolic_goodLevel_decomp hr hk hrk
  subst hrc
  exact finitePlaneFactor_integral χ a b hχ hc hr

theorem planeBlockGL_goodLevel_fixed {σ : CuspidalRepresentation} {v : σ.H}
    (hv : v ∈ levelThreeValues σ) {r k : FiniteGL} (hr : r ∈ planeParabolic FiniteAdeles)
    (hk : k ∈ finiteLevel) (hrk : r = goodPlaneFrameF * k * goodPlaneFrameF) :
    σ.π (atFinite (planeBlockGL r hr)) v = v := by
  obtain ⟨c, hc, hrc, hlev⟩ := planeParabolic_goodLevel_decomp hr hk hrk
  subst hrc
  rw [planeBlockGL_map integralEmbedding c hc hr]
  exact hv (planeBlockGL c hc) hlev

/-! ## The cell vector -/

/-- The good-plane cell `P_plane(𝔸_f) · w · K₁`. -/
abbrev InGoodPlaneCell (g : FiniteGL) : Prop :=
  ∃ p : FiniteGL, p ∈ planeParabolic FiniteAdeles ∧
    ∃ k : FiniteGL, k ∈ finiteLevel ∧ g = p * goodPlaneFrameF * k

section Cell

variable (σ : CuspidalRepresentation)

open Classical in
/-- The value `χ_f(p) |p| · σ(block p) v` at a plane-parabolic element, and `0` elsewhere. -/
def goodPlaneCellValue (χ : RankOneCharacter) (a b : ℂ) (v : σ.H) (p : FiniteGL) : σ.H :=
  if hp : p ∈ planeParabolic FiniteAdeles then
    finitePlaneFactor χ a b p hp • σ.π (atFinite (planeBlockGL p hp)) v
  else 0

open Classical in
/-- **The finite part of a plane-induced vector on the good-plane cell.** -/
def goodPlaneVector (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (v : σ.H) : σ.H :=
  if h : InGoodPlaneCell g then goodPlaneCellValue σ χ a b v (Classical.choose h) else 0

variable {σ}

theorem goodPlaneCellValue_of_mem {χ : RankOneCharacter} {a b : ℂ} {v : σ.H} {p : FiniteGL}
    (hp : p ∈ planeParabolic FiniteAdeles) :
    goodPlaneCellValue σ χ a b v p =
      finitePlaneFactor χ a b p hp • σ.π (atFinite (planeBlockGL p hp)) v := by
  unfold goodPlaneCellValue
  exact dite_eq_left hp

theorem goodPlaneVector_of_cell {χ : RankOneCharacter} {a b : ℂ} {v : σ.H} {g : FiniteGL}
    (h : InGoodPlaneCell g) :
    goodPlaneVector σ χ a b g v = goodPlaneCellValue σ χ a b v (Classical.choose h) := by
  unfold goodPlaneVector
  exact dite_eq_left h

theorem goodPlaneVector_of_not_cell {χ : RankOneCharacter} {a b : ℂ} {v : σ.H} {g : FiniteGL}
    (h : ¬ InGoodPlaneCell g) : goodPlaneVector σ χ a b g v = 0 := by
  unfold goodPlaneVector
  exact dite_eq_right h

theorem inGoodPlaneCell_of_mul_left {g p : FiniteGL} (hp : p ∈ planeParabolic FiniteAdeles)
    (h : InGoodPlaneCell (p * g)) : InGoodPlaneCell g := by
  obtain ⟨q, hq, k, hk, hpg⟩ := h
  refine ⟨p⁻¹ * q,
    (planeParabolic FiniteAdeles).mul_mem ((planeParabolic FiniteAdeles).inv_mem hp) hq, k, hk, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_assoc q, ← hpg, inv_mul_cancel_left]

theorem inGoodPlaneCell_of_mul_level {g k : FiniteGL} (hk : k ∈ finiteLevel)
    (h : InGoodPlaneCell (g * k)) : InGoodPlaneCell g := by
  obtain ⟨q, hq, k', hk', hgk⟩ := h
  exact ⟨q, hq, k' * k⁻¹, finiteLevel.mul_mem hk' (finiteLevel.inv_mem hk),
    by rw [← mul_assoc, ← hgk, mul_inv_cancel_right]⟩

/-! ### Independence of the decomposition -/

theorem goodPlaneCellValue_mul_level (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ levelThreeValues σ) {p r k : FiniteGL}
    (hp : p ∈ planeParabolic FiniteAdeles) (hr : r ∈ planeParabolic FiniteAdeles)
    (hk : k ∈ finiteLevel) (hrk : r = goodPlaneFrameF * k * goodPlaneFrameF) :
    goodPlaneCellValue σ χ a b v (p * r) = goodPlaneCellValue σ χ a b v p := by
  have hpr : p * r ∈ planeParabolic FiniteAdeles := (planeParabolic FiniteAdeles).mul_mem hp hr
  rw [goodPlaneCellValue_of_mem hpr, goodPlaneCellValue_of_mem hp,
    finitePlaneFactor_mul χ a b hp hr, finitePlaneFactor_goodLevel χ a b hχ hr hk hrk, mul_one,
    planeBlockGL_mul hp hr, ← atFinite_mul, map_mul, Module.End.mul_apply,
    planeBlockGL_goodLevel_fixed hv hr hk hrk]

/-- **Independence of the decomposition.** -/
theorem goodPlaneVector_eq (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ levelThreeValues σ) {g p k : FiniteGL}
    (hp : p ∈ planeParabolic FiniteAdeles) (hk : k ∈ finiteLevel)
    (hg : g = p * goodPlaneFrameF * k) :
    goodPlaneVector σ χ a b g v = goodPlaneCellValue σ χ a b v p := by
  have hcell : InGoodPlaneCell g := ⟨p, hp, k, hk, hg⟩
  have hq := (Classical.choose_spec hcell).1
  obtain ⟨k', hk', hgk'⟩ := (Classical.choose_spec hcell).2
  have h : p * goodPlaneFrameF * k = Classical.choose hcell * goodPlaneFrameF * k' :=
    hg.symm.trans hgk'
  have hqeq : Classical.choose hcell =
      p * (goodPlaneFrameF * (k * k'⁻¹) * goodPlaneFrameF) := by
    calc Classical.choose hcell =
          Classical.choose hcell * goodPlaneFrameF * k' * k'⁻¹ * goodPlaneFrameF⁻¹ := by group
      _ = p * goodPlaneFrameF * k * k'⁻¹ * goodPlaneFrameF⁻¹ := by rw [← h]
      _ = p * (goodPlaneFrameF * (k * k'⁻¹) * goodPlaneFrameF) := by
        rw [goodPlaneFrameF_inv]
        group
  have hr : k * k'⁻¹ ∈ finiteLevel := finiteLevel.mul_mem hk (finiteLevel.inv_mem hk')
  have hrP : goodPlaneFrameF * (k * k'⁻¹) * goodPlaneFrameF ∈ planeParabolic FiniteAdeles := by
    have hrr : goodPlaneFrameF * (k * k'⁻¹) * goodPlaneFrameF = p⁻¹ * Classical.choose hcell := by
      rw [hqeq, inv_mul_cancel_left]
    rw [hrr]
    exact (planeParabolic FiniteAdeles).mul_mem ((planeParabolic FiniteAdeles).inv_mem hp) hq
  rw [goodPlaneVector_of_cell hcell, hqeq]
  exact goodPlaneCellValue_mul_level χ a b hχ hv hp hrP hr rfl

/-! ### Equivariance -/

/-- **Left `P_plane(𝔸_f)`-equivariance.** -/
theorem goodPlaneVector_mul (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ levelThreeValues σ) {p : FiniteGL}
    (hp : p ∈ planeParabolic FiniteAdeles) (g : FiniteGL) :
    goodPlaneVector σ χ a b (p * g) v =
      finitePlaneFactor χ a b p hp • σ.π (atFinite (planeBlockGL p hp))
        (goodPlaneVector σ χ a b g v) := by
  by_cases hcell : InGoodPlaneCell g
  · obtain ⟨q, hq, k, hk, hg⟩ := hcell
    have hpq : p * q ∈ planeParabolic FiniteAdeles := (planeParabolic FiniteAdeles).mul_mem hp hq
    rw [goodPlaneVector_eq χ a b hχ hv hpq hk
        (show p * g = p * q * goodPlaneFrameF * k by rw [hg]; group),
      goodPlaneVector_eq χ a b hχ hv hq hk hg, goodPlaneCellValue_of_mem hpq,
      goodPlaneCellValue_of_mem hq, finitePlaneFactor_mul χ a b hp hq, planeBlockGL_mul hp hq,
      ← atFinite_mul, map_mul, Module.End.mul_apply, map_smul, smul_smul]
  · have hnc : ¬ InGoodPlaneCell (p * g) := fun h => hcell (inGoodPlaneCell_of_mul_left hp h)
    rw [goodPlaneVector_of_not_cell hcell, goodPlaneVector_of_not_cell hnc, map_zero, smul_zero]

/-- **Right `K₁`-invariance.** -/
theorem goodPlaneVector_mul_level (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ levelThreeValues σ) (g : FiniteGL) (k : finiteLevel) :
    goodPlaneVector σ χ a b (g * k.val) v = goodPlaneVector σ χ a b g v := by
  by_cases hcell : InGoodPlaneCell g
  · obtain ⟨q, hq, k', hk', hg⟩ := hcell
    rw [goodPlaneVector_eq χ a b hχ hv hq (finiteLevel.mul_mem hk' k.property)
        (show g * k.val = q * goodPlaneFrameF * (k' * k.val) by rw [hg, mul_assoc]),
      goodPlaneVector_eq χ a b hχ hv hq hk' hg]
  · have hnc : ¬ InGoodPlaneCell (g * k.val) := fun h =>
      hcell (inGoodPlaneCell_of_mul_level k.property h)
    rw [goodPlaneVector_of_not_cell hcell, goodPlaneVector_of_not_cell hnc]

/-- **The value at the cusp point** (the frame) is the level-three vector itself. -/
theorem goodPlaneVector_frame (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ levelThreeValues σ) :
    goodPlaneVector σ χ a b goodPlaneFrameF v = v := by
  have h1 : (1 : FiniteGL) ∈ planeParabolic FiniteAdeles := (planeParabolic FiniteAdeles).one_mem
  rw [goodPlaneVector_eq χ a b hχ hv h1 (one_mem finiteLevel) (by group),
    goodPlaneCellValue_of_mem h1, finitePlaneFactor_one, one_smul]
  have hblock : planeBlockGL (1 : FiniteGL) h1 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planeBlockGL]
  rw [hblock, TernaryPeriodPolynomials.SphericalDetection.Helpers.atFinite_one, map_one,
    Module.End.one_apply]

/-! ### Scalar-times-translate form

As SC's spherical `finitePlaneVector` (whose plane source uses it through `cFin` and `bFin`), the
cell vector is a scalar times a finite translate of `v`. -/

open Classical in
/-- The scalar of the good-plane cell vector: the finite factor on the cell, `0` off it. -/
def goodPlaneScalar (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) : ℂ :=
  if h : InGoodPlaneCell g then
    finitePlaneFactor χ a b (Classical.choose h) (Classical.choose_spec h).1
  else 0

open Classical in
/-- The finite `GL₂` translate of the good-plane cell vector (`1` off the cell). -/
def goodPlaneBlock (g : FiniteGL) : BinaryFiniteGL :=
  if h : InGoodPlaneCell g then planeBlockGL (Classical.choose h) (Classical.choose_spec h).1
  else 1

theorem goodPlaneVector_eq_smul (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (v : σ.H) :
    goodPlaneVector σ χ a b g v =
      goodPlaneScalar χ a b g • σ.π (atFinite (goodPlaneBlock g)) v := by
  unfold goodPlaneVector goodPlaneScalar goodPlaneBlock
  by_cases h : InGoodPlaneCell g
  · rw [dite_eq_left h, dite_eq_left h, dite_eq_left h, goodPlaneCellValue_of_mem (Classical.choose_spec h).1]
  · rw [dite_eq_right h, dite_eq_right h, dite_eq_right h, zero_smul]

/-- Off the cell the vector vanishes. -/
theorem goodPlaneVector_eq_zero (χ : RankOneCharacter) (a b : ℂ) {g : FiniteGL}
    (hg : ¬ InGoodPlaneCell g) (v : σ.H) : goodPlaneVector σ χ a b g v = 0 :=
  goodPlaneVector_of_not_cell hg

/-! ### Linearity, smoothness, real translations -/

theorem goodPlaneCellValue_add (χ : RankOneCharacter) (a b : ℂ) (p : FiniteGL) (v w : σ.H) :
    goodPlaneCellValue σ χ a b (v + w) p =
      goodPlaneCellValue σ χ a b v p + goodPlaneCellValue σ χ a b w p := by
  unfold goodPlaneCellValue
  split_ifs
  · rw [map_add, smul_add]
  · rw [add_zero]

theorem goodPlaneVector_add (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (v w : σ.H) :
    goodPlaneVector σ χ a b g (v + w) =
      goodPlaneVector σ χ a b g v + goodPlaneVector σ χ a b g w := by
  unfold goodPlaneVector
  split_ifs
  · exact goodPlaneCellValue_add χ a b _ v w
  · rw [add_zero]

theorem goodPlaneCellValue_smul (χ : RankOneCharacter) (a b : ℂ) (p : FiniteGL) (c : ℂ)
    (v : σ.H) : goodPlaneCellValue σ χ a b (c • v) p = c • goodPlaneCellValue σ χ a b v p := by
  unfold goodPlaneCellValue
  split_ifs
  · rw [map_smul, smul_comm]
  · rw [smul_zero]

theorem goodPlaneVector_smul (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (c : ℂ)
    (v : σ.H) : goodPlaneVector σ χ a b g (c • v) = c • goodPlaneVector σ χ a b g v := by
  unfold goodPlaneVector
  split_ifs
  · exact goodPlaneCellValue_smul χ a b _ c v
  · rw [smul_zero]

theorem goodPlaneVector_smooth (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) {v : σ.H}
    (hv : v ∈ σ.smooth) : goodPlaneVector σ χ a b g v ∈ σ.smooth := by
  unfold goodPlaneVector goodPlaneCellValue
  split_ifs
  · exact σ.smooth.smul_mem _ (σ.smooth_stable _ _ hv)
  · exact σ.smooth.zero_mem
  · exact σ.smooth.zero_mem

/-- Real translations of the vector commute with the finite part. -/
theorem goodPlaneVector_real (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (v : σ.H)
    (h : BinaryRealGL) :
    goodPlaneVector σ χ a b g (σ.π (atInfinity h) v) =
      σ.π (atInfinity h) (goodPlaneVector σ χ a b g v) := by
  unfold goodPlaneVector goodPlaneCellValue
  split_ifs
  · rw [map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      atFinite_mul_atInfinity_comm]
  · rw [map_zero]
  · rw [map_zero]

/-- Level-three vectors are stable under real translations. -/
theorem levelThreeValues_real {v : σ.H} (hv : v ∈ levelThreeValues σ) (h : BinaryRealGL) :
    σ.π (atInfinity h) v ∈ levelThreeValues σ := by
  intro k hk
  rw [← Module.End.mul_apply, ← map_mul, atFinite_mul_atInfinity_comm, map_mul,
    Module.End.mul_apply, hv k hk]

end Cell

end TernaryPeriodPolynomials.LevelThreeSource
