module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.Cell
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.FiniteSpherical
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SphericalBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneNontrivial

@[expose] public section


/-!
# The cell function at the good-line cusp

For the odd quadratic character `χ` of conductor three the spherical finite part `finiteLineVector`
of a line-induced section is not well defined, since `χ` is nontrivial on `Ẑ^×`.  Here the cell
function of `Cell.lean` is used instead: it is supported on the double coset `P_line(𝔸_f) · r⁻¹ ·
K` of the good-line cusp `r⁻¹`, where `K` is the finite level, and equals
`g = p r⁻¹ k ↦ χ_f(corner p) |corner p|^a |det block p|^b · π(block p) w`.

The cell is well defined because the stabiliser `P_line(𝔸_f) ∩ r⁻¹ K r` of the cusp consists of
elements whose integral corner is `≡ 1 (3)` and whose block lies in `GL₂(Ẑ)`: this is the content of
`lineCellFixes`, and it holds exactly when `χ` has conductor dividing three.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance (atFinite_mul)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.Spectral.CuspOrbits (lastRow_vecMul)
open TernaryPeriodPolynomials.Spectral.LevelOneNontrivial (ConductorThree)
open TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit (referenceIntegral)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)

namespace TernaryPeriodPolynomials.TwistedSource

/-! ## The finite factor as a representation of the line parabolic -/

section Hom

variable (σ : CuspidalRepresentation) (χ : RankOneCharacter) (a b : ℂ)

/-- `Φ p = finiteLineFactor χ a b p • π(atFinite (lineBlockGL p))` as a monoid hom on the finite
line parabolic. -/
def lineFactorHom : lineParabolic FiniteAdeles →* Module.End ℂ σ.H where
  toFun p := finiteLineFactor χ a b p.1 p.2 • σ.π (atFinite (lineBlockGL p.1 p.2))
  map_one' := by
    have h1 : (1 : FiniteGL) ∈ lineParabolic FiniteAdeles := (lineParabolic FiniteAdeles).one_mem
    have hblock : lineBlockGL (1 : FiniteGL) h1 = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lineBlockGL]
    show finiteLineFactor χ a b 1 h1 • σ.π (atFinite (lineBlockGL 1 h1)) = 1
    rw [finiteLineFactor_one, hblock,
      TernaryPeriodPolynomials.SphericalDetection.Helpers.atFinite_one, map_one, one_smul]
  map_mul' p q := by
    have hf := finiteLineFactor_mul χ a b p.2 q.2
    have hb := lineBlockGL_mul p.2 q.2
    show finiteLineFactor χ a b (p.1 * q.1) ((lineParabolic FiniteAdeles).mul_mem p.2 q.2) •
        σ.π (atFinite (lineBlockGL (p.1 * q.1) ((lineParabolic FiniteAdeles).mul_mem p.2 q.2))) =
      (finiteLineFactor χ a b p.1 p.2 • σ.π (atFinite (lineBlockGL p.1 p.2))) *
        (finiteLineFactor χ a b q.1 q.2 • σ.π (atFinite (lineBlockGL q.1 q.2)))
    rw [hf, hb, ← atFinite_mul, map_mul, smul_mul_assoc, mul_smul_comm,
      smul_smul]

theorem lineFactorHom_apply (p : lineParabolic FiniteAdeles) (w : σ.H) :
    lineFactorHom σ χ a b p w =
      finiteLineFactor χ a b p.1 p.2 • σ.π (atFinite (lineBlockGL p.1 p.2)) w := rfl

end Hom

/-! ## The good-line cusp -/

/-- The finite component of the cusp point `rationalGroup (rational referenceIntegral)⁻¹`. -/
def goodLineCusp : FiniteGL :=
  (GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles))⁻¹

theorem goodLineCusp_eq : goodLineCusp = rationalFinite (rational referenceIntegral)⁻¹ := by
  unfold goodLineCusp
  rw [map_inv, rationalFinite_goodLine]

/-! ## The factor on integral parabolic elements with corner `≡ 1 (3)` -/

/-- The finite factor is trivial on integral line-parabolic elements whose corner is `≡ 1 (3)`, for
a character of conductor dividing three. -/
theorem finiteLineFactor_integral_of_reduction_one (χ : RankOneCharacter) (a b : ℂ)
    (h3 : ConductorThree χ) {k : GeneralLinearGroup (Fin 3) IntegralAdeles}
    (hk : k ∈ lineParabolic IntegralAdeles)
    (hmap : GeneralLinearGroup.map integralEmbedding k ∈ lineParabolic FiniteAdeles)
    (hred : integralReduction (k.val 0 0) = 1) :
    finiteLineFactor χ a b (GeneralLinearGroup.map integralEmbedding k) hmap = 1 := by
  have hc : χ.toMonoidHom (integralAdeleUnit (lineCornerUnit k hk)) = 1 := h3 _ hred
  unfold finiteLineFactor
  rw [lineCornerUnit_map integralEmbedding k hk hmap, lineBlockGL_map integralEmbedding k hk hmap,
    finiteAdeleUnit_integral, finiteAdeleUnit_det_integral, hc,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit]
  ring

/-- **The congruence.**  If `p` in the finite line parabolic satisfies `p r⁻¹ = r⁻¹ k` with `k` in
the finite level, then `p` is the image of an integral line-parabolic matrix with corner `≡ 1 (3)`. -/
theorem goodLine_congruence {p : FiniteGL} (hp : p ∈ lineParabolic FiniteAdeles) {k : FiniteGL}
    (hk : k ∈ finiteLevel) (hpk : p * goodLineCusp = goodLineCusp * k) :
    ∃ P : GeneralLinearGroup (Fin 3) IntegralAdeles, P ∈ lineParabolic IntegralAdeles ∧
      p = GeneralLinearGroup.map integralEmbedding P ∧ integralReduction (P.val 0 0) = 1 := by
  obtain ⟨X, hXmem, hXk⟩ := Subgroup.mem_map.mp hk
  obtain ⟨P, hP⟩ : ∃ P : GeneralLinearGroup (Fin 3) IntegralAdeles,
      P = (goodLineFrame IntegralAdeles)⁻¹ * X * goodLineFrame IntegralAdeles := ⟨_, rfl⟩
  have hpk' : p * (GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles))⁻¹ =
      (GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles))⁻¹ * k := hpk
  have h1 : p = (GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles))⁻¹ * k *
      GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles) := by
    calc p = p * (GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles))⁻¹ *
          GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles) := by group
      _ = _ := by rw [hpk']
  have hPmap : GeneralLinearGroup.map integralEmbedding P = p := by
    rw [hP, map_mul, map_mul, map_inv, hXk]
    exact h1.symm
  have hPmem : P ∈ lineParabolic IntegralAdeles :=
    integral_mem_lineParabolic (by rw [hPmap]; exact hp)
  have h10 : P.val 1 0 = 0 := hPmem.1
  have h20 : P.val 2 0 = 0 := hPmem.2
  have hX : goodLineFrame IntegralAdeles * P * (goodLineFrame IntegralAdeles)⁻¹ = X := by
    rw [hP]
    group
  have e0 : X.val 2 0 = P.val 0 0 - (P.val 0 2 + P.val 1 2 + P.val 2 2) := by
    rw [← hX, Units.val_mul, Units.val_mul, goodLineFrame_val, goodLineFrame_inv_val]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, h10, h20]
    ring
  have e2 : X.val 2 2 = P.val 0 2 + P.val 1 2 + P.val 2 2 := by
    rw [← hX, Units.val_mul, Units.val_mul, goodLineFrame_val, goodLineFrame_inv_val]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  have hrow : ∀ j, integralReduction (X.val 2 j) = lastRow j := by
    intro j
    have h : lastRow ᵥ* (GeneralLinearGroup.map integralReduction X).val = lastRow := hXmem
    rw [lastRow_vecMul] at h
    exact congrFun h j
  have e : P.val 0 0 = X.val 2 0 + X.val 2 2 := by
    rw [e0, e2]
    ring
  refine ⟨P, hPmem, hPmap.symm, ?_⟩
  rw [e, map_add, hrow 0, hrow 2]
  simp [lastRow]

/-- On the stabiliser of the cusp, the finite factor fixes every spherical vector. -/
theorem lineFactor_apply_of_integral (χ : RankOneCharacter) (a b : ℂ) (h3 : ConductorThree χ)
    {σ : CuspidalRepresentation} {w : σ.H} (hw : w ∈ sphericalSubspace σ) {q : FiniteGL}
    (hq : q ∈ lineParabolic FiniteAdeles) {P : GeneralLinearGroup (Fin 3) IntegralAdeles}
    (hP : P ∈ lineParabolic IntegralAdeles) (hqP : q = GeneralLinearGroup.map integralEmbedding P)
    (hred : integralReduction (P.val 0 0) = 1) :
    finiteLineFactor χ a b q hq • σ.π (atFinite (lineBlockGL q hq)) w = w := by
  subst hqP
  rw [finiteLineFactor_integral_of_reduction_one χ a b h3 hP hq hred, one_smul,
    lineBlockGL_map integralEmbedding P hP hq]
  exact hw _

section Cell

variable (σ : CuspidalRepresentation) (χ : RankOneCharacter) (a b : ℂ)

/-- **The cell is well defined.** -/
theorem lineCellFixes (h3 : ConductorThree χ) :
    CellFixes (lineParabolic FiniteAdeles) finiteLevel goodLineCusp (lineFactorHom σ χ a b)
      (sphericalSubspace σ) := by
  intro p k hk hpk w hw
  obtain ⟨P, hPmem, hpP, hred⟩ := goodLine_congruence p.2 hk hpk
  rw [lineFactorHom_apply]
  exact lineFactor_apply_of_integral χ a b h3 hw p.2 hPmem hpP hred

/-- The cell function of the good-line cusp. -/
def lineCell (g : FiniteGL) : Module.End ℂ σ.H :=
  cellMap (lineParabolic FiniteAdeles) finiteLevel goodLineCusp (lineFactorHom σ χ a b) g

/-- **Left equivariance** under the finite line parabolic. -/
theorem lineCell_mul (h3 : ConductorThree χ) {w : σ.H} (hw : w ∈ sphericalSubspace σ)
    {p : FiniteGL} (hp : p ∈ lineParabolic FiniteAdeles) (g : FiniteGL) :
    lineCell σ χ a b (p * g) w =
      finiteLineFactor χ a b p hp • σ.π (atFinite (lineBlockGL p hp)) (lineCell σ χ a b g w) := by
  have h := cellMap_mul_left (lineCellFixes σ χ a b h3) ⟨p, hp⟩ g hw
  rw [lineFactorHom_apply] at h
  exact h

/-- **Right invariance** under the finite level. -/
theorem lineCell_level (h3 : ConductorThree χ) {w : σ.H} (hw : w ∈ sphericalSubspace σ)
    (g : FiniteGL) (k : finiteLevel) :
    lineCell σ χ a b (g * k.val) w = lineCell σ χ a b g w :=
  cellMap_mul_right (lineCellFixes σ χ a b h3) g k.property hw

/-- The cell function is the identity at the cusp. -/
theorem lineCell_cusp (h3 : ConductorThree χ) {w : σ.H} (hw : w ∈ sphericalSubspace σ) :
    lineCell σ χ a b goodLineCusp w = w :=
  cellMap_self (lineCellFixes σ χ a b h3) hw

theorem pi_atFinite_comm_atInfinity (f : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (h : BinaryRealGL) (w : σ.H) :
    σ.π (atFinite f) (σ.π (atInfinity h) w) = σ.π (atInfinity h) (σ.π (atFinite f) w) := by
  calc σ.π (atFinite f) (σ.π (atInfinity h) w)
      = (σ.π (atFinite f) * σ.π (atInfinity h)) w := (Module.End.mul_apply _ _ _).symm
    _ = σ.π (atFinite f * atInfinity h) w := by rw [← map_mul]
    _ = σ.π (atInfinity h * atFinite f) w := by rw [atFinite_mul_atInfinity_comm]
    _ = σ.π (atInfinity h) (σ.π (atFinite f) w) := by rw [map_mul, Module.End.mul_apply]

/-- Real translations commute with the cell function. -/
theorem lineCell_real (h3 : ConductorThree χ) {w : σ.H} (hw : w ∈ sphericalSubspace σ)
    (g : FiniteGL) (h : BinaryRealGL) :
    lineCell σ χ a b g (σ.π (atInfinity h) w) = σ.π (atInfinity h) (lineCell σ χ a b g w) := by
  have hw' := sphericalSubspace_real hw h
  by_cases hg : InCell (lineParabolic FiniteAdeles) finiteLevel goodLineCusp g
  · obtain ⟨p, k, hk, hgk⟩ := hg
    have e1 := cellMap_apply_of_eq (lineCellFixes σ χ a b h3) p hk hgk hw'
    have e2 := cellMap_apply_of_eq (lineCellFixes σ χ a b h3) p hk hgk hw
    unfold lineCell
    rw [e1, e2, lineFactorHom_apply, lineFactorHom_apply, map_smul,
      pi_atFinite_comm_atInfinity]
  · simp [lineCell, cellMap_eq_zero (Φ := lineFactorHom σ χ a b) hg]

/-- The cell function takes only two kinds of values, uniformly in the spherical input: zero, and
the finite factor of a parabolic element applied to the input. -/
theorem lineCell_apply_cases_uniform (h3 : ConductorThree χ) (g : FiniteGL) :
    (∀ w ∈ sphericalSubspace σ, lineCell σ χ a b g w = 0) ∨
      ∃ (p : FiniteGL) (hp : p ∈ lineParabolic FiniteAdeles), ∀ w ∈ sphericalSubspace σ,
        lineCell σ χ a b g w =
          finiteLineFactor χ a b p hp • σ.π (atFinite (lineBlockGL p hp)) w := by
  by_cases hg : InCell (lineParabolic FiniteAdeles) finiteLevel goodLineCusp g
  · obtain ⟨p, k, hk, hgk⟩ := hg
    refine Or.inr ⟨p.1, p.2, fun w hw => ?_⟩
    have e := cellMap_apply_of_eq (lineCellFixes σ χ a b h3) p hk hgk hw
    rw [lineFactorHom_apply] at e
    exact e
  · exact Or.inl fun w _ => by simp [lineCell, cellMap_eq_zero (Φ := lineFactorHom σ χ a b) hg]

/-- The cell function takes only two kinds of values: zero, and the finite factor of a parabolic
element applied to the input. -/
theorem lineCell_apply_cases (h3 : ConductorThree χ) {w : σ.H} (hw : w ∈ sphericalSubspace σ)
    (g : FiniteGL) :
    lineCell σ χ a b g w = 0 ∨ ∃ (p : FiniteGL) (hp : p ∈ lineParabolic FiniteAdeles),
      lineCell σ χ a b g w = finiteLineFactor χ a b p hp • σ.π (atFinite (lineBlockGL p hp)) w := by
  rcases lineCell_apply_cases_uniform σ χ a b h3 g with h | ⟨p, hp, h⟩
  · exact Or.inl (h w hw)
  · exact Or.inr ⟨p, hp, h w hw⟩

/-- The cell function preserves smooth spherical vectors. -/
theorem lineCell_smooth {w : σ.H} (hw : w ∈ σ.smooth) (h3 : ConductorThree χ)
    (hws : w ∈ sphericalSubspace σ) (g : FiniteGL) : lineCell σ χ a b g w ∈ σ.smooth := by
  rcases lineCell_apply_cases σ χ a b h3 hws g with h | ⟨_, _, h⟩
  · rw [h]
    exact σ.smooth.zero_mem
  · rw [h]
    exact σ.smooth.smul_mem _ (σ.smooth_stable _ _ hw)

end Cell

end TernaryPeriodPolynomials.TwistedSource
