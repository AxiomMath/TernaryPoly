module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.Cell
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.FiniteSphericalPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneNontrivial
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspOrbits

@[expose] public section


/-!
# The cell function of a plane-induced section at the identity-plane cusp

For a character `χ` of conductor dividing three the spherical finite part `finitePlaneVector` of a
plane-induced section does not exist (it needs `χ` trivial on all of `Ẑ^×`).  Instead the finite part
is the cell function of `Cell.lean` for the plane parabolic `P_plane(𝔸_f)`, the finite level `K₁` and
the cusp frame `q = 1`, with the representation `Φ p = χ_f(corner p) |corner p|^a |det block p|^b ·
π(block p)` (`planeFactorHom`).  It is well defined on the `GL₂(Ẑ)`-fixed vectors
(`planeCellFixes`): an element of `P_plane(𝔸_f) ∩ K₁` is an integral plane-parabolic matrix whose last
row reduces to `(0, 0, 1)` modulo three, so its corner is an integral unit congruent to one modulo
three, on which `χ` is trivial by `ConductorThree`, and its block lies in `GL₂(Ẑ)`.

The resulting `planeCell σ χ a b` is left `P_plane(𝔸_f)`-equivariant with the plane factor (`planeCell_mul`), right `K₁`-invariant (`planeCell_level`), the identity at `1`
(`planeCell_one`), zero off the cell, commutes with real translations and preserves smooth vectors.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance (atFinite_mul)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Spectral.LevelOneNontrivial (ConductorThree)

namespace TernaryPeriodPolynomials.TwistedSource

/-! ## Integral elements of the finite level -/

/-- The last row of an integral matrix whose finite image lies in the finite level reduces to
`(0, 0, 1)` modulo three. -/
theorem planeLevel_lastRow {m : GeneralLinearGroup (Fin 3) IntegralAdeles}
    (h : GeneralLinearGroup.map integralEmbedding m ∈ finiteLevel) (j : Fin 3) :
    integralReduction (m.val 2 j) = lastRow j := by
  obtain ⟨m', hm', hmm⟩ := Subgroup.mem_map.mp h
  have hentry : ∀ i j, m'.val i j = m.val i j := by
    intro i j
    apply integralEmbedding_injective
    have h' := congrArg (fun g : GeneralLinearGroup (Fin 3) FiniteAdeles => g.val i j) hmm
    simpa only [GeneralLinearGroup.map_apply] using h'
  have hrow : lastRow ᵥ* (GeneralLinearGroup.map integralReduction m').val = lastRow := hm'
  rw [TernaryPeriodPolynomials.Spectral.CuspOrbits.lastRow_vecMul] at hrow
  have hj := congrFun hrow j
  simp only [GeneralLinearGroup.map_apply, hentry] at hj
  exact hj

theorem planeBlockGL_one_eq (h1 : (1 : FiniteGL) ∈ planeParabolic FiniteAdeles) :
    planeBlockGL (1 : FiniteGL) h1 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeBlockGL]

/-! ## The finite factor on integral elements with corner congruent to one -/

/-- The finite plane factor is trivial on integral plane-parabolic elements whose corner is
congruent to one modulo three, when `χ` has conductor dividing three. -/
theorem finitePlaneFactor_integral_of_reduction_one (χ : RankOneCharacter) (a b : ℂ)
    (h3 : ConductorThree χ) {k : GeneralLinearGroup (Fin 3) IntegralAdeles}
    (hk : k ∈ planeParabolic IntegralAdeles)
    (hmap : GeneralLinearGroup.map integralEmbedding k ∈ planeParabolic FiniteAdeles)
    (hred : integralReduction (k.val 2 2) = 1) :
    finitePlaneFactor χ a b (GeneralLinearGroup.map integralEmbedding k) hmap = 1 := by
  have hc : integralReduction (planeCornerUnit k hk).val = 1 := hred
  unfold finitePlaneFactor
  rw [planeCornerUnit_map integralEmbedding k hk hmap, planeBlockGL_map integralEmbedding k hk hmap,
    finiteAdeleUnit_integral, finiteAdeleUnit_det_integral, h3 (planeCornerUnit k hk) hc,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit]
  ring

variable (σ : CuspidalRepresentation) (χ : RankOneCharacter) (a b : ℂ)

/-- The finite plane factor as a representation of the plane parabolic. -/
def planeFactorHom : planeParabolic FiniteAdeles →* Module.End ℂ σ.H where
  toFun p := finitePlaneFactor χ a b p.1 p.2 • σ.π (atFinite (planeBlockGL p.1 p.2))
  map_one' := by
    have h1 : (1 : FiniteGL) ∈ planeParabolic FiniteAdeles := (planeParabolic FiniteAdeles).one_mem
    change finitePlaneFactor χ a b 1 h1 • σ.π (atFinite (planeBlockGL (1 : FiniteGL) h1)) = 1
    rw [finitePlaneFactor_one, one_smul, planeBlockGL_one_eq h1,
      TernaryPeriodPolynomials.SphericalDetection.Helpers.atFinite_one, map_one]
  map_mul' := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩
    change finitePlaneFactor χ a b (p * q) ((planeParabolic FiniteAdeles).mul_mem hp hq) •
        σ.π (atFinite (planeBlockGL (p * q) ((planeParabolic FiniteAdeles).mul_mem hp hq))) =
      (finitePlaneFactor χ a b p hp • σ.π (atFinite (planeBlockGL p hp))) *
        (finitePlaneFactor χ a b q hq • σ.π (atFinite (planeBlockGL q hq)))
    rw [finitePlaneFactor_mul χ a b hp hq, planeBlockGL_mul hp hq, ← atFinite_mul, map_mul,
      smul_mul_assoc, mul_smul_comm, smul_smul]

theorem planeFactorHom_apply (p : planeParabolic FiniteAdeles) (w : σ.H) :
    planeFactorHom σ χ a b p w =
      finitePlaneFactor χ a b p.1 p.2 • σ.π (atFinite (planeBlockGL p.1 p.2)) w :=
  rfl

/-- On a spherical vector, an integral plane-parabolic element with corner congruent to one acts
trivially through the plane factor. -/
theorem planeFactor_smul_integral (h3 : ConductorThree χ) {w : σ.H}
    (hw : w ∈ sphericalSubspace σ) {X : GeneralLinearGroup (Fin 3) IntegralAdeles}
    (hX : X ∈ planeParabolic IntegralAdeles)
    (hmap : GeneralLinearGroup.map integralEmbedding X ∈ planeParabolic FiniteAdeles)
    (hred : integralReduction (X.val 2 2) = 1) :
    finitePlaneFactor χ a b (GeneralLinearGroup.map integralEmbedding X) hmap •
        σ.π (atFinite (planeBlockGL (GeneralLinearGroup.map integralEmbedding X) hmap)) w = w := by
  rw [finitePlaneFactor_integral_of_reduction_one χ a b h3 hX hmap hred, one_smul,
    planeBlockGL_map integralEmbedding X hX hmap]
  exact hw (planeBlockGL X hX)

/-- The plane factor fixes every spherical vector on `P_plane(𝔸_f) ∩ K₁`. -/
theorem planeCellFixes (h3 : ConductorThree χ) :
    CellFixes (planeParabolic FiniteAdeles) finiteLevel 1 (planeFactorHom σ χ a b)
      (sphericalSubspace σ) := by
  rintro ⟨p, hp⟩ k hk hpk w hw
  have hpk' : p = k := by simpa using hpk
  obtain ⟨X, -, hXk⟩ := Subgroup.mem_map.mp hk
  have hX : GeneralLinearGroup.map integralEmbedding X = p := hXk.trans hpk'.symm
  have hlevel : GeneralLinearGroup.map integralEmbedding X ∈ finiteLevel := by
    rw [hXk]
    exact hk
  have hmap : GeneralLinearGroup.map integralEmbedding X ∈ planeParabolic FiniteAdeles := by
    rw [hX]
    exact hp
  have hXpl : X ∈ planeParabolic IntegralAdeles := integral_mem_planeParabolic hmap
  have hred : integralReduction (X.val 2 2) = 1 := by
    simpa [lastRow] using planeLevel_lastRow hlevel 2
  subst hX
  rw [planeFactorHom_apply]
  exact planeFactor_smul_integral σ χ a b h3 hw hXpl hmap hred

/-! ## The cell function -/

/-- The finite part of a plane-induced section at the identity-plane cusp: the cell function of the
plane factor on `P_plane(𝔸_f) · 1 · K₁`. -/
def planeCell (g : FiniteGL) : Module.End ℂ σ.H :=
  cellMap (planeParabolic FiniteAdeles) finiteLevel 1 (planeFactorHom σ χ a b) g

/-- **Left equivariance.** -/
theorem planeCell_mul (h3 : ConductorThree χ) {w : σ.H} (hw : w ∈ sphericalSubspace σ)
    {p : FiniteGL} (hp : p ∈ planeParabolic FiniteAdeles) (g : FiniteGL) :
    planeCell σ χ a b (p * g) w =
      finitePlaneFactor χ a b p hp • σ.π (atFinite (planeBlockGL p hp)) (planeCell σ χ a b g w) :=
  (cellMap_mul_left (planeCellFixes σ χ a b h3) ⟨p, hp⟩ g hw).trans
    (planeFactorHom_apply σ χ a b ⟨p, hp⟩ _)

/-- **Right invariance under the finite level.** -/
theorem planeCell_level (h3 : ConductorThree χ) {w : σ.H} (hw : w ∈ sphericalSubspace σ)
    (g : FiniteGL) (k : finiteLevel) :
    planeCell σ χ a b (g * k.val) w = planeCell σ χ a b g w :=
  cellMap_mul_right (planeCellFixes σ χ a b h3) g k.property hw

/-- The cell function is the identity at the cusp point. -/
theorem planeCell_one (h3 : ConductorThree χ) {w : σ.H} (hw : w ∈ sphericalSubspace σ) :
    planeCell σ χ a b 1 w = w :=
  cellMap_self (planeCellFixes σ χ a b h3) hw

/-- The value of the cell function is zero or the plane factor applied to the vector. -/
theorem planeCell_apply_cases (h3 : ConductorThree χ) {w : σ.H} (hw : w ∈ sphericalSubspace σ)
    (g : FiniteGL) :
    planeCell σ χ a b g w = 0 ∨ ∃ (p : FiniteGL) (hp : p ∈ planeParabolic FiniteAdeles),
      planeCell σ χ a b g w =
        finitePlaneFactor χ a b p hp • σ.π (atFinite (planeBlockGL p hp)) w := by
  by_cases hcell : InCell (planeParabolic FiniteAdeles) finiteLevel 1 g
  · obtain ⟨p, k, hk, hg⟩ := hcell
    right
    refine ⟨p.1, p.2, ?_⟩
    unfold planeCell
    rw [cellMap_apply_of_eq (planeCellFixes σ χ a b h3) p hk hg hw, planeFactorHom_apply]
  · left
    unfold planeCell
    rw [cellMap_eq_zero hcell]
    simp

/-- The cell function vanishes on all spherical vectors, or is one fixed plane factor on all of
them. -/
theorem planeCell_apply_cases_uniform (h3 : ConductorThree χ) (g : FiniteGL) :
    (∀ w ∈ sphericalSubspace σ, planeCell σ χ a b g w = 0) ∨
      ∃ (p : FiniteGL) (hp : p ∈ planeParabolic FiniteAdeles), ∀ w ∈ sphericalSubspace σ,
        planeCell σ χ a b g w =
          finitePlaneFactor χ a b p hp • σ.π (atFinite (planeBlockGL p hp)) w := by
  by_cases hcell : InCell (planeParabolic FiniteAdeles) finiteLevel 1 g
  · obtain ⟨p, k, hk, hg⟩ := hcell
    right
    refine ⟨p.1, p.2, fun w hw => ?_⟩
    unfold planeCell
    rw [cellMap_apply_of_eq (planeCellFixes σ χ a b h3) p hk hg hw, planeFactorHom_apply]
  · left
    intro w _
    unfold planeCell
    rw [cellMap_eq_zero hcell]
    simp

/-- Real translations commute with the cell function. -/
theorem planeCell_real (h3 : ConductorThree χ) {w : σ.H} (hw : w ∈ sphericalSubspace σ)
    (g : FiniteGL) (h : BinaryRealGL) :
    planeCell σ χ a b g (σ.π (atInfinity h) w) = σ.π (atInfinity h) (planeCell σ χ a b g w) := by
  have hw' : σ.π (atInfinity h) w ∈ sphericalSubspace σ := sphericalSubspace_real hw h
  have hfix := planeCellFixes σ χ a b h3
  by_cases hcell : InCell (planeParabolic FiniteAdeles) finiteLevel 1 g
  · obtain ⟨p, k, hk, hg⟩ := hcell
    unfold planeCell
    rw [cellMap_apply_of_eq hfix p hk hg hw', cellMap_apply_of_eq hfix p hk hg hw]
    simp only [planeFactorHom_apply]
    rw [map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      atFinite_mul_atInfinity_comm]
  · unfold planeCell
    rw [cellMap_eq_zero hcell]
    simp

/-- The cell function preserves smooth vectors. -/
theorem planeCell_smooth {w : σ.H} (h3 : ConductorThree χ) (hw : w ∈ sphericalSubspace σ)
    (hs : w ∈ σ.smooth) (g : FiniteGL) : planeCell σ χ a b g w ∈ σ.smooth := by
  rcases planeCell_apply_cases σ χ a b h3 hw g with h | ⟨_, _, h⟩
  · rw [h]
    exact σ.smooth.zero_mem
  · rw [h]
    exact σ.smooth.smul_mem _ (σ.smooth_stable _ _ hs)

end TernaryPeriodPolynomials.TwistedSource
