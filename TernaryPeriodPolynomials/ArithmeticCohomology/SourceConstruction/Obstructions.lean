module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationPlaneLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationLineType
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Norm

@[expose] public section


/-!
# Character obstructions at the four cusps

The value of a normalized induced section at the reference frame of a cusp is an eigenvector of
the finite rank-one Levi units that the frame moves into the finite level, with eigenvalue the
character `χ`. Hence:

* good plane: every `u ∈ Ẑ^×` is moved into the level, so a section vanishes at the good-plane frame
  unless `χ` is trivial on `Ẑ^×` (`plane_induced_goodFrame_eq_zero`);
* identity plane and good line: the units `u ≡ 1 (3)` are moved into the level
  (`plane_induced_identity_eq_zero`, `line_induced_goodFrame_eq_zero`);
* bad line: every `u ∈ Ẑ^×` (`line_induced_identity_eq_zero`).

Consequences, all for an arbitrary `D`:

* if `χ` is nontrivial on some unit `u ≡ 1 (3)`, both summands vanish and `associatePair D = ⊥`
  (`associatePair_eq_bot_of_character`);
* if `χ(u) ≠ 1` for some `u ∈ Ẑ^×` (e.g. the odd quadratic character of conductor three),
  `coordinateImage D .plane true = ⊥` and `coordinateImage D .line false = ⊥`. In particular the
  construction input `SphericalGoodPlaneSource` is incompatible with `SphericalSourceConstruction`
  for spherical `D` (`not_spherical_of_goodPlane_inputs`), and source realization at the good plane
  is equivalent to the vanishing of the local joint eigenspace there
  (`sourceRealization_plane_true_iff_of_character`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit (referenceIntegral)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)

namespace TernaryPeriodPolynomials.SourceConstruction

variable {n : ℕ}

/-! ## Finite rank-one units -/

/-- A finite matrix whose last row reduces to `e₃*` modulo three lies in the finite level. -/
theorem mem_finiteLevel_of_lastRow (X : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (h : ∀ j, integralReduction (X.val 2 j) = lastRow j) :
    GeneralLinearGroup.map integralEmbedding X ∈ finiteLevel := by
  refine Subgroup.mem_map.mpr ⟨X, ?_, rfl⟩
  change lastRow ᵥ* (GeneralLinearGroup.map integralReduction X).val = lastRow
  rw [lastRow_vecMul]
  funext j
  exact h j

theorem planeLevi_integralAdeleUnit (u : IntegralAdelesˣ) :
    planeLevi (1 : BinaryAdelicGL) (integralAdeleUnit u) =
      atFinite (GeneralLinearGroup.map integralEmbedding
        (planeLevi (1 : GeneralLinearGroup (Fin 2) IntegralAdeles) u)) := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · change (planeBlock (1 : Matrix (Fin 2) (Fin 2) Adeles) (integralAdeleUnit u).val i j).1 =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
    fin_cases i <;> fin_cases j <;> simp [planeBlock, integralAdeleUnit]
  · change (planeBlock (1 : Matrix (Fin 2) (Fin 2) Adeles) (integralAdeleUnit u).val i j).2 =
      integralEmbedding (planeBlock (1 : Matrix (Fin 2) (Fin 2) IntegralAdeles) u.val i j)
    fin_cases i <;> fin_cases j <;> simp [planeBlock, integralAdeleUnit]

theorem lineLevi_integralAdeleUnit (u : IntegralAdelesˣ) :
    lineLevi (integralAdeleUnit u) (1 : BinaryAdelicGL) =
      atFinite (GeneralLinearGroup.map integralEmbedding
        (lineLevi u (1 : GeneralLinearGroup (Fin 2) IntegralAdeles))) := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · change ((lineLevi (integralAdeleUnit u) (1 : BinaryAdelicGL)).val i j).1 =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
    rw [lineLevi_val]
    fin_cases i <;> fin_cases j <;> simp [integralAdeleUnit]
  · change ((lineLevi (integralAdeleUnit u) (1 : BinaryAdelicGL)).val i j).2 =
      integralEmbedding ((lineLevi u (1 : GeneralLinearGroup (Fin 2) IntegralAdeles)).val i j)
    rw [lineLevi_val, lineLevi_val]
    fin_cases i <;> fin_cases j <;> simp [integralAdeleUnit]

/-- The eigenvalue argument: if a rank-one unit is moved into the level at a point, the value of
the section there is an eigenvector with eigenvalue `χ(u)`. -/
theorem eq_zero_of_character_shift {χ : ℂ} {value : ℂ} (h : value = χ * value) (hχ : χ ≠ 1) :
    value = 0 := by
  have hmul : (χ - 1) * value = 0 := by linear_combination -h
  rcases mul_eq_zero.mp hmul with h' | h'
  · exact absurd (sub_eq_zero.mp h') hχ
  · exact h'

/-! ## The plane cusps -/

theorem goodPlane_unit_conj_lastRow (u : IntegralAdelesˣ) (j : Fin 3) :
    (goodPlaneFrameR IntegralAdeles * planeLevi (1 : GeneralLinearGroup (Fin 2) IntegralAdeles) u *
        (goodPlaneFrameR IntegralAdeles)⁻¹).val 2 j =
      (Pi.single 2 1 : Fin 3 → IntegralAdeles) j := by
  rw [goodPlaneFrameR_inv, Units.val_mul, Units.val_mul, goodPlaneFrameR_val]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, planeLevi, planeBlock]

theorem goodPlane_unit_conj_mem (u : IntegralAdelesˣ) :
    GeneralLinearGroup.map integralEmbedding
      (goodPlaneFrameR IntegralAdeles * planeLevi (1 : GeneralLinearGroup (Fin 2) IntegralAdeles) u *
        (goodPlaneFrameR IntegralAdeles)⁻¹) ∈ finiteLevel := by
  apply mem_finiteLevel_of_lastRow
  intro j
  rw [goodPlane_unit_conj_lastRow]
  fin_cases j <;> simp [lastRow]

theorem goodPlane_unit_shift (u : IntegralAdelesˣ) :
    planeLevi (1 : BinaryAdelicGL) (integralAdeleUnit u) *
        rationalGroup (rational goodPlaneFrame)⁻¹ =
      rationalGroup (rational goodPlaneFrame)⁻¹ *
        atFinite (GeneralLinearGroup.map integralEmbedding
          (goodPlaneFrameR IntegralAdeles *
            planeLevi (1 : GeneralLinearGroup (Fin 2) IntegralAdeles) u *
            (goodPlaneFrameR IntegralAdeles)⁻¹)) := by
  rw [planeLevi_integralAdeleUnit, atFinite_mul_goodPlaneInv]
  simp only [map_mul, map_inv]

/-- **(O1)** A plane-induced section vanishes at the good-plane frame as soon as `χ` is nontrivial
on one finite integral unit. -/
theorem plane_induced_goodFrame_eq_zero (D : InducingData n) {s : ℂ} {f : AdelicGL → ℂ}
    (hf : IsInduced D .plane s f) (u : IntegralAdelesˣ)
    (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1) :
    f (rationalGroup (rational goodPlaneFrame)⁻¹) = 0 := by
  have hlevel : f (rationalGroup (rational goodPlaneFrame)⁻¹ *
      atFinite (GeneralLinearGroup.map integralEmbedding
        (goodPlaneFrameR IntegralAdeles *
          planeLevi (1 : GeneralLinearGroup (Fin 2) IntegralAdeles) u *
          (goodPlaneFrameR IntegralAdeles)⁻¹))) =
      f (rationalGroup (rational goodPlaneFrame)⁻¹) :=
    hf.2.1 ⟨_, goodPlane_unit_conj_mem u⟩ _
  have hchar := hf.2.2.2.2.1 (integralAdeleUnit u) (rationalGroup (rational goodPlaneFrame)⁻¹)
  rw [goodPlane_unit_shift, hlevel,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit,
    mul_one] at hchar
  exact eq_zero_of_character_shift hchar hu

theorem identityPlane_unit_mem (u : IntegralAdelesˣ) (hu : integralReduction u.val = 1) :
    GeneralLinearGroup.map integralEmbedding
      (planeLevi (1 : GeneralLinearGroup (Fin 2) IntegralAdeles) u) ∈ finiteLevel := by
  apply mem_finiteLevel_of_lastRow
  intro j
  fin_cases j <;> simp [planeLevi, planeBlock, lastRow, hu]

/-- **(O2, plane)** A plane-induced section vanishes at the identity as soon as `χ` is nontrivial
on one finite integral unit congruent to one modulo three. -/
theorem plane_induced_identity_eq_zero (D : InducingData n) {s : ℂ} {f : AdelicGL → ℂ}
    (hf : IsInduced D .plane s f) (u : IntegralAdelesˣ) (hu1 : integralReduction u.val = 1)
    (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1) : f 1 = 0 := by
  have hlevel : f (1 * atFinite (GeneralLinearGroup.map integralEmbedding
      (planeLevi (1 : GeneralLinearGroup (Fin 2) IntegralAdeles) u))) = f 1 :=
    hf.2.1 ⟨_, identityPlane_unit_mem u hu1⟩ _
  rw [one_mul] at hlevel
  have hchar := hf.2.2.2.2.1 (integralAdeleUnit u) 1
  rw [mul_one, planeLevi_integralAdeleUnit, hlevel,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit,
    mul_one] at hchar
  exact eq_zero_of_character_shift hchar hu

/-! ## The line cusps -/

theorem goodLine_unit_conj_lastRow (u : IntegralAdelesˣ) (j : Fin 3) :
    (goodLineFrame IntegralAdeles * lineLevi u (1 : GeneralLinearGroup (Fin 2) IntegralAdeles) *
        (goodLineFrame IntegralAdeles)⁻¹).val 2 j = ![u.val - 1, 0, 1] j := by
  rw [Units.val_mul, Units.val_mul, goodLineFrame_val, goodLineFrame_inv_val, lineLevi_val]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, sub_eq_add_neg]

theorem goodLine_unit_conj_mem (u : IntegralAdelesˣ) (hu : integralReduction u.val = 1) :
    GeneralLinearGroup.map integralEmbedding
      (goodLineFrame IntegralAdeles * lineLevi u (1 : GeneralLinearGroup (Fin 2) IntegralAdeles) *
        (goodLineFrame IntegralAdeles)⁻¹) ∈ finiteLevel := by
  apply mem_finiteLevel_of_lastRow
  intro j
  rw [goodLine_unit_conj_lastRow]
  fin_cases j <;> simp [lastRow]
  all_goals erw [map_sub, map_one, hu, sub_self]

theorem goodLine_unit_shift (u : IntegralAdelesˣ) :
    lineLevi (integralAdeleUnit u) (1 : BinaryAdelicGL) *
        rationalGroup (rational referenceIntegral)⁻¹ =
      rationalGroup (rational referenceIntegral)⁻¹ *
        atFinite (GeneralLinearGroup.map integralEmbedding
          (goodLineFrame IntegralAdeles *
            lineLevi u (1 : GeneralLinearGroup (Fin 2) IntegralAdeles) *
            (goodLineFrame IntegralAdeles)⁻¹)) := by
  rw [lineLevi_integralAdeleUnit, atFinite_mul_rationalGroup_general, map_inv rationalFinite,
    inv_inv, rationalFinite_goodLine]
  simp only [map_mul, map_inv]

/-- **(O2, line)** A line-induced section vanishes at the good-line frame as soon as `χ` is
nontrivial on one finite integral unit congruent to one modulo three. -/
theorem line_induced_goodFrame_eq_zero (D : InducingData n) {s : ℂ} {f : AdelicGL → ℂ}
    (hf : IsInduced D .line s f) (u : IntegralAdelesˣ) (hu1 : integralReduction u.val = 1)
    (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1) :
    f (rationalGroup (rational referenceIntegral)⁻¹) = 0 := by
  have hlevel : f (rationalGroup (rational referenceIntegral)⁻¹ *
      atFinite (GeneralLinearGroup.map integralEmbedding
        (goodLineFrame IntegralAdeles *
          lineLevi u (1 : GeneralLinearGroup (Fin 2) IntegralAdeles) *
          (goodLineFrame IntegralAdeles)⁻¹))) =
      f (rationalGroup (rational referenceIntegral)⁻¹) :=
    hf.2.1 ⟨_, goodLine_unit_conj_mem u hu1⟩ _
  have hchar := hf.2.2.2.2.1 (integralAdeleUnit u) (rationalGroup (rational referenceIntegral)⁻¹)
  rw [goodLine_unit_shift, hlevel,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit,
    mul_one] at hchar
  exact eq_zero_of_character_shift hchar hu

theorem badLine_unit_mem (u : IntegralAdelesˣ) :
    GeneralLinearGroup.map integralEmbedding
      (lineLevi u (1 : GeneralLinearGroup (Fin 2) IntegralAdeles)) ∈ finiteLevel := by
  apply mem_finiteLevel_of_lastRow
  intro j
  rw [lineLevi_val]
  fin_cases j <;> simp [lastRow]

/-- **(O3)** A line-induced section vanishes at the identity as soon as `χ` is nontrivial on one
finite integral unit. -/
theorem line_induced_identity_eq_zero (D : InducingData n) {s : ℂ} {f : AdelicGL → ℂ}
    (hf : IsInduced D .line s f) (u : IntegralAdelesˣ)
    (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1) : f 1 = 0 := by
  have hlevel : f (1 * atFinite (GeneralLinearGroup.map integralEmbedding
      (lineLevi u (1 : GeneralLinearGroup (Fin 2) IntegralAdeles)))) = f 1 :=
    hf.2.1 ⟨_, badLine_unit_mem u⟩ _
  rw [one_mul] at hlevel
  have hchar := hf.2.2.2.2.1 (integralAdeleUnit u) 1
  rw [mul_one, lineLevi_integralAdeleUnit, hlevel,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit,
    mul_one] at hchar
  exact eq_zero_of_character_shift hchar hu

/-- `LineCuspSection D false` forces `χ` to be trivial on every finite integral unit. -/
theorem character_trivial_of_lineCuspSection_false (D : InducingData n)
    (h : LineCuspSection D false) (u : IntegralAdelesˣ) :
    D.chi.toMonoidHom (integralAdeleUnit u) = 1 := by
  obtain ⟨f, hf, hne⟩ := h
  by_contra hu
  apply hne
  have hpoint : rationalGroup (lineCuspElement false)⁻¹ = 1 := by
    simp [lineCuspElement]
  rw [hpoint]
  exact line_induced_identity_eq_zero D hf u hu

/-! ## Cusp coordinates -/

/-- A source whose coefficient sections all vanish at the cusp point has zero coordinate there,
for every summand class. -/
theorem coordinateImage_eq_bot_of_vanish (D : InducingData n) (side : Side) (good : Bool)
    (q : RationalGL3) (hq : (QuotientGroup.mk q : Flags side) = cuspFlag side good)
    (hv : ∀ f : AdelicGL → ℂ, IsInduced D side cohomologicalPoint f → f (rationalGroup q⁻¹) = 0) :
    coordinateImage D side good = ⊥ := by
  have hle : boundarySummand D side ≤ LinearMap.ker (cuspRes n D.chi side good) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, hc, z, hz, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    refine cuspRes_classOf_eq_zero_of_vanish D side good hz q hq ?_
    intro x
    apply Subtype.ext
    apply MvPolynomial.ext
    intro m
    have hzero := hv _ (hc.1 (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) m)
    simpa using hzero
  rw [eq_bot_iff]
  rintro _ ⟨a, ha, rfl⟩
  rw [LinearMap.mem_ker.mp (hle ha)]
  exact Submodule.zero_mem _

/-- **(O1)** The good plane has no coordinate unless `χ` is trivial on `Ẑ^×`. -/
theorem coordinateImage_plane_true_eq_bot (D : InducingData n) (u : IntegralAdelesˣ)
    (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1) : coordinateImage D .plane true = ⊥ :=
  coordinateImage_eq_bot_of_vanish D .plane true (rational goodPlaneFrame) rfl
    fun _ hf => plane_induced_goodFrame_eq_zero D hf u hu

/-- **(O2, plane)** The identity plane has no coordinate unless `χ` is trivial on the units
congruent to one modulo three. -/
theorem coordinateImage_plane_false_eq_bot (D : InducingData n) (u : IntegralAdelesˣ)
    (hu1 : integralReduction u.val = 1) (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1) :
    coordinateImage D .plane false = ⊥ :=
  coordinateImage_eq_bot_of_vanish D .plane false 1 rfl fun _ hf => by
    rw [inv_one, map_one]
    exact plane_induced_identity_eq_zero D hf u hu1 hu

/-- **(O2, line)** The good line has no coordinate unless `χ` is trivial on the units congruent
to one modulo three. -/
theorem coordinateImage_line_true_eq_bot (D : InducingData n) (u : IntegralAdelesˣ)
    (hu1 : integralReduction u.val = 1) (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1) :
    coordinateImage D .line true = ⊥ :=
  coordinateImage_eq_bot_of_vanish D .line true (rational referenceIntegral) rfl
    fun _ hf => line_induced_goodFrame_eq_zero D hf u hu1 hu

/-- **(O3)** The bad line has no coordinate unless `χ` is trivial on `Ẑ^×`. -/
theorem coordinateImage_line_false_eq_bot (D : InducingData n) (u : IntegralAdelesˣ)
    (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1) : coordinateImage D .line false = ⊥ :=
  coordinateImage_eq_bot_of_vanish D .line false 1 rfl fun _ hf => by
    rw [inv_one, map_one]
    exact line_induced_identity_eq_zero D hf u hu

/-! ## Vanishing of the whole associate pair -/

theorem boundarySummand_eq_bot_of_coordinates (D : InducingData n) (side : Side)
    (htrue : coordinateImage D side true = ⊥) (hfalse : coordinateImage D side false = ⊥) :
    boundarySummand D side = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Submodule.mem_bot]
  refine (eq_zero_iff_cuspRes side a).mpr ⟨?_, ?_⟩
  · have hmem : cuspRes n D.chi side true a ∈ coordinateImage D side true := ⟨a, ha, rfl⟩
    rwa [htrue, Submodule.mem_bot] at hmem
  · have hmem : cuspRes n D.chi side false a ∈ coordinateImage D side false := ⟨a, ha, rfl⟩
    rwa [hfalse, Submodule.mem_bot] at hmem

/-- If `χ` is nontrivial on a finite integral unit congruent to one modulo three (conductor not
dividing three), the whole associate pair vanishes. -/
theorem associatePair_eq_bot_of_character (D : InducingData n) (u : IntegralAdelesˣ)
    (hu1 : integralReduction u.val = 1) (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1) :
    associatePair D = ⊥ := by
  have hplane := boundarySummand_eq_bot_of_coordinates D .plane
    (coordinateImage_plane_true_eq_bot D u hu) (coordinateImage_plane_false_eq_bot D u hu1 hu)
  have hline := boundarySummand_eq_bot_of_coordinates D .line
    (coordinateImage_line_true_eq_bot D u hu1 hu) (coordinateImage_line_false_eq_bot D u hu)
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  rw [hplane] at ha
  rw [hline] at hb
  simp only [SetLike.mem_coe, Submodule.mem_bot] at ha hb ⊢
  exact Prod.ext ha hb

/-! ## The inputs as stated -/

/-- For `χ` nontrivial on a finite integral unit, N2 holds exactly when no spherical `D` has a
nonzero plane summand. -/
theorem sphericalGoodPlaneSource_iff_of_character (D : InducingData n) (u : IntegralAdelesˣ)
    (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1) :
    SphericalGoodPlaneSource D ↔ (SphericalCusp D.cusp → boundarySummand D .plane = ⊥) := by
  constructor
  · intro hN2 hsph
    by_contra hS
    exact hN2 hsph hS (coordinateImage_plane_true_eq_bot D u hu)
  · intro h hsph hS
    exact absurd (h hsph) hS

/-- **N2 is incompatible with S1.** For `χ` nontrivial on a finite integral unit (for instance
the odd quadratic character of conductor three), `SphericalSourceConstruction D` and
`SphericalGoodPlaneSource D` together exclude every spherical `D`. -/
theorem not_spherical_of_goodPlane_inputs (D : InducingData n) (u : IntegralAdelesˣ)
    (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1)
    (hS1 : SphericalSourceConstruction D) (hN2 : SphericalGoodPlaneSource D) :
    ¬ SphericalCusp D.cusp := fun hsph =>
  hN2 hsph ((boundarySummand_plane_ne_bot_iff D).mpr (Or.inr (hS1 hsph)))
    (coordinateImage_plane_true_eq_bot D u hu)

/-- **S1 needs a nonzero pair.** For `χ` nontrivial on a unit congruent to one modulo three,
`SphericalSourceConstruction D` excludes every spherical `D`. -/
theorem not_spherical_of_sphericalSourceConstruction (D : InducingData n) (u : IntegralAdelesˣ)
    (hu1 : integralReduction u.val = 1) (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1)
    (hS1 : SphericalSourceConstruction D) : ¬ SphericalCusp D.cusp := fun hsph =>
  hS1 hsph (coordinateImage_plane_false_eq_bot D u hu1 hu)

theorem not_spherical_of_sphericalSourceConstructionLine (D : InducingData n)
    (u : IntegralAdelesˣ) (hu1 : integralReduction u.val = 1)
    (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1)
    (hS1 : SphericalSourceConstructionLine D) : ¬ SphericalCusp D.cusp := fun hsph =>
  hS1 hsph (coordinateImage_line_true_eq_bot D u hu1 hu)

/-- **The section input needs a character hypothesis (good line).** For `χ` nontrivial on a unit
congruent to one modulo three, `LineSectionConstruction D true` excludes every spherical `D`: no
line-induced section is nonzero at the good-line frame. -/
theorem not_spherical_of_lineSectionConstruction_true (D : InducingData n) (u : IntegralAdelesˣ)
    (hu1 : integralReduction u.val = 1) (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1)
    (hS : LineSectionConstruction D true) : ¬ SphericalCusp D.cusp := fun hsph => by
  obtain ⟨f, hf, hne⟩ := hS hsph
  exact hne (line_induced_goodFrame_eq_zero D hf u hu1 hu)

/-- A spherical vector is fixed by the bad-line Levi level. -/
theorem badLineLevelVector_of_spherical (σ : CuspidalRepresentation) (h : SphericalCusp σ) :
    BadLineLevelVector σ := by
  obtain ⟨v, hv, hfix⟩ := h
  exact ⟨v, hv, fun k _ => hfix k⟩

/-- **The section input needs a character hypothesis (bad line).** For `χ` nontrivial on a finite
integral unit, `LineSectionConstruction D false` excludes every `D` with a bad-line level vector,
in particular every spherical `D`. -/
theorem not_badLineLevelVector_of_lineSectionConstruction_false (D : InducingData n)
    (u : IntegralAdelesˣ) (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1)
    (hS : LineSectionConstruction D false) : ¬ BadLineLevelVector D.cusp := fun hlev => by
  exact hu (character_trivial_of_lineCuspSection_false D (hS hlev) u)

theorem not_spherical_of_lineSectionConstruction_false (D : InducingData n)
    (u : IntegralAdelesˣ) (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1)
    (hS : LineSectionConstruction D false) : ¬ SphericalCusp D.cusp := fun hsph =>
  not_badLineLevelVector_of_lineSectionConstruction_false D u hu hS
    (badLineLevelVector_of_spherical D.cusp hsph)

/-- For `χ` nontrivial on a finite integral unit, source realization at the good plane is exactly
the vanishing of the local joint eigenspace there. -/
theorem sourceRealization_plane_true_iff_of_character (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (u : IntegralAdelesˣ) (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1) :
    SourceRealization D hecke hhecke .plane true ↔
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane true = ⊥ := by
  have hno : ¬ ∃ c : sourceCocycles D .plane, sourceCoordinate D .plane true c ≠ 0 := fun h =>
    (coordinateImage_ne_bot_iff D .plane true).mpr h (coordinateImage_plane_true_eq_bot D u hu)
  constructor
  · intro h
    by_contra hne
    exact hno (h hne)
  · intro h hne
    exact absurd h hne

/-- The same at the bad line. -/
theorem sourceRealization_line_false_iff_of_character (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (u : IntegralAdelesˣ) (hu : D.chi.toMonoidHom (integralAdeleUnit u) ≠ 1) :
    SourceRealization D hecke hhecke .line false ↔
      localJoint n D.chi (pairCharacter D hecke hhecke) .line false = ⊥ := by
  have hno : ¬ ∃ c : sourceCocycles D .line, sourceCoordinate D .line false c ≠ 0 := fun h =>
    (coordinateImage_ne_bot_iff D .line false).mpr h (coordinateImage_line_false_eq_bot D u hu)
  constructor
  · intro h
    by_contra hne
    exact hno (h hne)
  · intro h hne
    exact absurd h hne

end TernaryPeriodPolynomials.SourceConstruction
