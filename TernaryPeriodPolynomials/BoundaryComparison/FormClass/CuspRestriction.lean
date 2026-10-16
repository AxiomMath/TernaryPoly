module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.FormClass
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaceTransfer
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaces
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneCusps
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.Face
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.FormClass

@[expose] public section


/-!
# Restriction of a `Γ(N)` class to the plane cusps; `PlaneLocallyInner` cusp by cusp

Formalized by Claude Sonnet 5.5.
Paper: Lemma C.3 and Proposition C.5.

* `resAtC N h n`: restriction of a complex class of `Γ(N)` to the plane group `Γ_{h⁻¹Ph}` (coefficients `faceRep N h n`).
* `planeH2Equiv_res_classPrincipal`: the face library's restriction/transport `planeH2Equiv ∘ resH2 ∘ classPrincipal` is `resAtC`.
* `planeFlagAt_surjective`: every rational plane is `h⁻¹⟨e₁,e₂⟩`, `h ∈ SL₃(ℤ)`.
* **`planeLocallyInner_iff_cusps`**: `PlaneLocallyInner x ↔ ∀ h, resAtC h x ∈ faceLocallyInner N h n`.
* **`formClass_planeLocallyInner`** (M3): the summed series class over cusps and seeds is `PlaneLocallyInner` provided each series restricts into the seed span of
  every cusp (`SeriesRestrictionInSeedSpan`, the explicit input from the constant-term package M1/M2).  Linear in the tuple of cusp forms; trivially true for the zero tuple.
* `formClass_line_eq_T`: with `classK_line_eq_T`, `r_Q = T(r_P)` at `K†` for the classical summed series.
* `res_classK_eq_avg` (M4, averaging formula): the restriction of `classK x` to `Γ_F ∩ Γ(N)` is the `K†/Γ(N)`-average of the translates of the transported class.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.FormSeriesModel
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.EisensteinClass

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) (h : SL(3, ℤ)) (n : ℕ)

/-- The restriction morphism `Res_{Γ_{h⁻¹Ph}} (E_n|Γ(N)) ⟶ E_n|Γ_{h⁻¹Ph}` (identity on values). -/
def cuspResRep : Rep.res (inclAt N h) (gammaRep (gammaN N) n) ⟶ faceRep N h n :=
  Rep.ofHom ⟨LinearMap.id, fun _ => LinearMap.ext fun _ => rfl⟩

/-- **Restriction of a complex class of `Γ(N)` to the plane group `Γ_{h⁻¹Ph}` of the cusp `h`.** -/
def resAtC : groupCohomology.H2 (gammaRep (gammaN N) n) →ₗ[ℂ] groupCohomology.H2 (faceRep N h n) :=
  (groupCohomology.map (inclAt N h) (cuspResRep N h n) 2).hom

variable (h3 : 3 ∣ N) (hN : 3 ≤ N) [NeZero N]

omit [NeZero N] in
theorem planeH2Equiv_res_classPrincipal (x : groupCohomology.H2 (gammaRep (gammaN N) n)) :
    planeH2Equiv N h3 h n trivialCharacter hN
        (resH2 (rationalCoefficientComponent n trivialCharacter)
          (fixedPointLevel_le_self (levelPrincipal N) (planeFlagAt h)) (classPrincipal N h3 n hN x)) =
      resAtC N h n x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    unfold planeH2Equiv
    rw [LinearEquiv.trans_apply, ← bridge_res]
    have hb : bridge (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N)
        (classPrincipal N h3 n hN (groupCohomology.H2π (gammaRep (gammaN N) n) c)) =
        (principalIso N h3 n hN).hom.hom (groupCohomology.H2π (gammaRep (gammaN N) n) c) := by
      unfold classPrincipal
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [hb]
    unfold principalIso
    simp only [groupCohomology.mapIso_hom]
    rw [groupCohomology.H2π_comp_map_apply]
    rw [groupCohomology.H2π_comp_map_apply]
    refine Eq.trans (EdgeNat.h2Map_π (planeEmbed N h3 h) (planeRep N h n trivialCharacter) (faceRep N h n)
      LinearMap.id (planeEmbed_hT N h n trivialCharacter h3) _) ?_
    unfold resAtC
    rw [groupCohomology.H2π_comp_map_apply]
    congr 1
    apply Subtype.ext
    funext p
    obtain ⟨a, b⟩ := p
    have hE : ∀ a : ↥(gammaNPAt N h), (principalEquiv N h3 hN).symm
        (Subgroup.inclusion (fixedPointLevel_le_self (levelPrincipal N) (planeFlagAt h)) (planeEmbed N h3 h a)) =
        inclAt N h a := by
      intro a
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      change (planeEmbed N h3 h a).1 = (Matrix.SpecialLinearGroup.mapGL ℚ (inclAt N h a).1)
      rw [planeEmbed_val]
      rfl
    change c.1 ((principalEquiv N h3 hN).symm
        (Subgroup.inclusion (fixedPointLevel_le_self (levelPrincipal N) (planeFlagAt h)) (planeEmbed N h3 h a)),
      (principalEquiv N h3 hN).symm
        (Subgroup.inclusion (fixedPointLevel_le_self (levelPrincipal N) (planeFlagAt h)) (planeEmbed N h3 h b))) =
      c.1 (inclAt N h a, inclAt N h b)
    rw [hE, hE]

omit [NeZero N] in
/-- **Every rational plane is `h⁻¹⟨e₁, e₂⟩` for an integral `h ∈ SL₃(ℤ)`.** -/
theorem planeFlagAt_surjective (F : Flags .plane) : ∃ h : SL(3, ℤ), planeFlagAt h = F := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective F
  obtain ⟨h, t, ht, hrow⟩ := exists_integral_cusp g
  refine ⟨h, ?_⟩
  change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) : Flags .plane) = QuotientGroup.mk g
  apply QuotientGroup.eq.mpr
  have e : ((Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ * g : GL (Fin 3) ℚ).val =
      ((h : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) * (g : Matrix (Fin 3) (Fin 3) ℚ) := by
    rw [map_inv, inv_inv, Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    rfl
  refine ⟨?_, ?_⟩
  · change ((Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ * g : GL (Fin 3) ℚ).val 2 0 = 0
    rw [e, hrow 0]; simp
  · change ((Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ * g : GL (Fin 3) ℚ).val 2 1 = 0
    rw [e, hrow 1]; simp

/-- **`PlaneLocallyInner` cusp by cusp.**  A class of `Γ(N)` is locally inner at every rational plane iff its restriction
to the plane group `Γ_{h⁻¹Ph}` of every integral cusp `h` lies in the face library's locally inner classes
`faceLocallyInner N h n` (vanishing on the radical and on the stabilizer of every complete flag over the plane). -/
theorem planeLocallyInner_iff_cusps (x : groupCohomology.H2 (gammaRep (gammaN N) n)) :
    PlaneLocallyInner N h3 hN n x ↔ ∀ h : SL(3, ℤ), resAtC N h n x ∈ faceLocallyInner N h n := by
  constructor
  · intro H h'
    have := H (planeFlagAt h')
    rw [mem_locallyInnerAt_iff_faceLocallyInner N h3 h' n trivialCharacter hN,
      planeH2Equiv_res_classPrincipal N h' n h3 hN] at this
    exact this
  · intro H F
    obtain ⟨h', rfl⟩ := planeFlagAt_surjective F
    rw [mem_locallyInnerAt_iff_faceLocallyInner N h3 h' n trivialCharacter hN,
      planeH2Equiv_res_classPrincipal N h' n h3 hN]
    exact H h'

theorem faceSeedSpan_le_cuspidalInH2 (n : ℕ) : faceSeedSpan N h n ≤ faceCuspidalInH2 N h n := by
  unfold faceSeedSpan faceCuspidalInH2
  exact Submodule.map_mono (Submodule.map_le_iff_le_comap.mp (faceSeed_map_edge_le_cuspidal N h n))

/-- **S6's M1/M2 as an explicit input** (the restriction of the series at the cusp `x` with seed `b` to every plane cusp `h⁻¹Ph` lies in
the span of the conjugated holomorphic and antiholomorphic seeds of that cusp; the standard cusp case is
`resP_eisensteinClass_eq` + `ConstantTermVanishing`).  It holds for the zero form. -/
def SeriesRestrictionInSeedSpan (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (x : PlaneFaces N) (b : Bool) : Prop :=
  ∀ h : SL(3, ℤ), resAtC N h n (complexify (gammaN N) n
    (TernaryPeriodPolynomials.Argument.Statements.EisensteinClass.eisensteinAtClass_gammaN N n f (Quotient.out x) b hn)) ∈
    faceSeedSpan N h n

/-- **M3 (reduction).**  If the restriction of each series `(x, b)` to every plane cusp lies in the seed span of that cusp
(`SeriesRestrictionInSeedSpan`, the input from S6's constant-term package), then the summed form class is locally inner at every
rational plane (`PlaneLocallyInner`), for every tuple of cusp forms.  Unconditionally linear: the zero tuple satisfies the premise. -/
theorem formClass_planeLocallyInner [Fintype (PlaneFaces N)] (hn : 4 ≤ n)
    (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (hS : ∀ x b, SeriesRestrictionInSeedSpan N n hn (f x b) x b) :
    PlaneLocallyInner N h3 hN n (∑ x, ∑ b, complexify (gammaN N) n
      (TernaryPeriodPolynomials.Argument.Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b)
        (Quotient.out x) b hn)) := by
  rw [planeLocallyInner_iff_cusps]
  intro h
  rw [map_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [← faceCuspidalInH2_eq_locallyInner N h n]
  exact faceSeedSpan_le_cuspidalInH2 N h n (hS x b h)

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers in
/-- **M4, the averaging formula for the plane coordinate (unconditional).**  The restriction of the `K†`-corestriction `classK x` to
`Γ_F ∩ Γ(N)` is the average over `K†/Γ(N)` of the conjugates of the transported class restricted to `Γ_F ∩ Γ(N)`:
the plane coordinate of `classK x` at the flag `F` is determined (`res_level_injective`) by the restrictions of the `K†`-translates
of `x` to the planes `q⁻¹F`; for the series these are the seed data of the cusps `q⁻¹F`. -/
theorem res_classK_eq_avg (x : groupCohomology.H2 (gammaRep (gammaN N) n)) (F : Flags .plane) :
    resH2 (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_mono_level (levelPrincipal N) (levelPrincipal_le N) F)
        (resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_level F) (classK N h3 hN n x)) =
      ((Fintype.card (↥rationalLevel ⧸ (levelPrincipal N).subgroupOf rationalLevel) : ℂ)⁻¹) •
        ∑ q : ↥rationalLevel ⧸ (levelPrincipal N).subgroupOf rationalLevel,
          resH2 (rationalCoefficientComponent n trivialCharacter)
            (fixedPointLevel_le_self (levelPrincipal N) F)
            (actH2 (rationalCoefficientComponent n trivialCharacter) ((Quotient.out q : ↥rationalLevel) : RationalGL3)
              (levelPrincipal_norm N _ (Quotient.out q).2) (classPrincipal N h3 n hN x)) := by
  have hc : resH2 (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_mono_level (levelPrincipal N) (levelPrincipal_le N) F)
        (resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_level F) (classK N h3 hN n x)) =
      resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_self (levelPrincipal N) F)
        (resH2 (rationalCoefficientComponent n trivialCharacter) (levelPrincipal_le N) (classK N h3 hN n x)) := by
    rw [resH2_comp, resH2_comp]
  rw [hc]
  change _ = _ • _
  have := resH2_trH2 (rationalCoefficientComponent n trivialCharacter) (levelPrincipal_le N) (levelPrincipal_norm N)
    (classPrincipal N h3 n hN x)
  have e : classK N h3 hN n x = trH2 (rationalCoefficientComponent n trivialCharacter) (levelPrincipal_le N)
      (levelPrincipal_norm N) (classPrincipal N h3 n hN x) := rfl
  rw [e, this, map_smul, map_sum]

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers in
/-- **`r_Q = T r_P` at `K†` for the classical summed series** (M3 + `classK_line_eq_T`), for every tuple of cusp forms, given the
input `SeriesRestrictionInSeedSpan` for each summand. -/
theorem formClass_line_eq_T [Fintype (PlaneFaces N)] (hn : 4 ≤ n)
    (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (hS : ∀ x b, SeriesRestrictionInSeedSpan N n hn (f x b) x b) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      BadPlaneInjectivity.IsUniquenessMap n trivialCharacter T ∧
      ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c =
            classK N h3 hN n (∑ x, ∑ b, complexify (gammaN N) n
              (TernaryPeriodPolynomials.Argument.Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b)
                (Quotient.out x) b hn)) →
          InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 ∧
          InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 ∧
          (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1 := by
  obtain ⟨T, hT, -, h⟩ := classK_line_eq_T N h3 hN n hn _ (formClass_planeLocallyInner N n h3 hN hn f hS)
  exact ⟨T, hT, h⟩

end TernaryPeriodPolynomials.Argument.FormClassK
