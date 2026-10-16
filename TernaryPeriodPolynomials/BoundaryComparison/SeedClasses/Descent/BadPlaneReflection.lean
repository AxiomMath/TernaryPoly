module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ClassIdentity
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ESLevelOne
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.CuspidalFamily

@[expose] public section


/-!
# The bad plane of the level-three group with its full Levi `GL₂(ℤ)`: finite reflections

Paper: Lemma C.3 (`ar:lem:seed`):

("The finite reflection projection supplies the corresponding full-level statement"),
("the holomorphic and antiholomorphic seeds span `𝒞_P(E)` after including all plane cusps and finite
reflections").

The library's arithmetic stabilizer `Λ₀` of the identity plane is `ℤ² ⋊ GL₂(ℤ)` (`Lam0`,
`identityPlaneExtension`), with coefficients `E_n = identityPlaneCoefficientRep n` (trivial
character). This file defines its literal mixed cuspidal group and compares it with the seeds.

* `borelQ`, `cuspGL F`: the stabilizer in `GL₂(ℤ)` of the rational cusp of a frame `F ∈ GL₂(ℚ)`
  (`GL₂(ℤ)`-version of `leviCuspStab`, reflections included).
* `badPlaneCuspidal n`: the classes of `H¹(GL₂(ℤ), H¹(ℤ², E_n))` (action of the Levi on the radical
  cohomology by conjugation, `splitRadicalH1Representation identityPlaneSplitting`) restricting to zero
  at `cuspGL F` for every frame `F`. This is the literal `𝒞_P(E)`.
* `cuspGL_iff_top`: finite-index descent `SL₂(ℤ) ⊆ GL₂(ℤ)` (`CuspidalFamily`) reduces the condition to
  the cuspidal condition of `SL₂(ℤ)`, which is the parabolic cohomology (`MixedCuspidal`).
* `cuspGL_iff_oddPeriodSpan` (`n` odd): a class of `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` is cuspidal iff its
  restriction to `SL₂(ℤ)` lies in the span of the odd period classes `[c_f] - [R c_f]`. The proof
  uses the library's level-one Eichler--Shimura (`es_levelOne_modular`) for the inclusion, and for
  the reverse inclusion the cuspidality of the period classes (`holCocycle_mem_parabolicCocycles`)
  and the fact that restrictions from `GL₂(ℤ)` are `-1`-eigenvectors of the reflection
  (`reflectionH1_restriction`).
* `badPlane_cuspidal_iff_reflSeedSpan`: for `x ∈ H²(Λ₀, E_n)` the edge of `x` lies in
  `badPlaneCuspidal n` iff the restriction of `x` to `Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)` lies in the span of the
  complexified de Rham classes of the reflection-invariant seeds `ω_f + \overline{ω_{f^*}}`
  (`reflSeedSpan`, `edge_reflSeed`).
* `map_plusResH2_badPlaneCuspidalInH2`: the restriction map `H²(Λ₀, E_n) → H²(Λ₀⁺, E_n)` is injective
  (`plusResH2_injective_of_odd`) and carries the classes with edge in `𝒞_P(E)` onto exactly
  `reflSeedSpan` (each reflection-invariant seed lifts to `H²(Λ₀, E_n)`, `reflSeedKerClass_mem_range`,
  by the library's cuspidal plane classes `seed_class_identity`).

The degree-two level transfer `H²(S) ≃ H²(N)^{S/N}` (`Statements.LevelTransfer`) is not needed here: the
binary edge of `Λ₀` is a bijection onto `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` in odd degree
(`identityPlaneFullBinaryEdge_injective`, `edgeH2_bijective`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups
open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension

/-- The upper triangular subgroup of `GL₂(ℚ)`. -/
def borelQ : Subgroup (GL (Fin 2) ℚ) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]; ring
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]
    simp [ha]

/-- **The stabilizer in `GL₂(ℤ)` of the rational cusp of a frame `F ∈ GL₂(ℚ)`**: the elements `γ`
with `F⁻¹ γ F` upper triangular. -/
def cuspGL (F : GL (Fin 2) ℚ) : Subgroup (GL (Fin 2) ℤ) :=
  borelQ.comap ((MulAut.conj F⁻¹).toMonoidHom.comp (GeneralLinearGroup.map (Int.castRingHom ℚ)))

theorem mem_cuspGL_iff (F : GL (Fin 2) ℚ) (γ : GL (Fin 2) ℤ) :
    γ ∈ cuspGL F ↔
      ((F⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) γ * F : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by
  change ((F⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) γ * F⁻¹⁻¹ : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 ↔ _
  rw [inv_inv]

/-- The inclusion `⊤ = SL₂(ℤ) → GL₂(ℤ)`. -/
def topToGL : (⊤ : Subgroup SL(2, ℤ)) →* GL (Fin 2) ℤ :=
  SpecialLinearGroup.toGL.comp (⊤ : Subgroup SL(2, ℤ)).subtype

theorem cuspGL_comap_top (F : GL (Fin 2) ℚ) :
    (cuspGL F).comap topToGL = leviCuspStab (⊤ : Subgroup SL(2, ℤ)) F := by
  ext γ
  rw [Subgroup.mem_comap, mem_cuspGL_iff, mem_leviCuspStab_iff]
  have : GeneralLinearGroup.map (Int.castRingHom ℚ) (topToGL γ) =
      SpecialLinearGroup.mapGL ℚ γ.1 := by
    ext i j
    simp [topToGL, SpecialLinearGroup.mapGL_coe_matrix]
  rw [this]


theorem SL2Z_le_range_topToGL : SL2Z ≤ topToGL.range := by
  intro g hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    have h : GeneralLinearGroup.det g = 1 := hg
    have := congrArg Units.val h
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  refine ⟨⟨⟨(g : Matrix (Fin 2) (Fin 2) ℤ), hdet⟩, Subgroup.mem_top _⟩, ?_⟩
  ext i j
  rfl

instance : (topToGL).range.FiniteIndex :=
  Subgroup.finiteIndex_of_le SL2Z_le_range_topToGL

theorem map_top_eq_pullback (n : ℕ) (z : groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))) :
    (groupCohomology.map topToGL (𝟙 (Rep.res topToGL (arithmeticBinaryRep (n + 1) (-1)))) 1).hom z =
      topPullH1 n (restriction (n + 1) (-1) (-1) z) := by
  obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (arithmeticBinaryRep (n + 1) (-1)) z
  rw [groupCohomology.H1π_comp_map_apply, restriction_apply, topPullH1_π]
  congr 1

/-- **Cuspidality for the full Levi `GL₂(ℤ)` through its subgroup `SL₂(ℤ)`.** -/
theorem cuspGL_iff_top (n : ℕ) (z : groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))) :
    z ∈ cuspidalFamily cuspGL (arithmeticBinaryRep (n + 1) (-1)) ↔
      topPullH1 n (restriction (n + 1) (-1) (-1) z) ∈
        cuspidalSubspace (⊤ : Subgroup SL(2, ℤ)) (binRep ⊤ n) := by
  rw [mem_cuspidalFamily_iff_map cuspGL topToGL, map_top_eq_pullback]
  have hfam : (fun F => (cuspGL F).comap topToGL) = leviCuspStab (⊤ : Subgroup SL(2, ℤ)) :=
    funext cuspGL_comap_top
  rw [hfam]
  exact Iff.rfl


open TernaryPeriodPolynomials.Argument.SeedC3 in
/-- The inverse of `topPullH1`. -/
def topPushH1 (n : ℕ) : groupCohomology.H1 (binRep ⊤ n) →ₗ[ℂ]
    groupCohomology.H1 (modularBinaryRep (n + 1) (-1)) :=
  oneCocyclePullbackH1 (binRep ⊤ n) (modularBinaryRep (n + 1) (-1)) topInv LinearMap.id
    (fun _ => rfl)

theorem topPushH1_π (n : ℕ) (c : groupCohomology.cocycles₁ (binRep ⊤ n)) :
    topPushH1 n (groupCohomology.H1π (binRep ⊤ n) c) =
      groupCohomology.H1π (modularBinaryRep (n + 1) (-1)) (topPush n c) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ c

theorem topPushH1_topPullH1 (n : ℕ) (w : groupCohomology.H1 (modularBinaryRep (n + 1) (-1))) :
    topPushH1 n (topPullH1 n w) = w := by
  obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (modularBinaryRep (n + 1) (-1)) w
  rw [topPullH1_π, topPushH1_π]
  congr 1

theorem reflectionH1_π (d : ℕ) (τ : ℤ) (c : groupCohomology.cocycles₁ (modularBinaryRep d τ)) :
    reflectionH1 d τ (groupCohomology.H1π (modularBinaryRep d τ) c) =
      groupCohomology.H1π (modularBinaryRep d τ) (modularCocycleReflection d τ c) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ c

theorem reflectionH1_involutive (d : ℕ) (τ : ℤ) (w : groupCohomology.H1 (modularBinaryRep d τ)) :
    reflectionH1 d τ (reflectionH1 d τ w) = w := by
  obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (modularBinaryRep d τ) w
  rw [reflectionH1_π, reflectionH1_π, modularCocycleReflection_involutive]


open TernaryPeriodPolynomials.Argument.SeedC3 in
/-- The odd period classes `[c_f] - [R c_f]` of level-one cusp forms of weight `n + 3`. -/
def oddPeriodSpan (n : ℕ) (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2) :
    Submodule ℂ (groupCohomology.H1 (modularBinaryRep (n + 1) (-1))) :=
  Submodule.span ℂ (Set.range (fun f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ) =>
    periodClass f hw - periodClassRefl f hw))

open TernaryPeriodPolynomials.Argument.SeedC3 in
/-- **Cuspidal classes of the full Levi `GL₂(ℤ)`, in binary coordinates** (`n` odd): a class of
`H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` restricts to zero at the stabilizer of every rational cusp iff its
restriction to `SL₂(ℤ)` is a combination of the odd period classes `[c_f] - [R c_f]` of
level-one cusp forms of weight `n + 3`. -/
theorem cuspGL_iff_oddPeriodSpan (n : ℕ) (hev : Even (n + 1))
    (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2)
    (z : groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))) :
    z ∈ cuspidalFamily cuspGL (arithmeticBinaryRep (n + 1) (-1)) ↔
      restriction (n + 1) (-1) (-1) z ∈ oddPeriodSpan n hw := by
  rw [cuspGL_iff_top]
  set w := restriction (n + 1) (-1) (-1) z with hwdef
  constructor
  · intro h
    have hpar := (mem_cuspidalSubspace_binRep_iff (Λ := (⊤ : Subgroup SL(2, ℤ))) (n := n) _).mp h
    obtain ⟨c, hc, hcw⟩ := Submodule.mem_map.mp hpar
    have hweq : w = groupCohomology.H1π (modularBinaryRep (n + 1) (-1)) (topPush n c) := by
      rw [← topPushH1_π, hcw, topPushH1_topPullH1]
    have hz : ∃ u : modularBinaryRep (n + 1) (-1), topPush n c ModularGroup.T =
        (modularBinaryRep (n + 1) (-1)).ρ ModularGroup.T u - u := by
      obtain ⟨u, hu⟩ := hc ⟨ModularGroup.T, Subgroup.mem_top _⟩ ⟨1, 1, Or.inl (by simp)⟩
      exact ⟨u, hu⟩
    have hmem := es_levelOne_modular (n + 1) hev (Nat.succ_pos n) ((n + 3 : ℕ) : ℤ) hw
      (topPush n c) hz
    rw [← hweq] at hmem
    -- w = (1/2)(w - R w)
    have hR : reflectionH1 (n + 1) (-1) w = -w := by
      have := reflectionH1_restriction (n + 1) (-1) (-1) z
      rw [← hwdef] at this
      rw [this]
      simp
    have hw2 : w = (2 : ℂ)⁻¹ • (w - reflectionH1 (n + 1) (-1) w) := by
      rw [hR, sub_neg_eq_add, ← two_smul ℂ w, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    let Θ : groupCohomology.H1 (modularBinaryRep (n + 1) (-1)) →ₗ[ℂ]
        groupCohomology.H1 (modularBinaryRep (n + 1) (-1)) :=
      (2 : ℂ)⁻¹ • (LinearMap.id - reflectionH1 (n + 1) (-1))
    have hΘ : Θ w = w := by
      change (2 : ℂ)⁻¹ • (w - reflectionH1 (n + 1) (-1) w) = w
      exact hw2.symm
    rw [← hΘ]
    have key := Submodule.mem_map_of_mem (f := Θ) hmem
    rw [Submodule.map_span] at key
    refine Submodule.span_le.mpr ?_ key
    rintro _ ⟨_, (⟨f, rfl⟩ | ⟨f, rfl⟩), rfl⟩
    · have e1 : Θ (periodClass f hw) = (2 : ℂ)⁻¹ • (periodClass f hw - periodClassRefl f hw) := by
        change (2 : ℂ)⁻¹ • (periodClass f hw - reflectionH1 (n + 1) (-1) (periodClass f hw)) = _
        rw [periodClass, reflectionH1_π]
        rfl
      show Θ (periodClass f hw) ∈ oddPeriodSpan n hw
      rw [e1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)
    · have e2 : Θ (periodClassRefl f hw) =
          -((2 : ℂ)⁻¹ • (periodClass f hw - periodClassRefl f hw)) := by
        change (2 : ℂ)⁻¹ • (periodClassRefl f hw -
          reflectionH1 (n + 1) (-1) (periodClassRefl f hw)) = _
        rw [periodClassRefl, reflectionH1_π, modularCocycleReflection_involutive]
        rw [← neg_sub, smul_neg]
        rfl
      show Θ (periodClassRefl f hw) ∈ oddPeriodSpan n hw
      rw [e2]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩))
  · intro h
    apply (mem_cuspidalSubspace_binRep_iff (Λ := (⊤ : Subgroup SL(2, ℤ))) (n := n) _).mpr
    have hle : oddPeriodSpan n hw ≤ Submodule.comap (topPullH1 n) (parabolicH1 ⊤ n) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨f, rfl⟩
      show topPullH1 n (periodClass f hw - periodClassRefl f hw) ∈ parabolicH1 ⊤ n
      rw [map_sub]
      have h1 : topPullH1 n (periodClass f hw) =
          groupCohomology.H1π (binRep ⊤ n) (holCocycle (liftTop n f)) := by
        rw [periodClass, topPullH1_π, topPull_classical f hev hw]
      have h2 : topPullH1 n (periodClassRefl f hw) =
          -groupCohomology.H1π (binRep ⊤ n) (antiholCocycle (liftTop n (fStar f))) := by
        rw [periodClassRefl, topPullH1_π, topPull_reflection f hev hw, map_neg]
      rw [h1, h2, sub_neg_eq_add]
      exact Submodule.add_mem _
        ⟨_, holCocycle_mem_parabolicCocycles _, rfl⟩
        ⟨_, antiholCocycle_mem_parabolicCocycles _, rfl⟩
    exact hle h


section BadPlane

open TernaryPeriodPolynomials.Argument.SeedC3

/-- **The mixed cuspidal group `𝒞_P(E)` of the identity (bad) plane of the level-three group**, with the full arithmetic Levi `GL₂(ℤ)` (reflections included): the classes of
`H¹(GL₂(ℤ), H¹(N_P, E_n))` that restrict to zero at the stabilizer in `GL₂(ℤ)` of every rational
cusp. -/
def badPlaneCuspidal (n : ℕ) : Submodule ℂ
    (groupCohomology.H1 (splitRadicalH1Representation identityPlaneSplitting
      (identityPlaneCoefficientRep n))) :=
  cuspidalFamily cuspGL (splitRadicalH1Representation identityPlaneSplitting
    (identityPlaneCoefficientRep n))

theorem mem_badPlaneCuspidal_iff (n : ℕ) (x : groupCohomology.H1
    (splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRep n))) :
    x ∈ badPlaneCuspidal n ↔
      ModuleCat.Hom.hom (identityPlaneLeviCohomologyIso n).hom x ∈
        cuspidalFamily cuspGL (arithmeticBinaryRep (n + 1) (-1)) :=
  mem_cuspidalFamily_iso_iff cuspGL (identityPlaneRadicalCoordinateIso n) x


/-- The edge of the reflection-invariant seed `ω_f + \overline{ω_{f^*}}` as a kernel class. -/
def reflSeedKerClass (n : ℕ) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    ↥(twoCohomologyRestriction plusExtensionS.inl (plusRep n)).ker :=
  relativeTwoCocycleClass plusExtensionS.inl (plusRep n)
    (seedRelCocycle f + (((1 * (-1 : ℝ) ^ (n + 1) : ℝ) : ℂ)) • seedConjRelCocycle (fStar f))

/-- The span of the complexified de Rham classes of the reflection-invariant seeds
`ω_f + \overline{ω_{f^*}}` in `H²(Λ₀⁺, E_n)` (the finite reflection projection of the seeds,
`n` odd, untwisted coefficients). -/
def reflSeedSpan (n : ℕ) : Submodule ℂ (groupCohomology.H2 (plusRep n)) :=
  Submodule.map (LinearMap.ker (twoCohomologyRestriction plusExtensionS.inl (plusRep n))).subtype
    (Submodule.span ℂ (Set.range (reflSeedKerClass n)))

/-- The binary-coordinate edge of `Λ₀⁺`, as a linear map on the kernel. -/
def plusBinaryEdge (n : ℕ) : ↥(twoCohomologyRestriction plusExtensionS.inl (plusRep n)).ker →ₗ[ℂ]
    groupCohomology.H1 (modularBinaryRep (n + 1) (-1)) :=
  (ModuleCat.Hom.hom (plusLeviCohomologyIso n).hom).comp (plusEdgeS n)

theorem plusBinaryEdge_injective (n : ℕ) : Function.Injective (plusBinaryEdge n) := by
  intro a b h
  apply plusEdgeS_injective n
  have h' := congrArg (ModuleCat.Hom.hom (plusLeviCohomologyIso n).inv) h
  have e : ∀ z, (ModuleCat.Hom.hom (plusLeviCohomologyIso n).inv)
      ((ModuleCat.Hom.hom (plusLeviCohomologyIso n).hom) z) = z := fun z =>
    congrArg (fun φ => ModuleCat.Hom.hom φ z) (plusLeviCohomologyIso n).hom_inv_id
  simpa [plusBinaryEdge, e] using h'

theorem plusBinaryEdge_reflSeed (n : ℕ) (hev : Even (n + 1))
    (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    plusBinaryEdge n (reflSeedKerClass n f) =
      (((n : ℂ) + 1)⁻¹) • (periodClass f hw - periodClassRefl f hw) := by
  have h := edge_reflSeed f 1 hw
  change (ModuleCat.Hom.hom (plusLeviCohomologyIso n).hom) (plusEdgeS n
    (relativeTwoCocycleClass plusExtensionS.inl (plusRep n)
      (seedRelCocycle f + (((1 * (-1 : ℝ) ^ (n + 1) : ℝ) : ℂ)) • seedConjRelCocycle (fStar f)))) = _
  rw [h, hev.neg_one_pow]
  simp

theorem oddPeriodSpan_eq_map (n : ℕ) (hev : Even (n + 1))
    (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2) :
    oddPeriodSpan n hw = Submodule.map (plusBinaryEdge n) (Submodule.span ℂ (Set.range (reflSeedKerClass n))) := by
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [Submodule.map_span]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    have hu : periodClass f hw - periodClassRefl f hw =
        ((n : ℂ) + 1) • plusBinaryEdge n (reflSeedKerClass n f) := by
      rw [plusBinaryEdge_reflSeed n hev hw f, smul_smul, mul_inv_cancel₀ hn, one_smul]
    show periodClass f hw - periodClassRefl f hw ∈ _
    rw [hu]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨reflSeedKerClass n f, ⟨f, rfl⟩, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
    rw [plusBinaryEdge_reflSeed n hev hw f]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)


theorem mem_map_iff_of_injective {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N]
    [Module ℂ N] (g : M →ₗ[ℂ] N) (hg : Function.Injective g) (S : Submodule ℂ M) (y : M) :
    g y ∈ Submodule.map g S ↔ y ∈ S := by
  constructor
  · rintro ⟨y', hy', h⟩
    rw [← hg h]; exact hy'
  · intro h; exact ⟨y, h, rfl⟩

/-- **Lemma C.3, last sentence, at the identity (bad) plane of the level-three group with its full
Levi `GL₂(ℤ)` (finite reflections included), `n` odd.** A class `x` of `H²(Λ₀, E_n)` has Hochschild--Serre
edge in the literal mixed cuspidal group `𝒞_P(E)` of `H¹(GL₂(ℤ), H¹(ℤ², E_n))` if and only if its
restriction to `Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)` lies in the span of the complexified de Rham classes of the
reflection-invariant seeds `ω_f + \overline{ω_{f^*}}`, `f ∈ S_{n+3}(SL₂(ℤ))`. -/
theorem badPlane_cuspidal_iff_reflSeedSpan (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (x : groupCohomology.H2 (identityPlaneCoefficientRep n)) :
    splitCohomologyEdge identityPlaneSplitting (identityPlaneCoefficientRep n)
        (identityPlaneH2ToRestrictionKernel n hn hodd x) ∈ badPlaneCuspidal n ↔
      plusResH2 n x ∈ reflSeedSpan n := by
  have hev : Even (n + 1) := hodd.add_one
  have hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2 := by push_cast; ring
  obtain ⟨y, hyval, hyedge⟩ := plusEdge_resH2 n hn hodd x
  rw [mem_badPlaneCuspidal_iff]
  change identityPlaneFullBinaryEdge n hn hodd x ∈ _ ↔ _
  rw [cuspGL_iff_oddPeriodSpan n hev hw, ← hyedge, ← hyval]
  change plusBinaryEdge n y ∈ oddPeriodSpan n hw ↔ _
  rw [oddPeriodSpan_eq_map n hev hw, mem_map_iff_of_injective _ (plusBinaryEdge_injective n)]
  unfold reflSeedSpan
  exact (mem_map_iff_of_injective _ (LinearMap.ker (twoCohomologyRestriction plusExtensionS.inl
    (plusRep n))).injective_subtype _ y).symm


open TernaryPeriodPolynomials.Spectral.CuspReduction in
/-- Every reflection-invariant seed class is the restriction of a class of `H²(Λ₀, E_n)`. -/
theorem reflSeedKerClass_mem_range (k : ℕ) (f : CuspForm Lvl1 (((2 * k + 1) + 3 : ℕ) : ℤ)) :
    ∃ x : groupCohomology.H2 (identityPlaneCoefficientRep (2 * k + 1)),
      plusResH2 (2 * k + 1) x = (reflSeedKerClass (2 * k + 1) f).val := by
  obtain ⟨b, hb, hb0, hres⟩ := seed_class_identity k f
  have hc : (((2 * k + 1 : ℕ) : ℂ) + 1) / 2 ≠ 0 := by
    have : (((2 * k + 1 : ℕ) : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k + 1)
    exact div_ne_zero this two_ne_zero
  refine ⟨((((2 * k + 1 : ℕ) : ℂ) + 1) / 2)⁻¹ •
    ambientToGroupH2 (2 * k + 1) (cuspRes (2 * k + 1) GeneralEisenstein.trivialCharacter GeneralEisenstein.Side.plane false b), ?_⟩
  rw [map_smul, hres, smul_smul, inv_mul_cancel₀ hc, one_smul]
  exact complexify_reflSeed f 1

theorem plusResH2_injective_of_odd (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    Function.Injective (plusResH2 n) := by
  intro a b hab
  obtain ⟨ya, hya, hyae⟩ := plusEdge_resH2 n hn hodd a
  obtain ⟨yb, hyb, hybe⟩ := plusEdge_resH2 n hn hodd b
  have hy : ya = yb := Subtype.ext (hya.trans (hab.trans hyb.symm))
  have h1 : restriction (n + 1) (-1) (-1) (identityPlaneFullBinaryEdge n hn hodd a) =
      restriction (n + 1) (-1) (-1) (identityPlaneFullBinaryEdge n hn hodd b) := by
    rw [← hyae, ← hybe, hy]
  exact identityPlaneFullBinaryEdge_injective n hn hodd (restriction_injective (n + 1) (-1) (-1) h1)

/-- The classes of `H²(Λ₀, E_n)` whose Hochschild--Serre edge lies in the literal mixed cuspidal
group of the bad plane. -/
def badPlaneCuspidalInH2 (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    Submodule ℂ (groupCohomology.H2 (identityPlaneCoefficientRep n)) :=
  Submodule.comap ((splitCohomologyEdge identityPlaneSplitting
    (identityPlaneCoefficientRep n)).comp (identityPlaneH2ToRestrictionKernel n hn hodd))
    (badPlaneCuspidal n)

/-- **Lemma C.3, last sentence, at the bad plane with finite reflections (`n = 2k + 1`).** The
restriction `H²(Λ₀, E_n) → H²(Λ₀⁺, E_n)` is injective, and it maps the classes with edge in the mixed
cuspidal group `𝒞_P(E)` of `H¹(GL₂(ℤ), H¹(ℤ², E_n))` onto exactly the span of the complexified de Rham
classes of the reflection-invariant seeds `ω_f + \overline{ω_{f^*}}`. -/
theorem map_plusResH2_badPlaneCuspidalInH2 (k : ℕ) :
    Submodule.map (plusResH2 (2 * k + 1))
        (badPlaneCuspidalInH2 (2 * k + 1) (by omega) ⟨k, rfl⟩) = reflSeedSpan (2 * k + 1) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (badPlane_cuspidal_iff_reflSeedSpan (2 * k + 1) (by omega) ⟨k, rfl⟩ x).mp hx
  · intro s hs
    obtain ⟨y, hy, rfl⟩ := hs
    -- every generator lifts to `H²(Λ₀)`; the lift has edge in `𝒞_P(E)` by the theorem above
    have key : y ∈ Submodule.span ℂ (Set.range (reflSeedKerClass (2 * k + 1))) := hy
    have hlift : ∀ z ∈ Submodule.span ℂ (Set.range (reflSeedKerClass (2 * k + 1))),
        ∃ x : groupCohomology.H2 (identityPlaneCoefficientRep (2 * k + 1)),
          plusResH2 (2 * k + 1) x = z.val := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨f, rfl⟩ := hz
        exact reflSeedKerClass_mem_range k f
      | zero => exact ⟨0, by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨xa, hxa⟩ := ha
        obtain ⟨xb, hxb⟩ := hb
        exact ⟨xa + xb, by rw [map_add, hxa, hxb]; rfl⟩
      | smul c a _ ha =>
        obtain ⟨xa, hxa⟩ := ha
        exact ⟨c • xa, by rw [map_smul, hxa]; rfl⟩
    obtain ⟨x, hx⟩ := hlift y key
    refine ⟨x, ?_, hx⟩
    apply (badPlane_cuspidal_iff_reflSeedSpan (2 * k + 1) (by omega) ⟨k, rfl⟩ x).mpr
    rw [hx]
    exact ⟨y, key, rfl⟩

end BadPlane

end TernaryPeriodPolynomials.Argument.SeedC3S4c
