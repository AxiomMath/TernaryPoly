module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CuspRestriction
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cell.KConj
public import TernaryPeriodPolynomials.EisensteinSeries.Class.SeedLinear
public import TernaryPeriodPolynomials.EisensteinSeries.Class.FlagCusp

@[expose] public section


/-!
# The complex bridge: restriction of the series to the face of a cusp and the conjugated seeds

Paper: "rationally conjugate the other plane cusps to `P`".

* `complexifyAt N h n` (the `FlagCusp.complexifyAt` = `complexify (gammaNPAt N h) n`): complexification
  `H²(Γ_{h⁻¹Ph}, E_n)_ℝ → H²(Γ_{h⁻¹Ph}, E_n)_ℂ`, the identity on cocycles; `resAtC_complexify`: `resAtC ∘ complexify = complexifyAt ∘ (real restriction)`.
* `complexifyAt_cuspSeedAt`: the complexification of the class of the transported seed `cuspSeedAt` is
  the `faceSeedKerClass N h n g` (the image of the seed class of `g` under `faceKerMap`, i.e. the
  conjugation `conjP N h` and the coefficient comparison `faceT h = ρ(h⁻¹)`); likewise for the
  antiholomorphic seed.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology
open TernaryPeriodPolynomials.Argument.SeedC3S4c (realDescent realDescent_apply)
open scoped MatrixGroups ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument
  TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham

section ComplexAt

variable (N : ℕ) (h : SL(3, ℤ)) (n : ℕ)

/-- On cocycles, `complexifyAt` (S3's `FlagCusp.complexifyAt`, the generic complexification of the plane
group of the cusp `h⁻¹Ph`) is the identity. -/
theorem complexifyAt_H2π (c : cocycles₂ (Rep.of (rhoAt N h n))) :
    complexifyAt N h n (H2π (Rep.of (rhoAt N h n)) c) =
      H2π (faceRep N h n) (cxCocycles (gammaNPAt N h) n c) :=
  complexify_H2π (gammaNPAt N h) n c

/-- The real restriction `H²(Γ(N), E_n)_ℝ → H²(Γ_{h⁻¹Ph}, E_n)_ℝ` (the one of `cuspFaceForm_class`). -/
def resReal : H2 (Rep.of (gammaRho (gammaN N) n)) →ₗ[ℝ] H2 (Rep.of (rhoAt N h n)) :=
  (groupCohomology.map (inclAt N h)
    (resMor (inclAt N h) (rhoAt N h n) (gammaRho (gammaN N) n) (fun _ => rfl)) 2).hom

/-- **`resAtC ∘ complexify = complexifyAt ∘ resReal`.** -/
theorem resAtC_complexify (c : H2 (Rep.of (gammaRho (gammaN N) n))) :
    TernaryPeriodPolynomials.Argument.FormClassK.resAtC N h n (complexify (gammaN N) n c) =
      complexifyAt N h n (resReal N h n c) := by
  induction c using H2_induction_on with | _ z => ?_
  rw [complexify_H2π]
  unfold TernaryPeriodPolynomials.Argument.FormClassK.resAtC resReal
  rw [H2π_comp_map_apply, H2π_comp_map_apply, complexifyAt_H2π]
  rfl

end ComplexAt

section SeedTransport

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (n : ℕ)

/-- The identity of the face as an equivariant map from the conjugate plane group's action to
`Γ_P`'s action along the conjugation `conjP N h`. -/
def faceIdEquivMap : EquivMap isOpen_faceSet isOpen_faceSet (cuspFaceAction N h)
    (gammaNPlaneData N).action (conjP N h).toMonoidHom where
  φ := id
  smooth := contDiffOn_id
  mapsTo _ hx := hx
  equiv _ _ _ := rfl

omit [NeZero N] in
theorem faceId_hρ (g : gammaNPAt N h) :
    (planeDataComap (gammaNPlaneData N) (conjP N h).toMonoidHom).rhoR n g =
      (gammaNPlaneData N).rhoR n ((conjP N h).toMonoidHom g) := by
  rw [planeDataComap_rhoR]; rfl

omit [NeZero N] in
/-- `comapAt` is the pullback along the identity equivariant map. -/
theorem comapAt_eq_pullInv (F : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action
    ((gammaNPlaneData N).rhoR n)) :
    comapAt N n h F = pullInv (faceIdEquivMap N h) (faceId_hρ N h n) F := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  have h1 := pullBack_apply isOpen_faceSet (faceIdEquivMap N h).smooth
    (faceIdEquivMap N h).mapsTo F.1 hx
  change (F.1 : RawForm Face (Coef n) 2) x = (pullBack isOpen_faceSet (faceIdEquivMap N h).smooth
    (faceIdEquivMap N h).mapsTo 2 F.1 : RawForm Face (Coef n) 2) x
  rw [h1]
  simp only [pullRaw, faceIdEquivMap, fderiv_id, id]
  exact ContinuousAlternatingMap.ext fun v => rfl

omit [NeZero N] in
/-- **The class of the transported form is the group-cohomology pullback of the class.** -/
theorem deRhamClass_comapAt (F : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action
    ((gammaNPlaneData N).rhoR n)) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        ((planeDataComap (gammaNPlaneData N) (conjP N h).toMonoidHom).rhoR n) (comapAt N n h F) =
      (groupCohomology.map (conjP N h).toMonoidHom
        (resMor (conjP N h).toMonoidHom
          ((planeDataComap (gammaNPlaneData N) (conjP N h).toMonoidHom).rhoR n)
          ((gammaNPlaneData N).rhoR n) (faceId_hρ N h n)) 2).hom
        (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
          (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n) F) := by
  rw [comapAt_eq_pullInv]
  exact deRhamClass_natural (faceIdEquivMap N h) convex_faceSet faceSet_nonempty convex_faceSet
    faceSet_nonempty (faceId_hρ N h n) F

end SeedTransport

section SeedBridge

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (n : ℕ)

/-- **Transport of classes: conjugation `conjP N h`, then `ρ(h⁻¹)`, then complexification is S4c's
`faceH2Map` of the complexified class.** -/
theorem complexifyAt_transport (y : H2 (Rep.of ((gammaNPlaneData N).rhoR n))) :
    complexifyAt N h n ((groupCohomology.map (MonoidHom.id (gammaNPAt N h))
      (twMor (intertwines_rhoAt N n h)) 2).hom
      ((groupCohomology.map (conjP N h).toMonoidHom
        (resMor (conjP N h).toMonoidHom
          ((planeDataComap (gammaNPlaneData N) (conjP N h).toMonoidHom).rhoR n)
          ((gammaNPlaneData N).rhoR n) (faceId_hρ N h n)) 2).hom y)) =
      FaceTransport.h2Map (faceEquiv N h) (gammaNRep N n) (faceRep N h n) (faceT h n)
        (faceT_intertwines N h n) (complexifyG N n y) := by
  induction y using H2_induction_on with | _ z => ?_
  rw [H2π_comp_map_apply, H2π_comp_map_apply, complexifyAt_H2π, complexifyG_H2π]
  refine Eq.trans ?_ (FaceTransport.h2Map_π (faceEquiv N h) (gammaNRep N n) (faceRep N h n)
    (faceT h n) (faceT_intertwines N h n) _).symm
  congr 1

end SeedBridge

section SeedValue

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (n : ℕ)

/-- **The complexified class of the transported seed is S4c's conjugated seed class**
`faceSeedKerClass N h n g` (the radical-kernel class `h^*[ω_g]`). -/
theorem complexifyAt_cuspSeedAt (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    complexifyAt N h n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
        (cuspFaceAction N h) (rhoAt N h n) (cuspSeedAt N n g h)) =
      ((faceSeedKerClass N h n g :
        ↥(twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker) :
          H2 (faceRep N h n)) := by
  have e1 : ((faceSeedKerClass N h n g :
        ↥(twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker) :
          H2 (faceRep N h n)) =
      FaceTransport.h2Map (faceEquiv N h) (gammaNRep N n) (faceRep N h n) (faceT h n)
        (faceT_intertwines N h n) ((gammaNSeedKerClass N n g : ↥(twoCohomologyRestriction
          (gammaNExt N).inl (gammaNRep N n)).ker) : H2 (gammaNRep N n)) := rfl
  rw [e1, gammaNSeedKerClass_val]
  show complexifyAt N h n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
    (cuspFaceAction N h) (rhoAt N h n) (twInv (intertwines_rhoAt N n h) (comapAt N n h
      (cuspSeedInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := g))))) = _
  rw [deRhamClass_twist convex_faceSet faceSet_nonempty (intertwines_rhoAt N n h),
    deRhamClass_comapAt, deRhamClass_cuspSeed]
  exact complexifyAt_transport N h n _

/-- **The complexified class of the transported antiholomorphic seed is S4c's
`faceSeedConjKerClass N h n g`.** -/
theorem complexifyAt_cuspSeedConjAt (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    complexifyAt N h n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
        (cuspFaceAction N h) (rhoAt N h n) (cuspSeedConjAt N n g h)) =
      ((faceSeedConjKerClass N h n g :
        ↥(twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker) :
          H2 (faceRep N h n)) := by
  have e1 : ((faceSeedConjKerClass N h n g :
        ↥(twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker) :
          H2 (faceRep N h n)) =
      FaceTransport.h2Map (faceEquiv N h) (gammaNRep N n) (faceRep N h n) (faceT h n)
        (faceT_intertwines N h n) ((gammaNSeedConjKerClass N n g : ↥(twoCohomologyRestriction
          (gammaNExt N).inl (gammaNRep N n)).ker) : H2 (gammaNRep N n)) := rfl
  rw [e1, gammaNSeedConjKerClass_val]
  show complexifyAt N h n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
    (cuspFaceAction N h) (rhoAt N h n) (twInv (intertwines_rhoAt N n h) (comapAt N n h
      (cuspSeedConjInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := g))))) = _
  rw [deRhamClass_twist convex_faceSet faceSet_nonempty (intertwines_rhoAt N n h),
    deRhamClass_comapAt, deRhamClass_cuspSeedConj]
  exact complexifyAt_transport N h n _

end SeedValue

section Values

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.Statements.EisensteinClass

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)
  (h h' : SL(3, ℤ)) (b : Bool)

/-- **The restriction of the complexified class of the series at the cusp `h'` to the plane group of the
cusp `h` is the complexification of the class of the pullback to the face of `h`.** -/
theorem resAtC_eisensteinAtClass :
    TernaryPeriodPolynomials.Argument.FormClassK.resAtC N h n (complexify (gammaN N) n
      (eisensteinAtClass_gammaN N n f h' b hn)) =
      complexifyAt N h n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
        (cuspFaceAction N h) (rhoAt N h n)
        (cuspFaceForm N h (planeEisensteinAtComponents b (CuspData.ofSL h') (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h')))) := by
  rw [resAtC_complexify, cuspFaceForm_class]
  rfl

variable {N n f hn h h'}

/-- **Exact value: different orbits.** If no coset `Γ_{k⁻¹Pk}γ`, `k = h' h⁻¹`, has `k γ ∈ P(ℤ)` then the
restriction of the series at `h'` (either seed type) to the cusp `h` is zero. -/
theorem resAtC_value_none (hN : 3 ≤ N)
    (hnone : ∀ c : Ck N (h' * h⁻¹), ¬ IsCellK N (h' * h⁻¹) c) :
    TernaryPeriodPolynomials.Argument.FormClassK.resAtC N h n (complexify (gammaN N) n
      (eisensteinAtClass_gammaN N n f h' b hn)) = 0 := by
  rw [resAtC_eisensteinAtClass]
  cases b
  · rw [faceClass_none N n f hn h h' hN hnone, _root_.map_zero]
  · rw [faceClass_true_none N n f hn h h' hN hnone, _root_.map_zero]

/-- **Exact value: positive cell.** `k γ = [[A, w], [0, 1]]`: the restriction of the holomorphic series is the
conjugated holomorphic seed of `f|A`, the antiholomorphic series gives the conjugated antiholomorphic seed
of `f|A`. -/
theorem resAtC_value_pos (hN : 3 ≤ N) {c₀ : Ck N (h' * h⁻¹)} (hc : IsCellK N (h' * h⁻¹) c₀)
    (h22 : ((cellMat N (h' * h⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1) :
    TernaryPeriodPolynomials.Argument.FormClassK.resAtC N h n (complexify (gammaN N) n
      (eisensteinAtClass_gammaN N n f h' b hn)) =
      if b then
        ((faceSeedConjKerClass N h n (cuspSlash N n (leviBlock (cellMat N (h' * h⁻¹) c₀)
          (cellMat_mem_planeStab N (h' * h⁻¹) hc h22)) f) :
          ↥(twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker) :
            H2 (faceRep N h n))
      else
        ((faceSeedKerClass N h n (cuspSlash N n (leviBlock (cellMat N (h' * h⁻¹) c₀)
          (cellMat_mem_planeStab N (h' * h⁻¹) hc h22)) f) :
          ↥(twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker) :
            H2 (faceRep N h n)) := by
  rw [resAtC_eisensteinAtClass]
  cases b
  · rw [faceClass_pos N n f hn h h' hN hc h22, complexifyAt_cuspSeedAt]
    rfl
  · rw [faceClass_true_pos N n f hn h h' hN hc h22, complexifyAt_cuspSeedConjAt]
    rfl

/-- **Exact value: negative cell (Levi determinant `-1`).** `k γ = [[A', w], [0, -1]]`, `M = k γ·diag(1,-1,-1)`
with Levi block `A ∈ SL₂(ℤ)`: the holomorphic series restricts to the conjugated ANTIholomorphic seed of
`(f|A)^*` and the antiholomorphic series to the conjugated holomorphic seed of `(f|A)^*` (no sign). -/
theorem resAtC_value_neg (hN : 3 ≤ N) {c₀ : Ck N (h' * h⁻¹)} (hc : IsCellK N (h' * h⁻¹) c₀)
    (h22 : ((cellMat N (h' * h⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1) :
    TernaryPeriodPolynomials.Argument.FormClassK.resAtC N h n (complexify (gammaN N) n
      (eisensteinAtClass_gammaN N n f h' b hn)) =
      if b then
        ((faceSeedKerClass N h n (fStarGen (leviGroup N) (leviGroup_J_stable N)
          (cuspSlash N n (leviBlock (cellMat N (h' * h⁻¹) c₀ * rPrime)
            (cellMat_mul_rPrime_mem N (h' * h⁻¹) hc h22)) f)) :
          ↥(twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker) :
            H2 (faceRep N h n))
      else
        ((faceSeedConjKerClass N h n (fStarGen (leviGroup N) (leviGroup_J_stable N)
          (cuspSlash N n (leviBlock (cellMat N (h' * h⁻¹) c₀ * rPrime)
            (cellMat_mul_rPrime_mem N (h' * h⁻¹) hc h22)) f)) :
          ↥(twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker) :
            H2 (faceRep N h n)) := by
  rw [resAtC_eisensteinAtClass]
  cases b
  · rw [faceClass_neg N n f hn h h' hN hc h22, complexifyAt_cuspSeedConjAt]
    rfl
  · rw [faceClass_true_neg N n f hn h h' hN hc h22, complexifyAt_cuspSeedAt]
    rfl

end Values

section Span

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.Statements.EisensteinClass

variable (N : ℕ) [NeZero N] (n : ℕ) (h : SL(3, ℤ))

theorem faceSeedKerClass_mem_span (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    ((faceSeedKerClass N h n g :
      ↥(twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker) : H2 (faceRep N h n)) ∈
        faceSeedSpan N h n :=
  ⟨faceSeedKerClass N h n g, Submodule.subset_span (Or.inl ⟨g, rfl⟩), rfl⟩

theorem faceSeedConjKerClass_mem_span (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    ((faceSeedConjKerClass N h n g :
      ↥(twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker) : H2 (faceRep N h n)) ∈
        faceSeedSpan N h n :=
  ⟨faceSeedConjKerClass N h n g, Submodule.subset_span (Or.inr ⟨g, rfl⟩), rfl⟩

variable (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) (h' : SL(3, ℤ)) (b : Bool)

/-- **For every pair of cusps `h'` (series) and `h` (face) and either seed type, the restriction of the
complexified class of the series lies in the span of the conjugated seeds of the cusp `h`**
(`3 ≤ N`, `4 ≤ n`): it is `0`, a conjugated holomorphic seed or a conjugated antiholomorphic seed
(`resAtC_value_none/pos/neg`). -/
theorem resAtC_eisensteinAtClass_mem_faceSeedSpan (hN : 3 ≤ N) :
    TernaryPeriodPolynomials.Argument.FormClassK.resAtC N h n (complexify (gammaN N) n
      (eisensteinAtClass_gammaN N n f h' b hn)) ∈ faceSeedSpan N h n := by
  by_cases hex : ∃ c : Ck N (h' * h⁻¹), IsCellK N (h' * h⁻¹) c
  · obtain ⟨c₀, hc⟩ := hex
    rcases cell_entry_pm_one N (h' * h⁻¹) hc with h22 | h22
    · rw [resAtC_value_pos b hN hc h22]
      cases b
      · exact faceSeedKerClass_mem_span N n h _
      · exact faceSeedConjKerClass_mem_span N n h _
    · rw [resAtC_value_neg b hN hc h22]
      cases b
      · exact faceSeedConjKerClass_mem_span N n h _
      · exact faceSeedKerClass_mem_span N n h _
  · have hnone : ∀ c : Ck N (h' * h⁻¹), ¬ IsCellK N (h' * h⁻¹) c := fun c hc => hex ⟨c, hc⟩
    rw [resAtC_value_none b hN hnone]
    exact Submodule.zero_mem _

end Span

section SeriesRestriction

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)

/-- **`SeriesRestrictionInSeedSpan` holds for every series** (`3 ≤ N`, `4 ≤ n`, every plane face `x` and
seed type `b`): this is the explicit input `hS` of S7's `formClass_planeLocallyInner`. -/
theorem seriesRestrictionInSeedSpan (hN : 3 ≤ N) (x : TernaryPeriodPolynomials.Argument.SeedC3S4c.PlaneFaces N) (b : Bool) :
    TernaryPeriodPolynomials.Argument.FormClassK.SeriesRestrictionInSeedSpan N n hn f x b := fun h =>
  resAtC_eisensteinAtClass_mem_faceSeedSpan N n h f hn (Quotient.out x) b hN

end SeriesRestriction

end TernaryPeriodPolynomials.Argument.EisensteinClass
