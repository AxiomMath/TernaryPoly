module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ReflectionDescent
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.BadPlaneSupply

@[expose] public section


/-!
# The seed classes are the restricted plane summand (S4c of Lemma C.3, bad plane, level one)

For odd `n = 2k + 1` and a level-one cusp form `f` of weight `n + 3`, the library supplies `b` in the
automorphic plane span, vanishing at the good plane, whose bad-plane class has binary edge `per f`
(`CuspidalSpan.cuspFormRealized`). Its restriction to `Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)` is `(n+1)/2` times the
complexified de Rham class of the reflection-invariant seed `ω_f + \overline{ω_{f^*}}`
(`seed_class_identity`): both have the same `Λ₀⁺`-edge, the odd part `½([c_f] - [R c_f])` of the
holomorphic period class (`restriction_levelOnePeriodMap`, `edge_reflSeed`), and the edge of
`Λ₀⁺` is injective (`plusEdgeS_injective`).

Written by Claude Opus 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.ModularH2
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneEichlerShimura
open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.Argument.CuspidalSpan
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)

/-- Restriction `H²(Λ₀, V) → H²(Λ₀⁺, V)`. -/
abbrev plusResH2 (n : ℕ) :
    groupCohomology.H2 (identityPlaneCoefficientRep n) →ₗ[ℂ] groupCohomology.H2 (plusRep n) :=
  twoCohomologyRestriction Lam0Plus.subtype (identityPlaneCoefficientRep n)

theorem plusResH2_relClass (n : ℕ)
    (c : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n)) :
    plusResH2 n (relativeTwoCocycleClass identityPlaneRadicalInclusion
        (identityPlaneCoefficientRep n) c).val =
      (relativeTwoCocycleClass plusExtensionS.inl (plusRep n) (plusRestrictS n c)).val := by
  rw [relativeTwoCocycleClass_apply, relativeTwoCocycleClass_apply, twoCohomologyRestriction_apply]
  rfl

/-- The `Λ₀⁺`-edge of the restriction of a `Λ₀`-class is the `SL₂(ℤ)`-restriction of its edge. -/
theorem plusEdge_resH2 (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (x : groupCohomology.H2 (identityPlaneCoefficientRep n)) :
    ∃ y : (twoCohomologyRestriction plusExtensionS.inl (plusRep n)).ker,
      y.val = plusResH2 n x ∧
        (plusLeviCohomologyIso n).hom (plusEdgeS n y) =
          restriction (n + 1) (-1) (-1) (identityPlaneFullBinaryEdge n hn hodd x) := by
  obtain ⟨c, hc⟩ := relativeTwoCocycleClass_surjective identityPlaneRadicalInclusion
    identityPlaneRadicalInclusion_injective (identityPlaneCoefficientRep n)
    ⟨x, identityPlaneH2_restriction_zero n hn hodd x⟩
  refine ⟨relativeTwoCocycleClass plusExtensionS.inl (plusRep n) (plusRestrictS n c), ?_, ?_⟩
  · rw [← plusResH2_relClass, hc]
  · rw [plusEdge_restrict, hc]
    rfl

/-- The library's ambient edge factors through the Mathlib class. -/
def ambientToGroupH2 (n : ℕ) :
    H2 Λ₀ (ρn n) →ₗ[ℂ] groupCohomology.H2 (identityPlaneCoefficientRep n) :=
  (LinearMap.range (boundaryMap Λ₀ (ρn n))).liftQ
    ((groupCohomology.H2π (identityPlaneCoefficientRep n)).hom.comp
      (ambientCocycleToGroup Λ₀ (ρn n))) (by
      rintro _ ⟨P, rfl⟩
      exact LinearMap.mem_ker.mpr
        ((ambientCocycle_H2_zero_iff Λ₀ (ρn n) _).mpr ⟨P, rfl⟩))

theorem edgeH2_eq_full (n : ℕ) (hn : 0 < n) (hodd : Odd n) (x : H2 Λ₀ (ρn n)) :
    edgeH2 n hn hodd x = identityPlaneFullBinaryEdge n hn hodd (ambientToGroupH2 n x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change edgeH2 n hn hodd (classOf Λ₀ (ρn n) C) = _
  rw [edgeH2_classOf, identityPlaneAmbientBinaryEdge_apply]
  rfl

theorem classicalBinaryCocycle_congr {w w' : ℤ} (hw : w = w')
    (f : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range w)
    (f' : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range w')
    (hfun : (f : UpperHalfPlane → ℂ) = f') (d : ℕ) (we : w = (d : ℤ) + 2) (we' : w' = (d : ℤ) + 2)
    (τ : ℤ) : classicalBinaryCocycle f d we τ = classicalBinaryCocycle f' d we' τ := by
  subst hw
  obtain rfl : f = f' := DFunLike.coe_injective hfun
  rfl

private theorem cuspForm_cast_coe {Λ : Subgroup (GL (Fin 2) ℝ)} {w w' : ℤ} (h : w = w')
    (g : CuspForm Λ w) : ((h ▸ g : CuspForm Λ w') : UpperHalfPlane → ℂ) = g := by
  subst h
  rfl

private theorem parityOf_neg_one : (parityOf (-1)).val = 1 := by
  simp [parityOf]

/-- An element of the relative kernel of `Λ₀⁺` whose edge is the odd part `½([c_f] - [R c_f])` of the
holomorphic period class is `(n+1)/2` times the complexified de Rham class of the
reflection-invariant seed `ω_f + \overline{ω_{f^*}}` (for even `n + 1`). -/
theorem eq_seed_of_edge {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
    (hw' : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2) (hpow : ((-1 : ℂ)) ^ (n + 1) = 1)
    (y : (twoCohomologyRestriction plusExtensionS.inl (plusRep n)).ker)
    (hy : (plusLeviCohomologyIso n).hom (plusEdgeS n y) =
      (2 : ℂ)⁻¹ • (periodClass f hw' - periodClassRefl f hw')) :
    y.val = (((n : ℂ) + 1) / 2) • complexify n
      (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty plusPlaneData.action
        (plusPlaneData.rhoR n) (reflSeedInv plusPlaneData plus_hΛ f 1)) := by
  rw [complexify_reflSeed, ← Submodule.coe_smul]
  congr 1
  apply plusEdgeS_injective n
  apply (plusLeviCohomologyIso n).toLinearEquiv.injective
  change (plusLeviCohomologyIso n).hom (plusEdgeS n y) =
    (plusLeviCohomologyIso n).hom (plusEdgeS n ((((n : ℂ) + 1) / 2) •
      relativeTwoCocycleClass plusExtensionS.inl (plusRep n)
        (seedRelCocycle f + (((1 * (-1 : ℝ) ^ (n + 1) : ℝ) : ℂ)) • seedConjRelCocycle (fStar f))))
  rw [hy, map_smul, map_smul, edge_reflSeed f 1 hw', hpow, smul_smul]
  have hn1 : ((n : ℂ)) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hsc : ((n : ℂ) + 1) / 2 * ((n : ℂ) + 1)⁻¹ = 2⁻¹ := by field_simp
  rw [hsc]
  push_cast
  module

/-- **S4c, bad plane, level one: the restricted plane class is the seed class.** For odd `n = 2k+1`
and a level-one cusp form `f` of weight `n + 3`, the library's realizing element `b` of the
automorphic plane span (vanishing at the good plane, bad-plane edge `per f`) restricts on
`Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)` to `(n+1)/2` times the complexified de Rham class of the reflection-invariant
seed `ω_f + \overline{ω_{f^*}}` (`reflSeedInv … f 1`). -/
theorem seed_class_identity (k : ℕ) (f : CuspForm Lvl1 (((2 * k + 1) + 3 : ℕ) : ℤ)) :
    ∃ b ∈ automorphicPlaneSpan (2 * k + 1),
      cuspRes (2 * k + 1) trivialCharacter .plane true b = 0 ∧
      plusResH2 (2 * k + 1) (ambientToGroupH2 (2 * k + 1)
          (cuspRes (2 * k + 1) trivialCharacter .plane false b)) =
        ((((2 * k + 1 : ℕ) : ℂ) + 1) / 2) • complexify (2 * k + 1)
          (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty plusPlaneData.action
            (plusPlaneData.rhoR (2 * k + 1)) (reflSeedInv plusPlaneData plus_hΛ f 1)) := by
  have hn : 0 < 2 * k + 1 := by omega
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hW : (((2 * k + 1) + 3 : ℕ) : ℤ) = -2 * hw (k + 1) := by simp only [hw]; push_cast; ring
  have hw' : (((2 * k + 1) + 3 : ℕ) : ℤ) = (((2 * k + 1) + 1 : ℕ) : ℤ) + 2 := by push_cast; ring
  obtain ⟨fL, hfun⟩ : ∃ fL : CuspForm levelOne (-2 * hw (k + 1)),
      (fL : UpperHalfPlane → ℂ) = f := ⟨hW ▸ f, cuspForm_cast_coe hW f⟩
  obtain ⟨b, hb, hgood, hedge⟩ := cuspFormRealized (2 * k + 1) hn hodd k rfl fL
  refine ⟨b, hb, hgood, ?_⟩
  obtain ⟨y, hy, hyedge⟩ := plusEdge_resH2 (2 * k + 1) hn hodd
    (ambientToGroupH2 (2 * k + 1) (cuspRes (2 * k + 1) trivialCharacter .plane false b))
  rw [← hy]
  have he := (edgeH2_eq_full (2 * k + 1) hn hodd
    (cuspRes (2 * k + 1) trivialCharacter .plane false b)).symm
  rw [he, hedge] at hyedge
  have hpow : ((-1 : ℂ)) ^ (2 * k + 1 + 1) = 1 := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]; norm_num
  refine eq_seed_of_edge f hw' hpow y (hyedge.trans ?_)
  change restriction (2 * (k + 1)) (-1) (-1) (per (k + 1) (-1) fL) = _
  rw [restriction_levelOnePeriodMap (2 * (k + 1)) (-1) (hw (k + 1)) (weight_eq_r (k + 1))
    (even_two_mul (k + 1)) (parityOf (-1)) (parityOf_sign (-1)) fL]
  rw [modularPeriod_eq, parityOf_neg_one]
  have hc : classicalBinaryCocycle fL (2 * (k + 1)) (weight_eq_r (k + 1)) (-1) =
      classicalBinaryCocycle f (2 * k + 1 + 1) hw' (-1) :=
    classicalBinaryCocycle_congr hW.symm fL f hfun _ _ _ _
  rw [hc]
  unfold periodClass periodClassRefl
  simp only [modularCocycleParity, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    map_smul, map_add, pow_one]
  module

end TernaryPeriodPolynomials.Argument.SeedC3S4c
