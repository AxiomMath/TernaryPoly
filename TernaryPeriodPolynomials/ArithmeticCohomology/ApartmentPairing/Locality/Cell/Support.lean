module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Geometry
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.SheetGeometry
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellChains
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.Cell0Geometry
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.LocalDegree
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.TranslateContributions
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.ConeRecursion
public import TernaryPeriodPolynomials.Topology.SingularHomology.SubordinateChains

@[expose] public section


/-!
# Lemma 3.3, G3: the support of a cell chain in the symmetric space

`cellSet n D` is the union of the images in the symmetric space of the affine simplices that make up the
chain `cellAtSpace n D`.  It is compact (`isCompact_cellSet`), carries the chain
(`cellAtSpace_mem_sub`), is moved by `Γ(6)` exactly as the cell is (`cellSet_smul`, and at the level of
chains `smul_cellAtSpace`), misses the diagonal flat unless `D = T₀` (`cellSet_not_flat`) and meets it
at most in the identity form `p0` for `D = T₀` (`cellSet_flat_T0`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Finsupp GeneralEisenstein TernaryPoly TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SymmetricSpaceArithmeticProper TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SingularCoverNaturality TernaryPoly.EquivariantSingularResolution
  TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry

/-- The image in the symmetric space of an affine simplex of positive definite forms. -/
def simpSet {n : ℕ} (y : AffSimp PDMat n) : Set Space :=
  Set.range (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) => nuSp (affMap n y t))

/-- The union of the simplices of the chain of a cell. -/
def cellSet (n : ℕ) (D : Cell) : Set Space :=
  ⋃ y ∈ (coneData.phi n D).support, simpSet y

theorem isCompact_simpSet {n : ℕ} (y : AffSimp PDMat n) : IsCompact (simpSet y) :=
  isCompact_range (nuSp.continuous.comp (affMap n y).continuous)

theorem isCompact_cellSet (n : ℕ) (D : Cell) : IsCompact (cellSet n D) :=
  (Finset.finite_toSet _).isCompact_biUnion fun y _ => isCompact_simpSet y

/-- `nuSpace` is equivariant for the integral group. -/
theorem nuSpace_smul (g : IntegralGL3) (M : PDMat) :
    nuSpace (g • M) = act (realIntegral g) (nuSpace M) := by
  apply embedding_injective
  have h := nu_smul g M
  change embedding (nuSpace (g • M)) = integralAction g (embedding (nuSpace M)) at h
  rw [h]
  unfold integralAction
  have hr : TernaryPoly.SymmetricSpaceRationalAction.realRational (integralRational g) =
      realIntegral g :=
    TernaryPoly.SymmetricSpaceRationalAction.realRational_integral g
  rw [leftAction_embedding, hr]

/-- The level-three action through `levelOfSix` is the action of the integral matrix. -/
theorem levelOfSix_smul_pd (g : TernaryPoly.IntegralGL3Congruence.principalSix) (M : PDMat) :
    levelOfSix g • M = (g.1 : IntegralGL3) • M :=
  Subtype.ext (by rw [smul_level_val, levelLift_levelOfSix]; rfl)

theorem nuSp_affMap_smul (g : TernaryPoly.IntegralGL3Congruence.principalSix) {n : ℕ}
    (y : AffSimp PDMat n) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    nuSp (affMap n (fun i => levelOfSix g • y i) t) = g • nuSp (affMap n y t) := by
  have h : affMap n (fun i => levelOfSix g • y i) t = (g.1 : IntegralGL3) • affMap n y t := by
    apply Subtype.ext
    rw [smul_pd_val, affMap_val, affMap_val, actMat_sum]
    simp only [levelOfSix_smul_pd, smul_pd_val]
  change nuSpace _ = _
  rw [h, nuSpace_smul]
  rfl

theorem simpSet_smul (g : TernaryPoly.IntegralGL3Congruence.principalSix) {n : ℕ}
    (y : AffSimp PDMat n) :
    simpSet (fun i => levelOfSix g • y i) = g • simpSet y := by
  ext S
  simp only [simpSet, Set.mem_range, Set.mem_smul_set]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨t, rfl⟩, (nuSp_affMap_smul g y t).symm⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, nuSp_affMap_smul g y t⟩

theorem phi_smul_six (g : TernaryPoly.IntegralGL3Congruence.principalSix) (n : ℕ) (D : Cell) :
    coneData.phi n (g • D) = mapAff (levelOfSix g • ·) n (coneData.phi n D) :=
  coneData.phi_smul bpt_smul epsQ_smul incQ_smul n (levelOfSix g) D

theorem cellSet_smul (g : TernaryPoly.IntegralGL3Congruence.principalSix) (n : ℕ) (D : Cell) :
    g • cellSet n D = cellSet n (g • D) := by
  have hinj : Function.Injective (fun y : AffSimp PDMat n => (levelOfSix g • ·) ∘ y) := by
    intro y y' h
    funext i
    exact MulAction.injective (levelOfSix g) (congrFun h i)
  unfold cellSet
  rw [phi_smul_six, mapAff, Finsupp.lmapDomain_apply, Finsupp.mapDomain_support_of_injective hinj,
    Finset.set_biUnion_finset_image, Set.smul_set_iUnion₂]
  refine Set.iUnion₂_congr fun y _ => ?_
  exact (simpSet_smul g y).symm

/-- A cell chain is supported in the set `cellSet`. -/
theorem cellAtSpace_mem_sub (n : ℕ) (D : Cell) :
    cellAtSpace n D ∈ SphereOddDegree.subChainSubmodule ℚ SpaceTop (cellSet n D) n := by
  unfold cellAtSpace realizeS
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun y hy => Submodule.smul_mem _ _ ?_
  refine SphereOddDegree.chainGenerator_mem_subChainSubmodule ?_
  rintro _ ⟨t, rfl⟩
  refine Set.mem_iUnion₂.mpr ⟨y, hy, t, ?_⟩
  simp [affSingS, SphereOddDegree.mvSimplexMap, SphereOddDegree.AffineBarycentricSubdivision.singularSimplexAsContinuousMap]

theorem mem_flat_iff_unip (S : Space) : S ∈ flat ↔ unip S = 0 := by
  show piR3 S = 0 ↔ _
  change (EuclideanSpace.equiv (Fin 3) ℝ).symm (unip S) = 0 ↔ _
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.map_eq_zero_iff

theorem cellSet_not_flat (n : ℕ) (D : Cell) (hD : D ≠ T0) : ∀ S ∈ cellSet n D, S ∉ flat := by
  intro S hS hf
  obtain ⟨y, hy, t, rfl⟩ := by simpa only [cellSet, simpSet, Set.mem_iUnion, Set.mem_range] using hS
  exact unip_ne_of_reach D hD (affMap_mem_reach D y (cellAt_support n D y hy) t)
    ((mem_flat_iff_unip _).mp hf)

theorem nuSpace_eq_p0 {M : PDMat} (hM : M.1 = 1) : nuSpace M = p0 := by
  apply Subtype.ext
  rw [p0_val]
  simp [nuSpace, SymmetricSpacePositive.normalize, hM]

theorem cellSet_flat_T0 (n : ℕ) : ∀ S ∈ cellSet n T0, S ∈ flat → S = p0 := by
  intro S hS hf
  obtain ⟨y, hy, t, rfl⟩ := by simpa only [cellSet, simpSet, Set.mem_iUnion, Set.mem_range] using hS
  have hM := affMap_mem_reach T0 y (cellAt_support n T0 y hy) t
  have hd := isDiagMat_of_unip_nuSpace _ ((mem_flat_iff_unip _).mp hf)
  exact nuSpace_eq_p0 (flat_reach T0 hM hd).2

/-- Translation by an element of `Γ(6)` as a map of the symmetric space. -/
def smulHom (g : TernaryPoly.IntegralGL3Congruence.principalSix) : SpaceTop ⟶ SpaceTop :=
  TopCat.ofHom ⟨fun S : Space => g • S, continuous_act _⟩

theorem map_sing_affSingS (g : TernaryPoly.IntegralGL3Congruence.principalSix) {n : ℕ}
    (y : AffSimp PDMat n) :
    ((underlyingMap (smulHom g)).f n).hom (sing SpaceTop (affSingS y)) =
      sing SpaceTop (affSingS (fun i => levelOfSix g • y i)) := by
  have h := congrArg (fun m => m.hom (1 : ℚ)) (generator_map (smulHom g) n (affSingS y))
  refine h.trans (congrArg (sing SpaceTop) ?_)
  apply (SpaceTop.toSSetObjEquiv _).injective
  refine ContinuousMap.ext fun t => ?_
  simp only [affSingS, Equiv.apply_symm_apply]
  exact (nuSp_affMap_smul g y t).symm

/-- **Equivariance of the cell chains of the symmetric space**: pushing the chain of a cell forward
along `S ↦ g • S` gives the chain of the translated cell. -/
theorem smul_cellAtSpace (g : TernaryPoly.IntegralGL3Congruence.principalSix) (n : ℕ) (D : Cell) :
    ((underlyingMap (smulHom g)).f n).hom (cellAtSpace n D) = cellAtSpace n (g • D) := by
  unfold cellAtSpace
  rw [phi_smul_six]
  have h : ((underlyingMap (smulHom g)).f n).hom ∘ₗ realizeS n =
      realizeS n ∘ₗ mapAff (levelOfSix g • ·) n := by
    apply Finsupp.lhom_ext
    intro y a
    simp only [LinearMap.comp_apply, realizeS, linearCombination_single, mapAff_single, map_smul,
      map_sing_affSingS]
    rfl
  exact LinearMap.congr_fun h _

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
