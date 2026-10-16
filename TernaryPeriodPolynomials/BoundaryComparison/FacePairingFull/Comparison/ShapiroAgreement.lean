module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.StabilizerRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Stabilizers
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.PairHomotopyHom
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ProjectiveUniqueness

@[expose] public section


/-!
# Agreement of the Shapiro coordinates with the library's `fullShapiroIso`

Let `Γ` act on a free vertex set `V` and on `Z`, `R = prodResolution Γ V Z`, `a = o.out` the representative of
an orbit `o` with stabilizer `S`.  The `S`-chain map `thetaTilde : bar(S) ⟶ Res_S R` underlying `fixThetaBar`
has an adjoint Γ-chain map `psi1 : Ind_S^Γ bar(S) = orbitResolution Γ a ⟶ R` (`Rep.indResAdjunction`).
Frobenius reciprocity (`orbitShapiroIso`) turns pullback along `psi1` into the Shapiro coordinate
`stabCoord` (`stabCoord_eq_psi1`), while the library's `o`-th coordinate `subCoord` is pullback along
`incl_o ≫ κ` for a comparison `κ : stabilizerResolution Γ Z ⟶ R`.  Both chain maps are over the augmentation
`1 ↦ [a]` (`psi_aug`, using `orbitResolution_augmentation_mk`), so they are homotopic (`uniqHomotopy`) and
`stabCoord` and `subCoord ∘ κ^*` induce the same map on cohomology (`stabCoord_homology_eq_subCoord`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits Finsupp
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison (uniqHomotopy)

section Step1

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] (S : Subgroup Γ)

theorem prodComplex_d_single_gen (G : Type) [Group G] [MulAction G V] [MulAction G Z] (k : ℕ)
    (y : (Fin (k + 2) → V) × Z) :
    ((prodComplex G V Z).d (k + 1) k).hom (MonoidAlgebra.single y 1) =
      ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • MonoidAlgebra.single (face V Z i y) 1 := by
  have h := prodComplex_d_comp_eq G V Z k (𝟙 ((prodComplex G V Z).X k))
  rw [Category.comp_id] at h
  change ((prodComplex G V Z).d (k + 1) k).hom (MonoidAlgebra.single y 1) = _
  rw [h]
  erw [Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [Rep.zsmul_hom]
  exact congrArg (fun w => ((-1 : ℤ) ^ (i : ℕ)) • w) (delta_single G V Z k i y)

theorem prodComplex_res_rho (k : ℕ) (g : S) :
    ((prodComplex S V Z).X k).ρ g = ((prodComplex Γ V Z).X k).ρ g.val := rfl

theorem prodComplex_res_d (k : ℕ) :
    ((prodComplex S V Z).d (k + 1) k).hom.toLinearMap =
      ((prodComplex Γ V Z).d (k + 1) k).hom.toLinearMap := by
  apply MonoidAlgebra.lhom_ext'
  intro y
  apply LinearMap.ext_ring
  have h1 := prodComplex_d_single_gen S k y
  have h2 := prodComplex_d_single_gen Γ k y
  exact h1.trans h2.symm

end Step1

section Step2

open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.EquivariantSingularSmall TernaryPoly.SingularComponentAugmentation TernaryPoly.EquivariantSingularPairHomotopy

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] (v₀ : V) (a : Z)

/-- The `S`-equivariant map from the bar resolution of the stabilizer `S` of `a` to the restriction to `S`
of the permutation resolution. -/
def thetaTilde (n : ℕ) :
    (Rep.barComplex ℚ (MulAction.stabilizer Γ a)).X n ⟶
      Rep.res (MulAction.stabilizer Γ a).subtype ((prodComplex Γ V Z).X n) :=
  Rep.ofHom ⟨((fixThetaBar (G := MulAction.stabilizer Γ a) (V := V) (Z := Z) v₀ a
    (fun g => g.2)).f n).hom.toLinearMap, fun g =>
      ((fixThetaBar (G := MulAction.stabilizer Γ a) (V := V) (Z := Z) v₀ a
        (fun g => g.2)).f n).hom.2 g⟩

theorem thetaTilde_comm (n : ℕ) :
    (Rep.barComplex ℚ (MulAction.stabilizer Γ a)).d (n + 1) n ≫ thetaTilde v₀ a n =
      thetaTilde (Z := Z) v₀ a (n + 1) ≫
        (Rep.resFunctor (MulAction.stabilizer Γ a).subtype).map ((prodComplex Γ V Z).d (n + 1) n) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro b
  have h := congrArg (fun t => t.hom b)
    ((fixThetaBar (G := MulAction.stabilizer Γ a) (V := V) (Z := Z) v₀ a (fun g => g.2)).comm (n + 1) n)
  have h2 := congrArg (fun t => t (((fixThetaBar (G := MulAction.stabilizer Γ a) (V := V) (Z := Z) v₀ a
    (fun g => g.2)).f (n + 1)).hom b))
    (prodComplex_res_d (MulAction.stabilizer Γ a) (V := V) (Z := Z) n)
  refine h.symm.trans ?_
  exact h2

/-- The Γ-chain map `Ind_S^Γ bar(S) ⟶ prodComplex Γ V Z` adjoint to `thetaTilde`. -/
def psi1 : (orbitResolution Γ a).complex ⟶ prodComplex Γ V Z where
  f n := ((Rep.indResAdjunction ℚ (MulAction.stabilizer Γ a).subtype).homEquiv _ _).symm
    (thetaTilde v₀ a n)
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    have e1 := (Rep.indResAdjunction ℚ (MulAction.stabilizer Γ a).subtype).homEquiv_naturality_right_symm
      (thetaTilde (Z := Z) v₀ a (j + 1))
      ((prodComplex Γ V Z).d (j + 1) j)
    have e2 := (Rep.indResAdjunction ℚ (MulAction.stabilizer Γ a).subtype).homEquiv_naturality_left_symm
      ((Rep.barComplex ℚ (MulAction.stabilizer Γ a)).d (j + 1) j) (thetaTilde (Z := Z) v₀ a j)
    exact e1.symm.trans ((congrArg
      (fun t => ((Rep.indResAdjunction ℚ (MulAction.stabilizer Γ a).subtype).homEquiv _ _).symm t)
      (thetaTilde_comm v₀ a j).symm).trans e2)

theorem stabCoord_eq_psi1 (W : Rep.{0} ℚ Γ) :
    stabCoord (MulAction.stabilizer Γ a) W v₀ a (fun g => g.2) =
      homPullback (psi1 v₀ a) W ≫ (orbitShapiroIso Γ a W).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro b
  have hmk : (Rep.Hom.hom
      (((Rep.indResAdjunction ℚ (MulAction.stabilizer Γ a).subtype).homEquiv _ _)
        (((Rep.indResAdjunction ℚ (MulAction.stabilizer Γ a).subtype).homEquiv _ _).symm
          (thetaTilde (Z := Z) v₀ a n)))).toLinearMap b =
      (Rep.Hom.hom (thetaTilde (Z := Z) v₀ a n)).toLinearMap b := by
    rw [Equiv.apply_symm_apply]
  change (stabResHom (S := MulAction.stabilizer Γ a) W c).hom
      (((fixThetaBar (G := MulAction.stabilizer Γ a) (V := V) (Z := Z) v₀ a (fun g => g.2)).f n).hom b) =
    ((psi1 v₀ a).f n ≫ c).hom (Representation.IndV.mk (MulAction.stabilizer Γ a).subtype
      ((Rep.barComplex ℚ (MulAction.stabilizer Γ a)).X n).ρ 1 b)
  have hc := congrArg (fun t => t (((fixThetaBar (G := MulAction.stabilizer Γ a) (V := V) (Z := Z) v₀ a
      (fun g => g.2)).f n).hom b))
    (stabResHom_hom (S := MulAction.stabilizer Γ a) (V := V) (Z := Z) W c)
  refine hc.trans ?_
  change c.hom ((thetaTilde (Z := Z) v₀ a n).hom b) = c.hom (((psi1 v₀ a).f n).hom _)
  refine congrArg c.hom ?_
  exact hmk.symm

theorem sumRes_pi_incl {I : Type} {A : I → Rep.{0} ℚ Γ} (P : ∀ i, ProjectiveResolution (A i)) (i : I) :
    (Family.inclusion (fun i => (P i).complex) i).f 0 ≫ (Family.sumResolution P).π.f 0 =
      (P i).π.f 0 ≫ Sigma.ι A i := by
  simp [Family.sumResolution, Family.inclusion, Family.augmentation]
  erw [Limits.ι_colimMap_assoc]
  simp
  rfl

theorem orbitFamilyIso_ι (X : Type) [MulAction Γ X] (o : labelOrbits Γ X)
    (p : labelOrbit Γ X o) (r : ℚ) :
    (orbitFamilyIso Γ X).hom.hom
      ((Sigma.ι (fun o : labelOrbits Γ X => orbitLabels Γ o.out) o).hom (MonoidAlgebra.single p r)) =
      MonoidAlgebra.single p.val r := by
  have h1 := congrArg (fun m : Rep.ofMulAction ℚ Γ (labelOrbit Γ X o) ⟶ sigmaLabels Γ
      (fun o : labelOrbits Γ X => ↥(labelOrbit Γ X o)) => m.hom (MonoidAlgebra.single p r))
    (Sigma.ι_comp_desc (sigmaLabelInclusion Γ (fun o : labelOrbits Γ X => ↥(labelOrbit Γ X o))) o)
  change (permutationMap (orbitPartition Γ X) (orbitPartition_equivariant Γ X)).hom
      ((Sigma.desc (sigmaLabelInclusion Γ (fun o : labelOrbits Γ X => ↥(labelOrbit Γ X o)))).hom
        ((Sigma.ι (fun o : labelOrbits Γ X => orbitLabels Γ o.out) o).hom (MonoidAlgebra.single p r))) = _
  have h2 : (Sigma.desc (sigmaLabelInclusion Γ (fun o : labelOrbits Γ X => ↥(labelOrbit Γ X o)))).hom
        ((Sigma.ι (fun o : labelOrbits Γ X => orbitLabels Γ o.out) o).hom (MonoidAlgebra.single p r)) =
      (sigmaLabelInclusion Γ (fun o : labelOrbits Γ X => ↥(labelOrbit Γ X o)) o).hom
        (MonoidAlgebra.single p r) := h1
  rw [h2]
  have h3 : (sigmaLabelInclusion Γ (fun o : labelOrbits Γ X => ↥(labelOrbit Γ X o)) o).hom
        (MonoidAlgebra.single p r) = MonoidAlgebra.single ⟨o, p⟩ r := permutationMap_single _ _ _ _
  rw [h3]
  exact permutationMap_single _ _ _ _

theorem stab_aug_incl (X : Type) [MulAction Γ X] (o : labelOrbits Γ X)
    (b : (Rep.barResolution ℚ (stabilizer Γ o.out)).complex.X 0) :
    (stabilizerResolution Γ X).π.f 0
      ((Family.inclusion (fun o : labelOrbits Γ X => (orbitResolution Γ o.out).complex) o).f 0
        (Representation.IndV.mk (stabilizer Γ o.out).subtype
          ((Rep.barResolution ℚ (stabilizer Γ o.out)).complex.X 0).ρ 1 b)) =
      MonoidAlgebra.single o.out (barAugmentValue Γ o.out b) := by
  have h1 := sumRes_pi_incl (fun o : labelOrbits Γ X => orbitResolution Γ o.out) o
  have h2 := congrArg (fun m => m.hom (Representation.IndV.mk (stabilizer Γ o.out).subtype
          ((Rep.barResolution ℚ (stabilizer Γ o.out)).complex.X 0).ρ 1 b)) h1
  have e : (stabilizerResolution Γ X).π.f 0 =
      (orbitFamilyResolution Γ X).π.f 0 ≫ (orbitFamilyIso Γ X).hom := by
    unfold stabilizerResolution
    simp
  rw [e]
  change (orbitFamilyIso Γ X).hom.hom (((Family.inclusion (fun o : labelOrbits Γ X =>
      (orbitResolution Γ o.out).complex) o).f 0 ≫ (orbitFamilyResolution Γ X).π.f 0).hom
      (Representation.IndV.mk (stabilizer Γ o.out).subtype
          ((Rep.barResolution ℚ (stabilizer Γ o.out)).complex.X 0).ρ 1 b)) = _
  rw [h1]
  change (orbitFamilyIso Γ X).hom.hom ((Sigma.ι (fun o : labelOrbits Γ X => orbitLabels Γ o.out) o).hom ((orbitResolution Γ o.out).π.f 0
    (Representation.IndV.mk (stabilizer Γ o.out).subtype
          ((Rep.barResolution ℚ (stabilizer Γ o.out)).complex.X 0).ρ 1 b))) = _
  rw [orbitResolution_augmentation_mk]
  rw [orbitFamilyIso_ι]
  simp [orbitPoint]

theorem barAugmentValue_single (S : Type) [Group S] (x : Fin 0 → S) :
    (Rep.barResolution ℚ S).π.f 0 (single x (MonoidAlgebra.single 1 1)) = (1 : ℚ) := by
  have h : (Rep.barResolution ℚ S).π.f 0 =
      (Rep.barComplex.isoStandardComplex ℚ S).hom.f 0 ≫ (Rep.standardComplex.ε ℚ S) := by
    simp [Rep.barResolution, Rep.standardComplex.εToSingle₀]
    rfl
  rw [h]
  change (Rep.standardComplex.ε ℚ S).hom ((Rep.diagonalSuccIsoFree ℚ S 0).inv.hom
    (single x (MonoidAlgebra.single 1 1))) = 1
  rw [diagonalSuccIsoFree_inv_single]
  simp [Rep.standardComplex.ε]

theorem prodRes_pi_f_zero (v₀ : V) (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) :
    (prodResolution Γ V Z v₀ hfree).π.f 0 = prodEps Γ V Z := by
  simp [prodResolution, prodEpsToSingle]

theorem psi_aug (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (o : labelOrbits Γ Z)
    (κ : (stabilizerResolution Γ Z).complex ⟶ prodComplex Γ V Z)
    (hκ : κ.f 0 ≫ (prodResolution Γ V Z v₀ hfree).π.f 0 = (stabilizerResolution Γ Z).π.f 0) :
    (psi1 v₀ o.out).f 0 ≫ (prodResolution Γ V Z v₀ hfree).π.f 0 =
      ((Family.inclusion (fun o : labelOrbits Γ Z => (orbitResolution Γ o.out).complex) o) ≫ κ).f 0 ≫
        (prodResolution Γ V Z v₀ hfree).π.f 0 := by
  have e : ((Family.inclusion (fun o : labelOrbits Γ Z => (orbitResolution Γ o.out).complex) o) ≫ κ).f 0 ≫
        (prodResolution Γ V Z v₀ hfree).π.f 0 =
      (Family.inclusion (fun o : labelOrbits Γ Z => (orbitResolution Γ o.out).complex) o).f 0 ≫
        (stabilizerResolution Γ Z).π.f 0 := by
    erw [HomologicalComplex.comp_f, Category.assoc, hκ]
  rw [e]
  refine (Rep.indResHomEquiv (stabilizer Γ o.out).subtype
    ((Rep.barResolution ℚ (stabilizer Γ o.out)).complex.X 0)
    (((ChainComplex.single₀ (Rep.{0} ℚ Γ)).obj (Rep.ofMulAction ℚ Γ Z)).X 0)).injective ?_
  apply Rep.free_ext
  intro x
  have hmk0 : (Rep.Hom.hom
      (((Rep.indResAdjunction ℚ (stabilizer Γ o.out).subtype).homEquiv _ _)
        (((Rep.indResAdjunction ℚ (stabilizer Γ o.out).subtype).homEquiv _ _).symm
          (thetaTilde (Z := Z) v₀ o.out 0)))).toLinearMap (single x (MonoidAlgebra.single 1 1)) =
      (Rep.Hom.hom (thetaTilde (Z := Z) v₀ o.out 0)).toLinearMap (single x (MonoidAlgebra.single 1 1)) := by
    rw [Equiv.apply_symm_apply]
  have hmk : ((psi1 v₀ o.out).f 0).hom (Representation.IndV.mk (stabilizer Γ o.out).subtype
      ((Rep.barResolution ℚ (stabilizer Γ o.out)).complex.X 0).ρ 1
        (single x (MonoidAlgebra.single 1 1))) =
      (thetaTilde (Z := Z) v₀ o.out 0).hom (single x (MonoidAlgebra.single 1 1)) := hmk0
  have hR := stab_aug_incl Z o (single x (MonoidAlgebra.single 1 1))
  have hbar : barAugmentValue Γ o.out (single x (MonoidAlgebra.single 1 1)) = 1 :=
    barAugmentValue_single (stabilizer Γ o.out) x
  rw [hbar] at hR
  have hL : (prodResolution Γ V Z v₀ hfree).π.f 0
      ((thetaTilde (Z := Z) v₀ o.out 0).hom (single x (MonoidAlgebra.single 1 1))) =
      MonoidAlgebra.single o.out 1 := by
    rw [prodRes_pi_f_zero]
    change (prodEps Γ V Z).hom (((fixThetaBar (G := MulAction.stabilizer Γ o.out) (V := V) (Z := Z) v₀
      o.out (fun g => g.2)).f 0).hom (single x (MonoidAlgebra.single 1 1))) = _
    exact (congrArg (fun w => (prodEps Γ V Z).hom w)
      (fixThetaBar_f_single (G := MulAction.stabilizer Γ o.out) (V := V) (Z := Z) v₀ o.out
        (fun g => g.2) 0 x)).trans (prodEps_single Γ V Z _ _)
  refine Eq.trans (b := MonoidAlgebra.single o.out (1 : ℚ)) ?_ hR.symm
  refine Eq.trans ?_ hL
  exact congrArg (fun w => ((prodResolution Γ V Z v₀ hfree).π.f 0).hom w) hmk
/-- The `o`-th Shapiro coordinate of the library's stabilizer decomposition, on Hom cochains of the
stabilizer resolution. -/
def subCoord (W : Rep.{0} ℚ Γ) (o : labelOrbits Γ Z) :
    homCochains (stabilizerResolution Γ Z).complex W ⟶
      homCochains (Rep.barResolution ℚ (stabilizer Γ o.out)).complex (Rep.res (stabilizer Γ o.out).subtype W) :=
  homPullback (Family.inclusion (fun o : labelOrbits Γ Z => (orbitResolution Γ o.out).complex) o) W ≫
    (orbitShapiroIso Γ o.out W).hom

/-- The `o`-th component of `fullShapiroIso` is `subCoord`. -/
theorem fullShapiroDegree_eq_subCoord (W : Rep.{0} ℚ Γ) (n : ℕ)
    (c : (stabilizerResolution Γ Z).complex.X n ⟶ W) (o : labelOrbits Γ Z) :
    fullShapiroDegree Γ Z W n c o = ((subCoord W o).f n).hom c := rfl

/-- **Agreement with the library's Shapiro decomposition.**  For any chain map `κ` from the library's
stabilizer resolution to the permutation resolution over the identity of `ℚ[Z]`, the Shapiro coordinate
`stabCoord` at a representative `a = o.out` of an orbit induces on cohomology the same map as `κ`-pullback
followed by the `o`-th component of `fullShapiroIso`. -/
theorem stabCoord_homology_eq_subCoord (W : Rep.{0} ℚ Γ)
    (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (o : labelOrbits Γ Z)
    (κ : (stabilizerResolution Γ Z).complex ⟶ prodComplex Γ V Z)
    (hκ : κ.f 0 ≫ (prodResolution Γ V Z v₀ hfree).π.f 0 = (stabilizerResolution Γ Z).π.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap (stabCoord (stabilizer Γ o.out) W v₀ o.out (fun g => g.2)) n =
      HomologicalComplex.homologyMap (homPullback κ W ≫ subCoord W o) n := by
  have : ∀ n, Projective ((orbitResolution Γ o.out).complex.X n) :=
    fun n => (orbitResolution Γ o.out).projective n
  have H := uniqHomotopy (C := (orbitResolution Γ o.out).complex)
    (Q := prodResolution Γ V Z v₀ hfree) (psi1 v₀ o.out)
    ((Family.inclusion (fun o : labelOrbits Γ Z => (orbitResolution Γ o.out).complex) o) ≫ κ)
    (psi_aug v₀ hfree o κ hκ)
  have hchain : homPullback κ W ≫ subCoord W o =
      homPullback ((Family.inclusion (fun o : labelOrbits Γ Z => (orbitResolution Γ o.out).complex) o) ≫
        κ) W ≫ (orbitShapiroIso Γ o.out W).hom := by
    unfold subCoord
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    rfl
  rw [hchain, stabCoord_eq_psi1]
  exact ((homPullbackHomotopy H W).compRight (orbitShapiroIso Γ o.out W).hom).homologyMap_eq n

end Step2


end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
