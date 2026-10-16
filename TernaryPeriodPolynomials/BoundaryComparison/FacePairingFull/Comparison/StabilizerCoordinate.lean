module

public import TernaryPeriodPolynomials.Topology.TopHomology.HomFunA
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallCochains
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.PairHomotopyHom
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ProjectiveUniqueness

@[expose] public section


/-!
# The Shapiro coordinate at a point, with Mathlib's group cohomology of the stabilizer

For a group `G` acting on a free vertex set `V` (base point `v₀`) and on a set `Z`, and a `G`-fixed point
`z : Z`, the simplicial map `(g_i) ↦ ((g_i v₀), z)` from the universal cover `EG` of `BG` to the nerve
`V^{•+1} × Z` of the permutation resolution induces a chain map `fixTheta` out of the standard resolution
and, composed with the isomorphism of the bar and standard resolutions, `fixThetaBar : barComplex ℚ G ⟶
prodComplex G V Z`.  Pulling back gives `fixCoord`, and `fixCoordH` lands in Mathlib's `groupCohomology W n`
(through the bar resolution, for which `groupCohomologyIso` is the homology of the inhomogeneous cochains).
For a point `z` of a `Γ`-set with stabilizer `S`, `faceCoord` first restricts Hom cochains from `Γ` to `S`
(`stabResChain`) and then applies `fixCoord` for the group `S`; on a generator `(x_1, ..., x_k)` of the bar
resolution it is the invariant function evaluated at the simplex with vertices `(x_1 ⋯ x_i) v₀` over `z`
(`stabCoord_single`).  It is independent of the chain map over the augmentation
(`fixCoord_homology_eq`, by `uniqHomotopy`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits Simplicial SimplicialObject AlgebraicTopology Finsupp

noncomputable section

namespace TernaryPeriodPolynomials.Argument.TopHomology

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem diagonalSuccIsoFree_inv_single (G : Type) [Group G] (m : ℕ) (f : Fin m → G) (g : G) (r : ℚ) :
    (Rep.diagonalSuccIsoFree ℚ G m).inv.hom (single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Rep.Hom.hom (Rep.leftRegularTensorTrivialIsoFree ℚ G (Fin m → G)).inv)
      (single f (.single g r)) = .single g 1 ⊗ₜ[ℚ] .single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step1]
  simp only [Rep.mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
    LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
    Functor.mapIso_inv, Rep.tensor_V, Rep.tensor_ρ, Iso.symm_inv, Functor.Monoidal.μIso_hom, Rep.μ_hom,
    MonoidalCategory.tensorIso_inv, Representation.linearizeTrivialIso, Rep.hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := ℚ)
    (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) ((1 : ℚ) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := ℚ)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans (by simp)


section Fix

open TernaryPoly.EquivariantSingularSmall

/-- Mathlib's group cohomology is the cohomology of the Hom complex of the bar resolution. -/
def gisoBar {G : Type} [Group G] (A : Rep.{0} ℚ G) (n : ℕ) :
    groupCohomology A n ≅ (homCochains (Rep.barComplex ℚ G) A).homology n :=
  groupCohomologyIso A n (Rep.barResolution ℚ G)

variable {G : Type} [Group G] {V Z : Type} [MulAction G V] [MulAction G Z]
  (v₀ : V) (z : Z) (hz : ∀ g : G, g • z = z)

/-- The simplicial map `EG ⟶ V^{•+1} × Z`, `(g_i) ↦ ((g_i v₀), z)`. -/
def fixNerveMap : classifyingSpaceUniversalCover G ⟶ prodNerve G V Z where
  app n := ⟨↾fun s => (fun i => s i • v₀, z), fun g => by
    ext s
    exact Prod.ext (funext fun i => mul_smul g (s i) v₀) (hz g).symm⟩
  naturality _ _ _ := rfl

/-- The chain map `standardComplex ℚ G ⟶ prodComplex G V Z`. -/
def fixTheta : Rep.standardComplex ℚ G ⟶ prodComplex G V Z :=
  (alternatingFaceMapComplex (Rep.{0} ℚ G)).map
    (Functor.whiskerRight (fixNerveMap v₀ z hz) (Rep.linearization ℚ G))

theorem fixTheta_f_single (k : ℕ) (x : Fin (k + 1) → G) :
    ((fixTheta v₀ z hz).f k).hom (MonoidAlgebra.single x 1) =
      MonoidAlgebra.single (fun i => x i • v₀, z) 1 := by
  simp only [fixTheta, fixNerveMap, alternatingFaceMapComplex_map_f, Functor.whiskerRight_app]
  exact Representation.linearizeMap_single _ _ _

/-- The chain map `barComplex ℚ G ⟶ prodComplex G V Z`. -/
def fixThetaBar : Rep.barComplex ℚ G ⟶ prodComplex G V Z :=
  (Rep.barComplex.isoStandardComplex ℚ G).hom ≫ fixTheta v₀ z hz

/-- On a generator `(x_1, ..., x_k)` of the bar resolution the chain map `fixThetaBar` is the simplex with
vertices the partial products `x_1 ⋯ x_i`, acting on `v₀`. -/
theorem fixThetaBar_f_single (k : ℕ) (x : Fin k → G) :
    ((fixThetaBar v₀ z hz).f k).hom (single x (MonoidAlgebra.single 1 1)) =
      MonoidAlgebra.single (fun i => Fin.partialProd x i • v₀, z) 1 := by
  change ((fixTheta v₀ z hz).f k).hom
    ((Rep.diagonalSuccIsoFree ℚ G k).inv.hom (single x (MonoidAlgebra.single 1 1))) = _
  rw [diagonalSuccIsoFree_inv_single, one_smul]
  exact fixTheta_f_single v₀ z hz k _

/-- The Shapiro-type coordinate at a fixed point `z`: pullback along `fixThetaBar`. -/
def fixCoord (W : Rep.{0} ℚ G) :
    homCochains (prodComplex G V Z) W ⟶ homCochains (Rep.barComplex ℚ G) W :=
  homPullback (fixThetaBar v₀ z hz) W

/-- On cohomology, with Mathlib's group cohomology (through the bar resolution). -/
def fixCoordH (W : Rep.{0} ℚ G) (n : ℕ) :
    (homCochains (prodComplex G V Z) W).homology n ⟶ groupCohomology W n :=
  HomologicalComplex.homologyMap (fixCoord v₀ z hz W) n ≫
    (gisoBar W n).inv

end Fix

section ResWrap

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z]

section Res

variable (S : Subgroup Γ) (W : Rep.{0} ℚ Γ)

/-- Restriction of a morphism out of the permutation resolution to the subgroup `S`. -/
def stabResHom {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ W) :
    (prodComplex S V Z).X k ⟶ Rep.res S.subtype W :=
  homOfFunA (A := Rep.res S.subtype W)
    (fun y => (homFunA (Γ := Γ) (V := V) (Z := Z) (A := W) c y : W))
    (fun g y => homFunA_equivariant (Γ := Γ) (V := V) (Z := Z) (A := W) c g.val y)

theorem homFunA_stabResHom {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ W) :
    homFunA (stabResHom (S := S) (V := V) (Z := Z) W c) =
      fun y => (homFunA (Γ := Γ) (V := V) (Z := Z) (A := W) c y : W) :=
  homFunA_homOfFunA _ _

theorem stabResHom_hom {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ W) :
    (stabResHom (S := S) W c).hom.toLinearMap = c.hom.toLinearMap := by
  apply MonoidAlgebra.lhom_ext'
  intro y
  apply LinearMap.ext_ring
  exact congrFun (homFunA_stabResHom (S := S) (V := V) (Z := Z) W c) y

theorem stabResHom_add {k : ℕ} (c c' : (prodComplex Γ V Z).X k ⟶ W) :
    stabResHom (S := S) W (c + c') = stabResHom (S := S) W c + stabResHom (S := S) W c' := by
  apply homFunA_injective
  rw [homFunA_add, homFunA_stabResHom, homFunA_stabResHom, homFunA_stabResHom]
  rfl

theorem stabResHom_smul {k : ℕ} (r : ℚ) (c : (prodComplex Γ V Z).X k ⟶ W) :
    stabResHom (S := S) W (r • c) = r • stabResHom (S := S) W c := by
  apply homFunA_injective
  rw [homFunA_smul, homFunA_stabResHom, homFunA_stabResHom]
  rfl

theorem stabResHom_d {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ W) :
    (prodComplex S V Z).d (k + 1) k ≫ stabResHom (S := S) W c =
      stabResHom (S := S) W ((prodComplex Γ V Z).d (k + 1) k ≫ c) := by
  apply homFunA_injective
  funext y
  rw [homFunA_comp_d, homFunA_stabResHom]
  have h := homFunA_comp_d (Γ := Γ) (V := V) (Z := Z) (A := W) c y
  rw [homFunA_stabResHom]
  refine Eq.trans ?_ h.symm
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

end Res

end ResWrap

section Coord

open TernaryPoly.EquivariantSingularSmall

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z]
  (S : Subgroup Γ) (W : Rep.{0} ℚ Γ)

/-- Restriction of Hom cochains of the permutation resolution to the stabilizer group, as a cochain map. -/
def stabResChain : homCochains (prodComplex Γ V Z) W ⟶
    homCochains (prodComplex S V Z) (Rep.res S.subtype W) where
  f k := ModuleCat.ofHom
    { toFun := fun c => stabResHom (S := S) W c
      map_add' := fun c c' => stabResHom_add S W c c'
      map_smul' := fun r c => stabResHom_smul S W r c }
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact stabResHom_d S W c

variable (v₀ : V) (z : Z) (hz : ∀ g : S, g • z = z)

/-- **The Shapiro coordinate at `z`, on cochains**: restriction to the stabilizer `S` followed by `fixCoord`. -/
def stabCoord : homCochains (prodComplex Γ V Z) W ⟶
    homCochains (Rep.barComplex ℚ S) (Rep.res S.subtype W) :=
  stabResChain S W ≫ fixCoord v₀ z hz (Rep.res S.subtype W)

/-- On a generator `(x_1, ..., x_k)` of the bar resolution of `S` the Shapiro coordinate is the value of the
invariant function of `c` at the simplex with vertices `(x_1 ⋯ x_i) v₀` over `z`. -/
theorem stabCoord_single (k : ℕ) (c : (prodComplex Γ V Z).X k ⟶ W) (x : Fin k → S) :
    ((((stabCoord S W v₀ z hz).f k).hom c).hom (single x (MonoidAlgebra.single 1 1))) =
      homFunA (Γ := Γ) (V := V) (Z := Z) (A := W) c (fun i => Fin.partialProd x i • v₀, z) := by
  change (stabResHom (S := S) W c).hom
      (((fixThetaBar v₀ z hz).f k).hom (single x (MonoidAlgebra.single 1 1))) = _
  rw [fixThetaBar_f_single]
  exact congrFun (homFunA_stabResHom (S := S) (V := V) (Z := Z) W c) _

/-- **The Shapiro coordinate at `z` on cohomology**, with values in the group cohomology of the stabilizer
of `z` (Mathlib's `groupCohomology`). -/
def faceCoord (n : ℕ) : (homCochains (prodComplex Γ V Z) W).homology n ⟶
    groupCohomology (Rep.res S.subtype W) n :=
  HomologicalComplex.homologyMap (stabResChain S W) n ≫ fixCoordH v₀ z hz (Rep.res S.subtype W) n

end Coord

section Canonical

open TernaryPoly.EquivariantSingularSmall TernaryPoly.EquivariantSingularPairHomotopy
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison (uniqHomotopy)

variable {G : Type} [Group G] {V Z : Type} [MulAction G V] [MulAction G Z]
  (W : Rep.{0} ℚ G) (v₀ : V) (z : Z) (hz : ∀ g : G, g • z = z)
  (hfree : ∀ (γ : G) (v : V), γ • v = v → γ = 1)

/-- Freeness of the restricted action on the vertices. -/
theorem free_stab (S : Subgroup G) (hfree : ∀ (γ : G) (v : V), γ • v = v → γ = 1) :
    ∀ (γ : S) (v : V), γ • v = v → γ = 1 := fun γ v h =>
  Subtype.ext (hfree γ.val v h)

/-- **Canonicity of the coordinate**: any chain map `barComplex ℚ G ⟶ prodComplex G V Z` with the same
augmentation as `fixThetaBar` induces the same map on cohomology of the Hom complexes. -/
theorem fixCoord_homology_eq (θ' : Rep.barComplex ℚ G ⟶ prodComplex G V Z)
    (h0 : θ'.f 0 ≫ (prodResolution G V Z v₀ hfree).π.f 0 =
      (fixThetaBar v₀ z hz).f 0 ≫ (prodResolution G V Z v₀ hfree).π.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap (homPullback θ' W) n =
      HomologicalComplex.homologyMap (fixCoord v₀ z hz W) n := by
  have : ∀ n, Projective ((Rep.barComplex ℚ G).X n) :=
    fun n => (Rep.barResolution ℚ G).projective n
  have H := uniqHomotopy (C := Rep.barComplex ℚ G) (Q := prodResolution G V Z v₀ hfree)
    θ' (fixThetaBar v₀ z hz) h0
  exact homPullback_cohomology_eq H W n

end Canonical

end TernaryPeriodPolynomials.Argument.TopHomology
