module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.SingularDiag
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.TensorCarriers
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Carriers
public import TernaryPeriodPolynomials.Topology.Singular.ComponentAugmentationEquivariant
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceAugmentationNaturality

@[expose] public section


/-!
# Face carriers: the chains carried by one label of a sum of faces

For a group `G` acting on a space `E` with a `G`-equivariant labelling `lab : E → Z` that is constant on
singular simplices (`LabelData`; e.g. a sum `Σ z, X z` over a discrete set of labels), the subspaces
`faceK z m` of the equivariant singular chains spanned by the simplices carrying the label `z` are the
carriers used for the acyclic-carrier construction of the comparison `Ψ'` (P09 M2.1(c)).

Generic part (any `LabelData`):

* `LabelData.faceK_smul` (K1): `faceK (g • z) m = (faceK z m).map (ρ g)`;
* `LabelData.faceK_subcomplex` (K2): `faceK z` is a subcomplex (faces of a simplex keep its label);
* `LabelData.faceK_cap` (K4): `capE E W a q b` maps `faceK z (a+q)` into `tensorK W (faceK z q)`;
* `LabelData.faceK_map` (K5): an equivariant map of spaces compatible with labels (`lab' (F x) = ψ (lab x)`)
  carries `faceK z` into `faceK (ψ z)`;
* `LabelData.faceK_diag` (K6): the Alexander-Whitney diagonal sends `faceK z n` into the span of tensors
  `u ⊗ v` with `u ∈ faceK z p`, `v ∈ faceK z q`;
* `LabelData.proj`: the projection of the chains onto the simplices carrying the label `z`; it commutes
  with the boundary (`proj_d`) and is the identity on `faceK z` (`proj_of_mem`).

Sigma-type spaces (`LabelData.ofSigma`, `Total X = Σ i, X i` with contractible fibres over a discrete
set of labels): augmented acyclicity of the carriers (K3) with respect to `singEps`:
`ofSigma_acyc0`, `ofSigma_acyc`, `ofSigma_exists_vertex`.  The fibre-wise statement is deduced from
the library's global exactness of the chains of the sum space (`scalar_exactAt`, `scalar_augmented_exact`)
by applying the projection `proj` to a primitive.

Concrete part: `principalSix` and the three face sums `LineFaceSum`, `PlaneFaceSum`, `CornerFaceSum`
of `TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation`, with the three specialisations
`lineFaceK`, `planeFaceK`, `flagFaceK` and (K1)-(K4), (K6), and (K5) for `lineChainMap` and
`planeChainMap` (`lineChainMap_flagFaceK`, `planeChainMap_flagFaceK`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalHomology
open TernaryPoly.FreeActionLinearization
open TernaryPeriodPolynomials.Argument.TopHomology
open SphereOddDegree.AlexanderWhitney
open scoped Simplicial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {G : Type} [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  {Z : Type} [MulAction G Z]

/-- The singular simplices form a basis of the chains. -/
def chainBasis (m : ℕ) : Module.Basis (SingularSimplex E m) ℚ (chainRep G E m) :=
  (Finsupp.basisSingleOne (R := ℚ) (ι := SingularSimplex E m)).map
    ((MonoidAlgebra.coeffLinearEquiv ℚ).symm ≪≫ₗ degreeLinearEquiv E m)

theorem chainBasis_apply (m : ℕ) (σ : SingularSimplex E m) :
    chainBasis (G := G) E m σ = chainElement G E m σ := by
  unfold chainBasis
  rw [Module.Basis.map_apply]
  simp only [Finsupp.coe_basisSingleOne, LinearEquiv.trans_apply]
  change degreeLinearEquiv E m ((MonoidAlgebra.coeffLinearEquiv ℚ).symm (Finsupp.single σ 1)) = _
  have : (MonoidAlgebra.coeffLinearEquiv ℚ).symm (Finsupp.single σ (1 : ℚ)) = MonoidAlgebra.single σ 1 := rfl
  rw [this, degreeLinearEquiv_single]
  rfl

/-- A `G`-equivariant labelling of the points of `E` which is constant on every singular simplex. -/
structure LabelData (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
    (Z : Type) [MulAction G Z] where
  lab : E → Z
  equivariant : ∀ (g : G) (x : E), lab (g • x) = g • lab x
  const : ∀ (m : ℕ) (σ : SingularSimplex E m) (u v : Convexity.StdSimplex ℝ (Fin (m+1))),
    lab (TopCat.toSSetObjEquiv E (.op ⦋m⦌) σ u) = lab (TopCat.toSSetObjEquiv E (.op ⦋m⦌) σ v)

/-- The base vertex of the standard simplex. -/
def v0 (m : ℕ) : Convexity.StdSimplex ℝ (Fin (m+1)) := Convexity.StdSimplex.single 0

namespace LabelData

variable {E} (L : LabelData G E Z)

/-- The label of a singular simplex. -/
def simpLab {m : ℕ} (σ : SingularSimplex E m) : Z :=
  L.lab (TopCat.toSSetObjEquiv E (.op ⦋m⦌) σ (v0 m))

theorem simpLab_eq {m : ℕ} (σ : SingularSimplex E m) (u : Convexity.StdSimplex ℝ (Fin (m+1))) :
    L.lab (TopCat.toSSetObjEquiv E (.op ⦋m⦌) σ u) = L.simpLab σ :=
  L.const m σ u (v0 m)

/-- The label is unchanged under every simplicial operator. -/
theorem simpLab_map {k m : ℕ} (θ : (⦋k⦌ : SimplexCategory) ⟶ ⦋m⦌) (σ : SingularSimplex E m) :
    L.simpLab ((TopCat.toSSet.obj E).map θ.op σ) = L.simpLab σ := by
  unfold simpLab
  have h := TopCat.toSSetObjEquiv_naturality_apply (X := E) θ σ (v0 k)
  refine Eq.trans (congrArg L.lab h) ?_
  exact L.simpLab_eq σ _

theorem simpLab_δ {m : ℕ} (i : Fin (m+2)) (σ : SingularSimplex E (m+1)) :
    L.simpLab ((TopCat.toSSet.obj E).δ i σ) = L.simpLab σ :=
  L.simpLab_map (SimplexCategory.δ i) σ

theorem simpLab_front (p q : ℕ) (σ : SingularSimplex E (p+q)) :
    L.simpLab (frontSimplex E p q σ) = L.simpLab σ :=
  L.simpLab_map (frontFace p q) σ

theorem simpLab_back (p q : ℕ) (σ : SingularSimplex E (p+q)) :
    L.simpLab (backSimplex E p q σ) = L.simpLab σ :=
  L.simpLab_map (backFace p q) σ

theorem simpLab_smul {m : ℕ} (g : G) (σ : SingularSimplex E m) :
    L.simpLab (g • σ) = g • L.simpLab σ := by
  unfold simpLab
  rw [singularEquiv_smul]
  exact L.equivariant g _

/-- The subspace of chains spanned by the simplices carrying the label `z`. -/
def faceK (z : Z) (m : ℕ) : Submodule ℚ ((equivariantChains G E).X m) :=
  Submodule.span ℚ {x | ∃ σ : SingularSimplex E m, L.simpLab σ = z ∧ x = chainElement G E m σ}

theorem chainElement_mem_faceK {z : Z} {m : ℕ} (σ : SingularSimplex E m) (h : L.simpLab σ = z) :
    chainElement G E m σ ∈ L.faceK z m :=
  Submodule.subset_span ⟨σ, h, rfl⟩

/-- **(K1)** The carriers are permuted by the group action according to the labels. -/
theorem faceK_smul (g : G) (z : Z) (m : ℕ) :
    L.faceK (g • z) m = (L.faceK z m).map (((equivariantChains G E).X m).ρ g) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨σ, hσ, rfl⟩
    refine ⟨chainElement G E m (g⁻¹ • σ), L.chainElement_mem_faceK _ ?_, ?_⟩
    · rw [L.simpLab_smul, hσ, inv_smul_smul]
    · change (chainRep G E m).ρ g (chainElement G E m (g⁻¹ • σ)) = _
      rw [chainElement_smul, smul_inv_smul]
  · rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨σ, hσ, rfl⟩ := hy
      change (chainRep G E m).ρ g (chainElement G E m σ) ∈ _
      rw [chainElement_smul]
      exact L.chainElement_mem_faceK _ (by rw [L.simpLab_smul, hσ])
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
    | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy

/-- **(K2)** The carriers form a subcomplex. -/
theorem faceK_subcomplex {z : Z} {m : ℕ} {x : (equivariantChains G E).X (m+1)}
    (hx : x ∈ L.faceK z (m+1)) :
    ((equivariantChains G E).d (m+1) m).hom x ∈ L.faceK z m := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨σ, hσ, rfl⟩ := hy
    change (equivariantD G E (m+1) m).hom (chainElement G E (m+1) σ) ∈ _
    rw [chainElement_d]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact zsmul_mem (L.chainElement_mem_faceK _ (by rw [L.simpLab_δ, hσ])) _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy

/-- **(K4)** The cap of a chain carried by `z` lies in `W ⊗ (chains carried by z)`. -/
theorem faceK_cap (z : Z) (W : Rep.{0} ℚ G) (a : ℕ) (b : chainRep G E a ⟶ W) (q : ℕ)
    {x : chainRep G E (a+q)} (hx : x ∈ L.faceK z (a+q)) :
    (capE E W a q b).hom x ∈ tensorK W (L.faceK z q) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨σ, hσ, rfl⟩ := hy
    rw [capE_chainElement]
    exact tmul_mem_tensorK W _ (L.chainElement_mem_faceK _ (by rw [L.simpLab_back, hσ]))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

/-- **(K6)** The diagonal of a chain carried by `z` is a combination of tensors of chains carried by `z`. -/
theorem faceK_diag (z : Z) (p q n : ℕ) (h : p + q = n) {x : (equivariantChains G E).X n}
    (hx : x ∈ L.faceK z n) :
    ((singDiagSystem E).Δ p q n h).hom x ∈ Submodule.span ℚ
      {t | ∃ (u : (equivariantChains G E).X p) (v : (equivariantChains G E).X q),
        u ∈ L.faceK z p ∧ v ∈ L.faceK z q ∧ t = (u ⊗ₜ[ℚ] v : (chainRep G E p ⊗ chainRep G E q : Rep.{0} ℚ G))} := by
  subst h
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨σ, hσ, rfl⟩ := hy
    change (singDelta0 (G := G) E p q).hom (chainElement G E (p+q) σ) ∈ _
    rw [singDelta0_chainElement]
    exact Submodule.subset_span ⟨_, _, L.chainElement_mem_faceK _ (by rw [L.simpLab_front, hσ]),
      L.chainElement_mem_faceK _ (by rw [L.simpLab_back, hσ]), rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

open scoped Classical in
/-- The projection of the chains onto the simplices carrying the label `z`. -/
def proj (z : Z) (m : ℕ) : chainRep G E m →ₗ[ℚ] chainRep G E m :=
  (chainBasis (G := G) E m).constr ℚ
    (fun σ => if L.simpLab σ = z then chainElement G E m σ else 0)

open scoped Classical in
theorem proj_chainElement (z : Z) (m : ℕ) (σ : SingularSimplex E m) :
    L.proj z m (chainElement G E m σ) = if L.simpLab σ = z then chainElement G E m σ else 0 := by
  unfold proj
  rw [← chainBasis_apply (G := G) E m σ, Module.Basis.constr_basis, chainBasis_apply]

open scoped Classical in
theorem proj_mem (z : Z) (m : ℕ) (x : chainRep G E m) : L.proj z m x ∈ L.faceK z m := by
  have hx : x ∈ Submodule.span ℚ (Set.range (chainBasis (G := G) E m)) := by
    rw [(chainBasis (G := G) E m).span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨σ, rfl⟩ := hy
    rw [chainBasis_apply, proj_chainElement]
    split_ifs with h
    · exact L.chainElement_mem_faceK _ h
    · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

open scoped Classical in
theorem proj_of_mem (z : Z) (m : ℕ) {x : chainRep G E m} (hx : x ∈ L.faceK z m) : L.proj z m x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨σ, hσ, rfl⟩ := hy
    rw [proj_chainElement, ite_eq_left hσ]
  | zero => rw [map_zero]; rfl
  | add y y' _ _ hy hy' => rw [map_add, hy, hy']; rfl
  | smul c y _ hy => rw [map_smul, hy]; rfl

open scoped Classical in
/-- The projection commutes with the boundary: faces of a simplex have the same label. -/
theorem proj_d (z : Z) (m : ℕ) (y : chainRep G E (m+1)) :
    (equivariantD G E (m+1) m).hom (L.proj z (m+1) y) =
      L.proj z m ((equivariantD G E (m+1) m).hom y) := by
  have key : (equivariantD G E (m+1) m).hom.toLinearMap ∘ₗ L.proj z (m+1) =
      L.proj z m ∘ₗ (equivariantD G E (m+1) m).hom.toLinearMap := by
    apply chainRep_linear_ext E
    intro σ
    simp only [LinearMap.comp_apply]
    rw [proj_chainElement]
    change (equivariantD G E (m+1) m).hom (if L.simpLab σ = z then _ else 0) =
      L.proj z m ((equivariantD G E (m+1) m).hom (chainElement G E (m+1) σ))
    rw [chainElement_d]
    simp only [map_sum, map_zsmul]
    split_ifs with h
    · rw [chainElement_d]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [proj_chainElement, ite_eq_left (by rw [L.simpLab_δ, h])]
    · rw [map_zero]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [proj_chainElement, ite_eq_right (by rw [L.simpLab_δ]; exact h), smul_zero]
  exact LinearMap.congr_fun key y

section Map

variable {E' : TopCat.{0}} [MulAction G E'] [ContinuousConstSMul G E'] {Z' : Type} [MulAction G Z']
  (L' : LabelData G E' Z') (F : E ⟶ E') (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
  (ψ : Z → Z') (hψ : ∀ x, L'.lab (F x) = ψ (L.lab x))

include hψ in
theorem simpLab_spaceMap {m : ℕ} (σ : SingularSimplex E m) :
    L'.simpLab ((TopCat.toSSet.map F).app (Opposite.op ⦋m⦌) σ) = ψ (L.simpLab σ) := by
  unfold LabelData.simpLab
  have h : TopCat.toSSetObjEquiv E' (.op ⦋m⦌) ((TopCat.toSSet.map F).app (Opposite.op ⦋m⦌) σ) (v0 m) =
      F (TopCat.toSSetObjEquiv E (.op ⦋m⦌) σ (v0 m)) := rfl
  rw [h, hψ]

include hψ in
/-- **(K5)** An equivariant map of spaces compatible with the labels carries `faceK z` into `faceK (ψ z)`. -/
theorem faceK_map (z : Z) (m : ℕ) {x : (equivariantChains G E).X m} (hx : x ∈ L.faceK z m) :
    ((spaceChainMap E F hF).f m).hom x ∈ L'.faceK (ψ z) m := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨σ, hσ, rfl⟩ := hy
    rw [spaceChainMap_chainElement]
    exact L'.chainElement_mem_faceK _ (by rw [L.simpLab_spaceMap L' F ψ hψ σ, hσ])
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

end Map

end LabelData

section Sigma

open TernaryPoly.SingularComponentAugmentation (Total)

variable {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)] [∀ i, ContractibleSpace (X i)]
  [TopologicalSpace ι] [DiscreteTopology ι] [MulAction G ι]
  [MulAction G (Total X)] [ContinuousConstSMul G (Total X)]
  (hlabel : ∀ (g : G) (x : Total X), (g • x).1 = g • x.1)

omit [∀ i, ContractibleSpace (X i)] in
/-- The label data of a sum of spaces indexed by a discrete set of labels. -/
def LabelData.ofSigma : LabelData G (TopCat.of (Total X)) ι where
  lab := Sigma.fst
  equivariant := hlabel
  const m σ u v := TernaryPoly.SingularComponentAugmentation.simplex_label_constant X m σ u v

omit [∀ i, ContractibleSpace (X i)] in
theorem ofSigma_simpLab_zero (σ : SingularSimplex (TopCat.of (Total X)) 0) :
    (LabelData.ofSigma (G := G) X hlabel).simpLab σ = (TopCat.toSSetObj₀Equiv σ).1 := by
  unfold LabelData.simpLab
  rw [TopCat.toSSetObj₀Equiv_apply]
  have h : v0 0 = (default : Convexity.StdSimplex ℝ (Fin (⦋0⦌.len + 1))) := Subsingleton.elim _ _
  rw [h]
  rfl

/-- The augmentation `singEps` as a rational linear form. -/
def epsL (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E] : chainRep G E 0 →ₗ[ℚ] ℚ :=
  (singEps (G := G) E).hom.toLinearMap

theorem scalarAug_of_mem_faceK (z : ι) {y : chainRep G (TopCat.of (Total X)) 0}
    (hy : y ∈ (LabelData.ofSigma (G := G) X hlabel).faceK z 0) :
    (TernaryPoly.SingularComponentAugmentation.scalarAugmentation X).hom y =
      epsL (G := G) (TopCat.of (Total X)) y • MonoidAlgebra.single z (1 : ℚ) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨σ, hσ, rfl⟩ := hy
    have h1 : chainElement G (TopCat.of (Total X)) 0 σ =
        degreeLinearEquiv (TopCat.of (Total X)) 0 (MonoidAlgebra.single σ 1) := by
      rw [degreeLinearEquiv_single]; rfl
    have he : epsL (G := G) (TopCat.of (Total X)) (chainElement G (TopCat.of (Total X)) 0 σ) = 1 :=
      singEps_chainElement _ σ
    rw [he]
    change (TernaryPoly.SingularComponentAugmentation.scalarAugmentation X).hom
      (chainElement G (TopCat.of (Total X)) 0 σ) = _
    rw [h1, TernaryPoly.SingularComponentAugmentation.scalarAugmentation_single,
      ← ofSigma_simpLab_zero X hlabel, hσ]
    exact (one_smul ℚ _).symm
  | zero => rw [map_zero, map_zero, zero_smul]
  | add y y' _ _ hy hy' => rw [map_add, map_add, hy, hy', add_smul]
  | smul c y _ hy => rw [map_smul, map_smul, hy, smul_assoc]

theorem ofSigma_acyc0 (z : ι) {y : chainRep G (TopCat.of (Total X)) 0}
    (hy : y ∈ (LabelData.ofSigma (G := G) X hlabel).faceK z 0)
    (h0 : (singEps (G := G) (TopCat.of (Total X))).hom y = 0) :
    ∃ x ∈ (LabelData.ofSigma (G := G) X hlabel).faceK z 1,
      ((equivariantChains G (TopCat.of (Total X))).d 1 0).hom x = y := by
  have hs : (TernaryPoly.SingularComponentAugmentation.scalarAugmentation X).hom y = 0 := by
    rw [scalarAug_of_mem_faceK X hlabel z hy]
    have : epsL (G := G) (TopCat.of (Total X)) y = 0 := h0
    rw [this, zero_smul]
  have hex := (ShortComplex.moduleCat_exact_iff _).mp
    (TernaryPoly.SingularComponentAugmentation.scalar_augmented_exact X)
  obtain ⟨w, hw⟩ := hex y hs
  refine ⟨(LabelData.ofSigma (G := G) X hlabel).proj z 1 w, LabelData.proj_mem _ z 1 w, ?_⟩
  have h1 := LabelData.proj_d (LabelData.ofSigma (G := G) X hlabel) z 0 w
  have h2 : (equivariantD G (TopCat.of (Total X)) 1 0).hom w = y := hw
  change (equivariantD G (TopCat.of (Total X)) 1 0).hom _ = y
  rw [h1, h2]
  exact LabelData.proj_of_mem _ z 0 hy

theorem ofSigma_acyc (z : ι) (m : ℕ) {y : chainRep G (TopCat.of (Total X)) (m+1)}
    (hy : y ∈ (LabelData.ofSigma (G := G) X hlabel).faceK z (m+1))
    (h0 : ((equivariantChains G (TopCat.of (Total X))).d (m+1) m).hom y = 0) :
    ∃ x ∈ (LabelData.ofSigma (G := G) X hlabel).faceK z (m+2),
      ((equivariantChains G (TopCat.of (Total X))).d (m+2) (m+1)).hom x = y := by
  have hex0 := TernaryPoly.SingularComponentAugmentation.scalar_exactAt X (m+1) (Nat.succ_ne_zero m)
  have hex := (ShortComplex.moduleCat_exact_iff _).mp
    ((HomologicalComplex.exactAt_iff' _ (m+2) (m+1) m (by simp) (by simp)).mp hex0)
  obtain ⟨w, hw⟩ := hex y h0
  refine ⟨(LabelData.ofSigma (G := G) X hlabel).proj z (m+2) w, LabelData.proj_mem _ z (m+2) w, ?_⟩
  have h1 := LabelData.proj_d (LabelData.ofSigma (G := G) X hlabel) z (m+1) w
  have h2 : (equivariantD G (TopCat.of (Total X)) (m+2) (m+1)).hom w = y := hw
  change (equivariantD G (TopCat.of (Total X)) (m+2) (m+1)).hom _ = y
  rw [h1, h2]
  exact LabelData.proj_of_mem _ z (m+1) hy

theorem ofSigma_exists_vertex (z : ι) :
    ∃ y ∈ (LabelData.ofSigma (G := G) X hlabel).faceK z 0,
      (singEps (G := G) (TopCat.of (Total X))).hom y = (1 : ℚ) := by
  let σ : SingularSimplex (TopCat.of (Total X)) 0 :=
    TopCat.toSSetObj₀Equiv.symm (⟨z, TernaryPoly.SingularComponentAugmentation.componentPoint X z⟩ :
      Total X)
  have hσ : (LabelData.ofSigma (G := G) X hlabel).simpLab σ = z := by
    rw [ofSigma_simpLab_zero X hlabel]
    simp [σ, TopCat.toSSetObj₀Equiv]
  exact ⟨chainElement G (TopCat.of (Total X)) 0 σ,
    LabelData.chainElement_mem_faceK _ _ hσ, singEps_chainElement _ σ⟩

end Sigma

section Concrete

open TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open TernaryPoly.OrdinaryIncidence TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SymmetricSpaceBoundaryFaces TernaryPoly.SymmetricSpaceBoundaryMV
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.IntegralGL3Congruence

local instance lineLabelTopology : TopologicalSpace Line := ⊥
local instance planeLabelTopology : TopologicalSpace Plane := ⊥
local instance flagLabelTopology : TopologicalSpace Flag := ⊥
local instance lineLabelDiscrete : DiscreteTopology Line := ⟨rfl⟩
local instance planeLabelDiscrete : DiscreteTopology Plane := ⟨rfl⟩
local instance flagLabelDiscrete : DiscreteTopology Flag := ⟨rfl⟩

/-- Labels of the simplices of the line face sum. -/
def lineLabelData : LabelData principalSix (TopCat.of LineFaceSum) Line :=
  LabelData.ofSigma lineFamily lineLabel_equivariant

/-- Labels of the simplices of the plane face sum. -/
def planeLabelData : LabelData principalSix (TopCat.of PlaneFaceSum) Plane :=
  LabelData.ofSigma planeFamily planeLabel_equivariant

/-- Labels of the simplices of the flag (corner) face sum. -/
def flagLabelData : LabelData principalSix (TopCat.of CornerFaceSum) Flag :=
  LabelData.ofSigma flagFamily flagLabel_equivariant


/-! ### The line face sum -/

/-- The chains of the line face sum carried by the line `z`. -/
abbrev lineFaceK (z : Line) (m : ℕ) : Submodule ℚ (lineChains.X m) := lineLabelData.faceK z m

theorem lineFaceK_smul (g : principalSix) (z : Line) (m : ℕ) :
    lineFaceK (g • z) m = (lineFaceK z m).map ((lineChains.X m).ρ g) :=
  lineLabelData.faceK_smul g z m

theorem lineFaceK_subcomplex {z : Line} {m : ℕ} {x : lineChains.X (m+1)}
    (hx : x ∈ lineFaceK z (m+1)) : (lineChains.d (m+1) m).hom x ∈ lineFaceK z m :=
  lineLabelData.faceK_subcomplex hx

theorem lineFaceK_acyc0 (z : Line) {y : lineChains.X 0} (hy : y ∈ lineFaceK z 0)
    (h0 : (singEps (G := principalSix) (TopCat.of LineFaceSum)).hom y = 0) :
    ∃ x ∈ lineFaceK z 1, (lineChains.d 1 0).hom x = y :=
  ofSigma_acyc0 lineFamily lineLabel_equivariant z hy h0

theorem lineFaceK_acyc (z : Line) (m : ℕ) {y : lineChains.X (m+1)}
    (hy : y ∈ lineFaceK z (m+1)) (h0 : (lineChains.d (m+1) m).hom y = 0) :
    ∃ x ∈ lineFaceK z (m+2), (lineChains.d (m+2) (m+1)).hom x = y :=
  ofSigma_acyc lineFamily lineLabel_equivariant z m hy h0

theorem lineFaceK_exists_vertex (z : Line) :
    ∃ y ∈ lineFaceK z 0, (singEps (G := principalSix) (TopCat.of LineFaceSum)).hom y = (1 : ℚ) :=
  ofSigma_exists_vertex lineFamily lineLabel_equivariant z

theorem lineFaceK_cap (z : Line) (W : Rep.{0} ℚ principalSix) (a : ℕ) (b : chainRep principalSix (TopCat.of LineFaceSum) a ⟶ W)
    (q : ℕ) {x : chainRep principalSix (TopCat.of LineFaceSum) (a+q)} (hx : x ∈ lineFaceK z (a+q)) :
    (capE (TopCat.of LineFaceSum) W a q b).hom x ∈ tensorK W (lineFaceK z q) :=
  lineLabelData.faceK_cap z W a b q hx

theorem lineFaceK_diag (z : Line) (p q n : ℕ) (h : p + q = n) {x : lineChains.X n}
    (hx : x ∈ lineFaceK z n) :
    ((singDiagSystem (TopCat.of LineFaceSum)).Δ p q n h).hom x ∈ Submodule.span ℚ
      {t | ∃ (u : lineChains.X p) (v : lineChains.X q), u ∈ lineFaceK z p ∧ v ∈ lineFaceK z q ∧
        t = (u ⊗ₜ[ℚ] v : (chainRep principalSix (TopCat.of LineFaceSum) p ⊗ chainRep principalSix (TopCat.of LineFaceSum) q : Rep.{0} ℚ principalSix))} :=
  lineLabelData.faceK_diag z p q n h hx

/-! ### The plane face sum -/

/-- The chains of the plane face sum carried by the plane `z`. -/
abbrev planeFaceK (z : Plane) (m : ℕ) : Submodule ℚ (planeChains.X m) := planeLabelData.faceK z m

theorem planeFaceK_smul (g : principalSix) (z : Plane) (m : ℕ) :
    planeFaceK (g • z) m = (planeFaceK z m).map ((planeChains.X m).ρ g) :=
  planeLabelData.faceK_smul g z m

theorem planeFaceK_subcomplex {z : Plane} {m : ℕ} {x : planeChains.X (m+1)}
    (hx : x ∈ planeFaceK z (m+1)) : (planeChains.d (m+1) m).hom x ∈ planeFaceK z m :=
  planeLabelData.faceK_subcomplex hx

theorem planeFaceK_acyc0 (z : Plane) {y : planeChains.X 0} (hy : y ∈ planeFaceK z 0)
    (h0 : (singEps (G := principalSix) (TopCat.of PlaneFaceSum)).hom y = 0) :
    ∃ x ∈ planeFaceK z 1, (planeChains.d 1 0).hom x = y :=
  ofSigma_acyc0 planeFamily planeLabel_equivariant z hy h0

theorem planeFaceK_acyc (z : Plane) (m : ℕ) {y : planeChains.X (m+1)}
    (hy : y ∈ planeFaceK z (m+1)) (h0 : (planeChains.d (m+1) m).hom y = 0) :
    ∃ x ∈ planeFaceK z (m+2), (planeChains.d (m+2) (m+1)).hom x = y :=
  ofSigma_acyc planeFamily planeLabel_equivariant z m hy h0

theorem planeFaceK_exists_vertex (z : Plane) :
    ∃ y ∈ planeFaceK z 0, (singEps (G := principalSix) (TopCat.of PlaneFaceSum)).hom y = (1 : ℚ) :=
  ofSigma_exists_vertex planeFamily planeLabel_equivariant z

theorem planeFaceK_cap (z : Plane) (W : Rep.{0} ℚ principalSix) (a : ℕ) (b : chainRep principalSix (TopCat.of PlaneFaceSum) a ⟶ W)
    (q : ℕ) {x : chainRep principalSix (TopCat.of PlaneFaceSum) (a+q)} (hx : x ∈ planeFaceK z (a+q)) :
    (capE (TopCat.of PlaneFaceSum) W a q b).hom x ∈ tensorK W (planeFaceK z q) :=
  planeLabelData.faceK_cap z W a b q hx

theorem planeFaceK_diag (z : Plane) (p q n : ℕ) (h : p + q = n) {x : planeChains.X n}
    (hx : x ∈ planeFaceK z n) :
    ((singDiagSystem (TopCat.of PlaneFaceSum)).Δ p q n h).hom x ∈ Submodule.span ℚ
      {t | ∃ (u : planeChains.X p) (v : planeChains.X q), u ∈ planeFaceK z p ∧ v ∈ planeFaceK z q ∧
        t = (u ⊗ₜ[ℚ] v : (chainRep principalSix (TopCat.of PlaneFaceSum) p ⊗ chainRep principalSix (TopCat.of PlaneFaceSum) q : Rep.{0} ℚ principalSix))} :=
  planeLabelData.faceK_diag z p q n h hx

/-! ### The flag face sum -/

/-- The chains of the flag face sum carried by the flag `z`. -/
abbrev flagFaceK (z : Flag) (m : ℕ) : Submodule ℚ (flagChains.X m) := flagLabelData.faceK z m

theorem flagFaceK_smul (g : principalSix) (z : Flag) (m : ℕ) :
    flagFaceK (g • z) m = (flagFaceK z m).map ((flagChains.X m).ρ g) :=
  flagLabelData.faceK_smul g z m

theorem flagFaceK_subcomplex {z : Flag} {m : ℕ} {x : flagChains.X (m+1)}
    (hx : x ∈ flagFaceK z (m+1)) : (flagChains.d (m+1) m).hom x ∈ flagFaceK z m :=
  flagLabelData.faceK_subcomplex hx

theorem flagFaceK_acyc0 (z : Flag) {y : flagChains.X 0} (hy : y ∈ flagFaceK z 0)
    (h0 : (singEps (G := principalSix) (TopCat.of CornerFaceSum)).hom y = 0) :
    ∃ x ∈ flagFaceK z 1, (flagChains.d 1 0).hom x = y :=
  ofSigma_acyc0 flagFamily flagLabel_equivariant z hy h0

theorem flagFaceK_acyc (z : Flag) (m : ℕ) {y : flagChains.X (m+1)}
    (hy : y ∈ flagFaceK z (m+1)) (h0 : (flagChains.d (m+1) m).hom y = 0) :
    ∃ x ∈ flagFaceK z (m+2), (flagChains.d (m+2) (m+1)).hom x = y :=
  ofSigma_acyc flagFamily flagLabel_equivariant z m hy h0

theorem flagFaceK_exists_vertex (z : Flag) :
    ∃ y ∈ flagFaceK z 0, (singEps (G := principalSix) (TopCat.of CornerFaceSum)).hom y = (1 : ℚ) :=
  ofSigma_exists_vertex flagFamily flagLabel_equivariant z

theorem flagFaceK_cap (z : Flag) (W : Rep.{0} ℚ principalSix) (a : ℕ) (b : chainRep principalSix (TopCat.of CornerFaceSum) a ⟶ W)
    (q : ℕ) {x : chainRep principalSix (TopCat.of CornerFaceSum) (a+q)} (hx : x ∈ flagFaceK z (a+q)) :
    (capE (TopCat.of CornerFaceSum) W a q b).hom x ∈ tensorK W (flagFaceK z q) :=
  flagLabelData.faceK_cap z W a b q hx

theorem flagFaceK_diag (z : Flag) (p q n : ℕ) (h : p + q = n) {x : flagChains.X n}
    (hx : x ∈ flagFaceK z n) :
    ((singDiagSystem (TopCat.of CornerFaceSum)).Δ p q n h).hom x ∈ Submodule.span ℚ
      {t | ∃ (u : flagChains.X p) (v : flagChains.X q), u ∈ flagFaceK z p ∧ v ∈ flagFaceK z q ∧
        t = (u ⊗ₜ[ℚ] v : (chainRep principalSix (TopCat.of CornerFaceSum) p ⊗ chainRep principalSix (TopCat.of CornerFaceSum) q : Rep.{0} ℚ principalSix))} :=
  flagLabelData.faceK_diag z p q n h hx

/-! ### The chain maps flag → line, flag → plane -/

/-- **(K5)** `lineChainMap` sends the chains carried by the flag `f` to those carried by its line. -/
theorem lineChainMap_flagFaceK (f : Flag) (m : ℕ) {x : flagChains.X m} (hx : x ∈ flagFaceK f m) :
    (lineChainMap.f m).hom x ∈ lineFaceK (flagLine f) m :=
  flagLabelData.faceK_map lineLabelData lineFaceMap lineFaceMap_equivariant flagLine
    (fun x => lineFaceMap_label x) f m hx

/-- **(K5)** `planeChainMap` sends the chains carried by the flag `f` to those carried by its plane. -/
theorem planeChainMap_flagFaceK (f : Flag) (m : ℕ) {x : flagChains.X m} (hx : x ∈ flagFaceK f m) :
    (planeChainMap.f m).hom x ∈ planeFaceK (flagPlane f) m :=
  flagLabelData.faceK_map planeLabelData planeFaceMap planeFaceMap_equivariant flagPlane
    (fun x => planeFaceMap_label x) f m hx

end Concrete

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
