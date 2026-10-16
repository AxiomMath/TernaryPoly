module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.LocalDegree
public import TernaryPeriodPolynomials.Topology.Rational.Relative.Homotopy

@[expose] public section


/-!
# Relative classes of degree-three cycles and their homotopy invariance

Generic bookkeeping for the local-degree computation of Lemma 3.3 (G3, local half).

* `cls`: the homology class of a degree-three cycle of a chain complex of rational vector spaces,
  additive in the cycle (`cls_add`, `cls_zero`, `cls_neg`) and natural for chain maps (`cls_map`).
* `RelCycle S c`, `relCls S c h`: relative 3-cycles and their classes in the relative singular
  homology of `(X, S)`; `relCls_map` (naturality for maps of pairs), `relCls_homotopy`
  (homotopy invariance for homotopies of pairs into a contractible space).
* `chainMap_sing`, `sing_mem_range`, `relCycle_of_mem_range`: pushforward of singular generators and
  the criterion "the boundary lies in the subspace chains".
* `degRel`: the local degree of a relative 3-cycle of `(ℝ³, ℝ³ ∖ 0)`, i.e. its class under the
  library's `localTopIso 1 : H₃(ℝ³, ℝ³ ∖ 0) ≅ ℚ`; `degπ_eq_degRel` identifies the existing
  `Retract.LocalDegree.degπ` with it.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.RationalRelativeSingular
  TernaryPoly.RationalSingularAugmentation TernaryPoly.ContractibleSingularHomology
  TernaryPoly.EuclideanLocalHomology TernaryPoly.FreeActionLinearization TernaryPoly.RationalSphere

namespace TernaryPeriodPolynomials.Argument.Lemma33.Orient

section Generic

variable (K L : ChainComplex (ModuleCat.{0} ℚ) ℕ)

theorem next_three : (ComplexShape.down ℕ).next 3 = 2 :=
  (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 3 2 from rfl)

abbrev AbF := forget₂ (ModuleCat.{0} ℚ) Ab

/-- The homology class of a degree-three cycle. -/
def cls (x : AbF.obj (K.X 3)) (h : AbF.map (K.d 3 2) x = 0) : AbF.obj (K.homology 3) :=
  AbF.map (K.homologyπ 3) (K.cyclesMk x 2 next_three h)

theorem cls_congr (x y : AbF.obj (K.X 3)) (hx : AbF.map (K.d 3 2) x = 0) (hy : AbF.map (K.d 3 2) y = 0)
    (e : x = y) : cls K x hx = cls K y hy := by
  subst e; rfl

theorem iCycles_injective : Function.Injective (AbF.map (K.iCycles 3)) :=
  (Preadditive.mono_iff_injective (K.iCycles 3)).1 inferInstance

theorem cyclesMk_add' (x y : AbF.obj (K.X 3)) (hx : AbF.map (K.d 3 2) x = 0) (hy : AbF.map (K.d 3 2) y = 0)
    (hxy : AbF.map (K.d 3 2) (x + y) = 0) :
    K.cyclesMk (x + y) 2 next_three hxy = K.cyclesMk x 2 next_three hx + K.cyclesMk y 2 next_three hy := by
  apply iCycles_injective K
  rw [map_add, HomologicalComplex.i_cyclesMk, HomologicalComplex.i_cyclesMk, HomologicalComplex.i_cyclesMk]

theorem cls_add (x y : AbF.obj (K.X 3)) (hx : AbF.map (K.d 3 2) x = 0) (hy : AbF.map (K.d 3 2) y = 0)
    (hxy : AbF.map (K.d 3 2) (x + y) = 0) : cls K (x + y) hxy = cls K x hx + cls K y hy := by
  unfold cls
  rw [cyclesMk_add' K x y hx hy hxy, map_add]

theorem cls_zero (h : AbF.map (K.d 3 2) 0 = 0) : cls K 0 h = 0 := by
  have := cls_add K 0 0 h h (by simp)
  simp only [add_zero] at this
  exact left_eq_add.mp this

theorem cls_neg (x : AbF.obj (K.X 3)) (hx : AbF.map (K.d 3 2) x = 0) (hn : AbF.map (K.d 3 2) (-x) = 0) :
    cls K (-x) hn = - cls K x hx := by
  have h0 : AbF.map (K.d 3 2) (x + -x) = 0 := by simp
  have := cls_add K x (-x) hx hn h0
  rw [cls_congr K (x + -x) 0 h0 (by simp) (by simp), cls_zero] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem cls_map (φ : K ⟶ L) (x : AbF.obj (K.X 3)) (hx : AbF.map (K.d 3 2) x = 0)
    (hφx : AbF.map (L.d 3 2) (AbF.map (φ.f 3) x) = 0) :
    AbF.map (homologyMap φ 3) (cls K x hx) = cls L (AbF.map (φ.f 3) x) hφx := by
  unfold cls
  rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.forget₂_comp_apply]
  congr 1
  apply iCycles_injective L
  rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.cyclesMap_i,
    ConcreteCategory.forget₂_comp_apply, HomologicalComplex.i_cyclesMk, HomologicalComplex.i_cyclesMk]

end Generic

/-! ### Relative classes of a pair -/

section Pairs

variable {X : Type} [TopologicalSpace X]

/-- The projection of chains to relative chains. -/
abbrev relπ (S : Set X) : chains X ⟶ relativeChains S := cokernel.π (inclusion S)

/-- `c` is a relative 3-cycle of the pair `(X, S)`. -/
def RelCycle (S : Set X) (c : AbF.obj ((chains X).X 3)) : Prop :=
  AbF.map ((relativeChains S).d 3 2) (AbF.map ((relπ S).f 3) c) = 0

/-- The class of a relative 3-cycle in the relative homology. -/
def relCls (S : Set X) (c : AbF.obj ((chains X).X 3)) (h : RelCycle S c) :
    AbF.obj ((relativeChains S).homology 3) :=
  cls (relativeChains S) (AbF.map ((relπ S).f 3) c) h

theorem relCls_congr {X : Type} [TopologicalSpace X] (S : Set X) (c c' : AbF.obj ((chains X).X 3))
    (h : RelCycle S c) (h' : RelCycle S c') (e : c = c') : relCls S c h = relCls S c' h' := by
  subst e; rfl

theorem relπ_map {Y : Type} [TopologicalSpace Y] (f : C(X, Y)) (S : Set X) (T : Set Y)
    (hf : Set.MapsTo f S T) :
    relπ S ≫ relativeMap f S T hf = chainMap f ≫ relπ T := by
  unfold relπ relativeMap
  exact cokernel.π_desc _ _ _

theorem relCls_map {Y : Type} [TopologicalSpace Y] (f : C(X, Y)) (S : Set X) (T : Set Y)
    (hf : Set.MapsTo f S T) (c : AbF.obj ((chains X).X 3)) (h : RelCycle S c)
    (h' : RelCycle T (AbF.map ((chainMap f).f 3) c)) :
    AbF.map (homologyMap (relativeMap f S T hf) 3) (relCls S c h) =
      relCls T (AbF.map ((chainMap f).f 3) c) h' := by
  unfold relCls
  have h1 : AbF.map ((relativeMap f S T hf).f 3) (AbF.map ((relπ S).f 3) c) =
      AbF.map ((relπ T).f 3) (AbF.map ((chainMap f).f 3) c) := by
    exact congrArg (fun m => ModuleCat.Hom.hom m c) (congrArg (fun m => m.f 3) (relπ_map f S T hf))
  have := cls_map (relativeChains S) (relativeChains T) (relativeMap f S T hf) _ h (by rw [h1]; exact h')
  rw [this]
  exact cls_congr _ _ _ _ _ h1

end Pairs


/-! ### Singular simplices and maps -/

section Sing

open TernaryPeriodPolynomials.Argument.Lemma33

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem chainMap_sing (f : C(X, Y)) (n : ℕ) (σ : SingularSimplex (TopCat.of X) n) :
    ((chainMap f).f n).hom (sing (TopCat.of X) σ) =
      sing (TopCat.of Y) ((TopCat.toSSet.map (TopCat.ofHom f)).app _ σ) := by
  have h1 : (chainMap f).f n =
      (TernaryPoly.SingularCoverNaturality.underlyingMap (TopCat.ofHom f)).f n := rfl
  have hg1 := congrArg (fun m => m.hom (1 : ℚ))
    (TernaryPoly.SingularCoverNaturality.generator_map (TopCat.ofHom f) n σ)
  rw [h1]
  exact hg1


theorem sing_mem_range (S : Set X) {n : ℕ} (σ : SingularSimplex (TopCat.of X) n)
    (h : ∀ t, (TopCat.of X).toSSetObjEquiv _ σ t ∈ S) :
    sing (TopCat.of X) σ ∈ LinearMap.range ((RationalRelativeSingular.inclusion S).f n).hom := by
  let σ'' : SingularSimplex (TopCat.of S) n :=
    ((TopCat.of S).toSSetObjEquiv _).symm
      ⟨fun t => ⟨(TopCat.of X).toSSetObjEquiv _ σ t, h t⟩,
        Continuous.subtype_mk ((TopCat.of X).toSSetObjEquiv _ σ).continuous _⟩
  refine ⟨sing (TopCat.of S) σ'', ?_⟩
  have e := chainMap_sing (X := S) (Y := X) ⟨Subtype.val, continuous_subtype_val⟩ n σ''
  have hs : (TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)))).app _ σ'' = σ := by
    apply ((TopCat.of X).toSSetObjEquiv _).injective
    exact ContinuousMap.ext (fun t => rfl)
  rw [hs] at e
  exact e

theorem relCycle_of_mem_range (S : Set X) (c : (chains X).X 3)
    (h : ((chains X).d 3 2).hom c ∈ LinearMap.range ((RationalRelativeSingular.inclusion S).f 2).hom) : RelCycle S c := by
  obtain ⟨b, hb⟩ := h
  unfold RelCycle
  have hcomm := congrArg (fun m => m.hom c) ((relπ S).comm 3 2)
  change ((relativeChains S).d 3 2).hom (((relπ S).f 3).hom c) = ((relπ S).f 2).hom (((chains X).d 3 2).hom c) at hcomm
  change ((relativeChains S).d 3 2).hom (((relπ S).f 3).hom c) = 0
  rw [hcomm, ← hb]
  have := congrArg (fun m => m.f 2) (cokernel.condition (RationalRelativeSingular.inclusion S))
  exact congrArg (fun m => m.hom b) this

end Sing

section Homotopy

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem relCls_homotopy [ContractibleSpace Y] (f g : C(X, Y)) (S : Set X) (T : Set Y)
    (hf : Set.MapsTo f S T) (hg : Set.MapsTo g S T) (H : ContinuousMap.Homotopy f g)
    (hH : ∀ t x, x ∈ S → H (t, x) ∈ T) (c : AbF.obj ((chains X).X 3)) (h : RelCycle S c)
    (h1 : RelCycle T (AbF.map ((chainMap f).f 3) c)) (h2 : RelCycle T (AbF.map ((chainMap g).f 3) c)) :
    relCls T (AbF.map ((chainMap f).f 3) c) h1 = relCls T (AbF.map ((chainMap g).f 3) c) h2 := by
  rw [← relCls_map f S T hf c h h1, ← relCls_map g S T hg c h h2]
  have := relativeHomologyMap_eq_of_homotopy f g S T hf hg H hH 2 (by norm_num)
  rw [this]

end Homotopy

/-! ### The Euclidean local degree -/

section Euclid

/-- Three-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The local degree of a relative 3-cycle of the pair `(E³, E³ ∖ 0)` in `H₃(ℝ³, ℝ³ ∖ 0) ≅ ℚ`. -/
def degRel (c : AbF.obj ((chains E3).X 3)) (h : RelCycle (Punctured 3) c) : ℚ :=
  (localTopIso 1).hom.hom (relCls (Punctured 3) c h)

theorem RelCycle.map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (S : Set X)
    (T : Set Y) (hf : Set.MapsTo f S T) (c : AbF.obj ((chains X).X 3)) (h : RelCycle S c) :
    RelCycle T (AbF.map ((chainMap f).f 3) c) := by
  unfold RelCycle at h ⊢
  have h1 : AbF.map ((relπ T).f 3) (AbF.map ((chainMap f).f 3) c) =
      AbF.map ((relativeMap f S T hf).f 3) (AbF.map ((relπ S).f 3) c) :=
    (congrArg (fun m => ModuleCat.Hom.hom m c) (congrArg (fun m => m.f 3) (relπ_map f S T hf))).symm
  rw [h1]
  have h2 := congrArg (fun m => ModuleCat.Hom.hom m (((relπ S).f 3).hom c)) ((relativeMap f S T hf).comm 3 2)
  change ((relativeChains T).d 3 2).hom (((relativeMap f S T hf).f 3).hom (((relπ S).f 3).hom c)) =
    ((relativeMap f S T hf).f 2).hom (((relativeChains S).d 3 2).hom (((relπ S).f 3).hom c)) at h2
  change ((relativeChains T).d 3 2).hom (((relativeMap f S T hf).f 3).hom (((relπ S).f 3).hom c)) = 0
  rw [h2]
  have h3 : ((relativeChains S).d 3 2).hom (((relπ S).f 3).hom c) = 0 := h
  rw [h3, map_zero]

end Euclid



section Link

open TernaryPoly.SymmetricSpacePositive
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

theorem degπ_eq_degRel (c : (chains Space).X 3)
    (h : ((localChains 3).d 3 2).hom ((locRel.f 3).hom c) = 0) :
    degπ c h = degRel (AbF.map ((chainMap piR3).f 3) c) h := rfl

theorem degRel_congr (c c' : AbF.obj ((chains E3).X 3)) (h : RelCycle (Punctured 3) c)
    (h' : RelCycle (Punctured 3) c') (e : c = c') : degRel c h = degRel c' h' := by
  subst e; rfl

end Link

/-! ### Scalar multiples -/

section Scalar

/-- `cyclesMk` read in the module category. -/
def cmk (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (x : K.X 3) (hx : (K.d 3 2).hom x = 0) : K.cycles 3 :=
  K.cyclesMk x 2 next_three hx

theorem cmk_smul (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (q : ℚ) (x : K.X 3)
    (hx : (K.d 3 2).hom x = 0) (hqx : (K.d 3 2).hom (q • x) = 0) :
    cmk K (q • x) hqx = q • cmk K x hx := by
  apply iCycles_injective K
  have h1 : (K.iCycles 3).hom (cmk K (q • x) hqx) = q • x :=
    HomologicalComplex.i_cyclesMk K (q • x) 2 next_three hqx
  have h2 : (K.iCycles 3).hom (cmk K x hx) = x := HomologicalComplex.i_cyclesMk K x 2 next_three hx
  have h3 : (K.iCycles 3).hom (q • cmk K x hx) = q • x := by rw [map_smul, h2]
  exact h1.trans h3.symm

/-- The class of a degree-three cycle, in the module category. -/
def clsM (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (x : K.X 3) (hx : (K.d 3 2).hom x = 0) :
    K.homology 3 := (K.homologyπ 3).hom (cmk K x hx)

theorem clsM_smul (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (q : ℚ) (x : K.X 3)
    (hx : (K.d 3 2).hom x = 0) (hqx : (K.d 3 2).hom (q • x) = 0) :
    clsM K (q • x) hqx = q • clsM K x hx := by
  unfold clsM
  rw [cmk_smul K q x hx hqx, map_smul]

theorem clsM_congr (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (x y : K.X 3) (hx : (K.d 3 2).hom x = 0)
    (hy : (K.d 3 2).hom y = 0) (e : x = y) : clsM K x hx = clsM K y hy := by
  subst e; rfl

end Scalar

section DegScalar

theorem degRel_of_relπ_eq (c c' : AbF.obj ((chains E3).X 3)) (h : RelCycle (Punctured 3) c)
    (h' : RelCycle (Punctured 3) c') (q : ℚ)
    (e : ((relπ (Punctured 3)).f 3).hom c = q • ((relπ (Punctured 3)).f 3).hom c') :
    degRel c h = q * degRel c' h' := by
  have hc : ((relativeChains (Punctured 3)).d 3 2).hom (((relπ (Punctured 3)).f 3).hom c) = 0 := h
  have hc' : ((relativeChains (Punctured 3)).d 3 2).hom (((relπ (Punctured 3)).f 3).hom c') = 0 := h'
  have hq : ((relativeChains (Punctured 3)).d 3 2).hom (q • ((relπ (Punctured 3)).f 3).hom c') = 0 := by
    rw [← e]; exact hc
  have h1 : clsM (relativeChains (Punctured 3)) (((relπ (Punctured 3)).f 3).hom c) hc =
      q • clsM (relativeChains (Punctured 3)) (((relπ (Punctured 3)).f 3).hom c') hc' := by
    rw [clsM_congr _ _ _ hc hq e, clsM_smul]
  change (localTopIso 1).hom.hom (clsM (relativeChains (Punctured 3))
      (((relπ (Punctured 3)).f 3).hom c) hc) =
    q * (localTopIso 1).hom.hom (clsM (relativeChains (Punctured 3))
      (((relπ (Punctured 3)).f 3).hom c') hc')
  rw [h1, map_smul, smul_eq_mul]

end DegScalar

end TernaryPeriodPolynomials.Argument.Lemma33.Orient
