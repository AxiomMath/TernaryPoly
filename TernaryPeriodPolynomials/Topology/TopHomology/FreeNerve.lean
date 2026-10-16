module

public import Mathlib.RepresentationTheory.Homological.Resolution
public import TernaryPeriodPolynomials.Topology.TopHomology.PermutationHom

@[expose] public section


/-!
# Projective resolutions of permutation modules by free simplicial sets

For a group `Γ` acting freely on a set `V` (with a base point) and acting on a set `Z`, the simplicial
`Γ`-set `[n] ↦ V^{n+1} × Z` (`prodNerve`) has an extra degeneracy over `Z`, so the alternating face map
complex of its linearization (`prodComplex`, `[n] ↦ ℚ[V^{n+1} × Z]`) is a projective resolution of the
permutation representation `ℚ[Z]` (`prodResolution`); this is Mathlib's standard resolution
`Rep.standardResolution` with an extra permutation factor.  A `Γ`-map `α : Z → Z'` induces a chain map
(`prodMapHom`) over `ℚ[α]` (`ofMulActionMap`).  Morphisms from `prodComplex` into a trivial representation
are invariant functions on `V^{k+1} × Z` (`homFun`, `homOfFun`), and the differential and the chain maps
act by the alternating sum of faces (`homFun_comp_d`) and by precomposition (`homFun_comp_map`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits Simplicial SimplicialObject AlgebraicTopology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.TopHomology

section Nerve

variable (Γ : Type) [Group Γ] (V Z : Type) [MulAction Γ V] [MulAction Γ Z]

/-- The simplicial `Γ`-set `[n] ↦ V^{n+1} × Z` (diagonal action). -/
def prodNerve : SimplicialObject (Action (Type) Γ) where
  obj n := Action.ofMulAction Γ ((Fin (n.unop.len + 1) → V) × Z)
  map f := { hom := ↾fun x => (x.1 ∘ f.unop.toOrderHom, x.2), comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The projection `V^{n+1} × Z → Z`. -/
def prodNerveAug : SimplicialObject.Augmented (Type) :=
  SimplicialObject.augment (prodNerve Γ V Z ⋙ forget _) Z (↾fun x => x.2)
    (fun _ _ _ => rfl)

variable {Γ V Z}

theorem cons_comp_succAbove_zero {n : ℕ} (v₀ : V) (x : Fin (n + 1) → V) :
    (Fin.cons v₀ x : Fin (n + 2) → V) ∘ (0 : Fin (n + 2)).succAbove = x := by
  funext j
  simp

theorem cons_comp_succAbove_succ {n : ℕ} (v₀ : V) (x : Fin (n + 2) → V) (i : Fin (n + 2)) :
    (Fin.cons v₀ x : Fin (n + 3) → V) ∘ i.succ.succAbove = Fin.cons v₀ (x ∘ i.succAbove) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp

theorem cons_comp_predAbove_succ {n : ℕ} (v₀ : V) (x : Fin (n + 1) → V) (i : Fin (n + 1)) :
    (Fin.cons v₀ x : Fin (n + 2) → V) ∘ i.succ.predAbove =
      Fin.cons v₀ (x ∘ i.predAbove) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp

/-- Extra degeneracy given a base point of `V`. -/
def prodExtraDegeneracy (v₀ : V) :
    SimplicialObject.Augmented.ExtraDegeneracy (prodNerveAug Γ V Z) where
  s' := ↾fun z => (fun _ => v₀, z)
  s n := ↾fun x => (Fin.cons v₀ x.1, x.2)
  s'_comp_ε := rfl
  s₀_comp_δ₁ := by
    ext ⟨x, z⟩
    change (_, z) = (_, z)
    congr 1
    funext i
    fin_cases i
    rfl
  s_comp_δ₀ := by
    intro n
    ext ⟨x, z⟩
    exact Prod.ext (cons_comp_succAbove_zero v₀ x) rfl
  s_comp_δ := by
    intro n i
    ext ⟨x, z⟩
    exact Prod.ext (cons_comp_succAbove_succ v₀ x i) rfl
  s_comp_σ := by
    intro n i
    ext ⟨x, z⟩
    exact Prod.ext (cons_comp_predAbove_succ v₀ x i) rfl

end Nerve

section Resolution

variable (Γ : Type) [Group Γ] (V Z : Type) [MulAction Γ V] [MulAction Γ Z]

/-- The linearized complex `[n] ↦ ℚ[V^{n+1} × Z]`. -/
def prodComplex : ChainComplex (Rep.{0} ℚ Γ) ℕ :=
  (alternatingFaceMapComplex (Rep.{0} ℚ Γ)).obj (prodNerve Γ V Z ⋙ Rep.linearization ℚ Γ)

/-- The projection of the zeroth term onto `Z`, as a morphism of `Γ`-sets. -/
def augAction : Action.ofMulAction Γ ((Fin 1 → V) × Z) ⟶ Action.ofMulAction Γ Z :=
  ⟨↾fun x => x.2, fun _ => rfl⟩

/-- The augmentation `ℚ[V × Z] ⟶ ℚ[Z]`. -/
def prodEps : (prodComplex Γ V Z).X 0 ⟶ Rep.ofMulAction ℚ Γ Z :=
  (Rep.linearization ℚ Γ).map (augAction Γ V Z) ≫ (Rep.linearizationOfMulActionIso ℚ Γ Z).hom

/-- The complex of `ℚ`-modules underlying `prodComplex`. -/
def prodForget : ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  ((forget₂ (Rep.{0} ℚ Γ) (ModuleCat.{0} ℚ)).mapHomologicalComplex _).obj (prodComplex Γ V Z)

/-- The augmented simplicial `ℚ`-module. -/
def prodAugModule : SimplicialObject.Augmented (ModuleCat.{0} ℚ) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.monoidAlgebraFree ℚ)).obj
    (prodNerveAug Γ V Z)

theorem prodForgetIso_d (n : ℕ) :
    (AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj (prodAugModule Γ V Z))).d
        (n + 1) n = (prodForget Γ V Z).d (n + 1) n := by
  have h1 := AlternatingFaceMapComplex.obj_d_eq
    (SimplicialObject.Augmented.drop.obj (prodAugModule Γ V Z)) n
  have h2 := AlternatingFaceMapComplex.obj_d_eq (prodNerve Γ V Z ⋙ Rep.linearization ℚ Γ) n
  have h4 := congrArg (forget₂ (Rep.{0} ℚ Γ) (ModuleCat.{0} ℚ)).map h2
  refine h1.trans (Eq.trans ?_ h4.symm)
  rw [Functor.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Functor.map_zsmul]
  rfl

/-- The augmented-simplicial complex is the underlying complex of `prodComplex`. -/
def prodForgetIso : AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj (prodAugModule Γ V Z)) ≅
    prodForget Γ V Z :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    have h : j + 1 = i := hij
    subst h
    exact (Category.id_comp _).trans ((prodForgetIso_d Γ V Z j).symm.trans (Category.comp_id _).symm))

variable {Γ V Z}

/-- Homotopy equivalence of the underlying complex with `ℚ[Z]` in degree zero. -/
def prodHomotopyEquiv (v₀ : V) : HomotopyEquiv (prodForget Γ V Z)
    ((ChainComplex.single₀ (ModuleCat.{0} ℚ)).obj ((forget₂ (Rep.{0} ℚ Γ) (ModuleCat.{0} ℚ)).obj
      (Rep.ofMulAction ℚ Γ Z))) :=
  (HomotopyEquiv.ofIso (prodForgetIso Γ V Z).symm).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
      ((prodExtraDegeneracy (Z := Z) (Γ := Γ) v₀).map (ModuleCat.monoidAlgebraFree ℚ)))

end Resolution

section Resolution2

variable (Γ : Type) [Group Γ] (V Z : Type) [MulAction Γ V] [MulAction Γ Z]

theorem prodHomotopyEquiv_f_zero (v₀ : V) :
    (prodHomotopyEquiv (Γ := Γ) (Z := Z) v₀).hom.f 0 =
      (forget₂ (Rep.{0} ℚ Γ) (ModuleCat.{0} ℚ)).map (prodEps Γ V Z) := by
  refine ModuleCat.hom_ext <| MonoidAlgebra.lhom_ext' fun (x : (Fin 1 → V) × Z) =>
    LinearMap.ext_ring ?_
  rfl

theorem prodComplex_d_comp_eps (v₀ : V) : (prodComplex Γ V Z).d 1 0 ≫ prodEps Γ V Z = 0 := by
  ext : 3
  have : (prodForget Γ V Z).d 1 0 ≫ (forget₂ (Rep.{0} ℚ Γ) (ModuleCat.{0} ℚ)).map (prodEps Γ V Z) =
      0 := by
    have h := (prodHomotopyEquiv (Γ := Γ) (Z := Z) v₀).hom.comm 1 0
    rw [prodHomotopyEquiv_f_zero] at h
    refine h.symm.trans ?_
    exact comp_zero
  exact LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.mp this) _

/-- The augmentation as a chain map. -/
def prodEpsToSingle (v₀ : V) : prodComplex Γ V Z ⟶
    (ChainComplex.single₀ (Rep.{0} ℚ Γ)).obj (Rep.ofMulAction ℚ Γ Z) :=
  ((prodComplex Γ V Z).toSingle₀Equiv _).symm ⟨prodEps Γ V Z, prodComplex_d_comp_eps Γ V Z v₀⟩

theorem prodEpsToSingle_comp_eq (v₀ : V) :
    ((forget₂ (Rep.{0} ℚ Γ) (ModuleCat.{0} ℚ)).mapHomologicalComplex _).map
        (prodEpsToSingle Γ V Z v₀) ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _ =
      (prodHomotopyEquiv (Γ := Γ) (Z := Z) v₀).hom := by
  dsimp
  ext1
  simpa using! (prodHomotopyEquiv_f_zero Γ V Z v₀).symm

theorem quasiIso_forget_prodEpsToSingle (v₀ : V) :
    QuasiIso (((forget₂ (Rep.{0} ℚ Γ) (ModuleCat.{0} ℚ)).mapHomologicalComplex _).map
      (prodEpsToSingle Γ V Z v₀)) := by
  have h : QuasiIso (prodHomotopyEquiv (Γ := Γ) (Z := Z) v₀).hom := inferInstance
  rw [← prodEpsToSingle_comp_eq Γ V Z v₀] at h
  exact quasiIso_of_comp_right (hφφ' := h)

instance (v₀ : V) : QuasiIso (prodEpsToSingle Γ V Z v₀) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (Rep.{0} ℚ Γ) (ModuleCat.{0} ℚ))]
  apply quasiIso_forget_prodEpsToSingle

end Resolution2

section Final

variable (Γ : Type) [Group Γ] (V Z : Type) [MulAction Γ V] [MulAction Γ Z]

/-- The permutation module of a `Γ`-map. -/
def ofMulActionMap {Z' : Type} [MulAction Γ Z'] (α : Z → Z') (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z) :
    Rep.ofMulAction ℚ Γ Z ⟶ Rep.ofMulAction ℚ Γ Z' :=
  ofMulActionLift Z (Rep.ofMulAction ℚ Γ Z') (fun z => MonoidAlgebra.single (α z) 1) (fun γ z => by
    simp [hα])

theorem ofMulActionMap_single {Z' : Type} [MulAction Γ Z'] (α : Z → Z')
    (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z) (z : Z) :
    (ofMulActionMap Γ Z α hα).hom (MonoidAlgebra.single z 1) = MonoidAlgebra.single (α z) 1 :=
  ofMulActionLift_single Z _ _ _ z

/-- The simplicial map induced by a map of the `Z` factors. -/
def prodNerveMap {Z' : Type} [MulAction Γ Z'] (α : Z → Z') (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z) :
    prodNerve Γ V Z ⟶ prodNerve Γ V Z' where
  app n := ⟨↾fun x => (x.1, α x.2), fun γ => by
    ext ⟨x, z⟩
    exact Prod.ext rfl (hα γ z)⟩
  naturality _ _ _ := rfl

/-- The chain map induced by a map of the `Z` factors. -/
def prodMapHom {Z' : Type} [MulAction Γ Z'] (α : Z → Z') (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z) :
    prodComplex Γ V Z ⟶ prodComplex Γ V Z' :=
  (alternatingFaceMapComplex (Rep.{0} ℚ Γ)).map
    (Functor.whiskerRight (prodNerveMap Γ V Z α hα) (Rep.linearization ℚ Γ))

theorem prodMapHom_f_single {Z' : Type} [MulAction Γ Z'] (α : Z → Z')
    (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z) (k : ℕ) (x : Fin (k + 1) → V) (z : Z) :
    ((prodMapHom Γ V Z α hα).f k).hom (MonoidAlgebra.single (x, z) 1) =
      MonoidAlgebra.single (x, α z) 1 := by
  simp only [prodMapHom, prodNerveMap, alternatingFaceMapComplex_map_f, Functor.whiskerRight_app]
  exact Representation.linearizeMap_single _ _ _

theorem prodEps_single (x : Fin 1 → V) (z : Z) :
    (prodEps Γ V Z).hom (MonoidAlgebra.single (x, z) 1) = MonoidAlgebra.single z 1 := by
  simp only [prodEps, augAction]
  exact Representation.linearizeMap_single _ _ _

theorem prodMapHom_f_zero_comp_eps {Z' : Type} [MulAction Γ Z'] (α : Z → Z')
    (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z) :
    (prodMapHom Γ V Z α hα).f 0 ≫ prodEps Γ V Z' = prodEps Γ V Z ≫ ofMulActionMap Γ Z α hα := by
  refine hom_ext_single ((Fin 1 → V) × Z) (Rep.ofMulAction ℚ Γ Z') (fun y => ?_)
  obtain ⟨x, z⟩ := y
  have h1 := prodMapHom_f_single Γ V Z α hα 0 x z
  have h2 := prodEps_single Γ V Z' x (α z)
  have h3 := prodEps_single Γ V Z x z
  have h4 := ofMulActionMap_single Γ Z α hα z
  change (prodEps Γ V Z').hom (((prodMapHom Γ V Z α hα).f 0).hom (MonoidAlgebra.single (x, z) 1)) =
    (ofMulActionMap Γ Z α hα).hom ((prodEps Γ V Z).hom (MonoidAlgebra.single (x, z) 1))
  exact ((congrArg (prodEps Γ V Z').hom h1).trans h2).trans
    (h4.symm.trans (congrArg (ofMulActionMap Γ Z α hα).hom h3.symm))

/-- The projective resolution `[n] ↦ ℚ[V^{n+1} × Z]` of `ℚ[Z]`. -/
abbrev prodResolution (v₀ : V) (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) :
    ProjectiveResolution (Rep.ofMulAction ℚ Γ Z) where
  complex := prodComplex Γ V Z
  projective n := projective_ofMulAction ((Fin (n + 1) → V) × Z) (fun γ y h =>
    hfree γ (y.1 0) (congrFun (congrArg Prod.fst h) 0))
  π := prodEpsToSingle Γ V Z v₀
  quasiIso := inferInstance

end Final

section HomLayer

variable (Γ : Type) [Group Γ] (V Z : Type) [MulAction Γ V] [MulAction Γ Z]

/-- The `i`-th face of a simplex. -/
def face {k : ℕ} (i : Fin (k + 2)) (y : (Fin (k + 2) → V) × Z) : (Fin (k + 1) → V) × Z :=
  (fun j => y.1 (i.succAbove j), y.2)

theorem hom_sum_single {H : Type} [MulAction Γ H] {A : Rep.{0} ℚ Γ} (c : Rep.ofMulAction ℚ Γ H ⟶ A)
    {n : ℕ} (r : Fin n → ℚ) (h : Fin n → H) :
    c.hom (∑ i, r i • MonoidAlgebra.single (h i) 1) =
      ∑ i, r i • c.hom (MonoidAlgebra.single (h i) 1) := by
  simp only [map_sum, map_smul]

theorem prodComplex_d_comp_eq (k : ℕ) {A : Rep.{0} ℚ Γ} (c : (prodComplex Γ V Z).X k ⟶ A) :
    (prodComplex Γ V Z).d (k + 1) k ≫ c =
      ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (SimplicialObject.δ (prodNerve Γ V Z ⋙ Rep.linearization ℚ Γ) i ≫ c) := by
  have h := AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq
    (prodNerve Γ V Z ⋙ Rep.linearization ℚ Γ) k
  have h' := congrArg (fun m => m ≫ c) h
  refine h'.trans ((Preadditive.sum_comp _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_))
  exact Preadditive.zsmul_comp (n := (-1 : ℤ) ^ (i : ℕ)) ..

theorem delta_single (k : ℕ) (i : Fin (k + 2)) (y : (Fin (k + 2) → V) × Z) :
    (SimplicialObject.δ (prodNerve Γ V Z ⋙ Rep.linearization ℚ Γ) i).hom (MonoidAlgebra.single y 1) =
      MonoidAlgebra.single (face V Z i y) 1 :=
  Representation.linearizeMap_single _ _ _

end HomLayer

section HomFunLayer

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z]
  {W : Type} [AddCommGroup W] [Module ℚ W]

/-- The function `y ↦ c(y)` attached to a morphism into a trivial representation. -/
def homFun {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ Rep.trivial ℚ Γ W) :
    (Fin (k + 1) → V) × Z → W :=
  fun y => c.hom (MonoidAlgebra.single y 1)

theorem homFun_invariant {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ Rep.trivial ℚ Γ W) (γ : Γ)
    (y : (Fin (k + 1) → V) × Z) : homFun c (γ • y) = homFun c y :=
  (homFunEquiv ((Fin (k + 1) → V) × Z) (Rep.trivial ℚ Γ W) c).2 γ y

theorem homFun_injective {k : ℕ} {c c' : (prodComplex Γ V Z).X k ⟶ Rep.trivial ℚ Γ W}
    (h : homFun c = homFun c') : c = c' :=
  hom_ext_single ((Fin (k + 1) → V) × Z) (Rep.trivial ℚ Γ W) (fun y => congrFun h y)

/-- The morphism attached to an invariant function. -/
def homOfFun {k : ℕ} (F : (Fin (k + 1) → V) × Z → W) (hF : ∀ (γ : Γ) y, F (γ • y) = F y) :
    (prodComplex Γ V Z).X k ⟶ Rep.trivial ℚ Γ W :=
  ofMulActionLift ((Fin (k + 1) → V) × Z) (Rep.trivial ℚ Γ W) F hF

theorem homFun_homOfFun {k : ℕ} (F : (Fin (k + 1) → V) × Z → W) (hF : ∀ (γ : Γ) y, F (γ • y) = F y) :
    homFun (homOfFun F hF) = F := by
  funext y
  exact ofMulActionLift_single ((Fin (k + 1) → V) × Z) (Rep.trivial ℚ Γ W) F hF y

theorem homOfFun_homFun {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ Rep.trivial ℚ Γ W) :
    homOfFun (homFun c) (homFun_invariant c) = c :=
  homFun_injective (homFun_homOfFun _ _)

theorem homFun_add {k : ℕ} (c c' : (prodComplex Γ V Z).X k ⟶ Rep.trivial ℚ Γ W) :
    homFun (c + c') = homFun c + homFun c' := rfl

theorem homFun_neg {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ Rep.trivial ℚ Γ W) :
    homFun (-c) = -homFun c := rfl

theorem homFun_sub {k : ℕ} (c c' : (prodComplex Γ V Z).X k ⟶ Rep.trivial ℚ Γ W) :
    homFun (c - c') = homFun c - homFun c' := rfl

theorem homFun_zero {k : ℕ} : homFun (0 : (prodComplex Γ V Z).X k ⟶ Rep.trivial ℚ Γ W) = 0 := rfl

theorem homFun_comp_d {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ Rep.trivial ℚ Γ W)
    (y : (Fin (k + 2) → V) × Z) :
    homFun ((prodComplex Γ V Z).d (k + 1) k ≫ c) y =
      ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • homFun c (face V Z i y) := by
  have h := prodComplex_d_comp_eq Γ V Z k c
  change ((prodComplex Γ V Z).d (k + 1) k ≫ c).hom (MonoidAlgebra.single y 1) = _
  rw [h]
  erw [Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [Rep.zsmul_hom]
  exact congrArg (fun w => ((-1 : ℤ) ^ (i : ℕ)) • c.hom w) (delta_single Γ V Z k i y)

theorem homFun_comp_map {Z' : Type} [MulAction Γ Z'] (α : Z → Z')
    (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z) {k : ℕ}
    (c : (prodComplex Γ V Z').X k ⟶ Rep.trivial ℚ Γ W) (x : Fin (k + 1) → V) (z : Z) :
    homFun ((prodMapHom Γ V Z α hα).f k ≫ c) (x, z) = homFun c (x, α z) := by
  change c.hom (((prodMapHom Γ V Z α hα).f k).hom (MonoidAlgebra.single (x, z) 1)) = _
  rw [prodMapHom_f_single]
  rfl

end HomFunLayer

end TernaryPeriodPolynomials.Argument.TopHomology
