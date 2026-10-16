module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.OrdinaryCohomology

@[expose] public section


open GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryFiniteness.ProductCohomology

noncomputable section

variable {G I : Type} [Group G] {V : I → Type}
  [∀ index, AddCommGroup (V index)] [∀ index, Module ℂ (V index)]

def productAction (actions : ∀ index, Representation ℂ G (V index)) :
    Representation ℂ G (∀ index, V index) where
  toFun element := LinearMap.pi (fun index =>
    (actions index element).comp (LinearMap.proj index))
  map_one' := by ext function index; simp
  map_mul' left right := by ext function index; simp [map_mul]

def componentCochain (level : Subgroup G) (actions : ∀ index, Representation ℂ G (V index))
    (index : I) (degree : ℕ) :
    cochains level (productAction actions) degree →ₗ[ℂ] cochains level (actions index) degree where
  toFun cochain := ⟨fun vertices => cochain.val vertices index, by
    intro element vertices
    exact congrFun (cochain.property element vertices) index⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def componentCycles (level : Subgroup G) (actions : ∀ index, Representation ℂ G (V index))
    (index : I) : cocycles level (productAction actions) →ₗ[ℂ] cocycles level (actions index) where
  toFun cocycle := ⟨componentCochain level actions index 2 cocycle.val, by
    funext vertices
    exact congrFun (congrFun cocycle.property vertices) index⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem component_boundary (level : Subgroup G) (actions : ∀ index, Representation ℂ G (V index))
    (index : I) (cochain : cochains level (productAction actions) 1) :
    componentCycles level actions index (boundaryMap level (productAction actions) cochain) =
      boundaryMap level (actions index) (componentCochain level actions index 1 cochain) := rfl

def componentClass (level : Subgroup G) (actions : ∀ index, Representation ℂ G (V index))
    (index : I) : H2 level (productAction actions) →ₗ[ℂ] H2 level (actions index) :=
  (LinearMap.range (boundaryMap level (productAction actions))).mapQ
    (LinearMap.range (boundaryMap level (actions index))) (componentCycles level actions index) (by
      rintro _ ⟨cochain, rfl⟩
      exact ⟨componentCochain level actions index 1 cochain, rfl⟩)

def productMap (level : Subgroup G) (actions : ∀ index, Representation ℂ G (V index)) :
    H2 level (productAction actions) →ₗ[ℂ] ∀ index, H2 level (actions index) :=
  LinearMap.pi (componentClass level actions)

def assembleCochain (level : Subgroup G) (actions : ∀ index, Representation ℂ G (V index))
    (degree : ℕ) (cochainsByIndex : ∀ index, cochains level (actions index) degree) :
    cochains level (productAction actions) degree :=
  ⟨fun vertices index => (cochainsByIndex index).val vertices, by
    intro element vertices
    funext index
    exact (cochainsByIndex index).property element vertices⟩

def assembleCycles (level : Subgroup G) (actions : ∀ index, Representation ℂ G (V index))
    (cyclesByIndex : ∀ index, cocycles level (actions index)) :
    cocycles level (productAction actions) :=
  ⟨assembleCochain level actions 2 (fun index => (cyclesByIndex index).val), by
    funext vertices index
    exact congrFun (cyclesByIndex index).property vertices⟩

theorem productMap_injective (level : Subgroup G) (actions : ∀ index, Representation ℂ G (V index)) :
    Function.Injective (productMap level actions) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro cohomologyClass vanishes
  change cohomologyClass = 0
  induction cohomologyClass using Submodule.Quotient.induction_on with
  | _ cocycle =>
    have component_vanishes (index : I) :
        classOf level (actions index) (componentCycles level actions index cocycle) = 0 :=
      congrFun vanishes index
    have component_boundary_exists (index : I) :
        ∃ cochain, boundaryMap level (actions index) cochain = componentCycles level actions index cocycle := by
      have equality := component_vanishes index
      change Submodule.Quotient.mk _ = 0 at equality
      exact (Submodule.Quotient.mk_eq_zero _).mp equality
    choose cochainsByIndex boundary using component_boundary_exists
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨assembleCochain level actions 1 cochainsByIndex, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext vertices index
    exact congrArg (fun cycle => cycle.val.val vertices) (boundary index)

theorem productMap_surjective (level : Subgroup G) (actions : ∀ index, Representation ℂ G (V index)) :
    Function.Surjective (productMap level actions) := by
  intro classes
  have representatives_exist (index : I) : ∃ cocycle, classOf level (actions index) cocycle = classes index :=
    Submodule.mkQ_surjective _ (classes index)
  choose cyclesByIndex represents using representatives_exist
  refine ⟨classOf level (productAction actions) (assembleCycles level actions cyclesByIndex), ?_⟩
  funext index
  exact represents index

def cohomologyEquiv (level : Subgroup G) (actions : ∀ index, Representation ℂ G (V index)) :
    H2 level (productAction actions) ≃ₗ[ℂ] ∀ index, H2 level (actions index) :=
  LinearEquiv.ofBijective (productMap level actions)
    ⟨productMap_injective level actions, productMap_surjective level actions⟩

end

end TernaryPeriodPolynomials.BoundaryFiniteness.ProductCohomology
