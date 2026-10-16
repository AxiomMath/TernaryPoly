module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.CentralSignCohomology
open CategoryTheory CategoryTheory.Limits

variable {G : Type} [Group G]

/-- The genuine equivariant endomorphism supplied by a central group element. -/
def centralHom (z : G) (hz : ∀ g, z*g = g*z) (A : Rep ℚ G) : A ⟶ A :=
  Rep.ofHom ⟨A.ρ z,fun g => by
    change A.ρ z * A.ρ g = A.ρ g * A.ρ z
    rw [← map_mul,← map_mul,hz g]⟩

theorem centralHom_natural (z : G) (hz : ∀ g, z*g = g*z)
    {A B : Rep ℚ G} (f : A ⟶ B) : centralHom z hz A ≫ f = f ≫ centralHom z hz B := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact f.hom.isIntertwining' z

/-- The central action is a genuine chain endomorphism of every complex of representations. -/
def centralChain (z : G) (hz : ∀ g, z*g = g*z) (P : ChainComplex (Rep ℚ G) ℕ) : P ⟶ P where
  f n := centralHom z hz (P.X n)
  comm' i j _ := centralHom_natural z hz (P.d i j)

/-- Central multiplication lifts the identity on the trivial module. -/
theorem centralChain_augmentation (z : G) (hz : ∀ g, z*g = g*z)
    (P : ProjectiveResolution (Rep.trivial ℚ G ℚ)) : centralChain z hz P.complex ≫ P.π = P.π := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have h := LinearMap.congr_fun ((P.π.f 0).hom.isIntertwining' z) v
    exact h
  | succ n => simp [HomologicalComplex.comp_f]

/-- The comparison theorem supplies an actual chain homotopy in every degree. -/
def centralChain_homotopy (z : G) (hz : ∀ g, z*g = g*z)
    (P : ProjectiveResolution (Rep.trivial ℚ G ℚ)) :
    Homotopy (centralChain z hz P.complex) (𝟙 P.complex) := by
  apply ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial ℚ G ℚ))
  · simpa using centralChain_augmentation z hz P
  · simp

/-- Contravariant application of Hom(-,A) to a genuine chain map. -/
def yonedaPullback (A : Rep ℚ G) {P : ChainComplex (Rep ℚ G) ℕ} (f : P ⟶ P) :
    P.linearYonedaObj ℚ A ⟶ P.linearYonedaObj ℚ A :=
  (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    ((((linearYoneda ℚ (Rep ℚ G)).obj A).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).map f).op

theorem yonedaPullback_apply (A : Rep ℚ G) {P : ChainComplex (Rep ℚ G) ℕ}
    (f : P ⟶ P) (n : ℕ) (v : P.X n ⟶ A) :
    (yonedaPullback A f).f n v = f.f n ≫ v := rfl

@[simp] theorem yonedaPullback_id (A : Rep ℚ G) (P : ChainComplex (Rep ℚ G) ℕ) :
    yonedaPullback A (𝟙 P) = 𝟙 (P.linearYonedaObj ℚ A) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change (𝟙 (P.X n)) ≫ v = v
  exact Category.id_comp v

/-- In Hom(-,A), a central element acting by minus identity induces minus identity. -/
theorem yonedaPullback_central (A : Rep ℚ G) (z : G) (hz : ∀ g, z*g = g*z)
    (hA : ∀ v : A, A.ρ z v = -v) (P : ChainComplex (Rep ℚ G) ℕ) :
    yonedaPullback A (centralChain z hz P) = -𝟙 (P.linearYonedaObj ℚ A) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change f.hom ((P.X n).ρ z v) = -f.hom v
  have hf := LinearMap.congr_fun (f.hom.isIntertwining' z) v
  exact hf.trans (hA (f.hom v))

/-- The sign action contracts every cohomology group of the genuine Hom complex. -/
theorem isZero_yoneda_homology (A : Rep ℚ G) (z : G) (hz : ∀ g, z*g = g*z)
    (hA : ∀ v : A, A.ρ z v = -v) (P : ProjectiveResolution (Rep.trivial ℚ G ℚ)) (n : ℕ) :
    IsZero ((P.complex.linearYonedaObj ℚ A).homology n) := by
  have h := (((linearYoneda ℚ (Rep ℚ G)).obj A).rightOp.mapHomotopy
    (centralChain_homotopy z hz P)).unop
  change Homotopy (yonedaPullback A (centralChain z hz P.complex))
    (yonedaPullback A (𝟙 P.complex)) at h
  rw [yonedaPullback_central A z hz hA,yonedaPullback_id] at h
  have he := h.homologyMap_eq n
  simp only [HomologicalComplex.homologyMap_neg,HomologicalComplex.homologyMap_id] at he
  apply (ModuleCat.isZero_of_iff_subsingleton).mpr
  have hzero (v : (P.complex.linearYonedaObj ℚ A).homology n) : v = 0 := by
    have hv : -v = v := congrArg (fun f => f v) he
    have h2 : (2 : ℚ) • v = 0 := by
      rw [two_smul]
      exact (congrArg (fun w => w+v) hv.symm).trans (neg_add_cancel v)
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- A central element acting by minus identity kills actual rational group cohomology in every degree. -/
theorem isZero_groupCohomology (A : Rep ℚ G) (z : G) (hz : ∀ g, z*g = g*z)
    (hA : ∀ v : A, A.ρ z v = -v) (n : ℕ) : IsZero (groupCohomology A n) :=
  (isZero_yoneda_homology A z hz hA (Rep.barResolution ℚ G) n).of_iso
    (groupCohomologyIso A n (Rep.barResolution ℚ G))

/-- Even without centrality, a sign element forces invariant vectors to vanish. -/
theorem invariants_eq_bot (A : Rep ℚ G) (z : G) (hA : ∀ v : A, A.ρ z v = -v) :
    A.ρ.invariants = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hfix := (Representation.mem_invariants A.ρ v).mp hv z
  rw [hA v] at hfix
  have h2 : (2 : ℚ) • v = 0 := by
    rw [two_smul]
    exact (congrArg (fun w => w+v) hfix.symm).trans (neg_add_cancel v)
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

end TernaryPoly.CentralSignCohomology
