module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.Connecting

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSingular
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalSingularAugmentation
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Restrict a genuine pair-preserving homotopy to its literal subspaces. -/
def subspaceHomotopy {f g : C(X,Y)} (S : Set X) (T : Set Y)
    (hf : Set.MapsTo f S T) (hg : Set.MapsTo g S T)
    (H : ContinuousMap.Homotopy f g) (hH : ∀ t x, x ∈ S → H (t,x) ∈ T) :
    ContinuousMap.Homotopy (subspaceMap f S T hf) (subspaceMap g S T hg) where
  toFun p := ⟨H (p.1,p.2.val),hH p.1 p.2.val p.2.property⟩
  continuous_toFun := (H.continuous.comp (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := by ext; exact H.map_zero_left x.val
  map_one_left x := by ext; exact H.map_one_left x.val

/-- Maps into a pair with contractible ambient space induce equal positive relative maps
whenever their actual subspace restrictions are homotopic. The source need not be contractible. -/
theorem relativeHomologyMap_eq_of_subspaceHomotopy [ContractibleSpace Y]
    (f g : C(X,Y)) (S : Set X) (T : Set Y)
    (hf : Set.MapsTo f S T) (hg : Set.MapsTo g S T)
    (H : ContinuousMap.Homotopy (subspaceMap f S T hf) (subspaceMap g S T hg))
    (k : ℕ) (hk : k ≠ 0) :
    homologyMap (relativeMap f S T hf) (k+1) =
      homologyMap (relativeMap g S T hg) (k+1) := by
  apply (cancel_mono (relativeSuccIso T k hk).hom).mp
  change _ ≫ connecting T k = _ ≫ connecting T k
  rw [← connecting_naturality, ← connecting_naturality]
  congr 1
  exact (show TopCat.Homotopy (TopCat.ofHom (subspaceMap f S T hf))
    (TopCat.ofHom (subspaceMap g S T hg)) from H).congr_homologyMap_singularChainComplexFunctor
      (ModuleCat.of.{0} ℚ ℚ) k

/-- Genuine pair-preserving homotopies induce equal relative homology maps in degree k+1,
for k>0 and contractible target ambient space. -/
theorem relativeHomologyMap_eq_of_homotopy [ContractibleSpace Y]
    (f g : C(X,Y)) (S : Set X) (T : Set Y)
    (hf : Set.MapsTo f S T) (hg : Set.MapsTo g S T)
    (H : ContinuousMap.Homotopy f g) (hH : ∀ t x, x ∈ S → H (t,x) ∈ T)
    (k : ℕ) (hk : k ≠ 0) :
    homologyMap (relativeMap f S T hf) (k+1) =
      homologyMap (relativeMap g S T hg) (k+1) :=
  relativeHomologyMap_eq_of_subspaceHomotopy f g S T hf hg
    (subspaceHomotopy S T hf hg H hH) k hk

/-- The literal identity pair map induces the identity relative chain map. -/
@[simp] theorem relativeMap_id (S : Set X) :
    relativeMap (ContinuousMap.id X) S S (fun _ hx => hx) = 𝟙 (relativeChains S) := by
  apply (cancel_epi (cokernel.π (inclusion S))).mp
  simp [relativeMap, cokernel.map]

/-- The literal homeomorphism-induced relative chain map agrees with the pair map. -/
theorem relativeHomeomorphIso_hom (e : X ≃ₜ Y) (S : Set X) (T : Set Y)
    (h : ∀ x, x ∈ S ↔ e x ∈ T) :
    (relativeHomeomorphIso e S T h).hom =
      relativeMap e.toHomotopyEquiv.toFun S T (fun x hx => (h x).mp hx) := rfl

end TernaryPoly.RationalRelativeSingular
