module

public import TernaryPeriodPolynomials.Topology.Euclidean.Local.HomologyAtPoint
public import TernaryPeriodPolynomials.Topology.Rational.Relative.Homotopy

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanLocalHomology
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular RationalSingularAugmentation

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Center a continuous Euclidean map at a specified point of its source and image. -/
def centeredMap (f : C(E,E)) (x : E) : C(E,E) :=
  ⟨fun z => f (z+x)-f x, (f.continuous.comp (continuous_id.add continuous_const)).sub
    continuous_const⟩

/-- A path of injective Euclidean maps gives an actual centered homotopy. -/
def centeredHomotopy (f : C(E,E)) (x : E)
    (H : ContinuousMap.Homotopy (ContinuousMap.id E) f) :
    ContinuousMap.Homotopy (ContinuousMap.id E) (centeredMap f x) where
  toFun p := H (p.1,p.2+x)-H (p.1,x)
  continuous_toFun := (H.continuous.comp (continuous_fst.prodMk
    (continuous_snd.add continuous_const))).sub
      (H.continuous.comp (continuous_fst.prodMk continuous_const))
  map_zero_left z := by simp
  map_one_left z := by simp [centeredMap]

/-- Injectivity at each time makes the centered homotopy preserve the punctured space. -/
theorem centeredHomotopy_punctured (f : C(E,E)) (x : E)
    (H : ContinuousMap.Homotopy (ContinuousMap.id E) f)
    (hH : ∀ t, Function.Injective (fun z => H (t,z))) :
    ∀ t z, z ∈ ({0}ᶜ : Set E) → centeredHomotopy f x H (t,z) ∈ ({0}ᶜ : Set E) := by
  intro t z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
  change H (t,z+x)-H (t,x) ≠ 0
  intro heq
  have := hH t (sub_eq_zero.mp heq)
  exact hz (add_right_cancel (this.trans (zero_add x).symm))

/-- An injective map has an actual centered endomorphism of the punctured pair. -/
theorem centeredMap_punctured (f : C(E,E)) (x : E) (hf : Function.Injective f) :
    Set.MapsTo (centeredMap f x) ({0}ᶜ : Set E) ({0}ᶜ : Set E) := by
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
  intro heq
  have he : z+x=x := hf (sub_eq_zero.mp heq)
  exact hz (add_right_cancel (he.trans (zero_add x).symm))

/-- Every centered map obtained by an isotopy acts identically on genuine local homology
in every degree at least two. This is a statement about the actual relative pair map. -/
theorem centered_localHomologyMap_eq_id (f : C(E,E)) (x : E)
    (hf : Function.Injective f) (H : ContinuousMap.Homotopy (ContinuousMap.id E) f)
    (hH : ∀ t, Function.Injective (fun z => H (t,z))) (k : ℕ) (hk : k ≠ 0) :
    homologyMap (relativeMap (centeredMap f x) ({0}ᶜ : Set E) ({0}ᶜ : Set E)
      (centeredMap_punctured f x hf)) (k+1) = 𝟙 _ := by
  have h := relativeHomologyMap_eq_of_homotopy (ContinuousMap.id E) (centeredMap f x)
    ({0}ᶜ : Set E) ({0}ᶜ : Set E) (fun _ hz => hz) (centeredMap_punctured f x hf)
    (centeredHomotopy f x H) (centeredHomotopy_punctured f x H hH) k hk
  simpa using h.symm

end TernaryPoly.EuclideanLocalHomology
