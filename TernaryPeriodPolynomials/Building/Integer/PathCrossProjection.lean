module

public import TernaryPeriodPolynomials.Building.OrientedChain.ImageFaceProjection
public import TernaryPeriodPolynomials.Building.Integer.PathJoinCycles

@[expose] public section

noncomputable section
namespace TernaryPoly.IntegerPathCrossProjection
open OrientedListChains OrientedChainJoin OrientedImageFaceProjection
open IntegerPathJoinCycles

variable {V W U : Type*}
local instance : DecidableEq W := Classical.decEq W

/-- Exact image faces commute with composing actual vertex maps. -/
theorem imageFace_map (h : U → V) (f : V → W) (l : List U) :
    imageFace f (l.map h) = imageFace (f ∘ h) l := by
  simp only [imageFace,List.map_map]

/-- Exact image-face projection is natural under arbitrary vertex relabeling, including
relabelings which collapse vertices or simplex dimensions. -/
theorem project_map (h : U → V) (f : V → W) (s : Finset W) (c : Chain U) :
    project f s (OrientedChainMap.map h c) =
      OrientedChainMap.map h (project (f ∘ h) s c) := by
  have he : (project f s).comp (OrientedChainMap.map h) =
      (OrientedChainMap.map h).comp (project (f ∘ h) s) := by
    apply chain_ext
    intro l
    change project f s (OrientedChainMap.map h (simplex l)) =
      OrientedChainMap.map h (project (f ∘ h) s (simplex l))
    rw [OrientedChainMap.map_simplex,project_simplex,project_simplex,imageFace_map]
    by_cases hs : imageFace (f ∘ h) l = s <;>
      simp only [hs,ite_true,ite_false,OrientedChainMap.map_simplex,map_zero]
  exact LinearMap.congr_fun he c

/-- The actual constant-on-fibers map to the two specified base vertices. -/
def twoFiber (A B : W) : Vertex → W := Sum.elim (fun _ => A) (fun _ => B)

theorem imageFace_left_right (A B : W) (k l : ℤ) :
    imageFace (twoFiber A B) [.inl k,.inr l] = {A,B} := by
  simp [imageFace,twoFiber]

theorem imageFace_right_left (A B : W) (k l : ℤ) :
    imageFace (twoFiber A B) [.inr l,.inl k] = {A,B} := by
  simp [imageFace,twoFiber,Finset.pair_comm]

/-- Exact two-fiber projection preserves the cross-edge coefficient on every chain. -/
theorem cross_project (A B : W) (c : IntegerPathJoinCycles.C) :
    cross (project (twoFiber A B) {A,B} c) = cross c := by
  have he : cross.comp (project (twoFiber A B) {A,B}) = cross := by
    apply chain_ext
    intro l
    change cross (project (twoFiber A B) {A,B} (simplex l)) = cross (simplex l)
    rw [project_simplex]
    by_cases hs : imageFace (twoFiber A B) l = {A,B}
    · simp only [hs,ite_true]
    · simp only [hs,ite_false,map_zero,cross_simplex]
      cases l with
      | nil => rfl
      | cons a l =>
        cases l with
        | nil => cases a <;> rfl
        | cons b l =>
          cases l with
          | cons d l => cases a <;> cases b <;> rfl
          | nil =>
            cases a with
            | inl k =>
              cases b with
              | inl m => rfl
              | inr l => exact (hs (imageFace_left_right A B k l)).elim
            | inr l =>
              cases b with
              | inl k => exact (hs (imageFace_right_left A B k l)).elim
              | inr m => rfl
  exact LinearMap.congr_fun he c

/-- The prescribed constant values determine the whole composed vertex map. -/
theorem comp_eq_twoFiber (h : Vertex → V) (f : V → W) (A B : W)
    (hA : ∀ k : ℤ, f (h (.inl k)) = A) (hB : ∀ l : ℤ, f (h (.inr l)) = B) :
    f ∘ h = twoFiber A B := by
  funext v
  cases v with
  | inl k => exact hA k
  | inr l => exact hB l

/-- Vanishing of just the projected cross-edge component detects zero model cross coefficient.
The injective relabeling is used to pull back the projected chain, not to assume it is a cycle. -/
theorem cross_zero_of_project_map (h : Vertex → V) (hh : Function.Injective h)
    (f : V → W) (A B : W)
    (hA : ∀ k : ℤ, f (h (.inl k)) = A) (hB : ∀ l : ℤ, f (h (.inr l)) = B)
    (c : IntegerPathJoinCycles.C) (hc : project f {A,B} (OrientedChainMap.map h c) = 0) : cross c = 0 := by
  rw [project_map,comp_eq_twoFiber h f A B hA hB] at hc
  have hz := (OrientedChainMap.map_eq_zero_iff h hh _).mp hc
  rw [← cross_project A B c,hz,map_zero]

/-- The exact hypothesis needed when globally splitting a mixed-triangle boundary by base edge. -/
theorem cross_zero_of_project_boundary (h : Vertex → V) (hh : Function.Injective h)
    (f : V → W) (A B : W)
    (hA : ∀ k : ℤ, f (h (.inl k)) = A) (hB : ∀ l : ℤ, f (h (.inr l)) = B)
    (z : IntegerGridExactness.C₁)
    (hz : project f {A,B} (boundary (OrientedChainMap.map h (mixed z))) = 0) :
    cross (boundary (mixed z)) = 0 := by
  rw [OrientedChainMap.boundary_map] at hz
  exact cross_zero_of_project_map h hh f A B hA hB _ hz

end TernaryPoly.IntegerPathCrossProjection
