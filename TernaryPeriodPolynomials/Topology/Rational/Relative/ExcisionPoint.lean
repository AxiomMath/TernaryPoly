module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionSmall

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeExcision
open CategoryTheory Limits HomologicalComplex TopologicalSpace ContractibleSingularHomology
open RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- The puncture of the literal subtype is identified with the literal ambient puncture preimage by the identity homeomorphism. -/
def pointPairIso (x : X) (V : Set X) (hx : x ∈ V) :
    relativeChains ({(⟨x,hx⟩ : V)}ᶜ : Set V) ≅ relativeChains (inside ({x}ᶜ : Set X) V) :=
  relativeHomeomorphIso (Homeomorph.refl V) _ _ (by
    intro v
    change v ≠ (⟨x,hx⟩ : V) ↔ v.val ≠ x
    exact not_congr Subtype.ext_iff)

/-- The punctured-subtype identification induces identity on its ambient chains. -/
theorem pointPairIso_projection (x : X) (V : Set X) (hx : x ∈ V) :
    cokernel.π (inclusion ({(⟨x,hx⟩ : V)}ᶜ : Set V)) ≫ (pointPairIso x V hx).hom =
      cokernel.π (inclusion (inside ({x}ᶜ : Set X) V)) := by
  simp [pointPairIso,relativeHomeomorphIso,cokernel.mapIso,cokernel.map,chainHomeomorphIso]

/-- The actual pair inclusion from a punctured neighborhood to the punctured ambient space. -/
def pointExcisionMap (x : X) (V : Set X) (hx : x ∈ V) :
    relativeChains ({(⟨x,hx⟩ : V)}ᶜ : Set V) ⟶ relativeChains ({x}ᶜ : Set X) :=
  (pointPairIso x V hx).hom ≫ excisionMap ({x}ᶜ : Set X) V

/-- Point-local excision is induced by the literal inclusion V→X, with no arbitrary map selection. -/
theorem pointExcisionMap_projection (x : X) (V : Set X) (hx : x ∈ V) :
    cokernel.π (inclusion ({(⟨x,hx⟩ : V)}ᶜ : Set V)) ≫ pointExcisionMap x V hx =
      inclusion V ≫ cokernel.π (inclusion ({x}ᶜ : Set X)) := by
  rw [pointExcisionMap,← Category.assoc,pointPairIso_projection,excisionMap_projection]

/-- The point-local map equals the actual continuous map-of-pairs cokernel construction. -/
theorem pointExcisionMap_eq_relativeMap (x : X) (V : Set X) (hx : x ∈ V) :
    pointExcisionMap x V hx = relativeMap ⟨Subtype.val,continuous_subtype_val⟩
      ({(⟨x,hx⟩ : V)}ᶜ : Set V) ({x}ᶜ : Set X)
      (fun _ hv h => hv (Subtype.ext h)) := by
  apply (cancel_epi (cokernel.π (inclusion ({(⟨x,hx⟩ : V)}ᶜ : Set V)))).mp
  rw [pointExcisionMap_projection]
  simp [relativeMap,cokernel.map]

/-- In a T1 space, the puncture of a point is an actual open subspace. -/
def puncturedOpen [T1Space X] (x : X) : Opens X := ⟨{x}ᶜ,isOpen_compl_singleton⟩

/-- A neighborhood of x and the open complement of x form an actual two-open cover. -/
theorem puncturedOpen_sup [T1Space X] (x : X) (V : Opens X) (hx : x ∈ V) :
    puncturedOpen x ⊔ V = ⊤ := by
  ext y
  by_cases hy : y = x
  · subst y
    simp [puncturedOpen,hx]
  · simp [puncturedOpen,hy]

/-- Point-local rational singular excision holds for the actual pair inclusion in every degree. -/
theorem pointExcisionMap_quasiIso [T1Space X] (x : X) (V : Opens X) (hx : x ∈ V) :
    QuasiIso (pointExcisionMap x (V : Set X) hx) := by
  have : QuasiIso (excisionMap ({x}ᶜ : Set X) (V : Set X)) :=
    excisionMap_quasiIso (puncturedOpen x) V (puncturedOpen_sup x V hx)
  unfold pointExcisionMap
  infer_instance

/-- The genuine point-local homology isomorphism induced by inclusion of an open neighborhood. -/
def pointLocalHomologyIso [T1Space X] (x : X) (V : Opens X) (hx : x ∈ V) (n : ℕ) :
    (relativeChains ({(⟨x,hx⟩ : V)}ᶜ : Set V)).homology n ≅
      (relativeChains ({x}ᶜ : Set X)).homology n := by
  have := pointExcisionMap_quasiIso x V hx
  exact asIso (homologyMap (pointExcisionMap x (V : Set X) hx) n)

/-- The point-local homology isomorphism has exactly the actual inclusion-induced homology map. -/
theorem pointLocalHomologyIso_hom [T1Space X] (x : X) (V : Opens X) (hx : x ∈ V) (n : ℕ) :
    (pointLocalHomologyIso x V hx n).hom = homologyMap (pointExcisionMap x (V : Set X) hx) n := rfl

end TernaryPoly.RationalRelativeExcision
