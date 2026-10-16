module

public import TernaryPeriodPolynomials.Building.Good.IntegralNormalization
public import TernaryPeriodPolynomials.Building.Good.LatticeReduction
public import TernaryPeriodPolynomials.Building.Good.ApartmentCycles

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodIntegralFrames
open ModThreeGoodAction GoodIntegralNormalization GoodLatticeReduction
open GoodIncidenceConnected GoodApartmentCycles

/-- An integral vector with residue-one coordinate sum determines an actual good line. -/
def vectorLine (v : IntegralVector) (hv : ∑ i, (v i : ZMod 3) = 1) : Line Good :=
  ⟨Submodule.span ℚ {rationalVector v},
    finrank_span_singleton (rationalVector_ne_zero (by rw [hv]; exact one_ne_zero)),
    ⟨v,Submodule.subset_span (Set.mem_singleton _),by rw [hv]; exact one_ne_zero⟩⟩

/-- The good line represented by a normalized matrix column. -/
def columnLine (M : Matrix (Fin 3) (Fin 3) ℤ) (hM : NormalizedColumns M)
    (j : Fin 3) : Line Good := vectorLine (fun i => M i j) (hM j)

/-- The actual apartment represented by an integral normalized frame. -/
def frameApartment (M : Matrix (Fin 3) (Fin 3) ℤ) (hM : NormalizedColumns M) :
    GoodApartmentCycles.Cycles Good :=
  apartmentCycle Good (columnLine M hM 0) (columnLine M hM 1) (columnLine M hM 2)

/-- Choose a normalized integral generator of an actual good rational line. -/
def lineGenerator (L : Line Good) : IntegralVector :=
  (good_line_primitive_generator L.property.1 L.property.2).choose

theorem lineGenerator_residue (L : Line Good) : ∑ i, (lineGenerator L i : ZMod 3) = 1 :=
  (good_line_primitive_generator L.property.1 L.property.2).choose_spec.2.2.2.2

theorem lineGenerator_span (L : Line Good) :
    Submodule.span ℚ {rationalVector (lineGenerator L)} = L.val :=
  (good_line_primitive_generator L.property.1 L.property.2).choose_spec.2.2.2.1

/-- Every triple of good rational lines is represented by a normalized integral matrix. -/
def lineFrame (L : Fin 3 → Line Good) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => lineGenerator (L j) i

theorem lineFrame_normalized (L : Fin 3 → Line Good) : NormalizedColumns (lineFrame L) :=
  fun j => lineGenerator_residue (L j)

@[simp] theorem columnLine_lineFrame (L : Fin 3 → Line Good) (j : Fin 3) :
    columnLine (lineFrame L) (lineFrame_normalized L) j = L j := by
  apply Subtype.ext
  exact lineGenerator_span (L j)

theorem apartment_eq_frame (L M N : Line Good) :
    apartmentCycle Good L M N =
      frameApartment (lineFrame ![L,M,N]) (lineFrame_normalized ![L,M,N]) := by
  rw [frameApartment,columnLine_lineFrame,columnLine_lineFrame,columnLine_lineFrame]
  rfl

end TernaryPoly.GoodIntegralFrames
