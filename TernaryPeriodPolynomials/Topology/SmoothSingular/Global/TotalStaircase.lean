module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal.TotalAugmentation
open CategoryTheory Limits

variable {K : RealBicomplex} {C : CochainComplex (ModuleCat.{0} ℝ) ℕ}
variable (a : TotalAugmentation C K) (hr : a.ExactRows)
include hr

/-- Every degree-two total cocycle is an actual augmented cocycle plus an actual total boundary.
The proof is the finite horizontal staircase, using the displayed totalization signs. -/
theorem total_cycle_lift (x : TotalTwo K) (hx : totalTwoD K x = 0) :
    ∃ z : C.X 2, (C.d 2 3).hom z = 0 ∧
      ∃ y : TotalOne K, x = totalOneD K y + a.augmentationTwo z := by
  rcases x with ⟨b20, b11, b02⟩
  have h30 : horizontal K 2 0 b20 = 0 := congrArg Prod.fst hx
  have h21 : vertical K 2 0 b20 + horizontal K 1 1 b11 = 0 :=
    congrArg (fun z => z.2.1) hx
  have h12 : -vertical K 1 1 b11 + horizontal K 0 2 b02 = 0 :=
    congrArg (fun z => z.2.2.1) hx
  have h03 : vertical K 0 2 b02 = 0 := congrArg (fun z => z.2.2.2) hx
  obtain ⟨u, hu⟩ := hr.horizontal_exact 1 0 b20 h30
  have h11 : horizontal K 1 1 (b11 + vertical K 1 0 u) = 0 := by
    rw [map_add, ← horizontal_vertical, hu]
    exact (add_comm _ _).trans h21
  obtain ⟨w, hw⟩ := hr.horizontal_exact 0 1 _ h11
  have h02 : horizontal K 0 2 (b02 - vertical K 0 1 w) = 0 := by
    rw [map_sub, ← horizontal_vertical, hw, map_add, vertical_squared, add_zero]
    simpa only [sub_eq_add_neg, add_comm] using h12
  obtain ⟨z, hz⟩ := hr.augmentation_exact 2 _ h02
  have hdz : (C.d 2 3).hom z = 0 := by
    apply hr.injective 3
    rw [map_zero, ← a.augment_vertical 2, hz, map_sub, h03, vertical_squared, sub_zero]
  refine ⟨z, hdz, ⟨u,w⟩, ?_⟩
  change (b20,b11,b02) =
    (horizontal K 1 0 u, -vertical K 1 0 u + horizontal K 0 1 w,
      vertical K 0 1 w) + (0,0,a.augment 2 z)
  rw [hu, hw, hz]
  apply Prod.ext
  · simp only [Prod.fst_add, add_zero]
  apply Prod.ext
  · change b11 = -vertical K 1 0 u + (b11 + vertical K 1 0 u) + 0
    abel
  · change b02 = vertical K 0 1 w + (b02 - vertical K 0 1 w)
    abel

/-- An augmented degree-two cochain which is a total boundary is already a boundary
in the original complex. This is the finite staircase in the reverse direction. -/
theorem total_boundary_lift (z : C.X 2) (y : TotalOne K)
    (hy : a.augmentationTwo z = totalOneD K y) :
    ∃ t : C.X 1, (C.d 1 2).hom t = z := by
  rcases y with ⟨u,w⟩
  have hu : horizontal K 1 0 u = 0 := (congrArg Prod.fst hy).symm
  have hw : -vertical K 1 0 u + horizontal K 0 1 w = 0 :=
    (congrArg (fun x => x.2.1) hy).symm
  have hz : a.augment 2 z = vertical K 0 1 w := congrArg (fun x => x.2.2) hy
  obtain ⟨s, hs⟩ := hr.horizontal_exact 0 0 u hu
  have hws : horizontal K 0 1 (w - vertical K 0 0 s) = 0 := by
    rw [map_sub, ← horizontal_vertical, hs]
    simpa only [sub_eq_add_neg, add_comm] using hw
  obtain ⟨t, ht⟩ := hr.augmentation_exact 1 _ hws
  refine ⟨t, hr.injective 2 ?_⟩
  rw [← a.augment_vertical 1, ht, map_sub, vertical_squared, sub_zero, hz]

end TernaryPoly.SmoothSingularGlobal.TotalAugmentation
