module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Bernoulli.Coordinates

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix Homogeneous

theorem apartment_translate (matrix frame : RationalGL3) :
    translateChain matrix (apartment frame) = apartment (matrix * frame) := by
  have action (representative : RationalGL3) :
      matrix • (QuotientGroup.mk representative : Edges) =
        QuotientGroup.mk (matrix * representative) := rfl
  simp only [apartment, map_sub, map_add, translateChain, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, action, mul_assoc]

theorem apartment_boundary (frame : RationalGL3) : chainBoundary (apartment frame) = 0 := by
  have first_line : (QuotientGroup.mk swapFirstTwo : Flags .line) =
      QuotientGroup.mk (Adelic.weyl : RationalGL3) := by
    apply line_flag_eq_of_column 1
    intro index
    fin_cases index <;> norm_num [Adelic.weyl, swapFirstTwo]
  have second_line : (QuotientGroup.mk (Adelic.weyl * swapFirstTwo) : Flags .line) =
      QuotientGroup.mk ((Adelic.weyl : RationalGL3) ^ 2) := by
    apply line_flag_eq_of_column 1
    intro index
    fin_cases index <;>
      norm_num [Adelic.weyl, swapFirstTwo, pow_two, Matrix.mul_apply,
        Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have third_line : (QuotientGroup.mk (Adelic.weyl ^ 2 * swapFirstTwo) : Flags .line) =
      QuotientGroup.mk (1 : RationalGL3) := by
    apply line_flag_eq_of_column 1
    intro index
    fin_cases index <;>
      norm_num [Adelic.weyl, swapFirstTwo, pow_two, Matrix.mul_apply,
        Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have translated_first := congrArg (fun flag : Flags .line => frame • flag) first_line
  have translated_second := congrArg (fun flag : Flags .line => frame • flag) second_line
  have translated_third := congrArg (fun flag : Flags .line => frame • flag) third_line
  change (QuotientGroup.mk (frame * swapFirstTwo) : Flags .line) =
    QuotientGroup.mk (frame * Adelic.weyl) at translated_first
  change (QuotientGroup.mk (frame * (Adelic.weyl * swapFirstTwo)) : Flags .line) =
    QuotientGroup.mk (frame * Adelic.weyl ^ 2) at translated_second
  change (QuotientGroup.mk (frame * (Adelic.weyl ^ 2 * swapFirstTwo)) : Flags .line) =
    QuotientGroup.mk (frame * 1) at translated_third
  simp only [← mul_assoc, mul_one] at translated_second translated_third
  simp only [apartment, map_add, map_sub, chainBoundary_single, endpoint,
    Quotient.map'_mk'', id_eq]
  change (Finsupp.single (Sum.inl (QuotientGroup.mk frame : Flags .plane)) 1 -
      Finsupp.single (Sum.inr (QuotientGroup.mk frame : Flags .line)) 1) -
    (Finsupp.single (Sum.inl (QuotientGroup.mk (frame * swapFirstTwo) : Flags .plane)) 1 -
      Finsupp.single (Sum.inr (QuotientGroup.mk (frame * swapFirstTwo) : Flags .line)) 1) +
    (Finsupp.single (Sum.inl (QuotientGroup.mk (frame * Adelic.weyl) : Flags .plane)) 1 -
      Finsupp.single (Sum.inr (QuotientGroup.mk (frame * Adelic.weyl) : Flags .line)) 1) -
    (Finsupp.single (Sum.inl (QuotientGroup.mk (frame * Adelic.weyl * swapFirstTwo) : Flags .plane)) 1 -
      Finsupp.single (Sum.inr (QuotientGroup.mk (frame * Adelic.weyl * swapFirstTwo) : Flags .line)) 1) +
    (Finsupp.single (Sum.inl (QuotientGroup.mk (frame * Adelic.weyl ^ 2) : Flags .plane)) 1 -
      Finsupp.single (Sum.inr (QuotientGroup.mk (frame * Adelic.weyl ^ 2) : Flags .line)) 1) -
    (Finsupp.single (Sum.inl (QuotientGroup.mk (frame * Adelic.weyl ^ 2 * swapFirstTwo) : Flags .plane)) 1 -
      Finsupp.single (Sum.inr (QuotientGroup.mk (frame * Adelic.weyl ^ 2 * swapFirstTwo) : Flags .line)) 1) = 0
  rw [plane_flag_swap, plane_flag_swap, plane_flag_swap]
  rw [translated_first, translated_second, translated_third]
  abel

theorem firstColumn_good (frame : IntegralGL3) (column_good : (frame.val 2 0 : ZMod 3) ≠ 0)
    (side : Side) : GoodFlag side
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame)) := by
  refine ⟨fun index => frame.val index 0, ?_, column_good⟩
  refine ⟨GeneralLinearGroup.map (Int.castRingHom ℚ) frame, rfl, Pi.single 0 1, ?_, ?_⟩
  · cases side with
    | plane => rfl
    | line => exact ⟨rfl, rfl⟩
  · ext index
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem firstColumn_goodFrame (frame : IntegralGL3)
    (columns_good : ∀ column, (frame.val 2 column : ZMod 3) = 1)
    (side : Side) : GoodFlag side
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame)) := by
  apply firstColumn_good frame _ side
  rw [columns_good]
  exact one_ne_zero

theorem normalizedApartment_good (frame : IntegralGL3)
    (columns_good : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    GoodChain (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frame)) := by
  have column_good (column : Fin 3) : (frame.val 2 column : ZMod 3) ≠ 0 := by
    rw [columns_good]
    exact one_ne_zero
  have good_edge (permutation : IntegralGL3)
      (rational_permutation : RationalGL3)
      (permutation_map : GeneralLinearGroup.map (Int.castRingHom ℚ) permutation = rational_permutation)
      (column : Fin 3) (column_eq : ∀ index, (frame * permutation).val index 0 = frame.val index column) :
      GoodChain (Finsupp.single
        (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame * rational_permutation)) 1) := by
    rw [← permutation_map, ← map_mul]
    apply goodChain_single
    · apply firstColumn_good _ _ .plane
      rw [column_eq]
      exact column_good column
    · apply firstColumn_good _ _ .line
      rw [column_eq]
      exact column_good column
  have identity_good : GoodChain (Finsupp.single
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame)) 1) := by
    apply goodChain_single
    · exact firstColumn_goodFrame frame columns_good .plane
    · exact firstColumn_goodFrame frame columns_good .line
  let swap : IntegralGL3 :=
    ⟨!![0,1,0;1,0,0;0,0,1], !![0,1,0;1,0,0;0,0,1], by
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three], by
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three]⟩
  have swap_map : GeneralLinearGroup.map (Int.castRingHom ℚ) swap = swapFirstTwo := by
    apply GeneralLinearGroup.ext
    intro row column
    fin_cases row <;> fin_cases column <;> norm_num [swap, swapFirstTwo,
      GeneralLinearGroup.map_apply]
  have weyl_map : GeneralLinearGroup.map (Int.castRingHom ℚ)
      (Adelic.weyl : IntegralGL3) = Adelic.weyl := by
    apply GeneralLinearGroup.ext
    intro row column
    fin_cases row <;> fin_cases column <;> norm_num [Adelic.weyl,
      GeneralLinearGroup.map_apply]
  have swapped_good := good_edge swap swapFirstTwo swap_map 1 (by
    intro index
    simp [swap, Matrix.mul_apply, Fin.sum_univ_three])
  have weyl_good := good_edge Adelic.weyl Adelic.weyl weyl_map 1 (by
    intro index
    simp [Adelic.weyl, Matrix.mul_apply, Fin.sum_univ_three])
  have weyl_swap_good := good_edge (Adelic.weyl * swap) (Adelic.weyl * swapFirstTwo)
    (by rw [map_mul, swap_map, weyl_map]) 2 (by
      intro index
      simp [swap, Adelic.weyl, Matrix.mul_apply,
        Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail])
  have weyl_squared_good := good_edge (Adelic.weyl ^ 2) (Adelic.weyl ^ 2)
    (by rw [map_pow, weyl_map]) 2 (by
      intro index
      simp [Adelic.weyl, pow_two, Matrix.mul_apply, Fin.sum_univ_three])
  have weyl_squared_swap_good := good_edge (Adelic.weyl ^ 2 * swap) (Adelic.weyl ^ 2 * swapFirstTwo)
    (by rw [map_mul, map_pow, swap_map, weyl_map]) 0 (by
      intro index
      simp [swap, Adelic.weyl, pow_two, Matrix.mul_apply,
        Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail])
  simpa only [apartment, mul_assoc] using
    goodChain_sub (goodChain_add (goodChain_sub (goodChain_add
      (goodChain_sub identity_good swapped_good) weyl_good) weyl_swap_good)
      weyl_squared_good) weyl_squared_swap_good

theorem normalizedApartment_goodCycle (frame : IntegralGL3)
    (columns_good : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    GoodCycle (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frame)) :=
  ⟨apartment_boundary _, normalizedApartment_good frame columns_good⟩

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
