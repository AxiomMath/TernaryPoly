module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.HomogeneousCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def binaryCuspRealize (cusp : CuspidalRepresentation) (degree : ℕ) :
    (BinaryDegreeMonomial (degree + 1) → cusp.smooth) →ₗ[ℂ]
      (BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) where
  toFun vectors argument := binaryHomogeneousReconstruct (degree + 1)
    (fun monomial => cusp.realize (vectors monomial) argument)
  map_add' first second := by
    funext argument
    change binaryHomogeneousReconstruct (degree + 1)
      (fun monomial => cusp.realize (first monomial + second monomial) argument) = _
    simp only [map_add, Pi.add_apply]
    exact (binaryHomogeneousReconstruct (degree + 1)).map_add _ _
  map_smul' scalar vectors := by
    funext argument
    change binaryHomogeneousReconstruct (degree + 1)
      (fun monomial => cusp.realize (scalar • vectors monomial) argument) = _
    simp only [map_smul, Pi.smul_apply]
    exact (binaryHomogeneousReconstruct (degree + 1)).map_smul scalar _

theorem binaryCuspRealize_coefficient (cusp : CuspidalRepresentation) (degree : ℕ)
    (vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth)
    (argument : BinaryAdelicGL) (monomial : BinaryDegreeMonomial (degree + 1)) :
    (binaryCuspRealize cusp degree vectors argument).val.coeff monomial.val =
      cusp.realize (vectors monomial) argument :=
  congrFun (binaryHomogeneousCoordinates_reconstruct (degree + 1)
    (fun monomial => cusp.realize (vectors monomial) argument)) monomial

theorem binaryCuspRealize_injective (cusp : CuspidalRepresentation) (degree : ℕ) :
    Function.Injective (binaryCuspRealize cusp degree) := by
  intro first second equality
  funext monomial
  apply cusp.injective
  funext argument
  have coefficient := congrArg
    (fun values => (values argument).val.coeff monomial.val) equality
  simpa only [binaryCuspRealize_coefficient] using coefficient

theorem binaryCuspRealize_values (cusp : CuspidalRepresentation) (degree : ℕ)
    (vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth) :
    BinaryValues cusp degree (binaryCuspRealize cusp degree vectors) := by
  intro monomial
  by_cases matching : Finsupp.degree monomial = degree + 1
  · refine ⟨vectors ⟨monomial, matching⟩, ?_⟩
    funext argument
    exact (binaryCuspRealize_coefficient cusp degree vectors argument ⟨monomial, matching⟩).symm
  · refine ⟨0, ?_⟩
    funext argument
    rw [map_zero, Pi.zero_apply,
      (binaryCuspRealize cusp degree vectors argument).property.coeff_eq_zero matching]

theorem binaryValues_iff_cuspRealize (cusp : CuspidalRepresentation) (degree : ℕ)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) :
    BinaryValues cusp degree values ↔
      ∃ vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth,
        binaryCuspRealize cusp degree vectors = values := by
  constructor
  · intro cuspidal
    have coordinates : ∀ monomial : BinaryDegreeMonomial (degree + 1),
        ∃ vector : cusp.smooth,
          cusp.realize vector = fun argument => (values argument).val.coeff monomial.val :=
      fun monomial => cuspidal monomial.val
    choose vectors realizes using coordinates
    refine ⟨vectors, ?_⟩
    funext argument
    apply binaryHomogeneousCoordinates_injective (degree + 1)
    funext monomial
    exact (binaryCuspRealize_coefficient cusp degree vectors argument monomial).trans
      (congrFun (realizes monomial) argument)
  · rintro ⟨vectors, rfl⟩
    exact binaryCuspRealize_values cusp degree vectors

theorem binaryCuspRealize_translate (cusp : CuspidalRepresentation) (degree : ℕ)
    (matrix : BinaryAdelicGL) (vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth)
    (argument : BinaryAdelicGL) :
    binaryCuspRealize cusp degree (fun monomial => cuspSmoothAction cusp matrix (vectors monomial)) argument =
      binaryCuspRealize cusp degree vectors (argument * matrix) := by
  apply binaryHomogeneousCoordinates_injective (degree + 1)
  funext monomial
  change (_ : MvPolynomial (Fin 2) ℂ).coeff monomial.val = (_ : MvPolynomial (Fin 2) ℂ).coeff monomial.val
  rw [binaryCuspRealize_coefficient, binaryCuspRealize_coefficient]
  exact cusp.equivariant matrix (vectors monomial) argument

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
