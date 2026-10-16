module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechBicomplex

@[expose] public section


/-! The actual augmented smooth Čech and exterior differentials commute. -/
noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set SmoothCoveringDeRham SymmetricSpaceCovering
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))

theorem formCechD_columnD (k q : ℕ) (v : FormCechTerms ρ U q k) :
    formCechD ρ U (q+1) k (formCechColumnD ρ U hU k q v) =
      formCechColumnD ρ U hU (k+1) q (formCechD ρ U q k v) := by
  funext t
  change formCechD ρ U (q+1) k (formCechColumnD ρ U hU k q v) t =
    differential ρ (cechDomain_isOpen U hU t) q (formCechD ρ U q k v t)
  rw [formCechD_apply, formCechD_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_zsmul]
  exact congrArg (((-1 : ℤ)^a.val) • ·)
    (restrictEquivariant_d ρ (cechDomain_isOpen U hU (t ∘ a.succAbove))
      (cechDomain_isOpen U hU t) (cechDomain_select_subset U a.succAbove t) (v (t ∘ a.succAbove)))

theorem formCechEmptyRecover_differential (q : ℕ) (v : FormCechTerms ρ U q 0) :
    formCechEmptyRecover ρ U (q+1) (formCechColumnD ρ U hU 0 q v) =
      differential ρ isOpen_univ q (formCechEmptyRecover ρ U q v) :=
  restrictEquivariant_d ρ (cechDomain_isOpen U hU Fin.elim0) isOpen_univ
    (univ_subset_cechDomain_empty U Fin.elim0) (v Fin.elim0)

end TernaryPoly.SmoothSingularGlobal
