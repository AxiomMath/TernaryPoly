module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open EquivariantMayerVietorisHomology SymmetricSpaceBoundaryFaceAugmentation

/-- The two open pieces have no positive homology, also as their actual chain biproduct. -/
theorem middle_positive (n : ℕ) (hn : n≠0) : IsZero (mvComplex.X₂.homology n) :=
  homologyBiprod_isZero n (left_positive n hn) (right_positive n hn)

/-- Actual principal-six equivariant boundary H1 is the kernel of literal signed flag incidence. -/
def boundaryH1Iso : boundaryChains.homology 1 ≅ kernel incidence :=
  (ambientHomologyIso 1).symm ≪≫
    homologyOneKernelIso mvComplex mvShortExact (middle_positive 1 (by decide)) ≪≫
      kernel.mapIso (homologyMap mvComplex.f 0) incidence interH0Iso middleH0Iso incidence_natural

/-- The actual edge map is the genuine MV connecting map followed by the literal corner-label augmentation. -/
def boundaryEdgeMap : boundaryChains.homology 1 ⟶ flagLabels :=
  (ambientHomologyIso 1).inv ≫ mvShortExact.δ 1 0 rfl ≫ interH0Iso.hom

/-- The H1 isomorphism preserves the actual edge map, including its signs. -/
theorem boundaryH1Iso_edge : boundaryH1Iso.hom ≫ kernel.ι incidence=boundaryEdgeMap := by
  let e := homologyOneKernelIso mvComplex mvShortExact (middle_positive 1 (by decide))
  let k := kernel.mapIso (homologyMap mvComplex.f 0) incidence interH0Iso middleH0Iso incidence_natural
  have hk : k.hom ≫ kernel.ι incidence=kernel.ι (homologyMap mvComplex.f 0) ≫ interH0Iso.hom :=
    kernel.lift_ι incidence (kernel.ι (homologyMap mvComplex.f 0) ≫ interH0Iso.hom) _
  have he : e.hom ≫ kernel.ι (homologyMap mvComplex.f 0)=mvShortExact.δ 1 0 rfl :=
    homologyOneKernelIso_hom_ι mvComplex mvShortExact _
  have h : (e.hom ≫ k.hom) ≫ kernel.ι incidence=mvShortExact.δ 1 0 rfl ≫ interH0Iso.hom :=
    (Category.assoc _ _ _).trans ((congrArg (fun m => e.hom ≫ m) hk).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ interH0Iso.hom) he)))
  exact (Category.assoc _ _ _).trans (congrArg (fun m => (ambientHomologyIso 1).inv ≫ m) h)

theorem boundaryEdgeMap_incidence : boundaryEdgeMap ≫ incidence=0 := by
  rw [←boundaryH1Iso_edge,Category.assoc,kernel.condition,comp_zero]

/-- Higher singular homology of the entire geometric boundary vanishes by actual MV exactness. -/
theorem boundary_homology_succ_succ (n : ℕ) : IsZero (boundaryChains.homology (n+2)) :=
  (homology_succ_succ_isZero mvComplex mvShortExact n (inter_positive (n+1) (Nat.succ_ne_zero n))
    (middle_positive (n+2) (by omega))).of_iso (ambientHomologyIso (n+2)).symm

theorem boundary_homology_ge_two (n : ℕ) (hn : 2≤n) : IsZero (boundaryChains.homology n) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [Nat.add_comm] using boundary_homology_succ_succ m

/-- The actual degree-zero group is the cokernel of the same literal signed incidence map. -/
def boundaryH0CokernelIso : boundaryChains.homology 0 ≅ cokernel incidence :=
  (ambientHomologyIso 0).symm ≪≫ homologyZeroCokernelIso mvComplex mvShortExact ≪≫
    cokernel.mapIso (homologyMap mvComplex.f 0) incidence interH0Iso middleH0Iso incidence_natural

end TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
