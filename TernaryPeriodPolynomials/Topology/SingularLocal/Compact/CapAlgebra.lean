module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Representatives

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCap.Algebra
open CategoryTheory HomologicalComplex SingularLocalCap SingularLocalCap.Homology

/-- The quotient-cycle representative projects to the actual opcycle of its underlying chain. -/
theorem cycleClass_opcycles (S : ShortComplex (ModuleCat.{0} ℚ)) (x : Cycles S) :
    S.homologyι (cycleClass S x) = S.pOpcycles x.val := by
  have h := congrArg (fun f => f x) S.moduleCatCyclesIso_inv_π
  change S.homologyπ (S.moduleCatCyclesIso.inv x) = cycleClass S x at h
  rw [← h]
  change (S.homologyπ ≫ S.homologyι) (S.moduleCatCyclesIso.inv x) = _
  rw [S.homology_π_ι]
  change S.pOpcycles (S.iCycles (S.moduleCatCyclesIso.inv x)) = _
  have hi := congrArg (fun f => f x) S.moduleCatCyclesIso_inv_iCycles
  change S.iCycles (S.moduleCatCyclesIso.inv x) = x.val at hi
  rw [hi]

/-- Every actual short-complex homology element has a genuine cycle representative. -/
theorem cycleClass_surjective (S : ShortComplex (ModuleCat.{0} ℚ)) :
    Function.Surjective (cycleClass S) := by
  intro z
  obtain ⟨x,hx⟩ := (Boundaries S).mkQ_surjective (S.moduleCatHomologyIso.hom z)
  refine ⟨x, ?_⟩
  change S.moduleCatHomologyIso.inv ((Boundaries S).mkQ x) = z
  rw [hx]
  exact congrArg (fun f => f z) S.moduleCatHomologyIso.hom_inv_id

/-- A complex's canonical degree comparison retains the actual opcycle of a cycle representative. -/
theorem represented_opcycles {c : ComplexShape ℕ} (K : HomologicalComplex (ModuleCat.{0} ℚ) c)
    (i j k : ℕ) (hi : c.prev j = i) (hk : c.next j = k) (x : Cycles (K.sc' i j k)) :
    K.homologyι j ((K.homologyIsoSc' i j k hi hk).inv (cycleClass _ x)) = K.pOpcycles j x.val := by
  change ((K.homologyIsoSc' i j k hi hk).inv ≫ K.homologyι j) (cycleClass _ x) = _
  rw [homologyIsoSc'_inv_ι]
  change (K.opcyclesIsoSc' i j k hi hk).inv ((K.sc' i j k).homologyι (cycleClass _ x)) = _
  rw [cycleClass_opcycles]
  exact congrArg (fun f => f x.val) (K.pOpcycles_opcyclesIsoSc'_inv i j k hi hk)

/-- Actual homology-map naturality for concrete cycles with explicitly chosen adjacent degrees. -/
theorem represented_natural {c : ComplexShape ℕ} {K L : HomologicalComplex (ModuleCat.{0} ℚ) c}
    (f : K ⟶ L) (i j k : ℕ) (hi : c.prev j = i) (hk : c.next j = k)
    (x : Cycles (K.sc' i j k)) (y : Cycles (L.sc' i j k)) (hy : y.val = f.f j x.val) :
    homologyMap f j ((K.homologyIsoSc' i j k hi hk).inv (cycleClass _ x)) =
      (L.homologyIsoSc' i j k hi hk).inv (cycleClass _ y) := by
  apply (ModuleCat.mono_iff_injective (L.homologyι j)).mp inferInstance
  rw [represented_opcycles]
  change (homologyMap f j ≫ L.homologyι j) _ = _
  rw [homologyι_naturality]
  change opcyclesMap f j (K.homologyι j _) = _
  rw [represented_opcycles,hy]
  exact congrArg (fun g => g x.val) (p_opcyclesMap f j)

/-- Every actual cohomology class has a cycle representative for the cap constructor. -/
theorem cochainClass_surjective (C : CochainComplex (ModuleCat.{0} ℚ) ℕ) (a : ℕ) :
    Function.Surjective (Descent.cochainClass C a) := by
  intro z
  obtain ⟨x,hx⟩ := cycleClass_surjective (C.sc' (a-1) a (a+1))
    ((C.homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).hom z)
  refine ⟨x, ?_⟩
  unfold Descent.cochainClass
  rw [hx]
  exact congrArg (fun f => f z)
    (C.homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).hom_inv_id

/-- Every actual chain homology class has a cycle representative for the cap constructor. -/
theorem chainClass_surjective (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ) :
    Function.Surjective (Descent.chainClass K n) := by
  intro z
  obtain ⟨x,hx⟩ := cycleClass_surjective (K.sc' (n+1) n (n-1))
    ((K.homologyIsoSc' (n+1) n (n-1) (down_prev _) (down_next _)).hom z)
  refine ⟨x, ?_⟩
  unfold Descent.chainClass
  rw [hx]
  exact congrArg (fun f => f z)
    (K.homologyIsoSc' (n+1) n (n-1) (down_prev _) (down_next _)).hom_inv_id

/-- Actual cochain maps send a represented cohomology class to the class of its literal image. -/
theorem cochainClass_natural {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ} (f : C ⟶ D) (a : ℕ)
    (x : Cycles (C.sc' (a-1) a (a+1))) (y : Cycles (D.sc' (a-1) a (a+1)))
    (hy : y.val = f.f a x.val) :
    homologyMap f a (Descent.cochainClass C a x) = Descent.cochainClass D a y :=
  represented_natural f _ _ _ (up_prev _) (up_next _) x y hy

/-- Actual chain maps send a represented homology class to the class of its literal image. -/
theorem chainClass_natural {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L) (n : ℕ)
    (x : Cycles (K.sc' (n+1) n (n-1))) (y : Cycles (L.sc' (n+1) n (n-1)))
    (hy : y.val = f.f n x.val) :
    homologyMap f n (Descent.chainClass K n x) = Descent.chainClass L n y :=
  represented_natural f _ _ _ (down_prev _) (down_next _) x y hy

end TernaryPoly.SingularLocalCompactCap.Algebra
