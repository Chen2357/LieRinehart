import LieRinehart.Basic
import Mathlib.Algebra.Lie.DirectSum

open DirectSum
variable (A L : Type*) (ι : Type*)  (β : ι → Type*)
variable [CommRing A] [LieRing L]
variable [∀ i, AddCommGroup (β i)] [∀ i, Module A (β i)] [∀ i, LieRingModule L (β i)]

instance [LieRinehartPair A L] [∀ i, NoContrLRModule A L (β i)] :
  NoContrLRModule A L (⨁ i, β i) where
  lier_smul x a f := by
    ext
    simp [smul_apply, lier_smul]

instance [DecidableEq ι] [LRAlgebra A L] [∀ i, LRModule A L (β i)] : LRModule A L (⨁ i, β i) :=
  let contr₁ (α : L →ₗ[A] A) (x : L) : (⨁ i, β i) →ₗ[A] (⨁ i, β i) := toModule A ι _ <| fun i => lof A ι _ i ∘ₗ contr A L (β i) α x
  let contr₂ (α : L →ₗ[A] A) : L →ₗ[A] (⨁ i, β i) →ₗ[A] (⨁ i, β i) := {
    toFun x := contr₁ α x
    map_add' := by intros; ext; simp [contr₁]
    map_smul' := by intros; ext; simp [contr₁]
  }
  let contr₃ : (L →ₗ[A] A) →ₗ[A] L →ₗ[A] (⨁ i, β i) →ₗ[A] (⨁ i, β i) := {
    toFun α := contr₂ α
    map_add' := by intros; ext; simp [contr₂, contr₁]
    map_smul' := by intros; ext; simp [contr₂, contr₁]
  }
  {
    contr := contr₃
    smul_lier := by
      intros α x f
      induction f using DirectSum.induction_on
      case zero => simp
      case of i m =>
        ext j
        simp [contr₃, contr₂, contr₁, ←lof_eq_of A, smul_lier, smul_apply]
        by_cases h : i = j
        . rw [←h]
          simp
        . simp [lof_eq_of, of_eq_of_ne _ _ _ (Ne.symm h)]
      case add f₁ f₂ ih₁ ih₂ =>
        simp [map_add, ih₁, ih₂]
        abel
  }
