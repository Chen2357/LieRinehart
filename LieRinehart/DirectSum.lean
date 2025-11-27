import LieRinehart.Basic
import Mathlib.Algebra.Lie.DirectSum

open DirectSum
open LieRinehartModule

variable (A L : Type*) (ι : Type*) (β : ι → Type*)
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [∀ i, AddCommGroup (β i)] [∀ i, Module A (β i)] [∀ i, LieRingModule L (β i)] [∀ i, LieRinehartModule A L (β i)]

instance : LieRinehartModule A L (⨁ i, β i) where
  lier_smul' := by
    intros
    ext
    simp [smul_apply, lier_smul]

instance [∀ i, IsSemilinear A L (β i)] : IsSemilinear A L (⨁ i, β i) where
  smul_lier_smul := by
    intros
    ext
    simp [smul_apply]

instance [∀ i, IsTrivial A L (β i)] : IsTrivial A L (⨁ i, β i) where
  smul_lier := by
    intros
    ext
    simp [smul_apply]

@[simp]
private lemma LieRinehartModule.symbol_of [∀ i, IsSemilinear A L (β i)] (x : L) (a : A) (m : ⨁ i, β i) (i : ι) : symbol A L (⨁ i, β i) x a m i = symbol A L (β i) x a (m i) := by
  simp [symbol]
  rfl

instance [∀ i, IsLinear A L (β i)] : IsLinear A L (⨁ i, β i) where
  symbol_smul := by
    intros
    ext
    simp [smul_apply]
