import LieRinehart.Basic

open LieRinehartModule

variable (A L M N : Type*)
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M] [LieRinehartModule A L M]
variable [AddCommGroup N] [Module A N] [LieRingModule L N] [LieRinehartModule A L N]

instance : LieRingModule L (M →ₗ[A] N) where
  bracket x f := {
    toFun m := ⁅x, f m⁆ - f ⁅x, m⁆
    map_add' := by intros; simp [lie_add]; abel
    map_smul' := by intros; simp [lier_smul, smul_sub]
  }
  add_lie := by intros; ext; simp; abel
  lie_add := by intros; ext; simp; abel
  leibniz_lie := by intros; ext; simp; abel

instance : LieRinehartModule A L (M →ₗ[A] N) where
  lier_smul' := by
    intros
    ext
    simp [Bracket.bracket, lier_smul, smul_sub]
    abel

instance [IsSemilinear A L N] : IsSemilinear A L (M →ₗ[A] N) where
  smul_lier_smul := by
    intros
    ext
    simp

instance [IsTrivial A L M] [IsTrivial A L N] : IsTrivial A L (M →ₗ[A] N) where
  smul_lier := by
    intros
    ext
    simp [Bracket.bracket, smul_sub]

@[simp]
private lemma LieRinehartModule.symbol_apply  [IsSemilinear A L M] [IsSemilinear A L N] (x : L) (a : A) (f : M →ₗ[A] N) (m : M) :
  symbol A L (M →ₗ[A] N) x a f m = symbol A L N x a (f m) - f (symbol A L M x a m) := by
  simp [symbol, Bracket.bracket, smul_sub]
  abel

instance [IsLinear A L M] [IsLinear A L N] : IsLinear A L (M →ₗ[A] N) where
  symbol_smul := by
    intros
    ext
    simp [smul_sub]
