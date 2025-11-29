import LieRinehart.Basic

variable (R A : Type*)
variable [CommRing R] [CommRing A] [Algebra R A]

instance : LieRinehartPair A (Derivation R A A) where
  bracket x y := x y
  add_lie := by simp
  lie_add := by simp
  leibniz_lie := by simp [Bracket.bracket]
  lier_one := by simp
  lier_mul := by intros; simp; ring
  lier_smul := by intros; ext; simp [Bracket.bracket]; ring

instance : LieRingModule (Derivation R A A) A where
  add_lie := by simp
  lie_add := by simp
  leibniz_lie := by simp [Bracket.bracket]

instance : LieRinehartAlgebra R A (Derivation R A A) where
  smul_lie := by simp [Bracket.bracket]
  lie_smul := by simp [Bracket.bracket]

open LieRinehartModule

instance : IsTrivial A (Derivation R A A) A where
  smul_lier := by simp [Bracket.bracket]
