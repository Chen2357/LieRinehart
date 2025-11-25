import Mathlib.Algebra.Lie.DirectSum

open DirectSum

variable (A L : Type*) (ι : Type*)  (β : ι → Type*)
variable [LieRing L] [DecidableEq ι]
variable [∀ i, AddCommGroup (β i)] [∀ i, LieRingModule L (β i)]

@[simp]
theorem bracket_of (x : L) {n : ι} (y : β n) :
    ⁅x, of _ _ y⁆ = of _ _ ⁅x, y⁆ := by
  ext i
  simp
  by_cases h : i = n
  · rw [h]
    simp
  . simp [of_eq_of_ne _ _ _ h]
