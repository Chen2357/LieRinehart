import Mathlib.LinearAlgebra.Alternating.Curry

namespace AlternatingMap

section AddCommMonoid

variable {R} [CommSemiring R]
variable {M} [AddCommMonoid M] [Module R M]
variable {N} [AddCommMonoid N] [Module R N]
variable {n : ℕ}

@[simp]
def uncurryLeft'
  (f : M →ₗ[R] (M [⋀^Fin (n)]→ₗ[R] N))
  (h : ∀ v : Fin n → M, ∀ k : Fin (n), f (v k) v = 0) :
  (M [⋀^Fin (n+1)]→ₗ[R] N) := mk ((toMultilinearMapLM ∘ₗ f).uncurryLeft) <| by
    intro v i j hv hij
    cases i using Fin.cases
    case zero =>
      simp
      cases j using Fin.cases
      case zero => contradiction
      case succ j =>
        rw [hv]
        have : (v j.succ) = Fin.tail v j := rfl
        rw [this]
        exact h (Fin.tail v) j
    case succ i =>
      have : (v i.succ) = Fin.tail v i := rfl
      rw [this] at hv
      cases j using Fin.cases
      case zero =>
        simp
        rw [←hv]
        exact h (Fin.tail v) i
      case succ j =>
        have : (v j.succ) = Fin.tail v j := rfl
        rw [this] at hv
        apply map_eq_zero_of_eq _ _ hv
        intro heq
        apply hij
        rw [heq]

@[simp]
theorem curryLeft_map_eq_zero
  (f : M [⋀^Fin (n+1)]→ₗ[R] N) (v : Fin n → M) (i : Fin n) :
  f.curryLeft (v i) v = 0 := by
  have : i.succ ≠ 0 := Fin.succ_ne_zero i
  apply map_eq_zero_of_eq _ _ _ this
  rfl

@[simp]
theorem curryLeft_map_tail
  (f : M [⋀^Fin (n+1)]→ₗ[R] N) (v : Fin (n+1) → M) :
  f.curryLeft (v 0) (Fin.tail v) = f v := by
  simp [Matrix.vecCons]

theorem eq_of_IsEmpty
  {ι : Type*} [e : IsEmpty ι]
  (f g : M [⋀^ι]→ₗ[R] N)
  (h : f e.elim = g e.elim) :
  f = g := by
  ext v
  have : v = e.elim := by
    ext i
    exfalso
    exact e.elim i
  rw [this, h]

theorem eq_zero_of_IsEmpty
  {ι : Type*} [e : IsEmpty ι]
  (f : M [⋀^ι]→ₗ[R] N)
  (h : f e.elim = 0) :
  f = 0 := eq_of_IsEmpty _ _ h

theorem eq_of_curryLeft
  (f g : M [⋀^Fin (n+1)]→ₗ[R] N)
  (h : ∀ m : M, f.curryLeft m = g.curryLeft m) :
  f = g := by
  ext v
  rw [←curryLeft_map_tail f v, ←curryLeft_map_tail g v, h (v 0)]

theorem eq_zero_of_curryLeft
  (f : M [⋀^Fin (n+1)]→ₗ[R] N)
  (h : ∀ m : M, f.curryLeft m = 0) :
  f = 0 := by
  ext v
  rw [←curryLeft_map_tail f v, h (v 0)]
  rfl

end AddCommMonoid

section AddCommGroup

variable {R} [CommSemiring R]
variable {M} [AddCommMonoid M] [Module R M]
variable {N} [AddCommGroup N] [Module R N]
variable {n : ℕ}

@[simp]
def uncurryLeft
  (f : M →ₗ[R] (M [⋀^Fin (n)]→ₗ[R] N))
  (h : match n with
    | 0 => True
    | _ + 1 => ∀ m : M, (f m).curryLeft m = 0) :
  (M [⋀^Fin (n+1)]→ₗ[R] N) := uncurryLeft' f <| by
    cases n
    case zero => simp
    case succ n =>
      simp at h
      intro v i
      cases i using Fin.cases
      case zero =>
        rw [←curryLeft_map_tail, h]
        simp
      case succ i =>
        apply neg_eq_zero.mp
        have : i.succ ≠ 0 := Fin.succ_ne_zero i
        rw [←map_swap _ _ this, ←curryLeft_map_tail]
        simp [-curryLeft_apply_apply, h]

@[simp]
theorem curryLeft_anticomm
  (f : M [⋀^Fin (n+2)]→ₗ[R] N) (m1 m2 : M):
  (f.curryLeft m1).curryLeft m2 + (f.curryLeft m2).curryLeft m1 = 0 := by
  calc
  _ = (f.curryLeft (m1 + m2)).curryLeft (m1 + m2)
    - (f.curryLeft m1).curryLeft m1
    - (f.curryLeft m2).curryLeft m2
    := by simp
  _ = 0 := by simp only [curryLeft_same]; abel

theorem curryLeft_skew
  (f : M [⋀^Fin (n+2)]→ₗ[R] N) (m1 m2 : M):
  (f.curryLeft m1).curryLeft m2 = -(f.curryLeft m2).curryLeft m1 := by
  apply add_eq_zero_iff_eq_neg.mp
  apply curryLeft_anticomm

@[simp]
theorem curryLeft_uncurryLeft
  (f : M →ₗ[R] (M [⋀^Fin (n)]→ₗ[R] N))
  (h : match n with
    | 0 => True
    | _ + 1 => ∀ m : M, (f m).curryLeft m = 0) :
  (uncurryLeft f h).curryLeft = f := by
  ext m v
  simp [uncurryLeft, uncurryLeft', Matrix.vecCons]

end AddCommGroup
