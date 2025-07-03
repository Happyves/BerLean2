
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

#check 1

-- #synth Field Float


-- #eval dist (1 : ℚ) 2


#check Float
#check ℝ

#check Pow.pow

#check Float.ofNat
#check OfNat

set_option pp.all true in
#check (1 : Real)

#synth OfNat Real 1
#synth OfNat Float 2

#print instOfNatAtLeastTwo
#print instOfNatFloat

-- #synth NatCast Float
#synth NatCast Real

instance : NatCast Float where
  natCast := Float.ofNat

#synth NatCast Float

#synth HPow Real Nat Real
-- #synth HPow Float Nat Float

instance : HPow Float Nat Float :=
  let rec go (x : Float) : Nat → Float
    | 0 => 1
    | n+1 => x*(go x n)
  ⟨go⟩

#synth HPow Float Nat Float


def F (S : Type) [Add S] [Sub S] [Mul S] [NatCast S] [HPow S Nat S] (x : S) :=
  2*x^2 - 4*x + 5


#eval F Float 0
#eval F Float 1
#eval F Float 2
#eval F Float 2.3e-1

#eval F ℚ 0
#eval F ℚ 1
#eval F ℚ 2
#eval F ℚ (23 / 100)



-- 2*(x-1)^2 + 3 = 2*x^2 -4*x +5

#check 1
/-

(2*(y-1)^2 + 3) - (2*(x-1)^2 + 3) ≥ (4*(x-1))*(y - x)
(y-1)^2 - (x-1)^2 ≥ (2*(x-1))*(y - x)
(y-1)^2 - (x-1)^2 ≥ (2*(x-1))*((y-1) - (x-1))
u^2 - v^2 ≥ (2*v)*(u - v)
(u - v)*(u + v) ≥ (2*v)*(u - v)
if u = v → 0 ≥ 0
if u > v → (c)
  u+v ≥ 2*v
  v+v ≥ 2*v by (c) and trans
if u < v → (c)
  u+v ≤ 2*v
  v+v ≤ 2*v by (c) and trans

Subgradient x ↦ 2*(x-1)
-/


def SubgradientDescent
  {S : Type} [Sub S] [Mul S]
  (Objective : S → S)
  (init : S)
  (StepSize : ℕ → S)
  (Subgradients : S → S)
  : ℕ → S
  | 0 => init
  | n + 1 =>
      let sofar := SubgradientDescent Objective init StepSize Subgradients n
      sofar - (StepSize n) * (Subgradients sofar)

-- #exit
#eval SubgradientDescent (F Float) 5 (fun n => 1 / (n+1)) (fun x => 2*(x-1)) 0
#eval SubgradientDescent (F Float) 5 (fun n => 1 / (n+1)) (fun x => 2*(x-1)) 1
#eval SubgradientDescent (F Float) 5 (fun n => 1 / (n+1)) (fun x => 2*(x-1)) 2
#eval SubgradientDescent (F Float) 5 (fun n => 1 / (n+1)) (fun x => 2*(x-1)) 3
#eval SubgradientDescent (F Float) 5 (fun n => 1 / (n+1)) (fun x => 2*(x-1)) 10


#eval SubgradientDescent (F Float) 10.42 (fun n => 1 / (n+3)) (fun x => 2*(x-1)) 0
#eval SubgradientDescent (F Float) 10.42 (fun n => 1 / (n+3)) (fun x => 2*(x-1)) 1
#eval SubgradientDescent (F Float) 10.42 (fun n => 1 / (n+3)) (fun x => 2*(x-1)) 2
#eval SubgradientDescent (F Float) 10.42 (fun n => 1 / (n+3)) (fun x => 2*(x-1)) 3
#eval SubgradientDescent (F Float) 10.42 (fun n => 1 / (n+3)) (fun x => 2*(x-1)) 10
#eval SubgradientDescent (F Float) 10.42 (fun n => 1 / (n+3)) (fun x => 2*(x-1)) 20
#eval SubgradientDescent (F Float) 10.42 (fun n => 1 / (n+3)) (fun x => 2*(x-1)) 30


-- Follows "Convex Optimisation algorithms" by Bertsekas, chapter 3.2



theorem Bounds
  (Objective : ℝ → ℝ) (init : ℝ) (StepSize : ℕ → ℝ) (Subgradients : ℝ → ℝ)
  (posSteps : ∀ i, StepSize i > 0)
  (subgradientProp : ∀ x, ∀ y, Objective x - Objective y ≤ Subgradients x * (x - y))
  (y : ℝ) (n : ℕ) :
    let nth := SubgradientDescent Objective init StepSize Subgradients
    (nth (n+1) - y)^2 ≤ (nth n - y)^2 - 2*(StepSize n)*(Objective (nth n) - Objective y) + (StepSize n)^2 * (Subgradients (nth n))^2 :=
    by
    intro nth
    calc
      (nth (n+1) - y)^2 ≤ (nth n - (StepSize n) * (Subgradients (nth n)) - y)^2 := by
        dsimp only [nth]
        dsimp only [SubgradientDescent]
        apply le_refl
      _ = (nth n - y)^2 - 2*(StepSize n)*(Subgradients (nth n))*((nth n) -  y) + (StepSize n)^2 * (Subgradients (nth n))^2 := by
        rw [sub_sub]
        rw [add_comm]
        rw [← sub_sub]
        rw [sub_pow_two]
        rw [mul_pow]
        congr 2
        calc
          2 * (nth n - y) * (StepSize n * Subgradients (nth n)) = 2 * ((StepSize n * Subgradients (nth n)) * (nth n - y)) := by
            rw [mul_assoc]
            nth_rewrite 2 [mul_comm]
            rfl
          _ = 2 * StepSize n * Subgradients (nth n) * (nth n - y) := by
            rw [← mul_assoc]
            rw [← mul_assoc]
      _ ≤ (nth n - y)^2 - 2*(StepSize n)*(Objective (nth n) - Objective y) + (StepSize n)^2 * (Subgradients (nth n))^2 := by
        apply add_le_add_right
        apply sub_le_sub_left
        nth_rewrite 2 [mul_assoc]
        rw [mul_le_mul_left]
        swap
        · rw [mul_pos_iff_of_pos_left]
          · apply posSteps
          · exact zero_lt_two
        · apply subgradientProp


example (f : ℝ → ℝ) (x₀ : ℝ) (s : ℕ → ℝ) (δ : ℝ → ℝ)
  (posSteps : ∀ i, s i > 0)
  (subgradientProp : ∀ x, ∀ y, f x - f y ≤ δ x * (x - y))
  (y : ℝ) (n : ℕ) :
    let x := SubgradientDescent f x₀ s δ
    (x (n+1) - y)^2 ≤ (x n - y)^2 - 2*(s n)*(f (x n) - f y) + (s n)^2 * (δ (x n))^2 :=
    by
    intro x
    calc
      (x (n+1) - y)^2 ≤ (x n - (s n) * (δ (x n)) - y)^2 := by
        simp [x, SubgradientDescent]
      _ = (x n - y)^2 - 2*(s n)*(δ (x n))*((x n) -  y) + (s n)^2 * (δ (x n))^2 := by
        ring
      _ ≤ (x n - y)^2 - 2*(s n)*(f (x n) - f y) + (s n)^2 * (δ (x n))^2 := by
        apply add_le_add_right
        apply sub_le_sub_left
        nth_rewrite 2 [mul_assoc]
        rw [mul_le_mul_left]
        swap
        · rw [mul_pos_iff_of_pos_left]
          · apply posSteps
          · exact zero_lt_two
        · apply subgradientProp


theorem ItDoesGoDown
  (f : ℝ → ℝ) (x₀ : ℝ) (s : ℕ → ℝ) (δ : ℝ → ℝ)
  (posSteps : ∀ i, s i > 0)
  (subgradientProp : ∀ x, ∀ y, f x - f y ≤ δ x * (x - y))
  (min : ℝ)
  -- (minIsMin: ∀ x, f min ≤ f x) isn't necessary : it is implied by `convenientSteps` for the iterates
  (n : ℕ)
  (convenientSteps :
      let x := SubgradientDescent f x₀ s δ
      s n < (2* (f (x n) - f min)) / (δ (x n))^2)
  (also :
    let x := SubgradientDescent f x₀ s δ
    δ (x n) ≠ 0):
    let x := SubgradientDescent f x₀ s δ
    ((x (n+1)) - min)^2 < ((x n) - min)^2 := by
      intro x
      have reminder := Bounds f x₀ s δ posSteps subgradientProp min n
      apply lt_of_le_of_lt reminder
      calc
        (x n - min) ^ 2 - 2 * s n * (f (x n) - f min) + s n ^ 2 * δ (x n) ^ 2 = (x n - min) ^ 2 - (2 * s n * (f (x n) - f min) - s n ^ 2 * δ (x n) ^ 2) := by
          ring
        _ < (x n - min) ^ 2 := by
          apply sub_lt_self
          rw [sub_pos]
          rw [show 2 * s n = s n * 2 by rw [mul_comm]]
          rw [pow_two]
          rw [mul_assoc, mul_assoc]
          rw [mul_lt_mul_left]
          swap
          · apply posSteps
          · dsimp at convenientSteps
            rw [div_eq_inv_mul] at convenientSteps
            rw [lt_inv_mul_iff₀'] at convenientSteps
            swap
            · apply sq_pos_of_ne_zero
              exact also
            · exact convenientSteps






-- # Appendix


def SubgradientDescentTR
  {S : Type} [Sub S] [Mul S]
  (Objective : S → S)
  (init : S)
  (StepSize : S)
  (Subgradients : S → S)
  : ℕ → S
  | 0 => init
  | n + 1 =>
      let next := init - (StepSize) * (Subgradients init)
      SubgradientDescentTR Objective next StepSize Subgradients n


example
  {S : Type} [Sub S] [Mul S]
  (Objective : S → S)
  (init : S)
  (StepSize :  S)
  (Subgradients : S → S)
  (n : Nat) :
    let nth := SubgradientDescentTR Objective init StepSize Subgradients
    (nth (n+1)) = (nth n) - (StepSize) * (Subgradients (nth n)) := by
    revert init
    induction' n with n ih
    · intro _
      dsimp!
    · intro init
      dsimp
      rw [SubgradientDescentTR.eq_2]
      apply ih
