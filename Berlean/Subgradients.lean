
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set Filter Topology

instance : NatCast Float where
  natCast := Float.ofNat

instance : HPow Float Nat Float :=
  let rec go (x : Float) : Nat → Float
    | 0 => 1
    | n+1 => x*(go x n)
  ⟨go⟩



-- # Subgradient descent

/-
This is a minimalist exposition of how one can do scientific computing in Lean.
For a proper scientific computing library in Lean, consult Tomáš Skřivan's SciLean
(https://lecopivo.github.io/scientific-computing-lean/)

We follow the exposition of chapter 3.2 of "Convex Optimization Algorithms" by Bertsekas.
-/

-- We want to minimise the following function
def F (S : Type) [Add S] [Sub S] [Mul S] [NatCast S] [HPow S Nat S] (x : S) :=
  2*x^2 - 4*x + 5

-- We can minmise it over floats
#eval F Float 0
#eval F Float 1
#eval F Float 2
#eval F Float 2.3e-1

-- Or over rationals !
#eval F ℚ 0
#eval F ℚ 1
#eval F ℚ 2
#eval F ℚ (23 / 100)

-- It even has a meaning for matrices!
#eval F (Matrix (Fin 2) (Fin 2) ℕ) !![0,1 ; 2,3]


/-
We'll study `F` over ℝ.
Assume we don't remember the following from highschool
-/
theorem canonical (x : ℝ) : 2*x^2 -4*x +5 = 2*(x-1)^2 + 3 := by
  nth_rewrite 2 [pow_two]
  rw [mul_sub_left_distrib]
  rw [mul_sub_right_distrib]
  rw [mul_one]
  rw [one_mul]
  rw [sub_sub]
  rw [add_sub]
  rw [← two_mul]
  rw [mul_sub]
  rw [mul_sub]
  rw [mul_one]
  rw [← pow_two]
  rw [← mul_assoc]
  rw [sub_add]
  rw [sub_add]
  congr 1
  rw [sub_sub]
  congr 1
  · rw [show (4 : ℝ) = 2*2  by norm_num]
  · norm_num


theorem withAutomation (x : ℝ) : 2*x^2 -4*x +5 = 2*(x-1)^2 + 3 := by
  ring

#print canonical
#print withAutomation

/- We'll use the following algorithm to find the minimum-/
def SubgradientDescent
  {S : Type} [Sub S] [Mul S]
  --(Objective : S → S) the function we want to minimise (isn't actually needed)
  (init : S) -- the initial point
  (StepSize : ℕ → S) -- we'll takes steps towards the minimum : this regulates their size
  (Subgradients : S → S) -- a mystirious oracle that tells us in which direction to take steps
  : ℕ → S -- as final input, we take the number of iterations, and we output the minimser candidate
  | 0 => init
  | n + 1 =>
      let sofar := SubgradientDescent init StepSize Subgradients n
      -- We compute the nth point ↑ with a recursive call, and return the step taken ↓
      sofar - (StepSize n) * (Subgradients sofar)




-- converges to minimiser
#eval SubgradientDescent (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 0
#eval SubgradientDescent (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 1
#eval SubgradientDescent (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 2
#eval SubgradientDescent (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 3
#eval SubgradientDescent (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 4
#eval SubgradientDescent (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 5
#eval SubgradientDescent (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 10
#eval SubgradientDescent (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 20
#eval SubgradientDescent (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 30

-- convergence speed depends of the stepsize
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 0
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 1
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 2
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 3
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 4
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 5
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 6
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 10
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 20
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 50
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 60
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 70

--converges, but not to minimiser
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^3) (fun x => 4*(x-1)) 0
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^3) (fun x => 4*(x-1)) 1
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^3) (fun x => 4*(x-1)) 2
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^3) (fun x => 4*(x-1)) 3
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^3) (fun x => 4*(x-1)) 10
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^3) (fun x => 4*(x-1)) 20
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^3) (fun x => 4*(x-1)) 30
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^3) (fun x => 4*(x-1)) 50

-- We can also use constant step sizes
#eval SubgradientDescent  (5 : Float) (fun _ => 1 / 42) (fun x => 4*(x-1)) 0
#eval SubgradientDescent  (5 : Float) (fun _ => 1 / 42) (fun x => 4*(x-1)) 1
#eval SubgradientDescent  (5 : Float) (fun _ => 1 / 42) (fun x => 4*(x-1)) 2
#eval SubgradientDescent  (5 : Float) (fun _ => 1 / 42) (fun x => 4*(x-1)) 3
#eval SubgradientDescent  (5 : Float) (fun _ => 1 / 42) (fun x => 4*(x-1)) 10
#eval SubgradientDescent  (5 : Float) (fun _ => 1 / 42) (fun x => 4*(x-1)) 20
#eval SubgradientDescent  (5 : Float) (fun _ => 1 / 42) (fun x => 4*(x-1)) 70

-- This one seems to diverge !
#eval SubgradientDescent  (5 : Float) (fun _ => 1) (fun x => 4*(x-1)) 0
#eval SubgradientDescent  (5 : Float) (fun _ => 1) (fun x => 4*(x-1)) 1
#eval SubgradientDescent  (5 : Float) (fun _ => 1) (fun x => 4*(x-1)) 2
#eval SubgradientDescent  (5 : Float) (fun _ => 1) (fun x => 4*(x-1)) 3
#eval SubgradientDescent  (5 : Float) (fun _ => 1) (fun x => 4*(x-1)) 10
#eval SubgradientDescent  (5 : Float) (fun _ => 1) (fun x => 4*(x-1)) 20
#eval SubgradientDescent  (5 : Float) (fun _ => 1) (fun x => 4*(x-1)) 70

-- We'll prove a little theorem that gives us conditions on the step size to yield convergence

-- A lemma
theorem Bounds
  (Objective : ℝ → ℝ) (init : ℝ) (StepSize : ℕ → ℝ) (Subgradients : ℝ → ℝ)
  (posSteps : ∀ i, StepSize i > 0)
  (subgradientProp : ∀ x, ∀ y, Objective x - Objective y ≤ Subgradients x * (x - y))
  -- ↑ is the property about so-called "subgradients" that makes subgradient descent work !
  -- It' usually states as `Objective y - Objective x ≥ Subgradients x * (y - x)` though
  (y : ℝ) (n : ℕ) :
    let nth := SubgradientDescent init StepSize Subgradients
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


-- Our `F` admits subgradients
theorem SubgradientForF (x y : ℝ) : (2*(y-1)^2 + 3) - (2*(x-1)^2 + 3) ≥ (4*(x-1))*(y - x) := by
  have help_1 : (2*(y-1)^2 + 3) - (2*(x-1)^2 + 3) = 2*((y-1)^2 - (x-1)^2 ) := by
    ring
  rw [help_1]
  clear help_1
  rw [mul_assoc]
  rw [show (4 : ℝ) = 2*2  by norm_num]
  rw [mul_assoc]
  rw [ge_iff_le]
  rw [mul_le_mul_left (show 0 < (2 : ℝ)  by norm_num)]
  rw [show y - x = (y-1) - (x-1) by ring]
  set u := x-1
  set v := y - 1
  rw [sq_sub_sq]
  rw [← mul_assoc]
  have h := lt_trichotomy u v
  cases h with
    | inl h =>
        rw [← sub_pos] at h
        rw [mul_le_mul_right h]
        rw [sub_pos] at h
        rw [two_mul]
        apply add_le_add_right
        apply le_of_lt
        exact h
    | inr h =>
        cases h with
          | inl h =>
              rw [h]
              rw [sub_self]
              rw [mul_zero]
              rw [mul_zero]
          | inr h =>
              rw [← sub_neg] at h
              rw [mul_le_mul_right_of_neg h]
              rw [sub_neg] at h
              rw [two_mul]
              apply add_le_add_right
              apply le_of_lt
              exact h


-- Same as `Bounds`, but with shorter notation and more automation
example (f : ℝ → ℝ) (x₀ : ℝ) (s : ℕ → ℝ) (δ : ℝ → ℝ)
  (posSteps : ∀ i, s i > 0)
  (subgradientProp : ∀ x, ∀ y, f x - f y ≤ δ x * (x - y))
  (y : ℝ) (n : ℕ) :
    let x := SubgradientDescent x₀ s δ
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
  --  (minIsMin:
  --      let x := SubgradientDescent x₀ s δ
  --      ∀ n, f min ≤ f (x n))
  -- ↑ isn't necessary : it is implied by `convenientSteps` just below
  -- (but it's in Proposition 3.2.2(b) in our source :P)
  (n : ℕ)
  (convenientSteps :
      let x := SubgradientDescent x₀ s δ
      s n < (2* (f (x n) - f min)) / (δ (x n))^2)
  (also :
    let x := SubgradientDescent x₀ s δ
    δ (x n) ≠ 0):
    let x := SubgradientDescent x₀ s δ
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
  (init : S)
  (StepSize : ℕ → S) -- should be increasing!
  (Subgradients : S → S)
  : ℕ → S
  | 0 => init
  | n + 1 =>
      let next := init - (StepSize n) * (Subgradients init)
      SubgradientDescentTR next StepSize Subgradients n

-- Difference not really noticable for few iterations
#eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 9001
#eval SubgradientDescentTR  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 9001


-- #eval SubgradientDescent  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 90000000

-- But ↑ overflows on my machine, whereas ↓ just takes ages

-- #eval SubgradientDescentTR  (5 : Float) (fun n => 1 / (n+1)^(1/4)) (fun x => 4*(x-1)) 90000000


/-
Side effect is that step-size get's indexed "in reverse".

For example, for 3 iterations we have
3 : init → init - (StepSize 2) * (Subgradients init)
2 : ⋯ → init - (StepSize 2) * (Subgradients init) - (StepSize 1) * (Subgradients ⋯)
1 : ⋯ → init - (StepSize 2) * (Subgradients init) - (StepSize 1) * (Subgradients ⋯) - (StepSize 0) * (Subgradients ⋯)
-/


#eval SubgradientDescentTR  (10.42 : Float) (fun n => (1/9)*(n-1)) (fun x => 4*(x-1)) 10
#eval SubgradientDescentTR  (10.42 : Float) (fun n => (1/19)*(n-1)) (fun x => 4*(x-1)) 20
#eval SubgradientDescentTR  (10.42 : Float) (fun n => (1/29)*(n-1)) (fun x => 4*(x-1)) 30
#eval SubgradientDescentTR  (10.42 : Float) (fun n => (1/30)*(n-1)) (fun x => 4*(x-1)) 31
#eval SubgradientDescentTR  (10.42 : Float) (fun n => (1/31)*(n-1)) (fun x => 4*(x-1)) 32
#eval SubgradientDescentTR  (10.42 : Float) (fun n => (1/32)*(n-1)) (fun x => 4*(x-1)) 33
#eval SubgradientDescentTR  (10.42 : Float) (fun n => (1/33)*(n-1)) (fun x => 4*(x-1)) 34


-- This also affects proofs we want to do about the function
example
  {S : Type} [Sub S] [Mul S]
  (init : S)
  (StepSize :  Nat → S)
  (Subgradients : S → S)
  (n : Nat) :
    let nth := SubgradientDescentTR init StepSize Subgradients
    let nth' := SubgradientDescentTR init (fun n => StepSize (n+1)) Subgradients
    (nth (n+1)) = (nth' n) - (StepSize 0) * (Subgradients (nth' n)) := by
    revert init
    induction' n with n ih
    · intro _
      dsimp!
    · intro init
      dsimp
      rw [SubgradientDescentTR.eq_2]
      nth_rewrite 2 [SubgradientDescentTR.eq_2]
      nth_rewrite 2 [SubgradientDescentTR.eq_2]
      apply ih



-- # Appendix of the appendix

-- Alternative Tail recursive version

def SubgradientDescentTR2
  {S : Type} [Sub S] [Mul S]
  (init : S)
  (StepSize : ℕ → S) -- should be increasing!
  (Subgradients : S → S)
  (iterations : ℕ) : S :=
  let rec go (init : S) : ℕ → S
    | 0 => init
    | n + 1 =>
        let next := init - (StepSize (iterations - (n+1))) * (Subgradients init)
        go next n
  go init iterations




#eval SubgradientDescentTR2  (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 0
#eval SubgradientDescentTR2  (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 1
#eval SubgradientDescentTR2  (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 2
#eval SubgradientDescentTR2  (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 3
#eval SubgradientDescentTR2  (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 4
#eval SubgradientDescentTR2  (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 5
#eval SubgradientDescentTR2  (10.42 : Float) (fun n => 1 / (n+1)) (fun x => 4*(x-1)) 10


example
  {S : Type} [Sub S] [Mul S]
  (init : S)
  (StepSize :  Nat → S)
  (Subgradients : S → S)
  (n : Nat) :
    let nth := SubgradientDescentTR2 init StepSize Subgradients
    (nth (n+1)) = (nth n) - (StepSize n) * (Subgradients (nth n)) := by
    dsimp
    unfold SubgradientDescentTR2
    have gen :
      ∀ m, ∀ init,
      SubgradientDescentTR2.go StepSize Subgradients (m + 1) init (n + 1) =
      SubgradientDescentTR2.go StepSize Subgradients m init n -
        StepSize m * Subgradients (SubgradientDescentTR2.go StepSize Subgradients m init n) := by
      induction' n with n ih
      · intro _ _
        rw [SubgradientDescentTR2.go.eq_2]
        rw [SubgradientDescentTR2.go.eq_1]
        rw [SubgradientDescentTR2.go.eq_1]
        rw [Nat.zero_add, Nat.succ_sub_one]
      · intro m init
        rw [SubgradientDescentTR2.go.eq_2]
        nth_rewrite 2 [SubgradientDescentTR2.go.eq_2]
        nth_rewrite 2 [SubgradientDescentTR2.go.eq_2]
        have help : (m + 1) - (n + 1 + 1) = m - (n+1) := by
          rw [Nat.succ_sub_succ]
        rw [help]
        apply ih
    apply gen
