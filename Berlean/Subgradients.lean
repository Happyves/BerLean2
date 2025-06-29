
import Mathlib.Data.Real.Basic

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

#synth NatCast Float
#synth NatCast Real

instance : NatCast Float where
  natCast := Float.ofNat

#synth NatCast Float

#synth HPow Real Nat Real
#synth HPow Float Nat Float

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
      let next := init - (StepSize n) * (Subgradients init)
      SubgradientDescent Objective next StepSize Subgradients n


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

#check 1

theorem SubgradientDescentStep
  {S : Type} [Sub S] [Mul S]
  (Objective : S → S) (init : S) (StepSize : ℕ → S) (Subgradients : S → S)
  (n : ℕ) :
    let nth := SubgradientDescent Objective init StepSize Subgradients
    nth (n+1) = nth n - (StepSize n)*(Subgradients (nth n))
    := by
      dsimp
      rw [SubgradientDescent.eq_2]
      have gen :
        ∀ s, SubgradientDescent Objective (init - s) StepSize Subgradients n =
        SubgradientDescent Objective init StepSize Subgradients n - s := by
          induction' n with n ih
          · intro s
            dsimp!
          · intro s
            dsimp!

#exit
theorem Bounds
  (Objective : ℝ → ℝ) (init : ℝ) (StepSize : ℕ → ℝ) (Subgradients : ℝ → ℝ)
  (y : ℝ) (n : ℕ) :
    let nth := SubgradientDescent Objective init StepSize Subgradients
    (nth (n+1) - y)^2 ≤ (nth n - y)^2 - 2*(StepSize n)*(Objective (nth n) - Objective y) + (StepSize n)^2 * (Subgradients (nth n))^2 :=
    by
    intro nth
    calc
      (nth (n+1) - y)^2 ≤ (nth n - (StepSize n) * (Subgradients n) - y)^2 := by
        --dsimp only [nth, SubgradientDescent]
        sorry
      _ = (nth n - y)^2 - 2*(StepSize n)*(Subgradients (nth n))*((nth n) -  y) + (StepSize n)^2 * (Subgradients (nth n))^2 := by
        sorry
      _ ≤ (nth n - y)^2 - 2*(StepSize n)*(Objective (nth n) - Objective y) + (StepSize n)^2 * (Subgradients (nth n))^2 := by
        sorry
