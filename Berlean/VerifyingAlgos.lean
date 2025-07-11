
import Lean
import Mathlib.Data.Nat.Basic

open Lean Meta Elab Tactic


-- # Verifying algorithms vs. algorithms that certify

/-
This is a minimalist exposition of what it means to verify an algorithm in Lean and how
it differs from writing an algorithm that produces proofs.

We assume little to no prerequisites.
-/


-- ## Introduction to Lists

namespace Expo

universe u

-- This is how we define linked lists in Lean
inductive List (α : Type u) where
| nil
| cons (val : α) (nx : List α)
deriving Repr

/-
If you've never programmed before, here's a short explaℕion. The above are instructions
for your computer on how to store the entries of the list. `cons` will, given the adresses
of `val` and the remainder of the list `nx`, allocate new memory that contains the latter
adresses, at a new adress it returns. `nil` instructs that we hav reached the end of the list.

This definition makes use of type polymorphism : we use it to define lists of ℕural number,
integers, or even lists of lists.
-/

-- This is how we define the list 1,2,3
def OneTwoThree : List ℕ :=
  .cons 1 <| .cons 2 <| .cons 3 .nil

-- With polymorphism, we can define lists of lists
-- ↓ would be (1,2),(3)
example : List (List ℕ) :=
  .cons (.cons 1 <| .cons 2 .nil) <| .cons (.cons 3 .nil) .nil


def FourFive : List ℕ :=
  .cons 4 <| .cons 5 .nil

-- We define the length of the list as a function that takes a list and returns a ℕural number
def List.length {α : Type u} : List α → ℕ
  -- Since lisls are built from `cons` and `nil`, we have to specify what to do in each case
  | .nil => 0
    -- the empty list has length 0
  | .cons _ nx => 1 + nx.length
    -- for a list strating with `cons`, we recursivly compute the length of its remainder,
    -- and increment it by 1.

-- This command allows us to interpret code right away
#eval OneTwoThree.length
#eval FourFive.length

-- Here's how we append two list
def List.append {α : Type u} : List α → List α → List α
  | .nil, l => l
  | .cons val nx, l => .cons val <| append nx l

-- 1,2,3 and 4,5 yields 1,2,3,4,5
#eval List.append OneTwoThree FourFive

def OneToFive :=
  List.append OneTwoThree FourFive



-- Let's prove that the length of two appended lists is the sum of their lengths
theorem theoremName {α : Type u} (a b : List α) : (a.append b).length = a.length + b.length := by
  -- Click at the end of the lines of code and look at the "InfoView" to your right to follow along
  induction a with
  -- The proof is by induction on the list
    | nil => -- the base case
      -- Here, we show the result for empt lists
      rw [List.append.eq_1]
      rw [List.length.eq_1]
      rw [Nat.zero_add]
    | cons v l ih => -- the induction step
      -- Assume the result is true the the remainder of a list built with `cons` :
      -- we show that we may then derive the result for the list.
      rw [List.append.eq_2]
      rw [List.length.eq_2]
      rw [List.length.eq_2]
      rw [ih]
      rw [Nat.add_assoc]


-- Next up, we define what ot means for a list to be a prefix of another
inductive List.isPrefixOf {α : Type u}  : List α → List α → Prop where
  -- We give two rule from which we allow the relation to follow :
  | nilCase (l : List α) : List.isPrefixOf .nil l
      -- the empty list is the prefix of any list
  | consCase (val : α) {a b : List α} (proof : List.isPrefixOf a b) : List.isPrefixOf (.cons val a) (.cons val b)
      -- if two lists have the same lead, and the tail of the first is a prefix of that of the second
      -- the the first is a prefix of the second

-- With these rules, we can "build" proofs similarly to how we built lists
-- Here's a proof that 1,2,3 is a prefix of 1,2,3,4,5
theorem termStyleProof : OneTwoThree.isPrefixOf OneToFive :=
  .consCase 1 <| .consCase 2 <| .consCase 3 <| .nilCase FourFive


-- And now it's your turn
theorem isPrefixOf_append
  {α : Type u} (a b : List α) : a.isPrefixOf (a.append b) := by
    sorry



-- ## Verified Algorithms

-- This algorithm (function) returns true iff the firs input was a prefix of the second
def List.checkIsPrefixOf {α : Type u} [DecidableEq α] : List α → List α → Bool
  | .nil, _ => true
  | .cons val₁ l₁, .cons val₂ l₂ =>
      if val₁ = val₂ then l₁.checkIsPrefixOf l₂ else false
  | _, _ => false

-- Let's prove our claim, ie. the correctness of the algorithm
theorem algoVerified {α : Type u} [DecidableEq α] :
  ∀ l L : List α, l.checkIsPrefixOf L = true ↔ l.isPrefixOf L := by
    intro l
    induction l with
      | nil =>
        intro L
        dsimp [List.checkIsPrefixOf]
        constructor
        · intro _
          apply List.isPrefixOf.nilCase
        · intro _
          apply Eq.refl
      | cons val₁ nx₁ ih =>
        intro L
        cases L with
          | nil =>
            dsimp [List.checkIsPrefixOf]
            constructor
            · intro ohNo
              apply False.elim
              apply Bool.noConfusion ohNo
            · intro ohNo
              apply False.elim
              cases ohNo
          | cons val₂ nx₂ =>
            dsimp [List.checkIsPrefixOf]
            by_cases C : val₁ = val₂
            · rw [C]
              rw [if_pos (by apply Eq.refl)]
              constructor
              · intro h
                apply List.isPrefixOf.consCase
                specialize ih nx₂
                rw [← ih]
                exact h
              · intro h
                cases h with
                  | consCase _ h =>
                    specialize ih nx₂
                    rw [ih]
                    exact h
            · rw [if_neg C]
              constructor
              · -- we've seen this case before ; let's watch some automation in action
                simp
              · intro h
                cases h with
                  | consCase _ h =>
                    apply False.elim
                    apply C
                    apply Eq.refl


example {α : Type u} [DecidableEq α] :
  ∀ l L : List α, l.checkIsPrefixOf L = true ↔ l.isPrefixOf L := by
    intro l
    induction l with
      | nil =>
        grind [List.checkIsPrefixOf, List.isPrefixOf.nilCase]
      | cons val₁ nx₁ ih =>
        intro L
        cases L with
          | nil =>
            dsimp [List.checkIsPrefixOf]
            constructor
            · grind
            · intro ohNo
              apply False.elim
              cases ohNo
          | cons val₂ nx₂ =>
            dsimp [List.checkIsPrefixOf]
            by_cases C : val₁ = val₂
            · rw [C]
              rw [if_pos (by apply Eq.refl)]
              constructor
              · grind [List.isPrefixOf.consCase]
              · intro h
                cases h with
                  | consCase _ h =>
                    grind
            · rw [if_neg C]
              constructor
              · grind
              · intro h
                cases h with
                  | consCase _ h =>
                    grind


-- Again, we want to show that 1,2,3 is a prefix of 1,2,3,4,5
theorem viaVerified : OneTwoThree.isPrefixOf OneToFive := by
  rw [← algoVerified]
  -- we express this via the output of our algorithm
  apply Eq.refl
  -- The above says that the result holds by reflexivity of equality, but the sides aren't the same ?!
  -- When comparing expressions, Lean may "reduce" them, and in this case it amounts to computing the
  -- ouput of the algorithm, so that after the reduction, the goal is actually `true = true` which
  -- indeed follows from reflexivity.

#print viaVerified
-- The proofs are different !
#print termStyleProof



-- # Algorithms that certify


-- Writing proofs that a list is a prefix of another is so simple that it feels like it can be automated.
-- This can be done too ! Here, we look at look at the internal representation of lists, and build an
-- internal representation of a proof that `left` is a prefix of `right`
partial def tryProof (left right : Expr) : TacticM Expr := do
    -- We'll unfold the defintions of lists to get their value
    let left ← whnf left
    let right ← whnf right
    let (lh,largs) := left.getAppFnArgs
    if lh == `Expo.List.nil
    then -- if the `left` list is empty ...
      let proof ← mkAppM `Expo.List.isPrefixOf.nilCase #[right]
      -- ... return the rule that says empty lists are prefixes of any list
      return proof
    else
      let (_,rargs) := right.getAppFnArgs
      -- otherwise, build the proof for the tails of the lists ...
      let sofar ← tryProof largs[2]! rargs[2]!
      -- .. and use the other rule to extend the proof to the current lists
      let extend ← mkAppM `Expo.List.isPrefixOf.consCase #[largs[1]!, sofar]
      return extend


-- Here's how we get to run this "tactic"
elab "tryCertify" : tactic => do
  -- We get the goal that we're trying to prove
  let g ← getMainTarget
  let (h,args) := g.getAppFnArgs
  if h != `Expo.List.isPrefixOf
    -- This "tactic" only proves stuff about lists being prefixes: throw an error if it's misused
    then throwError "This tactic only works when the goal is a prefix relation !"
  let left := args[1]!
  let right := args[2]!
  let proof ← tryProof left right
  -- Build the proof and use it to solve the goal
  closeMainGoal `tryCertify proof

-- Here it is in action
theorem viaCertified : OneTwoThree.isPrefixOf OneToFive := by
  tryCertify

#print viaCertified
-- They're the same proof
#print termStyleProof


-- Now, we didn't check if the lists really were prefixes of one another, did we ?
-- What happens if we try to use the "tactic" to prove that 6 is a prefix of 1,2,3,4,5 ?
theorem ohNo : (List.cons 6 .nil).isPrefixOf OneToFive := by
  tryCertify
  -- The kernel rejects the proof !
  -- Is the kernel trustworthy ? You may want to look at Mario Carnerio's Lean4Lean at
  -- https://github.com/digama0/lean4lean


-- Finally, we'll make some adjustements to our tactic to illustrate a point
partial def tryHarderProof (left right : Expr) : TacticM (Expr × _root_.List MVarId) := do
    let left ← whnf left
    let right ← whnf right
    let (lh,largs) := left.getAppFnArgs
    if lh == `Expo.List.nil
    then
      let proof ← mkAppM `Expo.List.isPrefixOf.nilCase #[right]
      return (proof, [])
    else
      let (_,rargs) := right.getAppFnArgs
      let (sofar, nextGoals) ← tryHarderProof largs[2]! rargs[2]!
      let newGoalType ← mkAppM `Eq #[largs[1]!, rargs[1]!]
      let newGoal ← mkFreshExprMVar <| .some newGoalType
      let listType := newGoalType.getAppArgs[0]!
      withLocalDecl `dummy .default listType <| fun dummy => do
        let dummyRight ← mkAppM `Expo.List.cons #[dummy, rargs[2]!]
        let preMotive ← mkAppM `Expo.List.isPrefixOf #[left, dummyRight]
        let motive := Expr.lam `dummy listType (preMotive.abstract #[dummy]) .default
        let extend ← mkAppM `Expo.List.isPrefixOf.consCase #[largs[1]!, sofar]
        let final ← mkAppOptM `Eq.ndrec #[.none, largs[1]!, motive, extend, rargs[1]!, newGoal]
        return (final, newGoal.mvarId! :: nextGoals)

elab "tryCertifyHard" : tactic => do
  let g ← getMainTarget
  let (h,args) := g.getAppFnArgs
  if h != `Expo.List.isPrefixOf
    then throwError "This tactic only works when the goal is a prefix relation !"
  let left := args[1]!
  let right := args[2]!
  let (proof, newGoals) ← tryHarderProof left right
  (← getMainGoal).assign proof
  replaceMainGoal newGoals

-- This time, we want the "tactic" to give us the euqlity of list entries as sub-goals
example : OneTwoThree.isPrefixOf OneToFive := by
  tryCertifyHard
  · rfl
  · rfl
  · rfl

-- This is convenient for *interactive* theorem proving, since user doesn't have to
-- apply the routine `List.isPrefixOf.consCase` and `List.isPrefixOf.nilCase`, and
-- leaves parts of the proof that can't be done systematically to the user.
example (n m : ℕ) (h₁ : n + m = 42) (h₂ : m = n * 5) :
  (List.cons 42 <| .cons m .nil).isPrefixOf (.cons (n + m) <| .cons (5 * n) <| .cons 37 .nil) := by
  tryCertifyHard
  · rw [h₁]
  · rw [Nat.mul_comm]
    apply h₂



-- # Appendix : Verified algorithms that certify


inductive POption (β : Sort _) where
| none
| some (val : β)

def List.certifyIsPrefixOf {α : Type u} [DecidableEq α]
  : (l : List α) → (L : List α) → POption (l.isPrefixOf L)
  | .nil, _ => by
    apply POption.some
    apply List.isPrefixOf.nilCase
  | .cons val₁ l₁, .cons val₂ l₂ =>
      if h : val₁ = val₂
      then
        let nx := List.certifyIsPrefixOf l₁ l₂
        match nx with
        | .none => .none
        | .some proof =>
          by
          apply POption.some
          rw [h]
          apply List.isPrefixOf.consCase
          apply proof
      else .none
  | _, _ => .none

def POption.isSome {β : Sort _} : POption β → Bool
  | none => false
  | some _ => true


theorem verifiedCeritfied {α : Type u} [DecidableEq α] :
  ∀ l L : List α, (List.certifyIsPrefixOf l L).isSome = true ↔ l.isPrefixOf L := by
    intro l L
    induction l, L using Expo.List.certifyIsPrefixOf.induct
    · dsimp [List.certifyIsPrefixOf, POption.isSome]
      constructor
      · intro _
        apply List.isPrefixOf.nilCase
      · intro _
        apply Eq.refl
    · rename_i a b c d e f
      dsimp [List.certifyIsPrefixOf]
      rw [dif_pos (Eq.refl b)]
      dsimp [d] at e
      rw [e]
      dsimp
      dsimp [POption.isSome]
      constructor
      · intro ohNo
        contradiction
      · intro ohNo
        apply False.elim
        cases ohNo with
          | consCase _ proof =>
            rw [← f, e] at proof
            contradiction
    · rename_i a b c d e f g
      dsimp [List.certifyIsPrefixOf]
      rw [dif_pos (Eq.refl b)]
      dsimp [d] at f
      rw [f]
      dsimp
      dsimp [POption.isSome]
      constructor
      · intro _
        apply List.isPrefixOf.consCase _ e
      · intro _
        rfl
    · rename_i a b c d e f
      dsimp [List.certifyIsPrefixOf]
      rw [dif_neg f]
      dsimp [POption.isSome]
      constructor
      · intro ohNo
        contradiction
      · intro ohNo
        cases ohNo
        contradiction
    · rename_i a b c d e
      cases b with
        | nil =>
          contradiction
        | cons f g =>
          cases c with
            | nil =>
              dsimp [List.certifyIsPrefixOf, POption.isSome]
              constructor
              · intro ohNo
                contradiction
              · intro ohNo
                apply False.elim
                cases ohNo
            | cons h i =>
              specialize e f g h i rfl rfl
              contradiction


theorem viaVerifiedCertified : OneTwoThree.isPrefixOf OneToFive := by
  rw [← verifiedCeritfied]
  apply Eq.refl

#print viaVerifiedCertified


theorem viaVerifiedCertified' : OneTwoThree.isPrefixOf OneToFive :=
  let res := List.certifyIsPrefixOf OneTwoThree OneToFive
  match h : res with
  | .some proof => proof
  | .none =>
    by
    dsimp [res] at h
    contradiction


-- # Appendix : solution

example
  {α : Type u} (l L : List α) : l.isPrefixOf (l.append L) := by
  induction l with
    | nil =>
        rw [List.append.eq_1]
        apply List.isPrefixOf.nilCase
    | cons val l ih =>
        rw [List.append.eq_2]
        apply List.isPrefixOf.consCase
        exact ih
