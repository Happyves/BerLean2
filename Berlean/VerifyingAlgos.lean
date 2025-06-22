
import Lean

open Lean Meta Elab Tactic


-- # Verifying algorithms vs. algorithms that certify

/-
Intro
-/


-- ## Introduction to Lists

namespace Expo

universe u

inductive List (α : Type u) where
| nil
| cons (val : α) (nx : List α)
deriving Repr


def OneTwoThree : List Nat :=
  .cons 1 <| .cons 2 <| .cons 3 .nil


def FourFive : List Nat :=
  .cons 4 <| .cons 5 .nil


def List.length {α : Type u} : List α → Nat
  | .nil => 0
  | .cons _ nx => 1 + nx.length


#eval OneTwoThree.length
#eval FourFive.length


def List.append {α : Type u} : List α → List α → List α
  | .nil, l => l
  | .cons val nx, l => .cons val <| append nx l

#eval List.append OneTwoThree FourFive

def OneToFive :=
  List.append OneTwoThree FourFive

-- **Todo** show `(· ++ ·).length = ·.length + ·.length` to highlight induction, and fun-induction


inductive List.isPrefixOf {α : Type u}  : List α → List α → Prop where
  | nilCase (l : List α) : List.isPrefixOf .nil l
  | consCase (val : α) {l L : List α} (proof : List.isPrefixOf l L) : List.isPrefixOf (.cons val l) (.cons val L)


theorem termStyleProof : OneTwoThree.isPrefixOf OneToFive :=
  .consCase 1 <| .consCase 2 <| .consCase 3 <| .nilCase FourFive



-- ## Verified Algorithms

def List.checkIsPrefixOf {α : Type u} [DecidableEq α] : List α → List α → Bool
  | .nil, _ => true
  | .cons val₁ l₁, .cons val₂ l₂ =>
      if val₁ = val₂ then l₁.checkIsPrefixOf l₂ else false
  | _, _ => false


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
              ·
                -- intro ohNo
                -- apply False.elim
                -- apply Bool.noConfusion ohNo
                simp
              · intro h
                cases h with
                  | consCase _ h =>
                    apply False.elim
                    apply C
                    apply Eq.refl




theorem viaVerified : OneTwoThree.isPrefixOf OneToFive := by
  rw [← algoVerified]
  apply Eq.refl

#print viaVerified


-- # Algorithms that certify

partial def tryProof (left right : Expr) : TacticM Expr := do
    let left ← whnf left
    let right ← whnf right
    let (lh,largs) := left.getAppFnArgs
    if lh == `Expo.List.nil
    then
      let proof ← mkAppM `Expo.List.isPrefixOf.nilCase #[right]
      return proof
    else
      let (_,rargs) := right.getAppFnArgs
      let sofar ← tryProof largs[2]! rargs[2]!
      let extend ← mkAppM `Expo.List.isPrefixOf.consCase #[largs[1]!, sofar]
      return extend



elab "tryCertify" : tactic => do
  let g ← getMainTarget
  let (h,args) := g.getAppFnArgs
  if h != `Expo.List.isPrefixOf
    then throwError "This tactic only works when the goal is a prefix relation !"
  let left := args[1]!
  let right := args[2]!
  let proof ← tryProof left right
  closeMainGoal `tryCertify proof

theorem viaCertified : OneTwoThree.isPrefixOf OneToFive := by
  tryCertify

#print viaCertified
#print termStyleProof

theorem ohNo : (List.cons 6 .nil).isPrefixOf OneToFive := by
  tryCertify



-- # Verified algorithms that certify

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


example {α : Type u} [DecidableEq α] :
  ∀ l L : List α, (List.certifyIsPrefixOf l L).isSome ↔ l.isPrefixOf L := by
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








-- # Appendix

example {α : Type u} [DecidableEq α] :
  ∀ l L : List α, l.checkIsPrefixOf L = true ↔ l.isPrefixOf L := by
    intro l L
    induction l, L using Expo.List.certifyIsPrefixOf.induct
    · dsimp [List.checkIsPrefixOf]
      constructor
      · intro _
        apply List.isPrefixOf.nilCase
      · intro _
        apply Eq.refl
    · sorry
    · sorry
    · sorry
    · sorry
