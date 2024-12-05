import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

structure PageOrderRule where
  left : Nat
  right : Nat
deriving BEq, Repr

def pageOrderRuleParser : Parser PageOrderRule := do
  let left ← digits
  let _ ← pchar '|'
  let right ← digits
  let _ ← pchar '\n'
  return ⟨left, right⟩

def updateParser : Parser (List Nat) := separated (pchar ',' *> pure ()) digits <* pchar '\n'

def parser : Parser (List PageOrderRule × List (List Nat)) := do
  let rules ← many1 pageOrderRuleParser
  let _ ← pchar '\n'
  let updates ← many1 updateParser
  let _ ← eof
  return (rules.toList, updates.toList)

def getMiddle (l : List Nat) : Nat :=
  if h : l.length > 0 then
    have : l.length / 2 < l.length := Nat.bitwise_rec_lemma (Nat.not_eq_zero_of_lt h)
    l[l.length / 2]
  else
    0

  def collectLefts (e : Nat) : List PageOrderRule → List Nat
  | [] => []
  | x :: xs =>
    if x.right = e then
      x.left :: collectLefts e xs
    else
      collectLefts e xs

  def isValidLoop (rules : List PageOrderRule) (forbidden: List Nat) : List Nat → Bool
  | [] => true
  | x :: xs =>
    if x ∈ forbidden then
      false
    else
      isValidLoop rules (collectLefts x rules ++ forbidden) xs

def part1 (input : (List PageOrderRule × List (List Nat))) : Nat :=
  let ⟨rules, updates⟩ := input
  getMiddle <$> updates.filter (isValidLoop rules []) |> List.sum


def orderUpdates (rules : List PageOrderRule) (update : List Nat) : List Nat :=
  let hasPredecessor (nodes : List Nat) (n : Nat) :=
    (rules.filter (fun ⟨l, r⟩ => l ∈ nodes ∧ r = n) |> List.length) > 0

  let rec loop : List Nat → List Nat
  | [] => []
  | xs =>
    let io := xs.findIdx? (Bool.not ∘ hasPredecessor xs)
    if hi : io.isSome then
      let i := io.get hi
      have hi : i < xs.length := by
        unfold i io
        conv =>
          enter [1, 1]
          rw [List.findIdx?_eq_guard_findIdx_lt]

        unfold io at hi
        conv at hi =>
          enter [1, 1]
          rw [List.findIdx?_eq_guard_findIdx_lt]
        simp_all only [Option.guard_isSome, Option.guard_pos, Option.get_some]

      let rest := xs.eraseIdx i
      have : rest.length < xs.length := by
        rw [List.length_eraseIdx_of_lt hi]
        exact Nat.sub_one_lt_of_lt hi

      xs[i] :: loop rest
    else
      dbgTrace "Failed to find a suitable element" fun () => []   -- Failure
    termination_by xs => xs.length
    decreasing_by
      simp_all only [i, io, hasPredecessor, rest]

  loop update

def part2 (input: (List PageOrderRule × List (List Nat))) : Nat :=
  let ⟨rules, updates⟩ := input
  let invalid := updates.filter (Bool.not ∘ isValidLoop rules [])

  getMiddle <$> orderUpdates rules <$> invalid |> List.sum


def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  -- Part 1
  let res1 := part1 input
  let _ ← IO.println s!"Part 1: {res1}"

  -- Part 2
  let res2 := part2 input
  let _ ← IO.println s!"Part 2: {res2}"
