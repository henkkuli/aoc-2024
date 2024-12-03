import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def lineParser : Parser (List Nat) :=
  separated (skipChar ' ') digits <* pstring "\n"

def lineListParser : Parser (List (List Nat)) :=
  Array.toList <$> many lineParser

def isSafe (l : List Nat) : Bool :=
  let paired := Mathlib.Tactic.BicategoryLike.pairs l
  let monotonic := (paired.all $ Function.uncurry (· ≤ ·)) ∨ (paired.all $ Function.uncurry (· ≥ ·))
  let diffCorrect := paired.all (fun ⟨a, b⟩ => a.dist b ≥ 1 ∧ a.dist b ≤ 3)
  monotonic ∧ diffCorrect

def isSafe2 (l : List Nat) : Bool :=
  let rec loop (pre suf : List ℕ) : Bool :=
    match suf with
    | [] => isSafe (pre ++ suf)
    | x :: xs =>
      isSafe (pre ++ xs) ∨ loop (pre ++ [x]) xs

  loop [] l

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ lineListParser.run input

  -- Part 1
  let res1 := input.countP isSafe
  let _ ← IO.println s!"Part 1: {res1}"

  -- Part 2
  let res2 := input.countP isSafe2
  let _ ← IO.println s!"Part 2: {res2}"
