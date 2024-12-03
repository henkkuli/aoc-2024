import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def pairParser : Parser (Nat × Nat) := do
  let a ← digits
  let _ ← ws
  let b ← digits
  return (a, b)

def pairListParser : Parser (List Nat × List Nat) := do
  let lists ← many (pairParser <* ws)
  let lists := lists.toList
  return ((·.fst) <$> lists, (·.snd) <$> lists)


def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ pairListParser.run input

  -- Part 1
  let left := input.fst.mergeSort
  let right := input.snd.mergeSort
  let res1 := Function.uncurry Nat.dist <$> left.zip right |> List.sum
  let _ ← IO.println s!"Part 1: {res1}"

  -- Part 2
  let res2 := (fun x => x * right.count x) <$> left |> List.sum
  let _ ← IO.println s!"Part 2: {res2}"
