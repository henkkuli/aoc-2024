import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parser : Parser (List (List Char)) :=
  Array.toList <$> many (Array.toList <$> many1 asciiLetter <* pchar '\n')

-- #eval [[1,2], [3,4]].sublists

def antidiagonals (l : List (List α)) : List (List α) :=
  let rec loop : (List (List α)) → List (List α)
    | [] => []
    | x :: xs =>
      let g : Option α → Option (List α) → List α
        | a, as => a.toList ++ as.getD []
      x.zipWithAll g ([] :: loop xs)

  loop l

def part2 (input : List (List Char)) : Nat :=
  let input : Array (Array Char) := List.toArray $ List.toArray <$> input
  let height := input.size
  let width := (List.minimum $ Array.size <$> input.toList).getD 0

  let idx (y x : Nat) : Option Char := (input.get? y >>= (·.get? x))
  let isMas : Option Char → Option Char → Option Char → Bool
    | some 'M', some 'A', some 'S' => true
    | some 'S', some 'A', some 'M' => true
    | _, _, _ => false

  let isMasAt (y x : Nat) : Nat :=
    if 1 ≤ x ∧ x < width - 1 ∧ 1 ≤ y ∧ y < height - 1 then
      if isMas (idx (y-1) (x-1)) (idx (y) (x)) (idx (y+1) (x+1)) ∧ isMas (idx (y+1) (x-1)) (idx (y) (x)) (idx (y-1) (x+1)) then
        1
      else
        0
    else
      0

  (Function.uncurry isMasAt <$> (List.range height).product (List.range width)).sum


def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  -- Part 1
  let rowscolsdiags := input ++ List.reverse <$> input ++ input.transpose ++ List.reverse <$> input.transpose ++
    antidiagonals input ++ antidiagonals input.reverse ++ List.reverse <$> antidiagonals input ++ List.reverse <$> antidiagonals input.reverse

  let res1 := List.sum (countOccurrences (pstring "XMAS" *> pure ()) <$> String.mk <$> rowscolsdiags)
  let _ ← IO.println s!"Part 1: {res1}"

  -- Part 2
  let res2 := part2 input
  let _ ← IO.println s!"Part 2: {res2}"
