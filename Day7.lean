import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

structure Calibration where
  target : Nat
  operands : List Nat

def calibrationParser : Parser Calibration := do
  let target ← digits
  let _ ← pstring ": "
  let operands ← separated (pchar ' ' *> pure ()) digits
  return ⟨target, operands⟩

def parser : Parser (List Calibration) :=
  Array.toList <$> (many (calibrationParser <* pchar '\n')) <* eof

def solve (ops : List (Nat → Nat → Nat)) (l : List Nat) : List Nat :=
  let rec loop : List Nat → List Nat
    | [] => []
    | x :: [] => [x]
    | x :: xs =>
      let possible := loop xs
      possible >>= fun y => ops.map fun op => op y x
  loop l.reverse

def part1 (input : List Calibration) : Nat :=
  List.sum $ Calibration.target <$> (input.filter fun cal =>
    (solve [(· + ·), (· * ·)] cal.operands).contains cal.target)

def concatNats (a b : Nat) : Nat :=
  (toString a ++ toString b).toNat!

def part2 (input : List Calibration) : Nat :=
  List.sum $ Calibration.target <$> (input.filter fun cal =>
    (solve [(· + ·), (· * ·), concatNats] cal.operands).contains cal.target)

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
