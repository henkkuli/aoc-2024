import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def mulParser : Parser (Nat × Nat) := do
  let _ ← pstring "mul("
  let a ← digits
  let _ ← pstring ","
  let b ← digits
  let _ ← pstring ")"
  return (a, b)

def condParser : Parser Bool :=
  (pstring "don't" *> pure false) <|> (pstring "do" *> pure true)

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  -- let input ← IO.ofExcept $ mulParser.run input

  -- Part 1
  let mut inputIter := input.iter
  let mut res1 := 0
  while ¬inputIter.atEnd do
    match mulParser inputIter with
    | .success _ (a, b) => res1 := res1 + a*b
    | .error _ _ => pure ()

    inputIter := inputIter.next
  let _ ← IO.println s!"Part 1: {res1}"

  -- Part 2
  inputIter := input.iter
  let mut res2 := 0
  let mut active := true
  while ¬inputIter.atEnd do
    match condParser inputIter with
    | .success _ cond => active := cond
    | .error _ _ => pure ()

    if active then
      match mulParser inputIter with
      | .success _ (a, b) => res2 := res2 + a*b
      | .error _ _ => pure ()

    inputIter := inputIter.next
  let _ ← IO.println s!"Part 2: {res2}"
