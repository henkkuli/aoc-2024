import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parser : Parser (List Nat) :=
  separated (pchar ' ' *> pure ()) digits <* pchar '\n' <* eof

def step : Nat → List Nat
| 0 => [1]
| n =>
  let s := toString n
  if Even s.length then
    let a := s.take $ s.length / 2
    let b := s.drop $ s.length / 2
    [a.toNat!, b.toNat!]
  else
    [2024 * n]

#guard step 0 == [1]
#guard step 1 == [2024]
#guard step 10 == [1, 0]
#guard step 99 == [9, 9]
#guard step 999 == [2021976]

def part1 (l : List Nat) : Nat :=
  List.range 25 |>.foldl (fun elems _ => elems >>= step) l |>.length

def part2 (l : List Nat) : Nat :=
  let NatNat := (fun _ : Nat => Nat)
  let addMany (l : AList NatNat) (val : Nat) (count : Nat) : AList NatNat :=
    if let some c := l.lookup val then
        l.insert val (c+count)
      else
        l.insert val count


  let initial : AList NatNat :=
    l.foldl (fun counts elem => addMany counts elem 1) ∅

  let stepAll : AList NatNat → AList NatNat :=
    AList.foldl (fun res val count =>
      step val |>.foldl (fun r v => addMany r v count) res
    ) ∅

  List.range 75 |>.foldl (fun elems _ => stepAll elems) initial |>.entries.map (fun a => a.snd) |>.sum

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  -- Part 1
  let _ ← IO.println s!"Part 1: {part1 input}"

  -- Part 2
  let _ ← IO.println s!"Part 2: {part2 input}"
