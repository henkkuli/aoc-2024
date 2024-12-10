import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parser : Parser (Array (Array Nat)) :=
  many (many ((fun c => c.toNat - '0'.toNat) <$> digit) <* pchar '\n') <* eof

def Array.get2D? (a : Array (Array α)) (y x : Int) : Option α :=
  if y < 0 ∨ x < 0 then
    none
  else
    a.get? y.toNat >>= fun r => r.get? x.toNat

def part1 (map : Array (Array Nat)) : Nat :=
  let moveHigher : Int × Int → List (Int × Int)
  | ⟨y, x⟩ =>
    if let some cur := map.get2D? y x then
      [(y-1, x), (y+1, x), (y, x-1), (y, x+1)] |>.filter fun ⟨y, x⟩ => (map.get2D? y x >>= fun h => cur + 1 == h).getD false
    else
      []

  let starts := map.toList.enum.flatMap fun (y, r) => r.toList.enum.flatMap fun (x, h) => if h == 0 then [(y, x)] else []
  let starts := starts.map fun (y, x) => (Int.ofNat y, Int.ofNat x)

  let trailheadScore : Int × Int → Nat
  | pos => List.range 9 |>.foldl (fun poss _ => (poss.flatMap moveHigher).dedup) [pos] |>.length

  starts.map trailheadScore |>.sum

def part2 (map : Array (Array Nat)) : Nat :=
  let moveHigher : Int × Int → List (Int × Int)
  | ⟨y, x⟩ =>
    if let some cur := map.get2D? y x then
      [(y-1, x), (y+1, x), (y, x-1), (y, x+1)] |>.filter fun ⟨y, x⟩ => (map.get2D? y x >>= fun h => cur + 1 == h).getD false
    else
      []

  let starts := map.toList.enum.flatMap fun (y, r) => r.toList.enum.flatMap fun (x, h) => if h == 0 then [(y, x)] else []
  let starts := starts.map fun (y, x) => (Int.ofNat y, Int.ofNat x)

  let trailheadScore : Int × Int → Nat
  | pos => List.range 9 |>.foldl (fun poss _ => (poss.flatMap moveHigher)) [pos] |>.length

  starts.map trailheadScore |>.sum

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  -- Part 1
  let _ ← IO.println s!"Part 1: {part1 input}"

  -- Part 2
  let _ ← IO.println s!"Part 2: {part2 input}"
