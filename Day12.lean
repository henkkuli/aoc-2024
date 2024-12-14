import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parser : Parser (Array (Array Char)) :=
  many (many (satisfy fun c => c ≠ '\n') <* pchar '\n') <* eof


def Array.modifyI (a : Array α) (i : Int) (f : α → α) : Array α :=
  if let some i := i.toNat' then
    a.modify i f
  else
    a

partial def collectAreaAndBorder (c : Char) (map : Array (Array (Char × Bool))) (y x : Int) : Array (Array (Char × Bool)) × Nat × Nat :=
  let opNeighbor (map : Array (Array (Char × Bool))) (y x : Int) : Array (Array (Char × Bool)) × Nat × Nat :=
    if let some (c', visited) := map.get2D? y x then
      if visited ∧ c = c' then
        (map, 0, 0)
      else if c = c' then
        collectAreaAndBorder c map y x
      else
        (map, 0, 1)
    else
      (map, 0, 1)

  -- Mark as visited
  let map := map.modifyI y fun row => row.modifyI x fun (c, _) => (c, true)
  [(y-1, x), (y+1, x), (y, x-1), (y, x+1)].foldl (fun (map, area, border) (y, x) =>
    let (m, a, b) := opNeighbor map y x
    (m, area + a, border + b)
  ) (map, 1, 0)

def part1 (input : Array (Array Char)) : Nat :=
  let inputVisited := input.map fun row => row.map fun c => (c, false)

  let (inputVisited, res) := List.finRange inputVisited.size |>.foldl (fun (iv, r) y =>
    List.finRange inputVisited[y].size |>.foldl (fun (iv, r) x =>
      if let some (c, false) := iv.get2D? y x then
        let (iv, a, b) := collectAreaAndBorder c iv y x
        (iv, r + a*b)
      else
        (iv, r)
    ) (iv, r)
  ) (inputVisited, 0)

  res

partial def collectAreaAndSegments (c : Char) (map : Array (Array (Char × Bool))) (y x : Int) : Array (Array (Char × Bool)) × Nat × Nat :=
  let opNeighbor (map : Array (Array (Char × Bool))) (y x dy dx ey ex: Int) : Array (Array (Char × Bool)) × Nat × Nat :=
    if let some (c', visited) := map.get2D? y x then
      if visited ∧ c = c' then
        (map, 0, 0)
      else if c = c' then
        collectAreaAndSegments c map y x
      else
        if (map.get2D? dy dx).map Prod.fst = some c ∧ (map.get2D? ey ex).map Prod.fst ≠ some c then
          (map, 0, 0)
        else
          (map, 0, 1)
    else
      if (map.get2D? dy dx).map Prod.fst = some c ∧ (map.get2D? ey ex).map Prod.fst ≠ some c then
        (map, 0, 0)
      else
        (map, 0, 1)

  -- Mark as visited
  let map := map.modifyI y fun row => row.modifyI x fun (c, _) => (c, true)
  [(y-1, x, y, x-1, y-1, x-1), (y+1, x, y, x-1, y+1, x-1), (y, x-1, y-1, x, y-1, x-1), (y, x+1, y-1, x, y-1, x+1)].foldl (fun (map, area, border) (y, x, dy, dx, ey, ex) =>
    let (m, a, b) := opNeighbor map y x dy dx ey ex
    (m, area + a, border + b)
  ) (map, 1, 0)

def part2 (input : Array (Array Char)) : Nat :=
  let inputVisited := input.map fun row => row.map fun c => (c, false)

  let (inputVisited, res) := List.finRange inputVisited.size |>.foldl (fun (iv, r) y =>
    List.finRange inputVisited[y].size |>.foldl (fun (iv, r) x =>
      if let some (c, false) := iv.get2D? y x then
        let (iv, a, b) := collectAreaAndSegments c iv y x
        (iv, r + a*b)
      else
        (iv, r)
    ) (iv, r)
  ) (inputVisited, 0)

  res

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  -- Part 1
  let _ ← IO.println s!"Part 1: {part1 input}"

  -- Part 2
  let _ ← IO.println s!"Part 2: {part2 input}"
