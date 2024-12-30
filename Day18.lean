import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String
open Batteries BinaryHeap

abbrev Pos := Nat × Nat

def posParser : Parser Pos := do
  let x ← digits
  skipChar ','
  let y ← digits
  return ⟨y, x⟩

def parser : Parser (List Pos) :=
  Array.toList <$> many (posParser <* skipChar '\n')



def part1 (height width : Nat) (input : List Pos) : Nat :=
  let map := List.replicate height (List.replicate width false |>.toArray) |>.toArray
  let map := input.foldl (fun map ⟨y, x⟩ => map.set2D y x true) map
  let dist := List.replicate height (List.replicate width none |>.toArray) |>.toArray

  let step (step : Nat) (map : Array (Array Bool)) (dist : Array (Array (Option Nat))) (p : Pos) : Array (Array (Option Nat)) × List Pos :=
    let (y, x) := p
    [(y-1, x), (y+1, x), (y, x-1), (y, x+1)].foldl (fun (dist, head) (y, x) =>
      if (dist.get2D? y x |>.bind id).isNone then
        if not ((map.get2D? y x).getD true) then
          (dist.set2D y x (some step), (y, x) :: head)
        else
          (dist, head)
      else
        (dist, head)
    ) (dist, [])

  let (dist, _) := List.range (width*height) |>.drop 1 |>.foldl (fun (dist, head) stepI =>
    head.foldr (fun pos (dist, head) =>
      let (dist, pos) := step stepI map dist pos
      (dist, pos ++ head)
    ) (dist, [])
  ) (dist, [(0, 0)])

  dist.get2D? (height-1) (width-1) |>.bind id |>.getD 0

def part2 (height width : Nat) (input : List Pos) : Pos :=
  -- Mark all bytes as inpenetrable
  let map := List.replicate height (List.replicate width false |>.toArray) |>.toArray
  let map := input.foldl (fun map ⟨y, x⟩ => map.set2D y x true) map

  let reached := List.replicate height (List.replicate width false |>.toArray) |>.toArray

  let flood (map : Array (Array Bool)) (reached : Array (Array Bool)) (p : Pos) : Array (Array Bool) × List Pos :=
    let (y, x) := p
    [(y-1, x), (y+1, x), (y, x-1), (y, x+1)].foldl (fun (reached, head) (y, x) =>
      if (reached.get2D? y x |>.getD false) then
        -- Has been reached already. Stop
        (reached, head)
      else
        if not ((map.get2D? y x).getD true) then
          (reached.set2D y x true, (y, x) :: head)
        else
          (reached, head)
    ) (reached, [])

  let floodAll (map : Array (Array Bool)) (reached : Array (Array Bool)) (p : Pos) : Array (Array Bool) × List Pos :=
    List.range (width*height) |>.foldl (fun (reached, head) _ =>
      head.foldr (fun pos (reached, head) =>
        let (reached, poss) := flood map reached pos
        (reached, poss ++ head)
      ) (reached, [])
    ) (reached, [p])

  let rec findLast (map : Array (Array Bool)) (reached : Array (Array Bool)) : List Pos → Array (Array Bool) × Array (Array Bool) × Option Pos
  | [] => (map, reached, none)
  | (y, x) :: xs =>
    let (map, reached, tailRes) := findLast map reached xs
    if tailRes.isNone then
      -- Mark free
      let map := map.set2D y x false

      let neighborReached :=  [(y-1, x), (y+1, x), (y, x-1), (y, x+1)].any fun (y, x) => (reached.get2D? y x).getD false
      if neighborReached then
        let (reached, _) := floodAll map reached (y, x)
        if reached.get2D? (height-1) (width-1) |>.getD false then
          (map, reached, some (y, x))
        else
          (map, reached, none)
      else
        (map, reached, none)
    else
      (map, reached, tailRes)

  -- Flood initially from the origin
  let (reached, _) := floodAll map reached (0, 0)

  let (_, _, res) := findLast map reached input
  res.getD (0, 0)

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  let (size, len) := (71, 1024)
  -- let (size, len) := (7, 12)      -- Sample

  -- Part 1
  let _ ← IO.println s!"Part 1: {part1 size size (input.take len)}"

  -- Part 2
  let (y, x) := part2 size size input
  let _ ← IO.println s!"Part 2: {x},{y}"
