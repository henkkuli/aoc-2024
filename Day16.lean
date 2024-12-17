import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String
open Batteries BinaryHeap

inductive Tile
| wall
| floor
deriving BEq, Repr, DecidableEq

inductive TileOrMarker
| wall
| floor
| start
| target
deriving BEq, Repr, DecidableEq

def tileOrMarkerParser : Parser TileOrMarker := do
  match ←any with
  | '#' => pure TileOrMarker.wall
  | '.' => pure TileOrMarker.floor
  | 'S' => pure TileOrMarker.start
  | 'E' => pure TileOrMarker.target
  | _ => fail "Unexpected character"

def TileOrMarker.toTile : TileOrMarker → Tile
| .wall => .wall
| .floor | .start | .target => .floor

abbrev Pos := Nat × Nat

def find2DPosP (arr : Array (Array α)) (p : α → Bool) : Option Pos :=
  let rowpos := arr.map (fun row => row.findIdx? p)
  if let some y := rowpos.findIdx? Option.isSome then
    if let some (some x) := rowpos[y]? then
      some ⟨y, x⟩
    else
      none
  else
    none

def parser : Parser (Array (Array Tile) × Pos × Pos) := do
  let map ← many1 (many1 (attempt tileOrMarkerParser) <* skipChar '\n') <* eof

  if let some start := find2DPosP map (· == .start) then
    if let some target := find2DPosP map (· == .target) then
       let map := map.map (fun row => row.map TileOrMarker.toTile)
       return ⟨map, start, target⟩
    else
      fail "Expected to find end"
  else
    fail "Expected to find start"

inductive Dir
| up
| right
| down
| left
deriving BEq, Repr, DecidableEq, Hashable

def Dir.cw : Dir → Dir
| .up => .right
| .right => .down
| .down => .left
| .left => .up

def Dir.ccw : Dir → Dir
| .up => .left
| .right => .up
| .down => .right
| .left => .down

def Dir.inv : Dir → Dir
| .up => .down
| .right => .left
| .down => .up
| .left => .right

def Dir.toFin : Dir → Fin 4
| .up => 0
| .right => 1
| .down => 2
| .left => 3

def heap_lt (a b : Nat × Pos × Dir) : Bool :=
  if a.1 ≥ b.1 then   -- Use ≥ because we want a min-heap but the default is a max-heap
    true
  else
    false

partial def part1.go (map : Array (Array Tile)) (target : Pos) (heap : BinaryHeap (Nat × Pos × Dir) heap_lt) (visited : Std.HashSet (Pos × Dir)) : Option Nat := do
  if let some ⟨dist, ⟨y, x⟩, dir⟩ := heap.max then
    let mut heap := heap.popMax
    if visited.contains ⟨⟨y, x⟩, dir⟩ then
      go map target heap visited
    else
      let visited := visited.insert ⟨⟨y, x⟩, dir⟩
      if target.1 = y ∧ target.2 = x then
        return dist

      let ⟨ny, nx⟩ := match dir with
        | .up => (y-1, x)
        | .right => (y, x+1)
        | .down => (y+1, x)
        | .left => (y, x-1)
      if let some .floor := map.get2D? ny nx then
        heap := heap.insert ⟨dist+1, ⟨ny, nx⟩, dir⟩
      heap := heap.insert ⟨dist+1000, ⟨y, x⟩, dir.cw⟩ |>.insert ⟨dist+1000, ⟨y, x⟩, dir.ccw⟩

      go map target heap visited
  else
     none

def part1 (input : Array (Array Tile) × Pos × Pos) : Nat :=
  let ⟨map, start, target⟩ := input
  part1.go map target (BinaryHeap.singleton heap_lt ⟨0, start, .right⟩) ∅ |>.getD 0

partial def part2.go (map : Array (Array Tile)) (heap : BinaryHeap (Nat × Pos × Dir) heap_lt) (visited : Array (Array (Vector (Option Nat) 4))) : Array (Array (Vector (Option Nat) 4)) := Id.run do
  if let some ⟨dist, ⟨y, x⟩, dir⟩ := heap.max then
    let mut heap := heap.popMax

    -- Check whether we already know a better solution
    if let some vd := visited.get2D? y x then
      if let some vd := vd.get dir.toFin then
        if vd ≤ dist then
          return go map heap visited

    let visited := visited.modify y fun row => row.modify x fun v => v.set dir.toFin dist

    let ⟨ny, nx⟩ := match dir with
      | .up => (y-1, x)
      | .right => (y, x+1)
      | .down => (y+1, x)
      | .left => (y, x-1)
    if let some .floor := map.get2D? ny nx then
      heap := heap.insert ⟨dist+1, ⟨ny, nx⟩, dir⟩
    heap := heap.insert ⟨dist+1000, ⟨y, x⟩, dir.cw⟩ |>.insert ⟨dist+1000, ⟨y, x⟩, dir.ccw⟩

    go map heap visited
  else
     visited

def part2 (input : Array (Array Tile) × Pos × Pos) : Nat :=
  let ⟨map, start, target⟩ := input
  let startMap : Array (Array (Vector (Option Nat) 4)) := map.map fun row => row.map fun _ => #v[none, none, none, none]
  let endMap := startMap    -- Just a copy

  let startMap := part2.go map (BinaryHeap.singleton heap_lt ⟨0, start, .right⟩) startMap
  let endMap := [Dir.up, .right, .down, .left].foldl (fun endMap dir => part2.go map (BinaryHeap.singleton heap_lt ⟨0, target, dir⟩) endMap) endMap

  if let some vd := endMap.get2D? start.1 start.2 then
    if let some opt := vd.get Dir.right.toFin then
      let maps := startMap.zip endMap |>.map fun ⟨a, b⟩ => a.zip b
      let cells := maps.toList.flatMap fun row => row.toList
      let optCells := cells.filter fun ⟨s, e⟩ =>
        let dirs := [Dir.up, .right, .down, .left]
        dirs.any fun dir =>
          match s[dir.toFin], e[dir.inv.toFin] with
          | some s, some e => e + s = opt
          | _, _ => false
      optCells.length
    else
      0
  else
    0

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  -- Part 1
  let _ ← IO.println s!"Part 1: {part1 input}"

  -- Part 2
  let _ ← IO.println s!"Part 2: {part2 input}"
