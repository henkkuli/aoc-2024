import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

inductive Tile
| wall
| floor
| box
deriving BEq, Repr, DecidableEq

inductive WideTile
| wall
| floor
| lbox
| rbox
deriving BEq, Repr, DecidableEq

inductive TileOrBot
| wall
| floor
| box
| bot
deriving BEq, Repr, DecidableEq

inductive Move
| up
| right
| down
| left
deriving BEq, Repr, DecidableEq

def tileOrBotParser : Parser TileOrBot := do
  match ←any with
  | '#' => pure TileOrBot.wall
  | '.' => pure TileOrBot.floor
  | 'O' => pure TileOrBot.box
  | '@' => pure TileOrBot.bot
  | _ => fail "Unexpected character"

def TileOrBot.toTile : TileOrBot → Tile
| .wall => .wall
| .floor | .bot => .floor
| .box => .box

def moveParser : Parser Move := do
  match ←any with
  | '^' => pure Move.up
  | '>' => pure Move.right
  | 'v' => pure Move.down
  | '<' => pure Move.left
  | _ => fail "Unexpected character"

def Pos := Nat × Nat

def parser : Parser (Array (Array Tile) × Pos × List Move) := do
  let map ← many1 (many1 (attempt tileOrBotParser) <* skipChar '\n')
  skipChar '\n'
  let moves ← Array.toList <$> many (moveParser <* tryCatch (skipChar '\n') (fun _ => pure ()) (fun () => pure ()))
  eof

  -- Find robot
  let rowpos := map.map (fun row => row.findIdx? (· == .bot))
  if let some y := rowpos.findIdx? Option.isSome then
    if let some (some x) := rowpos[y]? then
      let bot := (y, x)
      let map := map.map (fun row => row.map TileOrBot.toTile)
      return ⟨map, bot, moves⟩
    else
      fail "Expected to find a bot"
  else
    fail "Expected to find a bot"

partial def step.go (map : Array (Array Tile)) (pos : Pos) (move : Pos → Pos) : Option (Array (Array Tile)) :=
  match map.get2D? pos.1 pos.2 with
  | none => none
  | some .wall => none
  | some .floor => some $ map.modify pos.1 fun row => row.set! pos.2 .box
  | some .box => go map (move pos) move


def step (map : Array (Array Tile)) (pos : Pos) (move : Move) : Array (Array Tile) × Pos :=
  let move := match move with
  | .up => fun (y, x) => (y-1, x)
  | .right => fun (y, x) => (y, x+1)
  | .down => fun (y, x) => (y+1, x)
  | .left => fun (y, x) => (y, x-1)
  match step.go map (move pos) move with
  | none => (map, pos)  -- Nothing happens
  | some map =>
    -- Step taken. Just clear the box the bot stands on
    let pos := move pos
    let map := map.modify pos.1 fun row => row.set! pos.2 .floor
    (map, pos)


def part1 (input : Array (Array Tile) × Pos × List Move) : Nat :=
  let ⟨map, pos, moves⟩ := input
  let ⟨finalMap, _finalPos⟩ := moves.foldl (fun ⟨map, pos⟩ move => step map pos move) (map, pos)

  let boxPositions := finalMap.toList.enum.flatMap fun (y, row) => row.toList.enum.flatMap fun (x, t) =>
    match t with
    | .box => [(y, x)]
    | _ => []

  boxPositions.map (fun (y, x) => 100*y + x) |>.sum

partial def step2.goH (map : Array (Array WideTile)) (pos : Pos) (move : Pos → Pos) : Option (Array (Array WideTile)) :=
  match map.get2D? pos.1 pos.2 with
  | none => none
  | some .wall => none
  | some .floor => some map
  | some b => do
    let p := move pos
    let map ← goH map p move
    map.modify p.1 fun row => row.set! p.2 b

partial def step2.goV (map : Array (Array WideTile)) (pos : Pos) (move : Pos → Pos) : Option (Array (Array WideTile)) :=
  match map.get2D? pos.1 pos.2 with
  | none => none
  | some .wall => none
  | some .floor => some map
  | some .lbox => do
    let map ← goV map (move pos) move
    let map := map.modify (move pos).1 fun row => row.set! (move pos).2 .lbox
    let map := map.modify pos.1 fun row => row.set! pos.2 .floor
    let p := (pos.1, pos.2+1)
    let map ← goV map (move p) move
    let map := map.modify (move p).1 fun row => row.set! (move p).2 .rbox
    let map := map.modify p.1 fun row => row.set! p.2 .floor
    some map
  | some .rbox => do
    let map ← goV map (move pos) move
    let map := map.modify (move pos).1 fun row => row.set! (move pos).2 .rbox
    let map := map.modify pos.1 fun row => row.set! pos.2 .floor
    let p := (pos.1, pos.2-1)
    let map ← goV map (move p) move
    let map := map.modify (move p).1 fun row => row.set! (move p).2 .lbox
    let map := map.modify p.1 fun row => row.set! p.2 .floor
    some map


def step2 (map : Array (Array WideTile)) (pos : Pos) (move : Move) : Array (Array WideTile) × Pos :=
  let res := match move with
  | .up =>
    let move : Pos → Pos := fun (y, x) => (y-1, x)
    (step2.goV map (move pos) move, move pos)
  | .down =>
    let move : Pos → Pos := fun (y, x) => (y+1, x)
    (step2.goV map (move pos) move, move pos)
  | .right =>
    let move : Pos → Pos := fun (y, x) => (y, x+1)
    (step2.goH map (move pos) move, move pos)
  | .left =>
    let move : Pos → Pos := fun (y, x) => (y, x-1)
    (step2.goH map (move pos) move, move pos)

  match res with
  | (none, _) => (map, pos)
  | (some map, pos) =>
    -- Step taken. Just clear the box the bot stands on
    let map := map.modify pos.1 fun row => row.set! pos.2 .floor
    (map, pos)

def vis (map : Array (Array WideTile)) (pos : Pos) : String :=
  String.mk <| map.toList.enum.flatMap fun (y, row) =>
    let r := row.toList.enum.map fun
    | (x, .floor) => if y = pos.1 ∧ x = pos.2 then '@' else '.'
    | (_, .lbox) => '['
    | (_, .rbox) => ']'
    | (_, .wall) => '#'
    r ++ ['\n']

def part2 (input : Array (Array Tile) × Pos × List Move) : Nat :=
  let ⟨map, pos, moves⟩ := input
  -- Widen the warehouse
  let map := map.map fun row => row.flatMap fun
    | .wall => #[WideTile.wall, WideTile.wall]
    | .box => #[WideTile.lbox, WideTile.rbox]
    | .floor => #[WideTile.floor, WideTile.floor]
  let pos := (pos.1, 2*pos.2)

  let ⟨finalMap, _finalPos⟩ := moves.foldl (fun ⟨map, pos⟩ move => step2 map pos move) (map, pos)

  let boxPositions := finalMap.toList.enum.flatMap fun (y, row) => row.toList.enum.flatMap fun (x, t) =>
    match t with
    | .lbox => [(y, x)]
    | _ => []

  boxPositions.map (fun (y, x) => 100*y + x) |>.sum

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  -- Part 1
  let _ ← IO.println s!"Part 1: {part1 input}"

  -- Part 2
  let _ ← IO.println s!"Part 2: {part2 input}"
