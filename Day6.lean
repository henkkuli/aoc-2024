import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

inductive Cell
| empty
| wall
deriving BEq, Hashable, Repr

inductive CellOrGuard
| empty
| wall
| guard
deriving BEq, Hashable, Repr

def CellOrGuard.toCell : CellOrGuard → Cell
| empty | guard => .empty
| wall => .wall

def cellParser : Parser CellOrGuard :=
  (pchar '.' *> pure .empty) <|> (pchar '#' *> pure .wall) <|> (pchar '^' *> pure .guard)

inductive Direction
| up
| right
| down
| left
deriving BEq, Hashable, Repr

def Direction.next : Direction → Direction
| up => right
| right => down
| down => left
| left => up

structure GuardState where
  pos : Int × Int
  dir : Direction
deriving BEq, Hashable, Repr

def parser : Parser (Array (Array CellOrGuard)) :=
  many (many1 cellParser <* pchar '\n')

def findGuard (cols : (Array (Array CellOrGuard))) : Except String (GuardState × Array (Array Cell)) := do
  let rowpos := cols.map (fun row => row.findIdx? (· == .guard))
  if let some y := rowpos.findIdx? Option.isSome then
    if let some (some x) := rowpos[y]? then
      let guard := GuardState.mk (y, x) .up
      let map := cols.map (fun row => row.map CellOrGuard.toCell)
      return ⟨guard, map⟩
    else
      Except.error "Expected to find a guard"
  else
    Except.error "Expected to find a guard"

def GuardState.step (map : Array (Array Cell)) (g : GuardState) : Option GuardState :=
  let nextCell := match g.dir with
    | .up => (g.pos.fst - 1, g.pos.snd)
    | .right => (g.pos.fst, g.pos.snd + 1)
    | .down => (g.pos.fst + 1, g.pos.snd)
    | .left => (g.pos.fst, g.pos.snd - 1)

  if nextCell.fst < ↑0 ∨ nextCell.snd < ↑0 then
    none
  else
    match map.get? nextCell.fst.toNat >>= (Array.get? · nextCell.snd.toNat) with
    | some Cell.empty => some ⟨nextCell, g.dir⟩
    | some Cell.wall => some ⟨g.pos, g.dir.next⟩
    | none => none

def statesOnWalk (map : Array (Array Cell)) (g : GuardState) : MLList Id GuardState :=
  MLList.fix? (GuardState.step map) g

def part1 (map : Array (Array Cell)) (g : GuardState) : Nat :=
  let uniqueStates := MLList.dedup (statesOnWalk map g)
  let positions := uniqueStates.map (·.pos)
  let uniquePositions := MLList.dedup positions
  uniquePositions.force.length


-- Given an MLList, finds whether an element repeats. If not, then the list must be finite; otherwise this will take forever.
def repeats [Monad m] [BEq α] [Hashable α] [Repr α] (L : MLList m α) : m Bool :=
  let a := ((L.liftM : MLList (StateT (Std.HashSet α) $ OptionT m) α)).foldM (fun () val => do
    guard !(←get).contains val
    modify fun s => s.insert val
    pure ()
    ) () ∅
  Option.isNone <$> a

def part2 (map : Array (Array CellOrGuard)) (g : GuardState) : Nat :=
  let rec goCol (pre : Array (Array CellOrGuard)) (rowpre : Array CellOrGuard) (row : List CellOrGuard) (suf : List (Array CellOrGuard)) : Nat :=
    match row with
    | [] => 0
    | .empty :: xs =>
      let rest := goCol pre (rowpre.push .empty) xs suf
      let map := (pre ++ [rowpre ++ [CellOrGuard.wall] ++ xs] ++ suf)
      let map := map.map (fun row => row.map CellOrGuard.toCell)
      let r : Bool := repeats (statesOnWalk map g)
      if r then
        1 + rest
      else
        rest
    | x :: xs => goCol pre (rowpre.push x) xs suf

  let rec goRows (pre : Array (Array CellOrGuard)) (suf : List (Array CellOrGuard)) : Nat :=
    match suf with
    | [] => 0
    | x :: xs => (goCol pre #[] x.toList xs) + goRows (pre.push x) xs

  goRows #[] map.toList

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input
  let ⟨initialGuard, map⟩ ← IO.ofExcept $ findGuard input

  -- Part 1
  let res1 := part1 map initialGuard
  let _ ← IO.println s!"Part 1: {res1}"

  -- Part 2
  let res2 := part2 input initialGuard
  let _ ← IO.println s!"Part 2: {res2}"
