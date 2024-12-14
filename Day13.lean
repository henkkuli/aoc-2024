import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

structure Pos where
  y : Nat
  x : Nat
deriving DecidableEq, Repr

instance : Add Pos where
  add := fun a b => ⟨a.y + b.y, a.x + b.x⟩

instance : HMul Nat Pos Pos where
  hMul := fun c p => ⟨c * p.y, c * p.x⟩

instance : HMul Pos Nat Pos where
  hMul := fun p c => ⟨p.y * c, p.x * c⟩

structure Game where
  a : Pos
  b : Pos
  p : Pos
deriving DecidableEq, Repr

def gameParser : Parser Game := do
  pstring "Button A: X+" *> pure ()
  let ax ← digits
  pstring ", Y+" *> pure ()
  let ay ← digits
  pstring "\nButton B: X+" *> pure ()
  let bx ← digits
  pstring ", Y+" *> pure ()
  let by' ← digits
  pstring "\nPrize: X=" *> pure ()
  let px ← digits
  pstring ", Y=" *> pure ()
  let py ← digits
  pstring "\n" *> pure ()
  return ⟨⟨ay, ax⟩, ⟨by', bx⟩, ⟨py, px⟩⟩


def parser : Parser (List Game) :=
  separated (skipChar '\n') gameParser <* eof

def part1 (games : List Game) : Nat :=
  let minimumCost (g : Game) : Option Nat := List.product (List.range 101) (List.range 101) |>.map (fun (a, b) =>
    if g.a * a + g.b * b = g.p then
      some (3*a + b)
    else
      none
  ) |>.flatMap Option.toList |>.minimum

  games.flatMap (Option.toList ∘ minimumCost) |>.sum

def minimumCost (g : Game) : Option Nat :=
  let b1 := (Int.ofNat g.p.y * g.a.x) - g.p.x*g.a.y
  let b2 := (Int.ofNat g.b.y * g.a.x) - g.b.x*g.a.y
  if b2 = 0 then
    -- This happens if A and B are multiples of each other. Doesn't seem to happen in the input.
    if b1 = 0 then
      -- TODO: Solve a Diophantine equation. Isn't needed for input, and hence left unimplemented.
      none
    else
      -- But A and B are not aligned with the target
      none
  else
    let b := b1 / b2
    let a := (g.p.x - b * g.b.x) / g.a.x
    if a ≥ 0 ∧ b ≥ 0 then
      let a := a.toNat
      let b := b.toNat
      if g.a * a + g.b * b = g.p then
        some (3*a + b)
      else
        none
    else
      none

def part2 (games : List Game) : Nat :=
  games.map (fun g => ⟨g.a, g.b, ⟨10000000000000 + g.p.y, 10000000000000 + g.p.x⟩⟩) |>.flatMap (Option.toList ∘ minimumCost) |>.sum

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  -- Part 1
  let _ ← IO.println s!"Part 1: {part1 input}"

  -- Part 2
  let _ ← IO.println s!"Part 2: {part2 input}"
