import Mathlib
import Aoc2024
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

structure Guard where
  pos : Nat × Nat
  vel : Int × Int
deriving Repr

def intParser : Parser Int := do
  if (←peek?) = some '-' then
    skipChar '-'
    return Int.negOfNat (←digits)
  else
    return Int.ofNat (←digits)

def guardParser : Parser Guard := do
  skipString "p="
  let x ← digits
  skipChar ','
  let y ← digits
  skipString " v="
  let vx ← intParser
  skipChar ','
  let vy ← intParser
  skipChar '\n'
  return ⟨⟨y, x⟩, ⟨vy, vx⟩⟩

def parser : Parser (List Guard) :=
  Array.toList <$> many guardParser <* eof

def Guard.step (height width count : Nat) (g : Guard) : Guard :=
  if h : height > 0 ∧ width > 0 then
    have : NeZero height := NeZero.of_pos h.1
    have : NeZero width := NeZero.of_pos h.2
    let y : Fin height := Fin.ofNat' height g.pos.1
    let x : Fin width := Fin.ofNat' width g.pos.2
    -- Trust that velocity is small compared to the size of the grid
    let vy : Fin height := Fin.ofNat' height (g.vel.1 + height).toNat
    let vx : Fin width := Fin.ofNat' width (g.vel.2 + width).toNat

    -- Update position
    let y := y + count * vy
    let x := x + count * vx

    ⟨
      ⟨y, x⟩,
      ⟨vy, vx⟩
    ⟩
  else
    g     -- Invalid arguments. Do nothing

def part1 (height width : Nat) (guards : List Guard) : Nat :=
  let after := Guard.step height width 100 <$> guards
  let q1 := after.countP fun g => g.pos.1 < height/2 ∧ g.pos.2 < width/2
  let q2 := after.countP fun g => g.pos.1 > height/2 ∧ g.pos.2 < width/2
  let q3 := after.countP fun g => g.pos.1 > height/2 ∧ g.pos.2 > width/2
  let q4 := after.countP fun g => g.pos.1 < height/2 ∧ g.pos.2 > width/2
  q1 * q2 * q3 * q4

def part2 (height width steps : Nat) (guards : List Guard) : IO Unit := do
  IO.FS.createDir "day14"
  for i in [:steps] do
    let state := Guard.step height width i <$> guards
    let variance (l : List Nat) : Nat :=
      let mean := l.sum / l.length
      (l.map fun x => (mean.dist x).pow 2).sum

    let variance_y := state.map (Prod.fst ∘ Guard.pos) |> variance
    let variance_x := state.map (Prod.snd ∘ Guard.pos) |> variance
    -- Experimentally chosen limit for variance
    if variance_x < 200000 ∧ variance_y < 200000 then
      IO.println s!"{i}: {variance_y} {variance_x}"

      -- Write the picture to a file
      IO.FS.withFile s!"day14/{i}" IO.FS.Mode.writeNew fun f => do
        let pic : Array Char := List.replicate (height * width) '.' |>.toArray
        let pic := state.foldl (fun pic g => pic.set! (g.pos.1*width + g.pos.2) '#') pic
        for y in [:height] do
          let row := pic[y*width:(y+1)*width]
          let row := String.mk row.toArray.toList
          f.write row.toUTF8
          f.write "\n".toUTF8

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let input ← IO.ofExcept $ parser.run input

  let ⟨height, width⟩ := (103, 101)
  -- let ⟨height, width⟩ := (7, 11)    -- For sample

  -- Part 1
  let _ ← IO.println s!"Part 1: {part1 height width input}"

  -- Part 2
  part2 height width 10000 input
