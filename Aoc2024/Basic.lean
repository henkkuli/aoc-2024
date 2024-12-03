import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

partial def IO.FS.Stream.readToEnd (stream : Stream) : IO String := do
  let rec loop (s : String) := do
    let line ← stream.getLine
    if line.isEmpty then
      return s
    else
      loop (s ++ line)
  loop ""

partial def separated (sep : Parser Unit) (value : Parser α) : Parser (List α) :=
  let rec loop (res : Array α) : Parser (Array α) := do
    let res := res.push (←value)
    (sep *> loop res) <|> pure res

  Array.toList <$> loop #[]
