partial def IO.FS.Stream.readToEnd (stream : Stream) : IO String := do
  let rec loop (s : String) := do
    let line ← stream.getLine
    if line.isEmpty then
      return s
    else
      loop (s ++ line)
  loop ""
