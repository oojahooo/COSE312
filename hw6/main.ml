let main () =
    let print_code = ref false in
    let src = ref "" in
    let spec = [("-pp", Arg.Set print_code, "pretty print the input program")] in
    let usage = "Usage: run <options> <file>" in
    let _ = Arg.parse spec
                (fun
                   x ->
                     if Sys.file_exists x then src := x
                     else raise (Arg.Bad (x ^ ": No files given")))
                usage
    in

  if !src = "" then Arg.usage spec usage
    else
    try
      let file_channel = open_in !src in
      let lexbuf = Lexing.from_channel file_channel in
      let s_pgm = Parser.program Lexer.start lexbuf in
      let _ = print_endline "== source program ==";
              S.pp s_pgm in
      let _ = print_endline "== analyze the program ==" in
      let safe = Analyzer.verify s_pgm in
      let _ = print_endline ("program is " ^ (if safe then "safe" else "unsafe")) in
        if safe then
          let _ = print_endline "== execute the source program ==";
                  (try S.execute s_pgm;
                  with (Failure s) -> print_endline ("Error: "^s)) in
             ()
        else 
           print_endline "== input program is potentially unsafe and rejected =="
    with (Failure s) -> print_endline (!src ^ ": " ^ s)

let _ = main ()
