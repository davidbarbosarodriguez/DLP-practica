
open Parsing;;
open Lexing;;

open Lambda;;
open Parser;;
open Lexer;;


let read_multiline () =
  let rec aux acc =
    let line = read_line () in
    if String.contains line ';' && String.length line > 1 then
      let has_double = ref false in
      let pos = ref 0 in
      for i = 0 to String.length line - 2 do
        if line.[i] = ';' && line.[i+1] = ';' then begin
          has_double := true;
          pos := i
        end
      done;
      if !has_double then
        let line_without = String.sub line 0 !pos in
        String.concat " " (List.rev (line_without :: acc))
      else
        aux (line :: acc)
    else
      aux (line :: acc)
  in
  aux []
;;


let top_level_loop () =
  print_endline "Evaluator of lambda expressions...";
  let rec loop ctx =
    print_string ">> ";
    flush stdout;
    try
      let c = s token (from_string (read_multiline ())) in
      loop (execute ctx c)
    with
       Lexical_error ->
         print_endline "lexical error";
         loop ctx
     | Parse_error ->
         print_endline "syntax error";
         loop ctx
     | Type_error e ->
         print_endline ("type error: " ^ e);
         loop ctx
     | End_of_file ->
         print_endline "...bye!!!"
  in
    loop emptyctx
  ;;

top_level_loop ()
;;

