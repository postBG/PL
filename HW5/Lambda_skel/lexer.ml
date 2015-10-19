# 8 "lexer.mll"
 
 open Parser
 exception Eof
 exception LexicalError
 let verbose1 s =  (* (print_string s; print_newline(); s) *) s
 let verbose2 s =  (* (print_string s; print_newline()) *) ()
 let comment_depth = ref 0

# 11 "lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\247\255\248\255\249\255\251\255\252\255\084\000\000\000\
    \002\000\254\255\003\000\252\255\253\255\003\000\005\000\255\255\
    \254\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\002\000\005\000\
    \000\000\255\255\255\255\255\255\255\255\003\000\003\000\255\255\
    \255\255";
  Lexing.lex_default = 
   "\001\000\000\000\000\000\000\000\000\000\000\000\255\255\255\255\
    \255\255\000\000\011\000\000\000\000\000\255\255\255\255\000\000\
    \000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\008\000\008\000\008\000\008\000\008\000\000\000\008\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \008\000\000\000\008\000\000\000\000\000\000\000\000\000\000\000\
    \007\000\003\000\009\000\014\000\016\000\013\000\004\000\015\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\000\000\005\000\000\000\000\000\000\000\
    \000\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\000\000\
    \000\000\000\000\000\000\006\000\000\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \002\000\000\000\000\000\012\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\008\000\008\000\000\000\255\255\008\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\008\000\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\007\000\010\000\013\000\010\000\000\000\014\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\255\255\000\000\255\255\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\006\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\255\255\
    \255\255\255\255\255\255\006\000\255\255\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\010\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255";
  Lexing.lex_base_code = 
   "";
  Lexing.lex_backtrk_code = 
   "";
  Lexing.lex_default_code = 
   "";
  Lexing.lex_trans_code = 
   "";
  Lexing.lex_check_code = 
   "";
  Lexing.lex_code = 
   "";
}

let rec start lexbuf =
    __ocaml_lex_start_rec lexbuf 0
and __ocaml_lex_start_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 21 "lexer.mll"
             ( start lexbuf )
# 134 "lexer.ml"

  | 1 ->
# 22 "lexer.mll"
            ( comment_depth :=1;
              comment lexbuf;
              start lexbuf )
# 141 "lexer.ml"

  | 2 ->
let
# 25 "lexer.mll"
             id
# 147 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 25 "lexer.mll"
                ( ID id )
# 151 "lexer.ml"

  | 3 ->
# 26 "lexer.mll"
            (verbose2 "+"; LAMBDA)
# 156 "lexer.ml"

  | 4 ->
# 27 "lexer.mll"
           (verbose2 "-"; DOT)
# 161 "lexer.ml"

  | 5 ->
# 28 "lexer.mll"
           ( verbose2 "("; LP)
# 166 "lexer.ml"

  | 6 ->
# 29 "lexer.mll"
           ( verbose2 ")"; RP)
# 171 "lexer.ml"

  | 7 ->
# 30 "lexer.mll"
           ( verbose2 "eof"; EOF)
# 176 "lexer.ml"

  | 8 ->
# 31 "lexer.mll"
         ( raise LexicalError)
# 181 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_start_rec lexbuf __ocaml_lex_state

and comment lexbuf =
    __ocaml_lex_comment_rec lexbuf 10
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 34 "lexer.mll"
          (comment_depth := !comment_depth+1; comment lexbuf)
# 192 "lexer.ml"

  | 1 ->
# 35 "lexer.mll"
          (comment_depth := !comment_depth-1;
           if !comment_depth > 0 then comment lexbuf )
# 198 "lexer.ml"

  | 2 ->
# 37 "lexer.mll"
         (raise Eof)
# 203 "lexer.ml"

  | 3 ->
# 38 "lexer.mll"
         (comment lexbuf)
# 208 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

;;

