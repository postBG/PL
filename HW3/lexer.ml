# 13 "lexer.mll"
 
 open Parser
 exception Eof
 exception LexicalError
 let verbose1 s =  (* (print_string s; print_newline(); s) *) s
 let verbose2 s =  (* (print_string s; print_newline()) *) ()
 let comment_depth = ref 0
 let keyword_tbl = Hashtbl.create 31
 let _ = List.iter (fun (keyword, tok) -> Hashtbl.add keyword_tbl keyword tok)
                   [("unit", UNIT);
				    ("true", TRUE);
                    ("false", FALSE);
                    ("not", NOT);
                    ("if", IF);
                    ("then",THEN);
                    ("else",ELSE);
                    ("let", LET);
                    ("in", IN);
                    ("end", END);
	    	        ("proc", PROC);
                    ("while", WHILE);
                    ("do"   , DO);
                    ("read" , READ);
                    ("write", WRITE)
                  ] 

# 29 "lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\233\255\234\255\235\255\236\255\237\255\239\255\240\255\
    \241\255\002\000\243\255\244\255\245\255\246\255\247\255\248\255\
    \249\255\250\255\251\255\085\000\016\000\032\000\002\000\254\255\
    \242\255\035\000\252\255\253\255\035\000\036\000\255\255\254\255\
    ";
  Lexing.lex_backtrk = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\022\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\003\000\002\000\017\000\000\000\255\255\
    \255\255\255\255\255\255\255\255\003\000\003\000\255\255\255\255\
    ";
  Lexing.lex_default = 
   "\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\255\255\255\255\255\255\255\255\000\000\
    \000\000\026\000\000\000\000\000\255\255\255\255\000\000\000\000\
    ";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\022\000\022\000\022\000\022\000\022\000\000\000\022\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \022\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\
    \021\000\005\000\016\000\018\000\007\000\017\000\006\000\015\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\020\000\020\000\
    \020\000\020\000\009\000\008\000\013\000\014\000\012\000\024\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\020\000\020\000\
    \020\000\020\000\023\000\029\000\031\000\028\000\030\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\010\000\000\000\011\000\000\000\000\000\
    \000\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\004\000\019\000\003\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \000\000\000\000\000\000\000\000\019\000\000\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\027\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\022\000\022\000\000\000\255\255\022\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\022\000\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\009\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\020\000\020\000\
    \020\000\020\000\021\000\025\000\028\000\025\000\029\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\000\000\255\255\000\000\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\019\000\000\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \255\255\255\255\255\255\255\255\019\000\255\255\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\025\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255";
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
# 45 "lexer.mll"
             ( start lexbuf )
# 158 "lexer.ml"

  | 1 ->
# 46 "lexer.mll"
            ( comment_depth :=1;
              comment lexbuf;
              start lexbuf )
# 165 "lexer.ml"

  | 2 ->
# 49 "lexer.mll"
              ( NUM (int_of_string (verbose1 (Lexing.lexeme lexbuf))) )
# 170 "lexer.ml"

  | 3 ->
# 50 "lexer.mll"
          ( let id = verbose1 (Lexing.lexeme lexbuf)
            in try Hashtbl.find keyword_tbl id
               with _ -> ID id
            )
# 178 "lexer.ml"

  | 4 ->
# 54 "lexer.mll"
           (verbose2 "+"; PLUS)
# 183 "lexer.ml"

  | 5 ->
# 55 "lexer.mll"
           (verbose2 "-";MINUS)
# 188 "lexer.ml"

  | 6 ->
# 56 "lexer.mll"
           ( verbose2 "*"; STAR)
# 193 "lexer.ml"

  | 7 ->
# 57 "lexer.mll"
           ( verbose2 "/"; SLASH)
# 198 "lexer.ml"

  | 8 ->
# 58 "lexer.mll"
           (verbose2 "="; EQUAL)
# 203 "lexer.ml"

  | 9 ->
# 59 "lexer.mll"
           ( verbose2 "<"; LB)
# 208 "lexer.ml"

  | 10 ->
# 60 "lexer.mll"
           ( verbose2 ">"; RB)
# 213 "lexer.ml"

  | 11 ->
# 61 "lexer.mll"
           ( verbose2 "]"; RBLOCK)
# 218 "lexer.ml"

  | 12 ->
# 62 "lexer.mll"
           ( verbose2 "["; LBLOCK)
# 223 "lexer.ml"

  | 13 ->
# 63 "lexer.mll"
            (verbose2 ":="; COLONEQ)
# 228 "lexer.ml"

  | 14 ->
# 64 "lexer.mll"
           ( verbose2 ";"; SEMICOLON)
# 233 "lexer.ml"

  | 15 ->
# 65 "lexer.mll"
        ( verbose2 ","; COMMA)
# 238 "lexer.ml"

  | 16 ->
# 66 "lexer.mll"
        ( verbose2 "."; PERIOD)
# 243 "lexer.ml"

  | 17 ->
# 67 "lexer.mll"
           ( verbose2 "("; LP)
# 248 "lexer.ml"

  | 18 ->
# 68 "lexer.mll"
           ( verbose2 ")"; RP)
# 253 "lexer.ml"

  | 19 ->
# 69 "lexer.mll"
        ( verbose2 "{"; LC)
# 258 "lexer.ml"

  | 20 ->
# 70 "lexer.mll"
        ( verbose2 "}"; RC)
# 263 "lexer.ml"

  | 21 ->
# 71 "lexer.mll"
           ( verbose2 "eof"; EOF)
# 268 "lexer.ml"

  | 22 ->
# 72 "lexer.mll"
         (raise LexicalError)
# 273 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_start_rec lexbuf __ocaml_lex_state

and comment lexbuf =
    __ocaml_lex_comment_rec lexbuf 25
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 75 "lexer.mll"
          (comment_depth := !comment_depth+1; comment lexbuf)
# 284 "lexer.ml"

  | 1 ->
# 76 "lexer.mll"
          (comment_depth := !comment_depth-1;
           if !comment_depth > 0 then comment lexbuf )
# 290 "lexer.ml"

  | 2 ->
# 78 "lexer.mll"
         (raise Eof)
# 295 "lexer.ml"

  | 3 ->
# 79 "lexer.mll"
         (comment lexbuf)
# 300 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

;;

