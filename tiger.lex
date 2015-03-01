(* Josh Isenstein *)
type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1
val strSize = ref 0
val string = ref ""
val instring = ref false
val comm_level = ref 0

fun ascii(str) = Char.toString(chr(valOf(Int.fromString(substring(str, 1, 3)))))
fun ascii_int(str) = valOf(Int.fromString(substring(str, 1, 3)))
fun ctrl(str) = valOf(String.fromString(str)) 

val eof = fn () =>
    let val pos = hd(!linePos) 
       in
           if (!instring)
                  then (instring:=false;
                        ErrorMsg.error pos ("unterminated string"))
           else if (!comm_level <> 0)
                  then (comm_level := 0;
                        ErrorMsg.error pos ("unterminated comment"))
           else (); Tokens.EOF(pos,pos)
end
%% 
%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));
%s COMMENT STRING;
DIGIT = [0-9];
DIGITS = {DIGIT}+;
WHITESPACE = [ \t\r]+;
ID = [a-zA-Z][a-zA-Z0-9_]*;
NEWLINE = "\\n";
TAB = "\\t";
CONTROL = "\\^"[@A-Z\_^];
ASCII = "\\"{DIGIT}{3};
QUOTE = "\\\"";
BSLASH = "\\\\";
FORMATTING = [ \r\t\n\b\f];
IGNORE = "\\"{FORMATTING}+"\\";
%%
<COMMENT>\n	=>       (lineNum := !lineNum+1;
                      linePos := yypos :: !linePos;
                      continue());
<COMMENT>"/*" =>     (comm_level := !comm_level + 1; continue());
<COMMENT>"*/" =>     (comm_level := !comm_level - 1;
                      if !comm_level = 0
                      then YYBEGIN INITIAL
                      else ();
                      continue());
<COMMENT>. =>        (continue());

<STRING>\n	=>       (ErrorMsg.error yypos "newline in string";
                      lineNum := !lineNum+1;
                      linePos := yypos :: !linePos;
                      continue());
<STRING>"\"" =>      (YYBEGIN INITIAL;
                      instring := false;
                      Tokens.STRING(!string, yypos - !strSize - 1, yypos + 1));
<STRING>{IGNORE} =>  (strSize := !strSize + size(yytext); continue());
<STRING>{NEWLINE} => (string := !string ^ "\n";
                      strSize := !strSize + 2;
                      continue());
<STRING>{TAB} =>     (string := !string ^ "\t";
                      strSize := !strSize + 2;
                      continue());
<STRING>{CONTROL} => (string := !string ^ ctrl(yytext);
                      strSize := !strSize + 3;
                      continue());
<STRING>{ASCII} =>   (if ascii_int(yytext) > 255
                      then (ErrorMsg.error yypos ("Ascii character > than 255"))
                      else string := !string ^ ascii(yytext);
                      strSize := !strSize + 4;
                      continue());
<STRING>{QUOTE} =>   (string := !string ^ "\"";
                      strSize := !strSize + 2;
                      continue());
<STRING>{BSLASH} =>  (string := !string ^ "\\";
                      strSize := !strSize + 2;
                      continue());
<STRING>"\\". =>     (strSize := !strSize + 2;
                      ErrorMsg.error yypos ("Backslash in string " ^ yytext);
                      continue());
<STRING>. =>         (string := !string ^ yytext;
                      strSize := !strSize + size(yytext);
                      continue());

<INITIAL>\n	=>       (lineNum := !lineNum+1;
                      linePos := yypos :: !linePos;
                      continue());
<INITIAL>"/*"  =>    (YYBEGIN COMMENT; 
                      comm_level := !comm_level + 1;
                      continue());
<INITIAL>"\"" =>     (YYBEGIN STRING;
                      instring := true;
                      strSize := 0;
                      string := "";
                      continue());

<INITIAL>{WHITESPACE} => (continue());

<INITIAL>","            => (Tokens.COMMA(yypos, yypos+1));
<INITIAL>":"            => (Tokens.COLON(yypos, yypos+1));
<INITIAL>";"            => (Tokens.SEMICOLON(yypos, yypos+1));
<INITIAL>";"            => (Tokens.SEMICOLON(yypos, yypos+1));
<INITIAL>"."            => (Tokens.DOT(yypos, yypos+1));
<INITIAL>"+"            => (Tokens.PLUS(yypos, yypos+1));
<INITIAL>"-"            => (Tokens.MINUS(yypos, yypos+1));
<INITIAL>"*"            => (Tokens.TIMES(yypos, yypos+1));
<INITIAL>"/"            => (Tokens.DIVIDE(yypos, yypos+1));
<INITIAL>"="            => (Tokens.EQ(yypos, yypos+1));
<INITIAL>"<"            => (Tokens.LT(yypos, yypos+1));
<INITIAL>"<="           => (Tokens.LE(yypos, yypos+2));
<INITIAL>">"            => (Tokens.GT(yypos, yypos+1));
<INITIAL>">="           => (Tokens.GE(yypos, yypos+2));
<INITIAL>"<>"           => (Tokens.NEQ(yypos, yypos+2));
<INITIAL>"&"            => (Tokens.AND(yypos, yypos+1));
<INITIAL>"|"            => (Tokens.OR(yypos, yypos+1));
<INITIAL>":="           => (Tokens.ASSIGN(yypos, yypos+1));
<INITIAL>"("            => (Tokens.LPAREN(yypos, yypos+1));
<INITIAL>")"            => (Tokens.RPAREN(yypos, yypos+1));
<INITIAL>"["            => (Tokens.LBRACK(yypos, yypos+1));
<INITIAL>"]"            => (Tokens.RBRACK(yypos, yypos+1));
<INITIAL>"{"            => (Tokens.LBRACE(yypos, yypos+1));
<INITIAL>"}"            => (Tokens.RBRACE(yypos, yypos+1));

<INITIAL>while          => (Tokens.WHILE(yypos, yypos+5));
<INITIAL>var            => (Tokens.VAR(yypos,yypos+3));
<INITIAL>let            => (Tokens.LET(yypos, yypos+3));
<INITIAL>for            => (Tokens.FOR(yypos, yypos+3));
<INITIAL>to             => (Tokens.TO(yypos, yypos+2));
<INITIAL>break          => (Tokens.BREAK(yypos, yypos+5));
<INITIAL>in             => (Tokens.IN(yypos, yypos+2));
<INITIAL>end            => (Tokens.END(yypos, yypos+3));
<INITIAL>function       => (Tokens.FUNCTION(yypos, yypos+8));
<INITIAL>type           => (Tokens.TYPE(yypos, yypos+4));
<INITIAL>array          => (Tokens.ARRAY(yypos, yypos+5));
<INITIAL>if             => (Tokens.IF(yypos, yypos+2));
<INITIAL>then           => (Tokens.THEN(yypos, yypos+4));
<INITIAL>else           => (Tokens.ELSE(yypos, yypos+4));
<INITIAL>do             => (Tokens.DO(yypos, yypos+2));
<INITIAL>of             => (Tokens.OF(yypos, yypos+2));
<INITIAL>nil            => (Tokens.NIL(yypos, yypos+3));

<INITIAL>{ID}           => (Tokens.ID(yytext, yypos, yypos + size(yytext)));
<INITIAL>{DIGITS}       => (Tokens.INT(valOf(Int.fromString(yytext)),
                                       yypos,
                                       yypos + size(yytext)));

.                       => (ErrorMsg.error yypos
                                           ("illegal character " ^ yytext);
                            continue());
