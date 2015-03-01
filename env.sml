signature ENV =
sig
  type access
  type level
  type label
  type ty

  datatype enventry 
    = VARentry of {access: access, ty: ty}
    | FUNentry of {level: level, label: label, formals: ty list, result: ty}

  type tenv = ty Symbol.table
  type env = enventry Symbol.table

  val base_tenv : tenv
  val base_env : env
end

structure Env : ENV =
struct

  structure S = Symbol
  structure T = Types

  type access = unit   (* not used for the time being *)
  type level = unit    (* not used for the time being *)
  type label = unit    (* not used for the time being *)
  type ty = T.ty

  datatype enventry 
    = VARentry of {access: access, ty: ty}
    | FUNentry of {level: level, label: label, formals: ty list, result: ty}

  type tenv = ty Symbol.table

  type env = enventry Symbol.table
  fun sym(id) = Symbol.symbol(id);

  (* here you need to add all primtive types into the base_tenv *)
  val base_tenv =  let
                     val clean_env = S.empty;
                     val int_env = S.enter(clean_env, sym("int"), T.INT);
                     val string_env = S.enter(int_env, sym("string"), T.STRING);
                   in
                     string_env
                   end;
 
  (* here you need to add all primitive library functions into the base_env *)
  val base_env = let
                   val clean_env = S.empty;
                   val new_env = S.enter(clean_env, sym("print"),
                                         FUNentry{level=(), label=(),
                                                  formals=T.STRING::nil,
                                                  result=T.UNIT});
                   val new_env = S.enter(new_env, sym("flush"),
                                         FUNentry{level=(), label=(),
                                                  formals=nil, result=T.UNIT});
                   val new_env = S.enter(new_env, sym("getchar"),
                                         FUNentry{level=(), label=(),
                                                  formals=nil,
                                                  result=T.STRING});
                   val new_env = S.enter(new_env, sym("ord"),
                                         FUNentry{level=(), label=(),
                                                  formals=T.INT::nil,
                                                  result=T.INT});
                   val new_env = S.enter(new_env, sym("chr"),
                                         FUNentry{level=(), label=(),
                                                  formals=T.INT::nil,
                                                  result=T.STRING});
                   val new_env = S.enter(new_env, sym("size"),
                                         FUNentry{level=(), label=(),
                                                  formals=T.STRING::nil,
                                                  result=T.INT});
                   val new_env = S.enter(new_env, sym("substring"),
                                         FUNentry{level=(), label=(),
                                                  formals=T.STRING::T.INT::T.INT::nil,
                                                  result=T.STRING});
                   val new_env = S.enter(new_env, sym("concat"),
                                         FUNentry{level=(), label=(),
                                                  formals=T.STRING::T.STRING::nil,
                                                  result=T.STRING});
                   val new_env = S.enter(new_env, sym("not"),
                                         FUNentry{level=(), label=(),
                                                  formals=T.INT::nil,
                                                  result=T.INT});
                   val new_env = S.enter(new_env, sym("not"),
                                         FUNentry{level=(), label=(),
                                                  formals=T.INT::nil,
                                                  result=T.INT});
                   val new_env = S.enter(new_env, sym("exit"),
                                         FUNentry{level=(), label=(),
                                                  formals=T.INT::nil,
                                                  result=T.UNIT});
                 in
                   new_env
                 end;

end  (* structure Env *)
  
