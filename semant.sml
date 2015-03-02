signature SEMANT =
sig
  type ir_code
  val transprog : Absyn.exp -> {exp: ir_code, ty: Types.ty}
end

structure Semant : SEMANT = 
struct

  structure A = Absyn
  structure E = Env
  structure S = Symbol
  structure T = Types
  val error = ErrorMsg.error
  type ir_code = unit (* not used for the time being *)

  
  (*** FILL IN DETAILS OF YOUR TYPE CHECKER PLEASE !!! ***)

  (*************************************************************************
   *                       UTILITY FUNCTIONS                               *
   *************************************************************************)

  (* ...... *)

  val ret = {exp=(), ty=T.INT}

  fun checkInt ({exp=exp1, ty=T.INT}, {exp=exp2, ty=T.INT}, pos) = ret
    | checkInt ({exp=exp1, ty=T.STRING}, {exp=exp2, ty=T.STRING}, pos) = ret
    | checkInt ({exp=_, ty=_}, {exp=_, ty=_}, pos) = (error pos ("must use type int"); ret)

  fun checkNeqEq ({exp=exp1, ty=T.INT}, {exp=exp2, ty=T.INT}, pos) = (print("josh\n"); ret)
    | checkNeqEq ({exp=exp1, ty=T.STRING}, {exp=exp2, ty=T.STRING}, pos) = ret
    | checkNeqEq ({exp=exp1, ty=T.RECORD(r, unique)}, {exp=exp2, ty=T.NIL}, pos) = ret
    | checkNeqEq ({exp=exp1, ty=T.NIL}, {exp=exp2, ty=T.RECORD(r, unique)}, pos) = ret
    | checkNeqEq ({exp=exp1, ty=T.ARRAY(a1, unique1)}, {exp=exp2, ty=T.ARRAY(a2, unique2)}, pos) =
        if unique1 = unique2 then ret
        else (error pos("cannot compare differing types of arrays"); ret)
    | checkNeqEq ({exp=exp1, ty=T.RECORD(r1, unique1)}, {exp=exp2, ty=T.RECORD(r2, unique2)}, pos) =
        if unique1 = unique2 then ret
        else (error pos("cannot compare differing types of records"); ret)
    | checkNeqEq ({exp=exp1, ty=_}, {exp=exp2, ty=_}, pos) =
       (error pos("illegal types for eq/neq comparison"); ret)

  fun debug(pos) = (error pos("geeds r u"); ret)

  fun stringReturn() = {exp=(), ty=T.STRING}

  fun extractType({exp, ty}) = ty

 (**************************************************************************
  *                   TRANSLATING TYPE EXPRESSIONS                         *
  *                                                                        *
  *              transty : (E.tenv * A.ty) -> (T.ty * A.pos)               *
  *************************************************************************)
  fun transty (tenv, A.ArrayTy(id, pos)) =
    (case S.look(tenv, id) of
        SOME(ty) => (T.ARRAY(ty, ref ()), pos)
      | NONE => (error pos("unkown type:" ^ S.name(id)); (T.ARRAY(T.INT, ref ()), pos)))
    
    | transty (tenv, _ (* other cases *)) = (* ... *) (T.UNIT, 0)

  (* ...... *)




 (**************************************************************************
  *                   TRANSLATING EXPRESSIONS                              *
  *                                                                        *
  *  transexp : (E.env * E.tenv) -> (A.exp -> {exp : ir_code, ty : T.ty})  *
  **************************************************************************)
  fun transexp (env, tenv) expr =
    let fun g (A.OpExp {left,oper=A.NeqOp,right,pos}) = 
                   checkNeqEq(g left, g right, pos)

          | g (A.OpExp {left,oper=A.EqOp,right,pos}) =
                   checkNeqEq(g left, g right, pos)

          | g (A.OpExp {left,oper,right,pos}) =
		           checkInt(g left, g right, pos)

          | g (A.RecordExp {typ,fields,pos}) =
                   (* ... *) {exp=(), ty=T.RECORD ((* ? *) [], ref ())}

          | g (A.VarExp(var_exp)) = h(var_exp)
          | g (A.StringExp (exp, pos)) = stringReturn()
          | g (A.IntExp (_)) = ret
          | g (A.SeqExp(nil)) = ret
          | g (A.SeqExp((exp, pos)::nil)) = g exp
          | g (A.SeqExp((exp, pos)::rest)) = (g exp; g(A.SeqExp(rest)))
          | g (A.ArrayExp{typ, size, init, pos}) =
            let
              val lookup = getOpt(S.look(tenv, typ), T.NIL)
              val init_type = extractType(g(init)) 
            in
              case lookup of
                T.ARRAY(arr_type, unique) =>
                  if arr_type = init_type
                  then
                    if extractType(g(size)) = T.INT
                    then {exp=(), ty=T.ARRAY(arr_type, unique)}
                    else (error pos("array size must be of type INT"); ret)
                  else (error pos("array types must be the same"); ret)
                | _ => (error pos("some other array shit"); ret)
            end
          | g (A.LetExp {decs, body, pos}) =
            let
              val (env_, tenv_) = transdecs(env, tenv, decs)
            in
              (transexp(env_, tenv_) body)
            end
              
          | g _ (* other cases *) = {exp=(), ty=T.INT} 

        (* function dealing with "var", may be mutually recursive with g *)
        and h (A.SimpleVar (id,pos)) =
          let
            val result = S.look(env, id)
          in
            case result of
                 SOME(E.VARentry{access=_, ty=ty1}) => {exp=(), ty=ty1}
               | NONE => (error pos ("cannot find variable" ^ S.name(id)); ret)
               | _ => (error pos("cannot use function as variable"); ret)
          end
	  | h (A.FieldVar (v,id,pos)) = (* ... *) {exp=(), ty=T.INT}
	  | h (A.SubscriptVar (v,exp,pos)) = (* ... *) {exp=(), ty=T.INT}

     in g expr
    end

 (**************************************************************************
  *                   TRANSLATING DECLARATIONS                             *
  *                                                                        *
  *  transdec : (E.env * E.tenv * A.dec) -> (E.env * E.tenv)               *
  **************************************************************************)
  and transdec (env, tenv, A.VarDec({var={name, escape}, typ, init, pos})) =
    let
      val init_type = extractType(transexp(env, tenv) init)
    in
        case typ of
             SOME(sym1, pos1) =>
               (case S.look(tenv, sym1) of
                    SOME(found_typ) =>
                      if init_type = found_typ
                      then
                        (S.enter(env, name, E.VARentry{access=(),
                                                       ty=init_type}),
                                                       tenv)
                      else
                        (error pos("Conflicting pre-existing type name:" ^ S.name(name));
                        (S.enter(env, name,
                                 E.VARentry{access=(), ty=init_type}), tenv))
                  | NONE => (error pos("Unknown type:" ^ S.name(name));
                             (S.enter(env, name,
                                      E.VARentry{access=(), ty=init_type}),
                                      tenv)))
           | NONE =>
              (case init_type of
                  T.NIL => (error pos("nil assignment not bound to record");
                            (S.enter(env, name,
                                     E.VARentry{access=(), ty=init_type}),
                             tenv))
                | t => (S.enter(env, name,
                                E.VARentry{access=(), ty=init_type}), tenv))
    end
    | transdec (env, tenv, A.FunctionDec(declist)) = (* ... *) (env, tenv)
    | transdec (env, tenv, A.TypeDec({name, ty, pos}::rest)) =
      let
        val (trans, post) = transty(tenv, ty)
        val tenv' = S.enter(tenv, name, trans)
      in
        transdec(env, tenv', A.TypeDec(rest))
      end
    | transdec (env, tenv, A.TypeDec(nil)) = (env, tenv)


  (*** transdecs : (E.env * E.tenv * A.dec list) -> (E.env * E.tenv) ***)
  and transdecs (env,tenv,nil) = (env, tenv)
    | transdecs (env,tenv,dec::decs) =
	let val (env',tenv') = transdec (env,tenv,dec)
 	 in transdecs (env',tenv',decs)
	end

  (*** transprog : A.exp -> {exp : ir_code, ty : T.ty} ***)
  fun transprog prog = transexp (E.base_env, E.base_tenv) prog

end  (* structure Semant *)
  

