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

  fun checkNeqEq ({exp=exp1, ty=T.INT}, {exp=exp2, ty=T.INT}, pos) = (error pos("Geeds r u"); ret)
    | checkNeqEq ({exp=exp1, ty=T.STRING}, {exp=exp2, ty=T.STRING}, pos) = (error pos("Jeeds r u"); ret)
    | checkNeqEq ({exp=exp1, ty=T.RECORD(r, unique)}, {exp=exp2, ty=T.NIL}, pos) = (error pos("geeds r u1"); ret)
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
  fun transty (tenv, A.ArrayTy(id, pos)) = (* ... *) (T.UNIT, pos)
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

          | g (A.StringExp (exp, pos)) = stringReturn()
          | g (A.LetExp {decs, body, pos}) =
            let
              val (env_, tenv_) = transdecs(env, tenv, decs)
            in
              (transexp(env_, tenv_) body)
            end
              
          | g _ (* other cases *) = {exp=(), ty=T.INT} 

        (* function dealing with "var", may be mutually recursive with g *)
        and h (A.SimpleVar (id,pos)) = (* ... *) {exp=(), ty=T.INT}
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
    | transdec (env, tenv, A.TypeDec(declist)) = (* ... *) (env, tenv)


  (*** transdecs : (E.env * E.tenv * A.dec list) -> (E.env * E.tenv) ***)
  and transdecs (env,tenv,nil) = (env, tenv)
    | transdecs (env,tenv,dec::decs) =
	let val (env',tenv') = transdec (env,tenv,dec)
 	 in transdecs (env',tenv',decs)
	end

  (*** transprog : A.exp -> {exp : ir_code, ty : T.ty} ***)
  fun transprog prog = transexp (E.base_env, E.base_tenv) prog

end  (* structure Semant *)
  

