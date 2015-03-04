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
  val loop_level = ref 0
  val temp_level = ref 0
  val error = ErrorMsg.error
  type looplist = (A.symbol list) ref
  val loopvars : looplist = ref([])
  val loopvars_temp : looplist = ref([])
  type ir_code = unit (* not used for the time being *)

  val gt = ref({exp=(), ty=T.UNIT})

  
  (*** FILL IN DETAILS OF YOUR TYPE CHECKER PLEASE !!! ***)

  (*************************************************************************
   *                       UTILITY FUNCTIONS                               *
   *************************************************************************)

  (* ...... *)

  fun lookup_loopvar (key: A.symbol, nil) = false
      | lookup_loopvar (key: A.symbol, x::rest) = if key = x then true else lookup_loopvar(key, rest)

  val ret = {exp=(), ty=T.INT}
  val retunit = {exp=(), ty=T.UNIT}
  
  fun forInit(name) = (loop_level := !loop_level + 1; loopvars := name :: !loopvars)
  fun forDeinit() = (loop_level := !loop_level - 1; loopvars := tl(!loopvars))

  fun varsym(name: A.var) =
    case name of
       A.SimpleVar(sym, _) => sym
     | A.FieldVar (_, sym, _) => sym
     | A.SubscriptVar (v, _, _) => varsym(v)

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

  fun getName(T.NAME(sym, ref(SOME(ty)))) = getName(ty)
     | getName (ty) = ty


 (**************************************************************************
  *                   TRANSLATING TYPE EXPRESSIONS                         *
  *                                                                        *
  *              transty : (E.tenv * A.ty) -> (T.ty * A.pos)               *
  *************************************************************************)
  fun transty (tenv, A.ArrayTy(id, pos)) =
    (case S.look(tenv, id) of
        SOME(ty) => (T.ARRAY(ty, ref ()), pos)
      | NONE => (error pos("1unkown type:" ^ S.name(id)); (T.ARRAY(T.INT, ref ()), pos)))
    
    (*| transty (tenv, A.RecordTy(tfields)) =
      (case tfields of)
         nil =>
      | (tfield::nil)  =>
      | (tfield::rest) => *)
    | transty (tenv, A.NameTy(id, pos)) =
      (case S.look(tenv, id) of
            SOME(ty) => (T.NAME(id, ref(SOME(ty))), pos)
          | NONE => (error pos("2unknown type: " ^ S.name(id)); (T.UNIT, pos)))
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
          | g (A.SeqExp(nil)) = {exp=(), ty=T.UNIT}
          | g (A.SeqExp((exp, pos)::nil)) = g exp
          | g (A.SeqExp((exp, pos)::rest)) = (g exp; g(A.SeqExp(rest)))
          | g (A.ArrayExp{typ, size, init, pos}) =
            let
              val lookup = getOpt(S.look(tenv, typ), T.NIL)
              val init_type = extractType(g(init)) 
            in
              case lookup of
                T.ARRAY(arr_type, unique) =>
                  if getName(arr_type) = getName(init_type)
                  then
                    if extractType(g(size)) = T.INT
                    then {exp=(), ty=T.ARRAY(arr_type, unique)}
                    else (error pos("array size must be of type INT"); ret)
                  else (error pos("array types must be the same"); ret)
                | _ => (error pos("some other array shit"); ret)
            end
          | g (A.LetExp {decs, body, pos}) =
           ((*temp_level := !loop_level;
            loop_level := 0; *)
            loopvars_temp := !loopvars;
            loopvars := nil;
            (let
              val (env_, tenv_) = transdecs(env, tenv, decs)
            in
               ((*loop_level := !temp_level; *)
               gt := transexp(env_, tenv_) body;
               loopvars := !loopvars_temp)
            end); !gt)
          | g (A.IfExp {test, then', else', pos}) =
           (if extractType(g(test)) = T.INT then ()
            else (error pos("first exp of an if must eval to an int"));
            (case else' of
                SOME(exp2) =>
                  let
                    val then_ty = extractType(g(then'))
                    val else_ty = extractType(g(exp2))
                  in
                    if then_ty = else_ty then {exp=(), ty=then_ty}
                    else (error pos("then and else exps must return same type"); ret)
                  end
              | NONE =>
                  let
                    val then_ty = extractType(g(then'))
                  in
                    if then_ty = T.UNIT then {exp=(), ty=T.UNIT}
                    else (error pos("then exp must return UNIT"); ret)
                  end))
          | g (A.WhileExp{test, body, pos}) =
            (if not(extractType(g(test)) = T.INT) then 
            (error pos("first exp of a while must eval to an int"))
             else ();
            loop_level := !loop_level + 1;
            (let
               val exp2_ty = extractType(g(body))
             in
               if exp2_ty = T.UNIT then ()
               else (error pos("while exp must return UNIT"))
             end);
             loop_level := !loop_level - 1;
             ret)
          | g (A.ForExp{var={name, escape}, lo, hi, body, pos}) =
            (if extractType(g(lo)) = T.INT andalso extractType(g(hi)) = T.INT
             then ()
             else (error pos("for ranges must be integers"));
             forInit(name);
             (let
                val body_typ = extractType(transexp(S.enter(env, name, E.VARentry{access=(), ty=extractType(g(lo))}),
                                                            tenv) body)
              in
               if body_typ = T.UNIT then (forDeinit(); {exp=(), ty=T.UNIT})
                else (forDeinit(); error pos("body of for must return UNIT"); {exp=(), ty=T.UNIT})
              end)
            )
          | g (A.AssignExp{var, exp, pos}) =
            let
              val left_ty = extractType(h(var))
              val right_ty = extractType(g(exp))
            in
              if left_ty = right_ty then ()
              else (error pos("invalid assignment, types must be the same"));
              if (lookup_loopvar(varsym(var), !loopvars)) then (error pos("cannot assign to loop variable"))
              else ();
              retunit
            end
          | g (A.BreakExp(pos)) =
            if !loop_level > 0 then {exp=(), ty=T.UNIT}
            else (error pos("cannot break if not within a for/while stmt"); retunit)
          | g _ (* other cases *) = (print("here"); ret)

        (* function dealing with "var", may be mutually recursive with g *)
        and h (A.SimpleVar (id,pos)) =
          let
            val result = S.look(env, id)
          in
            case result of
                 SOME(E.VARentry{access=_, ty=ty1}) => {exp=(), ty=ty1}
               | NONE => (error pos ("cannot find variable " ^ S.name(id)); ret)
               | _ => (error pos("cannot use function as variable"); ret)
          end
	  | h (A.FieldVar (v,id,pos)) = (* ... *) {exp=(), ty=T.INT}
	  | h (A.SubscriptVar (v,exp,pos)) =
        (case h(v) of
          {exp=e, ty=T.ARRAY(typ, u)} =>
            if extractType(g(exp)) = T.INT then ()
            else error pos("array subscript must be of type int")
        | _  => (if extractType(g(exp)) = T.INT then ()
                 else error pos("array subscript must be of type int"); 
                 (error pos("trying to access a simple var as an array")));
         ret)
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
                      if init_type = getName(found_typ)
                      then
                        (S.enter(env, name, E.VARentry{access=(),
                                                       ty=init_type}),
                                                       tenv)
                      else
                        (print(S.name(sym1)^ "\n");error pos("Conflicting pre-existing type name:" ^ S.name(name));
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
  

