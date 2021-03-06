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
  val hack = ref 0
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


  (* debugging functions *)
  fun printRecordFields((x,y)::rest) = printType(y) ^ printRecordFields(rest)
    | printRecordFields(nil) = ""

  and printType(T.NIL) = "NIL"
    | printType(T.INT) = "INT"
    | printType(T.UNIT) = "UNIT"
    | printType(T.STRING) = "STRING"
    | printType(T.NAME(x,_)) = ("NAME: " ^ S.name(x))
    | printType(T.ARRAY(x,_)) = ("ARRAY: " ^ printType(x))
    | printType(T.RECORD(x,_)) = ("RECORD: " ^ printRecordFields(x))
  and printTYPE (t) = print(printType(t) ^ "\n")

  (* check for length equality of two lists *)
  fun sameListLength(l1, l2) =
    if List.length(l1) = List.length(l2) then true else false

  (* search for id in record list *)
  fun findInRecord((sym, ty)::rest, id, pos) = if S.name(id) = S.name(sym) then
    ty else findInRecord(rest, id, pos)
    | findInRecord(nil, id, pos) = (error pos (S.name(id) ^" does not exist in record"); T.INT)

  (* functions for dealing with loop variable data structure *)
  fun lookup_loopvar (key: A.symbol, nil) = false
      | lookup_loopvar (key: A.symbol, x::rest) = if key = x then true else lookup_loopvar(key, rest)

  (* placeholders for return values *)
  val ret = {exp=(), ty=T.INT}
  val retunit = {exp=(), ty=T.UNIT}
 
  (* macros for depth management in ForExp *)
  fun forInit(name) = (loop_level := !loop_level + 1; loopvars := name :: !loopvars)
  fun forDeinit() = (loop_level := !loop_level - 1; loopvars := tl(!loopvars))

  (* converts variable to symbol *)
  fun varsym(name: A.var) =
    case name of
       A.SimpleVar(sym, _) => sym
     | A.FieldVar (_, sym, _) => sym
     | A.SubscriptVar (v, _, _) => varsym(v)

  (* compares two expressions for comparison equality *)
  fun checkInt ({exp=exp1, ty=T.INT}, {exp=exp2, ty=T.INT}, pos) = ret
    | checkInt ({exp=exp1, ty=T.STRING}, {exp=exp2, ty=T.STRING}, pos) = ret
    | checkInt ({exp=_, ty=_}, {exp=_, ty=_}, pos) = (error pos ("must use type int"); ret)

  (* compares two expression types for legality of comparison *)
  fun checkNeqEq ({exp=exp1, ty=T.INT}, {exp=exp2, ty=T.INT}, pos) = ret
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

  (* same as above but returns a boolean instead of a return value *)
  fun boolTypes (T.INT, T.INT) = true
    | boolTypes (T.STRING, T.STRING) = true
    | boolTypes (T.RECORD(r, unique), T.NIL) = true
    | boolTypes (T.NIL, T.RECORD(r, unique)) = true
    | boolTypes (T.ARRAY(a1, unique1), T.ARRAY(a2, unique2)) =
        if unique1 = unique2 then true
        else false
    | boolTypes (T.RECORD(r1, unique1), T.RECORD(r2, unique2)) =
        if unique1 = unique2 then true
        else false
    | boolTypes (_, _) = false

  fun stringReturn() = {exp=(), ty=T.STRING}

  fun extractType({exp, ty}) = ty

  fun getName(T.NAME(sym, ref(SOME(t)))) = getName(t)
     | getName (t) = t

  (* macro for searching for a type in tenv *)
  fun typeLookup(tenv, pos, typ) =
    case S.look(tenv, typ) of
         SOME(typ) => getName(typ)
       | NONE => (error pos("Undefined type: " ^ S.name(typ)); T.INT)

  (* constructs a list of names declared as function parameters *)
  fun makeNameList({var={name, escape}, typ, pos}::rest) =
    name::makeNameList(rest)
  | makeNameList (nil) = nil

  (* contrsucts a list of types declared as functino parameters *)
  fun makeTypeList(tenv, {var={name, escape}, typ, pos}::rest, names) =
    if not(funcCheckItemList(name, tl(names))) then
      typeLookup(tenv, pos, typ)::makeTypeList(tenv, rest, tl(names))
    else makeTypeList(tenv, rest, tl(names))
    | makeTypeList(tenv, nil, names) = []
 
  (* convert parameters to formals for function decs *)
  and funcCheckItemList(item:S.symbol, x::rest) =
     if item = x then false else funcCheckItemList(item, rest)
     | funcCheckItemList(item:S.symbol, nil) = true

  (* creates temp environment to use when type checking function contents *)
  fun createFuncEnv({var={name, escape}, typ, pos}::rest, env, tenv) =
    let
      val new_type = typeLookup(tenv, pos, typ)
    in
      createFuncEnv(rest, S.enter(env, name, E.VARentry{access=(), ty=new_type}), tenv)
    end
  | createFuncEnv(nil, env, tenv) = env
   
  fun findLoops (T.NAME(sym1, typ1), tenv, master, pos) =
    if master = sym1 then (error pos("Cyclic types"); true)
    else (case !typ1
      of SOME(x) => findLoops(x, tenv,  master, pos)
        | NONE => false)
 | findLoops (_, tenv, master, pos) = false


  fun checkRecExp((sym, t)::xs) =
    (case getName(t) of
      T.NAME(_, _) => true 
    | _ => checkRecExp(xs)
    )
 | checkRecExp(nil) = false

 (**************************************************************************
  *                   TRANSLATING TYPE EXPRESSIONS                         *
  *                                                                        *
  *              transty : (E.tenv * A.ty) -> (T.ty * A.pos)               *
  *************************************************************************)
  fun transty (tenv, A.ArrayTy(id, pos)) =
    (case S.look(tenv, id) of
        SOME(ty) => (T.ARRAY(ty, ref ()), pos)
      | NONE => (error pos("1unkown type:" ^ S.name(id)); (T.ARRAY(T.INT, ref ()), pos)))
    
      | transty (tenv, A.NameTy(id, pos)) =
      (case S.look(tenv, id) of
            SOME(ty) => (T.NAME(id, ref(SOME(ty))), pos)
          | NONE => (error pos("2unknown type: " ^ S.name(id)); (T.UNIT, pos)))
    | transty (tenv, A.RecordTy({name, typ, pos}::rest)) =
      (checkForDups({name=name, typ=typ, pos=pos}::rest, nil);
       (T.RECORD(consRecordPairs({name=name, typ=typ, pos=pos}::rest, tenv), ref ()), pos)
      )
    | transty (tenv, A.RecordTy(nil)) = (T.RECORD(nil, ref ()), 0)

  and checkForDups({name, typ, pos}::rest, seenSoFar) =
   (if (checkItemList(name, seenSoFar)) then ()
    else error pos("duplicate item: " ^ S.name(name));
    checkForDups(rest, name::seenSoFar))
  | checkForDups(nil, seenSoFar) = ()

  and checkItemList(item:S.symbol, x::rest) =
     if item = x then false else checkItemList(item, rest)
     | checkItemList(item:S.symbol, nil) = true

  and consRecordPairs({name, typ, pos}::rest, tenv) =
    (case S.look(tenv, typ) of
      SOME(found_typ) => (name, found_typ)::consRecordPairs(rest, tenv)
        | NONE => (error pos("undefined type " ^ S.name(typ)); (name, T.UNIT)::consRecordPairs(rest, tenv))
    )
  | consRecordPairs(nil, tenv) = []


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

          | g (A.VarExp(var_exp)) = h(var_exp)
          | g (A.StringExp (exp, pos)) = stringReturn()
          | g (A.IntExp (_)) = ret
          | g (A.NilExp) = {exp=(), ty=T.NIL}
          | g (A.SeqExp(nil)) = {exp=(), ty=T.UNIT}
          | g (A.SeqExp((exp, pos)::nil)) = g exp
          | g (A.SeqExp((exp, pos)::rest)) = (g exp; g(A.SeqExp(rest)))
          | g (A.RecordExp{fields, typ, pos}) =
              (case getName(getOpt(S.look(tenv, typ), T.NIL)) of
                T.RECORD(found_pairs, unique) =>
                if checkRecExp(found_pairs) then
                  (transexp (env, recursiveRecords(found_pairs,
                  tenv, pos)) expr)
                else
                (if (not( sameListLength(found_pairs, fields))) then ret
                   else (
                   if compNames(fields, found_pairs, true) then
                          compTypes(fields, found_pairs) else ();
                          {exp=(), ty=T.RECORD(found_pairs, unique)}
                   )
                )
                | _ => (error pos("undefined record type"); ret)
              )
          | g (A.ArrayExp{typ, size, init, pos}) =
            let
              val lookup = getOpt(S.look(tenv, typ), T.NIL)
              val init_type = extractType(g(init)) 
            in
              case lookup of
                T.ARRAY(arr_type, unique) =>
                  if getName(arr_type) = getName(init_type) orelse
                     getName(init_type) = T.NIL
                  then
                    if extractType(g(size)) = T.INT
                    then {exp=(), ty=T.ARRAY(arr_type, unique)}
                    else (error pos("array size must be of type INT"); ret)
                  else (error pos("array types must be the same"); ret)
                | _ => (error pos("Type does not match array"); ret)
            end
          | g (A.LetExp {decs, body, pos}) =
           (loopvars_temp := !loopvars;
            loopvars := nil;
            (let
              val (env_, tenv_) = transdecs(env, tenv, decs)
            in
               (gt := transexp(env_, tenv_) body;
               loopvars := !loopvars_temp)
            end); !gt)
          | g (A.AppExp{func, args, pos}) =
            (case S.look(env, func) of
              SOME(E.FUNentry{level, label, formals, result}) =>
              (verifyFuncParams(formals, args, pos);
               {exp=(), ty=getName(result)})
            | SOME(E.VARentry{access, ty}) =>
                (error pos("calling a var as a function"); retunit)
            | NONE => 
                (error pos ("calling an undefined function"); retunit)
                )
          | g (A.IfExp {test, then', else', pos}) =
           (if extractType(g(test)) = T.INT then ()
            else (error pos("first exp of an if must eval to an int"));
            (case else' of
                SOME(exp2) =>
                  let
                    val then_ty = extractType(g(then'))
                    val else_ty = extractType(g(exp2))
                  in
                    if then_ty = else_ty orelse
                       else_ty = T.NIL
                    then {exp=(), ty=then_ty}
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
             retunit)
          | g (A.ForExp{var={name, escape}, lo, hi, body, pos}) =
            (if extractType(g(lo)) = T.INT andalso extractType(g(hi)) = T.INT
             then ()
             else (error pos("for ranges must be integers"));
             forInit(name);
             (let
                val body_typ = extractType(transexp(S.enter(env, name,
                                           E.VARentry{access=(), ty=extractType(g(lo))}),
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
              if boolTypes(getName(left_ty), getName(right_ty)) then ()
              else (error pos("invalid assignment, types must be the same"));
              if (lookup_loopvar(varsym(var), !loopvars))
              then (error pos("cannot assign to loop variable"))
              else ();
              retunit
            end
          | g (A.BreakExp(pos)) =
            if !loop_level > 0 then {exp=(), ty=T.UNIT}
            else (error pos("cannot break if not within a for/while stmt"); retunit)

       (* compare a list of names in a record creation *)
       and compNames((sym, exp, pos)::rest1, (master, typ)::rest2, flag) =
            if sym = master then compNames(rest1, rest2, flag)
            else (error pos ("Record field is " ^ S.name(sym) ^ " should be " ^ S.name(master));
                  compNames(rest1, rest2, false))
          | compNames(nil, nil, flag) = flag
          | compNames (_,_,flag)  = flag

      (* compare a list of types in a record creation *)
      and compTypes((sym1, exp, pos)::rest1, (sym2, master_typ)::rest2) =
          let
            val new_type = extractType(g(exp))
          in
            if boolTypes(getName(new_type) , getName(master_typ)) then compTypes(rest1, rest2)
            else (
              (error pos("Record type field mismatch. between " ^
            printType(getName(new_type)) ^ " and master: " ^
            printType(getName(master_typ)));
                  compTypes(rest1, rest2)) )
          end
        | compTypes(nil, nil) = ()
        | compTypes _ = ()

     and verifyRecordTypes((master_sym, master_typ)::rest1,
                           (sym, exp, pos)::rest2, main_pos, result) =
         let
           val new_type = extractType(g(exp))
         in
           (if boolTypes(getName(new_type), getName(master_typ)) then ()
            else (
            printTYPE(new_type) ; printTYPE(getName(master_typ));
            error pos ("Record field does not match type!!!"));
            if (S.name(master_sym) = S.name(sym)) then ()
            else (error pos ("Record field expected given"));
            verifyRecordTypes(rest1, rest2, main_pos, result)
            )
         end
      | verifyRecordTypes(nil, nil, main_pos, result) = {exp=(), ty=result}
      | verifyRecordTypes(_, _, main_pos, result) = 
            (error main_pos("fields don't match");{exp=(), ty=T.INT})

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
	  | h (A.FieldVar (v,id,pos)) =
         (case h(v) of
            {exp=e, ty=T.RECORD(r::rest,u)} =>
            {exp=(), ty=getName(findInRecord(r::rest, id, pos))}
          | {exp, ty} => (error pos("invalid record type in a fieldvar"); ret))
	  | h (A.SubscriptVar (v,exp,pos)) =
        (case h(v) of
          {exp=e, ty=T.ARRAY(typ, u)} =>
            if extractType(g(exp)) = T.INT then {exp=(), ty=getName(typ)}
            else (error pos("array subscript must be of type int"); ret)
        | _  => (if extractType(g(exp)) = T.INT then ()
                 else error pos("array subscript must be of type int"); 
                 (error pos("trying to access a simple var as an array"));
                 ret))
     
      and verifyFuncParams((ty)::rest1, (exp)::rest2, pos) =
        if (getName(extractType(g(exp))) =
            getName(ty)) then verifyFuncParams(rest1, rest2, pos)
        else (error pos("mismatched types in function parameters");
              verifyFuncParams(rest1, rest2, pos))
     | verifyFuncParams _ = ()

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
                      if boolTypes(getName(init_type), getName(found_typ))
                      then
                        (S.enter(env, name, E.VARentry{access=(),
                                                       ty=found_typ}),
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
    | transdec (env, tenv, A.FunctionDec({name, params, result, body, pos}::rest)) = 
      (temp_level := !loop_level;
       loop_level := 0;
      let
        val formals = makeTypeList(tenv, params, makeNameList(params))
        val new_env =createFuncEnv(params, env, tenv)
        val body_type = extractType(transexp(new_env, tenv) body)
      in
        (loop_level := !temp_level;
        (case result of
           SOME(sym, pos) =>
            if boolTypes(getName(typeLookup(tenv, pos, sym)), getName(body_type))
            then
              transdec(S.enter(env, name, E.FUNentry{level=(), label=(),
                                                        formals=formals,
                                              result=getName(body_type)}),
                                                        tenv,
                                                        A.FunctionDec(rest))
            else 
              (error pos("body of a function must return indicated type");
              transdec(S.enter(env, name, E.FUNentry{level=(), label=(),
                                                        formals=formals,
                                              result=typeLookup(tenv,pos,sym)}),
                                                        tenv,
                                                        A.FunctionDec(rest)))
         | NONE =>  
             (if getName(body_type) = T.UNIT then ()
             else error pos("Procedure must return type T.UNIT instead of "^
             printType(body_type));
             transdec(S.enter(env, name, E.FUNentry{level=(), label=(),
                                                    formals=formals,
                                                    result=T.UNIT}), tenv,
                                                    A.FunctionDec(rest)))
        ))
      end)
    | transdec (env, tenv, A.FunctionDec(nil)) = (env, tenv)
    | transdec (env, tenv, A.TypeDec({name, ty, pos}::rest)) =
      let
        val (trans, post) = transty(tenv, ty)
      in
        if findLoops(trans, tenv, name, pos) then 
          let
            val tenv' = S.enter(tenv, name, T.INT)
          in
             transdec(env, tenv', A.TypeDec(rest))
          end
         else
           let
             val tenv' = S.enter(tenv, name, trans)
           in
             transdec(env, tenv', A.TypeDec(rest))
           end
      end
    | transdec (env, tenv, A.TypeDec(nil)) = (env, tenv)

  and recursiveHandler (A.VarDec{var, typ, init, pos}, env, tenv, _,_) = (env, tenv)
  | recursiveHandler (A.FunctionDec(nil), env, tenv, temp_env, temp_tenv) = (env, tenv)
  | recursiveHandler (A.FunctionDec({name, params, body, result, pos}::rest), env, tenv, temp_env, temp_tenv) =
    (case result of
       SOME(sym, pos) =>
         (case S.look(temp_env, name) of
           SOME(value) => error pos ("Redefining function: " ^ S.name(name))
          | NONE => ();
          let
            val func_entry = E.FUNentry{level=(), label=(),
                                       formals=makeTypeList(tenv, params, makeNameList(params)),
                                       result=typeLookup(tenv, pos, sym)};
          in
           recursiveHandler(A.FunctionDec(rest), S.enter(env, name, func_entry),
                            tenv, S.enter(temp_env, name, func_entry), temp_tenv)
          end
         )
     | NONE =>
         (case S.look(temp_env, name) of
           SOME(value) => (error pos ("Redefining function: " ^ S.name(name)))
         | NONE => ();
         let
         val func_entry = E.FUNentry{level=(), label=(), formals=makeTypeList(tenv,
                                     params, makeNameList(params)),
                                     result=T.UNIT};
         in
         recursiveHandler(A.FunctionDec(rest), S.enter(env, name, func_entry),
                          tenv, S.enter(temp_env, name, func_entry), temp_tenv)
         end)
    )
  | recursiveHandler (A.TypeDec(nil), env, tenv, temp_env, temp_tenv) = (env, tenv)
  | recursiveHandler (A.TypeDec({name, ty, pos}::rest), env, tenv, temp_env, temp_tenv) =
    (case S.look(temp_tenv, name) of
       SOME(value) => error pos ("Redefining type: " ^ S.name(name))
      | NONE => ();
      let
        val type_entry = T.NAME(name, ref(NONE))
      in
        recursiveHandler(A.TypeDec(rest), env, S.enter(tenv, name, type_entry),
        temp_env, S.enter(temp_tenv, name, type_entry))
      end)

  and recursiveRecords((name,T.NAME(sym, t))::rest, tenv, pos) = (t:= S.look(tenv,sym); 
                                                                recursiveRecords(rest,tenv,pos))
    | recursiveRecords((name,ty)::rest, tenv, pos) = recursiveRecords(rest,tenv,pos)
    | recursiveRecords(nil, tenv, pos) = tenv


  (*** transdecs : (E.env * E.tenv * A.dec list) -> (E.env * E.tenv) ***)
  and transdecs (env,tenv,nil) = (env, tenv)
    | transdecs (env,tenv,dec::decs) =
    let 
      val (mut_env, mut_tenv) = recursiveHandler(dec, env, tenv, S.empty, S.empty)
	val (env',tenv') = transdec (mut_env, mut_tenv, dec)
 	 in transdecs (env',tenv',decs)
	end

  (*** transprog : A.exp -> {exp : ir_code, ty : T.ty} ***)
  fun transprog prog = transexp (E.base_env, E.base_tenv) prog

end  (* structure Semant *)
