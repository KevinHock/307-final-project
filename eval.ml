open Ast;;
open Env;;
open Store;;

let rec alloc_size alloc_type = match alloc_type with
  |Int -> 1
  |Array (inner_type, size) -> size * (alloc_size inner_type)
  |Pointer _ -> 1
  |Void -> raise (Invalid_argument "cannot allocate void")
;;

(*Takes a symbol table entry and breaks it down to its entry and then updates the location and makes a recursive call passing in the other entries as an argument.*)
let rec allocSym (loc:int) (st:symTable) : (int * symTable)	= match st with
	[]->(loc,st)
	|((name, Var entry)::xs) -> let newloc, newsym = allocSym (loc+(alloc_size entry.vtype)) xs in 
    (newloc, (name, Var {entry with loc=loc}) :: newsym)
  |((name, Fun entry)::xs)-> 
    let newloc, newsym = (allocSym loc xs ) in
    (newloc, (name, Fun entry) :: newsym)
;;

let rec allocRec (ps:proc_state) (st:symTable) : (proc_state* symTable) = match st with
  [] -> ps, st
  |((name, Var entry)::xs) -> 
    let newps = {ps with bp = ps.bp - (alloc_size entry.vtype)} in 
    let newps2, newsym = allocRec newps xs in 
    (newps2, (name, Var {entry with loc=newps.bp}) :: newsym)

let allocateMem [st] : environment = let _, newst = allocSym 0 st in [newst]
type stmtEvalRes = Next | BreakOut | ContinueOn;;

let print_var (name:string) (env:environment) (store:store) : unit = 
  let varloc = binding_of env name in 
  let res = match varloc with 
    | Var variable -> value_at store variable.loc
  in 
  print_string name;
  print_string ": ";
  print_string (string_of_int res);
  print_string "\n"

let rec expr_loc (expr:expr) (ps:proc_state) (env:environment) (store:store) : (int*store) = (match expr with
        | At (base, offset) -> let index, newStore = (eval_expr offset ps env store) in
          let base_loc, newStore2 = (expr_loc base ps env newStore) in
          ( base_loc + index, newStore2)
        | Deref (expr) ->
          eval_expr expr ps env store
        | Id (v) ->
        let loc = binding_of env v in 
        match loc with
        | (Var ve) -> (ve.loc, store)
      )
and eval_exprs (exprs:expr list) (ps:proc_state) (env:environment) (store: store) : (int list * store) = match exprs with
  | [] -> ([], store)
  | (x::xs) -> let res, newstore = eval_expr x ps env store in
    let new_list, newstore2 = (eval_exprs xs ps env newstore) in
    (res::new_list, newstore2)
and assign_args (args:int list) (params: varEntry list) (store: store) : store =
  match args with
    | [] -> store
    | (arg::newArgs) -> 
      let param::newParams = params in  
      let newStore = insert_value store param.loc arg in 
      assign_args newArgs newParams newStore

(* eval_expr and eval_cond return a store because in full
C-flat they do have side effects (pre- and post-increment,
function calls) *)
and eval_expr (expr:expr) (ps:proc_state) (env:environment) (store:store) : (int*store) = match expr with
	| Add (e1, e2) -> 
		let (r1,sto) = eval_expr e1 ps env store in
		let (r2,s2) = eval_expr e2 ps env sto in
		(r1 + r2, s2)
	| Sub (e1, e2) ->
		let (r1,sto) = eval_expr e1 ps env store in
		let (r2,s2) = eval_expr e2 ps env sto in
		(r1 - r2, s2)
	| Mul (e1, e2) ->
		let (r1,sto) = eval_expr e1 ps env store in
		let (r2,s2) = eval_expr e2 ps env sto in
		(r1 * r2, s2)
	| Div (e1, e2) ->
		let (r1,sto) = eval_expr e1 ps env store in
		let (r2,s2) = eval_expr e2 ps env sto in
		(r1 / r2, s2)
	| Neg (e1) ->
		let (r1,sto) = eval_expr e1 ps env store in
		(r1 * -1,sto)
	| Pre (e1) ->
		(
				let locValue, newStore1 = expr_loc e1 ps env store in
				let r1 = value_at newStore1 locValue in
		    let newStore2 = insert_value newStore1 locValue (r1+1) in
					(r1 + 1, newStore2)
		)
	| Post (e1) ->
		(
        let locValue, newStore1 = expr_loc e1 ps env store in
        let r1 = value_at newStore1 locValue in
        let newStore2 = insert_value newStore1 locValue (r1+1) in 
          (r1, newStore2)
		)
	| IntConst i -> 
		(i,store)
  | Deref (expr) -> let (locValue, newStore) = eval_expr expr ps env store in
    ((value_at newStore locValue), newStore)
  | AddressOf (expr) -> (expr_loc expr ps env store)
  | Call(fname,exprs) -> 
    let entry = binding_of env fname in
    (match entry with
      |(Fun f) ->
        let scope = f.syms in
        let (newps:proc_state), newscope = allocRec ps scope in
        let args, newstore1 = eval_exprs exprs ps env store in
        let unwrapVar symEntry = (match symEntry with
          | (_, Var varEntry) -> varEntry
        ) in
        let isArg varEntry = (varEntry.kind == Param) in
        let allvars = List.map unwrapVar newscope in
        let argvars:varEntry list = List.filter isArg allvars in
        let env2 = (match env with 
          | [global] -> [newscope;global]
          | [old_scope;global] -> [newscope;global]
        )
        in
        let newstore2 = assign_args args argvars newstore1 in
        let (rs,newps2,newstore3)= eval_stmt (List(f.body)) newps env2 newstore2 in
        eval_expr f.rv newps2 env2 newstore3
      )
  | x ->
    let locValue, newStore = expr_loc x ps env store in
    ((value_at newStore locValue), newStore)

(* eval_expr and eval_cond return a store because in full
C-flat they do have side effects (pre- and post-increment,
function calls) *)  
and eval_cond (cond:cond) (ps:proc_state) (env:environment) (store:store) : (bool*store) = match cond with
	| Equal (e1, e2) ->
		let (r1,sto) = eval_expr e1 ps env store in
		let (r2,s2) = eval_expr e2 ps env sto in
		(r1 == r2, s2)
	| Less (e1, e2) ->
	    let (r1,sto) = eval_expr e1 ps env store in
	    let (r2,s2) = eval_expr e2 ps env sto in
	    (r1 < r2, s2)
	| And(cond1, cond2) ->
		let (r1,sto) = eval_cond cond1 ps env store in
    if not r1 then 
      (false, sto) 
    else
		  let (r2,s2) = eval_cond cond2 ps env sto in
		    if(r2)then
			   (true , s2)
		    else
			   (false, s2)
	| Or (cond1, cond2) ->
		let (r1,sto) = eval_cond cond1 ps env store in
      if(r1)then 
        (true, sto) 
      else
		    let (r2,s2) = eval_cond cond2 ps env sto in
		      if(r2)then 
			     (true, s2)
		      else
			     (false, s2)
	| Not(cond1) ->
		let (r1,sto) = eval_cond cond1 ps env store in
	    (not(r1), sto)
	| True ->
		(true, store)
	| False ->
		(false, store)

and eval_list (statements:stmt list) (ps:proc_state) (env:environment) (store:store) : (stmtEvalRes*proc_state*store) = match statements with
	| [] -> 
		(Next,ps,store) 
	| stmt1::stmts ->
		let (resp, new_ps, new_store) = eval_stmt stmt1 ps env store in
		eval_list stmts new_ps env new_store

and eval_for_helper (cond:cond) (incr:stmt) (body:stmt) (ps:proc_state) (env:environment) (store:store) : (proc_state*store) = 
    let r1, store2 = eval_cond cond ps env store in
    if r1 then
      let res2, ps2, store3 = eval_stmt body ps env store2 in
      if res2 != BreakOut then
        let res3, ps3, store4 = eval_stmt incr ps2 env store3 in
        eval_for_helper cond incr body ps3 env store4
      else
        (ps2, store3)
    else
      (ps, store2)
and eval_stmt (stmt:stmt) (ps:proc_state) (env:environment) (store:store) : (stmtEvalRes*proc_state*store) = match stmt with
	| PrintInt e ->
	    let (r,sto) = eval_expr e ps env store in
	    print_int r; (Next, ps, sto) 
	| PrintStr s ->
	    print_string (Str.global_replace (Str.regexp "\\\\n") "\n" s); 
	    (* Escaping characters here because it's not done in the parser *)
	    (Next, ps, store)
	| List(stmt1::stmts)  -> 
		let (a,b,c) = eval_stmt stmt1 ps env store in
    if a == Next then 
		  eval_stmt (List stmts) b env c
    else
      (a, b, c)
	| VarAss(v, e) ->  
	   	(
				let (i,newStore1) = eval_expr e ps env store in
        let locValue, newStore2 = expr_loc v ps env newStore1 in
		    let newStore3 = insert_value newStore2 locValue i in
					(Next, ps, newStore3)
		)
	| IfThen(cond,stmt)->
		(
			let (r1,sto) = eval_cond cond ps env store in
		    if r1 then
				eval_stmt stmt ps env sto
			else (Next,ps,sto)
		)
	|IfThenElse(cond,stmt1,stmt2)->
		(
			let (r1,sto) = eval_cond cond ps env store in
		    if r1 then
				eval_stmt stmt1 ps env sto
			else
				eval_stmt stmt2 ps env sto
		)
	|Empty ->
		(Next, ps, store)
	|List[] ->
		(Next,ps,store) 
	|While(cond,stmt) ->
		let (r1,sto) = eval_cond cond ps env store in
		if r1 then 
			let (stmtRes,newPs,newStore) = eval_stmt stmt ps env sto in
		   	if stmtRes != BreakOut then eval_stmt (While (cond,stmt)) newPs env newStore
        else (Next, ps, sto)
		else
			(Next, ps , sto)
	|For(stmt1,cond,stmt2,stmt3) ->
		let (res1,ps1,store1) = eval_stmt stmt1 ps env store in
    let ps2, store2 = eval_for_helper cond stmt2 stmt3 ps1 env store1 in
    (Next, ps2, store2)
	|Switch(expr, cases, default_statements) ->
		let (target_num, sto) = (eval_expr expr ps env store) in
		let matches_num = fun (num, _) -> num == target_num in
		let matching = List.filter matches_num cases in
		(
			match matching with 
			| (_, statements)::remaining ->
				eval_list statements ps env sto 
			| [] ->
				eval_list default_statements ps env sto
		)
  |Break ->
    (BreakOut, ps, store)
  |Continue ->
    (ContinueOn, ps, store)
	|Expr(e) ->
  let (resultValue,newStore) = eval_expr e ps env store in 
  (Next,ps,newStore)
;;