(* Q0  : Get familiar with the external syntax of MiniML *)
let parse_tests : (string * (string, exp) either) list = [
    (* Provide your tests for the parser *)
  ("1;", Right (Int 1));
  ("let x = 3;", Left "Expected IN token");
  ("true;", Right (Bool true));
  ("1;", Right (Int 1));
  ("let fun apply (f : int -> int) : int -> int =
     fn x : int => f(x)
   in
   apply (fn x => x * 3) 100
end;", Right
     (Let
        ([Val
            (Rec ("apply", TArrow (TArrow (TInt, TInt), TArrow (TInt, TInt)),
                  Fn
                    ("f", Some (TArrow (TInt, TInt)),
                     Fn ("x", Some TInt, Apply (Var "f", Var "x")))),
             "apply")],
         Apply
           (Apply (Var "apply", Fn ("x", None, Primop (Times, [Var "x"; Int 3]))),
            Int 100)))); 
]


let free_vars_tests : (exp * name list) list = [
  (Int 10, []); 
  (((Let
       ([Val
           (Rec ("fact", TArrow (TInt, TInt),
                 Fn
                   ("x", Some TInt,
                    If (Primop (Equals, [Var "x"; Int 0]), Int 1,
                        Primop (Times,
                                [Var "x"; Apply (Var "fact", Primop (Minus, [Var "x"; Int 1]))])))),
            "fact")],
        Apply (Var "fact", Int 5)))), ["x"])
]

(* Q1  : Find the free variables in an expression *)
let rec free_vars (e : exp) : name list =
  match e with
  | Var y -> [y]
  | Int _ | Bool _ | Tuple [] -> [] 
  | If(e, e1, e2) ->
      union (free_vars e) (union (free_vars e1) (free_vars e2))
  | Primop (po, args) ->
      List.fold_right (fun e1 -> union (free_vars e1)) args [] 
  | Tuple (e1::etl) -> 
      union (free_vars e1) (free_vars (Tuple etl))
  | Fn (nm, _, e) -> delete [nm] (free_vars e)
  | Rec (nm, _, e) -> delete [nm] (free_vars e) 
  | Apply (e1, e2) -> union (free_vars e1) (free_vars e2) 
  | Anno (e, _) -> free_vars e
  | Let (decl, e2) -> 
      match decl with
      | [] -> (free_vars e2)
      | (Val (e1, nm))::dectl | (ByName (e1, nm))::dectl -> 
          union (free_vars e1) (delete [nm] (free_vars (Let(dectl, e2))))
      | (Valtuple (e1, nml))::dectl -> 
          union (free_vars e1) (delete nml (free_vars (Let(dectl, e2))))

let unused_vars_tests : (exp * name list) list = [
]

(* Q2  : Check variables are in use *)
let rec unused_vars (e : exp) : name list = 
  match e with
  | Var _ | Int _ | Bool _ | Tuple [] -> [] 
  | If(e, e1, e2) ->
      union (unused_vars e) (union (unused_vars e1) (unused_vars e2))
  | Primop (po, args) ->
      List.fold_right (fun e1 -> union (unused_vars e1)) args [] 
  | Tuple (e1::etl) -> 
      union (unused_vars e1) (unused_vars (Tuple etl))
  | Fn (nm, _, e) -> union (unused_vars e) (if member nm (free_vars e) then [] else [nm])
  | Rec (nm, _, e) -> unused_vars e
  | Apply (e1, e2) -> union (unused_vars e1) (unused_vars e2) 
  | Anno (e, _) -> unused_vars e
  | Let (decl, e2) -> 
      match decl with
      | [] -> unused_vars e2
      | (Val (e1, nm))::dectl | (ByName (e1, nm))::dectl -> 
          union (unused_vars e1) (union (unused_vars (Let(dectl, e2))) (if member nm (free_vars (Let(dectl, e2))) then [] else [nm]))
      | (Valtuple (e1, nml))::dectl -> 
          let rec notMemberList nmList list = match nmList with (* takes free_vars (Let(dectl, e2)) as input *)
            | [] -> [] 
            | (n1::ns) -> 
                (if (member n1 list) then [] else [n1])@(notMemberList ns list)
          in
          union (unused_vars e1) (union (unused_vars (Let(dectl, e2))) (notMemberList nml (free_vars (Let(dectl, e2)))))

let subst_tests : (((exp * name) * exp) * exp) list = [
]

(* Q3  : Substitute a variable *)
let rec subst ((e', x) : exp * name) (e : exp) : exp =
  match e with
  | Var y ->
      if x = y then
        e'
      else
        Var y

  | Int _ | Bool _ -> e
  | Primop (po, es) -> Primop (po, List.map (subst (e', x)) es)
  | If (e1, e2, e3) -> If (subst (e', x) e1, subst (e', x) e2, subst (e', x) e3)
  | Tuple es -> Tuple (List.map (subst (e', x)) es)
  | Anno (e, t) -> Anno (subst (e', x) e, t) 
  | Let (ds, e2) -> 
      (match ds with 
       | [] -> Let (ds, (subst (e', x) e2))
       | (Val (e1, nm))::tl ->
           if x <> nm && not (member nm (free_vars e')) then 
             let s1 = Val ((subst (e', x) e1), nm) in 
             let Let (stl, e2') = subst (e', x) (Let (tl, e2)) in 
             Let ((s1::stl), e2') 
           else (* i.e. member nm (free_vars e') is true or x = nm *)
             let newNm = (fresh_var nm) in 
             let s1 = Val ((subst ((Var newNm), nm) e1), newNm) in 
             subst (e', x) (Let ((s1::tl, (subst ((Var newNm), nm) e2))))
       | (ByName (e1, nm))::tl ->
           if x <> nm && not (member nm (free_vars e')) then 
             let s1 = ByName ((subst (e', x) e1), nm) in 
             let Let (stl, e2') = subst (e', x) (Let (tl, e2)) in 
             Let ((s1::stl), e2') 
           else (* i.e. member nm (free_vars e') is true or x = nm *)
             let newNm = (fresh_var nm) in 
             let s1 = ByName ((subst ((Var newNm), nm) e1), newNm) in 
             subst (e', x) (Let ((s1::tl, (subst ((Var newNm), nm) e2))))
               
       | (Valtuple (e1, nml))::tl ->
           (* function that returns a list of names that are in 'list' *)
           let rec memberList nmList list = match nmList with 
             | [] -> []
             | (n1::ns) -> 
                 (if (member n1 list) then [n1] else [])@(memberList ns list)
           in
           (* List of names to be renamed *)
           let listTBR = (memberList nml (free_vars e')) in
           
           (* nice case where no renaming needed *)
           if not (member x nml) && listTBR = [] then
             let s1 = Valtuple ((subst (e', x) e1), nml) in
             let Let (stl, e2') = subst (e', x) (Let (tl, e2)) in
             (Let ((s1::stl), e2')) 
             
           else (* i.e. listTBR != [] OR x is a member of nml *) 
             (* function that returns a Let with modified names from listTBR, 
             and with a new e1 substitued from names in listTBR *)
             let rec helperRename nml firstNames newE2 =
               (* firstNames is the accumulator for name-list *)
               (* We build a new name-list throughout the iterations using  
                   firstNames, while updating e2 *)
               match nml with 
               | [] -> (Let (((Valtuple (e1, firstNames))::tl), newE2))
               | (n1::ns) when ((x = n1) || (member n1 listTBR)) -> 
                   let newNM = (fresh_var n1) in
                   (* idk why I'm using a tuple here, it has nothing to do with that lol*)
                   let (e2', newNML) = ((subst ((Var newNM), n1) newE2), (firstNames@[newNM]))
                   in 
                   helperRename ns newNML e2' 
               | (n1::ns) -> helperRename ns (firstNames@[n1]) newE2
             in 
             let newLET = helperRename nml [] e2 in
             (* subst (e', x) *)newLET
      )
      
      (* let s1 = Val (subst (e', x) e1 ) in
                s1::(Let(tstl,tlSub)) *) 
             (* Let (ds, (subst (e', x) e)) 
  
*) 

  | Apply (e1, e2) -> Apply ((subst (e', x) e1), (subst (e', x) e2))
  | Fn (y, t, e) -> 
      if x <> y && not (member y (free_vars e')) then Fn (y, t, (subst (e', x) e)) 
      else (* i.e. member y (free_vars e') is true or x = y*)
        let newY = (fresh_var y) in subst (e', x) (Fn (newY, t, (subst ((Var newY), y) e))) 
  | Rec (y, t, e) -> 
      if x <> y && not (member y (free_vars e')) then Rec (y, t, (subst (e', x) e)) 
      else (* i.e. member y (free_vars e') is true or x = y*)
        let newY = (fresh_var y) in subst (e', x) (Rec (newY, t, (subst ((Var newY), y) e))) 

                       
(*Fn (y, t, (subst ((fresh_var y), y)e)) *)

                                (* if x = y then let newY = (fresh_var y) in subst (e', x) (Fn (newY, t, (subst ((Var newY), y) e)))  *)




let x13 = Let ([(Val((Int 5), ("x"))); (Val((Int 11), ("y")))], Primop(Plus, [Var "x"; Var "y"]));;

let x14 = Let ([(Val((Int 5), ("x"))); (Val((Int 11), ("y")))], Primop(Plus, [Var "x"; Var "w"]));;

let x15 = Let ([(Val((Var "w"), ("x"))); (Val((Int 11), ("y")))], Primop(Plus, [Var "x"; Var "y"]));;

let x16 = Primop(Plus, [Var "x"; Var "w"]);;
    
let x17 = Primop(Plus, [Var "a"; Primop(Plus, [Var "b"; Primop(Plus, [Var "c"; Var "d"])])]);;
    
let x18 = Let ([(Valtuple(Tuple[Var "z"; Var "w"; Int 4], ["a"; "b"; "c"])); (Val((Int 11), ("d")))], x17);;

let x19 = Let ([(Valtuple(Tuple[Var "z"; Var "w"; Int 4], ["a"; "b"; "c"]))], Primop(Plus, [Var "a"; Primop(Plus, [Var "b"; Var "c"])]));;

let x20 = Let ([(Valtuple(Tuple[Var "z"; Var "w"; Int 4], ["a"; "b"; "c"]))], Primop(Plus, [Var "a"; Primop(Plus, [Var "b"; Var "d"])]));;

let x21 = Primop(Or, [Bool false; Var "w"]);;

let Right x3 = P.parse valid_program_3

let x22 = Rec ("fact", TArrow (TInt, TInt), Fn ("x", Some TInt, If (Primop (Equals, [Var "x"; Int 0]), Int 1, Primop (Times, [Var "x"; Apply (Var "fact", Primop (Minus, [Var "x"; Int 1]))]))))

let x23 = Let ([(Val((Int 5), ("x"))); (Val((Var "x"), ("y")))], Primop(Plus, [Var "y"; Var "y"]));;





let eval_tests : (exp * exp) list = [
]

(* Q4  : Evaluate an expression in big-step *)
let rec eval : exp -> exp =
  (* do not change the code from here *)
  let bigstep_depth = ref 0 in
  fun e ->
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "eval (" ^ Print.exp_to_string e ^ ")\n");
    incr bigstep_depth;
  (* to here *)
    let result =
      match e with
      | Int _ | Bool _ -> e
      | Tuple es -> Tuple (List.map eval es)
      | If (e1, e2, e3) ->
          begin match eval e1 with
            | Bool b ->
                if b then
                  eval e2
                else
                  eval e3
            | _ -> stuck "Condition for if expression should be of the type bool"
          end
      | Anno (e, _) -> eval e     (* types are ignored in evaluation *)
      | Var x -> stuck ("Free variable \"" ^ x ^ "\" during evaluation")

      | Fn (x, t, e) -> Fn (x, t, e)
                          
      | Apply (e1, e2) -> 
          begin match eval e1 with
            | Fn (x, t, e) -> let v2 = eval e2 in eval (subst (v2, x) e)
            | _ -> stuck ("Left argument for apply operation should be a function")
          end 
          
      | Rec (f, t, e) -> eval (subst ((Rec (f, t, e)), f) e) 
                           
                           
      | Primop (And, es) ->
          let vs = List.map eval es in
          begin match vs with
            | [Bool true; v2] -> v2
            | [Bool false; _] -> Bool false
            | _ -> stuck "Left argument for AND operation should be of the type bool"
          end 
      | Primop (Or, es) ->
          let vs = List.map eval es in
          begin match vs with
            | [Bool false; v2] -> v2
            | [Bool true; _] -> Bool true
            | _ -> stuck "Left arguments for OR operation should be of the type bool"
          end
      | Primop (op, es) ->
          let vs = List.map eval es in
          begin match eval_op op vs with
            | None -> stuck "Bad arguments to primitive operation"
            | Some v -> v
          end

      | Let (ds, e) -> 
          begin match ds with
            | [] -> eval e
            | (Val (e1, nm))::tl -> 
                let v1 = eval e1 in
                eval (subst (v1, nm) (Let (tl, e)))
            | (ByName (e1, nm))::tl -> 
                eval (subst (e1, nm) (Let (tl, e)))
            | (Valtuple (e1, nml))::tl -> 
                let Tuple valList = eval e1 in
                if (List.length valList <> List.length nml) then
                  stuck ("Tuple of wrong length in Let expression")
                else 
                  let rec helperSubst valList nml tl e =
                    begin match (valList, nml) with
                      | ([], []) -> Let (tl, e)
                      | ((v1::vs), (n1::ns)) -> 
                          let Let (tl', e') = subst (v1, n1) (Let (tl, e)) in 
                          helperSubst vs ns tl' e'
                    end
                  in
                  eval (helperSubst valList nml tl e)
          end
    in
  (* do not change the code from here *)
    decr bigstep_depth;
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "result of eval (" ^ Print.exp_to_string e ^ ") = "
         ^ Print.exp_to_string result ^ "\n");
  (* to here *)
    result


let infer_tests : ((context * exp) * typ) list = [
]

(* Q5  : Type an expression *)
(* Q7* : Implement the argument type inference
         For this question, move this function below the "unify". *)
let rec infer (ctx : context) (e : exp) : typ = match e with
  | Int _ -> TInt
  | Bool _ -> TBool 
  | Var x -> ctx_lookup ctx x 
    
  | If (e1, e2, e3) -> begin match infer ctx e1 with 
      | TBool -> 
          let t1 = infer ctx e2 in
          let t2 = infer ctx e3 in
          if t1 = t2 then t1
          else type_fail ("Arguments for If expression should be of same type")
      | _ -> type_fail ("Condition should be a boolean in If expression")
    end
    
  | Fn (x, t, e) -> begin match t with
      | Some ty -> let t' = (infer (extend ctx (x, ty)) e) in
          TArrow (ty, t')
      | None -> let alpha = fresh_tvar () in
          let t' = (infer (extend ctx (x, alpha)) e) in
          (* ??? ceci est une supposition -> check if x has some type in the ctx, and else catch the notFound error*)
          TArrow (alpha, t')
    end
    
  | Rec (f, t, e) -> 
      let t' = (infer (extend ctx (f, t)) e) in
      if t' = t then t else type_fail ("Wrong recursion type")
          (* TArrow (t, t') *)
        
  | Tuple es -> TProduct (List.map (infer ctx) es)
                  
  | Apply (e1, e2) -> 
      let t1 = infer ctx e1 in
      let t2 = infer ctx e2 in
      begin match t1 with
        (* NEED TO UNIFY ??? t11 WITH t2*)
      (* Check last video at 20:44 and after *)
        
          (* | TArrow (t11, TVar tyopref) -> 
            let _ = unify t11 t2 in
            TVar tyopref
        *)
        | TArrow (t11, t12) -> 
            if t11 = t2 then t12
            else type_fail ("Input type does not match Function type")
        | _ -> type_fail ("Function required for application")
      end

  | Anno (e, t) -> 
      let t1 = infer ctx e in
      if t1 = t then t
      else type_fail ("Type does not match required type") 
          
  | Primop (op, es) -> 
      begin match es with 
        | [e1; e2] -> 
            let t1 = infer ctx e1 in
            let t2 = infer ctx e2 in
            begin match op with
              | Plus | Minus | Times | Div -> 
                  if (t1 = TInt) && (t2 = TInt) then TInt
                  else type_fail ("Operator requires two integers")
              | Equals | NotEquals | LessThan | LessEqual | GreaterThan |  GreaterEqual ->
                  if (t1 = TInt) && (t2 = TInt) then TBool
                  else type_fail ("Operator requires two integers")
              | And | Or ->
                  if (t1 = TBool) && (t2 = TBool) then TBool
                  else type_fail ("Operator requires two integers")
              | _ -> type_fail ("Wrong operator for two arguments")
            end
        | [e1] ->
            let t1 = infer ctx e1 in 
            begin match op with
              | Negate -> 
                  if t1 = TInt then TInt
                  else type_fail ("Operator requires an integers")
              | _ -> type_fail ("Wrong operator for one arguments")
            end
        | _ -> type_fail ("Operators require at most 2 arguments")
      end 
      
  | Let (dec, e2) -> 
      let rec helperCtx dec ctx = match dec with 
        | [] -> ctx
        | (Val (e1, nm))::tl | (ByName (e1, nm))::tl -> 
            let t1 = infer ctx e1 in
            let newCtx = extend ctx (nm, t1) in
            helperCtx tl newCtx 
        | (Valtuple (e1, nml))::tl ->
            let TProduct tList = infer ctx e1 in
            let newCtx = extend_list ctx (List.combine nml tList) in
            helperCtx tl newCtx 
      in
      infer (helperCtx dec ctx) e2
    
let unify_tests : ((typ * typ) * unit) list = [
]

(* find the next function for Q5 *)
(* Q6  : Unify two types *)
let rec unify (ty1 : typ) (ty2 : typ) : unit = 
  let rec freeVarsType ty = 
    match ty with
    | TInt | TBool -> []
    | TArrow (t1, t2) -> (freeVarsType t1)@(freeVarsType t2)
    | TProduct tyl -> union_list (List.map freeVarsType tyl)
    | TVar ({contents = None} as tyopref) -> [tyopref]
    | TVar {contents = Some t} -> freeVarsType t
  in
  match (ty1, ty2) with
  | (TInt, TInt) | (TBool, TBool) -> ()
                                     
  | (TArrow (t1, t2), TArrow (s1, s2)) -> 
      let _ = unify t1 s1 in unify t2 s2 
      (* unify t1 s1; unify t2 s2 *)
        
  | (TProduct tyl1, TProduct tyl2) -> 
      let _ = List.map2 unify tyl1 tyl2 in ()

  
(* case [alpha = beta] OR [Some t1 = Some t1] *) 
  | (TVar ({contents = ty1} as tyopref1), TVar ({contents = ty2} as tyopref2))  
    when ((*tyopref1 <> ref None && *)tyopref1 = tyopref2) -> tyopref1 := ty2
      (* tyopref1 := Some (TVar tyopref2) *)
        

          (*| (TVar ({contents = ty1}), TVar ({contents = ty2} as tyopref2)) -> 
            let (None, None) = (ty1, ty2) in tyopref2 := ty1*)

          (*| (TVar ({contents = (None as ty1)}), TVar ({contents = None} as tyopref2)) -> 
            tyopref2 := ty1 *)
        

 (* | (TVar tyopref1, TVar tyopref2)  when (!tyopref1 <> None) ->     *)                                                
  
  
  | (TVar ({contents = tyop1} as tyopref1), ty2)  (*when (ty2 <> TVar (ref None))*) ->
      (* occurs check *)
      let p = (List.memq (tyopref1) (freeVarsType ty2)) in 
      if not p then 
        (if (tyop1 = None) then tyopref1 := Some ty2
         else let Some ty1 = tyop1 in unify ty1 ty2)
      else type_fail ("No instantiation found for given types")
  | (ty1, TVar ({contents = tyop2} as tyopref2)) ->
      (* occurs check *)
      let p = (List.memq (tyopref2) (freeVarsType ty1)) in
      if not p then 
        (if (tyop2 = None) then tyopref2 := Some ty1
         else let Some ty2 = tyop2 in unify ty1 ty2)
      else type_fail ("No instantiation found for given types")
          
          
   (* | (ty1, TVar tyopref2)  when (ty1 <> (TVar ((Some _) ref))) ->
      tyopref2 := Some ty1 *)
          (*| (ty1, TVar tyopref2)  when (not (member (!tyopref2) []) && ty1 <> TVar (ref None)) ->
      tyopref2 := Some ty1 *)


(* case [alpha = beta] *)
  
  
          
 
  
(*
      | (TVar ({contents = (None as ty1)}), TVar ({contents = None} as r2)) -> 
         r2 := ty1 
     *)   
        

  | _ -> type_fail ("Unification failure") 
      

(* Now you can play with the language that you've implemented! *)
let execute (s: string) : unit =
  match P.parse s with
  | Left s -> print_endline ("parsing failed: " ^ s)
  | Right e ->
      try
       (* first we type check the program *)
        ignore (infer (Ctx []) e);
        let result = eval e in
        print_endline ("program is evaluated to: " ^ Print.exp_to_string result)
      with
      | NotImplemented -> print_endline "code is not fully implemented"
      | Stuck s -> print_endline ("evaluation got stuck: " ^ s)
      | NotFound -> print_endline "variable lookup failed"
      | TypeError s -> print_endline ("type error: " ^ s)
      | e -> print_endline ("unknown failure: " ^ Printexc.to_string e)


(************************************************************
 *             Do not change these functions.               *
 *               They are needed for tests.                 *
 ************************************************************)
let list_to_string el_to_string l : string =
  List.fold_left
    begin fun acc el ->
      if acc = "" then
        el_to_string el
      else
        acc ^ "; " ^ el_to_string el
    end
    ""
    l
  |> fun str -> "[" ^ str ^ "]"

let run_test name f ts stringify : unit =
  List.iteri
    begin fun idx (input, expected_output) ->
      try
        let output = f input in
        if output <> expected_output then
          begin
            print_string (name ^ " test #" ^ string_of_int idx ^ " failed\n");
            print_string (stringify output ^ " <> " ^ stringify expected_output)
          end
      with
      | exn ->
          print_string (name ^ " test #" ^ string_of_int idx ^ " raised an exception:\n");
          print_string (Printexc.to_string exn)
    end
    ts

let run_free_vars_tests () : unit =
  run_test "free_vars" free_vars free_vars_tests (list_to_string (fun x -> x))

let run_unused_vars_tests () : unit =
  run_test "unused_vars" unused_vars unused_vars_tests (list_to_string (fun x -> x))

let run_subst_tests () : unit =
  run_test "subst" (fun (s, e) -> subst s e) subst_tests Print.exp_to_string

let run_eval_tests () : unit =
  run_test "eval" eval eval_tests Print.exp_to_string

let run_infer_tests () : unit =
  run_test "infer" (fun (ctx, e) -> infer ctx e) infer_tests Print.typ_to_string

let run_unify_tests () : unit =
  run_test "unify" (fun (ty1, ty2) -> unify ty1 ty2) unify_tests (fun () -> "()")

let run_all_tests () : unit =
  run_free_vars_tests ();
  run_unused_vars_tests ();
  run_subst_tests ();
  run_eval_tests ();
  run_infer_tests ();
  run_unify_tests ()
