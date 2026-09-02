(**************************************************************************)
(*                                                                        *)
(*  SPDX-License-Identifier LGPL-2.1                                      *)
(*  Copyright (C)                                                         *)
(*  CEA (Commissariat à l'énergie atomique et aux énergies alternatives)  *)
(*                                                                        *)
(**************************************************************************)

open Cil_types

let check_result_from_formals kf loc af =
  let formals = Globals.Functions.get_params kf in
  match af with
  | {it_content = {term_node = TLval(TResult(_),_)}}, From(l) ->
    List.iter (
      fun x ->
        match x with
        | {it_content =
             {term_node = TLval(TMem({term_node = TLval(TVar(lv),TNoOffset)}),TNoOffset)} }
        | {it_content =
             {term_node = TLval(TMem({term_node =
                                        TBinOp(PlusPI,{term_node = TLval(TVar(lv),TNoOffset)},
                                               {term_node = Trange(_,_)})}),TNoOffset)}}
        | {it_content = {term_node = TLval(TVar(lv),_)}} ->
          begin
            let is_formal =
              List.exists (fun v ->
                  match v.vlogic_var_assoc with
                  | Some x -> Cil_datatype.Logic_var.equal lv x
                  | _ -> Rpp_options.Self.abort ~source:loc
                           "Variable %a have no vlogic_var_assocf in assert clause of function %s."
                           Printer.pp_varinfo v (Kernel_function.get_name kf)
                ) formals
            in
            match is_formal with
            | true -> ()
            | false ->
              Rpp_options.Self.abort ~source:loc
                "Variable %a is not a paramter of function %s ."
                Printer.pp_logic_var lv (Kernel_function.get_name kf)
          end
        | _ -> Rpp_options.Self.abort ~source:loc
                 "Unsupported term in assigns of function %s e."
                 (Kernel_function.get_name kf)
    ) l
  | _ -> Rpp_options.Self.abort ~source:loc
           "The \\callpure for function %s require that %s is pure i.e. assigns result from formals"
           (Kernel_function.get_name kf)(Kernel_function.get_name kf)

(**
       Function checking if the give function is a pure function by analyzing the assert clauses
*)
let check_is_pure_function kf loc =
  let rec aux data =
    match data  with
    | x :: y  ->
      (match x.b_assigns with
       | Writes([])-> Rpp_options.Self.abort ~source:loc
           "The \\callpure for function %s require that %s is pure i.e. assigns result from formals"
           (Kernel_function.get_name kf)(Kernel_function.get_name kf)
       | Writes(l) -> List.iter (check_result_from_formals kf loc) l; aux y
       | WritesAny -> Rpp_options.Self.abort ~source:loc
              "The plugin RPP require assigns annotation for function %s"
                         (Kernel_function.get_name kf)(Kernel_function.get_name kf))
    | [] -> ()
  in
  aux @@ Annotations.behaviors kf

class virtual ['env, 'call_data, 'callset, 'relprop] rpp_visitor = object (self)

  method virtual build_Toffset:
    'env -> Cil_types.term_offset -> Cil_types.term_offset
  method virtual build_Toffset_at : 'env ->
    Cil_types.term_offset -> string -> Cil_types.term_offset
  method virtual build_call :
    'env -> string -> int -> Cil_types.varinfo -> Cil_types.term list ->
    'call_data
  method virtual build_call_Toffset :
    'env -> Cil_types.term_offset -> Cil_types.term_offset
  method virtual build_call_app : 'env ->
    int ->
    Cil_types.varinfo ->
    Cil_types.term list -> Cil_types.logic_type -> Cil_types.term
  method virtual build_call_binop : 'env ->
    Cil_types.binop ->
    Cil_types.term -> Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method virtual build_call_const : 'env ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> Cil_types.term
  method virtual build_call_logic_coerce : 'env ->
    Cil_types.logic_type ->
    Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method virtual build_call_unop : 'env ->
    Cil_types.unop -> Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method virtual build_call_valme :
    'env -> Cil_types.term ->
    Cil_types.term_offset -> Cil_types.logic_type -> Cil_types.term
  method virtual build_call_valvar : 'env ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> Cil_types.logic_type -> Cil_types.term
  method virtual build_callset : 'env -> 'call_data list -> 'callset
  method virtual build_predicate_and :
    'env -> Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_app :
    'env -> Cil_types.logic_info ->
    Cil_types.logic_label list -> Cil_types.term list -> Cil_types.predicate
  method virtual build_predicate_exists :
    'env -> Cil_types.quantifiers -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_false : 'env -> Cil_types.predicate
  method virtual build_predicate_forall :
    'env -> Cil_types.quantifiers -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_iff :
    'env -> Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_implies :
    'env -> Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_label :
    'env -> Cil_types.logic_label list -> Cil_types.logic_label list
  method virtual build_predicate_not :
    'env -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_or :
    'env -> Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_quan :
    'env -> Cil_types.quantifiers -> Cil_types.quantifiers
  method virtual build_predicate_rel :
    'env ->
    Cil_types.relation ->
    Cil_types.term -> Cil_types.term -> Cil_types.predicate
  method virtual build_predicate_true : 'env -> Cil_types.predicate
  method virtual build_predicate_xor :
    'env -> Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_rpp_predicate_forall :
    'env -> Cil_types.quantifiers -> Cil_types.predicate -> 'relprop
  method virtual build_rpp_predicate_forall_callset :
    'env -> Cil_types.quantifiers -> 'callset -> Cil_types.predicate -> 'relprop
  method virtual build_rpp_predicate_implies :
    'env -> Cil_types.predicate -> 'relprop
  method virtual build_rpp_predicate_implies_callset :
    'env -> 'callset -> Cil_types.predicate -> 'relprop
  method virtual build_rpp_predicate_rel :
    'env -> Cil_types.relation -> Cil_types.term -> Cil_types.term -> 'relprop
  method virtual build_rpp_quan :
    'env -> Cil_types.quantifiers -> Cil_types.quantifiers
  method virtual build_term_app : 'env ->
    Cil_types.logic_info ->
    Cil_types.term list -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_app_call : 'env ->
    int ->
    Cil_types.varinfo ->
    Cil_types.term list -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_app_result :
    'env -> string -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_at_mem :
    'env -> Cil_types.term -> string -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_at_var : 'env ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> string -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_binop : 'env ->
    Cil_types.binop ->
    Cil_types.term -> Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_binop_at : 'env ->
    Cil_types.binop ->
    Cil_types.term ->
    Cil_types.term -> Cil_types.logic_type -> string -> Cil_types.term
  method virtual build_term_const : 'env ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> Cil_types.term
  method virtual build_term_const_at : 'env ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> string -> Cil_types.term
  method virtual build_term_logic_coerce : 'env ->
    Cil_types.logic_type ->
    Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_logic_coerce_at : 'env ->
    Cil_types.logic_type ->
    Cil_types.term -> Cil_types.logic_type -> string -> Cil_types.term
  method virtual build_term_range : 'env ->
    Cil_types.term option -> Cil_types.term option ->
    Cil_types.logic_type -> Cil_types.term
  method virtual build_term_unop : 'env ->
    Cil_types.unop -> Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_valvar : 'env ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_valvar_at : 'env ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> Cil_types.logic_type -> string -> Cil_types.term

  method visit_call_app env inline funct formals ty =
    let new_terms = List.map (fun x -> self#visit_call env x) formals in
    self#build_call_app env inline funct new_terms ty

  method visit_call_valvar env logic_var off ty =
    let new_off = self#build_call_Toffset env off in
    self#build_call_valvar env logic_var new_off ty

  method visit_call_const env l_c ty =
    self#build_call_const env l_c ty

  method visit_call_binop env binop t1 t2 ty =
    let new_t1 = self#visit_call env t1 in
    let new_t2 = self#visit_call env t2 in
    self#build_call_binop env binop new_t1 new_t2 ty

  method visit_call_logic_coerce env ty t typ =
    let new_t = self#visit_call env t in
    self#build_call_logic_coerce env ty new_t typ

  method visit_call_unop env op t ty =
    let new_t = self#visit_call env t in
    self#build_call_unop env op new_t ty

  method visit_call_valme env t off ty  =
    let new_off = self#build_call_Toffset env off in
    let new_t = self#visit_call env t in
    self#build_call_valme env new_t new_off ty

  method visit_call env term =
    let (loc,_) = term.term_loc in
    match term.term_node with
    | Tapp({l_var_info={lv_name ="\\callpure"}},[],terms) ->
      let (inline,funct,formals) =
        (match terms with
         | {term_node = TConst (Integer(i,_))} :: q -> (match q with
             | {term_node=TLval(TVar({lv_origin=Some(x)}),TNoOffset)} :: p ->
               if Ast_types.is_fun x.vtype then
                 Z.to_int i,x,p
               else
                 Rpp_options.Self.fatal ~source:loc
                   "Something went wrong during parsing: Expected \
                    a function as first or second parameter"
             | _ ->
               Rpp_options.Self.fatal ~source:loc
                 "Something went wrong during parsing: Expected \
                  a logical variable as second parameter")
         | _ ->
           Rpp_options.Self.fatal ~source:loc
             "Something went wrong during parsing: Expected \
              an integer as first parameter")
      in
      check_is_pure_function (Globals.Functions.get funct) loc;
      self#visit_call_app env inline funct formals (term.term_type)
    | Tapp({l_var_info={lv_name ="\\callpure"}},_::_,_) ->
      Rpp_options.Self.abort ~source:loc "Something went wrong during parsing: \
                                          Expect no label for built-in \\callpure:@. @[%a@] @."
        Printer.pp_term term
    | TLval((TVar(logic_var),off)) ->
      self#visit_call_valvar env logic_var off (term.term_type)
    | TConst ((Integer(_,_)) as l_c) | TConst((LReal(_)) as l_c) ->
      self#visit_call_const env l_c (term.term_type)
    | TConst(_) -> Rpp_options.Self.abort ~source:loc
                     "Unsupported logical constant in callpure:@. @[%a@] @."
                     Printer.pp_term term
    | TBinOp((PlusA|PlusPI|MinusA|Mult|Div|Mod|Lt|Gt|Le|Ge|Eq|Ne|BAnd|BXor|BOr as binop),
             t1,t2) ->
      self#visit_call_binop env binop t1 t2 (term.term_type)
    | TBinOp(_,_,_)-> Rpp_options.Self.abort ~source:loc
                        "Unsupported binary operation:@. @[%a@] @."
                        Printer.pp_term term
    | TCast(_, ((Ctype _ | Linteger | Lreal) as ty), t) ->
      self#visit_call_logic_coerce env ty t term.term_type
    | TCast(_,ty,t) ->
      Rpp_options.Self.abort ~source:loc
        "Unsupported logical conversion from %a to %a:@\n%a"
        Printer.pp_logic_type t.term_type
        Printer.pp_logic_type ty
        Printer.pp_term term
    | TUnOp(Neg as op,t) ->
      self#visit_call_unop env op t (term.term_type)
    | TUnOp(_,_) -> Rpp_options.Self.abort ~source:loc
                      "Unsupported unary operator in callpure:@. @[%a@] @."
                      Printer.pp_term term
    | TLval(TMem(t),off) ->
      self#visit_call_valme env t off (term.term_type)
    | _ ->   Rpp_options.Self.fatal ~source:loc
               "Something went wrong during parsing: Unsupported \
                term in parameter of \\callpure:@\n%a"
               Printer.pp_term term

  method visit_term_binop_at env oper t1 t2 ty s =
    let new_t1 = self#visit_term_at env t1 s in
    let new_t2 = self#visit_term_at env t2 s in
    self#build_term_binop_at env oper new_t1 new_t2 ty s

  method visit_term_logic_coerce_at env ty term typ s =
    let new_term = self#visit_term_at env term s in
    self#build_term_logic_coerce_at env ty new_term typ s

  method visit_term_const_at env l_g ty s =
    self#build_term_const_at env l_g ty s

  method visit_term_valvar_at env l_v t_o ty s =
    let new_offset = self#build_Toffset_at env t_o s in
    self#build_term_valvar_at env l_v new_offset ty s

  method visit_term_at env term label =
    let (loc,_) = term.term_loc in
    match term.term_node with
    | TBinOp((PlusA|PlusPI|MinusA|Mult|Div|Mod|Lt|Gt|Le|Ge|Eq|Ne|BAnd|BXor|BOr as operator),
             term1,term2) ->
      self#visit_term_binop_at env operator term1 term2 (term.term_type) label
    | TBinOp(_,_,_)-> Rpp_options.Self.abort ~source:loc
                        "Unsupported binary operation:@. @[%a@] @."
                        Printer.pp_term term
    | TLval (TVar(logic_var),t_o) ->
      self#visit_term_valvar_at env logic_var t_o (term.term_type) label
    | TConst ((Integer(_,_)) as l_g) | TConst((LReal(_)) as l_g) ->
      self#visit_term_const_at env l_g (term.term_type) label
    | TConst(_) -> Rpp_options.Self.abort ~source:loc "Unsupported logical constant:@. @[%a@] @."
                     Printer.pp_term term
    | TCast(_, ((Ctype _ | Linteger | Lreal) as ty), t) ->
      self#visit_term_logic_coerce_at env ty t term.term_type label
    | TCast(_,ty,t) ->
      Rpp_options.Self.abort ~source:loc
        "Unsupported logical conversion from %a to %a:@\n%a"
        Printer.pp_logic_type t.term_type
        Printer.pp_logic_type ty
        Printer.pp_term term
    | _ ->  Rpp_options.Self.abort ~source:loc " Not supported term in at term:@. @[%a@] @."
              Printer.pp_term term

  method visit_term_app_call env inline funct formals ty =
    let new_terms = List.map (fun x -> self#visit_call env x) formals in
    self#build_term_app_call env inline funct new_terms ty

  method visit_term_binop env oper t1 t2 ty =
    let new_t1 = self#visit_term env t1 in
    let new_t2 = self#visit_term env t2 in
    self#build_term_binop env oper new_t1 new_t2 ty

  method visit_term_logic_coerce env ty term typ =
    let new_term = self#visit_term env term in
    self#build_term_logic_coerce env ty new_term typ

  method visit_term_const env l_g ty =
    self#build_term_const env l_g ty

  method visit_term_valvar env l_v t_o ty =
    let new_offset = self#build_Toffset env t_o in
    self#build_term_valvar env l_v new_offset ty

  method visit_term_app_result env id ty =
    self#build_term_app_result env id ty

  method visit_term_at_val env l_v x s ty =
    let new_offset = self#build_Toffset env x in
    self#build_term_at_var env l_v new_offset s ty

  method visit_term_at_mem env t s ty =
    let new_term = self#visit_term_at env t s in
    self#build_term_at_mem env new_term s ty

  method visit_term_unop env unop t ty =
    let new_t = self#visit_term env t in
    self#build_term_unop env unop new_t ty

  method visit_term_range env t1 t2 ty =
    let new_t1 = match t1 with
      | None -> None
      | Some t -> Some (self#visit_term env t)
    in
    let new_t2 = match t2 with
      | None -> None
      | Some t -> Some (self#visit_term env t)
    in
    self#build_term_range env new_t1 new_t2 ty

  method visit_term_app env logicinfo t_list ty =
    let new_terms = List.map (fun x -> self#visit_term env x) t_list in
    self#build_term_app env logicinfo new_terms ty

  method visit_term env term =
    let (loc,_) = term.term_loc in
    match term.term_node with
    | Tapp({l_var_info={lv_name ="\\callpure"}},[],terms) ->
      let (inline,funct,formals) =
        (match terms with
         | {term_node = TConst (Integer(i,_))} :: q -> (match q with
             | {term_node=TLval(TVar({lv_origin=Some(x)}),TNoOffset)} :: p ->
               if Ast_types.is_fun x.vtype then
                 Z.to_int i,x,p
               else
                 Rpp_options.Self.fatal ~source:loc
                   "Something went wrong during parsing: Expected\
                    a function as seconde or first parameter"
             | _ ->
               Rpp_options.Self.fatal ~source:loc
                 "Something went wrong during parsing: Expected\
                  a logical variable as seconde parameter")
         | _ ->
           Rpp_options.Self.fatal ~source:loc
             "Something went wrong during parsing: Expected\
              an integer for first parameter")
      in
      check_is_pure_function (Globals.Functions.get funct) loc;
      self#visit_term_app_call env inline funct formals (term.term_type)
    | Tapp({l_var_info={lv_name ="\\callpure"}},_::_,_) ->
      let (loc,_) = term.term_loc in
      Rpp_options.Self.fatal ~source:loc "Something went wrong during parsing:\
                                          Expect no label for built-in \\callpure:@. @[%a@] @."
        Printer.pp_term term
    | TBinOp((PlusA|PlusPI|MinusA|Mult|Div|Mod|Lt|Gt|Le|Ge|Eq|Ne|BAnd|BXor|BOr as operator),
             term1,term2) ->
      self#visit_term_binop env operator term1 term2 (term.term_type)
    | TBinOp(_,_,_)-> Rpp_options.Self.abort ~source:loc
                        "Unsupported binary operation:@. @[%a@] @."
                        Printer.pp_term term
    | TCast(_, ((Ctype _ | Linteger | Lreal) as ty), t) ->
      self#visit_term_logic_coerce env ty t term.term_type
    | TCast(_,ty,t) ->
      Rpp_options.Self.abort ~source:loc
        "Unsupported logical conversion from %a to %a:@\n%a"
        Printer.pp_logic_type t.term_type
        Printer.pp_logic_type ty
        Printer.pp_term term
    | TConst ((Integer(_,_)) as l_g) | TConst((LReal(_)) as l_g) ->
      self#visit_term_const env l_g (term.term_type)
    | TConst(_) -> Rpp_options.Self.abort ~source:loc "Unsupported logical constant:@. @[%a@] @."
                     Printer.pp_term term
    | TLval (TVar(logic_var),t_o) ->
      self#visit_term_valvar env logic_var t_o (term.term_type)
    | Tapp({l_var_info={lv_name ="\\callresult"}},[],{term_node = TConst (LStr(id))} :: []) ->
      self#visit_term_app_result env id (term.term_type)
    | Tapp({l_var_info={lv_name ="\\callresult"}},_, _::_) ->
      Rpp_options.Self.fatal ~source:loc "Something went wrong during parsing:\
                                          Expect one existing indentifier for \
                                          built-in \\callresult:@. @[%a@] @."
        Printer.pp_term term

    | Tapp({l_var_info={lv_name ="\\callresult"}},_::_,_) ->
      Rpp_options.Self.fatal ~source:loc "Something went wrong during parsing:\
                                          Expect no label for built-in \\callresult:@. @[%a@] @."
              Printer.pp_term term

    | Tapp (logicinfo,_,t_list) ->
      self#visit_term_app env logicinfo t_list (term.term_type)
    | Tat({term_node = TLval(TVar(l_v),x)},FormalLabel(s)) ->
      self#visit_term_at_val env l_v x s (term.term_type)
    | Tat({term_node = TLval(TMem(t),TNoOffset)},FormalLabel(s)) ->
      self#visit_term_at_mem env t s (term.term_type)
    | TUnOp(Neg as op,t) ->
      self#visit_term_unop env op t (term.term_type)
    | TUnOp(_,_) -> Rpp_options.Self.abort ~source:loc
                      "Unsupported unary operator:@. @[%a@] @."
                      Printer.pp_term term
    | Trange(t1,t2) ->
      self#visit_term_range env t1 t2 (term.term_type)
    | _ ->  Rpp_options.Self.abort ~source:loc " Not supported term in predicate:@. @[%a@] @."
              Printer.pp_term term

  method visit_predicate_rel env rel t1 t2 =
    let new_t1 = self#visit_term env t1 in
    let new_t2 = self#visit_term env t2 in
    self#build_predicate_rel env rel new_t1 new_t2

  method visit_predicate_false env =
    self#build_predicate_false env

  method visit_predicate_true env =
    self#build_predicate_true env

  method visit_predicate_and env pred1 pred2  =
    let new_pred1 = self#visit_predicate env pred1 in
    let new_pred2 = self#visit_predicate env pred2 in
    self#build_predicate_and env new_pred1 new_pred2

  method visit_predicate_or env pred1 pred2 =
    let new_pred1 = self#visit_predicate env pred1 in
    let new_pred2 = self#visit_predicate env pred2 in
    self#build_predicate_or env new_pred1 new_pred2

  method visit_predicate_xor env pred1 pred2 =
    let new_pred1 = self#visit_predicate env pred1 in
    let new_pred2 = self#visit_predicate env pred2 in
    self#build_predicate_xor env new_pred1 new_pred2

  method visit_predicate_implies env pred1 pred2 =
    let new_pred1 = self#visit_predicate env pred1 in
    let new_pred2 = self#visit_predicate env pred2 in
    self#build_predicate_implies env new_pred1 new_pred2

  method visit_predicate_iff env pred1 pred2 =
    let new_pred1 = self#visit_predicate env pred1 in
    let new_pred2 = self#visit_predicate env pred2 in
    self#build_predicate_iff env new_pred1 new_pred2

  method visit_predicate_not env pred =
    let new_pred = self#visit_predicate env pred in
    self#build_predicate_not env new_pred

  method visit_predicate_app env logicinfo l t_list =
    let new_terms = List.map (fun x -> self#visit_term env x) t_list in
    let new_labels = self#build_predicate_label env l in
    self#build_predicate_app env logicinfo new_labels new_terms

  method visit_predicate_forall env quan pred =
    let new_quan = self#build_predicate_quan env quan in
    let new_pred = self#visit_predicate env pred in
    self#build_predicate_forall env new_quan new_pred

  method visit_predicate_exists env quan pred =
    let new_quan = self#build_predicate_quan env quan in
    let new_pred = self#visit_predicate env pred in
    self#build_predicate_exists env new_quan new_pred

  method visit_predicate env predicate =
    match predicate.pred_content with
    | Prel(rel,t1,t2) ->
      self#visit_predicate_rel env rel t1 t2
    | Pfalse ->
      self#visit_predicate_false env
    | Ptrue ->
      self#visit_predicate_true env
    | Pand(pred1,pred2) ->
      self#visit_predicate_and env pred1 pred2
    | Por(pred1,pred2) ->
      self#visit_predicate_or env pred1 pred2
    | Pxor(pred1,pred2) ->
      self#visit_predicate_xor env pred1 pred2
    | Pimplies(pred1,pred2) ->
      self#visit_predicate_implies env pred1 pred2
    | Piff(pred1,pred2) ->
      self#visit_predicate_iff env pred1 pred2
    | Pnot (pred1) ->
      self#visit_predicate_not env pred1
    | Papp (logicinfo,l,t_list) ->
      self#visit_predicate_app env logicinfo l t_list
    | Pforall(quan,pred) ->
      self#visit_predicate_forall env quan pred
    | Pexists(quan,pred) ->
      self#visit_predicate_exists env quan pred
    | _ -> let (loc,_) = predicate.pred_loc in
      Rpp_options.Self.abort ~source:loc "Not supported predicate constructor:@. @[%a@] @."
        Printer.pp_predicate predicate

  method visit_calls env id inline funct formals =
    let new_terms = List.map (fun x -> self#visit_call env x) formals in
    self#build_call env id inline funct new_terms

  method visit_call_term env call_term =
    let (loc,_) = call_term.term_loc in
    match call_term.term_node with
    | Tapp({l_var_info={lv_name ="\\call"}},[],terms)->
      let (id,inline,funct,formals) =
        (match terms with
         |{term_node =TConst(LStr(s))} :: k ->
           (match k with
            | {term_node = TConst (Integer(i,_))} :: q -> (match q with
                | {term_node=TLval(TVar({lv_origin=Some(x)}),TNoOffset)} :: p ->
                  if Ast_types.is_fun x.vtype then
                   s,Z.to_int i,x,p
                  else
                    Rpp_options.Self.fatal ~source:loc
                      "Something went wrong during parsing: \
                       Expected a function as third or first parameter"
                | _ ->
                  Rpp_options.Self.fatal ~source:loc
                    "Something went wrong during parsing: \
                     Expected a logical variable as third parameter")
            | _ ->
              Rpp_options.Self.fatal ~source:loc
                "Something went wrong during parsing: \
                 Expected an integer for seconde parameter")
         | _ ->
           Rpp_options.Self.fatal ~source:loc
             "Something went wrong during parsing: \
              Expected an string for first parameter (identifier)")

      in
      self#visit_calls env id inline funct formals
    | Tapp({l_var_info = {lv_name = "\\call"}},_::_,_) ->
      Rpp_options.Self.fatal ~source:loc
        "Something went wrong during parsing:\
         Expected no label for build-in \\call:@. @[%a@] @."
        Printer.pp_term call_term
    | _ -> Rpp_options.Self.fatal ~source:loc
             "Something went wrong during parsing:\
              \\callset contain no \\call:@. @[%a@] @."
             Printer.pp_term call_term

  method visit_callset env calls =
    let new_calls = List.map (fun x -> self#visit_call_term env x) calls in
    self#build_callset env new_calls

  method visit_callset_predicate env callset =
    match callset.pred_content with
    | Papp({l_var_info = {lv_name = "\\callset"}},[],calls) ->
      self#visit_callset env calls
    | Papp({l_var_info = {lv_name = "\\callset"}},_::_,_) ->
      let (loc,_) = callset.pred_loc in
      Rpp_options.Self.fatal ~source:loc
        "Something went wrong during parsing:\
         Expected no label for build-in \\callset::@. @[%a@] @."
        Printer.pp_predicate callset
    | _ ->  let (loc,_) = callset.pred_loc in
      Rpp_options.Self.fatal ~source:loc
        "Expected \\callset built-in but have:@. @[%a@] @. \
         Whise error must normaly not be raised"
        Printer.pp_predicate callset

  method visit_rpp_predicate_forall_callset env quan callset pred =
    let new_quan = self#build_rpp_quan env quan in
    let new_callset = self#visit_callset_predicate env callset in
    let new_pred = self#visit_predicate env pred in
    self#build_rpp_predicate_forall_callset env new_quan new_callset new_pred

  method visit_rpp_predicate_forall env quan pred =
    let new_quan = self#build_rpp_quan env quan in
    let new_pred = self#visit_predicate env pred in
    self#build_rpp_predicate_forall env new_quan new_pred

  method visit_rpp_predicate_rel  env rel t1 t2 =
    let new_t1 = self#visit_term env t1 in
    let new_t2 = self#visit_term env t2 in
    self#build_rpp_predicate_rel env rel new_t1 new_t2

  method visit_rpp_predicate_implies env pred =
    let new_pred = self#visit_predicate env pred in
    self#build_rpp_predicate_implies env new_pred

  method visit_rpp_predicate_implies_callset env callset pred =
    let new_callset = self#visit_callset_predicate env callset in
    let new_pred = self#visit_predicate env pred in
    self#build_rpp_predicate_implies_callset env new_callset new_pred

  method visit_rpp_predicate env predicate =
    let (loc,_) = predicate.pred_loc in
    match predicate.pred_content with
    | Pforall(_, ({pred_content = Pimplies(_,{pred_content = Papp({l_var_info = {lv_name = "\\callset"}},_,_)})})) ->
      Rpp_options.Self.fatal ~source:loc
        "Something went wrong during parsing: Expected \\callset built-in\
         to be the first element in predicate or in \\forall:@. @[%a@] @."
        Printer.pp_predicate predicate

    | Pforall(quan, ({pred_content = Pimplies(({pred_content = Papp({l_var_info = {lv_name = "\\callset"}},_,_)} as callset),pred)}))->
      self#visit_rpp_predicate_forall_callset env quan callset pred
    | Pforall(quan,pred) ->
      self#visit_rpp_predicate_forall env quan pred
    | Prel(rel,t1,t2) ->
      self#visit_rpp_predicate_rel env rel t1 t2
    | Pimplies(({pred_content = Papp({l_var_info = {lv_name = "\\callset"}},_,_)}as callset),pred)->
      self#visit_rpp_predicate_implies_callset  env callset pred
    | Pimplies(_,{pred_content = Papp({l_var_info = {lv_name = "\\callset"}},_,_)})->
      Rpp_options.Self.fatal ~source:loc
        "Something went wrong during parsing: Expected \\callset built-in\
         to be the first element in predicat or in \\forall:@. @[%a@] @."
        Printer.pp_predicate predicate
    | Pimplies(_,_) ->
      self#visit_rpp_predicate_implies env predicate
    | _ ->
      Rpp_options.Self.abort ~source:loc
        "Error in predicate: Unsuported predicate in relational clause:@. @[%a@] @."
        Printer.pp_predicate predicate
end
