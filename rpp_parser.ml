(**************************************************************************)
(*  This file is part of RPP plug-in of Frama-C.                          *)
(*                                                                        *)
(*  Copyright (C) 2016-2018                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*    alternatives)                                                       *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file LICENSE).                      *)
(**************************************************************************)

open Logic_typing
open Logic_ptree
open Cil_types

let () =
  let callpure =
    {bl_name = "\\callpure";
     bl_labels = []; bl_params = []; bl_type = None;
     bl_profile = []}
  and  callset =
    {bl_name = "\\callset";
     bl_labels = []; bl_params = []; bl_type = None;
     bl_profile = []}
  and  call =
    {bl_name = "\\call";
     bl_labels = []; bl_params = []; bl_type = None;
     bl_profile = []}
  and  callresult =
    {bl_name = "\\callresult";
     bl_labels = []; bl_params = []; bl_type = None;
     bl_profile = []}
  in
  Logic_builtin.add callpure;
  Logic_builtin.add callset;
  Logic_builtin.add call;
  Logic_builtin.add callresult

let id_hash = Hashtbl.create 3;;

exception Unknow_label of string

let type_relational ~typing_context ~loc:loc l =

  let id_checker ctxt identifier  =
    match Str.bounded_split (Str.regexp "_") identifier 2 with
    | "Pre":: id :: [] | "Post" :: id :: []->
      let _ = try (Hashtbl.find id_hash id) with
        | Not_found -> raise (Unknow_label identifier)
        | _ -> assert false
      in
      FormalLabel(identifier)
    | _ -> ctxt.error loc "Expect label of the forme Pre_id or Post_id, but have:@ @[%s@] @."
             identifier
  in

  let id_update ctxt identifier  =
    match Str.bounded_split (Str.regexp "_") identifier 2 with
    | "Pre":: id :: [] ->
      let _ = try (Hashtbl.find id_hash id) with
        | Not_found -> ctxt.error loc "Unknown label: @ @[%s@]  @." identifier
        | _ -> assert false
      in
      "Pre"
    | "Post" :: id :: []->
      let _ = try (Hashtbl.find id_hash id) with
        | Not_found -> ctxt.error loc "Unknown label: @ @[%s@] @." identifier
        | _ -> assert false
      in
      "Here"
    | _ -> ctxt.error loc "Expect label of the forme Pre_id or Post_id but have: @ @[%s@]  @."
             identifier
  in

  let function_parameter_check ctxt x t pred =
    match x.term_type with
    | Ctype(ty) -> if Cil_datatype.Typ.equal t ty then ()
      else
        let test = new Printer.extensible_printer () in
        ctxt.error loc "Cast are not supported:@. @[%a and %a are not compatible@] \
                        for term @. @[%a@] in call of %s @."
          (test#logic_type None)  x.term_type (Printer.pp_typ) t
          Printer.pp_term x (pred.vname)
    | Linteger ->
      begin match t with
        | TInt _ -> ()
        | TNamed({ttype = TInt _},_) -> ()
        | _ -> ctxt.error loc  "Cast are not supported:@. @[%a and %a are not compatible@] \
                                for term @[%a@] in call of %s @."
                 (Printer.pp_logic_type)  x.term_type (Printer.pp_typ) t
                 Printer.pp_term x (pred.vname)
      end
    | Lreal ->
      begin match t with
        | TFloat _ -> ()
        | _ -> ctxt.error loc  "Cast are not supported:@. @[%a and %a are not compatible@] \
                                for term @[%a@] in call of %s @."
                 (Printer.pp_logic_type)  x.term_type (Printer.pp_typ) t
                 Printer.pp_term x (pred.vname)
      end
    | _ ->  ctxt.error loc "Function %s is called with a parameter with type \
                            is not supported:@. @[%a@] @." (pred.vname) Printer.pp_term x
  in

  let is_func var ctxt =
    match var.vtype with
    | TFun _ -> var
    | _ -> ctxt.error loc "Expected a C function: @ @[%a@] @." Printer.pp_varinfo var
  in

  let test_origin ctxt found =
    match found.lv_origin with
    | Some var -> is_func var ctxt
    | None -> ctxt.error loc "No origin information for: @ @[%a@] @." Printer.pp_logic_var found
  in

  let check_is_function_name ctxt p =
    match p.lexpr_node with
    | PLvar x ->
      let test =
        try ctxt.find_var x  with
        | _ -> ctxt.error loc "Unknow function: @ @[%s@]  @." x
      in
      test_origin ctxt test
    | _ ->
      ctxt.error loc "Expected a function name for call but get:@ @[%a@] @." Logic_print.print_lexpr p
  in

  let check_inline_option p =
    match p.lexpr_node with
    | PLconstant(c) -> (match c with
        | IntConstant(s) ->Some(int_of_string s)
        | _ -> None)
    | _ -> None
  in

  let check_call_param ctxt env p f =
    match p.lexpr_node with
    | PLapp ("\\callpure", [], _) ->  ctxt.type_term ctxt env p (** an application. *)
    | PLvar _ -> typing_context.type_term ctxt env p (** a variable *)
    | PLarrow _ -> typing_context.type_term ctxt env p (** field access ({t a->x})*)
    | PLconstant _ -> ctxt.type_term ctxt env p (** a constant. *)
    | PLbinop _ -> ctxt.type_term ctxt env p (** binary operator. *)
    | PLdot _ -> ctxt.type_term ctxt env p (** field access ({t a.x}) *)
    | PLarrget _ -> ctxt.type_term ctxt env p (** array access. *)
    | PLunop _ -> ctxt.type_term ctxt env p (** unary operator. *)
    | _ -> ctxt.error loc "Unsupported terme@. @[%a@] @.in parameter for function %s @."
             Logic_print.print_lexpr p f
  in

  let fun_n_param p =
    match p.vtype with
    | TFun (_,Some l,_,_) -> List.length l
    | TFun (_,None,_,_) -> 0
    | _ -> assert false
  in

  let fun_type_return p =
    match p.vtype with
    | TFun (t,_,_,_) -> t
    | _ -> assert false
  in

  let fun_type_param p =
    match p.vtype with
    | TFun (_,Some t,_,_) -> t
    | TFun (_,None,_,_) ->  []
    | _ -> assert false
  in

  let type_term ctxt env p =
    match p.lexpr_node with
    | PLapp("\\callpure", [], param) ->
      let (inline,param) = (match check_inline_option (List.hd param) with
          | None -> (1,param)
          | Some x -> (x, (List.tl param)))
      in
      let pred = check_is_function_name ctxt (List.hd param) in
      let length_pre = List.length (List.tl param) and length_f = fun_n_param pred in
      if length_pre <> length_f then (
        ctxt.error loc "Expected %d parameter for the call of the pure function %s @."
          length_f pred.vname
      )
      else(
        let predn = List.map (fun p -> check_call_param ctxt env p (pred.vname)) (List.tl param) in
        List.iter2 (fun x (_,t,_) -> function_parameter_check ctxt x t pred)
          (predn) (fun_type_param pred);
        let li = List.hd (ctxt.find_all_logic_functions "\\callpure") in
        li.l_type <- Some(Cil_types.Ctype(fun_type_return pred));
        let inline = Logic_const.tinteger ~loc:pred.vdecl inline in
        let lv_funct = Cil.cvar_to_lvar pred in
        let funct = {term_node = TLval(TVar(lv_funct),TNoOffset);
                     term_loc = inline.term_loc;
                     term_type=Cil_types.Ctype(pred.vtype);
                     term_name = []}
        in
        Logic_const.term ~loc:p.lexpr_loc (Tapp(li,[],(inline :: [funct]) @ predn))
          (Cil_types.Ctype(fun_type_return pred)))

    | PLat(v,l)->
      let label =
        try id_checker ctxt l with
        | Unknow_label s -> ctxt.error loc
                              "Unknow label: @[%s@] in @[%a@]@."
                              s Logic_print.print_lexpr p
      in
      let v_t = typing_context.type_term ctxt env v in
      Logic_const.term ~loc:p.lexpr_loc (Tat (v_t, label)) (v_t.term_type)

    | PLapp ("\\callresult", [], param) ->
      if List.length param <> 1 then
        ctxt.error loc "Expected one parameter for \\callresult built-in (identifier):@. @[%a@] @."
          Logic_print.print_lexpr p
      else
        (
          let id = List.hd param in
          let id = match id.lexpr_node with
            | PLvar n -> n
            | _ -> ctxt.error loc "Expect an identifier as parameter for \
                                   built-in \\callresult: @. @[%a@] @."
                     Logic_print.print_lexpr p
          in
          let f =
            (try (Hashtbl.find id_hash id)
             with
             | Not_found -> ctxt.error loc "Unknown identifier %s for @. @[%a@] @."
                              id Logic_print.print_lexpr p
             | _ -> assert false
            )
          in
          let li = List.hd (ctxt.find_all_logic_functions "\\callresult") in
          li.l_type <- Some(Cil_types.Ctype(fun_type_return f));
          let ti = Logic_const.tstring ~loc:p.lexpr_loc id in
          Logic_const.term ~loc:p.lexpr_loc (Tapp(li,[],[ti])) (Cil_types.Ctype(fun_type_return f)))

    | PLapp ("\\callpure", _, _) ->
      ctxt.error loc "Expect no label for built-in \\callpure: @. @[%a@] @."
        Logic_print.print_lexpr p
    | PLapp ("\\callresult", _, _) ->
      ctxt.error loc "Expect no label for built-in \\callresult: @. [%a@] @."
        Logic_print.print_lexpr p
    | _ -> typing_context.type_term ctxt env p
  in

  let check_identifier ctxt l pred  =
    let rec aux li acc =
      match li with
      | h1 :: q1 -> aux q1 (h1 :: acc)
      | [] -> acc
    in
    if List.length l == 0 then
      ctxt.error loc "Expect an identifier for the \\call to function %s @." pred.vname
    else(
      let reverse = aux l [] in
      (List.tl reverse,List.hd reverse))
  in

  let check_callset_param ctxt env p =
    match p.lexpr_node with
    | PLapp ("\\call",[], param) ->
      let (inline,param) = (match check_inline_option (List.hd param) with
          | None -> (1,param)
          | Some x -> (x, (List.tl param)))
      in
      let pred = check_is_function_name ctxt (List.hd param) in
      let (funct_param, id) = check_identifier ctxt (List.tl param) pred in
      let length_pre = (List.length funct_param) and length_f = fun_n_param pred in
      if length_pre <> length_f then (
        ctxt.error loc "Expected %d parameter for the \\call of the function %s: @. @[%a@] @."
          length_f pred.vname  Logic_print.print_lexpr p
      )
      else(
        let id = (match id.lexpr_node with
            | PLvar n -> n
            | _ -> ctxt.error loc "Expect an identifier as last parameter \
                                   for function %s: @. [%a@] @."
                     pred.vname Logic_print.print_lexpr p)
        in
        match (Hashtbl.find id_hash id) with
        | exception Not_found ->
          Hashtbl.add id_hash id pred;
          let predn =
            List.map (fun p -> check_call_param ctxt env p (pred.vname)) (List.rev funct_param)
          in
          List.iter2 (fun x (_,t,_) -> function_parameter_check ctxt x t pred)
            (predn) (fun_type_param pred);

          let li = List.hd (ctxt.find_all_logic_functions "\\call") in
          let inline = Logic_const.tinteger ~loc:pred.vdecl inline in
          let id = Logic_const.tstring ~loc:pred.vdecl id in
          li.l_type <- Some(Cil_types.Ctype(fun_type_return pred));
          let lv_funct = Cil.cvar_to_lvar pred in
          let funct = {term_node = TLval(TVar(lv_funct),TNoOffset);
                       term_loc = inline.term_loc;
                       term_type=Cil_types.Ctype(pred.vtype);
                       term_name = []}
          in
          Logic_const.term ~loc:p.lexpr_loc (Tapp(li,[],id::inline::[funct]@predn))
            (Cil_types.Ctype(fun_type_return pred))

        | _ -> ctxt.error loc "Multiple use of identifier %s @." id)

    | PLapp ("\\call", _, _) -> ctxt.error loc "Expect no label for built-in \\call: @. @[%a@] @."
                                  Logic_print.print_lexpr p

    | _ -> ctxt.error loc "Unsupported terme type in \\callset built-in: @. @[%a@] @."
             Logic_print.print_lexpr p
  in

  let check_call_set ctxt env p  =
    match p.lexpr_node with
    | PLapp ("\\callset",[], param) ->
      let calls = (List.map (fun p -> check_callset_param ctxt env p) param) in
      let li = List.hd (ctxt.find_all_logic_functions "\\callset") in
      let named_pred =
        {
          pred_name =[];
          pred_loc = p.lexpr_loc;
          pred_content = (Papp(li,[],calls))
        }
      in
      Logic_const.pred_of_id_pred (Logic_const.new_predicate named_pred)

    | PLapp ("\\callset", _, _) -> ctxt.error loc "Expect no label for built-in \\callset @."

    | _ -> ctxt.error loc "Unsupported terme type in \\rela built-in @."
  in

  let type_predicate  ctxt env p =
    match p.lexpr_node with
    | PLnamed(name,exp) ->
      let pred = ctxt.type_predicate ctxt env exp in
      {pred_name = [name];
       pred_loc = pred.pred_loc;
       pred_content = pred.pred_content}

    | PLapp ("\\callpure", _, _) -> ctxt.error loc "A \\callpure is equivalent to a terme @."

    | PLapp("\\rela",[], param) ->
      if not(Rpp_options.Is_buildin_rela_first.get()) then
        ctxt.error loc
          "Expected \\rela built-in to be the first element in predicat or in \\forall: @. @[%a@] @."
          Logic_print.print_lexpr p
      else(
        (if List.length param != 2 then(
            ctxt.error loc "Expected 2 parameter for the \\rela built-in: @. @[%a@] @."
              Logic_print.print_lexpr p)
         else(
           let callset = check_call_set ctxt env (List.hd param) in
           let pred = typing_context.type_predicate ctxt env (List.hd(List.tl param)) in
           Logic_const.pimplies ~loc:p.lexpr_loc (callset, pred)
         )))

    | PLimplies(({lexpr_node = PLapp("\\callset",_,_)} as set),pred) ->
      if not(Rpp_options.Is_buildin_rela_first.get()) then
        ctxt.error loc
          "Expected \\callset built-in to be the first element in predicat \
           or in \\forall:@. @[%a@] @."
          Logic_print.print_lexpr p
      else(
        let callset = check_call_set ctxt env set in
        let pred = typing_context.type_predicate ctxt env pred in
        Logic_const.pimplies ~loc:p.lexpr_loc (callset, pred)
      )

    | PLapp("\\callset",_,_) ->
      ctxt.error loc "Built-in \\callset must be the first element in an implication: @. @[%a@] @."
        Logic_print.print_lexpr p

    | PLforall(_) -> typing_context.type_predicate ctxt env p

    | PLapp ("\\rela", _, _) -> ctxt.error loc "Expect no label for built-in \\rela: @. @[%a@] @."
                                  Logic_print.print_lexpr p

    | PLapp (a,labels,param) ->
      let new_labels =
        List.map (fun x -> (id_update ctxt x)) labels
      in
      let new_pred =
        typing_context.type_predicate ctxt env ({p with lexpr_node = PLapp(a,new_labels,param)})
      in
      begin
        match new_pred.pred_content with
        |Papp(l_v,_,params) ->
          let new_labels_list =
            List.map (fun x  -> FormalLabel(x)) labels
          in
          {new_pred with pred_content = Papp(l_v,new_labels_list,params)}
        | _ -> assert false
      end
    | _ -> Rpp_options.Is_buildin_rela_first.set(false); typing_context.type_predicate ctxt env p
  in

  let ctxt = { typing_context with type_term ;type_predicate} in
  match l with
  | p ::[] -> Rpp_options.Is_buildin_rela_first.set(true);
    let acsl_pred = Ext_preds[ctxt.type_predicate ctxt ctxt.pre_state p] in
    Hashtbl.clear id_hash;
    acsl_pred
  | _ -> typing_context.error loc "expecting one predicate in relational clause @."

let ()  = Logic_typing.register_behavior_extension "relational"  type_relational
