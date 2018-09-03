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

open Cil_types
open Rpp_types

let map_extend f l ll =
  let rec aux func list list_long acc =
    match list,list_long with
    | [], _::_ -> (List.rev acc, list_long)
    | [],[] -> (List.rev acc, list_long)
    | h1 :: q1 , h2 :: q2 -> aux f q1 q2 (func h1 h2::acc)
    | _::_ ,[] -> invalid_arg "map_extend"

  in
  aux f l ll []

(**
   Generation of the axiomatic definition
 **)
let generat_axiom l self new_predi new_labels logic_info logic_info_pure =
  let name_axiome =
    String.concat "_" ["Relational_axiome";string_of_int (Rpp_options.Counting_axiome.next ())]
  in
  let name_lemma =
    String.concat "_" ["Relational_lemma";string_of_int (Rpp_options.Counting_axiome.get ())]
  in
  let predicate_named =
    Logic_const.new_predicate new_predi
  in
  let new_labels = match new_labels with
    | _ :: _ -> new_labels
    | [] -> [FormalLabel("L")]
  in
  let lemma =
    Cil_types.Dlemma (name_lemma,false,new_labels,[],
                      (Logic_const.pred_of_id_pred predicate_named),[],l)
  in
  let functions =
    Hashtbl.fold (fun _ (logic_information,_) acc ->
        Queue.add (fun () ->
            Logic_utils.add_logic_function logic_information;
          )
          self#get_filling_actions;
        (Cil_types.Dfun_or_pred (logic_information,l)) :: acc)
      logic_info_pure.predicate_info_pure []
  in
  let pred =
    Hashtbl.fold (fun _ (logic_information,_,_,_,_) acc ->
        Queue.add (fun () ->
            Logic_utils.add_logic_function logic_information;
          )
          self#get_filling_actions;
        (Cil_types.Dfun_or_pred (logic_information,l)) :: acc)
      logic_info.predicate_info []
  in
  let axiome =
    Cil_types.Daxiomatic(name_axiome,functions@pred@[lemma],[],l)
  in
  Queue.add(fun () ->
      Annotations.add_global (Rpp_options.emitter) axiome;
    )
    self#get_filling_actions;
  (axiome,name_lemma,predicate_named)

let check_type t1 t2 =
  match t1, t2 with
  | Ctype(t1),t2 when Cil_datatype.Typ.equal t1 t2 -> ()
  | _ , _ -> assert false

let param_generat self x y l label =
  let x = Cil.get_varinfo self#behavior x in
  let term_nodei =
    TLval(TVar(Cil.cvar_to_lvar x),TNoOffset)
  in
  let termi =
    {term_node = term_nodei;
     term_loc = l;
     term_type = Ctype(x.vtype);
     term_name = []}
  in
  let old_term_nodei =
    Tat(termi,BuiltinLabel(label))
  in
  let term = {
    term_node = old_term_nodei;
    term_loc = l;
    term_type = Ctype(x.vtype);
    term_name = []}
  in
  check_type y.lv_type x.vtype;
  term

let pointer_param_generat self x y l =
  let x = Cil.get_varinfo self#behavior x in
  let term_nodei =
    TLval(TVar(Cil.cvar_to_lvar x),TNoOffset)
  in
  let term ={
    term_node = term_nodei;
    term_loc = l;
    term_type = Ctype(x.vtype);
    term_name = []}
  in
  check_type y.lv_type x.vtype;
  term
(**
   Generation of behaviour clauses for the pure function involved in the relational propertie
*)
let generat_behavior_pure l self logic_info_pure =
  let name_behavior =
    String.concat "_" ["Relational_behavior";
                       string_of_int (Rpp_options.Counting_axiome.get ())]
  in
  Hashtbl.iter (
    fun _ (logic_information,kf) ->
      Queue.add(fun () ->
          let kf = Cil.get_kernel_function self#behavior kf in
          let params = List.map2 (fun x y ->
              param_generat self x y l Old
            ) (Globals.Functions.get_params kf) (logic_information.l_profile)
          in
          let term_node1 =
            TLval(TResult(Kernel_function.get_return_type kf),TNoOffset)
          in
          let term_node2 =
            Tapp(logic_information,[],params)
          in
          let logic_return_type =
            match logic_information.l_type with
            | Some x -> x
            | None -> assert false
          in
          let t =
            Kernel_function.get_return_type kf
          in
          check_type logic_return_type t;
          let term1 = {
            term_node = term_node1;
            term_loc = l;
            term_type = Ctype(t);
            term_name = []}
          in
          let term2 = {
            term_node = term_node2;
            term_loc = l;
            term_type = logic_return_type;
            term_name = []}
          in
          let predi =
            Logic_const.prel(Req,term1,term2)
          in
          let ensures =
            (Normal,Logic_const.new_predicate predi)
          in
          let funbehavior =
            Cil.mk_behavior ~name:name_behavior ~post_cond:[ensures] ()
          in
          Annotations.add_behaviors ~register_children:true (Rpp_options.emitter) kf [funbehavior];

          (*Set the status of the clause to true (the behavior is supposed valid)*)
          let property =
            Property.ip_of_ensures kf (Kglobal) funbehavior ensures
          in
          Property_status.emit (Rpp_options.emitter) [] property Property_status.True;
        )
        self#get_filling_actions)
    logic_info_pure.predicate_info_pure

let make_result kf sub l =
  match Kernel_function.get_return_type kf, sub with
  | TVoid(_), [] -> []
  | _ , [y]->
    begin
      let t =
        Kernel_function.get_return_type kf
      in
      let term_node =
        TLval(TResult(t),TNoOffset)
      in
      let term = {
        term_node = term_node;
        term_loc = l;
        term_type = Ctype(t);
        term_name = []}
      in
      check_type y.lv_type t;
      [term]
    end
  | _ , _ -> assert false

let make_labels logic_information =
  match logic_information.l_labels with
  | FormalLabel("pre") :: FormalLabel("post") :: [] ->
    [BuiltinLabel(Pre);BuiltinLabel(Post)]
  | FormalLabel("post") :: []  ->
    [BuiltinLabel(Post)]
  | FormalLabel("pre") :: []  ->
    [BuiltinLabel(Pre)]
  | [] -> []
  | _ -> assert false

(**
   Generation of behaviour clauses for the function involved in the relational propertie
*)
let generat_behavior l self logic_info =
  let name_behavior =
    String.concat "_" ["Relational_behavior";
                       string_of_int (Rpp_options.Counting_axiome.get ())]
  in
  Hashtbl.iter (
    fun _ (logic_information, kf,assigns,froms,pointers) ->
      Queue.add(fun () ->
          let (params,sub) =
            map_extend (fun x y->
                param_generat self x y l Old
              ) (Globals.Functions.get_params kf) (logic_information.l_profile)
          in
          let (params_froms,sub) =
            map_extend (fun x y ->
                param_generat self x y l Pre
              ) froms sub
          in
          let (params_assigns_post,sub) =
            map_extend (fun x y->
                param_generat self x y l Post
              ) assigns sub
          in
          let (param_pointers,sub) =
            map_extend (fun x y ->
                pointer_param_generat self x y l
              ) pointers sub
          in
          let param_result = make_result kf sub l in
          let labels = make_labels logic_information in
          let predicate =
            Papp(logic_information,labels,
                 params@params_froms@params_assigns_post@param_pointers@param_result)
          in
          let loc = l in
          let predicate_name =
            {pred_name = [];pred_loc= loc;pred_content= predicate}
          in
          let ensures =
            (Normal,Logic_const.new_predicate predicate_name)
          in
          let funbehavior =
            Cil.mk_behavior ~name:name_behavior ~post_cond:[ensures] ()
          in
          Annotations.add_behaviors ~register_children:true (Rpp_options.emitter) kf [funbehavior];

          (*Set the status of the clause to true (the behavior is supposed valid)*)
          let property =
            Property.ip_of_ensures kf (Kglobal) funbehavior ensures
          in
          Property_status.emit (Rpp_options.emitter) [] property Property_status.True;
        )
        self#get_filling_actions)
    logic_info.predicate_info

(**
   Generation of behaviour clauses for the target function involved in the relational propertie
*)
let generat_behavior_for_kf l self logic_info (target_kf,replace_target) global_map =
  let name_behavior =
    "Relational_behavior"
  in
  let (from_map,assert_map,from_p_map,assert_p_map) =
    global_map
  in
  Hashtbl.iter (
    fun _ (logic_information, kf,assigns,froms,pointers) ->
      if Cil_datatype.Kf.equal kf replace_target then
        begin
          let (params,sub) =
            map_extend (fun x y->
                param_generat self x y l Old
              ) (Globals.Functions.get_params target_kf) (logic_information.l_profile)
          in
          let (params_froms,sub) =
            map_extend (fun x y ->
                match  Cil_datatype.Varinfo.Map.find x from_map with
                | exception Not_found -> assert false
                | {lv_origin = Some x} -> param_generat self x y l Pre
                | _ -> assert false
              ) froms sub
          in
          let (params_assigns_post,sub) =
            map_extend (fun x y->
                match  Cil_datatype.Varinfo.Map.find x assert_map with
                | exception Not_found -> assert false
                | {lv_origin = Some x} -> param_generat self x y l Post
                | _ -> assert false
              ) assigns sub
          in
          let (param_pointers,sub) =
            map_extend (fun x y ->
                match  Cil_datatype.Varinfo.Map.find x from_p_map with
                | exception Not_found ->
                  begin
                    match  Cil_datatype.Varinfo.Map.find x assert_p_map with
                    | exception Not_found -> assert false
                    | {lv_origin = Some x} -> pointer_param_generat self x y l
                    | _ -> assert false
                  end
                | {lv_origin = Some x} -> pointer_param_generat self x y l
                | _ -> assert false
              ) pointers sub
          in
          let param_result = make_result kf sub l in
          let labels = make_labels logic_information in
          let predicate =
            Papp(logic_information,labels,
                 params@params_froms@params_assigns_post@param_pointers@param_result)
          in
          let loc = l in
          let predicate_name =
            {pred_name = [];pred_loc= loc;pred_content= predicate}
          in
          (*Since Cil_datatype.Predicate.equal don't support the annotation, we use string equality.
            This is a temporare solution and not very nice*)
          let test =
            Annotations.fold_ensures(fun _ (_,pred_name) test ->
                let s1 =
                  Format.asprintf "Fold pred %a @." Printer.pp_predicate pred_name.ip_content
                in
                let s2 =
                  Format.asprintf "Fold pred %a @." Printer.pp_predicate predicate_name
                in
                String.equal s1 s2 || test
              ) target_kf name_behavior false
          in
          match test with
          | false ->
            let ensures =
              (Normal,Logic_const.new_predicate predicate_name)
            in
            let funbehavior =
              Cil.mk_behavior ~name:name_behavior ~post_cond:[ensures] ()
            in
            Annotations.add_behaviors
              ~register_children:true (Rpp_options.emitter) target_kf [funbehavior];

            (*Set the status of the clause to true (the behavior is supposed valid)*)
            let property =
              Property.ip_of_ensures target_kf (Kglobal) funbehavior ensures
            in
            Property_status.emit (Rpp_options.emitter) [] property Property_status.True;
          | true -> ()
        end
      else ()) logic_info.predicate_info

(**
   Generation of behaviour clauses for the target pure function involved in the relational propertie
*)
let generat_behavior_pure_for_kf l self logic_info_pure (target_kf,replace_target)=
  let name_behavior =
    "Relational_behavior"
  in
  Hashtbl.iter (
    fun _ (logic_information,kf) ->
      if Cil_datatype.Kf.equal kf replace_target then
        begin
          let params = List.map2 (fun x y ->
              param_generat self x y l Old
            ) (Globals.Functions.get_params target_kf) (logic_information.l_profile)
          in
          let term_node1 =
            TLval(TResult(Kernel_function.get_return_type target_kf),TNoOffset)
          in
          let term_node2 =
            Tapp(logic_information,[],params)
          in
          let logic_return_type =
            match logic_information.l_type with
            | Some x -> x
            | None -> assert false
          in
          let t =
            Kernel_function.get_return_type kf
          in
          check_type logic_return_type t;
          let term1 = {
            term_node = term_node1;
            term_loc = l;
            term_type =Ctype(Kernel_function.get_return_type target_kf);
            term_name = []}
          in
          let term2 = {
            term_node = term_node2;
            term_loc = l;
            term_type = logic_return_type;
            term_name = []}
          in
          let predicate_name =
            Logic_const.prel(Req,term1,term2)
          in
          (*Since Cil_datatype.Predicate.equal don't support the annotation, we use string equality.
            This is a temporare solution and not very nice*)
          let test =
            Annotations.fold_ensures(fun _ (_,pred_name) test ->
                let s1 =
                  Format.asprintf "Fold pred %a @." Printer.pp_predicate pred_name.ip_content
                in
                let s2 =
                  Format.asprintf "Fold pred %a @." Printer.pp_predicate predicate_name
                in
                String.equal s1 s2 || test
              ) target_kf name_behavior false
          in
          match test with
          | false ->
            let ensures =
              (Normal,Logic_const.new_predicate predicate_name)
            in
            let funbehavior =
              Cil.mk_behavior ~name:name_behavior ~post_cond:[ensures] ()
            in
            Annotations.add_behaviors
              ~register_children:true (Rpp_options.emitter) target_kf [funbehavior];
            (*Set the status of the clause to true (the behavior is supposed valid)*)
            let property =
              Property.ip_of_ensures target_kf (Kglobal) funbehavior ensures
            in
            Property_status.emit (Rpp_options.emitter) [] property Property_status.True;
          | true -> ()
        end
      else ()) logic_info_pure.predicate_info_pure

(**
   Generation of behaviour clauses for the target pure function involved in the relational propertie
*)
let generat_help_behavior_pure_for_kf l logic_infos_pure (target_kf,replace_target)=
  let name_behavior =
    "Relational_behavior_helper"
  in
  let functions = Hashtbl.create 7 in
  List.iter(
    fun logic_info_pure ->
      Hashtbl.iter (
        fun _ (logic_information,kf) ->
          if not(Cil_datatype.Kf.equal kf replace_target) then
            begin
              match Hashtbl.find functions kf with
              | exception Not_found ->
                Hashtbl.add functions kf (ref ([logic_information]))
              | x -> x:= logic_information :: !x
            end
      )logic_info_pure
  )logic_infos_pure;

  let rec aux list acc =
    match list with
    | [] -> ()
    | h :: q  ->
      begin
        let param = List.map (fun x ->
            Cil_const.make_logic_var_quant
              (x.lv_name) (x.lv_type)
          ) (acc.l_profile)
        in
        let params = List.map (fun x ->
            let term_nodei =
              TLval(TVar(x),TNoOffset)
            in
            {term_node = term_nodei;
             term_loc = l;
             term_type = x.lv_type;
             term_name = []}
          ) param
        in
        let term_node1 =
          Tapp(acc,[],params)
        in
        let t =
          match acc.l_type with
          | None -> assert false
          | Some x -> x
        in
        let term1 = {term_node = term_node1;
                     term_loc = l;
                     term_type = t;
                     term_name = []}
        in

        let term_node2 =
          Tapp(List.hd list,[],params)
        in
        let term2 = {term_node = term_node2;
                     term_loc = l;
                     term_type = t;
                     term_name = []}
        in
        let predi =
          Logic_const.prel(Req,term1,term2)
        in
        let new_axiome_predicate_content =
          Pforall(param,predi)
        in
        let predicate_name = {pred_name = [];
                              pred_loc = l;
                              pred_content = new_axiome_predicate_content;}
        in
        (*Since Cil_datatype.Predicate.equal don't support the annotation, we use string equality.
              This is a temporare solution and not very nice*)
        let test =
          Annotations.fold_ensures(fun _ (_,pred_name) test ->
              let s1 =
                Format.asprintf "Fold pred %a @." Printer.pp_predicate pred_name.ip_content
              in
              let s2 =
                Format.asprintf "Fold pred %a @." Printer.pp_predicate predicate_name
              in
              String.equal s1 s2 || test
            ) target_kf name_behavior false
        in
        begin
          match test with
          | false ->
            let ensures =
              (Normal,Logic_const.new_predicate predicate_name)
            in
            let funbehavior =
              Cil.mk_behavior ~name:name_behavior ~post_cond:[ensures] ()
            in
            Annotations.add_behaviors
              ~register_children:true (Rpp_options.emitter) target_kf [funbehavior];
            (*Set the status of the clause to true (the behavior is supposed valid)*)
            let property =
              Property.ip_of_ensures target_kf (Kglobal) funbehavior ensures
            in
            Property_status.emit (Rpp_options.emitter) [] property Property_status.True
          | true -> ()
        end;
        aux q h
      end
  in
  Hashtbl.iter(
    fun _ l ->
      aux (List.tl !l) (List.hd !l)
  )functions


(**
   Function for generating the axiomatic definition related the
   relational property and the corresponding behaviour for each
   function related the the relational property
*)
let relationnel_axiom l self new_predi new_labels (logic_info) (logic_info_pure) =
  let (axiome,name_lemma,predicate_named) =
    generat_axiom l self new_predi new_labels logic_info logic_info_pure
  in
  generat_behavior_pure l self logic_info_pure;
  generat_behavior l self logic_info;
  (axiome,(name_lemma,[],[],(Logic_const.pred_of_id_pred predicate_named),l))
