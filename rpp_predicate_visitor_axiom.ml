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
open Rpp_predicate_visitor

let make_separate env separated call_data =
  let separated_terms =
    List.fold_left(fun data i ->
        let terms = List.map
            (fun x -> Rpp_generator.do_one_terms_vis_axiom
                i.id_sep call_data i.formal_binder
                env.self_axiom x)
            i.separated_terms_axiom
        in terms @ data
      ) [] separated
  in
  match separated_terms with
  | h::_ ->
    let pointer_predicate_separated =
      Pseparated(separated_terms)
    in
    let pred =
      {pred_name = [];pred_loc=h.term_loc; pred_content= pointer_predicate_separated}
    in
    Some pred
  | [] ->  None

let id_convert_axiom identifier loc call_side_effect_data=
  match Str.bounded_split (Str.regexp "_") identifier 2 with
  | "Pre":: id :: []  ->
    (match List.find (fun data -> String.equal id data.id )
             call_side_effect_data  with
    | exception Not_found ->
      Rpp_options.Self.abort ~source:loc "The id %s is unknown in this clause" id
    | _ -> String.concat "_" ["pre";id])
  |  "Post" :: id :: [] ->
    (match List.find (fun data -> String.equal id data.id)
             call_side_effect_data  with
    | exception Not_found ->
      Rpp_options.Self.abort ~source:loc "The id %s is unknown in this clause" id
    | _ -> String.concat "_" ["post";id])
  | _ -> Rpp_options.Self.abort ~source:loc "Expect label of the forme Pre_id or Post_id:@ @[%s@] @."
           identifier

exception Found_equals

let rec make_unique_name ?(acc:int = 0) n formals =
  match Cil_datatype.Logic_var.Map.iter(
      fun _ x -> match String.equal x.lv_name n with
        | true -> raise Found_equals
        | false -> ())
      formals with
  | exception Found_equals -> let new_name = String.concat "_" [n; string_of_int acc ] in
    make_unique_name ~acc:(acc+1) new_name formals
  | _ -> n

let typer self loc l env func =
  let args = match func.vtype with
    | TFun (_,l,_,_) ->  Cil.argsToList l
    | _ -> assert false
  in
  List.map2(fun th (_,t,_) ->
      let new_t =
        Rpp_predicate_visitor.get_typ_in_current_project t self loc
      in
     match th.term_type,new_t with
      | Ctype(t1) ,t2 when Cil_datatype.Typ.equal t1 t2 -> th
      | Ctype(_) ,_  | Linteger , TInt(_)
      | Linteger, TNamed({ttype = TInt _},_)
      | Lreal , TInt(_) | Lreal , TFloat(_) ->
        Logic_const.term
          ~loc:(env.pos_axiom)
          (TCastE(new_t,th))
          (Ctype new_t)
      | _ , _->    Rpp_options.Self.fatal ~source:env.loc_axiom
                     "Something went wrong :\
                      Logic function %s is called with a parameter with type \
                      is not supported :@. @[%a@] @."
                     (func.vname) Printer.pp_term th ) l args

let make_new_global env id l n =
  List.map (fun x ->
      let name =
        String.concat "" [x.vname;"_";id; n]
      in
      let assigns_type =
        Rpp_predicate_visitor.get_typ_in_current_project
          x.vtype env.self_axiom#behavior env.loc_axiom
      in
      Cil_const.make_logic_var_quant name (Ctype assigns_type)) l

let make_new_global2 env id l n =
  make_new_global env id (List.map(fun (_,x) -> x ) l) n

let make_global_filter env id l n map =
  List.map (fun x ->
      match Cil_datatype.Varinfo.Map.find x map  with
      | exception Not_found ->
        let name =
          String.concat "_" [x.vname;"_";id;n]
        in
        let assigns_type =
          Rpp_predicate_visitor.get_typ_in_current_project
            x.vtype env.self_axiom#behavior env.loc_axiom
        in
        let l_v =
          Cil_const.make_logic_var_quant name (Ctype assigns_type)
        in
        l_v
      | v -> v)
    (List.map(fun (_,x) -> x ) l)

let make_map l1 l2=
  let new_map = Cil_datatype.Varinfo.Map.empty in
  List.fold_left2(fun x l1 l2 ->
      Cil_datatype.Varinfo.Map. add l1 l2 x)
    new_map l1 l2

let make_map2 l1 l2 =
  make_map (List.map(fun (_,x) -> x ) l1) l2

let make_new_logic env name map =
  List.map (fun x ->
      let  name =
        String.concat "" [x.vname;name]
      in
      let typ =
        Rpp_predicate_visitor.get_typ_in_current_project
            x.vtype env.self_axiom#behavior env.loc_axiom
      in
      Cil_const.make_logic_var_formal name (Ctype typ))
    map

let make_read env kf formals param_from param_assigns param_pointer pointers data =

  let param_from_pre = make_map data.froms param_from in
  let param_assigns_post = make_map data.assigns param_assigns in
  let param_pointer = make_map pointers param_pointer in
  let global_map =
    (param_from_pre,param_assigns_post,param_pointer,Cil_datatype.Varinfo.Map.empty)
  in
  let f t =
    Rpp_generator.do_one_simpl_term_vis
      kf formals (Some(-1)) global_map env.self_axiom t
  in
  let read_terms_post =
    List.fold_right(fun (x,_) acc ->
        (f x) ::acc) data.assigns_p []
  in
  let read_terms_post =
    List.fold_right(fun (x,_) acc ->
        (f x) ::acc) data.assigns_p_f read_terms_post
  in
  let read_terms_post = List.map
      (fun x ->
         let new_term_node = Tat(x,FormalLabel("post")) in
         let new_term = {x with term_node = new_term_node}in
         Logic_const.new_identified_term new_term
      ) read_terms_post
  in
  let read_terms_pre =
    List.fold_right(fun (x,_) acc ->
        (f x)::acc) data.from_p []
  in
  let read_terms_pre =
    List.fold_right(fun (x,_) acc ->
        (f x) ::acc) data.from_p_f read_terms_pre
  in
  let read_terms_pre = List.map
      (fun x ->
         let new_term_node = Tat(x,FormalLabel("pre")) in
         let new_term = {x with term_node = new_term_node}in
         Logic_const.new_identified_term new_term
      ) read_terms_pre
  in
  read_terms_post@read_terms_pre

let make_logic_information env name kf type_return data pointers predicate_info =
  let new_logic_information =
    Cil_const.make_logic_info name
  in
  let test_kf =
    Cil.get_kernel_function env.self_axiom#behavior kf
  in
  let return_param_name = "return_variable_relational" in
  let param_return =
    match type_return with
    | TVoid _ -> []
    | x ->
      let type_return =
        Rpp_predicate_visitor.get_typ_in_current_project
          x env.self_axiom#behavior env.loc_axiom
      in
      [Cil_const.make_logic_var_formal (return_param_name) (Ctype(type_return))]
  in
  let param = make_new_logic env "" (Globals.Functions.get_params test_kf) in
  let param_from_pre = make_new_logic env "_pre" data.froms in
  let param_assigns_post = make_new_logic env "_post" data.assigns in
  let param_pointer = make_new_logic env "" pointers in
  new_logic_information.l_profile <-
    param @ param_from_pre @ param_assigns_post @
    param_pointer@param_return;
  new_logic_information.l_type <- None;
  if List.length data.assigns_p <> 0 ||  List.length data.assigns_p_f <> 0 then
    new_logic_information.l_labels <-
      FormalLabel("post") :: []
  else ();
  if List.length data.from_p <> 0|| List.length data.from_p_f <> 0 then
    new_logic_information.l_labels <-
      FormalLabel("pre") :: new_logic_information.l_labels
  else ();
  let read_terms =
    make_read env kf param param_from_pre param_assigns_post param_pointer pointers data
  in
  begin
    match read_terms with
    | [] -> ()
    | x -> new_logic_information.l_body <- LBreads(x)
  end;
  Hashtbl.add predicate_info name (new_logic_information, test_kf,data.assigns,data.froms,pointers);
  (new_logic_information,test_kf,data.assigns,data.froms,pointers)

let make_separate_term data =
  let separated_terms =
    List.fold_right(fun (x,_) acc ->
        x ::acc) data.assigns_p []
  in
  let separated_terms =
    List.fold_right(fun (x,_) acc ->
        x::acc) data.assigns_p_f separated_terms
  in
  let separated_terms =
    List.fold_right(fun (x,_) acc ->
        x ::acc) data.from_p separated_terms
  in
  let separated_terms =
    List.fold_right(fun (x,_) acc ->
        x ::acc) data.from_p_f separated_terms
  in
  let separated_term =
    Rpp_predicate_visitor.clone_killer
      separated_terms
      []
      Cil_datatype.Term.equal
  in
  separated_term

let make_labels logic_info id =
  match logic_info.l_labels with
  | FormalLabel("pre") :: FormalLabel("post") :: [] ->
    let name1 = String.concat "_" ["pre";id] in
    let name2 = String.concat "_" ["post";id] in
    [FormalLabel(name1);FormalLabel(name2)]
  | FormalLabel("post") :: []  ->
    let name2 = String.concat "_" ["post";id] in
    [FormalLabel(name2)]
  | FormalLabel("pre") :: []  ->
    let name1 = String.concat "_" ["pre";id] in
    [FormalLabel(name1)]
  | [] -> []
  | _ -> assert false

let predicate_visitor predicate self_behavior =
  let v = object (self)
    inherit [_] Rpp_visitor.rpp_visitor

    val quant_map = ref Cil_datatype.Logic_var.Map.empty
    val fun_quant_map = ref Cil_datatype.Logic_var.Map.empty
    val new_labels = ref ([]:Cil_types.logic_label list)
    val call_side_effect_data = ref ([]:Rpp_types.call_data_logic list)
    val call_data_separated = ref([]:Rpp_types.call_data_separated list)
    val functions_pure = ref ([]:string list)
    val predicate_info_pure :
      (string, Cil_types.logic_info*Cil_types.kernel_function)
        Hashtbl.t =
      Hashtbl.create 3
    val predicate_info :
      (string, Cil_types.logic_info*Cil_types.kernel_function*
               Cil_types.varinfo list *Cil_types.varinfo list *Cil_types.varinfo list)
        Hashtbl.t =
      Hashtbl.create 3
    val formal_pointer_check= ref ([]:Cil_types.term list)

    method  build_call_app env inline funct formals ty =
      let temp = !quant_map in
      quant_map := !fun_quant_map;
      let data = self#build_term_app_call env inline funct formals ty in
      quant_map := temp;
      data

    method build_call_Toffset env offset =
      let temp = !quant_map in
      quant_map := !fun_quant_map;
      let data = self#build_Toffset env offset in
      quant_map := temp;
      data

    method  build_call_valvar env logic_var off ty =
      let temp = !quant_map in
      quant_map := !fun_quant_map;
      let data = self#build_term_valvar env logic_var off ty in
      quant_map := temp;
      data

    method  build_call_const env l_c ty =
      let temp = !quant_map in
      quant_map := !fun_quant_map;
      let data = self#build_term_const env l_c ty in
      quant_map := temp;
      data

    method  build_call_valme env new_term off ty =
      let temp = !quant_map in
      quant_map := !fun_quant_map;

      let term_node_axiome = TLval(TMem(new_term),off) in
      let typ = match ty with
        | Ctype t -> Ctype(Rpp_predicate_visitor.get_typ_in_current_project
                             t (env.self_axiom#behavior) (env.loc_axiom))
        | Linteger -> Linteger
        | Lreal -> Lreal
        | _ -> Rpp_options.Self.fatal ~source:env.loc_axiom
                 "Match bad terme type in term:@. @[%a@] @." Printer.pp_term new_term
      in
      let axiome_term =
        Logic_const.term
          ~loc:(env.pos_axiom)
          term_node_axiome
          typ
      in
      quant_map := temp;
      axiome_term

    method  build_call_binop env bin term1 term2 ty =
      let temp = !quant_map in
      quant_map := !fun_quant_map;
      let data = self#build_term_binop env bin term1 term2 ty in
      quant_map := temp;
      data

    method  build_call_logic_coerce env l_c term ty =
      let temp = !quant_map in
      quant_map := !fun_quant_map;
      let data = self#build_term_logic_coerce env l_c term ty in
      quant_map := temp;
      data

    method  build_call_unop =
      fun env unop term ty ->
        let temp = !quant_map in
        quant_map := !fun_quant_map;
        let data = self#build_term_unop env unop term ty in
        quant_map := temp;
        data

    method build_call env id _ func formals =
      let data =
        Rpp_predicate_visitor.check_function_side_effect func env.loc_axiom
      in
      let pointers = Rpp_predicate_visitor.clone_killer
          ((List.fold_right(fun (_,x) acc -> x ::acc) data.assigns_p [])
           @ (List.fold_right(fun (_,x) acc -> x ::acc) data.from_p []))
          []
          (Cil_datatype.Varinfo.equal)
      in
      let new_terms =
        typer env.self_axiom#behavior env.loc_axiom formals env func
      in
      let vis = new Rpp_predicate_visitor.separate_checker
        env.loc_axiom !formal_pointer_check id
      in
      let visitor =
        Visitor.visitFramacTerm vis
      in
      List.iter(fun x -> let _ = visitor x in ()) formals;
      formal_pointer_check := !formal_pointer_check@new_terms;

      (*Generation of terms for the assert predicate and the copie information*)
      let func_type_return =
        Rpp_predicate_visitor.function_return_type func env.self_axiom#behavior env.loc_axiom
      in

      (*Generation of the term node for the axiome predicate*)
      let num_name =
        string_of_int (Rpp_options.Counting_return_formals_verification_function_axiom.next ())
      in
      let name =
        String.concat "_" ["return_variable_relational";num_name]
      in
      let name =
        make_unique_name name !quant_map
      in
      let logic_var_axiome =
        match func_type_return with
        | TVoid(_) -> None
        | x ->
          let new_type =
            Rpp_predicate_visitor.get_typ_in_current_project
              x (env.self_axiom#behavior) (env.loc_axiom)
          in
          Some(Cil_const.make_logic_var_quant name (Ctype(new_type)))
      in
      let term_node_result =
        match logic_var_axiome with
        | None -> None
        | Some x -> Some (TLval(TVar(x),TNoOffset))
      in
      let param_from = make_new_global env id data.froms "_pre" in
      let param_assigns_post = make_new_global env id data.assigns "_post" in
      let map_param_from = make_map data.froms param_from in
      let map_param_assigns_post = make_map data.assigns param_assigns_post in
      let param_from_p = make_new_global2 env id data.from_p "" in
      let map_aux = make_map2 data.from_p param_from_p in
      let param_assigns_p = make_global_filter env id data.assigns_p "" map_aux in
      let map_param_from_p = make_map2 data.from_p param_from_p in
      let map_param_assigns_post_p = make_map2 data.assigns_p param_assigns_p in
      let name =
        String.concat "_" [func.vname;"acsl";
                           string_of_int (Rpp_options.Counting_axiome.get () + 1)]
      in
      let kf =
        Globals.Functions.get func
      in
      let (logic_information,_,_,_,_) =
        try (Hashtbl.find predicate_info name ) with
          Not_found ->
          make_logic_information env name
            kf func_type_return data
            pointers predicate_info
      in
      let param_pointer =
        Rpp_predicate_visitor.clone_killer
          (param_assigns_p@param_from_p) [] Cil_datatype.Logic_var.equal
      in
      let globals_terms =
        List.map (fun x ->
            let term_node = TLval(TVar(x),TNoOffset) in
            {term_node = term_node;
             term_loc = env.pos_axiom;
             term_type = x.lv_type;
             term_name = []}
          ) (param_from@param_assigns_post@param_pointer)
      in
      let (term_result_add,logic_result_add) =
        match term_node_result,logic_var_axiome with
        | None,None -> [],[]
        | Some x,Some y ->  [{term_node = x;
                              term_loc = env.pos_axiom;
                              term_type = y.lv_type;
                              term_name = []}] ,[y]
        | _ -> assert false
      in
      let labels = make_labels logic_information id in
      let new_pred_axiome =
        Papp(logic_information,labels,new_terms@globals_terms@term_result_add)
      in
      let separated_terms =
        make_separate_term data
      in
      let formals =
        Kernel_function.get_formals kf
      in
      let formals_map = Cil_datatype.Logic_var.Map.empty in
      let formals_map =
        List.fold_left2 (fun x y z ->
            Cil_datatype.Logic_var.Map.add (Cil.cvar_to_lvar y) z x
          ) formals_map formals new_terms
      in
      let sep = {
        separated_terms_axiom = separated_terms;
        formal_binder = formals_map;
        id_sep = id;
      }
      in
      call_data_separated := sep :: !call_data_separated;
      let data = {
        id = id;
        logi_def_formals = ((List.rev param_from) @ (List.rev param_assigns_post)
                            @ param_pointer @ logic_result_add);
        from_map_logic =  map_param_from;
        assigns_map_logic =  map_param_assigns_post;
        from_map_p_logic =  map_param_from_p ;
        assigns_map_p_logic =  map_param_assigns_post_p;
        predicate_axiom =  new_pred_axiome;
        return_logic =  logic_var_axiome;
        predicate_labels = labels;
      }
      in
      call_side_effect_data := data :: !call_side_effect_data;
      data

    method  build_callset _ call_data =
      let new_quant =
        List.fold_left(fun acc data ->
            (data.logi_def_formals)@acc )[] call_data
      in
      let new_pred_axiom =
        List.map(fun data ->
            data.predicate_axiom
          ) call_data
      in
      let labels =
        List.fold_left
          (fun acc data -> data.predicate_labels @ acc)
          [] call_data
      in
      (new_quant,labels,new_pred_axiom)

    method  build_term_app_call env _ funct formals _ =
      let new_terms =
        typer env.self_axiom#behavior env.loc_axiom formals env funct
      in
      (*Generation of the term node for the axiome predicate*)
      let name = String.concat "_" [funct.vname;"acsl_pure";
                                    string_of_int (Rpp_options.Counting_axiome.get () + 1)]
      in
      let (logic_information,_) =
        try (Hashtbl.find predicate_info_pure name) with
          Not_found ->
          (let new_logic_information = Cil_const.make_logic_info name in
           let kf = Globals.Functions.get funct in
           let current_kf = Cil.get_kernel_function env.self_axiom#behavior kf in
           new_logic_information.l_profile <-
             List.map (fun x ->
                 let typ = match x.vtype with
                   | t ->
                     Ctype (
                       Rpp_predicate_visitor.get_typ_in_current_project
                         t env.self_axiom#behavior env.loc_axiom)
                 in
                 Cil_const.make_logic_var_formal (x.vname) typ)
               (Globals.Functions.get_params current_kf);
           let return = Kernel_function.get_return_type current_kf in
           let typ = match return  with
             | TVoid _ ->
               Rpp_options.Self.fatal ~source:env.loc_axiom
                 "Function %s have a unsupported return type void"
                 (funct.vname)
             | t ->   Ctype (
                 Rpp_predicate_visitor.get_typ_in_current_project
                   t env.self_axiom#behavior env.loc_axiom)
           in
           new_logic_information.l_type <- Some (typ);
           new_logic_information.l_var_info.lv_type <- typ;
           Hashtbl.add predicate_info_pure name (new_logic_information, current_kf);
           (new_logic_information,current_kf)
          ) in
      let term_node_axiome = Tapp(logic_information,[],new_terms) in
      let return_type =
        match logic_information.l_type with
        | Some t -> t
        | None -> assert false
      in
      let new_term_axiome =
        Logic_const.term
          ~loc:(env.pos_axiom)
          term_node_axiome
          (return_type)
      in
      new_term_axiome

    method  build_term_binop_at env binop term1_assert term2_assert ty _ =
      self#build_term_binop env binop term1_assert term2_assert ty

    method  build_term_logic_coerce_at env ty term_assert typ _ =
      self#build_term_logic_coerce env ty term_assert typ

    method  build_term_const_at env logic_const ty _ =
      self#build_term_const env logic_const ty

    method  build_term_valvar_at env logic_var new_off ty label =
      let origine =
        match logic_var.lv_origin with
        | Some(var) -> (Some var,None)
        | None ->
          let new_logic_var =
            (try (Cil_datatype.Logic_var.Map.find logic_var !quant_map) with
               Not_found -> Rpp_options.Self.abort ~source:env.loc_axiom
                              "Unknow logical variable %s in \\at"
                              logic_var.lv_name)
          in (None,Some(new_logic_var))
      in
      match Str.bounded_split (Str.regexp "_") label 2 with
      | "Pre":: id :: [] ->
        let new_lv_axiom =
          match origine with
          | None ,Some x -> x
          | Some v,None ->
            let data =
              try List.find (fun data -> String.equal id data.id) !call_side_effect_data with
              | Not_found ->
                Rpp_options.Self.fatal ~source:env.loc_axiom
                  "The identifier %s is suppose to existe according to \
                   the parser, but cannot be found" id
            in
            let new_lv_axiom =
              try Cil_datatype.Varinfo.Map.find v (data.from_map_p_logic) with
              | Not_found -> Rpp_options.Self.abort ~source:env.loc_axiom
                               "The pointer %a is suppose not \
                                used in the assignement of an over variable"
                               Printer.pp_varinfo v
            in
            new_lv_axiom
          | _ -> assert false
        in
        let typ = match ty with
          | Ctype t -> Ctype(Rpp_predicate_visitor.get_typ_in_current_project
                               t (env.self_axiom#behavior) (env.loc_axiom))
          | Linteger -> Linteger
          | Lreal -> Lreal
          | _ -> Rpp_options.Self.fatal ~source:env.loc_axiom
                   "Match bad terme type in term variable"
        in
        let term_node_axiom = TLval(TVar(new_lv_axiom),new_off) in
        let axiom_term =
          Logic_const.term
            ~loc:env.pos_axiom
            term_node_axiom
            typ
        in
        axiom_term

      | "Post" :: id :: [] ->
        let new_lv_axiom = match origine with
          | None ,Some x -> x
          | Some v, None ->
            let data =
              try List.find (fun data -> String.equal id data.id) !call_side_effect_data with
              | Not_found ->
                Rpp_options.Self.fatal ~source:env.loc_axiom
                  "The identifier %s is suppose to existe according to \
                   the parser, but cannot be found" id

            in
            let new_lv_axiom =
              try Cil_datatype.Varinfo.Map.find v (data.assigns_map_p_logic) with
              | Not_found -> Rpp_options.Self.abort ~source:env.loc_axiom
                               "The pointer %a is suppose not to be assigned"
                               Printer.pp_varinfo v
            in
            new_lv_axiom
          | _ -> assert false
        in
        let typ = match ty with
          | Ctype t -> Ctype(Rpp_predicate_visitor.get_typ_in_current_project
                               t (env.self_axiom#behavior) (env.loc_axiom))
          | Linteger -> Linteger
          | Lreal -> Lreal
          | _ -> Rpp_options.Self.fatal ~source:env.loc_axiom
                   "Match bad terme type in term variable"
        in
        let term_node_axiome = TLval(TVar(new_lv_axiom),new_off) in
        let axiom_term =
          Logic_const.term
            ~loc:env.pos_axiom
            term_node_axiome
            typ
        in
        axiom_term

      | _ -> Rpp_options.Self.fatal ~source:env.loc_axiom
               "Something went wrong during parsing: \\at have an unsupported label %s" label

    method  build_Toffset_at env off _ =
      self#build_Toffset env off


    method build_term_binop env binop term1_axiome term2_axiome ty =
      let new_ty = match ty with
        | Ctype t ->
          Ctype(Rpp_predicate_visitor.get_typ_in_current_project
                  t (env.self_axiom#behavior) (env.loc_axiom))
        | Linteger -> Linteger
        | Lreal -> Lreal
        | _ ->
          Rpp_options.Self.fatal ~source:env.loc_axiom "Match bad terme type in logic corece"
      in
      let new_term_axiome =
        Logic_const.term
          ~loc:(env.pos_axiom)
          (TBinOp(binop,term1_axiome,term2_axiome))
          (new_ty)
      in
      new_term_axiome

    method  build_term_logic_coerce env ty term_axiome typ =
      let new_ty = match ty with
        | Ctype t ->
          Ctype(Rpp_predicate_visitor.get_typ_in_current_project
                  t (env.self_axiom#behavior) (env.loc_axiom))
        | Linteger -> Linteger
        | Lreal -> Lreal
        | _ ->
          Rpp_options.Self.fatal ~source:env.loc_axiom "Match bad terme type in logic corece"
      in
      let new_typ = match typ with
        | Ctype t ->
          Ctype(Rpp_predicate_visitor.get_typ_in_current_project
                  t (env.self_axiom#behavior) (env.loc_axiom))
        | Linteger -> Linteger
        | Lreal -> Lreal
        | _ -> Rpp_options.Self.fatal ~source:env.loc_axiom "Match bad terme type in logic corece"
      in
      let new_term_axiome =
        Logic_const.term
          ~loc:(env.pos_axiom)
          (TLogic_coerce(new_ty,term_axiome))
          (new_typ)
      in
      new_term_axiome

    method  build_term_const env logic_const _ =
      match logic_const with
      | Integer(int,x) ->
        let new_term =
          Logic_const.term ~loc:(env.pos_axiom) (TConst (Integer (int,x))) Linteger
        in
        new_term
      | LReal(l_r) ->
        let new_term =
          Logic_const.term ~loc:(env.pos_axiom) (TConst (LReal l_r)) Lreal
        in
        new_term
      | _ -> Rpp_options.Self.fatal ~source:env.loc_axiom "Match bad term constant"

    method build_Toffset env offset =
      match offset with
      | TNoOffset -> TNoOffset
      | TField(field_info,field_offset) ->
        let new_field_info =
          Cil.get_fieldinfo (env.self_axiom#behavior) field_info
        in
        let new_field_offset =
          self#build_Toffset env field_offset
        in
        TField(new_field_info,new_field_offset)
      | TModel(_,_) -> (** access to a model field. *)
        Rpp_options.Self.abort ~source:env.loc_axiom
          "Error in pedicate: access to a model field are not supported"
      (** index. Note that a range is denoted by [TIndex(Trange(i1,i2),ofs)] *)
      | TIndex(term_index,index_offset) ->
        let new_term_index =
          self#visit_term env term_index
        in
        let new_index_offset =
          self#build_Toffset env index_offset
        in
        TIndex(new_term_index,new_index_offset)

    method  build_term_valvar env logic_var new_off ty =
      let new_logic_var =
        try Cil_datatype.Logic_var.Map.find logic_var !quant_map with
          Not_found ->  Rpp_options.Self.abort ~source:env.loc_axiom
                          "Error in predicate: terme %s has no quantifiers"
                          (logic_var.lv_name)
      in
      match new_off with
      | TNoOffset ->
        let term_node_axiome =
          TLval(TVar(new_logic_var),new_off)
        in
        let axiome_term =
          Logic_const.term
            ~loc:(env.pos_axiom)
            term_node_axiome
            (new_logic_var.lv_type)
        in
        axiome_term
      | _ ->
        let new_ty = match ty with
          | Ctype t ->
            Ctype(Rpp_predicate_visitor.get_typ_in_current_project
                    t (env.self_axiom#behavior) (env.loc_axiom))
          | Linteger -> Linteger
          | Lreal -> Lreal
          | _ ->
            Rpp_options.Self.fatal ~source:env.loc_axiom "Match bad terme type in term variable"
        in
        let term_node_axiome =
          TLval(TVar(new_logic_var),new_off)
        in
        let axiome_term =
          Logic_const.term
            ~loc:(env.pos_axiom)
            term_node_axiome
            new_ty
        in
        axiome_term

    method  build_term_app_result env id _ =
      let data =
        try List.find (fun data -> String.equal id  data.id) !call_side_effect_data with
        | Not_found ->
          Rpp_options.Self.fatal ~source:env.loc_axiom
            "The identifier %s is suppose to existe according to \
             the parser, but cannot be found" id
      in
      let l_v_axiome =
        match data.return_logic with
        | None -> Rpp_options.Self.abort ~source:env.loc_axiom
                    "Id %s refer to a function with not return variable" id
        | Some x -> x
      in
      let term_node_axiome =
        TLval(TVar(l_v_axiome),TNoOffset)
      in
      let axiome_term =
        Logic_const.term
          ~loc:(env.pos_axiom)
          term_node_axiome
          (l_v_axiome.lv_type)
      in
      axiome_term

    method  build_term_at_var env l_v new_off s _ =
      let v =
        match l_v.lv_origin with
        | Some(var) -> var
        | None ->
          match Cil_datatype.Logic_var.Map.find l_v !quant_map with
          | exception Not_found -> Rpp_options.Self.abort ~source:env.loc_axiom
                                     "Unknow logical vaiable %a in \\at built-in"
                                     Printer.pp_logic_var l_v
          | _ -> Rpp_options.Self.abort ~source:env.loc_axiom
                   "Logical vaiable %a in \\at built-in is a formal variable, \
                    it can not be modified"
                   Printer.pp_logic_var l_v
      in
      match Str.bounded_split (Str.regexp "_") s 2 with
      | "Pre":: id :: [] ->
        let data =
          try List.find (fun data -> String.equal id data.id) !call_side_effect_data with
          | Not_found ->
            Rpp_options.Self.fatal ~source:env.loc_axiom
              "The identifier %s is suppose to existe according to \
               the parser, but cannot be found" id
        in
        let new_lv_axiom =
          try Cil_datatype.Varinfo.Map.find v (data.from_map_logic) with
          | Not_found -> Rpp_options.Self.abort ~source:env.loc_axiom
                           "The variable %a is suppose not \
                            used in the assignement of an over variable"
                           Printer.pp_varinfo v
        in
        let term_node_axiom = TLval(TVar(new_lv_axiom),new_off) in
        let axiom_term =
          Logic_const.term
            ~loc:(env.pos_axiom)
            term_node_axiom
            (new_lv_axiom.lv_type)
        in
        axiom_term

      | "Post" :: id :: [] ->
        let data =
          try List.find (fun data -> String.equal id data.id) !call_side_effect_data with
          | Not_found ->
            Rpp_options.Self.fatal ~source:env.loc_axiom
              "The identifier %s is suppose to existe according to \
               the parser, but cannot be found" id
        in
        let new_lv_axiom =
          try Cil_datatype.Varinfo.Map.find v (data.assigns_map_logic) with
          | Not_found -> Rpp_options.Self.abort ~source:env.loc_axiom
                           "The variable %a is suppose not to be assigned"
                           Printer.pp_varinfo v
        in
        let term_node_axiom = TLval(TVar(new_lv_axiom),new_off) in
        let axiom_term =
          Logic_const.term
            ~loc:(env.pos_axiom)
            term_node_axiom
            (new_lv_axiom.lv_type)
        in
        axiom_term

      | _ -> Rpp_options.Self.fatal ~source:env.loc_axiom
               "Something went wrong during parsing: \\at have an unsupported label %s" s

    method  build_term_at_mem env t s ty =
      match Str.bounded_split (Str.regexp "_") s 2 with
      | "Pre":: id :: [] ->
        let typ = match ty with
          | Ctype t -> Ctype(Rpp_predicate_visitor.get_typ_in_current_project
                               t (env.self_axiom#behavior) (env.loc_axiom))
          | Linteger -> Linteger
          | Lreal -> Lreal
          | _ -> Rpp_options.Self.fatal ~source:env.loc_axiom
                   "Match bad terme type in term variable"
        in
        let the_terme_node_axiome = TLval(TMem(t),TNoOffset) in
        let axiome_term =
          Logic_const.term
            ~loc:env.pos_axiom
            the_terme_node_axiome
            typ
        in
        let name_label = String.concat "_" ["pre";id] in
        let term_node_axiom = Tat(axiome_term,FormalLabel(name_label)) in
        let axiome_term =
          Logic_const.term
            ~loc:env.pos_axiom
            term_node_axiom
            typ
        in
        axiome_term

      | "Post" :: id :: [] ->
        let typ = match ty with
          | Ctype t -> Ctype(Rpp_predicate_visitor.get_typ_in_current_project
                               t (env.self_axiom#behavior) (env.loc_axiom))
          | Linteger -> Linteger
          | Lreal -> Lreal
          | _ -> Rpp_options.Self.fatal ~source:env.loc_axiom
                   "Match bad terme type in term variable"
        in
        let the_terme_node_axiome = TLval(TMem(t),TNoOffset) in
        let axiom_term =
          Logic_const.term
            ~loc:env.pos_axiom
            the_terme_node_axiome
            typ
        in
        let name_label = String.concat "_" ["post";id] in
        let term_node_axiom = Tat(axiom_term,FormalLabel(name_label)) in
        let axiome_term =
          Logic_const.term
            ~loc:env.pos_axiom
            term_node_axiom
            typ
        in
        axiome_term

      | _ -> Rpp_options.Self.fatal ~source:env.loc_axiom
               "Something went wrong during parsing: \\at have an unsupported label %s" s

    method  build_term_unop env op  term_axiome ty =
      let new_ty = match ty with
        | Ctype t ->
          Ctype(Rpp_predicate_visitor.get_typ_in_current_project
                  t (env.self_axiom#behavior) (env.loc_axiom))
        | Linteger -> Linteger
        | Lreal -> Lreal
        | _ ->
          Rpp_options.Self.fatal ~source:env.loc_axiom "Match bad terme type in logic corece"
      in
      let term_node_axiome =
        TUnOp(op,term_axiome)
      in
      let axiome_term =
        Logic_const.term
          ~loc:(env.pos_axiom)
          term_node_axiome
          (new_ty)
      in
      axiome_term

    method  build_term_range env term1 term2 _ =
      let (term1_axiom,term2_axiom)=
        match term1,term2 with
        | None,None -> (None,None)
        | Some(term1_axiome),None -> (Some term1_axiome,None)
        | None, Some(term2_axiom) -> (None,Some term2_axiom)
        | Some(term1_axiom),Some(term2_axiom) ->
          (Some term1_axiom,Some term2_axiom)
      in
      let axiom_term =
        Logic_const.trange
          ~loc:(env.pos_axiom)
          (term1_axiom,term2_axiom)
      in
      axiom_term

    method  build_term_app env logic_info t_list ty =
      let new_logicinfo =
        Cil.get_logic_info env.self_axiom#behavior logic_info
      in
      let new_ty = match ty with
        | Ctype t ->
          Ctype(Rpp_predicate_visitor.get_typ_in_current_project
                  t (env.self_axiom#behavior) (env.loc_axiom))
        | Linteger -> Linteger
        | Lreal -> Lreal
        | _ ->
          Rpp_options.Self.fatal ~source:env.loc_axiom "Match bad terme type in logic corece"
      in
      let term_node_axiom =
        Tapp(new_logicinfo,[],t_list)
      in
      let axiom_term =
        Logic_const.term
          ~loc:(env.pos_axiom)
          term_node_axiom
          new_ty
      in
      axiom_term

    method  build_predicate_rel env rel t1_axiom t2_axiom =
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = Prel(rel,t1_axiom, t2_axiom);
      }
      in
      new_axiome_predicate

    method  build_predicate_false env =
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = Pfalse;
      }
      in
      new_axiome_predicate

    method  build_predicate_true env =
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = Pfalse;
      }
      in
      new_axiome_predicate

    method  build_predicate_and env pred1_axiome pred2_axiome =
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = Pand(pred1_axiome,pred2_axiome);
      }
      in
      new_axiome_predicate

    method  build_predicate_or env pred1_axiome pred2_axiome =
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = Por(pred1_axiome,pred2_axiome);
      }
      in
      new_axiome_predicate

    method  build_predicate_xor env pred1_axiome pred2_axiome =
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = Pxor(pred1_axiome,pred2_axiome);
      }
      in
      new_axiome_predicate

    method  build_predicate_implies env pred1_axiome pred2_axiome =
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = Pimplies(pred1_axiome,pred2_axiome);
      }
      in
      new_axiome_predicate

    method  build_predicate_iff env pred1_axiome pred2_axiome =
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = Piff(pred1_axiome,pred2_axiome);
      }
      in
      new_axiome_predicate

    method  build_predicate_not env pred_axiom =
      let new_axiom_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = Pnot(pred_axiom);
      }
      in
      new_axiom_predicate

    method build_predicate_label env l =
      let new_labels =
        begin
          fun l ->
            List.map(
              fun x ->
                match x with
                | FormalLabel(id) ->
                  (FormalLabel(
                      id_convert_axiom id (env.loc_axiom)
                        (!call_side_effect_data)))
                | _ -> assert false) l
        end
      in
      new_labels l

    method  build_predicate_app env logic_info l_axiom t_list =
      let new_logicinfo =
        Cil.get_logic_info env.self_axiom#behavior logic_info
      in
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = Papp(new_logicinfo,l_axiom,t_list);
      }
      in
      new_axiome_predicate

    method build_predicate_quan env quan =
      List.iter (fun x ->
          match x.lv_type with
          | Ctype(t) ->
            let new_t =
              Rpp_predicate_visitor.get_typ_in_current_project
                t env.self_axiom#behavior env.loc_axiom
            in
            let new_logic_var =
              Cil_const.make_logic_var_quant
                (x.lv_name) (Ctype(new_t))
            in
            begin
              match Cil_datatype.Logic_var.Map.find x !quant_map with
              | exception Not_found ->
                quant_map := Cil_datatype.Logic_var.Map.add x new_logic_var !quant_map
              | _ -> Rpp_options.Self.abort ~source:env.loc_axiom
                       "Quantified logic variable %a already exists" Printer.pp_logic_var x
            end

          | Linteger ->
            Rpp_options.Self.abort ~source:env.loc_axiom
              "Error in pedicate: A C function can not have a mathematical integer as parameter:@. @[%a@]@."
              Printer.pp_logic_var x
          | Lreal ->
            Rpp_options.Self.abort ~source:env.loc_axiom
              "Error in pedicate: A C function can not have a mathematical real as parameter:@. @[%a@]@."
              Printer.pp_logic_var x
          | Ltype _ ->
            Rpp_options.Self.abort ~source:env.loc_axiom
              "Error in pedicate: A C function can not have a logic type as parameter:@. @[%a@]@."
              Printer.pp_logic_var x
          | Lvar _ ->
            Rpp_options.Self.abort ~source:env.loc_axiom
              "Error in pedicate: A C function can not have a logic type variable as parameter:@. @[%a@]@."
              Printer.pp_logic_var x
          | Larrow _ ->
            Rpp_options.Self.abort ~source:env.loc_axiom
              "Error in predicate: A C function can not have a logic function type as parameter:@. @[%a@]@."
              Printer.pp_logic_var x)
        quan ;
      quan

    method build_predicate_forall env quan pred =
      let new_quant = List.map(fun x ->
          let new_logic_var =
            (try (Cil_datatype.Logic_var.Map.find x !quant_map) with
             | Not_found -> Rpp_options.Self.fatal ~source:env.loc_axiom
                              "Quantified logic variable %a is not in the new \
                               quantified logic varible" Printer.pp_logic_var x

             | _ -> assert false)
          in
          quant_map :=Cil_datatype.Logic_var.Map.remove x !quant_map;
          new_logic_var) quan
      in
      let new_axiom_predicate_content =
        Pforall(new_quant,pred)
      in
      let new_axiom_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = new_axiom_predicate_content;
      }
      in
      new_axiom_predicate

    method build_predicate_exists env quan pred =
      let new_quant = List.map(fun x ->
          let new_logic_var =
            (try (Cil_datatype.Logic_var.Map.find x !quant_map) with
             | Not_found -> Rpp_options.Self.fatal ~source:env.loc_axiom
                              "Quantified logic variable %a is not in the new \
                               quantified logic varible" Printer.pp_logic_var x

             | _ -> assert false)
          in
          quant_map := Cil_datatype.Logic_var.Map.remove x !quant_map;
          new_logic_var) quan
      in
      let new_axiom_predicate_content =
        Pexists(new_quant,pred)
      in
      let new_axiom_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = new_axiom_predicate_content;
      }
      in
      new_axiom_predicate

    method build_rpp_quan env quan =
      List.iter (fun x ->
          match x.lv_type with
          | Ctype(t) ->
            let new_t =
              Rpp_predicate_visitor.get_typ_in_current_project
                t env.self_axiom#behavior env.loc_axiom
            in
            let new_logic_var =
              Cil_const.make_logic_var_quant
                (x.lv_name) (Ctype(new_t))
            in
            quant_map := Cil_datatype.Logic_var.Map.add x new_logic_var !quant_map;
            fun_quant_map := Cil_datatype.Logic_var.Map.add x new_logic_var !fun_quant_map

          | Linteger ->
            Rpp_options.Self.abort ~source:env.loc_axiom
              "Error in pedicate: A C function can not have a mathematical integer as parameter"
          | Lreal ->
            Rpp_options.Self.abort ~source:env.loc_axiom
              "Error in pedicate: A C function can not have a mathematical real as parameter"
          | Ltype _ ->
            Rpp_options.Self.abort ~source:env.loc_axiom
              "Error in pedicate: A C function can not have a logic type as parameter"
          | Lvar _ ->
            Rpp_options.Self.abort ~source:env.loc_axiom
              "Error in pedicate: A C function can not have a logic type variable as parameter"
          | Larrow _ ->
            Rpp_options.Self.abort ~source:env.loc_axiom
              "Error in predicate: A C function can not have a logic function type as parameter")
        quan ;
      let new_quan_local  = List.map(fun x ->
          let new_logic_var =
            (try (Cil_datatype.Logic_var.Map.find x !quant_map) with
             | Not_found -> Rpp_options.Self.fatal ~source:env.loc_axiom
                              "Quantified logic variable %a is not in the new \
                               quantified logic varible" Printer.pp_logic_var x

             | _ -> assert false)
          in
          new_logic_var) quan
      in
      new_quan_local

    method build_rpp_predicate_forall env quan new_axiome_predicate =
      let new_axiome_predicate_content =
        Pforall(quan,new_axiome_predicate)
      in
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = new_axiome_predicate_content;}
      in
      let logic =
        {predicate_info= predicate_info}
      in
      let logic_pure =
        {predicate_info_pure= predicate_info_pure}
      in
      (new_axiome_predicate,[],logic,logic_pure)

    method build_rpp_predicate_forall_callset env quan (new_quant,new_labels,new_pred_axiom) new_axiome_predicate =
      let new_pred_axiom =
        List.fold_left(fun acc predicate_axiom ->
            let pred_1_named ={
              pred_name = [];
              pred_loc= env.pos_axiom;
              pred_content= predicate_axiom}
            in
            let pred_node =
              Pimplies(pred_1_named,acc)
            in
            {pred_name = [];
             pred_loc= env.pos_axiom;
             pred_content= pred_node}

          ) new_axiome_predicate new_pred_axiom
      in
      let pred =
        make_separate
          env !call_data_separated !call_side_effect_data
      in
      let new_pred_axiom =
        match pred with
        | None -> new_pred_axiom
        | Some x ->
          let pred_node =
            Pimplies(x,new_pred_axiom)
          in
          {pred_name = [];
           pred_loc= env.pos_axiom;
           pred_content= pred_node}
      in
      let new_axiome_predicate_content =
        Pforall(quan@(new_quant),new_pred_axiom)
      in
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = new_axiome_predicate_content;
      }
      in
      let logic =
        {predicate_info= predicate_info}
      in
      let logic_pure =
        {predicate_info_pure= predicate_info_pure}
      in
      (new_axiome_predicate,new_labels,logic,logic_pure)

    method build_rpp_predicate_implies_callset env (new_quant,new_labels,new_pred_axiom) new_axiome_predicate =
      let new_pred_axiom =
        List.fold_left(fun acc predicate_axiom ->
            let pred_1_named ={
              pred_name = [];
              pred_loc= env.pos_axiom;
              pred_content= predicate_axiom}
            in
            let pred_node =
              Pimplies(pred_1_named,acc)
            in
            {pred_name = [];
             pred_loc= env.pos_axiom;
             pred_content= pred_node}

          ) new_axiome_predicate new_pred_axiom
      in
      let pred =
        make_separate
          env !call_data_separated !call_side_effect_data
      in
      let new_pred_axiom =
        match pred with
        | None -> new_pred_axiom
        | Some x ->
          let pred_node =
            Pimplies(x,new_pred_axiom)
          in
          {pred_name = [];
           pred_loc= env.pos_axiom;
           pred_content= pred_node}
      in
      let new_axiome_predicate_content =
        Pforall(new_quant,new_pred_axiom)
      in
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = new_axiome_predicate_content;
      }
      in
      let logic =
        {predicate_info= predicate_info}
      in
      let logic_pure =
        {predicate_info_pure= predicate_info_pure}
      in
      (new_axiome_predicate,new_labels,logic,logic_pure)

    method build_rpp_predicate_implies _ new_axiome_predicate =
      let logic =
        {predicate_info= predicate_info}
      in
      let logic_pure =
        {predicate_info_pure= predicate_info_pure}
      in
      (new_axiome_predicate,[],logic,logic_pure)

    method  build_rpp_predicate_rel env rel t1_axiome t2_axiome =
      let new_axiome_predicate ={
        pred_name = [];
        pred_loc = env.pos_axiom;
        pred_content = Prel(rel,t1_axiome, t2_axiome);
      }
      in
      let logic =
        {predicate_info= predicate_info}
      in
      let logic_pure =
        {predicate_info_pure= predicate_info_pure}
      in
      (new_axiome_predicate,[],logic,logic_pure)

  end
  in
  let (loc,_)=predicate.pred_loc in
  let env = {
    loc_axiom = loc;
    pos_axiom = predicate.pred_loc;
    self_axiom = self_behavior;
  }
  in
  v#visit_rpp_predicate env predicate
