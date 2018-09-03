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

(**
   Function returning the type refering to the new project
*)
let rec get_typ_in_current_project t self loc=
  match t with
  | TVoid(_) -> t
  | TInt(_) -> t
  | TFloat(_) -> t
  | TPtr(t,a) -> let new_t = get_typ_in_current_project t self loc in TPtr(new_t,a)
  | TArray(t,e,b,a) -> let new_t = get_typ_in_current_project t self loc in TArray(new_t,e,b,a)
  | TFun(_) ->  Rpp_options.Self.abort ~source:loc
                  "Error in predicate: Function types are not supported yet"
  | TNamed (t,a) -> let new_c = Cil.get_typeinfo self t in TNamed(new_c,a)
  | TComp (c,b,a) ->let new_c = Cil.get_compinfo self c in TComp(new_c,b,a)
  | TEnum (e,a) -> let new_e = Cil.get_enuminfo self e in TEnum(new_e,a)
  | TBuiltin_va_list(_) -> t

let sorter l =
  List.fold_right (fun (x,y) (l1, l2) -> (x::l1, y::l2)) l ([],[])

let id_convert identifier loc call_side_effect_data=
  match Str.bounded_split (Str.regexp "_") identifier 2 with
  | "Pre":: id :: []  ->
    (match List.find (fun data -> String.equal id data.id_call )
             call_side_effect_data  with
    | exception Not_found ->
      Rpp_options.Self.abort ~source:loc "The id %s is unknown in this clause" id
    | _ -> Pre)
  |  "Post" :: id :: [] ->
    (match List.find (fun data -> String.equal id data.id_call)
             call_side_effect_data  with
    | exception Not_found ->
      Rpp_options.Self.abort ~source:loc "The id %s is unknown in this clause" id
    | _ ->  Here)
  | _ -> Rpp_options.Self.abort ~source:loc "Expect label of the forme Pre_id or Post_id:@ @[%s@] @."
           identifier

(**
     Function making "Set" stmt for a varinfo set to an expression
*)
let make_stmt_from_exp exp loc =
  let rec aux acc1 acc2 e =
    match e with
    | [] -> (acc1,acc2)
    | None :: q -> aux acc1 acc2 q
    | Some(e,varinfo,_) :: q ->
      let return_lval =
        (Var(varinfo),NoOffset)
      in
      let new_stmt =
        Cil.mkStmt ~valid_sid:true (Instr(Set(return_lval,e,loc)))
      in
      aux (new_stmt :: acc1) (varinfo :: acc2) q
  in
  aux [] [] exp

(**
   Function returning the type return by a function
*)
let function_return_type funct =
  match funct.vtype with
  | TFun(t,_,_,_) -> get_typ_in_current_project t
  | _ -> assert false

(**
   Function making a copie of the local variable of copie funct for new_funct
*)
let make_local new_funct copie_funct i self loc inlining =
  let rec aux locals i acc =
    match locals with
    | [] -> acc
    | h :: q ->
      let name =
        String.concat "_" [h.vname; string_of_int i ]
      in
      let varinfo =
        Cil.makeLocalVar new_funct name (get_typ_in_current_project h.vtype self loc)
      in
      varinfo.vdefined <- h.vdefined;
      aux q i (varinfo:: acc)
  in
  match inlining with
  (*TODO return empty list id inlining is equals to 0. The term inliner will not work. Wait
    before merge request for seprated generation is merged.*)
  | 0 -> copie_funct.slocals
  | _ ->  List.rev(aux copie_funct.slocals i [])


type side_effect = {
  mutable assigns: Cil_types.varinfo list;
  mutable froms: Cil_types.varinfo list;
  mutable assigns_p: (Cil_types.term * Cil_types.varinfo) list;
  mutable assigns_p_f: (Cil_types.term * Cil_types.varinfo) list;
  mutable from_p: (Cil_types.term * Cil_types.varinfo) list;
  mutable from_p_f: (Cil_types.term * Cil_types.varinfo) list;
}

(**
    Function checking the side effect of a given funct be analyzing the corresponding assigns clauses
*)
let check_function_side_effect funct loc =
  let kf = Globals.Functions.get funct in
  let rec sort_pointer l acc acc_p =
    match l with
    | [] -> (acc, acc_p)
    | h :: q ->
      begin
        match h.term_node with
        | TLval(TMem({term_node =
                        TBinOp(IndexPI,{term_node = TLval(TVar(l_v),TNoOffset)},
                               {term_node = Trange(_,_)})}),TNoOffset)
        | TLval(TMem({term_node = TLval(TVar(l_v),TNoOffset)}),TNoOffset) ->
          begin
            match l_v.lv_origin with
            | Some v ->
              begin
                match  Globals.Vars.find v with
                | exception Not_found -> sort_pointer q acc ((h,v)::acc_p)
                | _ -> sort_pointer q ((h,v)::acc) acc_p
              end
            | None ->  Rpp_options.Self.abort ~source:loc
                         "Not supported parameter in \\assigns \\from \
                          annotation (not varinfo): @. @[%a@] @."
                         Printer.pp_logic_var l_v
          end
        | _ -> Rpp_options.Self.fatal ~source:loc
                 "Something went wrong during verification of assignes definition: \
                  @. @[%a@] @. is not supported."
                 Printer.pp_term h
      end
  in
  let rec check_pointer l =
    match l with
    | [] -> ()
    | {term_node = TLval(TMem({term_node = TLval(TVar(_),TNoOffset)}),TNoOffset)} :: q ->
      check_pointer q
    | {term_node =
         TLval(TMem({term_node =
                       TBinOp(IndexPI,{term_node = TLval(TVar(_),TNoOffset)},
                              {term_node = Trange(_,_)})}),TNoOffset)} :: q ->
      check_pointer q
    | _ -> Rpp_options.Self.abort ~source:loc
             "Not supported definition of pointer \
              assignment in assigns clause:@. @[%a@] @." Printer.pp_term (List.hd l)
  in
  let rec fillter l acc f =
    match l with
    | [] -> acc
    | h :: q -> if (List.exists (f h) acc) then fillter q acc f
      else fillter q (h :: acc) f
  in
  let rec supported_side_effect l acc acc_p =
    match l with
    | [] -> (acc,acc_p)
    | h :: q ->
      begin
        match h.it_content.term_node with
        | TLval(TVar(l_v),TNoOffset)| TLval(TVar(l_v),TField(_,TNoOffset))->
          begin
            match l_v.lv_origin with
            | Some v ->
              begin
                match  Globals.Vars.find v with
                | exception Not_found ->
                  supported_side_effect q acc acc_p
                | _ -> supported_side_effect q (v::acc) acc_p
              end
            | None ->  Rpp_options.Self.abort ~source:loc
                         "Not supported parameter in \\assigns \\from annotation (not varinfo)"
          end
        | TLval(TResult(_),_) -> supported_side_effect q acc acc_p
        | TLval(TMem(_),TNoOffset) -> supported_side_effect q acc ((h.it_content)::acc_p)
        | TLval(TMem(_),_)-> Rpp_options.Self.abort ~source:loc
                               "Not supported paramter in \\assigns \\from annotation (pointer)"
        | _ ->  Rpp_options.Self.abort ~source:loc
                  "Not supported paramter in \\assigns \\from annotation:@. @[%a@] @."
                  Printer.pp_term h.it_content
      end
  in
  let rec sort_assigns_form l acc =
    match l with
    | [] -> acc
    | (_,FromAny) :: _ ->  Rpp_options.Self.abort ~source:loc
                             "The \\call require \\assigns \\from annotations"
    | (assigns,From(l)) :: q ->
      let (ass,ass_p),(froms,froms_p) = acc in
      let new_assigns,new_assigns_p =
        supported_side_effect [assigns] ass ass_p
      in
      let new_from,new_from_p =
        supported_side_effect l froms froms_p
      in
      sort_assigns_form q ((new_assigns,new_assigns_p),(new_from,new_from_p))
  in
  let rec get_assigns_form data acc =
    match data with
    | x :: y  ->
      let data =
        (match x.b_assigns with
         | WritesAny -> Rpp_options.Self.abort ~source:loc
                          "The \\call require \\assigns \\from annotations"
         | Writes([])-> get_assigns_form y acc
         | Writes(l) -> sort_assigns_form l acc )
      in
      get_assigns_form y data
    | [] -> acc
  in
  let behaviours = Annotations.behaviors ~populate:false kf in
  begin
    match behaviours with
    | [] -> Rpp_options.Self.abort ~source:loc
              "The RPP require \\assigns \\from annotations for function %a"
              Printer.pp_fundec (Kernel_function.get_definition kf)
    | _ -> ()
  end;
  let ((a,a_t),(f,f_t)) =
    get_assigns_form behaviours (([],[]),([],[]))
  in

  (*TODO: Put all formal and globales in the side effect if option is activated
    Use a visitor: need to detect local memory access
    Qet all mem acces and say separation*)

  let f1 = Cil_datatype.Varinfo.equal in
  let f2 = Cil_datatype.Term.equal in
  let new_a,new_b =
    fillter a [] f1,fillter f [] f1
  in
  let new_a_t,new_f_t =
    fillter a_t [] f2,fillter f_t [] f2
  in
  check_pointer new_a_t;
  check_pointer new_f_t;
  let new_a_t,new_a_t_f = sort_pointer new_a_t [] [] in
  let new_f_t,new_f_t_f = sort_pointer new_f_t [] [] in
  {
    assigns = new_a;
    froms = new_b;
    assigns_p = new_a_t;
    assigns_p_f = new_a_t_f;
    from_p = new_f_t;
    from_p_f = new_f_t_f;
  }

let pretty_effect_data func data =
  let f y =
    List.map(fun (x,_)-> x) y
  in
  let space = "    " in
  Format.printf "Side effect data for function %a@." Printer.pp_varinfo func;
  Format.printf "%sAssigns variable: %a @." space
    (Pretty_utils.pp_list ~sep:"," ~pre:"[" ~suf:"]" Printer.pp_varinfo)
    data.assigns;
  Format.printf "%sFrom variable: %a @." space
    (Pretty_utils.pp_list ~sep:"," ~pre:"[" ~suf:"]" Printer.pp_varinfo)
    data.froms;
  Format.printf "%sAssigns globale pointer: %a @." space
    (Pretty_utils.pp_list ~sep:"," ~pre:"[" ~suf:"]" Printer.pp_term )
    (f data.assigns_p);
  Format.printf "%sAssigns pointer given as paramter: %a @." space
    (Pretty_utils.pp_list ~sep:"," ~pre:"[" ~suf:"]" Printer.pp_term)
    (f data.assigns_p_f);
  Format.printf "%sFrom globale pointer: %a @." space
    (Pretty_utils.pp_list ~sep:"," ~pre:"[" ~suf:"]" Printer.pp_term)
    (f data.from_p);
  Format.printf "%sFrom pointer given as paramter: %a @." space
    (Pretty_utils.pp_list ~sep:"," ~pre:"[" ~suf:"]" Printer.pp_term)
    (f data.from_p_f)

let rec make_unique_gloable_name ?(acc:int = 0) n formals =
  match List.find(fun x -> String.equal x.vname n) formals with
  | exception Not_found -> n
  | _ -> let new_name = String.concat "_" [n; string_of_int acc ] in
    make_unique_gloable_name ~acc:(acc+1) new_name formals

let make_globale globale id map_ex self loc pos formals num =
  let map = Cil_datatype.Varinfo.Map.empty
  in
  let rec aux global i m acc =
    match global with
    | [] -> (m,acc)
    | h :: q ->
      match Cil_datatype.Varinfo.Map.find h map_ex with
      | exception Not_found ->
        let name = String.concat "_" [h.vname; id ; string_of_int num] in
        let name = make_unique_gloable_name name formals in
        let varinfo =
          Cil.makeGlobalVar
            ~source:true ~temp:false name (get_typ_in_current_project h.vtype self loc)
        in
        varinfo.vdecl <- pos;
        varinfo.vdefined <- true;
        varinfo.vreferenced <- true;
        (*Globals.Vars.add_decl varinfo;*)
        let l_v = Cil.cvar_to_lvar varinfo in
        let m = Cil_datatype.Varinfo.Map.add h l_v m in
        aux q i m (l_v::acc)
      | v ->
        let m = Cil_datatype.Varinfo.Map.add h v m in
        aux q i m (v::acc)
  in
  aux globale id map []

let rec clone_killer l1 acc f=
  match l1 with
  | [] -> acc
  | h :: q -> if (List.exists (f h) acc) then clone_killer q acc f
    else clone_killer q (h :: acc) f

let typer func env formals =
  let args = match func.vtype with
    | TFun (_,l,_,_) ->  Cil.argsToList l
    | _ -> assert false
  in
  List.fold_left2(fun (fq,eq) fh (_,t,_)->
      match fh.term_node with
      | TLval (TVar(l_v),TNoOffset)
      | TLval (TMem({term_node = TLval (TVar(l_v),TNoOffset)}),TNoOffset) ->
        begin
          match l_v.lv_origin with
          | Some x -> (x::fq,None::eq)
          | None -> Rpp_options.Self.fatal ~source:env.loc
                      "Something went wrong:\
                       Logic variable @[%a@] have not originale varinfo."
                      Printer.pp_logic_var l_v
        end
      | _ ->
        let name =
          String.concat "_" ["aux_local_variable";
                             string_of_int (Rpp_options.Counting_aux_local_variable.next())]
        in
        let term_type = match fh.term_type, t with
          | Ctype t ,_-> t
          | Linteger, TInt(_) -> t
          | Linteger, TNamed({ttype = TInt _},_) ->
            get_typ_in_current_project t env.self#behavior env.loc
          | Lreal ,TInt(_) | Lreal , TFloat(_) -> t
          | _,_ ->  Rpp_options.Self.fatal ~source:env.loc
                      "Something went wrong during parsing:@.\
                       Function %s is called with a parameter with type \
                       is not supported:@. @[%a@] @."
                      (func.vname) Printer.pp_term fh
        in
        let assert_varinfo =
          Cil.makeLocalVar env.new_funct name term_type
        in
        let term_to_exp = !(Db.Properties.Interp.term_to_exp) in
        let exp = term_to_exp None fh in
        (assert_varinfo::fq,Some(exp,assert_varinfo,fh)::eq))
    ([],[]) formals args

let inliner env inline_data data globals data_annot num proof =
  Queue.add(fun () ->
      (* Get the body of the function and add it to the wrapper function*)
      let bodie =
        Rpp_generator.do_one_copy
          ~proof:proof
          inline_data.kf  (inline_data.formals) (inline_data.return_option)
          (inline_data.locals) (inline_data.id_option)
          data (inline_data.inlining)
          env.new_funct (env.self) (env.proj) (env.loc,env.loc) data_annot num
      in
      env.new_funct.sbody.blocals <- env.new_funct.sbody.blocals @
                                     inline_data.formal_var @
                                     Extlib.list_of_opt inline_data.return_option;
      env.new_funct.sbody.bstmts <- env.new_funct.sbody.bstmts @ inline_data.formal_exp
                                    @ [(Cil.mkStmt ~valid_sid:true (Block bodie))];
      (*The body include some assert clauses corresponding to requires clauses*)
      (*Copy of require clauses and transformation to assert clause*)
      let behaviours =
        Rpp_generator.do_one_require_copy
          inline_data.kf inline_data.formals
          inline_data.id_option
          data
          env.self env.proj
      in
      let requires =
        Rpp_generator.sort_funbehavior behaviours
      in
      List.iter(fun data ->
          let the_code_annotation =
            Logic_const.new_code_annotation (AAssert ([],(Logic_const.pred_of_id_pred data)))
          in
          Annotations.add_code_annot
            Rpp_options.emitter ~kf:(Globals.Functions.get (env.new_funct.svar))
            (List.hd (bodie.bstmts))
            the_code_annotation
        )requires;

      (*Add the requires clauses to the new kernel function.*)
      let behaviours =
        Rpp_generator.do_one_require_copy
          inline_data.kf inline_data.formals
          inline_data.id_option
          data
          env.self env.proj
      in
      let requires = Rpp_generator.sort_funbehavior behaviours in
      let globals = List.map (
          fun x ->
            match x.lv_origin with
            | None -> Rpp_options.Self.fatal ~source:env.loc
                        "Something went wrong:\
                         Logic variable @[%a@] have not originale varinfo."
                        Printer.pp_logic_var x
            | Some x -> x
        ) globals
      in
      let formal_map =
        inline_data.formal_map
      in
      let vis =
        new Rpp_generator.aux_visitor_3
          env.self#behavior
          ((Kernel_function.get_formals  ((Globals.Functions.get (env.new_funct.svar))))
           @globals)
          (formal_map)
      in
      let new_predicate =
        List.map(fun x ->
            Visitor.visitFramacIdPredicate vis x;
          ) requires
      in
      let funbehs =
        Cil.mk_behavior ~name:"default!" ~requires:new_predicate ()
      in
      Annotations.add_behaviors ~register_children:true
        (Rpp_options.emitter) (Globals.Functions.get (env.new_funct.svar)) ([funbehs]);
    )
    env.self#get_filling_actions

let make_separate env inline_info call_side_effect_data=
  Queue.add(fun () ->
      let separated_terms =
        List.fold_left(fun data i ->
            let terms = List.map
                (fun x -> Rpp_generator.do_one_terms_vis
                    i.kf i.formals i.locals i.id_option
                    call_side_effect_data
                    env.self x)
                i.separated_terms
            in terms @ data
          ) [] (inline_info)
      in
      begin
        match separated_terms with
        | h::_ ->
          let pointer_predicate_separated =
            Pseparated(separated_terms)
          in
          let predicate_name =
            {pred_name = [];pred_loc=h.term_loc; pred_content= pointer_predicate_separated}
          in
          let requires =
            Logic_const.new_predicate predicate_name
          in
          let funbehs =
            Cil.mk_behavior ~name:"default!" ~requires:([requires]) ()
          in
          Annotations.add_behaviors ~register_children:true
            (Rpp_options.emitter) (Globals.Functions.get (env.new_funct.svar)) ([funbehs]);

        | [] ->  ()
      end)
    env.self#get_filling_actions;

  (**
     Visitor for checking there is no memory charing
  *)
class separate_checker l terms id = object(_)
  inherit Visitor.frama_c_inplace

  method! vterm t =
    match t.term_type with
    | Ctype(TPtr _) ->
      List.iter (fun x ->
          match Cil_datatype.Term.equal x t with
          | true ->
            Rpp_options.Self.abort ~source:l
              "Pointer variable %a is assigns or used in trace %s but also in \
               an over trace.@. Memory sharing is not supported yet. Declare a \
               new pointer variable for trace %s" Printer.pp_term x id id;
          | false -> ()) terms; Cil.DoChildren
    | _ -> Cil.DoChildren
end

let predicate_visitor ?(proof=false) predicate new_funct self proj data_annot num =
  let v = object (self)
    inherit [_] Rpp_visitor.rpp_visitor

    val quant_map = ref Cil_datatype.Logic_var.Map.empty
    val fun_quant_map = ref Cil_datatype.Logic_var.Map.empty
    val call_side_effect_data = ref ([]:Rpp_types.call_data list)
    val inline_info = ref ([]:Rpp_types.inline_info list)
    val formal_pointer_check= ref ([]:Cil_types.term list)

    method  build_call_app env inline funct formals ty =
      let temp = !quant_map in
      quant_map := !fun_quant_map;
      let name =
        String.concat "_" ["local_variable_relational";
                           string_of_int
                             (Rpp_options.Counting_local_variable_verification_function.next ())]
      in
      let data = self#funct_term_app_call env inline funct formals ty name in
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

      let term_node_assert = TLval(TMem(new_term),off) in
      let typ = match ty with
        | Ctype t -> Ctype(get_typ_in_current_project
                             t (env.self#behavior) (env.loc))
        | Linteger -> Linteger
        | Lreal -> Lreal
        | _ -> Rpp_options.Self.fatal ~source:env.loc
                 "Match bad terme type in term:@. @[%a@] @." Printer.pp_term new_term
      in
      let assert_term =
        Logic_const.term
          ~loc:(env.pos)
          term_node_assert
          typ
      in

      quant_map := temp;
      assert_term

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

    method  build_call_unop env unop term ty =
      let temp = !quant_map in
      quant_map := !fun_quant_map;
      let data = self#build_term_unop env unop term ty in
      quant_map := temp;
      data

    method build_call env id inline func formals =
      let data = check_function_side_effect func env.loc in
      let (func_formals,new_exp) =
        typer func env formals
      in
      let vis = new separate_checker
        env.loc !formal_pointer_check id
      in
      let visitor =
        Visitor.visitFramacTerm vis
      in
      List.iter(fun x -> let _ = visitor x in ()) formals;
      formal_pointer_check := !formal_pointer_check@formals;

      (*Generation of stmt for auxiliarie local variable*)
      let (new_stmt,new_stmt_var) = make_stmt_from_exp new_exp env.pos in

      (*Generation of terms for the assert predicate and the copie information*)
      let func_type_return = function_return_type func (env.self#behavior) (env.loc)in
      let name =
        String.concat "_" ["return_variable_relational";
                           string_of_int
                             (Rpp_options.Counting_return_formals_verification_function.next ())]
      in
      let return =
        match func_type_return with
        |TVoid(_) -> None
        | x -> Some (Cil.makeLocalVar (env.new_funct) name x)
      in
      (*Generation des variables locals *)
      let locals =
        make_local (env.new_funct) (Kernel_function.get_definition (Globals.Functions.get func))
          (Rpp_options.Counting_local_variable_copies.next()) env.self#behavior env.loc inline
      in

      (*Génération des pointer globales*)
      let map = Cil_datatype.Varinfo.Map.empty in
      let (new_assigns_p,new_assigns_p_list) =
        make_globale
          (List.fold_right (fun (_,x) acc -> x ::acc) data.assigns_p [])
          id map env.self#behavior env.loc env.pos func_formals num
      in
      let (new_froms_p,new_froms_p_list) =
        make_globale
          (List.fold_right(fun (_,x) acc -> x ::acc) data.from_p [])
          id new_assigns_p env.self#behavior env.loc env.pos func_formals num
      in
      (*Génération des variable globales*)
      let map = Cil_datatype.Varinfo.Map.empty in
      let (new_assigns,new_assigns_list) =
        make_globale data.assigns id map env.self#behavior env.loc env.pos func_formals num
      in
      let (new_froms,new_from_list) =
        make_globale data.froms id  new_assigns env.self#behavior env.loc env.pos func_formals num
      in
      let f y =
        List.map(fun (x,_)-> x) y
      in
      let separated_term =
        (f data.from_p_f)@(f data.from_p)@(f data.assigns_p)@(f data.assigns_p_f)
      in
      let separated_term = clone_killer separated_term [] (Cil_datatype.Term.equal) in
      let inline_data = {
        kf = Globals.Functions.get func;
        formal_var = new_stmt_var;
        formal_exp = new_stmt;
        separated_terms = separated_term;
        id_option = Some id;
        inlining = inline;
        formals = List.rev func_formals;
        return_option = return;
        locals = locals;
        formal_map = new_exp;
      }
      in
      inline_info := inline_data :: !inline_info;
      let data = {
        id_call = id;
        return =  return;
        froms_map = new_froms;
        assigns_map =  new_assigns;
        froms_map_p =  new_froms_p;
        assigns_map_p = new_assigns_p ;
      }
      in
      call_side_effect_data := data :: !call_side_effect_data;
      inliner env inline_data
        (data.froms_map,data.assigns_map,data.froms_map_p,data.assigns_map_p)
        (new_assigns_list@new_from_list@new_assigns_p_list@new_froms_p_list)
        data_annot num env.proof;

    method  build_callset _ _ = ()

    method  build_term_app_call env inline funct formals ty =
      let name =
        String.concat "_" ["return_variable_relational";
                           string_of_int
                             (Rpp_options.Counting_return_formals_verification_function.next ())]
      in
      self#funct_term_app_call env inline funct formals ty name

    method  funct_term_app_call env inline funct formals _ return_name =
      let (func_formals,new_exp) =
        typer funct env formals
      in
      (*Generation of stmt for auxiliarie local variable*)
      let (new_stmt,new_stmt_var) =
        make_stmt_from_exp new_exp env.pos
      in
      (*Generation of terms for the assert predicate and the copie information*)
      let func_type_return =
        function_return_type funct env.self#behavior env.loc
      in
      let return =
        Cil.makeLocalVar env.new_funct return_name func_type_return
      in
      let logic_var = Cil.cvar_to_lvar return in
      (*Generation des variables locals *)
      let kf = Globals.Functions.get funct in
      let inline_data =
        match Kernel_function.get_definition kf with
        | exception _ ->
          {
            kf;
            formal_var = new_stmt_var;
            formal_exp = new_stmt;
            separated_terms = [];
            id_option = None;
            inlining = 0;
            formals = List.rev func_formals;
            return_option = Some return;
            locals = [];
            formal_map = new_exp;
          }
        | f ->
          let locals =
            make_local env.new_funct f
              (Rpp_options.Counting_local_variable_copies.next()) env.self#behavior env.loc inline
          in
          {
            kf;
            formal_var = new_stmt_var;
            formal_exp = new_stmt;
            separated_terms = [];
            id_option = None;
            inlining = inline;
            formals = List.rev func_formals;
            return_option = Some return;
            locals = locals;
            formal_map = new_exp;
          }
      in
      inline_info := inline_data :: !inline_info;
      let term_node_assert = TLval(TVar(logic_var),TNoOffset) in
      let new_term_assert =
        Logic_const.term
          ~loc:(env.pos)
          term_node_assert
          (logic_var.lv_type)
      in
      let map = Cil_datatype.Varinfo.Map.empty in
      inliner env inline_data
        (map,map,map,map) [] data_annot num env.proof;
      new_term_assert


    method  build_term_binop_at env binop term1_assert term2_assert ty _ =
      self#build_term_binop env binop term1_assert term2_assert ty

    method  build_term_logic_coerce_at env ty term_assert typ _ =
      self#build_term_logic_coerce env ty term_assert typ

    method  build_term_const_at env logic_const ty _ =
      self#build_term_const env logic_const ty

    method  build_term_valvar_at env logic_var new_off ty label =
      match Str.bounded_split (Str.regexp "_") label 2 with
      | "Pre":: id :: [] ->
        let new_lv_assert = match logic_var.lv_origin with
          | None ->
            let assert_param_varinfo =
              try (Cil_datatype.Logic_var.Map.find logic_var !quant_map) with
                Not_found -> Rpp_options.Self.abort ~source:env.loc
                               "Unknow logical vaiable %s in \\at"
                               logic_var.lv_name
            in
            assert_param_varinfo
          | Some v ->
            let data =
              try List.find (fun data -> String.equal id data.id_call) !call_side_effect_data with
              | Not_found -> Rpp_options.Self.fatal ~source:env.loc
                               "The identifier %s is suppose to existe according \
                                to the parser, but cannot be found for label %s"
                               id label
            in
            let new_lv_assert =
              try Cil_datatype.Varinfo.Map.find v (data.froms_map_p) with
              | Not_found -> Rpp_options.Self.abort ~source:env.loc
                               "The pointer %a is suppose not to be\
                                used in the assignement of an over variable"
                               Printer.pp_varinfo v
            in
            new_lv_assert
        in
        let typ = match ty with
          | Ctype t -> Ctype(get_typ_in_current_project t (env.self#behavior) (env.loc))
          | Linteger -> Linteger
          | Lreal -> Lreal
          | _ -> Rpp_options.Self.fatal ~source:env.loc
                   "Match bad terme type for logical variable:@. @[%a@] @."
                   Printer.pp_logic_var logic_var
        in
        let the_terme_node_assert = TLval(TVar(new_lv_assert),new_off) in
        let new_assert_term =
          Logic_const.term
            ~loc:(env.pos)
            the_terme_node_assert
            typ
        in
        new_assert_term

      | "Post" :: id :: [] ->
        let new_lv_assert = match logic_var.lv_origin with
          | None ->
            let assert_param_varinfo =
              try Cil_datatype.Logic_var.Map.find logic_var !quant_map with
                Not_found -> Rpp_options.Self.abort ~source:env.loc
                               "Unknow logical vaiable %s in \\at"
                               logic_var.lv_name
            in
            assert_param_varinfo
          | Some v ->
            let data =
              try List.find (fun data -> String.equal id data.id_call) !call_side_effect_data with
              | Not_found -> Rpp_options.Self.fatal ~source:env.loc
                               "The identifier %s is suppose to existe according \
                                to the parser, but cannot be found for label %s"
                               id label
            in
            let new_lv_assert =
              try Cil_datatype.Varinfo.Map.find v (data.assigns_map_p) with
              | Not_found -> Rpp_options.Self.abort ~source:env.loc
                               "The pointer %a is suppose not to be assigned"
                               Printer.pp_varinfo v
            in
            new_lv_assert
        in
        let typ = match ty with
          | Ctype t -> Ctype(get_typ_in_current_project t (env.self#behavior) (env.loc))
          | Linteger -> Linteger
          | Lreal -> Lreal
          | _ -> Rpp_options.Self.fatal ~source:env.loc
                   "Match bad terme type in term variable:@. @[%a@] @."
                   Printer.pp_logic_var logic_var
        in
        let the_terme_node_assert = TLval(TVar(new_lv_assert),new_off) in
        let new_assert_term =
          Logic_const.term
            ~loc:(env.pos)
            the_terme_node_assert
            typ
        in
        new_assert_term
      | _ -> Rpp_options.Self.fatal ~source:env.loc
               "Something went wrong during parsing: \\at have an unsupported label %s" label


    method  build_Toffset_at env off _ =
      self#build_Toffset env off

    method build_term_binop env binop term1_assert term2_assert ty =
      let new_ty = match ty with
        | Ctype t ->
          Ctype(get_typ_in_current_project t (env.self#behavior) (env.loc))
        | Linteger -> Linteger
        | Lreal -> Lreal
        | _ ->  Rpp_options.Self.fatal ~source:env.loc "Match bad terme type in logic corece"
      in
      let new_term_assert =
        Logic_const.term
          ~loc:(env.pos)
          (TBinOp(binop,term1_assert,term2_assert))
          (new_ty)
      in
      new_term_assert

    method  build_term_logic_coerce env ty term_assert typ =
      let new_ty = match ty with
        | Ctype t -> Ctype(get_typ_in_current_project t (env.self#behavior) (env.loc))
        | Linteger -> Linteger
        | Lreal -> Lreal
        | _ -> Rpp_options.Self.fatal ~source:env.loc "Match bad terme type in logic corece"
      in
      let new_typ = match typ with
        | Ctype t -> Ctype(get_typ_in_current_project t (env.self#behavior) (env.loc))
        | Linteger -> Linteger
        | Lreal -> Lreal
        | _ -> Rpp_options.Self.fatal ~source:env.loc "Match bad terme type in logic corece"
      in
      let new_term_assert =
        Logic_const.term
          ~loc:(env.pos)
          (TLogic_coerce(new_ty,term_assert))
          (new_typ)
      in
      new_term_assert

    method  build_term_const env logic_const _ =
      match logic_const with
      | Integer(int,x) ->
        let new_term =
          Logic_const.term ~loc:(env.pos) (TConst (Integer (int,x))) Linteger
        in
        new_term
      | LReal(l_r) ->
        let new_term =
          Logic_const.term ~loc:(env.pos) (TConst (LReal l_r)) Lreal
        in
        new_term
      | _ -> Rpp_options.Self.fatal ~source:env.loc "Match bad term constant"

    method build_Toffset env offset =
      match offset with
      | TNoOffset -> TNoOffset
      | TField(field_info,field_offset) ->
        let new_field_info =
          Cil.get_fieldinfo (env.self#behavior) field_info
        in
        let new_field_offset =
          self#build_Toffset env field_offset
        in
        TField(new_field_info,new_field_offset)
      | TModel(_,_) -> (** access to a model field. *)
        Rpp_options.Self.abort ~source:env.loc
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
      let assert_param_varinfo =
        try (Cil_datatype.Logic_var.Map.find logic_var !quant_map) with
          Not_found ->  Rpp_options.Self.abort ~source:env.loc
                          "Error in predicate: terme %s has no quantifiers"
                          (logic_var.lv_name)
      in
      match new_off with
      | TNoOffset ->
        let term_node_assert =
          TLval(TVar( assert_param_varinfo),new_off)
        in
        let assert_term =
          Logic_const.term
            ~loc:(env.pos)
            term_node_assert
            (assert_param_varinfo.lv_type)
        in
        assert_term
      | _ ->
        let new_ty = match ty with
          | Ctype t -> Ctype(get_typ_in_current_project t (env.self#behavior) (env.loc))
          | Linteger -> Linteger
          | Lreal -> Lreal
          | _ -> Rpp_options.Self.fatal ~source:env.loc "Match bad terme type in term variable"
        in
        let term_node_assert =
          TLval(TVar(assert_param_varinfo),new_off)
        in
        let assert_term =
          Logic_const.term
            ~loc:(env.pos)
            term_node_assert
            new_ty
        in
        assert_term

    method  build_term_app_result env id _ =
      let data =
        try List.find (fun data -> String.equal id  data.id_call) !call_side_effect_data with
        | Not_found -> Rpp_options.Self.fatal ~source:env.loc
                         "The identifier %s is suppose to existe according to the \
                          parser, but cannot be found" id
      in
      let l_v = match data.return with
        | None -> Rpp_options.Self.abort ~source:env.loc
                    "Id %s refer to a function with not return variable" id
        | Some x -> Cil.cvar_to_lvar x
      in
      let term_node_assert =
        TLval(TVar(l_v),TNoOffset)
      in
      let assert_term =
        Logic_const.term
          ~loc:(env.pos)
          term_node_assert
          (l_v.lv_type)
      in
      assert_term

    method  build_term_at_var env l_v new_off s _ =
      let v =
        match l_v.lv_origin with
        | Some(var) -> var
        | None ->
          begin
            match Cil_datatype.Logic_var.Map.find l_v !quant_map with
            | exception Not_found -> Rpp_options.Self.abort ~source:env.loc
                                       "Unknow logical vaiable %a in \\at built-in"
                                       Printer.pp_logic_var l_v
            | _ -> Rpp_options.Self.abort ~source:env.loc
                     "Logical vaiable %a in \\at built-in is a formal variable, \
                      it can not be modified"
                     Printer.pp_logic_var l_v
          end
      in
      match Str.bounded_split (Str.regexp "_") s 2 with
      | "Pre":: id :: [] ->
        let data =
          try List.find (fun data -> String.equal id data.id_call) !call_side_effect_data with
          | Not_found ->
            Rpp_options.Self.fatal ~source:env.loc
              "The identifier %s is suppose to existe according to \
               the parser, but cannot be found" id
        in
        let new_lv_assert =
          try Cil_datatype.Varinfo.Map.find v (data.froms_map) with
          | Not_found -> Rpp_options.Self.abort ~source:env.loc
                           "The variable %a is suppose not to be\
                            used in the assignement of an over variable"
                           Printer.pp_varinfo v
        in
        let the_term_node_assert = TLval(TVar(new_lv_assert),new_off) in
        let new_the_term =
          Logic_const.term
            ~loc:(env.pos)
            the_term_node_assert
            (new_lv_assert.lv_type)
        in
        let term_node_assert = Tat(new_the_term,BuiltinLabel(Pre)) in
        let assert_term =
          Logic_const.term
            ~loc:(env.pos)
            term_node_assert
            (new_lv_assert.lv_type)
        in
        assert_term

      | "Post" :: id :: [] ->
        let data =
          try List.find (fun data -> String.equal id data.id_call) !call_side_effect_data with
          | Not_found -> Rpp_options.Self.fatal ~source:env.loc
                           "The identifier %s is suppose to existe according \
                            to the parser, but cannot be found" id
        in
        let new_lv_assert =
          try Cil_datatype.Varinfo.Map.find v (data.assigns_map) with
          | Not_found -> Rpp_options.Self.abort ~source:env.loc
                           "The variable %s is suppose not to be assigned"
                           v.vname
        in
        let the_term_node_assert = TLval(TVar(new_lv_assert),new_off) in
        let new_the_term =
          Logic_const.term
            ~loc:(env.pos)
            the_term_node_assert
            (new_lv_assert.lv_type)
        in
        let term_node_assert = Tat(new_the_term,BuiltinLabel(Here)) in
        let assert_term =

          Logic_const.term
            ~loc:(env.pos)
            term_node_assert
            (new_lv_assert.lv_type)
        in
        assert_term

      | _ -> Rpp_options.Self.fatal ~source:env.loc
               "Something went wrong during parsing: \\at have an unsupported label %s" s

    method  build_term_at_mem env t s ty =
      match Str.bounded_split (Str.regexp "_") s 2 with
      | "Pre":: _ :: [] ->
        let the_terme_node_assert = TLval(TMem(t),TNoOffset) in
        let typ = match ty with
          | Ctype t -> Ctype(get_typ_in_current_project t (env.self#behavior) (env.loc))
          | Linteger -> Linteger
          | Lreal -> Lreal
          | _ -> Rpp_options.Self.fatal ~source:env.loc "Match bad terme type in term variable"
        in
        let new_assert_term =
          Logic_const.term
            ~loc:env.pos
            the_terme_node_assert
            typ
        in
        let term_node_assert = Tat(new_assert_term,BuiltinLabel(Pre)) in
        let assert_term =
          Logic_const.term
            ~loc:env.pos
            term_node_assert
            typ
        in
        assert_term

      | "Post" :: _ :: [] ->
        let the_terme_node_assert = TLval(TMem(t),TNoOffset) in
        let typ = match ty with
          | Ctype t -> Ctype(get_typ_in_current_project t (env.self#behavior) (env.loc))
          | Linteger -> Linteger
          | Lreal -> Lreal
          | _ -> Rpp_options.Self.fatal ~source:env.loc "Match bad terme type in term variable"
        in
        let new_assert_term =
          Logic_const.term
            ~loc:env.pos
            the_terme_node_assert
            typ
        in
        let term_node_assert = Tat(new_assert_term,BuiltinLabel(Here)) in
        let assert_term =
          Logic_const.term
            ~loc:env.pos
            term_node_assert
            typ
        in
        assert_term

      | _ -> Rpp_options.Self.fatal ~source:env.loc
               "Something went wrong during parsing: \\at have an unsupported label %s" s

    method  build_term_unop env op  term_assert ty =
      let term_node_assert =
        TUnOp(op,term_assert)
      in
      let new_ty = match ty with
        | Ctype t ->
          Ctype(get_typ_in_current_project t (env.self#behavior) (env.loc))
        | Linteger -> Linteger
        | Lreal -> Lreal
        | _ ->
          Rpp_options.Self.fatal ~source:env.loc "Match bad terme type in logic corece"
      in
      let assert_term =
        Logic_const.term
          ~loc:(env.pos)
          term_node_assert
          (new_ty)
      in
      assert_term

    method  build_term_range env term1 term2 _ =
      let (term1_assert,term2_assert)=
        match term1,term2 with
        | None, None-> (None,None)
        | Some(term1_assert),None -> (Some term1_assert,None)
        | None, Some(term2_assert) -> (None,Some term2_assert)
        | Some(term1_assert),Some(term2_assert) -> (Some term1_assert,Some term2_assert)
      in
      let assert_term =
        Logic_const.trange
          ~loc:(env.pos)
          (term1_assert,term2_assert)
      in
      assert_term

    method build_term_app  env logic_info t_list ty =
      let new_logicinfo = Cil.get_logic_info env.self#behavior logic_info in
      let new_ty = match ty with
        | Ctype t ->
          Ctype(get_typ_in_current_project t (env.self#behavior) (env.loc))
        | Linteger -> Linteger
        | Lreal -> Lreal
        | _ ->
          Rpp_options.Self.fatal ~source:env.loc "Match bad terme type in logic corece"
      in
      let term_node_assert =
        Tapp(new_logicinfo,[],t_list)
      in
      let assert_term =
        Logic_const.term
          ~loc:(env.pos)
          term_node_assert
          new_ty
      in
      assert_term

    method  build_predicate_rel env rel t1_assert t2_assert =
      let new_assert_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = Prel(rel,t1_assert,t2_assert);
      }
      in
      new_assert_predicate

    method  build_predicate_false env =
      let new_assert_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = Pfalse;
      }
      in
      new_assert_predicate

    method  build_predicate_true env =
      let new_assert_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = Pfalse;
      }
      in
      new_assert_predicate

    method  build_predicate_and env pred1_assert pred2_assert =
      let new_assert_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = Pand(pred1_assert,pred2_assert);
      }
      in
      new_assert_predicate

    method  build_predicate_or env pred1_assert pred2_assert =
      let new_assert_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = Por(pred1_assert,pred2_assert);
      }
      in
      new_assert_predicate

    method  build_predicate_xor env pred1_assert pred2_assert =
      let new_assert_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = Pxor(pred1_assert,pred2_assert);
      }
      in
      new_assert_predicate

    method  build_predicate_implies env pred1_assert pred2_assert =
      let new_assert_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = Pimplies(pred1_assert,pred2_assert);
      }
      in
      new_assert_predicate

    method  build_predicate_iff env pred1_assert pred2_assert =
      let new_assert_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = Piff(pred1_assert,pred2_assert);
      }
      in
      new_assert_predicate

    method  build_predicate_not env pred_assert =
      let new_assert_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = Pnot(pred_assert);
      }
      in
      new_assert_predicate

    method build_predicate_label env l =
      let new_labels =
        begin
          fun l ->
            List.map(
              fun x ->
                match x with
                | FormalLabel(id) ->
                  (BuiltinLabel((id_convert id (env.loc) (!call_side_effect_data))))
                | _ -> assert false) l
        end
      in
      new_labels l

    method  build_predicate_app env logic_info l_assert t_list =
      let new_logicinfo = Cil.get_logic_info env.self#behavior logic_info in
      let new_assert_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = Papp(new_logicinfo,l_assert,t_list);
      }
      in
      new_assert_predicate

    method build_predicate_quan env quan =
      List.iter (fun x ->
          match x.lv_type with
          | Ctype(t) ->
            let new_t =
              get_typ_in_current_project t env.self#behavior env.loc
            in
            let new_logic_var =
              Cil_const.make_logic_var_quant
                (x.lv_name) (Ctype(new_t))
            in
            begin
              match Cil_datatype.Logic_var.Map.find x !quant_map with
              | exception Not_found ->
                quant_map := Cil_datatype.Logic_var.Map.add x new_logic_var !quant_map
              | _ -> Rpp_options.Self.abort ~source:env.loc
                       "Quantified logic variable %a already exists" Printer.pp_logic_var x
            end
          | Linteger ->
            Rpp_options.Self.abort ~source:env.loc
              "Error in pedicate: Mathematical integer in quantifier are not supported:@. @[%a@]@."
              Printer.pp_logic_var x
          | Lreal ->
            Rpp_options.Self.abort ~source:env.loc
              "Error in pedicate: Mathematical real in quantifier are not supported:@. @[%a@]@."
              Printer.pp_logic_var x
          | Ltype _ ->
            Rpp_options.Self.abort ~source:env.loc
              "Error in pedicate: Logic type in quantifier are not supported:@. @[%a@]@."
              Printer.pp_logic_var x
          | Lvar _ ->
            Rpp_options.Self.abort ~source:env.loc
              "Error in pedicate: Logic variable in quantifier are not supported:@. @[%a@]@."
              Printer.pp_logic_var x
          | Larrow _ ->
            Rpp_options.Self.abort ~source:env.loc
              "Error in predicate: Logic function type in quantifier are not supported:@. @[%a@]@."
              Printer.pp_logic_var x)
        quan ;
      quan

    method build_predicate_forall env quan pred =
      let new_quant = List.map(fun x ->
          let new_logic_var =
            (try (Cil_datatype.Logic_var.Map.find x !quant_map) with
             | Not_found -> Rpp_options.Self.fatal ~source:env.loc
                              "Quantified logic variable %a is not in the new \
                               quantified logic varible" Printer.pp_logic_var x

             | _ -> assert false)
          in
          quant_map := Cil_datatype.Logic_var.Map.remove x !quant_map;
          new_logic_var) quan
      in
      let new_predicate_content =
        Pforall(new_quant,pred)
      in
      let new_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = new_predicate_content;
      }
      in
      new_predicate

    method build_predicate_exists env quan pred =
      let new_quant = List.map(fun x ->
          let new_logic_var =
            (try (Cil_datatype.Logic_var.Map.find x !quant_map) with
             | Not_found -> Rpp_options.Self.fatal ~source:env.loc
                              "Quantified logic variable %a is not in the new \
                               quantified logic varible" Printer.pp_logic_var x

             | _ -> assert false)
          in
          quant_map := Cil_datatype.Logic_var.Map.remove x !quant_map;
          new_logic_var) quan
      in
      let new_predicate_content =
        Pexists(new_quant,pred)
      in
      let new_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = new_predicate_content;
      }
      in
      new_predicate

    method build_rpp_quan env quan =
      List.iter (fun x ->
          match x.lv_type with
          | Ctype(t) ->
            let new_t =
              get_typ_in_current_project t env.self#behavior env.loc
            in
            let new_param_varinfo =
              Cil.makeFormalVar (env.new_funct) (x.lv_name) new_t
            in
            quant_map := Cil_datatype.Logic_var.Map.add x (Cil.cvar_to_lvar new_param_varinfo) !quant_map;
            fun_quant_map := Cil_datatype.Logic_var.Map.add x (Cil.cvar_to_lvar new_param_varinfo) !fun_quant_map

          | Linteger ->
            Rpp_options.Self.abort ~source:env.loc
              "Error in pedicate: A C function can not have a mathematical integer as parameter"
          | Lreal ->
            Rpp_options.Self.abort ~source:env.loc
              "Error in pedicate: A C function can not have a mathematical real as parameter"
          | Ltype _ ->
            Rpp_options.Self.abort ~source:env.loc
              "Error in pedicate: A C function can not have a logic type as parameter"
          | Lvar _ ->
            Rpp_options.Self.abort ~source:env.loc
              "Error in pedicate: A C function can not have a logic type variable as parameter"
          | Larrow _ ->
            Rpp_options.Self.abort ~source:env.loc
              "Error in predicate: A C function can not have a logic function type as parameter")
        quan ;

    method build_rpp_predicate_forall env _ new_assert_predicate =
      make_separate env !inline_info !call_side_effect_data;
      Queue.add(fun () ->
          env.new_funct.sbody.bstmts <- env.new_funct.sbody.bstmts @ [Cil.mkStmt ~valid_sid:true (Return(None,(env.loc,env.loc)))];
        )
        env.self#get_filling_actions;new_assert_predicate

    method build_rpp_predicate_forall_callset env _ () new_assert_predicate =
      make_separate env !inline_info !call_side_effect_data;
      Queue.add(fun () ->
          env.new_funct.sbody.bstmts <- env.new_funct.sbody.bstmts @ [Cil.mkStmt ~valid_sid:true (Return(None,(env.loc,env.loc)))];
        )
        env.self#get_filling_actions;
      new_assert_predicate

    method build_rpp_predicate_implies_callset env () new_assert_predicate =
      make_separate env !inline_info !call_side_effect_data;
      Queue.add(fun () ->
          env.new_funct.sbody.bstmts <- env.new_funct.sbody.bstmts @ [Cil.mkStmt ~valid_sid:true (Return(None,(env.loc,env.loc)))];
        )
        env.self#get_filling_actions;
      new_assert_predicate

    method build_rpp_predicate_implies env new_assert_predicate =
      make_separate env !inline_info !call_side_effect_data;
      Queue.add(fun () ->
          env.new_funct.sbody.bstmts <- env.new_funct.sbody.bstmts @ [Cil.mkStmt ~valid_sid:true (Return(None,(env.loc,env.loc)))];
        )
        env.self#get_filling_actions;
      new_assert_predicate

    method  build_rpp_predicate_rel env rel t1_assert t2_assert =
      make_separate env !inline_info !call_side_effect_data;
      Queue.add(fun () ->
          env.new_funct.sbody.bstmts <- env.new_funct.sbody.bstmts @ [Cil.mkStmt ~valid_sid:true (Return(None,(env.loc,env.loc)))];
        )
        env.self#get_filling_actions;
      let new_assert_predicate ={
        pred_name = [];
        pred_loc = env.pos;
        pred_content = Prel(rel,t1_assert,t2_assert);
      }
      in
      new_assert_predicate

  end
  in
  let (loc,_)=predicate.pred_loc in
  let env = {
    loc = loc;
    pos = predicate.pred_loc;
    new_funct = new_funct;
    proj = proj;
    self = self;
    proof = proof;
  }
  in
  let new_predicate =
    v#visit_rpp_predicate env predicate
  in

  (*Add the assert clause in the new kernel function for the proof of the
               relational property and make relation between the properties of the
               assert and the corresponding lemma*)
  let predicate_named =
    Logic_const.new_predicate new_predicate
  in
  let the_code_annotation =
    Logic_const.new_code_annotation
      (AAssert ([],(Logic_const.pred_of_id_pred predicate_named)))
  in
  Queue.add(fun () ->
      Annotations.add_code_annot
        Rpp_options.emitter ~kf:(Globals.Functions.get (env.new_funct.svar))
        (List.hd (List.rev env.new_funct.sbody.bstmts))
        the_code_annotation;
    )
    self#get_filling_actions;
  the_code_annotation
