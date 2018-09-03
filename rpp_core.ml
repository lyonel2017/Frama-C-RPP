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

open Rpp_options
open Cil_types
open Cil


let print_hello message =
  Self.result "***************************************";
  Self.result "          %s" message;
  Self.result "***************************************"

(**
   Function for generating a new function and ACSL annotations for prouving the relational property
*)
let relationel_function f l predicate self proj annot_data =
  (*Making data for the generation of the new kf for each relational property*)
  let data =
    List.fold_left (fun data predicate ->
        let name =
          String.concat "_" ["relational_wrapper";
                             string_of_int
                               (Rpp_options.Counting_relational_verification_function.next ())]
        in
        let wrapper_num =
          (Rpp_options.Counting_relational_verification_function.get ());
        in
        let new_fundec =
          Cil.emptyFunction name
        in
        new_fundec.svar.vdefined <- true;
        let spec =
          Cil.empty_funspec ()
        in
        Queue.add(fun () ->
            Cfg.clearCFGinfo ~clear_id:false new_fundec;
            Cfg.cfgFun new_fundec;
            Globals.Functions.replace_by_definition spec new_fundec f.svar.vdecl;
            new_fundec.sbody <- {battrs = [];
                                 bscoping = true;
                                 blocals = [];
                                 bstatics = [];
                                 bstmts = []};
          )
          self#get_filling_actions;

        let (new_axiome_predicate,new_labels,call_info_logic,call_info_logic_pure) =
          Rpp_predicate_visitor_axiom.predicate_visitor (List.hd predicate) self
        in

        (*Make the axiomatic clause (relational propertie as an hypothese) and add
          behaviours to the function linked to the relational propertie for linking
          the function to the axiomatic (logical function)*)
        (*This action is done before making the kernel function because a binding
          is down between the kf of the function involved in the relational propertie
          and the new generated kf (wrapper function)*)
        let (axiom,id_lemma) =
          Rpp_axiomatic_generator.relationnel_axiom
            l self new_axiome_predicate new_labels call_info_logic call_info_logic_pure
        in
        annot_data := (wrapper_num,call_info_logic,call_info_logic_pure)::!annot_data;
        let code_annotation =
          Rpp_predicate_visitor.predicate_visitor
            (List.hd predicate) new_fundec self proj !annot_data wrapper_num
        in

        (*Relation between the properties of the
          assert and the corresponding lemma*)
        Queue.add(fun () ->
            let property2 = Property.ip_lemma id_lemma
            in
            let property3 = Property.ip_of_code_annot_single
                (Globals.Functions.get (new_fundec.svar))
                (List.hd (List.rev new_fundec.sbody.bstmts))
                code_annotation
            in
            Property_status.emit
              (Rpp_options.emitter) ~hyps:[property3] property2 Property_status.True;
          )
          self#get_filling_actions;


        (new_fundec,axiom)::data
      ) [] (List.rev predicate)
  in
  data


(**
   Function for generating a new function for the prove of relational properties
*)
let relationel_proof f predicate self proj annot_data =
  (*Making data for the generation of the new kf for each relational property*)
  let data =
    List.fold_left (fun data (predicate,property2) ->
        let name =
          String.concat "_" ["relational_wrapper";
                             string_of_int
                               (Rpp_options.Counting_relational_verification_function.next ())]
        in
        let wrapper_num =
          (Rpp_options.Counting_relational_verification_function.get ());
        in
        let new_fundec =
          Cil.emptyFunction name
        in
        new_fundec.svar.vdefined <- true;
        let spec =
          Cil.empty_funspec ()
        in
        Queue.add(fun () ->
            Cfg.clearCFGinfo ~clear_id:false new_fundec;
            Cfg.cfgFun new_fundec;
            Globals.Functions.replace_by_definition spec new_fundec f.svar.vdecl;
            new_fundec.sbody <- {battrs = [];
                                 bscoping = true;
                                 blocals =[];
                                 bstatics = [];
                                 bstmts = []};
          )
          self#get_filling_actions;

        let code_annotation =
          Rpp_predicate_visitor.predicate_visitor ~proof:false
            (List.hd predicate) new_fundec self proj !annot_data wrapper_num
        in

        (*Relation between the properties of the
          assert and the corresponding lemma*)
        begin
          match property2 with
          | None -> ()
          | Some x ->
            begin
              Queue.add(fun () ->
                  let property3 = Property.ip_of_code_annot_single
                      (Globals.Functions.get (new_fundec.svar))
                      (List.hd (List.rev new_fundec.sbody.bstmts))
                      code_annotation
                  in
                  Property_status.emit
                    (Rpp_options.emitter) ~hyps:[property3] x Property_status.True;
                )
                self#get_filling_actions;
            end
        end;
        new_fundec::data
      ) [] (List.rev predicate)
  in
  data

(**
   Function for generating functions and ACSL annotations to prouve relational
   properties for the current visited function prototype
*)
let relationel_axiome l predicate self annot_data =
  List.fold_left (fun global_data pred ->
      let (new_axiome_predicate,new_labels,call_info_logic,call_info_logic_pure) =
        Rpp_predicate_visitor_axiom.predicate_visitor (List.hd pred) self
      in
      (*Make the axiomatic clause (relational propertie as an hypothese) and add
        behaviours to the function linked to the relational propertie for linking
        the function to the axiomatic (logical function)*)
      (*This action is done before making the kernel function because a binding is
        down between the kf of the function involved in the relational propertie
        and the new generated kf (wrapper function)*)

      let (axiom,_id_lemma) =
        Rpp_axiomatic_generator.relationnel_axiom
          l self new_axiome_predicate new_labels call_info_logic call_info_logic_pure
      in
       annot_data := (-1,call_info_logic,call_info_logic_pure)::!annot_data;
      (*Set the status of the clause to true (the behavior is supposed valid)*)
      (*let property = Property.ip_of_ensures kf (Kglobal) funbehavior ensures in
        Property_status.emit (Rpp_options.emitter) [] property Property_status.True;*)
      axiom :: global_data;
    )[] predicate


(**
   Function for generating functions to prouve relational
   properties for the current visited function
*)
let generat_prouves self project predicates x annot=
  match List.hd x with
  | GFun(f,l) ->
    if List.length predicates <> 0
    then (
      let relationnel_fonc =
        List.fold_left (fun fq f ->
            (GFun(f,l)::fq)) []
          (relationel_proof f predicates self project annot)
      in
      (GFun(f,l)::relationnel_fonc))
    else (x)
  | _ ->  x


(**
   Function for generating functions and ACSL annotations to prouve relational
   properties for the current visited function
*)
let generat_prouves_hyp self project predicates x annot=
  match List.hd x with
  | GFun(f,l) ->
    if List.length predicates <> 0
    then (
      let (relationnel_fonc,relationnel_axiom) =
        List.fold_left (fun (fq,tq) (f,a) ->
            (GFun(f,l)::fq, GAnnot(a,l)::tq )) ([],[])
          (relationel_function f l predicates self project annot)
      in
      (GFun(f,l)::relationnel_fonc @ relationnel_axiom))
    else (x)
  | _ ->  x

(**
   Function for generating ACSL annotations for the current visited function prototype
*)
let generat_prouves_prototype self predicates x annot =
  match List.hd x with
  | GFunDecl(f,v,l)->
    if List.length predicates  <> 0
    then (
      let relationnel_axiom =
        List.fold_left (fun tq a ->
            ( GAnnot(a,l)::tq )) []
          (relationel_axiome l predicates self annot)
      in
      (GFunDecl(f,v,l)::relationnel_axiom))
    else (x)
  | GFun(f,l)->
    if List.length predicates <> 0
    then (
      let relationnel_axiom =
        List.fold_left (fun tq a ->
            ( GAnnot(a,l)::tq )) []
          (relationel_axiome l predicates self annot)
      in
      (GFun(f,l)::relationnel_axiom))
    else (x)
  | _ -> x


class generation_of_prouve_system prj = object (self)
  inherit Visitor.generic_frama_c_visitor(Cil.refresh_visit prj)

  val relataional_clause_list = ref []
  val annot_data = ref []

  val mutable new_glob = []

  method add_new_global g = new_glob <- g :: new_glob

  method! vglob_aux g =
    match g with
    | GFun(_,_) ->
      (match Rpp_options.Enable_only_hyp.get (), Rpp_options.Enable_only_prove.get () with
       | false,false->
         DoChildrenPost (
           fun x ->
             let pred =  !relataional_clause_list in
             relataional_clause_list := [];
             generat_prouves_hyp
               (self:>Rpp_types.visitor)
               (Project.current ())
               pred x annot_data)
       | true ,false->
         DoChildrenPost(
           fun x ->
             let pred =  !relataional_clause_list in
             relataional_clause_list := [];
             generat_prouves_prototype
               (self:>Rpp_types.visitor)
               pred x annot_data)
       | false ,true ->
         DoChildrenPost(
           fun x ->
             let pred =  !relataional_clause_list in
             let pred = List.map (fun x -> (x,None)) pred in
             relataional_clause_list := [];
             generat_prouves
               (self:>Rpp_types.visitor)
               (Project.current ())
               pred x annot_data)
       | true ,true ->
         DoChildrenPost(
           fun x ->
             let pred =  !relataional_clause_list in
             relataional_clause_list := [];
             generat_prouves_hyp
               (self:>Rpp_types.visitor)
               (Project.current ())
               pred x annot_data)
      )
    | GFunDecl(_,_,_) ->
      DoChildrenPost(
        fun x ->
          let pred =  !relataional_clause_list in
          relataional_clause_list := [];
          generat_prouves_prototype
            (self:>Rpp_types.visitor)
            pred x annot_data)
    | _ -> JustCopy

  method! vfile _ =
    let postaction f = f.globals <- f.globals @ new_glob; f in
    DoChildrenPost postaction

  method! vbehavior g =
    let rec aux g l =
      match g with
      | [] ->
        relataional_clause_list := l;
        []
      | (_,"relational",Ext_preds(predicate)) :: q -> aux q (predicate :: l)
      | h :: q -> h :: aux q l
    in
    let b_extended = aux g.b_extended []
    in ChangeDoChildrenPost ({g with b_extended},fun x -> x)
end

let main () =
  Ast.compute ();
  let module OLS = Datatype.List(Datatype.String) in
  let module OKF = Datatype.Option(Kernel_function) in
  let module OP = Datatype.Option(Property) in
  let test kf =
    Dynamic.get
      ~plugin:"Wp" "wp_compute"
      (Datatype.func3 OKF.ty OLS.ty OP.ty Datatype.unit)
      (Some kf)
      []
      None
  in
  Globals.Functions.iter test;

  let report =
    Dynamic.get
      ~plugin:"Report" "print" (Datatype.func Datatype.unit Datatype.unit)
  in
  report ()
