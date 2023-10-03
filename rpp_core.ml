(**************************************************************************)
(*  This file is part of RPP plug-in of Frama-C.                          *)
(*                                                                        *)
(*  Copyright (C) 2016-2023                                               *)
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
   Function for generating a new function and ACSL annotations
   for proving the relational property
*)
let relationel_function l predicate self proj annot_data =
  (*Making data for the generation of the new kf for each relational property*)
  let wrapper_num =
    Rpp_options.Counting_relational_verification_function.next ()
  in
  let name = "relational_wrapper_" ^ string_of_int wrapper_num in
  let new_fundec = Cil.emptyFunction name in
  new_fundec.svar.vdefined <- true;
  let spec = Cil.empty_funspec () in
  Queue.add(
    fun () ->
      Cfg.clearCFGinfo ~clear_id:false new_fundec;
      Cfg.cfgFun new_fundec;
      Globals.Functions.replace_by_definition spec new_fundec l;
      new_fundec.sbody <- Cil.mkBlock [])
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
      l self new_axiome_predicate new_labels
      call_info_logic call_info_logic_pure
  in
  annot_data := (wrapper_num,call_info_logic,call_info_logic_pure)::!annot_data;
  let code_annotation =
    Rpp_predicate_visitor.predicate_visitor
      (List.hd predicate) new_fundec self proj !annot_data wrapper_num
  in
  (*Relation between the properties of the
    assert and the corresponding lemma*)
  Queue.add(fun () ->
      let property2 = Property.ip_lemma id_lemma in
      let property3 =
        Property.ip_of_code_annot_single
          (Globals.Functions.get (new_fundec.svar))
          (List.hd (List.rev new_fundec.sbody.bstmts))
          code_annotation
      in
      Property_status.emit
        (Rpp_options.emitter) ~hyps:[property3] property2 Property_status.True;
    )
    self#get_filling_actions;
    (new_fundec,axiom)

(**
   Function for generating a new function for the prove of relational properties
*)
let relationel_proof loc predicate self proj annot_data =
  (*Making data for the generation of the new kf for each relational property*)
  let wrapper_num =
    Rpp_options.Counting_relational_verification_function.next ()
  in
  let name = "relational_wrapper_" ^ string_of_int wrapper_num in
  let new_fundec = Cil.emptyFunction name in
  new_fundec.svar.vdefined <- true;
  let spec = Cil.empty_funspec () in
  Queue.add(
    fun () ->
      Cfg.clearCFGinfo ~clear_id:false new_fundec;
      Cfg.cfgFun new_fundec;
      Globals.Functions.replace_by_definition spec new_fundec loc;
      new_fundec.sbody <- Cil.mkBlock [])
    self#get_filling_actions;
  ignore
    (Rpp_predicate_visitor.predicate_visitor ~proof:false
       (List.hd predicate) new_fundec self proj !annot_data wrapper_num);
  new_fundec

(**
   Function for generating functions and ACSL annotations to prouve relational
   properties for the current visited function prototype
*)
let relationel_axiome l pred self annot_data =
  let (new_axiome_predicate,new_labels,call_info_logic,call_info_logic_pure) =
    Rpp_predicate_visitor_axiom.predicate_visitor (List.hd pred) self
  in
  (*Make the axiomatic clause (relational propertie as an hypothese) and add
    behaviours to the function linked to the relational propertie for linking
    the function to the axiomatic (logical function)
  *)
  (*This action is done before making the kernel function because a binding is
     down between the kf of the function involved in the relational propertie
     and the new generated kf (wrapper function)*)

  let (axiom,_id_lemma) =
    Rpp_axiomatic_generator.relationnel_axiom
      l self new_axiome_predicate new_labels
      call_info_logic call_info_logic_pure
  in
  annot_data := (-1,call_info_logic,call_info_logic_pure)::!annot_data;
  (*Set the status of the clause to true (the behavior is supposed valid)*)
  (*let property = Property.ip_of_ensures kf (Kglobal) funbehavior ensures in
     Property_status.emit (Rpp_options.emitter) [] property Property_status.True;*)
  axiom

(**
   Function for generating functions to prouve relational
   properties for the current visited function
*)
let generat_proofs self project predicates loc annot =
  let rel_fun =
    relationel_proof loc predicates self project annot
  in
  [GFun(rel_fun,loc)]

(**
   Function for generating functions and ACSL annotations to prouve relational
   properties for the current visited function
*)
let generat_proofs_axioms self project predicates loc annot=
  let (rel_fun,rel_ax) =
    relationel_function loc predicates self project annot
  in
  [ GFun(rel_fun, loc); GAnnot(rel_ax,loc)]

(**
   Function for generating ACSL annotations for the current visited function prototype
*)
let generat_axioms self predicates loc annot =
  let rel_ax =
    relationel_axiome loc predicates self annot
  in
  [GAnnot(rel_ax,loc)]

class generation_of_prouve_system prj = object (self)
  inherit Visitor.generic_frama_c_visitor(Visitor_behavior.refresh prj)

  val relataional_clause_list = ref []
  val annot_data = ref []

  val mutable new_glob = []

  method add_new_global g = new_glob <- g :: new_glob

  method private add_new_globals gs = new_glob <- new_glob @ gs

  method! vannotation = function
    | Dextended
        ({ext_name = "relational"; ext_kind = Ext_preds p; ext_loc},_,_) ->
      let new_globs =
        begin
          match Rpp_options.Enable_only_hyp.get (),
                Rpp_options.Enable_only_prove.get ()
          with
          | true ,false->
            generat_axioms
              (self:>Rpp_types.visitor) p ext_loc annot_data
          | false ,true ->
            generat_proofs
              (self:>Rpp_types.visitor)
              (Project.current ()) p ext_loc annot_data
          | _ ,_ ->
            generat_proofs_axioms
              (self:>Rpp_types.visitor)
              (Project.current ()) p ext_loc annot_data
        end
      in
      self#add_new_globals new_globs;
      JustCopy
    | _ -> JustCopy

  method! vglob_aux = function
    | GAnnot (Dextended ({ ext_name = "relational"},_,_), _) ->
      DoChildrenPost (fun _ -> []) (* once treated, remove the clause. *)
    | _ -> DoChildren

  method! vfile _ =
    let postaction f = f.globals <- f.globals @ new_glob; f in
    DoChildrenPost postaction

  method! vbehavior g =
    let rec aux g l =
      match g with
      | [] ->
        relataional_clause_list := l;
        []
      | { ext_name = "relational"; ext_kind = Ext_preds(predicate)} :: q ->
        aux q (predicate :: l)
      | h :: q ->
        h :: aux q l
    in
    let b_extended = aux g.b_extended [] in
    ChangeDoChildrenPost ({g with b_extended},fun x -> x)
end
