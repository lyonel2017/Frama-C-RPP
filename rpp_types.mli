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

class type visitor =
  object
    inherit Visitor.generic_frama_c_visitor
    method add_new_global: Cil_types.global -> unit
  end


type call_data = {
  mutable id_call: string;
  mutable return: Cil_types.varinfo option;
  mutable froms_map:  Cil_types.logic_var Cil_datatype.Varinfo.Map.t;
  mutable assigns_map: Cil_types.logic_var Cil_datatype.Varinfo.Map.t;
  mutable froms_map_p: Cil_types.logic_var Cil_datatype.Varinfo.Map.t;
  mutable assigns_map_p: Cil_types.logic_var Cil_datatype.Varinfo.Map.t ;
}

type call_data_logic = {
  mutable id: string;
  mutable logi_def_formals: Cil_types.logic_var list;
  mutable from_map_logic: Cil_types.logic_var Cil_datatype.Varinfo.Map.t;
  mutable assigns_map_logic: Cil_types.logic_var Cil_datatype.Varinfo.Map.t;
  mutable from_map_p_logic: Cil_types.logic_var Cil_datatype.Varinfo.Map.t ;
  mutable assigns_map_p_logic: Cil_types.logic_var Cil_datatype.Varinfo.Map.t ;
  mutable predicate_axiom: Cil_types.predicate_node;
  mutable return_logic: Cil_types.logic_var option;
  mutable predicate_labels: Cil_types.logic_label list;
}

type call_data_separated = {
  mutable separated_terms_axiom: Cil_types.term list;
  mutable formal_binder:  Cil_types.term Cil_datatype.Logic_var.Map.t ;
  mutable id_sep: string;
}

type inline_info = {
  mutable kf : Cil_types.kernel_function;
  mutable formal_var: Cil_types.varinfo list;
  mutable formal_exp: Cil_types.stmt list;
  mutable separated_terms: Cil_types.term list; (*TODO: move in call_data*)
  mutable id_option: string option;
  mutable inlining: int;
  mutable formals: Cil_types.varinfo list;
  mutable return_option: Cil_types.varinfo option;
  mutable locals: Cil_types.varinfo list;
  mutable formal_map: (Cil_types.exp * Cil_types.varinfo * Cil_types.term) option list;
}

type logic_info_pure = {
  mutable predicate_info_pure:
    (string, Cil_types.logic_info*Cil_types.kernel_function)
      Hashtbl.t;
}

type logic_info = {
  mutable predicate_info:
    (string, Cil_types.logic_info*Cil_types.kernel_function*
             Cil_types.varinfo list *Cil_types.varinfo list *Cil_types.varinfo list)
      Hashtbl.t;
}

type call_info = {
  mutable inline: inline_info list;
  mutable logic: logic_info;
  mutable logic_pure: logic_info_pure;
}

type rpp_env = {
  mutable loc: Cil_types.location;
  mutable proj: Project.t;
  mutable new_funct: Cil_types.fundec;
  mutable self: visitor;
  mutable proof:bool;
}

type rpp_env_axiom = {
  mutable loc_axiom: Cil_types.location;
  mutable self_axiom : visitor;
}
