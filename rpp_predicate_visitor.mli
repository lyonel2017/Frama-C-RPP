(**************************************************************************)
(*                                                                        *)
(*  SPDX-License-Identifier LGPL-2.1                                      *)
(*  Copyright (C)                                                         *)
(*  CEA (Commissariat à l'énergie atomique et aux énergies alternatives)  *)
(*                                                                        *)
(**************************************************************************)

val predicate_visitor:
  ?proof:bool ->
  Cil_types.predicate -> Cil_types.fundec ->
  Rpp_types.visitor ->
  Project.t ->
  (int * Rpp_types.logic_info * Rpp_types.logic_info_pure) list -> int ->
  Cil_types.code_annotation

val sorter :
  ('a * 'b) list -> 'a list * 'b list

val id_convert:
  string -> Cil_types.location ->
  Rpp_types.call_data list -> Cil_types.logic_builtin_label

val make_stmt_from_exp:
  (Cil_types.exp * Cil_types.varinfo * Cil_types.term) option list ->
  Cil_types.location -> Cil_types.stmt list * Cil_types.varinfo list

val function_return_type:
  Cil_types.varinfo -> Visitor_behavior.t ->
  Cil_types.location -> Cil_types.typ

val make_local:
  Cil_types.fundec ->
  Cil_types.kernel_function ->
  int -> Visitor_behavior.t ->
  Cil_types.location -> int ->
  Cil_types.varinfo list

type side_effect = {
  mutable assigns: Cil_types.varinfo list;
  mutable froms: Cil_types.varinfo list;
  mutable assigns_p: (Cil_types.term * Cil_types.varinfo) list;
  mutable assigns_p_f: (Cil_types.term * Cil_types.varinfo) list;
  mutable from_p: (Cil_types.term * Cil_types.varinfo) list;
  mutable from_p_f: (Cil_types.term * Cil_types.varinfo) list;
}

val check_function_side_effect:
  Cil_types.varinfo -> Cil_types.location -> side_effect

val pretty_effect_data:
Cil_types.varinfo ->
side_effect ->
unit

val make_unique_global_name:
  ?acc:int -> String.t -> Cil_types.varinfo list -> String.t

val make_global:
  Cil_datatype.Varinfo.Map.key list ->
  string ->
  Cil_types.logic_var Cil_datatype.Varinfo.Map.t ->
  Visitor_behavior.t ->
  Cil_types.location ->
  Cil_types.varinfo list ->
  int ->
  Cil_types.logic_var Cil_datatype.Varinfo.Map.t * Cil_types.logic_var list

val clone_killer:
  'a list -> 'a list -> ('a -> 'a -> bool) -> 'a list


class separate_checker:
  Cil_types.location -> Cil_types.term list ->
  string -> Visitor.frama_c_visitor
