(**************************************************************************)
(*                                                                        *)
(*  SPDX-License-Identifier LGPL-2.1                                      *)
(*  Copyright (C)                                                         *)
(*  CEA (Commissariat à l'énergie atomique et aux énergies alternatives)  *)
(*                                                                        *)
(**************************************************************************)

val generat_axiom:
Cil_types.location ->
< behavior : Visitor_behavior.t;
  get_filling_actions : (unit -> unit) Queue.t; .. > ->
Cil_types.predicate ->
Cil_types.logic_label list ->
Rpp_types.logic_info ->
Rpp_types.logic_info_pure ->
Cil_types.global_annotation * string * Cil_types.toplevel_predicate

val generat_behavior_pure:
Fileloc.t ->
< behavior : Visitor_behavior.t;
  get_filling_actions : (unit -> unit) Queue.t; .. > ->
Rpp_types.logic_info_pure -> unit

val generat_behavior:
Fileloc.t ->
< behavior : Visitor_behavior.t;
  get_filling_actions : (unit -> unit) Queue.t; .. > ->
Rpp_types.logic_info -> unit

val generat_behavior_for_kf:
Cil_types.location ->
< behavior : Visitor_behavior.t;
  get_filling_actions : (unit -> unit) Queue.t; .. > ->
Rpp_types.logic_info ->
Cil_types.kernel_function * Cil_types.kernel_function ->
Cil_types.logic_var Cil_datatype.Varinfo.Map.t *
Cil_types.logic_var Cil_datatype.Varinfo.Map.t *
Cil_types.logic_var Cil_datatype.Varinfo.Map.t *
Cil_types.logic_var Cil_datatype.Varinfo.Map.t ->
unit

val generat_behavior_pure_for_kf:
Fileloc.t ->
< behavior : Visitor_behavior.t;
  get_filling_actions : (unit -> unit) Queue.t; .. > ->
Rpp_types.logic_info_pure -> Kernel_function.t * Cil_datatype.Kf.t -> unit

val generat_help_behavior_pure_for_kf:
Cil_types.location ->
(string, Cil_types.logic_info * Cil_datatype.Kf.t) Hashtbl.t list ->
Cil_types.kernel_function * Cil_datatype.Kf.t -> unit

val relationnel_axiom:
Cil_types.location ->
< behavior : Visitor_behavior.t;
  get_filling_actions : (unit -> unit) Queue.t; .. > ->
Cil_types.predicate -> Cil_types.logic_label list ->
Rpp_types.logic_info -> Rpp_types.logic_info_pure ->
Cil_types.global_annotation * Property.identified_lemma
