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

val do_one_copy:
?proof:bool ->
Kernel_function.t -> Cil_types.varinfo list -> Cil_types.varinfo option ->
Cil_types.varinfo list -> Datatype.String.Map.key option ->
(Cil_types.logic_var Cil_datatype.Varinfo.Map.t *
 Cil_types.logic_var Cil_datatype.Varinfo.Map.t *
 Cil_types.logic_var Cil_datatype.Varinfo.Map.t *
 Cil_types.logic_var Cil_datatype.Varinfo.Map.t) ->
int -> Cil_types.fundec ->
Rpp_types.visitor -> Project.t ->
Cil_types.location ->
(int * Rpp_types.logic_info * Rpp_types.logic_info_pure) list -> int ->
Cil_types.block

val do_one_require_copy:
Kernel_function.t -> Cil_types.varinfo list ->
Datatype.String.Map.key option ->
(Cil_types.logic_var Cil_datatype.Varinfo.Map.t *
 Cil_types.logic_var Cil_datatype.Varinfo.Map.t *
 Cil_types.logic_var Cil_datatype.Varinfo.Map.t *
 Cil_types.logic_var Cil_datatype.Varinfo.Map.t) ->
Rpp_types.visitor -> Project.t ->
Cil_types.funbehavior list

val sort_funbehavior: Cil_types.behavior list -> Cil_types.identified_predicate list

val do_one_terms_vis: Kernel_function.t ->
Cil_types.varinfo list ->
Cil_types.varinfo list ->
Datatype.String.Map.key option ->
Rpp_types.call_data list ->
Rpp_types.visitor -> Cil_types.term ->
Cil_types.term

val do_one_terms_vis_axiom:
String.t ->
Rpp_types.call_data_logic list ->
Cil_types.term Cil_datatype.Logic_var.Map.t ->
Rpp_types.visitor ->
Cil_types.term ->
Cil_types.term

val do_one_simpl_term_vis:
Kernel_function.t ->
Cil_types.logic_var list ->
'a option ->
Cil_types.logic_var Cil_datatype.Varinfo.Map.t *
Cil_types.logic_var Cil_datatype.Varinfo.Map.t *
Cil_types.logic_var Cil_datatype.Varinfo.Map.t *
Cil_types.logic_var Cil_datatype.Varinfo.Map.t ->
< behavior : Visitor_behavior.t; .. > -> Cil_types.term -> Cil_types.term

val do_one_require_vis:
< behavior : Visitor_behavior.t; .. > ->
Cil_types.fundec ->
Cil_types.varinfo list ->
('a * Cil_types.varinfo * Cil_types.term) option list ->
Cil_types.kernel_function ->
Cil_types.identified_predicate list ->
Cil_types.identified_predicate list
