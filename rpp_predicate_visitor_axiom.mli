(**************************************************************************)
(*                                                                        *)
(*  SPDX-License-Identifier LGPL-2.1                                      *)
(*  Copyright (C)                                                         *)
(*  CEA (Commissariat à l'énergie atomique et aux énergies alternatives)  *)
(*                                                                        *)
(**************************************************************************)

val make_unique_name:
?acc:int ->
String.t -> Cil_types.logic_var Cil_datatype.Logic_var.Map.t -> String.t

val predicate_visitor:
  Cil_types.predicate ->
  Rpp_types.visitor ->
  Cil_types.predicate * Cil_types.logic_label list * Rpp_types.logic_info * Rpp_types.logic_info_pure
