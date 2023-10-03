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

val make_unique_name:
?acc:int ->
String.t -> Cil_types.logic_var Cil_datatype.Logic_var.Map.t -> String.t

val predicate_visitor:
  Cil_types.predicate ->
  Rpp_types.visitor ->
  Cil_types.predicate * Cil_types.logic_label list * Rpp_types.logic_info * Rpp_types.logic_info_pure
