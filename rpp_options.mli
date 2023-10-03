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

module Self: Plugin.General_services

module Enabled: Parameter_sig.Bool

module Enable_only_hyp: Parameter_sig.Bool

module Enable_only_prove: Parameter_sig.Bool

module Counting_relational_verification_function: State_builder.Counter

val emitter: Emitter.t

module Counting_local_variable_verification_function: State_builder.Counter

module Counting_return_formals_verification_function: State_builder.Counter

module Counting_return_formals_verification_function_axiom: State_builder.Counter

module Counting_local_variable_copies: State_builder.Counter

module Counting_axiome: State_builder.Counter

module Counting_behavior: State_builder.Counter

module Counting_label: State_builder.Counter

module Counting_aux_local_variable: State_builder.Counter

module Is_buildin_rela_first: State_builder.Ref
  with type data = bool
