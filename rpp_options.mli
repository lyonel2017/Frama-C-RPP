(**************************************************************************)
(*                                                                        *)
(*  SPDX-License-Identifier LGPL-2.1                                      *)
(*  Copyright (C)                                                         *)
(*  CEA (Commissariat à l'énergie atomique et aux énergies alternatives)  *)
(*                                                                        *)
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
