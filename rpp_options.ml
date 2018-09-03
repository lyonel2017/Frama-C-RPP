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

module Self = Plugin.Register(struct
    let name = "RPP"
    let shortname = "rpp"
    let help = "Prove relationel properties"
  end)

module Enabled = Self.False(struct
    let option_name = "-rpp"
    let help = "when on (off by default), prove relationnel properties and generate the correspnding logical definition."
  end)

module Enable_only_hyp = Self.False(struct
    let option_name = "-rpp-hyp"
    let help = "when on (off by default), only generate the logical defintion of the relational proprerties."
  end)

module Enable_only_prove = Self.False(struct
    let option_name = "-rpp-pro"
    let help = "when on (off by default), only generate the code transformation for relational proprerties proof."
  end)

module Counting_relational_verification_function = State_builder.Counter
    (struct
      let name = "Count_relational_verify_function"
    end)

let emitter =
  Emitter.create "Rpp" [Emitter.Code_annot;Emitter.Funspec;Emitter.Global_annot;Emitter.Property_status]
    ~correctness:[] ~tuning: []

module Counting_local_variable_verification_function = State_builder.Counter
    (struct
      let name = "Counting_local_variable_verification_function"
    end)

module Counting_return_formals_verification_function = State_builder.Counter
    (struct
      let name = "Counting_return_formals_verification_function"
    end)

module Counting_return_formals_verification_function_axiom = State_builder.Counter
    (struct
      let name = "Counting_return_formals_verification_function_axiom"
    end)

module Counting_local_variable_copies = State_builder.Counter
    (struct
      let name = "Counting_local_variable_copies"
    end)

module Counting_axiome = State_builder.Counter
    (struct
      let name = "Counting_axiome"
    end)

module Counting_behavior = State_builder.Counter
    (struct
      let name = "Counting_behavior"
    end)

module Counting_label = State_builder.Counter
    (struct
      let name = "Counting_labes"
    end)

module Counting_aux_local_variable = State_builder.Counter
    (struct
      let name = "Counting_aux_local_variable"
    end)

module Is_buildin_rela_first =
  State_builder.Ref
    (Datatype.Bool)
    (struct
      let name = "Is_buildin_rela_first"
      let dependencies = []
      let default () = true
    end)
