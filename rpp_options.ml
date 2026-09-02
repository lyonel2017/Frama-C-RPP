(**************************************************************************)
(*                                                                        *)
(*  SPDX-License-Identifier LGPL-2.1                                      *)
(*  Copyright (C)                                                         *)
(*  CEA (Commissariat à l'énergie atomique et aux énergies alternatives)  *)
(*                                                                        *)
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
