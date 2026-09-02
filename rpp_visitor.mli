(**************************************************************************)
(*                                                                        *)
(*  SPDX-License-Identifier LGPL-2.1                                      *)
(*  Copyright (C)                                                         *)
(*  CEA (Commissariat à l'énergie atomique et aux énergies alternatives)  *)
(*                                                                        *)
(**************************************************************************)

val check_is_pure_function:
  Cil_types.kernel_function -> Filepos.t -> unit

class virtual ['env, 'call_data, 'callset, 'relprop] rpp_visitor : object

  method virtual build_Toffset:
    'env -> Cil_types.term_offset -> Cil_types.term_offset
  method virtual build_Toffset_at : 'env ->
    Cil_types.term_offset -> string -> Cil_types.term_offset
  method virtual build_call :
    'env -> string -> int -> Cil_types.varinfo -> Cil_types.term list ->
    'call_data
  method virtual build_call_Toffset :
    'env -> Cil_types.term_offset -> Cil_types.term_offset
  method virtual build_call_app : 'env ->
    int ->
    Cil_types.varinfo ->
    Cil_types.term list -> Cil_types.logic_type -> Cil_types.term
  method virtual build_call_binop : 'env ->
    Cil_types.binop ->
    Cil_types.term -> Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method virtual build_call_const : 'env ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> Cil_types.term
  method virtual build_call_logic_coerce : 'env ->
    Cil_types.logic_type ->
    Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method virtual build_call_unop : 'env ->
    Cil_types.unop -> Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method virtual build_call_valme :
    'env -> Cil_types.term ->
    Cil_types.term_offset -> Cil_types.logic_type -> Cil_types.term
  method virtual build_call_valvar : 'env ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> Cil_types.logic_type -> Cil_types.term
  method virtual build_callset : 'env -> 'call_data list -> 'callset
  method virtual build_predicate_and :
    'env -> Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_app :
    'env -> Cil_types.logic_info ->
    Cil_types.logic_label list -> Cil_types.term list -> Cil_types.predicate
  method virtual build_predicate_exists :
    'env -> Cil_types.quantifiers -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_false : 'env -> Cil_types.predicate
  method virtual build_predicate_forall :
    'env -> Cil_types.quantifiers -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_iff :
    'env -> Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_implies :
    'env -> Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_label :
    'env -> Cil_types.logic_label list -> Cil_types.logic_label list
  method virtual build_predicate_not :
    'env -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_or :
    'env -> Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_predicate_quan :
    'env -> Cil_types.quantifiers -> Cil_types.quantifiers
  method virtual build_predicate_rel :
    'env ->
    Cil_types.relation ->
    Cil_types.term -> Cil_types.term -> Cil_types.predicate
  method virtual build_predicate_true : 'env -> Cil_types.predicate
  method virtual build_predicate_xor :
    'env -> Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method virtual build_rpp_predicate_forall :
    'env -> Cil_types.quantifiers -> Cil_types.predicate -> 'relprop
  method virtual build_rpp_predicate_forall_callset :
    'env -> Cil_types.quantifiers -> 'callset -> Cil_types.predicate -> 'relprop
  method virtual build_rpp_predicate_implies :
    'env -> Cil_types.predicate -> 'relprop
  method virtual build_rpp_predicate_implies_callset :
    'env -> 'callset -> Cil_types.predicate -> 'relprop
  method virtual build_rpp_predicate_rel :
    'env -> Cil_types.relation -> Cil_types.term -> Cil_types.term -> 'relprop
  method virtual build_rpp_quan :
    'env -> Cil_types.quantifiers -> Cil_types.quantifiers
  method virtual build_term_app : 'env ->
    Cil_types.logic_info ->
    Cil_types.term list -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_app_call : 'env ->
    int ->
    Cil_types.varinfo ->
    Cil_types.term list -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_app_result :
    'env -> string -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_at_mem :
    'env -> Cil_types.term -> string -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_at_var : 'env ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> string -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_binop : 'env ->
    Cil_types.binop ->
    Cil_types.term -> Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_binop_at : 'env ->
    Cil_types.binop ->
    Cil_types.term ->
    Cil_types.term -> Cil_types.logic_type -> string -> Cil_types.term
  method virtual build_term_const : 'env ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> Cil_types.term
  method virtual build_term_const_at : 'env ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> string -> Cil_types.term
  method virtual build_term_logic_coerce : 'env ->
    Cil_types.logic_type ->
    Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_logic_coerce_at : 'env ->
    Cil_types.logic_type ->
    Cil_types.term -> Cil_types.logic_type -> string -> Cil_types.term
  method virtual build_term_range : 'env ->
    Cil_types.term option -> Cil_types.term option ->
    Cil_types.logic_type -> Cil_types.term
  method virtual build_term_unop : 'env ->
    Cil_types.unop -> Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_valvar : 'env ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> Cil_types.logic_type -> Cil_types.term
  method virtual build_term_valvar_at : 'env ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> Cil_types.logic_type -> string -> Cil_types.term
  method visit_call : 'env -> Cil_types.term -> Cil_types.term
  method visit_call_app : 'env ->
    int ->
    Cil_types.varinfo ->
    Cil_types.term list -> Cil_types.logic_type -> Cil_types.term
  method visit_call_binop : 'env ->
    Cil_types.binop ->
    Cil_types.term ->
    Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method visit_call_const : 'env ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> Cil_types.term
  method visit_call_logic_coerce : 'env ->
    Cil_types.logic_type ->
    Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method visit_call_term : 'env -> Cil_types.term -> 'call_data
  method visit_call_unop : 'env ->
    Cil_types.unop ->
    Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method visit_call_valme : 'env ->
    Cil_types.term ->
    Cil_types.term_offset -> Cil_types.logic_type -> Cil_types.term
  method visit_call_valvar : 'env ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> Cil_types.logic_type -> Cil_types.term
  method visit_calls : 'env ->
    string ->
    int -> Cil_types.varinfo -> Cil_types.term list -> 'call_data
  method visit_callset : 'env -> Cil_types.term list -> 'callset
  method visit_callset_predicate : 'env -> Cil_types.predicate -> 'callset
  method visit_predicate : 'env -> Cil_types.predicate -> Cil_types.predicate
  method visit_predicate_and : 'env ->
    Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method visit_predicate_app : 'env ->
    Cil_types.logic_info ->
    Cil_types.logic_label list ->
    Cil_types.term list -> Cil_types.predicate
  method visit_predicate_exists : 'env ->
    Cil_types.quantifiers ->
    Cil_types.predicate -> Cil_types.predicate
  method visit_predicate_false : 'env -> Cil_types.predicate
  method visit_predicate_forall : 'env ->
    Cil_types.quantifiers ->
    Cil_types.predicate -> Cil_types.predicate
  method visit_predicate_iff : 'env ->
    Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method visit_predicate_implies : 'env ->
    Cil_types.predicate ->
    Cil_types.predicate -> Cil_types.predicate
  method visit_predicate_not : 'env -> Cil_types.predicate -> Cil_types.predicate
  method visit_predicate_or : 'env ->
    Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method visit_predicate_rel : 'env ->
    Cil_types.relation ->
    Cil_types.term -> Cil_types.term -> Cil_types.predicate
  method visit_predicate_true : 'env -> Cil_types.predicate
  method visit_predicate_xor : 'env ->
    Cil_types.predicate -> Cil_types.predicate -> Cil_types.predicate
  method visit_rpp_predicate : 'env -> Cil_types.predicate -> 'relprop
  method visit_rpp_predicate_forall : 'env ->
    Cil_types.quantifiers ->
    Cil_types.predicate -> 'relprop
  method visit_rpp_predicate_forall_callset : 'env ->
    Cil_types.quantifiers ->
    Cil_types.predicate ->
    Cil_types.predicate -> 'relprop
  method visit_rpp_predicate_implies : 'env -> Cil_types.predicate -> 'relprop
  method visit_rpp_predicate_implies_callset : 'env ->
    Cil_types.predicate ->
    Cil_types.predicate -> 'relprop
  method visit_rpp_predicate_rel : 'env ->
    Cil_types.relation ->
    Cil_types.term -> Cil_types.term -> 'relprop
  method visit_term : 'env -> Cil_types.term -> Cil_types.term
  method visit_term_app : 'env ->
    Cil_types.logic_info ->
    Cil_types.term list -> Cil_types.logic_type -> Cil_types.term
  method visit_term_app_call : 'env ->
    int ->
    Cil_types.varinfo ->
    Cil_types.term list -> Cil_types.logic_type -> Cil_types.term
  method visit_term_app_result :
    'env -> string -> Cil_types.logic_type -> Cil_types.term
  method visit_term_at : 'env -> Cil_types.term -> string -> Cil_types.term
  method visit_term_at_mem : 'env ->
    Cil_types.term ->
    string -> Cil_types.logic_type -> Cil_types.term
  method visit_term_at_val : 'env ->
    Cil_types.logic_var ->
    Cil_types.term_offset ->
    string -> Cil_types.logic_type -> Cil_types.term
  method visit_term_binop : 'env ->
    Cil_types.binop ->
    Cil_types.term ->
    Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method visit_term_binop_at : 'env ->
    Cil_types.binop ->
    Cil_types.term ->
    Cil_types.term ->
    Cil_types.logic_type -> string -> Cil_types.term
  method visit_term_const : 'env ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> Cil_types.term
  method visit_term_const_at : 'env ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> string -> Cil_types.term
  method visit_term_logic_coerce : 'env ->
    Cil_types.logic_type ->
    Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method visit_term_logic_coerce_at : 'env ->
    Cil_types.logic_type ->
    Cil_types.term ->
    Cil_types.logic_type -> string -> Cil_types.term
  method visit_term_range : 'env ->
    Cil_types.term option ->
    Cil_types.term option -> Cil_types.logic_type -> Cil_types.term
  method visit_term_unop : 'env ->
    Cil_types.unop ->
    Cil_types.term -> Cil_types.logic_type -> Cil_types.term
  method visit_term_valvar : 'env ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> Cil_types.logic_type -> Cil_types.term
  method visit_term_valvar_at : 'env ->
    Cil_types.logic_var ->
    Cil_types.term_offset ->
    Cil_types.logic_type -> string -> Cil_types.term

end
