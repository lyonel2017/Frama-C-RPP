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

val check_is_pure_function:
  Cil_types.kernel_function -> Filepath.position -> unit

class virtual ['self] rpp_visitor : object('self)
  constraint 'a =
    < build_Toffset : 'b -> Cil_types.term_offset -> 'c;
    build_Toffset_at : 'b -> Cil_types.term_offset -> string -> 'd;
    build_call : 'b -> string -> int -> Cil_types.varinfo -> 'e list -> 'f;
    build_call_Toffset : 'b -> Cil_types.term_offset -> 'g;
    build_call_app : 'b ->
    int ->
    Cil_types.varinfo ->
    'e list -> Cil_types.logic_type -> 'e;
    build_call_binop : 'b ->
    Cil_types.binop ->
    'e -> 'e -> Cil_types.logic_type -> 'e;
    build_call_const : 'b ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> 'e;
    build_call_logic_coerce : 'b ->
    Cil_types.logic_type ->
    'e -> Cil_types.logic_type -> 'e;
    build_call_unop : 'b ->
    Cil_types.unop -> 'e -> Cil_types.logic_type -> 'e;
    build_call_valme : 'b -> 'e -> 'g -> Cil_types.logic_type -> 'e;
    build_call_valvar : 'b ->
    Cil_types.logic_var ->
    'g -> Cil_types.logic_type -> 'e;
    build_callset : 'b -> 'f list -> 'h;
    build_predicate_and : 'b -> 'i -> 'i -> 'i;
    build_predicate_app : 'b -> Cil_types.logic_info -> 'j -> 'k list -> 'i;
    build_predicate_exists : 'b -> 'l -> 'i -> 'i;
    build_predicate_false : 'b -> 'i;
    build_predicate_forall : 'b -> 'l -> 'i -> 'i;
    build_predicate_iff : 'b -> 'i -> 'i -> 'i;
    build_predicate_implies : 'b -> 'i -> 'i -> 'i;
    build_predicate_label : 'b -> Cil_types.logic_label list -> 'j;
    build_predicate_not : 'b -> 'i -> 'i;
    build_predicate_or : 'b -> 'i -> 'i -> 'i;
    build_predicate_quan : 'b -> Cil_types.quantifiers -> 'l;
    build_predicate_rel : 'b -> Cil_types.relation -> 'k -> 'k -> 'i;
    build_predicate_true : 'b -> 'i;
    build_predicate_xor : 'b -> 'i -> 'i -> 'i;
    build_rpp_predicate_forall : 'b -> 'm -> 'i -> 'n;
    build_rpp_predicate_forall_callset : 'b -> 'm -> 'h -> 'i -> 'n;
    build_rpp_predicate_implies : 'b -> 'i -> 'n;
    build_rpp_predicate_implies_callset : 'b -> 'h -> 'i -> 'n;
    build_rpp_predicate_rel : 'b -> Cil_types.relation -> 'k -> 'k -> 'n;
    build_rpp_quan : 'b -> Cil_types.quantifiers -> 'm;
    build_term_app : 'b ->
    Cil_types.logic_info ->
    'k list -> Cil_types.logic_type -> 'k;
    build_term_app_call : 'b ->
    int ->
    Cil_types.varinfo ->
    'e list -> Cil_types.logic_type -> 'k;
    build_term_app_result : 'b -> string -> Cil_types.logic_type -> 'k;
    build_term_at_mem : 'b -> 'o -> string -> Cil_types.logic_type -> 'k;
    build_term_at_var : 'b ->
    Cil_types.logic_var ->
    'c -> string -> Cil_types.logic_type -> 'k;
    build_term_binop : 'b ->
    Cil_types.binop ->
    'k -> 'k -> Cil_types.logic_type -> 'k;
    build_term_binop_at : 'b ->
    Cil_types.binop ->
    'o -> 'o -> Cil_types.logic_type -> string -> 'o;
    build_term_const : 'b ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> 'k;
    build_term_const_at : 'b ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> string -> 'o;
    build_term_logic_coerce : 'b ->
    Cil_types.logic_type ->
    'k -> Cil_types.logic_type -> 'k;
    build_term_logic_coerce_at : 'b ->
    Cil_types.logic_type ->
    'o -> Cil_types.logic_type -> string -> 'o;
    build_term_range : 'b ->
    'k option -> 'k option -> Cil_types.logic_type -> 'k;
    build_term_unop : 'b ->
    Cil_types.unop -> 'k -> Cil_types.logic_type -> 'k;
    build_term_valvar : 'b ->
    Cil_types.logic_var ->
    'c -> Cil_types.logic_type -> 'k;
    build_term_valvar_at : 'b ->
    Cil_types.logic_var ->
    'd -> Cil_types.logic_type -> string -> 'o;
    visit_call : 'b -> Cil_types.term -> 'e;
    visit_call_app : 'b ->
    int ->
    Cil_types.varinfo ->
    Cil_types.term list -> Cil_types.logic_type -> 'e;
    visit_call_binop : 'b ->
    Cil_types.binop ->
    Cil_types.term ->
    Cil_types.term -> Cil_types.logic_type -> 'e;
    visit_call_const : 'b ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> 'e;
    visit_call_logic_coerce : 'b ->
    Cil_types.logic_type ->
    Cil_types.term -> Cil_types.logic_type -> 'e;
    visit_call_term : 'b -> Cil_types.term -> 'f;
    visit_call_unop : 'b ->
    Cil_types.unop ->
    Cil_types.term -> Cil_types.logic_type -> 'e;
    visit_call_valme : 'b ->
    Cil_types.term ->
    Cil_types.term_offset -> Cil_types.logic_type -> 'e;
    visit_call_valvar : 'b ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> Cil_types.logic_type -> 'e;
    visit_calls : 'b ->
    string ->
    int -> Cil_types.varinfo -> Cil_types.term list -> 'f;
    visit_callset : 'b -> Cil_types.term list -> 'h;
    visit_callset_predicate : 'b -> Cil_types.predicate -> 'h;
    visit_predicate : 'b -> Cil_types.predicate -> 'i;
    visit_predicate_and : 'b ->
    Cil_types.predicate -> Cil_types.predicate -> 'i;
    visit_predicate_app : 'b ->
    Cil_types.logic_info ->
    Cil_types.logic_label list ->
    Cil_types.term list -> 'i;
    visit_predicate_exists : 'b ->
    Cil_types.quantifiers ->
    Cil_types.predicate -> 'i;
    visit_predicate_false : 'b -> 'i;
    visit_predicate_forall : 'b ->
    Cil_types.quantifiers ->
    Cil_types.predicate -> 'i;
    visit_predicate_iff : 'b ->
    Cil_types.predicate -> Cil_types.predicate -> 'i;
    visit_predicate_implies : 'b ->
    Cil_types.predicate ->
    Cil_types.predicate -> 'i;
    visit_predicate_not : 'b -> Cil_types.predicate -> 'i;
    visit_predicate_or : 'b ->
    Cil_types.predicate -> Cil_types.predicate -> 'i;
    visit_predicate_rel : 'b ->
    Cil_types.relation ->
    Cil_types.term -> Cil_types.term -> 'i;
    visit_predicate_true : 'b -> 'i;
    visit_predicate_xor : 'b ->
    Cil_types.predicate -> Cil_types.predicate -> 'i;
    visit_rpp_predicate : 'b -> Cil_types.predicate -> 'n;
    visit_rpp_predicate_forall : 'b ->
    Cil_types.quantifiers ->
    Cil_types.predicate -> 'n;
    visit_rpp_predicate_forall_callset : 'b ->
    Cil_types.quantifiers ->
    Cil_types.predicate ->
    Cil_types.predicate -> 'n;
    visit_rpp_predicate_implies : 'b -> Cil_types.predicate -> 'n;
    visit_rpp_predicate_implies_callset : 'b ->
    Cil_types.predicate ->
    Cil_types.predicate -> 'n;
    visit_rpp_predicate_rel : 'b ->
    Cil_types.relation ->
    Cil_types.term -> Cil_types.term -> 'n;
    visit_term : 'b -> Cil_types.term -> 'k;
    visit_term_app : 'b ->
    Cil_types.logic_info ->
    Cil_types.term list -> Cil_types.logic_type -> 'k;
    visit_term_app_call : 'b ->
    int ->
    Cil_types.varinfo ->
    Cil_types.term list -> Cil_types.logic_type -> 'k;
    visit_term_app_result : 'b -> string -> Cil_types.logic_type -> 'k;
    visit_term_at : 'b -> Cil_types.term -> string -> 'o;
    visit_term_at_mem : 'b ->
    Cil_types.term ->
    string -> Cil_types.logic_type -> 'k;
    visit_term_at_val : 'b ->
    Cil_types.logic_var ->
    Cil_types.term_offset ->
    string -> Cil_types.logic_type -> 'k;
    visit_term_binop : 'b ->
    Cil_types.binop ->
    Cil_types.term ->
    Cil_types.term -> Cil_types.logic_type -> 'k;
    visit_term_binop_at : 'b ->
    Cil_types.binop ->
    Cil_types.term ->
    Cil_types.term ->
    Cil_types.logic_type -> string -> 'o;
    visit_term_const : 'b ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> 'k;
    visit_term_const_at : 'b ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> string -> 'o;
    visit_term_logic_coerce : 'b ->
    Cil_types.logic_type ->
    Cil_types.term -> Cil_types.logic_type -> 'k;
    visit_term_logic_coerce_at : 'b ->
    Cil_types.logic_type ->
    Cil_types.term ->
    Cil_types.logic_type -> string -> 'o;
    visit_term_range : 'b ->
    Cil_types.term option ->
    Cil_types.term option -> Cil_types.logic_type -> 'k;
    visit_term_unop : 'b ->
    Cil_types.unop ->
    Cil_types.term -> Cil_types.logic_type -> 'k;
    visit_term_valvar : 'b ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> Cil_types.logic_type -> 'k;
    visit_term_valvar_at : 'b ->
    Cil_types.logic_var ->
    Cil_types.term_offset ->
    Cil_types.logic_type -> string -> 'o >

  method virtual build_Toffset : 'b -> Cil_types.term_offset -> 'c
  method virtual build_Toffset_at : 'b -> Cil_types.term_offset -> string -> 'd
  method virtual build_call : 'b -> string -> int -> Cil_types.varinfo -> 'e list -> 'f
  method virtual build_call_Toffset : 'b -> Cil_types.term_offset -> 'g
  method virtual build_call_app : 'b ->
    int ->
    Cil_types.varinfo ->
    'e list -> Cil_types.logic_type -> 'e
  method virtual build_call_binop : 'b ->
    Cil_types.binop ->
    'e -> 'e -> Cil_types.logic_type -> 'e
  method virtual build_call_const : 'b ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> 'e
  method virtual build_call_logic_coerce : 'b ->
    Cil_types.logic_type ->
    'e -> Cil_types.logic_type -> 'e
  method virtual build_call_unop : 'b ->
    Cil_types.unop -> 'e -> Cil_types.logic_type -> 'e
  method virtual build_call_valme : 'b -> 'e -> 'g -> Cil_types.logic_type -> 'e
  method virtual build_call_valvar : 'b ->
    Cil_types.logic_var ->
    'g -> Cil_types.logic_type -> 'e
  method virtual build_callset : 'b -> 'f list -> 'h
  method virtual build_predicate_and : 'b -> 'i -> 'i -> 'i
  method virtual build_predicate_app : 'b -> Cil_types.logic_info -> 'j -> 'k list -> 'i
  method virtual build_predicate_exists : 'b -> 'l -> 'i -> 'i
  method virtual build_predicate_false : 'b -> 'i
  method virtual build_predicate_forall : 'b -> 'l -> 'i -> 'i
  method virtual build_predicate_iff : 'b -> 'i -> 'i -> 'i
  method virtual build_predicate_implies : 'b -> 'i -> 'i -> 'i
  method virtual build_predicate_label : 'b -> Cil_types.logic_label list -> 'j
  method virtual build_predicate_not : 'b -> 'i -> 'i
  method virtual build_predicate_or : 'b -> 'i -> 'i -> 'i
  method virtual build_predicate_quan : 'b -> Cil_types.quantifiers -> 'l
  method virtual build_predicate_rel : 'b -> Cil_types.relation -> 'k -> 'k -> 'i
  method virtual build_predicate_true : 'b -> 'i
  method virtual build_predicate_xor : 'b -> 'i -> 'i -> 'i
  method virtual build_rpp_predicate_forall : 'b -> 'm -> 'i -> 'n
  method virtual build_rpp_predicate_forall_callset : 'b -> 'm -> 'h -> 'i -> 'n
  method virtual build_rpp_predicate_implies : 'b -> 'i -> 'n
  method virtual build_rpp_predicate_implies_callset : 'b -> 'h -> 'i -> 'n
  method virtual build_rpp_predicate_rel : 'b -> Cil_types.relation -> 'k -> 'k -> 'n
  method virtual build_rpp_quan : 'b -> Cil_types.quantifiers -> 'm
  method virtual build_term_app : 'b ->
    Cil_types.logic_info ->
    'k list -> Cil_types.logic_type -> 'k
  method virtual build_term_app_call : 'b ->
    int ->
    Cil_types.varinfo ->
    'e list -> Cil_types.logic_type -> 'k
  method virtual build_term_app_result : 'b -> string -> Cil_types.logic_type -> 'k
  method virtual build_term_at_mem : 'b -> 'o -> string -> Cil_types.logic_type -> 'k
  method virtual build_term_at_var : 'b ->
    Cil_types.logic_var ->
    'c -> string -> Cil_types.logic_type -> 'k
  method virtual build_term_binop : 'b ->
    Cil_types.binop ->
    'k -> 'k -> Cil_types.logic_type -> 'k
  method virtual build_term_binop_at : 'b ->
    Cil_types.binop ->
    'o -> 'o -> Cil_types.logic_type -> string -> 'o
  method virtual build_term_const : 'b ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> 'k
  method virtual build_term_const_at : 'b ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> string -> 'o
  method virtual build_term_logic_coerce : 'b ->
    Cil_types.logic_type ->
    'k -> Cil_types.logic_type -> 'k
  method virtual build_term_logic_coerce_at : 'b ->
    Cil_types.logic_type ->
    'o -> Cil_types.logic_type -> string -> 'o
  method virtual build_term_range : 'b ->
    'k option -> 'k option -> Cil_types.logic_type -> 'k
  method virtual build_term_unop : 'b ->
    Cil_types.unop -> 'k -> Cil_types.logic_type -> 'k
  method virtual build_term_valvar : 'b ->
    Cil_types.logic_var ->
    'c -> Cil_types.logic_type -> 'k
  method virtual build_term_valvar_at : 'b ->
    Cil_types.logic_var ->
    'd -> Cil_types.logic_type -> string -> 'o
  method visit_call : 'b -> Cil_types.term -> 'e
  method visit_call_app : 'b ->
    int ->
    Cil_types.varinfo ->
    Cil_types.term list -> Cil_types.logic_type -> 'e
  method visit_call_binop : 'b ->
    Cil_types.binop ->
    Cil_types.term ->
    Cil_types.term -> Cil_types.logic_type -> 'e
  method visit_call_const : 'b ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> 'e
  method visit_call_logic_coerce : 'b ->
    Cil_types.logic_type ->
    Cil_types.term -> Cil_types.logic_type -> 'e
  method visit_call_term : 'b -> Cil_types.term -> 'f
  method visit_call_unop : 'b ->
    Cil_types.unop ->
    Cil_types.term -> Cil_types.logic_type -> 'e
  method visit_call_valme : 'b ->
    Cil_types.term ->
    Cil_types.term_offset -> Cil_types.logic_type -> 'e
  method visit_call_valvar : 'b ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> Cil_types.logic_type -> 'e
  method visit_calls : 'b ->
    string ->
    int -> Cil_types.varinfo -> Cil_types.term list -> 'f
  method visit_callset : 'b -> Cil_types.term list -> 'h
  method visit_callset_predicate : 'b -> Cil_types.predicate -> 'h
  method visit_predicate : 'b -> Cil_types.predicate -> 'i
  method visit_predicate_and : 'b ->
    Cil_types.predicate -> Cil_types.predicate -> 'i
  method visit_predicate_app : 'b ->
    Cil_types.logic_info ->
    Cil_types.logic_label list ->
    Cil_types.term list -> 'i
  method visit_predicate_exists : 'b ->
    Cil_types.quantifiers ->
    Cil_types.predicate -> 'i
  method visit_predicate_false : 'b -> 'i
  method visit_predicate_forall : 'b ->
    Cil_types.quantifiers ->
    Cil_types.predicate -> 'i
  method visit_predicate_iff : 'b ->
    Cil_types.predicate -> Cil_types.predicate -> 'i
  method visit_predicate_implies : 'b ->
    Cil_types.predicate ->
    Cil_types.predicate -> 'i
  method visit_predicate_not : 'b -> Cil_types.predicate -> 'i
  method visit_predicate_or : 'b ->
    Cil_types.predicate -> Cil_types.predicate -> 'i
  method visit_predicate_rel : 'b ->
    Cil_types.relation ->
    Cil_types.term -> Cil_types.term -> 'i
  method visit_predicate_true : 'b -> 'i
  method visit_predicate_xor : 'b ->
    Cil_types.predicate -> Cil_types.predicate -> 'i
  method visit_rpp_predicate : 'b -> Cil_types.predicate -> 'n
  method visit_rpp_predicate_forall : 'b ->
    Cil_types.quantifiers ->
    Cil_types.predicate -> 'n
  method visit_rpp_predicate_forall_callset : 'b ->
    Cil_types.quantifiers ->
    Cil_types.predicate ->
    Cil_types.predicate -> 'n
  method visit_rpp_predicate_implies : 'b -> Cil_types.predicate -> 'n
  method visit_rpp_predicate_implies_callset : 'b ->
    Cil_types.predicate ->
    Cil_types.predicate -> 'n
  method visit_rpp_predicate_rel : 'b ->
    Cil_types.relation ->
    Cil_types.term -> Cil_types.term -> 'n
  method visit_term : 'b -> Cil_types.term -> 'k
  method visit_term_app : 'b ->
    Cil_types.logic_info ->
    Cil_types.term list -> Cil_types.logic_type -> 'k
  method visit_term_app_call : 'b ->
    int ->
    Cil_types.varinfo ->
    Cil_types.term list -> Cil_types.logic_type -> 'k
  method visit_term_app_result : 'b -> string -> Cil_types.logic_type -> 'k
  method visit_term_at : 'b -> Cil_types.term -> string -> 'o
  method visit_term_at_mem : 'b ->
    Cil_types.term ->
    string -> Cil_types.logic_type -> 'k
  method visit_term_at_val : 'b ->
    Cil_types.logic_var ->
    Cil_types.term_offset ->
    string -> Cil_types.logic_type -> 'k
  method visit_term_binop : 'b ->
    Cil_types.binop ->
    Cil_types.term ->
    Cil_types.term -> Cil_types.logic_type -> 'k
  method visit_term_binop_at : 'b ->
    Cil_types.binop ->
    Cil_types.term ->
    Cil_types.term ->
    Cil_types.logic_type -> string -> 'o
  method visit_term_const : 'b ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> 'k
  method visit_term_const_at : 'b ->
    Cil_types.logic_constant ->
    Cil_types.logic_type -> string -> 'o
  method visit_term_logic_coerce : 'b ->
    Cil_types.logic_type ->
    Cil_types.term -> Cil_types.logic_type -> 'k
  method visit_term_logic_coerce_at : 'b ->
    Cil_types.logic_type ->
    Cil_types.term ->
    Cil_types.logic_type -> string -> 'o
  method visit_term_range : 'b ->
    Cil_types.term option ->
    Cil_types.term option -> Cil_types.logic_type -> 'k
  method visit_term_unop : 'b ->
    Cil_types.unop ->
    Cil_types.term -> Cil_types.logic_type -> 'k
  method visit_term_valvar : 'b ->
    Cil_types.logic_var ->
    Cil_types.term_offset -> Cil_types.logic_type -> 'k
  method visit_term_valvar_at : 'b ->
    Cil_types.logic_var ->
    Cil_types.term_offset ->
    Cil_types.logic_type -> string -> 'o

end
