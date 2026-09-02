(**************************************************************************)
(*                                                                        *)
(*  SPDX-License-Identifier LGPL-2.1                                      *)
(*  Copyright (C)                                                         *)
(*  CEA (Commissariat à l'énergie atomique et aux énergies alternatives)  *)
(*                                                                        *)
(**************************************************************************)

open Rpp_options
open Rpp_core

let run () =
  if Enabled.get() then(
    Rpp_core.print_hello "Rpp start";
    let old = Project.current () in
    let vis prj =
      (new generation_of_proof_system prj :> Visitor.generic_frama_c_visitor)
    in
    let final_project =
      File.create_project_from_visitor ~reorder:true "RP proof system" vis
    in
    Project.set_current final_project;
    File.pretty_ast ();
    Filecheck.check_ast "Rpp";
    (*main ();*)
    Project.set_current old;
    Rpp_core.print_hello "Rpp end"
  )

let () =  Boot.Main.extend run
