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

open Rpp_options
open Rpp_core

let run () =
  if Enabled.get() then(
    Rpp_core.print_hello "Rpp start";
    let old = Project.current () in
    let vis prj =
      (new generation_of_prouve_system prj :> Visitor.generic_frama_c_visitor)
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

let () =  Db.Main.extend run
