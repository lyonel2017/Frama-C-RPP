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

let rpp_selector
    (popup_factory:GMenu.menu GMenu.factory) _ ~button: _ localizable =
  match localizable with
  | _  ->
    let callback () =
      let vis prj =
        (new Rpp_core.generation_of_prouve_system prj :>
           Visitor.frama_c_visitor)
      in
      let final_project =
        File.create_project_from_visitor ~reorder:true "RP proof system" vis
      in
      Project.set_current final_project;
      Ast.clear_last_decl();
      File.reorder_ast();
      File.pretty_ast ();
      Filecheck.check_ast "Rpp";

    in ignore(popup_factory#add_item "Rpp" ~callback)

let main_gui main_ui = main_ui#register_source_selector rpp_selector

let () =
  Design.register_extension main_gui

