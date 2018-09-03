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

open Cil_types
open Cil
open Rpp_types

(**
   Visitor for coping function bodies
*)
class aux_visitor vis_beh var_ret = object(self)
  inherit Visitor.generic_frama_c_visitor(vis_beh)

  val stmt_hashtb = Hashtbl.create 3

  (*Return statment are replaced by an affectation to the local variable
    ("var_ret") used in the proof of the relational property*)
  method! vstmt_aux s =
    (*Set the statement to origine status to avoid the visitor to lose
      the binding with the statement annotation: it is not the best
      solution but it work => find beter solution for the futur*)
    let s =  Cil.get_original_stmt self#behavior s in
    match (s.skind, s.labels) with
    | Return (Some e,l),[] ->
      let var_ret = match var_ret with
        |None -> let (loc,_) = l in
          Rpp_options.Self.fatal ~source:loc
            "Function is supposed to return something, but no return variable have been created"
        | Some x -> x
      in
      let return_lval =
        (Var(var_ret),NoOffset)
      in
      let new_stmt =
        Cil.mkStmt ~valid_sid:true (Instr(Set(return_lval,e,l)))
      in
      ChangeDoChildrenPost(new_stmt, fun x -> x)

    | Return (None,l), [] ->
      let _var_ret = match var_ret with
        | None -> None
        | Some _ -> let (loc,_) = l in
          Rpp_options.Self.fatal ~source:loc
            "Function is supposed to return nothing, but a return variable have been created"
      in
      let new_stmt =
        Cil.mkEmptyStmt ~valid_sid:true ()
      in
      ChangeDoChildrenPost(new_stmt, fun x -> x)


    | Return (None,_), h::[] ->
      (match h with
       | Label(name,l,b) ->
         begin
           let new_stmt = (try (Hashtbl.find stmt_hashtb name) with
               | Not_found ->
                 let new_name =
                   String.concat "_" [name;"label";
                                      string_of_int (Rpp_options.Counting_label.next ())]
                 in
                 let _var_ret = match var_ret with
                   | None -> None
                   | Some _ -> let (loc,_) = l in
                     Rpp_options.Self.fatal ~source:loc
                       "Function is supposed to return nothing, but a \
                        return variable have been created"
                 in
                 let new_stmt =
                   Cil.mkEmptyStmt ~valid_sid:true ()
                 in
                 new_stmt.labels <-[Label(new_name,l,b)];
                 Hashtbl.add stmt_hashtb name new_stmt;
                 new_stmt)
           in
           ChangeDoChildrenPost(new_stmt, fun x -> x)
         end

       | _ -> Rpp_options.Self.abort "Juste Label in Goto are supported yet")

    | Goto(target,_), [] ->
      (match (!target.skind,!target.labels) with
       | Return (Some e,_),h::[] ->
         (match h with
          | Label(name,l,b) ->
            let new_stmt = (try (Hashtbl.find stmt_hashtb name ) with
                | Not_found ->
                  (let new_name =
                     String.concat "_" [name;"label";
                                        string_of_int (Rpp_options.Counting_label.next ())]
                   in
                   let var_ret = match var_ret with
                     |None -> let (loc,_) = l in
                       Rpp_options.Self.fatal ~source:loc
                         "Function is supposed to return something, but no return \
                          variable have been created"
                     | Some x -> x
                   in
                   let return_lval =
                     (Var(var_ret),NoOffset)
                   in
                   let new_stmt =
                     Cil.mkStmt ~valid_sid:true (Instr(Set(return_lval,e,l)))
                   in
                   new_stmt.labels <-[Label(new_name,l,b)];
                   Hashtbl.add stmt_hashtb name new_stmt;
                   new_stmt))
            in
            let goto_stmt = Cil.mkStmt ~valid_sid:true (Goto((ref new_stmt),l)) in
            ChangeTo goto_stmt

          | _ -> Rpp_options.Self.abort "Juste Label in Goto are supported yet")

       | Return (None,_), h::[] ->
         (match h with
          | Label(name,l,b) ->
            begin
              let new_stmt = (try (Hashtbl.find stmt_hashtb name) with
                  | Not_found ->
                    let new_name =
                      String.concat "_" [name;"label";
                                         string_of_int (Rpp_options.Counting_label.next ())]
                    in
                    let _var_ret = match var_ret with
                      | None -> None
                      | Some _ -> let (loc,_) = l in
                        Rpp_options.Self.fatal ~source:loc
                          "Function is supposed to return nothing, but a \
                           return variable have been created"
                    in
                    let new_stmt =
                      Cil.mkEmptyStmt ~valid_sid:true ()
                    in
                    new_stmt.labels <-[Label(new_name,l,b)];
                    Hashtbl.add stmt_hashtb name new_stmt;
                    new_stmt)
              in
              let goto_stmt = Cil.mkStmt ~valid_sid:true (Goto((ref new_stmt),l)) in
              ChangeTo goto_stmt
            end
          | _ -> Rpp_options.Self.abort "Juste Label in Goto are supported yet")

       | _, h::[] ->
         (match h with
          | Label(name,l,b) ->
            let new_stmt = (try (Hashtbl.find stmt_hashtb name ) with
                | Not_found ->
                  (let new_name =
                     String.concat "_" [name;"label";
                                        string_of_int (Rpp_options.Counting_label.next ())]
                   in
                   let new_stmt =
                     Cil.mkStmt ~valid_sid:true (!target.skind)
                   in
                   new_stmt.labels <-[Label(new_name,l,b)];
                   Hashtbl.add stmt_hashtb name new_stmt;
                   new_stmt))
            in

            let goto_stmt = Cil.mkStmt ~valid_sid:true (Goto((ref new_stmt),l)) in
            ChangeTo goto_stmt

          | _ -> Rpp_options.Self.abort "Juste Label in Goto are supported yet")
       | _ -> Rpp_options.Self.abort "Juste one Label in Goto are supported")

    (* UnspecifiedSequence are not really in the scope of relational property verification,
       so they are replaced by block. *)
    | UnspecifiedSequence l,[] ->
      let b = Cil.block_from_unspecified_sequence l in
      ChangeDoChildrenPost (Cil.mkStmt ~valid_sid:true (Block b), fun x-> x)

    | _,[] ->
      ChangeDoChildrenPost(Cil.mkStmt ~valid_sid:true s.skind, fun x -> x)

    | kind, h::[] ->
      (match (kind,h) with
       | Goto(_,_),Label(_,l_label,_) -> let (loc,_) = l_label in
         Rpp_options.Self.abort ~source:loc " Label on goto are not supported yet"
       | Return (Some e,l),Label(name,_,b) ->
         let new_stmt = (try (Hashtbl.find stmt_hashtb name) with
             | Not_found ->
               (let new_name =
                  String.concat "_" [name;"label";
                                     string_of_int (Rpp_options.Counting_label.next ())]
                in
                let var_ret = match var_ret with
                  |None -> let (loc,_) = l in
                    Rpp_options.Self.fatal ~source:loc
                      "Function is supposed to return something, but no \
                       return variable have been created"
                  | Some x -> x
                in
                let return_lval = (Var(var_ret),NoOffset) in
                let new_stmt =
                  Cil.mkStmt ~valid_sid:true (Instr(Set(return_lval,e,l)))
                in
                new_stmt.labels <-[Label(new_name,l,b)];
                Hashtbl.add stmt_hashtb name new_stmt;
                new_stmt))
         in
         ChangeDoChildrenPost(new_stmt, fun x -> x)
       | Return (None,l), Label(name,_,b) ->
         let new_stmt = (try (Hashtbl.find stmt_hashtb name) with
             | Not_found ->
               let new_name =
                 String.concat "_" [name;"label";
                                    string_of_int (Rpp_options.Counting_label.next ())]
               in
               let _var_ret = match var_ret with
                 | None -> None
                 | Some _ -> let (loc,_) = l in
                   Rpp_options.Self.fatal ~source:loc
                     "Function is supposed to return nothing, but a \
                      return variable have been created"
               in
               let new_stmt =
                 Cil.mkEmptyStmt ~valid_sid:true ()
               in
               new_stmt.labels <-[Label(new_name,l,b)];
               Hashtbl.add stmt_hashtb name new_stmt;
               new_stmt)
         in
         ChangeDoChildrenPost(new_stmt, fun x -> x)

       | _, Label(name,l,b) ->
         let new_stmt = (try (Hashtbl.find stmt_hashtb name) with
             | Not_found ->
               (let new_name =
                  String.concat "_" [name;"label";
                                     string_of_int (Rpp_options.Counting_label.next ())]
                in
                let new_stmt =
                  Cil.mkStmt ~valid_sid:true kind
                in
                new_stmt.labels <-[Label(new_name,l,b)];
                Hashtbl.add stmt_hashtb name new_stmt;
                new_stmt))
         in
         ChangeDoChildrenPost(new_stmt, fun x ->x )

       | _ -> Rpp_options.Self.abort "Juste Label are supported yet")

    | _ ,_::_ -> Rpp_options.Self.abort "Multiple labels on a stmt are no supported yet"

end

(**
   Visitor for coping \requires clauses
*)
class aux_visitor_2 vis_beh = object(_)
  inherit Visitor.generic_frama_c_visitor(vis_beh)

  method! vbehavior b =
    match b.b_requires with
    | [] -> ChangeDoChildrenPost(Cil.mk_behavior ~name:b.b_name (), fun x -> x)
    | _ ->
      let new_funbehavior =
        Cil.mk_behavior ~name:b.b_name ~assumes: b.b_assumes ~requires: b.b_requires ()
      in
      ChangeDoChildrenPost(new_funbehavior, fun x -> x)
end

(**
   Visitor for transforming require predicate into predicate juste with the formals of the function
*)
class aux_visitor_3 vis_beh l_v_list ?(quan=[]) formal_map = object(_)
  inherit Visitor.generic_frama_c_visitor(vis_beh)

  val test = ref false

  val quant = ref quan

  method! vpredicate _ =
    DoChildrenPost(fun x -> if not(!test) then (test := true;Logic_const.ptrue) else x)

  method! vpredicate_node p =
    match p with
    | Pforall(q,_) ->
      let inter = !quant in
      quant := q @ !quant;
      DoChildrenPost(fun x -> quant := inter; if not(!test) then (test := true;Ptrue) else x)

    | Pand(a,b) ->
      let vis =
        new aux_visitor_3 vis_beh l_v_list formal_map ~quan:!quant
      in
      let new_a =
        Visitor.visitFramacPredicate vis a
      in
      let new_b =
        Visitor.visitFramacPredicate vis b
      in
      begin
        match new_a.pred_content,new_b.pred_content with
        | Ptrue,Ptrue -> test := true;Cil.ChangeTo Ptrue
        | _,Ptrue -> test := true;Cil.ChangeTo new_a.pred_content
        | Ptrue,_ -> test := true;Cil.ChangeTo new_b.pred_content
        | _, _ -> test := true;Cil.ChangeTo (Pand(new_a,new_b))
      end

    | Prel _ | Pseparated _ | Pvalid _ | Pimplies _ | Pvalid_read _ |Pnot _
      -> DoChildrenPost(fun x -> if not(!test) then (test := true;Ptrue) else x)

    | _ -> Rpp_options.Self.abort
             "Unsupported predicate in requires clause:@. @[%a@] @."
             Printer.pp_predicate_node p

  method! vterm t =
    let rec aux lv data =
      match data with
      | Some(_,v,new_t)::_ when (Cil.cvar_to_lvar v).lv_id == lv.lv_id  ->
        ChangeDoChildrenPost(new_t,fun x->x)
      | _::q  -> aux lv q
      | [] -> DoChildren
    in
    match t.term_node with
    | TLval(TVar(l_v),_) -> aux l_v formal_map
    | _ -> DoChildren

  method! vlogic_var_use l =
    let rec aux2 lv data =
      match data with
      | h::_ when h.lv_id == (Cil.get_original_logic_var vis_beh lv).lv_id  ->
        DoChildrenPost(fun x -> test:=true; x)
      | _::q  -> aux2 lv q
      | [] -> test:= false; DoChildrenPost(fun x -> x)
    in
    let rec aux lv data =
      match data with
      | h::_ when (Cil.cvar_to_lvar h).lv_id == lv.lv_id  ->
        DoChildrenPost(fun x -> test:=true; x)
      | _::q  -> aux lv q
      | [] -> aux2 lv !quant
    in aux l l_v_list

end

class aux_visitor_5 vis_behavior = object
  inherit Visitor.generic_frama_c_visitor(vis_behavior)

  method! vbehavior g =
    let rec aux g  =
      match g with
      | [] -> []
      | (_,"relational",Ext_preds(_)) :: q -> aux q
      | h :: q -> h :: aux q
    in
    let b_extended = aux g.b_extended
    in ChangeDoChildrenPost ({g with b_extended},fun x -> x)
end

class aux_visitor_6 vis_beh = object(_)
  inherit Visitor.generic_frama_c_visitor(vis_beh)

  method! vterm t =
    match t.term_node with
    | TLval(TMem(t_aux),TNoOffset) ->
      ChangeDoChildrenPost(t_aux, fun x -> x)
    | TLval(TMem(_),_) ->
      let (l,_) = t.term_loc in
      Rpp_options.Self.abort ~source:l
        "Unsupported term in separate generation:@. @[%a@] @."
        Printer.pp_term t

    | _ -> DoChildren
end

class aux_visitor_7 vis_beh formals_map = object(self)
  inherit Visitor.generic_frama_c_visitor(vis_beh)

  method! vterm t =
    match t.term_node with
    | TLval(TMem(t_aux),TNoOffset) ->
      self#vterm t_aux
    | TLval(TMem(_),_) ->
      let (l,_) = t.term_loc in
      Rpp_options.Self.abort ~source:l
        "Unsupported term in separate generation:@. @[%a@] @."
        Printer.pp_term t

    (* Use "\let in" in the future if more support is require*)

    | TLval(TVar(log),TNoOffset) ->
      begin
        match Cil_datatype.Logic_var.Map.find log formals_map with
        | exception Not_found -> ChangeDoChildrenPost(t, fun x -> x)
        | term ->
          ChangeDoChildrenPost(term, fun x -> x)
      end
    | TLval(TVar(log),off) ->
      begin
        match Cil_datatype.Logic_var.Map.find log formals_map with
        | exception Not_found -> ChangeDoChildrenPost(t, fun x -> x)
        | {term_node = TLval(a,off_sub)} as term ->
          let new_offset = Logic_const.addTermOffset off off_sub in
          let new_term =
            {term with term_node = TLval(a,new_offset)}
          in
          ChangeDoChildrenPost(new_term, fun x -> x)
        | term ->
          let (l,_) = term.term_loc in
          Rpp_options.Self.abort ~source:l
            "Unsupported term in separate generation.\
             Term to replace:@. @[%a@] @.\
             by @. @[%a@] @."
            Printer.pp_term t Printer.pp_term term
      end
    | _ -> ChangeDoChildrenPost(t, fun x -> x)
end

let global_binder_aux map self log_map log_map_orig =
  Cil_datatype.Varinfo.Map.iter
    (fun vo data ->
       begin
         match Cil_datatype.Logic_var.Map.find (Cil.cvar_to_lvar vo) !log_map with
         | exception Not_found ->
           log_map := Cil_datatype.Logic_var.Map.add
               (Cil.cvar_to_lvar vo)
               (Cil.cvar_to_lvar (Cil.get_varinfo self#behavior vo)) !log_map;
         | _ -> ()
       end;
       Cil.unset_logic_var self#behavior (Cil.cvar_to_lvar vo);
       Cil.set_logic_var self#behavior
         (Cil.cvar_to_lvar vo) data;

       begin
         match Cil_datatype.Logic_var.Map.find (Cil.cvar_to_lvar vo) !log_map_orig with
         | exception Not_found ->
           log_map_orig := Cil_datatype.Logic_var.Map.add
               (Cil.cvar_to_lvar vo)
               (Cil.cvar_to_lvar (Cil.get_original_varinfo self#behavior vo))
               !log_map_orig;
         | _ -> ()
       end;
       Cil.unset_orig_logic_var self#behavior (Cil.cvar_to_lvar vo);
       Cil.set_orig_logic_var self#behavior
         data (Cil.cvar_to_lvar vo)) map

let binder_aux f apply id self global_map =
  let log_map = ref Cil_datatype.Logic_var.Map.empty in
  let log_map_orig = ref Cil_datatype.Logic_var.Map.empty in

  (*Make the binding for the globale variable*)
  begin
    match id with
    | None ->  ()
    | Some _ ->
      begin
        let (from_map,assert_map,from_p_map,assert_p_map) =
          global_map
        in
        global_binder_aux assert_map self log_map log_map_orig;
        global_binder_aux from_map self log_map log_map_orig;
        global_binder_aux from_p_map self log_map log_map_orig;
        global_binder_aux assert_p_map self log_map log_map_orig;
      end
  end;

  let data = f apply in

  Cil_datatype.Logic_var.Map.iter (fun a b ->
      Cil.unset_logic_var self#behavior a;
      Cil.set_logic_var self#behavior
        a b) !log_map;

  Cil_datatype.Logic_var.Map.iter (fun a b ->
      Cil.unset_orig_logic_var self#behavior a;
      Cil.set_orig_logic_var self#behavior
        a b) !log_map_orig;

  data

let global_binder map self var_map var_map_orig log_map log_map_orig =
  Cil_datatype.Varinfo.Map.iter
    (fun vo data ->
       match  data with
       | {lv_origin = Some(var)} ->
         begin
           match Cil_datatype.Varinfo.Map.find vo !var_map with
           | exception Not_found ->
             var_map := Cil_datatype.Varinfo.Map.add vo
                 (Cil.get_varinfo self#behavior vo)
                 !var_map;
           | _ -> ()
         end;
         Cil.unset_varinfo self#behavior vo;
         Cil.set_varinfo self#behavior vo var;

         begin
           match Cil_datatype.Varinfo.Map.find vo !var_map_orig with
           | exception Not_found ->
             var_map_orig := Cil_datatype.Varinfo.Map.add vo
                 (Cil.get_original_varinfo self#behavior vo)
                 !var_map_orig;
           | _ -> ()
         end;
         Cil.unset_orig_varinfo self#behavior vo;
         Cil.set_orig_varinfo self#behavior var vo;

         begin
           match Cil_datatype.Logic_var.Map.find (Cil.cvar_to_lvar vo) !log_map with
           | exception Not_found ->
             log_map := Cil_datatype.Logic_var.Map.add
                 (Cil.cvar_to_lvar vo)
                 (Cil.cvar_to_lvar (Cil.get_varinfo self#behavior vo)) !log_map;
           | _ -> ()
         end;
         Cil.unset_logic_var self#behavior (Cil.cvar_to_lvar vo);
         Cil.set_logic_var self#behavior
           (Cil.cvar_to_lvar vo) (Cil.cvar_to_lvar var);

         begin
           match Cil_datatype.Logic_var.Map.find (Cil.cvar_to_lvar vo) !log_map_orig with
           | exception Not_found ->
             log_map_orig := Cil_datatype.Logic_var.Map.add
                 (Cil.cvar_to_lvar vo)
                 (Cil.cvar_to_lvar (Cil.get_original_varinfo self#behavior vo))
                 !log_map_orig;
           | _ -> ()
         end;
         Cil.unset_orig_logic_var self#behavior (Cil.cvar_to_lvar vo);
         Cil.set_orig_logic_var self#behavior
           (Cil.cvar_to_lvar var) (Cil.cvar_to_lvar vo);

       | _ -> assert false) map

let binder_no_local_logic f apply id self formalsinit formalsi global_map =
  let log_map = ref Cil_datatype.Logic_var.Map.empty in
  let log_map_orig = ref Cil_datatype.Logic_var.Map.empty in

  (*Make the binding for the formals*)
  assert (List.length formalsinit = List.length formalsi);
  List.iter2
    (fun a b ->
       log_map := Cil_datatype.Logic_var.Map.add
           (Cil.cvar_to_lvar a)
           (Cil.cvar_to_lvar (Cil.get_varinfo self#behavior a)) !log_map;
       Cil.unset_logic_var self#behavior (Cil.cvar_to_lvar a);
       Cil.set_logic_var self#behavior
         (Cil.cvar_to_lvar a) b)
    formalsinit formalsi;

  List.iter2
    (fun a b ->
       log_map_orig := Cil_datatype.Logic_var.Map.add
           (Cil.cvar_to_lvar b)
           (Cil.cvar_to_lvar (Cil.get_original_varinfo self#behavior b))
           !log_map_orig;
       Cil.unset_orig_logic_var self#behavior a;
       Cil.set_orig_logic_var self#behavior
         a (Cil.cvar_to_lvar b))
    formalsi formalsinit;

  (*Make the binding for the globale variable*)
  begin
    match id with
    | None ->  ()
    | Some _ ->
      begin
        let (from_map,assert_map,from_p_map,assert_p_map) =
          global_map
        in
        global_binder_aux assert_map self log_map log_map_orig;
        global_binder_aux from_map self log_map log_map_orig;
        global_binder_aux from_p_map self log_map log_map_orig;
        global_binder_aux assert_p_map self log_map log_map_orig;
      end
  end;

  let data = f apply in

  Cil_datatype.Logic_var.Map.iter (fun a b ->
      Cil.unset_logic_var self#behavior a;
      Cil.set_logic_var self#behavior
        a b) !log_map;

  Cil_datatype.Logic_var.Map.iter (fun a b ->
      Cil.unset_orig_logic_var self#behavior a;
      Cil.set_orig_logic_var self#behavior
        a b) !log_map_orig;
  data

let binder_sub f apply id self formalsinit formalsi global_map =
  let var_map = ref Cil_datatype.Varinfo.Map.empty in
  let log_map = ref Cil_datatype.Logic_var.Map.empty in
  let var_map_orig = ref Cil_datatype.Varinfo.Map.empty in
  let log_map_orig = ref Cil_datatype.Logic_var.Map.empty in

  (*Make the binding for the formals*)
  assert (List.length formalsinit = List.length formalsi);
  List.iter2 (fun x y ->
      var_map := Cil_datatype.Varinfo.Map.add x
          (Cil.get_varinfo self#behavior x) !var_map;
      Cil.unset_varinfo self#behavior x;
      Cil.set_varinfo self#behavior x y ) formalsinit formalsi;

  List.iter2 (fun x y ->
      var_map_orig := Cil_datatype.Varinfo.Map.add y
          (Cil.get_original_varinfo self#behavior y)
          !var_map_orig;
      Cil.unset_orig_varinfo self#behavior x;
      Cil.set_orig_varinfo self#behavior x y) formalsi formalsinit;

  List.iter2
    (fun a b ->
       log_map := Cil_datatype.Logic_var.Map.add
           (Cil.cvar_to_lvar a)
           (Cil.cvar_to_lvar (Cil.get_varinfo self#behavior a)) !log_map;
       Cil.unset_logic_var self#behavior (Cil.cvar_to_lvar a);
       Cil.set_logic_var self#behavior
         (Cil.cvar_to_lvar a) (Cil.cvar_to_lvar b))
    formalsinit formalsi;

  List.iter2
    (fun a b ->
       log_map_orig := Cil_datatype.Logic_var.Map.add
           (Cil.cvar_to_lvar b)
           (Cil.cvar_to_lvar (Cil.get_original_varinfo self#behavior b))
           !log_map_orig;
       Cil.unset_orig_logic_var self#behavior (Cil.cvar_to_lvar a);
       Cil.set_orig_logic_var self#behavior
         (Cil.cvar_to_lvar a) (Cil.cvar_to_lvar b))
    formalsi formalsinit;

  (*Make the binding for the globale variable*)
  begin
    match id with
    | None ->  ()
    | Some _ ->
      begin
        let (from_map,assert_map,from_p_map,assert_p_map) =
          global_map
        in
        global_binder assert_map self var_map var_map_orig log_map log_map_orig;
        global_binder from_map self var_map var_map_orig log_map log_map_orig;
        global_binder from_p_map self var_map var_map_orig log_map log_map_orig;
        global_binder assert_p_map self var_map var_map_orig log_map log_map_orig;
      end
  end;

  let data = f apply in

  Cil_datatype.Varinfo.Map.iter ( fun x y ->
      Cil.unset_varinfo self#behavior x;
      Cil.set_varinfo self#behavior
        x y) !var_map;

  Cil_datatype.Logic_var.Map.iter (fun a b ->
      Cil.unset_logic_var self#behavior a;
      Cil.set_logic_var self#behavior
        a b) !log_map;

  Cil_datatype.Varinfo.Map.iter ( fun x y ->
      Cil.unset_orig_varinfo self#behavior x;
      Cil.set_orig_varinfo self#behavior
        x y) !var_map_orig;

  Cil_datatype.Logic_var.Map.iter (fun a b ->
      Cil.unset_orig_logic_var self#behavior a;
      Cil.set_orig_logic_var self#behavior
        a b) !log_map_orig;
  data


let binder f apply funct id self locals formalsi global_map =

  let var_map = ref Cil_datatype.Varinfo.Map.empty in
  let log_map = ref Cil_datatype.Logic_var.Map.empty in
  let var_map_orig = ref Cil_datatype.Varinfo.Map.empty in
  let log_map_orig = ref Cil_datatype.Logic_var.Map.empty in

  (*Make the binding for the formals*)
  assert (List.length funct.sformals = List.length formalsi);
  List.iter2 (fun x y ->
      var_map := Cil_datatype.Varinfo.Map.add x
          (Cil.get_varinfo self#behavior x) !var_map;
      Cil.unset_varinfo self#behavior x;
      Cil.set_varinfo self#behavior x y ) funct.sformals formalsi;

  List.iter2 (fun x y ->
      var_map_orig := Cil_datatype.Varinfo.Map.add y
          (Cil.get_original_varinfo self#behavior y)
          !var_map_orig;
      Cil.unset_orig_varinfo self#behavior x;
      Cil.set_orig_varinfo self#behavior x y) formalsi funct.sformals;

  List.iter2
    (fun a b ->
       log_map := Cil_datatype.Logic_var.Map.add
           (Cil.cvar_to_lvar a)
           (Cil.cvar_to_lvar (Cil.get_varinfo self#behavior a)) !log_map;
       Cil.unset_logic_var self#behavior (Cil.cvar_to_lvar a);
       Cil.set_logic_var self#behavior
         (Cil.cvar_to_lvar a) (Cil.cvar_to_lvar b))
    funct.sformals formalsi;

  List.iter2
    (fun a b ->
       log_map_orig := Cil_datatype.Logic_var.Map.add
           (Cil.cvar_to_lvar b)
           (Cil.cvar_to_lvar (Cil.get_original_varinfo self#behavior b))
           !log_map_orig;
       Cil.unset_orig_logic_var self#behavior (Cil.cvar_to_lvar a);
       Cil.set_orig_logic_var self#behavior
         (Cil.cvar_to_lvar a) (Cil.cvar_to_lvar b))
    formalsi funct.sformals;

  (*Make the binding for the locals*)
  assert (List.length funct.slocals = List.length locals);
  List.iter2 (fun x y ->
      var_map := Cil_datatype.Varinfo.Map.add x
          (Cil.get_varinfo self#behavior x) !var_map;
      Cil.unset_varinfo self#behavior x;
      Cil.set_varinfo self#behavior x y ) funct.slocals locals;

  List.iter2 (
    fun x y ->
      var_map_orig := Cil_datatype.Varinfo.Map.add y
          (Cil.get_original_varinfo self#behavior y)
          !var_map_orig;
      Cil.unset_orig_varinfo self#behavior x;
      Cil.set_orig_varinfo self#behavior x y) locals funct.slocals;

  List.iter2
    (fun a b ->
       log_map := Cil_datatype.Logic_var.Map.add
           (Cil.cvar_to_lvar a)
           (Cil.cvar_to_lvar (Cil.get_varinfo self#behavior a)) !log_map;
       Cil.unset_logic_var self#behavior (Cil.cvar_to_lvar a);
       Cil.set_logic_var self#behavior
         (Cil.cvar_to_lvar a) (Cil.cvar_to_lvar b))
    funct.slocals locals;

  List.iter2
    (fun a b ->
       log_map_orig := Cil_datatype.Logic_var.Map.add
           (Cil.cvar_to_lvar b)
           (Cil.cvar_to_lvar (Cil.get_original_varinfo self#behavior b))
           !log_map_orig;
       Cil.unset_orig_logic_var self#behavior (Cil.cvar_to_lvar a);
       Cil.set_orig_logic_var self#behavior
         (Cil.cvar_to_lvar a) (Cil.cvar_to_lvar b))
    locals funct.slocals;

  (*Make the binding for the globale variable*)
  begin
    match id with
    | None ->  ()
    | Some _ ->
      begin
        let (from_map,assert_map,from_p_map,assert_p_map) =
          global_map
        in
        global_binder assert_map self var_map var_map_orig log_map log_map_orig;
        global_binder from_map self var_map var_map_orig log_map log_map_orig;
        global_binder from_p_map self var_map var_map_orig log_map log_map_orig;
        global_binder assert_p_map self var_map var_map_orig log_map log_map_orig;
      end
  end;

  let data = f apply in

  Cil_datatype.Varinfo.Map.iter ( fun x y ->
      Cil.unset_varinfo self#behavior x;
      Cil.set_varinfo self#behavior
        x y) !var_map;

  Cil_datatype.Logic_var.Map.iter (fun a b ->
      Cil.unset_logic_var self#behavior a;
      Cil.set_logic_var self#behavior
        a b) !log_map;

  Cil_datatype.Varinfo.Map.iter ( fun x y ->
      Cil.unset_orig_varinfo self#behavior x;
      Cil.set_orig_varinfo self#behavior
        x y) !var_map_orig;

  Cil_datatype.Logic_var.Map.iter (fun a b ->
      Cil.unset_orig_logic_var self#behavior a;
      Cil.set_orig_logic_var self#behavior
        a b) !log_map_orig;
  data

(**
   Function for making substitution in behavior
*)
let do_one_behavior_vis kf formalsi id global_map self annot =
  let f p =
    let vis = new aux_visitor_5 self#behavior in
    Visitor.visitFramacBehaviors vis p
  in
  let formalsinit = Kernel_function.get_formals kf in
  let terms =
    binder_sub f annot id self formalsinit formalsi global_map
  in
  terms

class aux_visitor_4 vis current add_global id global_map proj annot_data loc num =
  object(self)
    inherit Visitor.generic_frama_c_visitor (vis#behavior)

    method private add_new_func vi decl =
      let spec = Cil.empty_funspec () in
      Globals.Functions.replace_by_declaration spec vi decl;
      add_global (GFunDecl(spec,vi,decl))

    method private add_rela_func rename new_kf current_kf =
      List.iter (fun (pred,log,log_pure) ->
          if not(num = pred) || rename then
            begin
              Rpp_axiomatic_generator.generat_behavior_for_kf
                loc self log (new_kf,Cil.get_kernel_function vis#behavior current_kf)
                global_map;
              Rpp_axiomatic_generator.generat_behavior_pure_for_kf
                loc self log_pure (new_kf,Cil.get_kernel_function vis#behavior current_kf)
            end
          else ();
        ) annot_data;

    method private add_rela_pure_func v rename new_kf current_kf =
      List.iter (fun (pred,log,log_pure) ->
          if not(num = pred) || rename then
            begin
              Rpp_axiomatic_generator.generat_behavior_pure_for_kf
                loc self log_pure (new_kf,Cil.get_kernel_function vis#behavior current_kf);
              Rpp_axiomatic_generator.generat_behavior_for_kf
                loc self log (new_kf,Cil.get_kernel_function vis#behavior current_kf)
                global_map;
            end
          else ();
        )annot_data;
      let log_pure =
        List.fold_left (fun acc (pred,_,x) ->
            if not(num = pred) || rename then
              x.predicate_info_pure :: acc
            else
              acc
          ) [] annot_data
      in
      let exists = List.exists(fun x ->
          let find = ref false in
          Hashtbl.iter(fun _ (_,kf) ->
              find := !find || (String.equal (Kernel_function.get_name kf) v.vname);
            ) x;
          !find;
        ) log_pure
      in
      begin
        match exists with
        | true -> Rpp_axiomatic_generator.generat_help_behavior_pure_for_kf
                    loc log_pure (new_kf,Cil.get_kernel_function vis#behavior current_kf);
        | _ -> ()
      end;

    method private replace_func id v rename exp1 expl return l s name =
      let aux vari =
        try Globals.Functions.get vari with
        | Not_found ->  Rpp_options.Self.fatal
                          "Can not found the kernel function  %a"
                          Printer.pp_varinfo vari
        | _ -> assert false
      in
      match  Globals.Functions.find_by_name name with
      | exception Not_found ->
        let new_vi =
          Cil.makeVarinfo
            ~source:false ~temp:false true false name (v.vtype)
        in
        self#add_new_func new_vi v.vdecl;
        let new_kf= try Globals.Functions.get new_vi with
          | Not_found ->  Rpp_options.Self.fatal
                            "Can not found the new kernel function  %a"
                            Printer.pp_varinfo new_vi
          | _ -> assert false
        in
        let annot,current_kf =
          Project.on proj (
            fun x ->
              let x = aux x in
              let beha = Annotations.behaviors ~populate:false x in
              (beha,x)
          ) (Cil.get_original_varinfo vis#behavior v)
        in
        let formalsi = Kernel_function.get_formals new_kf in
        let annot =
          do_one_behavior_vis current_kf formalsi id global_map self annot
        in
        Annotations.add_behaviors
          ~register_children:true (Rpp_options.emitter) new_kf annot;
        begin
          match id with
          | Some _ ->
            self#add_rela_func rename new_kf current_kf
          | None ->
            self#add_rela_pure_func v rename new_kf current_kf;
        end;
        let new_exp = {exp1 with enode = Lval(Var(new_vi),NoOffset)} in
        s.skind <- Instr(Call(return,new_exp,expl,l));
        s

      | kf ->
        let current_kf =
          Project.on proj (
            fun x ->
              aux x
          ) (Cil.get_original_varinfo vis#behavior v)
        in
        begin
          match id with
          | Some _ ->
            self#add_rela_func rename kf current_kf
          | None ->
            self#add_rela_pure_func v rename kf current_kf;
        end;
        let new_exp =
          {exp1 with enode = Lval(Var(Globals.Functions.get_vi kf),NoOffset)}
        in
        s.skind <- Instr(Call(return,new_exp,expl,l));
        s

    method private is_inlined v =
      match current with
      | None -> false
      | Some fonct ->
        begin
          let funct =
            Kernel_function.get_definition fonct
          in
          let vo = Cil.get_varinfo self#behavior funct.svar in
          Cil_datatype.Varinfo.equal v vo
        end

    method! vstmt_aux s =
      match s.skind with
      | Instr(Call(return,exp1,expl,l)) ->
        begin
          match exp1.enode with
          | Lval(Var(v),NoOffset) ->
            begin
              let rename =
                self#is_inlined v
              in
              match id with
              | Some id ->
                let name =
                  String.concat "_" [v.vname;id]
                in
                let new_s =
                  self#replace_func
                    (Some id) v rename exp1 expl return l s name
                in
                Cil.ChangeDoChildrenPost(new_s, fun x->x)

              | None ->
                let name =
                  String.concat "_"
                    [v.vname;"aux";string_of_int num]
                in
                let new_s =
                  self#replace_func
                    None v rename exp1 expl return l s name
                in
                Cil.ChangeDoChildrenPost(new_s, fun x->x)
            end
          | _ ->
            let (l,_) = loc in
            Rpp_options.Self.abort ~source:l
              "Function pointers are not supported: %a @."
              Printer.pp_stmt s
        end
      | _ -> Cil.ChangeDoChildrenPost(s,fun x->x)
  end

(**
   Function for making substitution in term
*)
let do_one_terms_vis_axiom id global_map formal_map self terms =
  let global_map =
    let data =
      List.find (fun x -> String.equal (x.id) id)
        global_map
    in
    (data.from_map_logic,data.assigns_map_logic,data.from_map_p_logic,data.assigns_map_p_logic)
  in
  let f p =
    let vis = new aux_visitor_7 self#behavior formal_map in
    Visitor.visitFramacTerm vis p
  in
  let terms =
    binder_aux f terms (Some id) self global_map
  in
  terms

(**
   Function for making substitution in term
*)
let do_one_simpl_term_vis kf formalsi id global_map self term =
  let f t =
    let vis = new Visitor.generic_frama_c_visitor(self#behavior) in
    Visitor.visitFramacTerm vis t
  in
  let formalsinit = Kernel_function.get_formals kf in
  let terms =
    binder_no_local_logic f term id self formalsinit formalsi global_map
  in
  terms

(**
   Function for making substitution in term
*)
let do_one_terms_vis kf formalsi locals id global_map self terms=

  let funct = Kernel_function.get_definition  kf in
  let global_map =
    match id with
    | None ->
      let map =
        Cil_datatype.Varinfo.Map.empty
      in
      (map,map,map,map)
    | Some id ->
      let data =
        List.find (fun x -> String.equal (x.id_call) id)
          global_map
      in
      (data.froms_map,data.assigns_map,data.froms_map_p,data.assigns_map_p)
  in
  let f p =
    let vis = new aux_visitor_6 self#behavior in
    vis#set_current_func funct;
    vis#set_current_kf kf;
    Visitor.visitFramacTerm vis p
  in
  let terms =
    binder f terms funct id self locals formalsi global_map
  in
  terms

(**
   Function for making one copy of terms
*)
let do_one_require_copy kf formalsi id global_map self proj=
  let f p =
    let vis = new aux_visitor_2 self#behavior in
    let beh =
      Project.on proj (Visitor.visitFramacBehaviors vis) p
    in
    beh
  in
  match kf.fundec with
  | Declaration (_,_,param,_) ->
    begin
      match param with
      | None | Some [] -> []
      | Some formalsinit ->
        let beh =
          binder_sub
            f ((Annotations.behaviors ~populate:false kf)) id self formalsinit formalsi global_map
        in
        beh
    end
  | Definition (funct,_) ->
    begin
      let beh =
        binder_sub
          f ((Annotations.behaviors ~populate:false kf)) id self funct.sformals formalsi global_map
      in
      beh
    end

(**
   Function returning the type refering to the new project
*)
let rec get_typ_in_current_project t self loc=
  match t with
  | TVoid(_) -> t
  | TInt(_) -> t
  | TFloat(_) -> t
  | TPtr(t,a) -> let new_t = get_typ_in_current_project t self loc in TPtr(new_t,a)
  | TArray(t,e,b,a) -> let new_t = get_typ_in_current_project t self loc in TArray(new_t,e,b,a)
  | TFun(_) ->  Rpp_options.Self.abort ~source:loc
                  "Error in predicate: Function types are not supported yet"
  | TNamed (t,a) -> let new_c = Cil.get_typeinfo self t in TNamed(new_c,a)
  | TComp (c,b,a) ->let new_c = Cil.get_compinfo self c in TComp(new_c,b,a)
  | TEnum (e,a) -> let new_e = Cil.get_enuminfo self e in TEnum(new_e,a)
  | TBuiltin_va_list(_) -> t

(**
   Function making a copie of the local variable of copie funct for new_funct
*)
let make_local new_funct copie_funct i self loc =
  let rec aux locals i acc =
    match locals with
    | [] -> acc
    | h :: q ->
      let name =
        String.concat "_" [h.vname; string_of_int i ]
      in
      let old_blk_vi = new_funct.sbody.blocals in
      let varinfo =
        Cil.makeLocalVar new_funct name (get_typ_in_current_project h.vtype self loc)
      in
      varinfo.vdefined <- h.vdefined;
      new_funct.sbody.blocals <- old_blk_vi;
      aux q i (varinfo:: acc)
  in
  List.rev(aux copie_funct.slocals i [])

(**
   Function for sorting the require clause from the copy of behaviors
*)
let sort_funbehavior funbehavior =
  let rec aux funbe acc =
    match funbe with
    | [] -> acc
    | h :: q -> if Cil.is_default_behavior h then aux q (h.b_requires @ acc)
      else (
        if List.length h.b_requires == 0 then aux q acc else
          Rpp_options.Self.abort
            "Require clauses are only supported in default behaviour\
             (Require clause exist in %s)" h.b_name
      )
  in aux funbehavior []

(**
   Function detecting if a function is variadic
*)
let is_variadic_function vi = match vi.vtype with
  | TFun(_, _, is_v, _) -> is_v
  | _ -> false

(**
   Function detecting the function to be inlined and call the inline function
*)
let inliner self proj funct id global_map = object (_)
  inherit Visitor.frama_c_inplace

  method !vstmt_aux stmt =
    match stmt.skind with
    | Instr(Call(return,
                 { enode = Lval(Var vi, NoOffset)} ,
                 args,
                 loc)) ->
      begin
        if is_variadic_function vi then
          begin
            Rpp_options.Self.warning ~current:true ~once:true
              "Variadic function call are not\
               supported:@ @[%a@] @." Printer.pp_stmt stmt;
            Cil.DoChildrenPost(fun _-> stmt)
          end
        else
          begin
            let aux vari =
              try Globals.Functions.get vari with
              | Not_found ->  Rpp_options.Self.fatal
                                "Can not found the kernel function:@ @[%a@] @."
                                Printer.pp_varinfo vari
              | _ -> assert false
            in
            let kf =
              Project.on proj (
                fun x ->
                  aux x
              ) (Cil.get_original_varinfo self#behavior vi)
            in
            let inline_funct =
              match Kernel_function.get_definition kf with
              | exception _ -> Rpp_options.Self.fatal
                                 "Can not found the definition of function:@ @[%a@] @."
                                 Printer.pp_varinfo vi
              | x -> x
            in
            let _,loc = loc in
            let locals =
              make_local
                (funct) inline_funct
                (Rpp_options.Counting_local_variable_copies.next()) self#behavior loc
            in

            let formals, initializers =
              (* Formals become locals of the new block. They are initialized to the
                 corresponding argument. *)
              try
                List.fold_left2
                  (fun (vars, inits) h exp ->
                     let name =
                       String.concat "_"
                         ["aux_local_variable";
                          string_of_int (Rpp_options.Counting_aux_local_variable.next())]
                     in
                     let old_blk_vi = funct.sbody.blocals in
                     let vi' =
                       Cil.makeLocalVar
                         funct name (get_typ_in_current_project h.vtype self#behavior loc)
                     in
                     funct.sbody.blocals <- old_blk_vi;
                     let init =
                       Cil.mkStmtOneInstr ~valid_sid:true
                         (Set ((Var vi', NoOffset), exp, exp.eloc))
                     in
                     vi' :: vars, init :: inits)
                  ([], []) inline_funct.sformals
                  args
              with Invalid_argument _ ->
                Rpp_options.Self.fatal "inliner: undetected variadic function call:@ @[%a@] @."
                  Printer.pp_varinfo vi
            in
            let resi =
              match return with
              | Some ((Var(v),NoOffset)) -> Some v
              | Some (x) ->
                Rpp_options.Self.fatal "Unsupported return variable in inlier:@ @[%a@] @."
                  Printer.pp_lval x
              | None -> None
            in
            let f p =
              (*Save the current new kf and make a binding with the wrapper
                function for code annotation generation*)
              let buffer_kf = Cil.get_kernel_function self#behavior kf in
              Cil.set_kernel_function self#behavior
                kf
                (Globals.Functions.get (funct.svar));
              let vis = new aux_visitor self#behavior resi in
              vis#set_current_func inline_funct;
              vis#set_current_kf kf;
              let bodys = funct.sbody in
              let locals = funct.slocals in
              let formals = funct.sformals in
              let body =
                Project.on proj (Visitor.visitFramacBlock vis) p
              in
              funct.sbody <- bodys;
              funct.slocals <- locals;
              funct.sformals <- formals;
              (*Make binding for reversing the last binding with the kf*)
              Cil.set_kernel_function self#behavior
                kf
                buffer_kf;
              body
            in
            let body =
              binder f (inline_funct.sbody) inline_funct id self locals formals global_map
            in
            let inline_body = Cil.mkBlock [(Cil.mkStmt ~valid_sid:true (Block body))] in
            let first_stmt = List.hd (inline_body.bstmts) in
            inline_body.blocals <- formals;
            inline_body.bstmts <- initializers @ inline_body.bstmts;

            (*The body include some assert clauses corresponding to requires clauses*)
            (*Copy of require clauses and transformation to assert clause*)
            let behaviours =
              do_one_require_copy
                kf formals id global_map self proj
            in
            let requires =
              sort_funbehavior behaviours
            in
            List.iter(fun data ->
                let the_code_annotation =
                  Logic_const.new_code_annotation (AAssert ([],(Logic_const.pred_of_id_pred data)))
                in
                Annotations.add_code_annot
                  Rpp_options.emitter ~kf:(Globals.Functions.get (funct.svar))
                  first_stmt
                  the_code_annotation
              )requires;
            Cil.DoChildrenPost(fun _ -> Cil.mkStmt ~valid_sid:true (Block inline_body))
          end
      end
    | Instr(Call(_)) ->
      Rpp_options.Self.warning ~current:true
        "Function pointer are not\
         supported:@ @[%a@] @." Printer.pp_stmt stmt;
      Cil.DoChildren

    | _ -> Cil.DoChildren
end


(**
   Function for making one copy of the body of kf
*)
let do_one_copy ?(proof=false) kf formalsi resi locals id global_map inline new_funct self proj l annot_data num =
  match inline with
  | 0 ->
    begin
      let return_lval = match resi with
        | None -> None
        | Some x -> Some(Var(x),NoOffset)
      in
      let current_kf = Cil.get_kernel_function self#behavior kf in
      let var_funct = match current_kf.fundec with
        | Definition (f,_) -> f.svar
        | Declaration (_,v,_,_) -> v
      in
      let new_exp_node =
        Lval(Var(var_funct),NoOffset)
      in
      let new_exp =
        Cil.new_exp l new_exp_node
      in
      let params =
        List.map (fun x -> Cil.new_exp l (Lval(Var(x),NoOffset)))
          formalsi
      in
      let k = Instr(Call(return_lval, new_exp, params, l))
      in
      let s = Cil.mkStmt ~valid_sid:true k
      in
      let b = {battrs = [];
               bscoping = true;
               blocals = [];
               bstatics = [];
               bstmts = [s]}
      in
      if not proof then
        begin
          let funct_vis = new aux_visitor_4
            self None self#add_new_global
            id global_map proj annot_data l num
          in
          Visitor.visitFramacBlock funct_vis b
        end
      else
        b
    end

  | n ->
    begin
      let funct = Kernel_function.get_definition kf in

      let f p =
        (*Save the current new kf and make a binding with the wrapper
          function for code annotation generation*)
        let buffer_kf = Cil.get_kernel_function self#behavior kf in

        Cil.set_kernel_function self#behavior
          kf
          (Globals.Functions.get (new_funct.svar));

        let vis = new aux_visitor (self#behavior) resi in
        vis#set_current_func funct;
        vis#set_current_kf kf;
        let bodys = new_funct.sbody in
        let locals = new_funct.slocals in
        let formals = new_funct.sformals in
        let body =
          Project.on proj (Visitor.visitFramacBlock vis) p
        in
        new_funct.sbody <- bodys;
        new_funct.slocals <- locals;
        new_funct.sformals <- formals;
        (*Make binding for reversing the last binding with the kf*)
        Cil.set_kernel_function self#behavior
          kf
          buffer_kf;
        body
      in
      let body =
        binder f (funct.sbody) funct id self locals formalsi global_map
      in
      (**
             Inlining all function
      *)

      let rec aux b i =
        match i with
        | 0 -> b
        | k ->
          let vis =
            inliner self proj new_funct id global_map
          in
          let block =
            Visitor.visitFramacBlock vis b
          in
          aux block (k - 1)
      in
      let new_body = aux body (n - 1) in
      if not proof then
        begin
          let funct_vis = new aux_visitor_4
            self (Some kf)
            self#add_new_global
            id global_map proj annot_data l num
          in
          funct_vis#set_current_func new_funct;
          funct_vis#set_current_kf (Globals.Functions.get (new_funct.svar));
          let new_body = Visitor.visitFramacBlock funct_vis new_body in
          new_body
        end
      else new_body
    end
