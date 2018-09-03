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

open Filecheck
open Cil_types

let fun_type_param p =
  match p.vtype with
  | TFun (_,Some t,_,_) -> t
  | TFun (_,None,_,_) ->  []
  | _ -> assert false;;

let fun_type_return p =
  match p.vtype with
  | TFun (t,_,_,_) -> t
  | _ -> assert false;;

let id_checker identifier loc id_hash =
  match identifier with
  | FormalLabel(s) ->
    ( match Str.bounded_split (Str.regexp "_") s 2 with
      | "Pre":: id :: [] | "Post" :: id :: []->
        let _ = (try (Hashtbl.find id_hash id) with
            | Not_found -> Rpp_options.Self.fatal ~source:loc  "Unknown label: @ @[%s@] @." s
            | _ -> assert false)
        in true
      | _ -> false)
  |  _ ->  false

let id_update identifier loc id_hash  =
  match identifier with
  | FormalLabel(s) ->
    (match Str.bounded_split (Str.regexp "_") s 2 with
     | "Pre":: id :: [] ->
       let _ = try (Hashtbl.find id_hash id) with
         | Not_found -> Rpp_options.Self.fatal ~source:loc"Unknown label: @ @[%s@]  @." s
         | _ -> assert false
       in
       BuiltinLabel(Pre)
     | "Post" :: id :: []->
       let _ = try (Hashtbl.find id_hash id) with
         | Not_found -> Rpp_options.Self.fatal ~source:loc "Unknown label: @ @[%s@]  @." s
         | _ -> assert false
       in
       BuiltinLabel(Here)
     | _ -> identifier)
  | _ -> identifier

let check_param_type param funct loc=
  List.iter2 (fun x (_,t,_) ->
      match x.term_type with
      | Ctype(ty) ->
        if Cil_datatype.Typ.equal t ty then ()
        else
          Rpp_options.Self.fatal ~source:loc
            "Cast are not supported:@. @[%a and %a are not \
             compatible@] for term @[%a@] in callpure of %s @."
            (Printer.pp_logic_type)  x.term_type
            (Printer.pp_typ) t (Printer.pp_term) x (funct.vname)
      | Linteger ->
        begin match t with
          | TInt _ -> ()
          | _ -> Rpp_options.Self.fatal ~source: loc
                   "Cast are not supported:@. @[%a and %a are not compatible@] \
                    for term @[%a@] in callpure of %s @."
                   (Printer.pp_logic_type)  x.term_type (Printer.pp_typ) t
                   Printer.pp_term x (funct.vname)
        end
      | Lreal ->
        begin match t with
          | TFloat _ -> ()
          | _ -> Rpp_options.Self.fatal ~source: loc
                   "Cast are not supported:@. @[%a and %a are not compatible@] \
                    for term @[%a@] in callpure of %s @."
                   (Printer.pp_logic_type)  x.term_type (Printer.pp_typ) t
                   Printer.pp_term x (funct.vname)
        end
      | _ -> Rpp_options.Self.fatal ~source:loc
               "Function %s is called with a parameter with type \
                is not a C type:@. @[%a@] @." (funct.vname) Printer.pp_term x
    ) param (fun_type_param funct)

let rpp_extend_checker check =
  let module Origin = (val check: Extensible_checker) in

  let module New_check =
  struct
    class check  ?is_normalized id = object(self)
      inherit Origin.check ?is_normalized id as super

      val id_hash = Hashtbl.create 3

      method! vterm t =
        let (loc,_) = t.term_loc in
        match t.term_node with
        | Tapp({l_var_info={lv_name ="\\callpure"}},[],terms) ->
          begin
            match terms with
            | {term_node = TConst (Integer(_,_))} :: q ->
              begin
                match q with
                | {term_node=TLval(TVar({lv_origin=Some(x)}),TNoOffset)} :: p ->
                  begin
                    match x with
                    | {vtype=TFun(_)} ->
                      check_param_type p x loc;
                      if Cil_datatype.Logic_type.equal (t.term_type) (Ctype(fun_type_return x)) then ()
                      else
                        begin
                        Rpp_options.Self.fatal ~source:loc
                           "\\callpure type (@[%a@]) is different from result type \
                            of function @[%a@] (@[%a@]):@.@[%a@]"
                          Printer.pp_logic_type (t.term_type) Printer.pp_varinfo x
                          Printer.pp_logic_type (Ctype(fun_type_return x))
                          (Printer.pp_term) t
                        end;
                      Cil.DoChildren
                    | _ ->  Rpp_options.Self.fatal ~source:loc
                             "Expected a function as seconde parameter::@. @[%a@] @."
                             (Printer.pp_term) t
                  end
                | _ ->  Rpp_options.Self.fatal ~source:loc
                          "Expected a logical variable as seconde parameter :@. @[%a@] @."
                         (Printer.pp_term) t
              end
            | _ ->  Rpp_options.Self.fatal ~source:loc
                      "Expected an integer for first parameter:@. @[%a@] @."
                      (Printer.pp_term) t
          end

        | Tapp({l_var_info={lv_name ="\\call"}},[],terms) ->
          begin
          match terms with
           |{term_node =TConst(LStr(s))} :: k ->
             begin
             match  Hashtbl.find id_hash s with
              | exception Not_found ->
                begin
                  match k with
                 | {term_node = TConst (Integer(_,_))} :: q ->
                   begin
                     match q with
                     | {term_node=TLval(TVar({lv_origin=Some(x)}),TNoOffset)} :: p ->
                       begin
                         match x with
                         | {vtype=TFun(_)} ->
                          check_param_type p x loc;
                          Hashtbl.add id_hash s x;
                          Cil.DoChildren
                         | _ ->  Rpp_options.Self.fatal ~source:loc
                                   "Expected a function as thrid parameter:@. @[%a@] @."
                                   (Printer.pp_term) t
                       end
                     | _ -> Rpp_options.Self.fatal ~source:loc
                              "Expected a logical variable as third parameter:@. @[%a@] @."
                              (Printer.pp_term) t
                   end
                 | _ -> Rpp_options.Self.fatal ~source:loc
                          "Expected an integer for seconde parameter:@. @[%a@] @."
                          (Printer.pp_term) t
                end
              | _ -> Rpp_options.Self.fatal ~source:loc
                       "Multiple use of identifier %s @." s
             end
           | _ -> Rpp_options.Self.fatal ~source:loc
                    "Expected an string for first parameter (identifier):@. @[%a@] @."
                    (Printer.pp_term) t
          end

        | Tapp({l_var_info={lv_name ="\\callresult"}},[],terms) ->
          if (List.length terms) <> 1 then
            Rpp_options.Self.fatal ~source:loc
              "\\callresult contain more then one parameter:@. @[%a@] @."
              (Printer.pp_term) t
          else
            let term = List.hd terms in
            begin
              match term.term_node with
              | TConst (LStr(s)) ->
                let v = (try (Hashtbl.find id_hash s) with
                    | Not_found -> Rpp_options.Self.fatal ~source:loc
                                     "Unknown identifier %s in \\callresult:@. @[%a@] @."
                                     s (Printer.pp_term) t
                    | _ -> assert false)
                in
                if (Cil_datatype.Logic_type.equal (Ctype(fun_type_return v)) (t.term_type)) then ()
                else
                  begin
                    Rpp_options.Self.fatal ~source:loc
                      "\\callresult type (@[%a@]) is different from result type of function @[%a@] \
                       (@[%a@]) with identifier %s @."
                      Printer.pp_logic_type (t.term_type) Printer.pp_varinfo v
                      Printer.pp_logic_type (Ctype(fun_type_return v)) s
                  end
              | _ -> Rpp_options.Self.fatal ~source:loc
                       "\\callresult contain no string : @[%a@] @." Printer.pp_term term
            end;
            Cil.SkipChildren

        | Tapp ({l_var_info={lv_name ="\\callpure"}},_::_, _) ->
          Rpp_options.Self.fatal ~source:loc "Expect no label for built-in \\callpure:@. @[%a@]"
            Printer.pp_term t
        | Tapp ({l_var_info={lv_name ="\\callresult"}}, _::_, _) ->
          Rpp_options.Self.fatal ~source:loc "Expect no label for built-in \\callresult:@. @[%a@]"
            Printer.pp_term t
        | Tapp ({l_var_info={lv_name ="\\call"}}, _::_, _) ->
          Rpp_options.Self.fatal ~source:loc "Expect no label for built-in \\callresult:@. @[%a@]"
            Printer.pp_term t
        | Tat(v,l)->
          let new_label = id_update l loc id_hash in
          let need_upadte = Cil_datatype.Logic_label.equal new_label l in
          begin
            match need_upadte with
            | false ->
              let new_term =
                {t with term_node = Tat(v,new_label)}
              in
              Cil.ChangeTo new_term
            | true -> super#vterm t
          end
        | _ -> super#vterm t

      method! vpredicate p =
        let (loc,_) = p.pred_loc in
        match p.pred_content with
        | Papp({l_var_info={lv_name ="\\callset"}},[],terms) ->
          Hashtbl.clear id_hash;
          List.iter
            (fun x ->
               match x.term_node with
               | Tapp({l_var_info={lv_name ="\\call"}},_,_)->
                 let _ = self#vterm x in ()
               | _ -> Rpp_options.Self.fatal ~source:loc
                        "\\callset contain no \\call: @. @[%a@] @." Printer.pp_term x
            ) terms;
          Cil.SkipChildren
        | Papp (a,labels,param) ->
          let new_labels = List.map  (fun y -> (id_update y loc id_hash)) labels in
          let need_update =
            List.fold_left2 (fun acc x y -> acc && Cil_datatype.Logic_label.equal x y)
              true new_labels labels
          in
          begin
            match need_update with
            | false ->
              let new_labels = List.map  (fun y -> (id_update y loc id_hash)) labels in
              let new_pred =
                {p with pred_content = Papp(a,new_labels,param)}
              in
              Cil.ChangeTo new_pred
            | true -> super#vpredicate p
          end
        | _ ->
          super#vpredicate p

    end
  end
  in
  (module New_check: Extensible_checker)

let () = extend_checker rpp_extend_checker
