(**************************************************************************)
(*                                                                        *)
(*  SPDX-License-Identifier LGPL-2.1                                      *)
(*  Copyright (C)                                                         *)
(*  CEA (Commissariat à l'énergie atomique et aux énergies alternatives)  *)
(*                                                                        *)
(**************************************************************************)

open Filecheck
open Cil_types

let id_checker identifier loc id_hash =
  match identifier with
  | FormalLabel(s) ->
    ( match Str.bounded_split (Str.regexp "_") s 2 with
      | "Pre":: id :: [] | "Post" :: id :: []->
        if not (Hashtbl.mem id_hash id) then
          Rpp_options.Self.fatal ~source:loc  "Unknown label: @ @[%s@] @." s
      | _ -> ())
  |  _ -> ()

let _id_update identifier loc id_hash  =
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

let check_param_type fname param formals loc=
  match formals with
  | Some l ->
    List.iter2 (fun x (_,t,_) ->
        match x.term_type with
        | Ctype(ty) ->
          if Cil_datatype.Typ.equal t ty then ()
          else
            Rpp_options.Self.fatal ~source:loc
              "Cast are not supported:@. @[%a and %a are not \
               compatible@] for term @[%a@] in callpure of %s @."
              (Printer.pp_logic_type)  x.term_type
              (Printer.pp_typ) t (Printer.pp_term) x (fname)
        | Linteger ->
          if not (Ast_types.is_integral t) then
            Rpp_options.Self.fatal ~source: loc
              "Cast are not supported:@. @[%a and %a are not compatible@] \
               for term @[%a@] in callpure of %s @."
              (Printer.pp_logic_type)  x.term_type (Printer.pp_typ) t
              Printer.pp_term x (fname)
        | Lreal ->
          if not (Ast_types.is_float t) then
            Rpp_options.Self.fatal ~source: loc
              "Cast are not supported:@. @[%a and %a are not compatible@] \
               for term @[%a@] in callpure of %s @."
              (Printer.pp_logic_type)  x.term_type (Printer.pp_typ) t
              Printer.pp_term x (fname)
        | _ -> Rpp_options.Self.fatal ~source:loc
                 "Function %s is called with a parameter with type \
                  is not a C type:@. @[%a@] @." (fname) Printer.pp_term x
      ) param l
  | None ->
    Rpp_options.Self.fatal ~source:loc
      "Function %s is declared without prototype. Can't use it in a relational property" fname

let rpp_extend_checker check =
  let module Origin = (val check: Extensible_checker) in

  let module New_check =
  struct
    class check  ?is_normalized id = object(self)
      inherit Origin.check ?is_normalized id as super

      val id_hash = Hashtbl.create 3

      method! vterm t =
        let loc = fst t.term_loc in
        match t.term_node with
        | Tapp({l_var_info={lv_name ="\\callpure"}},[],terms) ->
          begin
            match terms with
            | {term_node = TConst (Integer(_,_))} :: q ->
              begin
                match q with
                | {term_node=TLval(TVar({lv_origin=Some(x)}),TNoOffset)} :: p ->
                  if Ast_types.is_fun x.vtype then begin
                    let (rt, args, _is_va,_) = Cil.splitFunctionType x.vtype in
                    check_param_type x.vname p args loc;
                    if not (Cil_datatype.Logic_type.equal (t.term_type) (Ctype rt)) then
                        Rpp_options.Self.fatal ~source:loc
                        "\\callpure type (@[%a@]) is different from result type \
                         of function @[%a@] (@[%a@]):@.@[%a@]"
                        Printer.pp_logic_type t.term_type Printer.pp_varinfo x
                        Printer.pp_typ rt Printer.pp_term t
                  end else
                    Rpp_options.Self.fatal ~source:loc
                      "Expected a function as second parameter::@. @[%a@] @."
                      (Printer.pp_term) t;
                  DoChildren
                | _ ->
                  Rpp_options.Self.fatal ~source:loc
                    "Expected a logical variable as seconde parameter :@. @[%a@] @."
                    (Printer.pp_term) t
              end
            | _ ->
              Rpp_options.Self.fatal ~source:loc
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
                       if Ast_types.is_fun x.vtype then
                         let (_, args, _, _) = Cil.splitFunctionType x.vtype in
                         check_param_type x.vname p args loc;
                         Hashtbl.add id_hash s x;
                         Cil.DoChildren
                       else
                         Rpp_options.Self.fatal ~source:loc
                           "Expected a function as thrid parameter:@. @[%a@] @."
                           (Printer.pp_term) t
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
                let v =
                  match Hashtbl.find_opt id_hash s with
                  | Some v -> v
                  | None ->
                    Rpp_options.Self.fatal ~source:loc
                      "Unknown identifier %s in \\callresult:@. @[%a@] @."
                      s (Printer.pp_term) t
                in
                let (rt,_,_,_) = Cil.splitFunctionType v.vtype in
                if (Cil_datatype.Logic_type.equal (Ctype rt) (t.term_type)) then ()
                else
                  begin
                    Rpp_options.Self.fatal ~source:loc
                      "\\callresult type (@[%a@]) is different from result type of function @[%a@] \
                       (@[%a@]) with identifier %s @."
                      Printer.pp_logic_type (t.term_type) Printer.pp_varinfo v
                      Printer.pp_logic_type (Ctype rt) s
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
          id_checker l loc id_hash;
          self#vterm v
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
        | Papp (li,labels,params) ->
          List.iter (fun l -> id_checker l loc id_hash) labels;
          ignore (super#vlogic_info_use li);
          List.iter
            (fun t ->
               ignore
                 (Visitor.visitFramacTerm (self:>Visitor.frama_c_visitor) t))
            params;
          Cil.SkipChildren
        | _ -> super#vpredicate p
    end
  end
  in
  (module New_check: Extensible_checker)

let () = extend_checker rpp_extend_checker
