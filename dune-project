(lang dune 3.3)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                        ;;
;;  SPDX-License-Identifier LGPL-2.1                                      ;;
;;  Copyright (C)                                                         ;;
;;  CEA (Commissariat à l'énergie atomique et aux énergies alternatives)  ;;
;;                                                                        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(using dune_site 0.1)
(generate_opam_files true)

(name frama-c-rpp)

(package (name frama-c-rpp)
 (depends
  ("frama-c" (and (>= 28.0~) (< 29.0~)))
 )
)
