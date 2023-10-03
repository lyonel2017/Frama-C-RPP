##########################################################################
#  This file is part of RPP plug-in of Frama-C.                          #
#                                                                        #
#  Copyright (C) 2016-2023                                               #
#    CEA (Commissariat à l'énergie atomique et aux énergies              #
#    alternatives)                                                       #
#                                                                        #
#  you can redistribute it and/or modify it under the terms of the GNU   #
#  Lesser General Public License as published by the Free Software       #
#  Foundation, version 2.1.                                              #
#                                                                        #
#  It is distributed in the hope that it will be useful,                 #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         #
#  GNU Lesser General Public License for more details.                   #
#                                                                        #
#  See the GNU Lesser General Public License version 2.1                 #
#  for more details (enclosed in the file LICENSE).                      #
##########################################################################

VERSION = 0.0.2
EXTRAVERSION ?=

ifndef FRAMAC_SHARE
FRAMAC_SHARE  :=$(shell frama-c-config -print-share-path)
endif
ifndef FRAMAC_LIBDIR
FRAMAC_LIBDIR :=$(shell frama-c-config -print-libpath)
endif

PLUGIN_ENABLE:=yes
PLUGIN_DYNAMIC:=yes
PLUGIN_DISTRIBUTED:=$(PLUGIN_ENABLE)

PLUGIN_NAME := Rpp

PLUGIN_CMI := rpp_types
PLUGIN_CMO := rpp_options \
	rpp_extend_checker \
	rpp_parser \
	rpp_visitor \
	rpp_axiomatic_generator \
	rpp_generator \
	rpp_predicate_visitor \
	rpp_predicate_visitor_axiom \
	rpp_core \
	rpp_register
PLUGIN_GUI_CMO := rpp_gui
PLUGIN_TESTS_DIRS := rpp \
	../benchmarks/stackoverflow

include $(FRAMAC_SHARE)/Makefile.dynamic


ifeq ("$(OPENSOURCE)","no")
LICENSE=PROPRIETARY
HEADERS=HEADERS_PROPRIETARY
else
LICENSE=LGPL
HEADERS=HEADERS_LGPL
endif

RPP_DISTRIBUTED_FILES=rpp_options.ml rpp_options.mli \
	rpp_extend_checker.ml rpp_extend_checker.mli \
	rpp_parser.ml rpp_parser.mli \
	rpp_visitor.ml rpp_visitor.mli \
	rpp_axiomatic_generator.ml rpp_axiomatic_generator.mli \
	rpp_generator.ml rpp_generator.mli \
	rpp_predicate_visitor.ml rpp_predicate_visitor.mli \
	rpp_predicate_visitor_axiom.ml rpp_predicate_visitor_axiom.mli \
	rpp_core.ml rpp_core.mli \
	rpp_register.ml rpp_register.mli \
	rpp_gui.ml rpp_gui.mli rpp_types.mli Rpp.mli \
	Makefile rpp-manual.pdf README.md LICENSE opam

NO_HEADERS=rpp-manual.pdf README.md LICENSE opam

license:
	cp $(LICENSE) LICENSE

rpp-manual.pdf:
	make -C doc/Grammar
	cp doc/Grammar/grammar.pdf $@

headers:: license
	$(PRINT_MAKING) $@
	headache -c .headache_config.txt \
                 -h $(HEADERS) \
                 $(filter-out $(NO_HEADERS), $(RPP_DISTRIBUTED_FILES))

ifeq ("$(EXTRAVERSION)","")
DISTRIBDIR=frama-c-rpp-$(VERSION)
else
DISTRIBDIR=frama-c-rpp-$(VERSION)-$(EXTRAVERSION)
endif

distrib: headers rpp-manual.pdf
	$(RM) -r $(DISTRIBDIR)
	$(RM) $(DISTRIBDIR).tar.gz
	$(MKDIR) $(DISTRIBDIR)
	tar -cf - $(RPP_DISTRIBUTED_FILES) | tar -C $(DISTRIBDIR) -xf -
	tar zcf $(DISTRIBDIR).tar.gz $(DISTRIBDIR)
