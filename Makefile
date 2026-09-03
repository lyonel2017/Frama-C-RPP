##########################################################################
#                                                                        #
#  SPDX-License-Identifier LGPL-2.1                                      #
#  Copyright (C)                                                         #
#  CEA (Commissariat à l'énergie atomique et aux énergies alternatives)  #
#                                                                        #
##########################################################################

.PHONY: all build clean

FRAMAC_SHARE:=$(shell frama-c -no-autoload-plugins -print-share-path)

include ${FRAMAC_SHARE}/Makefile.common

##########################################################################
# Build

all:: build

build::
	dune build @install

clean:: purge-tests
	dune clean
	rm -rf _build .merlin

##########################################################################
# Tests

PTEST_ALL_DIRS:=tests benchmarks
include ${FRAMAC_SHARE}/Makefile.testing

##########################################################################
# Install

include ${FRAMAC_SHARE}/Makefile.installation

##########################################################################
# Headers

include ${FRAMAC_SHARE}/Makefile.headers

headers/headache_config.txt: \
  headers/headache_config.rpp.txt \
  ${FRAMAC_SHARE}/headache_config.txt
	$(RM) $@
	$(ECHO) "# Generated file. Edit headache_config.rpp.txt instead" > $@
	$(CAT) $^ >> $@
	$(CHMOD_RO) $@

headers: headers/headache_config.txt
check-headers: headers/headache_config.txt

# old
rpp-manual.pdf:
	make -C doc/Grammar
	cp doc/Grammar/grammar.pdf $@
