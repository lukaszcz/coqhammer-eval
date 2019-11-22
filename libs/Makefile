all: lf plf vfa

lf: lf/Makefile
	cd lf && $(MAKE)

plf: plf/Makefile
	cd plf && $(MAKE)

vfa: vfa/Makefile
	cd vfa && $(MAKE)

%/Makefile: %/_CoqProject
	cd `dirname $<` && coq_makefile -f _CoqProject -o Makefile

clean:
	cd lf && $(MAKE) clean
	cd plf && $(MAKE) clean
	cd vfa && $(MAKE) clean
	-rm lf/Makefile lf/Makefile.conf
	-rm plf/Makefile plf/Makefile.conf
	-rm vfa/Makefile vfa/Makefile.conf

.PHONY: all clean lf plf vfa
