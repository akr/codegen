all install : Makefile.coq
	$(MAKE) -f Makefile.coq $@

plugin : Makefile.coq
	$(MAKE) -f Makefile.coq src/codegen_plugin.cmxs

Makefile.coq : _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

check:
	cd test; $(MAKE) check

clean :
	rm -f \
	  Makefile.coq \
	  src/*.o \ \
	  src/*.cmi \
	  src/*.cmo \
	  src/*.cmx \
	  src/*.cma \
	  src/*.cmxa \
	  src/*.cmxs \
	  src/*.a \
	  src/*.d \
	  theories/*.glob \
	  theories/*.vo \
	  theories/*.d
