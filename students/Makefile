SRCS=01-effectful/Monad.lagda.rst   \
        02-dependent/Indexed.lagda.rst \
	03-total/Recursion.lagda.rst \
	04-generic/Desc.lagda.rst \
	05-open/Problems.lagda.rst

DIFF=diff -u
PATCH=patch

all: $(SRCS)

# Use ONLY to UPDATE a patch
%.patch: %.lagda.rst.orig # ../%.lagda.rst
	$(DIFF) ../$*.lagda.rst $*.lagda.rst.orig > $@; true

%.lagda.rst: %.patch # ../%.lagda.rst
	$(PATCH) ../$*.lagda.rst $*.patch -o $@

clean:
	rm -i $(SRCS)

force:
	true
