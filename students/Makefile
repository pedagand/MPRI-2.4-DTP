SRCS=01-effectful/Monad.lagda.rst   \
        02-dependent/Indexed.lagda.rst \
	03-total/Recursion.lagda.rst \
	04-generic/Desc.lagda.rst \
	05-open/Problems.lagda.rst

DIFF=diff -u
PATCH=patch

all: $(SRCS)

# Use ONLY to UPDATE a patch
%.patch: ../%.lagda.rst %.student.lagda.rst
	$(DIFF) $*.lagda.rst $*.student.lagda.rst > $@; true

%.lagda.rst: 
	$(PATCH) ../$*.lagda.rst $*.patch -o $@

clean:
	rm -i $(TARGETS)

force:
	true
