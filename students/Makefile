SRCS=Index.lagda.rst\
	00-agda/Warmup.lagda.rst   \
	01-effectful/Monad.lagda.rst   \
        02-dependent/Indexed.lagda.rst \
	03-total/Recursion.lagda.rst \
	04-generic/Desc.lagda.rst \
	05-open/Problems.lagda.rst

DIFF=diff -u
PATCH=patch
STUDENTIZE=python3 studentize.py

all: $(SRCS)

Index.lagda.rst:
	$(STUDENTIZE) ../Readme.lagda.rst
	mv ../Readme.student.lagda.rst Index.lagda.rst

%.lagda.rst: force
	$(STUDENTIZE) ../$*.lagda.rst
	mv ../$*.student.lagda.rst  $*.lagda.rst

clean:
	rm -i $(SRCS)

force:
	true
