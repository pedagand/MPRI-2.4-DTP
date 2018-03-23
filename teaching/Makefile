TARGETS=01-effectful/Monad.lagda.rst   \
        02-dependent/Indexed.lagda.rst \
	03-total/Recursion.lagda.rst \
	04-generic/Desc.lagda.rst \
	05-open/Problems.lagda.rst

SRC_DIR=../
STUDENTIZE=python ../studentize.py
DIFF=diff -u
PATCH=patch

all: $(TARGETS)

%.student: force
	$(STUDENTIZE) $(SRC_DIR)/$*.lagda.rst
	mv $(SRC_DIR)/$*.student.lagda.rst $*.student

%.patch: %.lagda.rst.orig %.student
	$(DIFF) $*.student $*.lagda.rst.orig > $@; true

%.lagda.rst: %.student
	$(PATCH) $*.student $*.patch -o $@.orig
	cp $@.orig $@

clean:
	rm -i $(TARGETS)

force:
	true
