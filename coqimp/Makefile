COQBIN   := $${coq85bin}
COQC     := $(strip $(COQBIN))coqc
COQDEP   := $(strip $(COQBIN))coqdep

SUBDIRS  := framework framework/auxlibs framework/model framework/logic framework/proof tactics tactics/basetac tactics/sepauto certiucos/code certiucos/spec certiucos/proofs certiucos/ucos_lib certiucos/proofs/time certiucos/spec/absoprules certiucos/inline
#certiucos/proofs/msgqueue certiucos/proofs/oscore certiucos/proofs/mailbox certiucos/proofs/semaphore certiucos/proofs/mutex

COQFLAGS := -R . CertiOS 


SRCFILES := $(shell find $(SUBDIRS) -type f -name "*.v")
OBJFILES := $(patsubst %.v, %.vo, $(SRCFILES))
QOBJFILES := $(patsubst %.v, %.vio, $(SRCFILES))

all: $(OBJFILES)

quick: $(QOBJFILES)

version: 
	$(COQC) --version

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

%.vio: %.v
	$(COQC) $(COQFLAGS) $< -quick

clean:
	find . -type f -name "*.vo" -delete
	find . -type f -name "*.glob" -delete
	find . -type f -name "*.d" -delete
	find . -type f -name "*.vio" -delete
	rm -f .deps

deps: .deps

.deps: $(SRCFILES)
	$(COQDEP) $(COQFLAGS) $(SRCFILES) > $@

%.v.d: %.v
	$(COQDEP) -slash $(COQFLAGS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )



-include $(addsuffix .d,$(SRCFILES))
.SECONDARY: $(addsuffix .d,$(SRCFILES))


-include .deps
