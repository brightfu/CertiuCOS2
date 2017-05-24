ROOT:=../../
RELATIVE:=tactics/pure/

SRCFILES := $(shell find $(SUBDIRS) -type f -name "*.v")
FORAC := $(patsubst %.v, %.vo, $(SRCFILES))
FORAC2 := $(patsubst %.v, %.vio, $(SRCFILES))

all:
	$(MAKE) -C $(ROOT)

%.vo: %.v
	$(MAKE) -C $(ROOT) $(RELATIVE)$@

%.vio: %.v
	$(MAKE) -C $(ROOT) $(RELATIVE)$@

clean:
	find . -type f -name "*.vo" -delete
	find . -type f -name "*.glob" -delete
	find . -type f -name "*.d" -delete
	find . -type f -name "*.vio" -delete
	rm -f .deps

$(FORAC):

$(FORAC2):
