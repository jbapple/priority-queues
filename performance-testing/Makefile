HSOURCES=HeapSortTest.hs ListBinom.hs NestedBinom.hs Heap.hs QuickBinom.hs Labor.hs ExtractedSkew.hs BootExtract.hs MeldTest.hs

all: MeldTest.exe HeapSortTest.exe

.PHONY: zip

MeldTest.exe: $(HSOURCES) Makefile
	ghc --make -W -O2 MeldTest.hs -o $@

HeapSortTest.exe: $(HSOURCES) Makefile
	ghc --make -W -O2 HeapSortTest.hs -o $@

zip: HeapSortTest.zip

HeapSortTest.zip: $(HSOURCES) Makefile
	if [[ -a $@ ]]; then rm $@; fi
	zip HeapSortTest $^