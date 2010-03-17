HSOURCES=HeapSortTest.hs ListBinom.hs NestedBinom.hs Heap.hs QuickBinom.hs Labor.hs ExtractedSkew.hs

.PHONY: zip

HeapSortTest.exe: $(HSOURCES) Makefile
	ghc --make -W -O2 HeapSortTest.hs -o $@

zip: HeapSortTest.zip

HeapSortTest.zip: $(HSOURCES) Makefile
	if [[ -a $@ ]]; then rm $@; fi
	zip HeapSortTest $^