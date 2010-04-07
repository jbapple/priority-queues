COQC=coqc -opt

.PHONY: all extract

all: Bootstrap.vo

extract: BootExtract.hs

BootExtract.hs: Extract.v Bootstrap.vo
	$(COQC) Extract.v

Bootstrap.vo: Bootstrap.v OrderSig.vo PQSig.vo caseTactic.vo
	$(COQC) Bootstrap.v 

PQSig.vo: PQSig.v OrderSig.vo
	$(COQC) PQSig.v

OrderSig.vo: OrderSig.v
	$(COQC) OrderSig.v

caseTactic.vo: caseTactic.v
	$(COQC) caseTactic.v

skewBinaryHeap.vo: skewBinaryHeap.v PQSig.vo caseTactic.vo
	$(COQC) skewBinaryHeap.v

SkewBinHeapVerify.vo: SkewBinHeapVerify.v skewBinaryHeap.vo caseTactic.vo
	$(COQC) SkewBinHeapVerify.v