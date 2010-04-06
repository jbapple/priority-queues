COQC=coqc -opt

.PHONY: all

all: Inline.vo

Inline.vo: Inline.v OrderSig.vo PQSig.vo
	$(COQC) Inline.v

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