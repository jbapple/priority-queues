COQC=coqc -opt

.PHONY: all

all: skewBinaryHeap.vo

PQSig.vo: PQSig.v OrderSig.vo
	$(COQC) PQSig.v

OrderSig.vo: OrderSig.v
	$(COQC) OrderSig.v

caseTactic.vo: caseTactic.v
	$(COQC) caseTactic.v

skewBinaryHeap.vo: skewBinaryHeap.v PQSig.vo caseTactic.vo
	$(COQC) skewBinaryHeap.v