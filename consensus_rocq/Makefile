.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) AdoptCommit.v
	$(ROCQC) FastPaxos.v
	$(ROCQC) EPaxos.v
	$(ROCQC) SwiftPaxos.v

clean:
	rm -f *.vo* *.glob .*.aux *.cache .*.cache