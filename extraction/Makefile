COQ_FILE = Extraction.v


default: 
	coqc $(COQ_FILE)

test: default
	ghc -fno-code *.hs

clean:
	rm -rf *~
	rm -f *.hs
	rm -rf $(COQ_FILE:.v=.vo) $(COQ_FILE:.v=.glob)
