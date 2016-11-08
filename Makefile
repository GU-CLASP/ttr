OPT=0

all:
	ghc --make -O$(OPT) -o cubical Main.hs
bnfc:
	bnfc --haskell -d Exp.cf
	happy -gca Exp/Par.y
	alex -g Exp/Lex.x
	ghc --make -O$(OPT) Exp/Test.hs -o Exp/Test
clean:
	rm -f *.log *.aux *.hi *.o cubical
	cd Exp && rm -f ParExp.y LexExp.x LexhExp.hs \
                        ParExp.hs PrintExp.hs AbsExp.hs *.o *.hi

tests:
	runghc Tests.hs
