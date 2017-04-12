js: *.hs Exp/Par.hs Exp/Lex.hs
	nix-shell ghcjs.nix --run "ghcjs --make JS"

bnfc: Exp/Lex.x

Exp/Par.hs: Exp/Par.y
	happy -gca Exp/Par.y

Exp/Lex.hs: Exp/Lex.x
	alex -g Exp/Lex.x

Exp/Test: Exp/Test.hs
	ghc --make Exp/Test.hs -o Exp/Test

Exp/Lex.x Exp/Lex.y: Exp.cf
	bnfc --haskell -d Exp.cf

clean:
	rm -f *.log *.aux *.hi *.o
	cd Exp && rm -f ParExp.y LexExp.x LexhExp.hs \
                        ParExp.hs PrintExp.hs AbsExp.hs *.o *.hi
