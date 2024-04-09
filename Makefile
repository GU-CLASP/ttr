


bnfc: Exp/Lex.x

Exp/Par.hs: Exp/Par.y
	happy Exp/Par.y

Exp/Lex.hs: Exp/Lex.x
	alex Exp/Lex.x

Exp/Test: Exp/Test.hs
	ghc --make Exp/Test.hs -o Exp/Test

Exp/Lex.x Exp/Par.y: Exp.cf
	bnfc --haskell -d Exp.cf

clean:
	rm -f *.log *.aux *.hi *.o *.js_o *.js_hi Exp/*

js: *.hs Exp/Par.hs Exp/Lex.hs
	nix-shell ghcjs/shell.nix --run "ghcjs --make JS"
		cp examples/*.tt JS.jsexe

# stack-setup:
# 	nix-shell stack/shell.nix --pure --run "stack --stack-yaml=stack/stack.yaml setup"


