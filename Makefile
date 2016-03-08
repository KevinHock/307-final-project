MLFLAGS=-g

Lexer.ml: Lexer.mll Parser.mli
		ocamllex Lexer.mll

Lexer.cmo: Lexer.ml
		ocamlc $(MLFLAGS) -c Lexer.ml

Parser.mli: Parser.mly
		ocamlyacc -v Parser.mly

Parser.cmo: Parser.mli Parser.ml
		ocamlc $(MLFLAGS) -c Parser.mli
		ocamlc $(MLFLAGS) -c Parser.ml

ast.cmo: ast.ml
		ocamlc $(MLFLAGS) -c ast.ml

store.cmo: store.ml
		ocamlc $(MLFLAGS) -c store.ml

env.cmo: env.ml ast.cmo store.cmo
		ocamlc $(MLFLAGS) -c env.ml

eval.cmo: eval.ml env.cmo ast.cmo store.cmo
		ocamlc $(MLFLAGS) -c eval.ml

main.cmo: main.ml ast.cmo env.cmo store.cmo eval.cmo Parser.cmo Lexer.cmo
		ocamlc $(MLFLAGS) -c main.ml

main: main.cmo ast.cmo env.cmo store.cmo eval.cmo Parser.cmo Lexer.cmo
		ocamlc $(MLFLAGS) -o main str.cma ast.cmo env.cmo store.cmo eval.cmo Lexer.cmo Parser.cmo main.cmo

all: main

clean:
		rm *.cmo *.cmi main Lexer.ml Parser.ml Parser.mli Parser.output
