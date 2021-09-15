skompiluj: GrupaPrzemiennaModulo.v Wiezniowie.v
	coqc -R "./" ""  GrupaPrzemiennaModulo.v
	coqc -R "./" ""  Wiezniowie.v

wyczysc:
	rm *.vo *.glob *.vos *.html *.vo *.aux *.vok

