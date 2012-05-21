FILES=Core.hs Parser.hs PrettyPrint.hs Language.hs Iseq.hs

Core : $(FILES)
	ghc $(FILES)
