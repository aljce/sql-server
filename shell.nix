with import <nixpkgs> { };

haskell.lib.buildStackProject {
  name = "sql-server";
  ghc = haskell.packages.ghc7103.ghc;
  buildInputs = [ z3
                  ncurses
                  git
                  cabal-install ];
}
