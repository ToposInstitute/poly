let
  sources = import ./nix/sources.nix;
  emacsOverlay = import sources.emacs-overlay;
  pkgs = import sources.nixpkgs { overlays = [ emacsOverlay ]; };
  emacsPackages = pkgs.emacsPackagesNgGen pkgs.emacsPgtkGcc;
  emacsWithPackages = emacsPackages.emacsWithPackages;
  epkgs = emacsWithPackages (epkgs: [ epkgs.vterm ]);
in with pkgs;
mkShell {
  buildInputs = [
    pkgs.emacsPgtkGcc # This will only work on WSL if you have the XServer configured corrrectly.  Otherwise, use pkgs.emacs
    pkgs.libtool
    pkgs.ripgrep
    pkgs.fd
    # see: https://gist.github.com/ecthiender/b9db474e80113bdc18d472de1593eb3c
    pkgs.haskellPackages.haskell-language-server
    pkgs.haskellPackages.hlint
    pkgs.haskellPackages.ormolu
    pkgs.haskellPackages.ghcid
    pkgs.haskellPackages.cabal-install
    pkgs.haskellPackages.cabal-fmt
    epkgs
    pkgs.cmake
    pkgs.nixfmt
    (agda.withPackages (ps: [ ps.standard-library]))
  ];
}
