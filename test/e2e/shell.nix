{ pkgs ? import ../../nix/default.nix {}
, cardanoWallet ? import ../../default.nix { inherit pkgs; }
# Whether to build cardano-wallet from this source directory and
# include in the shell.
, bins ? true
}:

let
  gems = pkgs.bundlerEnv {
    name = "gems-cardano-wallet-e2e";
    gemdir = ./.;
    ruby = pkgs.ruby_2_7;
  };
in pkgs.mkShell {
  name = "cardano-wallet-e2e";
  buildInputs = [
    gems
    gems.wrappedRuby
    pkgs.bundix
    pkgs.screen
  ] ++ pkgs.lib.optionals bins [
    cardanoWallet.cardano-wallet
    cardanoWallet.cardano-node
  ];
  CARDANO_NODE_CONFIGS = pkgs.cardano-node-deployments;
}
