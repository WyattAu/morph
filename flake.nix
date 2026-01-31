{
  description = "Lean 4 Dev Environment (Managed via Elan)";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in
    {
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          elan        # The Lean Version Manager
          git         # Required by Lake
          glibc       # Required for compiled C code
          ccache      # Speeds up builds
        ];

      shellHook = ''
          echo ">> Lean 4 Environment (Elan)"
          
          # Read the desired version
          TOOLCHAIN=$(cat lean-toolchain)
          
          # Only try to install if it's not already in the list
          if ! elan toolchain list | grep -q "$TOOLCHAIN"; then
              elan toolchain install "$TOOLCHAIN"
          fi
          
          echo ">> Active Toolchain:"
          lean --version
        '';
      };
    };
}