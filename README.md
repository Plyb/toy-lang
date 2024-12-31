Relies on `std` from [koka-community](https://github.com/orgs/koka-community/repositories) (and probably `parsing` in the future)

add `-i<path-to-koka-community>/std` to `koka.languageServer.compilerArguments` in vscode settings, then run with the launch config in this repo. Replace `<path-to-koka-community>` with the parent directory of where you have cloned the `std` repository from `koka-community` on GitHub.

## Branch Info

This branch has the addition of a simple typechecker (based on the simply typed lambda calculus). It requires type tags on function parameters, val declarations, and return types on recursive declarations.
