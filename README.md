Relies on `std` from [koka-community](https://github.com/orgs/koka-community/repositories) (and probably `parsing` in the future)

run with
```
koka -e -i<path-to-koka-community>/std interpreter.kk
```
with `<path-to-koka-community>` replaced with a path to where you have cloned down the needed repositories

## Branch Info

This branch has the addition of a simple typechecker (based on the simply typed lambda calculus). It requires type tags on function parameters, val declarations, and return types on recursive declarations.
