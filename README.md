
# Münster Curry compiler + TypeClass (mirror)

A mirror repository of Münster Curry compiler (MCC) with TypeClass extentions.
The original repository is [wlux -> type-classes][type-classes].


## Build

Building this compiler requires a haskell compiler (e.g. GHC).

- apply patch

  remove CPP directives.
  
  ```sh
  sed -i -e '/#else/,/#endif/d' -e '/#if/d' hs2010/Semigroup.lhs
  ```

- configure and build

  ```sh
  autoconf -i
  ./configure
  make
  ```


[type-classes]: https://hub.darcs.net/wlux/type-classes "wlux -> type-classes"

