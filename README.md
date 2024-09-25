<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Didactic Coq

[![Docker CI][docker-action-shield]][docker-action-link]
[![coqdoc][coqdoc-shield]][coqdoc-link]

[docker-action-shield]: https://github.com/motrellin/didcoq/actions/workflows/docker-action.yml/badge.svg?branch=main
[docker-action-link]: https://github.com/motrellin/didcoq/actions/workflows/docker-action.yml


[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://motrellin.github.io/didcoq/./docs/toc.html


tba


## Meta

- Author(s):
  - Max Ole Elliger (initial)
- License: [MIT License](LICENSE)
- Compatible Coq versions: Developed for 8.19.0
- Additional dependencies: none
- Coq namespace: `DidCoq`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Didactic Coq
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-didcoq
```

To instead build and install manually, do:

``` shell
git clone --recurse-submodules https://github.com/motrellin/didcoq.git
cd didcoq
make all  # or make -j <number-of-cores-on-your-machine> all
make install
```


## Documentation
tba.
