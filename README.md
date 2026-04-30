# Agda Synthetic Categories

An agda development focussed on the development of ∞-category theory using simplicial
type theory.
Visit [the-forest](https://samtoth.github.io/agda-synthetic-categories) to browse
the resource and find out more about the project.
Benchmark history is published at
[the benchmark page](https://samtoth.github.io/agda-synthetic-categories/benchmarks/).

Have questions or just want to chat? Join our [Discord server](https://discord.gg/Jfxv4jPTva)!

## Development

The easiest way to build or work on this project is using nix, and we provide a range
of targets for building, watching, and serving the site via the Makefile. To build
the project and set up a server you can run `make server` from the nix shell, with an
optional `PORT=` parameter (default: `1313`). To see all `make` targets run
`make help`.

### Installing without nix

To get working on the library without nix you will at minimum need a working
installation of Agda nightly version
[f3697415ac835c4e0898fb7eb0a5a46e313c2065](https://github.com/agda/agda/commit/f3697415ac835c4e0898fb7eb0a5a46e313c2065)
or newer. You can find the latest release binaries
[here](https://github.com/agda/agda/releases/). See also the Agda documentation:
[installing from source](https://agda.readthedocs.io/en/latest/getting-started/installation.html#option-2-install-the-development-version-of-agda-from-source-for-advanced-users).

In order to build the forest, you will need:

- [agda-forester](https://github.com/samtoth/agda-forester)
- [treelist](https://github.com/samtoth/treelist)
- [Forester version 5](https://sr.ht/~jonsterling/forester/)
- We use [Kento Okura's forest-server](https://github.com/kentookura/forest-server)
  by default to serve the Forest locally, but you may choose other options. A python
  server target is provided in the makefile.

### Emacs mode

I have been using the emacs mode by the Topos Institute at
[github:ToposInstitute/forester.el](https://github.com/ToposInstitute/forester.el), which works well when
editing trees, but there is currently no solution for working
with literate agda in forests.
