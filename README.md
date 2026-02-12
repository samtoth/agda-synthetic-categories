# Agda Synthetic Categories

An agda development focussed on the development of ∞-category theory using simplicial
type theory.
Visit [the-forest](https://samtoth.github.io/agda-synthetic-categories) to browse
the resource and find out more about the project.

## Development

The easiest way to build or work on this project is using nix, and we provide a range
of targets for building, watching, and serving the site via the Makefile. To build
the project and set up a server you can run `make server` from the nix shell, with an
optional `PORT=` parameter (default: `1313`). To see all `make` targets run
`make help`.

### Emacs mode

I have been using the emacs mode by the Topos Institute at
[github:ToposInstitute/forester.el](https://github.com/ToposInstitute/forester.el), which works well when
editing trees, but there is currently no solution for working
with literate agda in forests.
