# Agda Synthetic Categories
 
An agda development focussed on the development of infinity category theory 
using simplicial type theory.
Visit [the-forest](https://samtoth.github.io/agda-synthetic-categories) to browse the resource and find out more about the project.


## Building
 
The easiest way to build or work on this project is using nix. To build the site
simply run `nix-build`, and the site will be generated into the folder `/output`,
you can then serve this any way of your choosing, for example using the python
command:

```
python3 -m http.server 1313 -d result
```


## Development 

There is also a provided script for launching a live reloading 
dev server.

Use `nix-shell` to load into the dev-shell, and then you can use 
[Kento Okura's forester server tool](https://github.com/kentookura/forest-server) 
by running `forest watch -- "build --dev"` to start it off :)

### Emacs mode

I have been using the emacs mode by the Topos Institute at
[github:ToposInstitute/forester.el](https://github.com/ToposInstitute/forester.el), which works well when 
edditing trees, but there is currently no solution for working
with literate agda in forests.
