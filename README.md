 # Agda Synthetic Categories
 
An agda development focussed on the development of infinity category theory 
using simplicial type theory.
Visit [the-forest]() to browse the resource and find out more about the project.


 ## Building
 
The easiest way to build or work on this project is using nix. To build the site
simply run `nix-build`, and the site will be generated into the folder `/output`,
you can then serve this any way of your choosing, for example using the python
command:

```
python3 -m http.server 1313 -d result
```


 ## Development 

There is also a provided script for launching a live reloading 
dev server.

Use `nix-shell` to load into a shell, and then just run `./server.sh` to start it off :)
