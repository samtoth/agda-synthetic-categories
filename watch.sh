#!/bin/bash

./build.sh

fswatch -o src/ | while read num ; \
  do \
    echo "Rebuilding forest"
    time ./build.sh
    echo "Done"
    echo
  done
