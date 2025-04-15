#!/bin/bash

trap "kill 0" EXIT

./watch.sh &

forest watch 1313 -- "build --dev"

wait
