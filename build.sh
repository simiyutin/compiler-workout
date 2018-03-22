#! /bin/bash

(make clean && eval $(opam config env) && make) | grep error
