#!/bin/sh -e
make check
cd expressions && make check && cd ..
cd deep-expressions && make check && cd ..
