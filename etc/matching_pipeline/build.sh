#!/usr/bin/env bash

BUILD_DIR="_build"
mkdir -p ${BUILD_DIR}
lualatex --output-directory=${BUILD_DIR} --output-format=dvi picture.tex
dvisvgm ${BUILD_DIR}/picture.dvi