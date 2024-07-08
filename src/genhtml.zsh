#!/bin/zsh

foreach file ( *.agda )
    agda --html $file
end

rsync -av html ~/src/shinji-kono.github.io/galois
