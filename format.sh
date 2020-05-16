#!/bin/bash
shopt -s globstar
shopt -s nullglob
targets='{app,src,test}/**/*.hs'
brittany_flags="--write-mode=inplace --omit-output-check"

eval brittany "\"\$@\"" $brittany_flags  "$targets"
# work around brittany not recognising GADTs properly (#261, #79)
eval sed -i -e "'s/::\([A-Z!\(]\)/:: \1/g'" "$targets"
# work around brittany weirdly-formatting DataKinds
eval sed -i -e "\"s/ \([(@]\) '/ \1'/g\"" "$targets"

# work around https://github.com/haskell-suite/haskell-src-exts/issues/451
eval sed -i -e "'s/(~)/EQUALITY/g'" "$targets"

sed -i -e 's/Cabal-Version:\(\s*\)3.0/Cabal-Version:\12.4/g' *.cabal
eval stylish-haskell -i "$targets"
sed -i -e 's/Cabal-Version:\(\s*\)2.4/Cabal-Version:\13.0/g' *.cabal

eval hlint -h hlint.yml "$targets"

eval sed -i -e "'s/EQUALITY/(~)/g'" "$targets"
# undo haskell-src-exts workarounds, both hlint and stylish-haskell are affected
