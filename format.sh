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

eval stylish-haskell -i "$targets"

eval hlint -h hlint.yml "$targets"
