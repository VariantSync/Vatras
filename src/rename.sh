#!/bin/bash
filetypes=("*.agda" "*.lagda.md")
replacements=("Lang.Annotation/Framework.Annotation") #("VarLang/𝕃" "Domain/𝔸" "ConfLang/ℂ" "VSet/VMap" "import Definitions/import Framework.Definitions")
for filetype in "${filetypes[@]}";
do
  for replacement in "${replacements[@]}";
  do
    #find -name "$filetype" -exec sed "s/$replacement/g" > dry.txt {} \;
    echo "Running find -name '$filetype' -exec vim -nEs +'%s/$replacement/g' +wq {} \;"
    find -name "$filetype" -exec vim -nEs +"%s/$replacement/g" +wq {} \;
    #find -name "$filetype" -exec echo {} \;
  done
done

#find -name "*.lagda.md" -exec echo {} \;
