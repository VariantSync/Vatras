#!/usr/bin/env bash

cd "$(dirname ${BASH_SOURCE[0]})/.."

possible-inconsistencies() {
  echo 'postulates:'
  grep 'postulate' -r src --include '*agda*'

  echo
  echo 'terminating pragmas:'
  grep 'TERMINATING' -r src --include '*agda*'

  echo
  echo 'holes:'
  (
    grep -F '{!' -r src --include '*agda*'
    grep ' ?\( \|$\)' -r src --include '*agda*'
  )
}

with-doc() {
  # Used for alignment.
  # Cannot use 'column' because it doesn't exist on MAC.
  columnCount="$(possible-inconsistencies | awk 'BEGIN { max=0 } { if (max < length($0)) max=length($0) } END { print max }')"

  POSIXLY_CORRECT=1 awk '
    BEGIN {
      doc[""]=""
      doc["postulates:"]=""
      doc["terminating pragmas:"]=""
      doc["holes:"]=""

      doc["src/Util/String.agda:  where postulate trustMe : _"]="Also proposed in the Agda issue tracker to make String propositions provable. Only used in examples."
      # Note: this above postulate appears four times
      doc["src/Show/Lines.agda:{-# NON_TERMINATING #-}"]="Only used for printing and thus not proof relevant. Also, NON_TERMINATING functions do not reduce during type checking."
      doc["src/Tutorial/A_NewLanguage.lagda.md:We are using the `{-# TERMINATING -#}` flag here:"]="This is actually a comment."
      doc["src/Tutorial/A_NewLanguage.lagda.md:{-# TERMINATING #-}"]="Simplification of the tutorial. Not used in the anything else."
      doc["src/Tutorial/A_NewLanguage.lagda.md:MyConfig = {!!}"]="Intentional hole to be filled by you! Not used in anything other than the tutorial."
      doc["src/Tutorial/A_NewLanguage.lagda.md:⟦_⟧ = {!!}"]="Intentional hole to be filled by you! Not used in anything other than the tutorial."
      doc["src/Tutorial/B_Translation.lagda.md:conf e c²ᶜᶜ = {!!}"]="Intentional hole to be filled by you! Not used in anything other than the tutorial."
      doc["src/Tutorial/B_Translation.lagda.md:fnoc e cᵐʸ = {!!}"]="Intentional hole to be filled by you! Not used in anything other than the tutorial."
      doc["src/Tutorial/B_Translation.lagda.md:preservation-⊆[] e c = {!!}"]="Intentional hole to be filled by you! Not used in anything other than the tutorial."
      doc["src/Tutorial/B_Translation.lagda.md:preservation-⊇[] e c = {!!}"]="Intentional hole to be filled by you! Not used in anything other than the tutorial."
      doc["src/Tutorial/B_Translation.lagda.md:translate (D ⟨ l , r ⟩) = {!!}"]="Intentional hole to be filled by you! Not used in anything other than the tutorial."
      doc["src/Tutorial/B_Translation.lagda.md:translate (a -< cs >-)  = {!!}"]="Intentional hole to be filled by you! Not used in anything other than the tutorial."
      doc["src/Tutorial/C_Proofs.lagda.md:  {!!}   -- write down the proof of correctness in this hole"]="Intentional hole to be filled by you! Not used in anything other than the tutorial."
      doc["src/Tutorial/C_Proofs.lagda.md:  {!!} , -- write down the expression in this hole"]="Intentional hole to be filled by you! Not used in anything other than the tutorial."
      doc["src/Tutorial/C_Proofs.lagda.md:2CC≽MyLang = {!!}"]="Intentional hole to be filled by you! Not used in anything other than the tutorial."
      doc["src/Tutorial/C_Proofs.lagda.md:MyLang-is-Sound = {!!}"]="Intentional hole to be filled by you! Not used in anything other than the tutorial."

      exitCode=0
    }

    {
      padding='"$columnCount"' - length($0) + 3
      if ($0 in doc) {
        printf "%s% *s%s\n", $0, padding, "", doc[$0]
      } else {
        printf "\033[30;41m%s% *s%s\033[39;49m\n", $0, padding, "", "UNDOCUMENTED!!!"
        exitCode=1
      }
    }

    END {
      exit exitCode
  }
  '
}

if [ "$1" = "--with-documentation" ]
then
  possible-inconsistencies | with-doc
  exitCode=$?
else
  possible-inconsistencies
  exitCode=$?
fi

echo
echo "Hint: Use '$0 --with-documentation | less -S' to be able to see documentation to each source and to scroll horizontally"

exit $exitCode
