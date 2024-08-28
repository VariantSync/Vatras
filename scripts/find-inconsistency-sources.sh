#!/usr/bin/env bash

cd "$(dirname ${BASH_SOURCE[0]})/.."
export POSIXLY_CORRECT=1

awkDocumentationMap='
    function document(count, line, documentation) {
      doc[count ":" line]=documentation
    }

    BEGIN {
      ignore[""]=1
      ignore["postulates:"]=1
      ignore["terminating pragmas:"]=1
      ignore["holes:"]=1

      document(1,
        "src/Vatras/Util/String.agda:  where postulate trustMe : _",
        "Also proposed in the Agda issue tracker to make String propositions provable. Only used in examples.")
      document(2,
        "src/Vatras/Util/String.agda:  where postulate trustMe : _",
        "Also proposed in the Agda issue tracker to make String propositions provable. Only used in examples.")
      document(3,
        "src/Vatras/Util/String.agda:  where postulate trustMe : _",
        "Also proposed in the Agda issue tracker to make String propositions provable. Only used in examples.")
      document(4,
        "src/Vatras/Util/String.agda:  where postulate trustMe : _",
        "Also proposed in the Agda issue tracker to make String propositions provable. Only used in examples.")
      document(1,
        "src/Vatras/Show/Lines.agda:{-# NON_TERMINATING #-}",
        "Only used for printing and thus not proof relevant. Also, NON_TERMINATING functions do not reduce during type checking.")
      document(1,
        "src/Vatras/Tutorial/A_NewLanguage.lagda.md:We are using the `{-# TERMINATING -#}` flag here:",
        "This is actually a comment.")
      document(1,
        "src/Vatras/Tutorial/A_NewLanguage.lagda.md:{-# TERMINATING #-}",
        "Simplification of the tutorial. Not used in the anything else.")
      document(1,
        "src/Vatras/Tutorial/A_NewLanguage.lagda.md:MyConfig = {!!}",
        "Intentional hole to be filled by you! Not used in anything other than the tutorial.")
      document(1,
        "src/Vatras/Tutorial/A_NewLanguage.lagda.md:⟦_⟧ = {!!}",
        "Intentional hole to be filled by you! Not used in anything other than the tutorial.")
      document(1,
        "src/Vatras/Tutorial/B_Translation.lagda.md:conf e c²ᶜᶜ = {!!}",
        "Intentional hole to be filled by you! Not used in anything other than the tutorial.")
      document(1,
        "src/Vatras/Tutorial/B_Translation.lagda.md:fnoc e cᵐʸ = {!!}",
        "Intentional hole to be filled by you! Not used in anything other than the tutorial.")
      document(1,
        "src/Vatras/Tutorial/B_Translation.lagda.md:preservation-⊆[] e c = {!!}",
        "Intentional hole to be filled by you! Not used in anything other than the tutorial.")
      document(1,
        "src/Vatras/Tutorial/B_Translation.lagda.md:preservation-⊇[] e c = {!!}",
        "Intentional hole to be filled by you! Not used in anything other than the tutorial.")
      document(1,
        "src/Vatras/Tutorial/B_Translation.lagda.md:translate (D ⟨ l , r ⟩) = {!!}",
        "Intentional hole to be filled by you! Not used in anything other than the tutorial.")
      document(1,
        "src/Vatras/Tutorial/B_Translation.lagda.md:translate (a -< cs >-)  = {!!}",
        "Intentional hole to be filled by you! Not used in anything other than the tutorial.")
      document(1,
        "src/Vatras/Tutorial/C_Proofs.lagda.md:  {!!}   -- write down the proof of correctness in this hole",
        "Intentional hole to be filled by you! Not used in anything other than the tutorial.")
      document(1,
        "src/Vatras/Tutorial/C_Proofs.lagda.md:  {!!} , -- write down the expression in this hole",
        "Intentional hole to be filled by you! Not used in anything other than the tutorial.")
      document(1,
        "src/Vatras/Tutorial/C_Proofs.lagda.md:2CC≽MyLang = {!!}",
        "Intentional hole to be filled by you! Not used in anything other than the tutorial.")
      document(1,
        "src/Vatras/Tutorial/C_Proofs.lagda.md:MyLang-is-Sound = {!!}",
        "Intentional hole to be filled by you! Not used in anything other than the tutorial.")

      exitCode=0
    }
'

possibleInconsistencies() {
  grepRecursive() {
    find src -name '*agda*' -exec grep "$@" {} + | sort
  }

  echo 'postulates:'
  grepRecursive 'postulate'

  echo
  echo 'terminating pragmas:'
  grepRecursive 'TERMINATING'

  echo
  echo 'holes:'
  grepRecursive -F '{!'
  grepRecursive ' ?\( \|$\)'
}

withDoc() {
  # Used for alignment.
  # Cannot use 'column' because it doesn't exist on macOS.
  columnCount="$(possibleInconsistencies | awk 'BEGIN { max=0 } { if (max < length($0)) max=length($0) } END { print max }')"

  awk -e "$awkDocumentationMap" -e '
    {
      padding='"$columnCount"' - length($0) + 3

      if ($0 in ignore) {
        print $0
      } else if (++counts[$0] ":" $0 in doc) {
        printf "%s% *s%s\n", $0, padding, "", doc[counts[$0] ":" $0]
      } else {
        exitCode=1
        printf "\033[30;41m%s% *s%s\033[39;49m\n", $0, padding, "", "UNDOCUMENTED!!!"
      }
    }

    END {
      exit exitCode
    }
  '
}

ciMessages() {
  awk -v FS=: -e "$awkDocumentationMap" -e '
    {
      if ($0 in ignore) {
      } else if (++counts[$0] ":" $0 in doc) {
        delete doc[counts[$0] ":" $0]
      } else {
        exitCode=1

        printf("::error file=%s,line=", $1)

        # Yeah, awk has no builtin escaping
        gsub("'\''", "'\''\\'\'''\''", $1)
        pattern=$0
        gsub("^[^:]*:", "", pattern)
        gsub("'\''", "'\''\\'\'''\''", pattern)

        system("grep -F -n -e '\''" pattern "'\'' '\''" $1 "'\'' | head -n 1 | sed \"s/:.*/::Undocumented source of inconsistency./\"")
      }
    }

    END {
      for (line in doc) {
        exitCode=1

        gsub("%", "%25", line)
        gsub("\\n", "%0A", line)
        gsub("\"", "\\\"", line)

        documentation=doc[line]
        gsub("%", "%25", documentation)
        gsub("\\n", "%0A", documentation)
        gsub("\"", "\\\"", documentation)

        print "::error file=scripts/find-inconsistency-sources.sh::Obsolete inconsistency documentation:%0Adoc[\"" line "\"]=\"" documentation "\""
      }

      exit exitCode
    }
  '
}

if [ "$1" = "--with-documentation" ]
then
  possibleInconsistencies | withDoc
  exitCode=$?

  echo
  echo "Hint: Use '$0 --with-documentation | less -S' to be able to see documentation to each source and to scroll horizontally"
elif [ "$1" = "--ci" ]
then
  possibleInconsistencies | ciMessages
  exitCode=$?
else
  possibleInconsistencies
  exitCode=$?

  echo
  echo "Hint: Use '$0 --with-documentation | less -S' to be able to scroll horizontally"
fi

exit $exitCode
