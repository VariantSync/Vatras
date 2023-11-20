#!/usr/bin/env bash

cd "$(dirname ${BASH_SOURCE[0]})/../src"
projectDir="$PWD"

agdaFiles=( $(find . -regextype posix-extended -regex '.*/.*\.l?agda(.md)?' | sed 's|^./||') )

parseInfoAction() {
  echo "$1" | sed 's/^\([^"]*"\)\{3\}//; s/"[^"]*$//;'
}

parseFileNames() {
  messages="$1"
  shift

  while read -r message
  do
    "$@" $(echo "$message" | sed 's/^\([^\]*\):\([0-9]*\),\([0-9]*\)-\([0-9]*\)\\n.*/\1 \2 \3 \4/') "$(echo "$message" | sed 's/^[^\]*\\n//')"
  done < <(
    echo "$messages" |
      sed "s|^$projectDir/||; s|\\\\n$projectDir/|\\n|g"
  )
}

if [ "$1" = "github-action" ]
then
  error() {
    if [ "$1" = "$2" ]
    then
      echo "::error file=src/$2,line=$3,col=$4,endColumn=$5::$(echo "$6" | sed 's/%/%25/g; s/\\n/%0A/g')"
    else
      dependencyErrors["$1"]="$2"
    fi
  }
  warning() {
    if [ "$1" = "$2" ]
    then
      echo "::warning file=src/$2,line=$3,col=$4,endColumn=$5::$(echo "$6" | sed 's/%/%25/g; s/\n/%0A/g')"
    fi
  }
  goal() {
    echo "::notice ::$message"
  }
  dependencyErrors() {
    echo -n "::notice ::The following files couldn't be checked because a dependency of them has errors:"
    for file in "${!dependencyErrors[@]}"
    do
      echo -n "%0A  $file (depends on ${dependencyErrors["$file"]})"
    done
    echo
  }
else
  error() {
    if [ "$1" = "$2" ]
    then
      echo "${7:-error} in $2 on line $3 column $4-$5 while checking $1:"
      echo "  $6" | sed 's/\\n/\n  /g'
    elif [ "${7:-error}" = "error" ]
    then
      dependencyErrors["$1"]="$2"
    fi
  }
  warning() {
    error "$@" warning
  }
  goal() {
    echo "goal in $1"
    echo "  $2" | sed 's/\\n/\n  /g'
  }
  dependencyErrors() {
    echo "note: The following files couldn't be checked because a dependency of them has errors:"
    for file in "${!dependencyErrors[@]}"
    do
      echo "  $file (depends on ${dependencyErrors["$file"]})"
    done
  }
fi

processMessages() {
  declare -A dependencyErrors
  currentFileIndex=-1
  exitCode=0

  while read -r line
  do
    case "$line" in
      *'"*Error*"'*)
        exitCode=1
        parseFileNames "$(parseInfoAction "$line")" error "${agdaFiles[currentFileIndex]}"
        ;;
      *'"*All Warnings*"'*)
        parseFileNames "$(parseInfoAction "$line")" warning "${agdaFiles[currentFileIndex]}"
        ;;
      *'"*All Goals*"'*)
        goal "${agdaFiles[currentFileIndex]}" "$(parseInfoAction "$line")"
        ;;
      '(agda2-highlight-clear)')
        (( ++ currentFileIndex ))
        ;;
    esac
  done

  if [ "${#dependencyErrors[@]}" -gt 0 ]
  then
    dependencyErrors
  fi

  return "$exitCode"
}

processMessages < <(
  printf '%s\n' "${agdaFiles[@]}" |
    sed 's/.*/IOTCM "\0" None Indirect (Cmd_load "\0" [])/' |
    agda --interaction |
    grep -F -e '"*Error*"' -e '*All Warnings*' -e '*All Goals*' -e '(agda2-highlight-clear)'
  )
