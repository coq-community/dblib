#!/bin/bash
set -euo pipefail

function doshow () {
    set -x;
    "$@"
    { ret=$?; } 2>/dev/null
    { set +x; } 2>/dev/null
    return $ret
}

function coq {
    doshow docker exec COQ bash -c "$1 "'"$@"' "$1" "$@"
}

function coqsh {
    doshow docker exec COQ /bin/bash -c "$1"
}

function begin {
    printf 'travis_fold:start:%s\r' "$1"
}

function end {
    printf 'travis_fold:end:%s\r' "$1"
}

function install {
    begin pull
    COQ_IMAGE="${COQ_IMAGE-coqorg/coq:$COQ}"
    doshow docker pull "$COQ_IMAGE"
    doshow docker run -d -i --init --name=COQ -v "$TRAVIS_BUILD_DIR:/home/coq/$PACKAGE" -w /home/coq/"$PACKAGE" "$COQ_IMAGE"
    end pull

    begin opam-deps
    coqsh "echo 'eval \$(opam env)' >>~/.bashrc"
    coq opam update -y
    coq opam pin add "$PACKAGE" . -vynk path
    coq opam install "$PACKAGE" -vyj "$NJOBS" --deps-only
    coq opam config list
    coq opam repo list
    coq opam list
    end opam-deps
}

function script {
    coq opam install "$PACKAGE" -vyj "$NJOBS"
}

function after_script {
    coq opam uninstall "$PACKAGE" -vy
    doshow docker stop COQ
}

env
begin "$1"
"$@"
end "$1"
