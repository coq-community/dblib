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
    cmd="$1"
    shift
    doshow docker exec COQ bash -c "$cmd "'"$@"' "$cmd" "$@"
}

function coqsh {
    doshow docker exec COQ /bin/bash -c "$1"
}

function begin {
    echo -e "travis_fold:start:$1${ANSI_YELLOW}$2${ANSI_CLEAR}"
}

function end {
    echo -e "\ntravis_fold:end:$1\r"
}

function install {
    COQ_IMAGE="${COQ_IMAGE-coqorg/coq:$COQ}"
    begin pull "Pull $COQ_IMAGE and start container"
    doshow docker pull "$COQ_IMAGE"
    doshow docker run -d -i --init --name=COQ -v "$TRAVIS_BUILD_DIR:/home/coq/$PACKAGE" -w /home/coq/"$PACKAGE" "$COQ_IMAGE"
    coqsh "echo 'eval \$(opam env)' >>~/.bashrc"
    end pull

    begin opam-deps "Install OPAM dependencies"
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

"$@"
