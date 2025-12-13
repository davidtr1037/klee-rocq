#!/bin/bash
CURRENT_PATH=$(dirname ${BASH_SOURCE[0]})
ROOT=$(realpath ${CURRENT_PATH}/../..)
KLEE=klee

function run_klee_no_opt {
    bc_file=$1
    output=$2
    echo "testing ${bc_file}"
    $KLEE \
        -search=dfs \
        -rewrite-equalities=0 \
        -generate-proof \
        -proof-output-path=${output} \
        $1
    time coqc -Q ${ROOT}/coq SE ${output}
    ls -lh ${output}
}

function run_klee {
    bc_file=$1
    output=$2
    echo "testing ${bc_file}"
    $KLEE \
        -search=dfs \
        -rewrite-equalities=0 \
        -generate-proof \
        -proof-output-path=${output} \
        -optimize-proof \
        -cache-pc-expr \
        -cache-register-expr \
        -cache-stack-expr \
        -cache-sym-names \
        $1
    time coqc -Q ${ROOT}/coq SE ${output}
    ls -lh ${output}
}

run_klee $1 ${ROOT}/coq/out.v
