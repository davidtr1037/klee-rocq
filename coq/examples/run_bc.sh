#!/bin/bash
CURRENT_PATH=$(dirname ${BASH_SOURCE[0]})
ROOT=$(realpath ${CURRENT_PATH}/../..)
KLEE=klee

function run_klee {
    output=${ROOT}/coq/out.v
    bc_file=$1
    echo "testing ${bc_file}"
    $KLEE \
        -search=dfs \
        -generate-proof \
        -proof-output-path=${output} \
        -optimize-proof \
        -decompose-state \
        -cache-pc-expr \
        -cache-register-expr \
        -cache-stack-expr \
        $1 &> /dev/null
    time coqc -Q ${ROOT}/coq SE ${output}
    ls -lh ${output}
}

run_klee $1
