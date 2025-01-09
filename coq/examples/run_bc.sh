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

run_klee $1
