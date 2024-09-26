#!/bin/bash
CURRENT_PATH=$(dirname ${BASH_SOURCE[0]})
ROOT=$(realpath ${CURRENT_PATH}/../..)
KLEE=klee

function run_klee {
    output=${ROOT}/coq/out.v
    debug_output=${ROOT}/coq/debug.v
    po_output=/tmp/po
    bc_file=$1
    echo "testing ${bc_file}"
    $KLEE \
        -search=dfs \
        -generate-proof \
        -proof-output-path=${output} \
        -proof-debug-script-path=${debug_output} \
        -decompose-state \
        -cache-coq-expr \
        -optimize-proof \
        $1 &> /dev/null
    time coqc -Q ${ROOT}/coq SE ${output}
    coqc -Q ${ROOT}/coq SE ${debug_output} > ${po_output}
    ls -lh ${po_output}
}

run_klee $1
