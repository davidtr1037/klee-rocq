#!/bin/bash
CURRENT_PATH=$(dirname ${BASH_SOURCE[0]})
ROOT=$(realpath ${CURRENT_PATH}/../..)
KLEE=klee

function run_klee {
    output=/tmp/out.v
    bc_file=$1
    echo "testing ${bc_file}"
    $KLEE \
        -search=dfs \
        -rewrite-equalities=0 \
        -generate-proof \
        -decompose-state \
        -cache-pc-expr \
        -cache-register-expr \
        -cache-stack-expr \
        -cache-sym-names \
        -proof-output-path=${output} \
        $1 &> /dev/null
    coqc -Q ${ROOT}/coq SE ${output}
}

files=(\
    test_1.bc \
    test_2.bc \
    test_3.bc \
    test_4.bc \
    test_5.bc \
    test_6.bc \
    test_7.bc \
    test_8.bc \
    test_9.bc \
    test_10.bc \
    test_11.bc \
    test_12.bc \
    test_13.bc \
    test_14.bc \
    test_15.bc \
    test_16.bc \
    test_17.bc \
    test_18.bc \
    test_19.bc \
    test_20.bc \
)
for f in "${files[@]}"; do
    run_klee $f
done
