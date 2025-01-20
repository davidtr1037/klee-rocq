#!/bin/bash
CURRENT_PATH=$(dirname ${BASH_SOURCE[0]})
ROOT=$(realpath ${CURRENT_PATH}/../..)
KLEE=klee

function run_klee_no_opt {
    output=/tmp/out.v
    bc_file=$1
    echo "testing ${bc_file}"
    $KLEE \
        -search=dfs \
        -rewrite-equalities=0 \
        -generate-proof \
        -proof-output-path=${output} \
        $1 &> /dev/null
    test $? -eq 0 || echo "KLEE failed..."
    coqc -Q ${ROOT}/coq SE ${output}
    test $? -eq 0 || echo "coqc failed..."
}

function run_klee {
    output=/tmp/out.v
    bc_file=$1
    echo "testing ${bc_file}"
    $KLEE \
        -search=dfs \
        -rewrite-equalities=0 \
        -generate-proof \
        -optimize-proof \
        -cache-pc-expr \
        -cache-register-expr \
        -cache-stack-expr \
        -cache-sym-names \
        -proof-output-path=${output} \
        $1 &> /dev/null
    test $? -eq 0 || echo "KLEE failed..."
    coqc -Q ${ROOT}/coq SE ${output}
    test $? -eq 0 || echo "coqc failed..."
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

function run_all_no_opt {
    for f in "${files[@]}"; do
        run_klee_no_opt $f
    done
}

function run_all {
    for f in "${files[@]}"; do
        run_klee $f
    done
}

run_all
