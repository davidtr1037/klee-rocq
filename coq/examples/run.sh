#!/bin/bash
CURRENT_PATH=$(dirname ${BASH_SOURCE[0]})
ROOT=$(realpath ${CURRENT_PATH}/../..)
KLEE=klee

function run_klee {
    output=/tmp/out.v
    bc_file=$1
    echo "testing ${bc_file}"
    $KLEE -search=dfs -generate-proof -proof-output-path=${output} $1 &> /dev/null
    coqc -Q ${ROOT}/coq SE ${output}
}

run_klee test_1.bc &&
run_klee test_2.bc &&
run_klee test_3.bc &&
run_klee test_4.bc &&
#run_klee test_5.bc &&
run_klee test_6.bc &&
run_klee test_7.bc
