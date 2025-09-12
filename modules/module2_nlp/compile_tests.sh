#!/bin/bash
# Auto-generated compilation script
echo 'Compiling C source files to object files...'

echo 'Compiling ../../data/sample_code/factorial.c to factorial.o...'
gcc -c ../../data/sample_code/factorial.c -o factorial.o -DSKIP_MAIN
if [ $? -ne 0 ]; then
    echo 'Failed to compile ../../data/sample_code/factorial.c'
    exit 1
fi

echo 'Compiling ../../data/sample_code/factorial.c to factorial.o...'
gcc -c ../../data/sample_code/factorial.c -o factorial.o -DSKIP_MAIN
if [ $? -ne 0 ]; then
    echo 'Failed to compile ../../data/sample_code/factorial.c'
    exit 1
fi

echo 'Compiling ../../data/sample_code/factorial.c to factorial.o...'
gcc -c ../../data/sample_code/factorial.c -o factorial.o -DSKIP_MAIN
if [ $? -ne 0 ]; then
    echo 'Failed to compile ../../data/sample_code/factorial.c'
    exit 1
fi

echo 'Compiling ../../data/sample_code/factorial.c to factorial.o...'
gcc -c ../../data/sample_code/factorial.c -o factorial.o -DSKIP_MAIN
if [ $? -ne 0 ]; then
    echo 'Failed to compile ../../data/sample_code/factorial.c'
    exit 1
fi

echo 'Compiling ../../data/sample_code/pid_controller.c to pid_controller.o...'
gcc -c ../../data/sample_code/pid_controller.c -o pid_controller.o -DSKIP_MAIN
if [ $? -ne 0 ]; then
    echo 'Failed to compile ../../data/sample_code/pid_controller.c'
    exit 1
fi

echo 'Compiling ../../data/sample_code/pid_controller.c to pid_controller.o...'
gcc -c ../../data/sample_code/pid_controller.c -o pid_controller.o -DSKIP_MAIN
if [ $? -ne 0 ]; then
    echo 'Failed to compile ../../data/sample_code/pid_controller.c'
    exit 1
fi

echo 'Linking test runner with object files...'
gcc -o test_runner test_runner.c pid_controller.o factorial.o -lm
if [ $? -eq 0 ]; then
    echo 'Compilation successful. Run ./test_runner to execute tests.'
    echo 'Cleaning up object files...'
    rm -f pid_controller.o factorial.o
else
    echo 'Linking failed. Check the errors above.'
    exit 1
fi
