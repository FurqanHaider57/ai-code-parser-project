#!/bin/bash
# Auto-generated compilation script
echo 'Compiling C source files to object files...'

echo 'Compiling ..\..\user_code.c to user_code.o...'
gcc -c ..\..\user_code.c -o user_code.o -DSKIP_MAIN
if [ $? -ne 0 ]; then
    echo 'Failed to compile ..\..\user_code.c'
    exit 1
fi

echo 'Compiling ..\..\user_code.c to user_code.o...'
gcc -c ..\..\user_code.c -o user_code.o -DSKIP_MAIN
if [ $? -ne 0 ]; then
    echo 'Failed to compile ..\..\user_code.c'
    exit 1
fi

echo 'Compiling ..\..\user_code.c to user_code.o...'
gcc -c ..\..\user_code.c -o user_code.o -DSKIP_MAIN
if [ $? -ne 0 ]; then
    echo 'Failed to compile ..\..\user_code.c'
    exit 1
fi

echo 'Compiling ..\..\user_code.c to user_code.o...'
gcc -c ..\..\user_code.c -o user_code.o -DSKIP_MAIN
if [ $? -ne 0 ]; then
    echo 'Failed to compile ..\..\user_code.c'
    exit 1
fi

echo 'Linking test runner with object files...'
gcc -o test_runner test_runner.c user_code.o -lm
if [ $? -eq 0 ]; then
    echo 'Compilation successful. Run ./test_runner to execute tests.'
    echo 'Cleaning up object files...'
    rm -f user_code.o
else
    echo 'Linking failed. Check the errors above.'
    exit 1
fi
