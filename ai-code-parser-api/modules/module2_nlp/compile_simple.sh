#!/bin/bash
# Simple compilation - you may need to edit your .c files to exclude main()
echo 'This script assumes your .c files do not have main() functions'
echo 'If they do, please comment out or remove the main() functions first'
echo ''
read -p 'Have you removed/commented main() functions from your .c files? (y/n): ' response
if [ "$response" = "y" ]; then
    echo 'Compiling test runner...'
    gcc -o test_runner test_runner.c ..\..\user_code.c -lm
    if [ $? -eq 0 ]; then
        echo 'Compilation successful. Run ./test_runner to execute tests.'
    else
        echo 'Compilation failed. Check the errors above.'
    fi
else
    echo 'Please edit your .c files first, then run this script again.'
fi
