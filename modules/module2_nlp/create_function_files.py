#!/usr/bin/env python3
"""
Helper script to create function-only versions of C files
(removes main() functions for linking with test runner)
"""
import re
import os
from pathlib import Path

def remove_main_function(c_content):
    """Remove main function from C code"""
    # Pattern to match main function
    main_pattern = r'int\s+main\s*\([^)]*\)\s*\{(?:[^{}]*\{[^{}]*\})*[^{}]*\}'
    # Remove main function
    cleaned = re.sub(main_pattern, '', c_content, flags=re.DOTALL)
    return cleaned

# Process each C file and create function-only version in current directory
print("Processing ../../data/sample_code/factorial.c...")
try:
    with open("../../data/sample_code/factorial.c", "r") as file:
        content = file.read()
    cleaned = remove_main_function(content)
    with open("factorial_func.c", "w") as out:
        out.write(cleaned)
    print("Created factorial_func.c")
except Exception as e:
    print("Error processing ../../data/sample_code/factorial.c: {e}")

print("Processing ../../data/sample_code/pid_controller.c...")
try:
    with open("../../data/sample_code/pid_controller.c", "r") as file:
        content = file.read()
    cleaned = remove_main_function(content)
    with open("pid_controller_func.c", "w") as out:
        out.write(cleaned)
    print("Created pid_controller_func.c")
except Exception as e:
    print("Error processing ../../data/sample_code/pid_controller.c: {e}")

print("\nFunction-only files created in current directory!")
print("Now run: gcc -o test_runner test_runner.c factorial_func.c pid_controller_func.c -lm")
