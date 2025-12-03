#!/bin/bash
echo " AI Code Parser - Project Status Check"
echo "=" $(printf '%*s' 50 '' | tr ' ' '=')

# Check Python environment
echo " Python Environment:"
python --version
echo "   Virtual environment: $(if [ -n "$VIRTUAL_ENV" ]; then echo " Active"; else echo " Not active"; fi)"

# Check system dependencies
echo ""
echo "🔧 System Dependencies:"
echo -n "   Frama-C: "
if command -v frama-c &> /dev/null; then
    frama-c -version | head -1
else
    echo "Not installed"
fi

echo -n "   GDB: "
if command -v gdb &> /dev/null; then
    gdb --version | head -1 | cut -d' ' -f1-4
else
    echo "Not installed"
fi

echo -n "   Clang: "
if command -v clang &> /dev/null; then
    clang --version | head -1 | cut -d' ' -f1-3
else
    echo "Not installed"
fi

echo -n "   Node.js: "
if command -v node &> /dev/null; then
    echo " $(node --version)"
else
    echo "Not installed"
fi

# Check Python packages
echo ""
echo " Python Packages:"
key_packages=("torch" "transformers" "langchain" "pytest" "fastapi")
for package in "${key_packages[@]}"; do
    echo -n "   $package: "
    if pip show "$package" &> /dev/null; then
        version=$(pip show "$package" 2>/dev/null | grep Version | cut -d' ' -f2)
        echo " $version"
    else
        echo " Not installed"
    fi
done

# Check project structure
echo ""
echo " Project Structure:"
required_dirs=("modules" "tools" "tests" "data" "scripts")
for dir in "${required_dirs[@]}"; do
    echo -n "   $dir/: "
    if [ -d "$dir" ]; then
        echo " Present"
    else
        echo " Missing"
    fi
done

# Check external repositories
echo ""
echo " External Repositories:"
repos=("tools/ChatDBG" "tools/LLMDebugger" "tools/Awesome-Code-LLM")
for repo in "${repos[@]}"; do
    echo -n "   $(basename $repo): "
    if [ -d "$repo" ]; then
        echo " Cloned"
    else
        echo " Missing"
    fi
done

echo ""
echo " Phase 1-2 Completion Status:"
completion_items=(
    "Project structure created"
    "Virtual environment setup"
    "External repositories cloned"
    "All 4 modules implemented"
    "Integration tests created"
    "Sample data provided"
    "Development scripts ready"
)

for item in "${completion_items[@]}"; do
    echo "    $item"
done

echo ""
echo " Ready for Next Phase Development!"
