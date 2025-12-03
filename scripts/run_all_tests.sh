#!/bin/bash
echo "Running all Phase 1-2 tests"

# Activate virtual environment
if [ -f "venv/bin/activate" ]; then
    source venv/bin/activate
    echo "Virtual environment activated"
else
    echo "Virtual environment not found, using system Python"
fi

# Run main application demo
echo "Running main application demo..."
python main.py
echo ""

# Run pytest integration tests
echo " Running pytest integration tests..."
pytest tests/test_integration.py -v --tb=short
echo ""

# Test individual modules
echo " Testing individual modules..."

echo "Testing Module 1 (AI Debugging)..."
python -c "
from modules.module1_debugging import AIDebugger
debugger = AIDebugger()
result = debugger.test_integration()
print(f'✅ Module 1: {result[\"status\"]}')
"

echo "Testing Module 2 (NLP Test Generation)..."
python -c "
from modules.module2_nlp import NLPTestGenerator
generator = NLPTestGenerator()
result = generator.test_basic_functionality()
print(f'✅ Module 2: {result[\"status\"]}')
"

echo "Testing Module 3 (Formal Verification)..."
python -c "
from modules.module3_formal import FormalVerifier
verifier = FormalVerifier()
result = verifier.test_framac_integration()
print(f'✅ Module 3: {result[\"status\"]}')
"

echo "Testing Module 4 (Simulink Generation)..."
python -c "
from modules.module4_simulink import SimulinkGenerator
generator = SimulinkGenerator()
result = generator.test_basic_parsing()
print(f'✅ Module 4: {result[\"status\"]}')
"

echo "All tests completed!"
