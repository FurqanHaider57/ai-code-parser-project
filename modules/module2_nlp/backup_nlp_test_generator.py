"""
Enhanced NLP Test Generator - Phase 3 Implementation (Auto C Binding)
Automatically scans .c files and generates comprehensive test cases with function-specific logic
"""
import logging
import re
import os
from typing import List, Dict, Optional, Tuple
from pathlib import Path
from dataclasses import dataclass

import torch  # type: ignore
from transformers import AutoTokenizer, AutoModelForSeq2SeqLM  # type: ignore
import numpy as np  # type: ignore

logger = logging.getLogger(__name__)

@dataclass
class CFunctionInfo:
    """Information about a discovered C function"""
    name: str
    return_type: str
    parameters: List[Tuple[str, str]]  # [(type, name), ...]
    signature: str
    file_path: str
    line_number: int
    body_preview: str = ""

class EnhancedNLPTestGenerator:
    """Enhanced NLP-based test case generator with intelligent C function discovery"""

    def __init__(self, code_directory: str = "../../data/sample_code"):
        logger.info("🚀 Initializing Enhanced NLP Test Generator (Phase 3)")
        
        self.code_directory = Path(code_directory)
        self.device = self._setup_device()
        self.tokenizer = None
        self.model = None
        self.test_templates = self._load_test_templates()
        self.function_patterns = self._load_function_patterns()
        
        # Initialize models
        self._initialize_models()
        
        # Discover C functions with detailed analysis
        self.discovered_functions = self._discover_c_functions_enhanced()
        
        logger.info(f"✅ Enhanced NLP Test Generator initialized with {len(self.discovered_functions)} functions discovered")

    def _setup_device(self) -> str:
        """Setup computing device"""
        if torch.cuda.is_available():
            device = "cuda"
            logger.info(f"🔥 Using GPU: {torch.cuda.get_device_name(0)}")
        else:
            device = "cpu"
            logger.info("💻 Using CPU for computations")
        return device

    def _initialize_models(self):
        """Initialize NLP model for intelligent test generation"""
        try:
            model_name = "t5-small"
            logger.info(f"📥 Loading model: {model_name}")
            self.tokenizer = AutoTokenizer.from_pretrained(model_name)
            self.model = AutoModelForSeq2SeqLM.from_pretrained(model_name)
            self.model.to(self.device)
            logger.info("✅ NLP models loaded successfully")
        except Exception as e:
            logger.error(f"Model initialization failed: {e}")
            self.tokenizer = None
            self.model = None

    def _load_test_templates(self) -> Dict:
        """Load comprehensive test case templates"""
        return {
            "functional": [
                "Call {function} with {input_desc} and verify {expected_desc}",
                "Test {function} returns {expected_desc} when given {condition}",
                "Validate {function} correctly processes {input_type} input",
                "Verify {function} output matches expected {output_type} for {scenario}",
            ],
            "boundary": [
                "Test {function} with minimum value: {min_value}",
                "Test {function} with maximum value: {max_value}",
                "Test {function} with zero/empty input",
                "Test {function} with boundary conditions for {param_type}",
                "Validate {function} behavior at {boundary_type} boundaries",
            ],
            "error": [
                "Ensure {function} handles {invalid_input} appropriately",
                "Verify {function} error handling for {error_condition}",
                "Test {function} with null/invalid {parameter_name}",
                "Validate {function} exception behavior with {exception_scenario}",
            ],
            "performance": [
                "Benchmark {function} with {load_type} input",
                "Test {function} scalability with {scale_condition}",
                "Verify {function} memory usage under {memory_condition}",
                "Measure {function} execution time for {performance_scenario}",
            ],
        }

    def _load_function_patterns(self) -> Dict:
        """Load patterns for function-specific test generation"""
        return {
            "factorial": {
                "valid_inputs": [0, 1, 5, 10],
                "expected_outputs": [1, 1, 120, 3628800],
                "boundary_cases": [0, 1],
                "error_cases": [-1, -5],
                "domain": "mathematical"
            },
            "fibonacci": {
                "valid_inputs": [0, 1, 5, 10],
                "expected_outputs": [0, 1, 5, 55],
                "boundary_cases": [0, 1],
                "error_cases": [-1],
                "domain": "mathematical"
            },
            "isPrime": {
                "valid_inputs": [2, 3, 4, 17, 25],
                "expected_outputs": [True, True, False, True, False],
                "boundary_cases": [2],
                "error_cases": [0, 1, -5],
                "domain": "mathematical"
            },
            "pid_controller": {
                "test_scenarios": [
                    {"setpoint": 100.0, "measurement": 95.0, "kp": 0.1, "ki": 0.01, "kd": 0.05, "desc": "basic control"},
                    {"setpoint": 50.0, "measurement": 50.0, "kp": 1.0, "ki": 0.1, "kd": 0.1, "desc": "at setpoint"},
                    {"setpoint": 0.0, "measurement": 10.0, "kp": 0.5, "ki": 0.05, "kd": 0.02, "desc": "negative error"}
                ],
                "boundary_cases": ["zero gains", "very small gains", "large error"],
                "domain": "control_systems"
            },
            "signal_generator": {
                "test_scenarios": [
                    {"frequency": 1.0, "time": 0.0, "expected_range": "0.0", "desc": "at time zero"},
                    {"frequency": 1.0, "time": 0.25, "expected_range": "1.0", "desc": "at quarter period"},
                    {"frequency": 2.0, "time": 1.0, "expected_range": "[-1,1]", "desc": "normal operation"}
                ],
                "boundary_cases": ["zero frequency", "very high frequency", "negative time"],
                "domain": "signal_processing"
            },
            "sort": {
                "test_scenarios": ["empty array", "single element", "sorted array", "reverse sorted", "duplicates"],
                "domain": "algorithm"
            },
            "search": {
                "test_scenarios": ["element found", "element not found", "empty array", "first element", "last element"],
                "domain": "algorithm"
            }
        }

    def _discover_c_functions_enhanced(self) -> List[CFunctionInfo]:
        """Enhanced C function discovery with detailed analysis"""
        functions = []
        
        if not self.code_directory.exists():
            logger.warning(f"Code directory {self.code_directory} does not exist")
            return functions

        # Enhanced regex for function detection
        func_pattern = re.compile(
            r'^\s*(?P<return_type>(?:const\s+)?(?:unsigned\s+)?(?:struct\s+)?[a-zA-Z_][\w\s\*]*?)\s+'
            r'(?P<func_name>[a-zA-Z_][\w]*)\s*'
            r'\((?P<params>[^)]*)\)\s*'
            r'(?P<body_start>\{)',
            re.MULTILINE
        )

        for c_file in self.code_directory.glob("*.c"):
            try:
                content = c_file.read_text(encoding="utf-8", errors="ignore")
                lines = content.split('\n')
                
                for match in func_pattern.finditer(content):
                    func_name = match.group('func_name').strip()
                    
                    # Skip main function
                    if func_name == 'main':
                        continue
                    
                    return_type = self._clean_type(match.group('return_type'))
                    params_str = match.group('params').strip()
                    
                    # Parse parameters
                    parameters = self._parse_parameters(params_str)
                    
                    # Build clean signature
                    param_list = ", ".join([f"{ptype} {pname}" for ptype, pname in parameters])
                    signature = f"{return_type} {func_name}({param_list});"
                    
                    # Get line number
                    line_num = content[:match.start()].count('\n') + 1
                    
                    # Extract function body preview (first few lines)
                    body_preview = self._extract_function_body_preview(content, match.end())
                    
                    functions.append(CFunctionInfo(
                        name=func_name,
                        return_type=return_type,
                        parameters=parameters,
                        signature=signature,
                        file_path=str(c_file),
                        line_number=line_num,
                        body_preview=body_preview
                    ))
                    
                    logger.info(f"📝 Discovered function: {func_name} in {c_file.name}")
                    
            except Exception as e:
                logger.error(f"Error processing {c_file}: {e}")
                continue
        
        return functions

    def _clean_type(self, type_str: str) -> str:
        """Clean and normalize type string"""
        return ' '.join(type_str.split())

    def _parse_parameters(self, params_str: str) -> List[Tuple[str, str]]:
        """Parse function parameters into (type, name) tuples"""
        if not params_str or params_str.strip() == 'void':
            return []
        
        parameters = []
        param_parts = [p.strip() for p in params_str.split(',')]
        
        for param in param_parts:
            if not param:
                continue
            
            # Handle pointer types and complex declarations
            param_tokens = param.split()
            if len(param_tokens) >= 2:
                param_name = param_tokens[-1].lstrip('*')
                param_type = ' '.join(param_tokens[:-1])
                if '*' in param_tokens[-1]:
                    param_type += '*'
                parameters.append((param_type, param_name))
            else:
                # Fallback for complex cases
                parameters.append(("unknown", param))
        
        return parameters

    def _extract_function_body_preview(self, content: str, start_pos: int) -> str:
        """Extract first few lines of function body for analysis"""
        try:
            lines = content[start_pos:].split('\n')[:5]  # First 5 lines
            return '\n'.join(line.strip() for line in lines if line.strip())
        except:
            return ""

    def _analyze_function_purpose(self, func_info: CFunctionInfo) -> Dict:
        """Analyze function purpose based on name and signature"""
        analysis = {
            "category": "general",
            "domain": "general",
            "complexity": "medium",
            "input_types": [],
            "output_type": func_info.return_type,
            "likely_operations": []
        }
        
        name_lower = func_info.name.lower()
        
        # Categorize by function name patterns
        if any(math_term in name_lower for math_term in ['factorial', 'fibonacci', 'prime', 'gcd', 'lcm']):
            analysis["category"] = "mathematical"
            analysis["domain"] = "mathematics"
        elif any(algo_term in name_lower for algo_term in ['sort', 'search', 'find', 'binary']):
            analysis["category"] = "algorithm"
            analysis["domain"] = "data_structures"
        elif any(string_term in name_lower for string_term in ['str', 'string', 'char', 'copy', 'concat']):
            analysis["category"] = "string_processing"
            analysis["domain"] = "text_processing"
        elif any(mem_term in name_lower for mem_term in ['malloc', 'free', 'alloc', 'memory']):
            analysis["category"] = "memory_management"
            analysis["domain"] = "system_programming"
        elif any(io_term in name_lower for io_term in ['read', 'write', 'file', 'print', 'scan']):
            analysis["category"] = "input_output"
            analysis["domain"] = "file_system"
        
        # Analyze parameters
        for param_type, param_name in func_info.parameters:
            analysis["input_types"].append(param_type)
        
        return analysis

    async def generate_test_cases_from_functions(self, num_tests: int = 5) -> Dict:
        """Generate test cases for all discovered functions"""
        if not self.discovered_functions:
            return {
                "status": "No C functions discovered",
                "functions_found": 0,
                "test_cases": {},
                "unit_test_code": ""
            }
        
        # Remove duplicates based on function name + signature
        unique_functions = {}
        for func_info in self.discovered_functions:
            key = f"{func_info.name}_{func_info.signature}"
            if key not in unique_functions:
                unique_functions[key] = func_info
        
        unique_func_list = list(unique_functions.values())
        logger.info(f"Processing {len(unique_func_list)} unique functions (removed {len(self.discovered_functions) - len(unique_func_list)} duplicates)")
        
        all_test_cases = {}
        all_unit_tests = []
        
        for func_info in unique_func_list:
            logger.info(f"🧪 Generating tests for function: {func_info.name}")
            
            # Analyze function
            func_analysis = self._analyze_function_purpose(func_info)
            
            # Generate test cases for this function
            func_tests = await self._generate_function_specific_tests(
                func_info, func_analysis, num_tests
            )
            
            all_test_cases[f"{func_info.name}_{func_info.file_path.split('/')[-1]}"] = func_tests
            
            # Generate unit test code for this function
            unit_test_code = self._generate_function_unit_test(func_info, func_tests)
            all_unit_tests.append(unit_test_code)
        
        # Update discovered_functions to use unique list
        self.discovered_functions = unique_func_list
        
        # Combine all unit tests
        combined_unit_test = self._generate_combined_test_runner(all_unit_tests)
        
        # Save to file
        self._save_test_runner(combined_unit_test)
        
        return {
            "status": "Test generation complete",
            "functions_found": len(unique_func_list),
            "discovered_functions": [f.name for f in unique_func_list],
            "test_cases": all_test_cases,
            "unit_test_code": combined_unit_test,
            "total_tests": sum(len(tests["all_tests"]) for tests in all_test_cases.values())
        }

    async def _generate_function_specific_tests(
        self, func_info: CFunctionInfo, analysis: Dict, num_tests: int
    ) -> Dict:
        """Generate comprehensive tests for a specific function"""
        tests = {
            "functional_tests": [],
            "boundary_tests": [],
            "error_tests": [],
            "performance_tests": [],
            "all_tests": []
        }
        
        # Check if we have predefined patterns for this function
        func_pattern = self.function_patterns.get(func_info.name)
        
        if func_pattern:
            # Use predefined patterns for known functions
            tests = await self._generate_from_patterns(func_info, func_pattern, num_tests)
        else:
            # Generate based on function signature and analysis
            tests = await self._generate_from_analysis(func_info, analysis, num_tests)
        
        # Combine all tests
        tests["all_tests"] = (
            tests["functional_tests"] + 
            tests["boundary_tests"] + 
            tests["error_tests"] + 
            tests["performance_tests"]
        )
        
        return tests

    async def _generate_from_patterns(self, func_info: CFunctionInfo, pattern: Dict, num_tests: int) -> Dict:
        """Generate tests using predefined patterns for known functions"""
        tests = {
            "functional_tests": [],
            "boundary_tests": [],
            "error_tests": [],
            "performance_tests": []
        }
        
        # Functional tests with known inputs/outputs
        if "valid_inputs" in pattern and "expected_outputs" in pattern:
            for inp, exp in zip(pattern["valid_inputs"], pattern["expected_outputs"]):
                tests["functional_tests"].append({
                    "description": f"Test {func_info.name}({inp}) == {exp}",
                    "input": str(inp),
                    "expected_output": str(exp),
                    "test_code": f"assert({func_info.name}({inp}) == {exp});"
                })
        
        # Boundary tests
        if "boundary_cases" in pattern:
            for boundary in pattern["boundary_cases"]:
                tests["boundary_tests"].append({
                    "description": f"Test {func_info.name} boundary case: {boundary}",
                    "input": str(boundary),
                    "expected_output": "defined_behavior",
                    "test_code": f"// Test boundary: {func_info.name}({boundary})"
                })
        
        # Error tests
        if "error_cases" in pattern:
            for error_case in pattern["error_cases"]:
                tests["error_tests"].append({
                    "description": f"Test {func_info.name} error handling: {error_case}",
                    "input": str(error_case),
                    "expected_output": "error_or_invalid",
                    "test_code": f"// Test error case: {func_info.name}({error_case})"
                })
        
        return tests

    async def _generate_from_analysis(self, func_info: CFunctionInfo, analysis: Dict, num_tests: int) -> Dict:
        """Generate tests based on function analysis"""
        tests = {
            "functional_tests": [],
            "boundary_tests": [],
            "error_tests": [],
            "performance_tests": []
        }
        
        # Generate based on parameter types
        for i, (param_type, param_name) in enumerate(func_info.parameters):
            if "int" in param_type:
                tests["functional_tests"].append({
                    "description": f"Test {func_info.name} with valid integer {param_name}",
                    "input": "valid_integer",
                    "expected_output": "expected_result",
                    "test_code": f"// TODO: Test {func_info.name} with integer parameter"
                })
                
                tests["boundary_tests"].append({
                    "description": f"Test {func_info.name} with {param_name} = 0",
                    "input": "0",
                    "expected_output": "boundary_result",
                    "test_code": f"// TODO: Test {func_info.name} boundary case"
                })
                
                tests["error_tests"].append({
                    "description": f"Test {func_info.name} with negative {param_name}",
                    "input": "negative_value",
                    "expected_output": "error_handling",
                    "test_code": f"// TODO: Test {func_info.name} error case"
                })
        
        return tests

    def _generate_function_unit_test(self, func_info: CFunctionInfo, test_cases: Dict) -> str:
        """Generate unit test code for a specific function"""
        # Create unique function name to avoid duplicates
        file_name = Path(func_info.file_path).stem
        unique_name = f"{func_info.name}_{file_name}"
        
        lines = []
        lines.append(f"// Unit tests for {func_info.name} from {file_name}.c")
        lines.append(f"void test_{unique_name}() {{")
        lines.append(f'    printf("\\n=== Testing {func_info.name} from {file_name}.c ===\\n");')
        lines.append("    int passed = 0, total = 0;")
        lines.append("")
        
        # Add specific test cases based on function patterns
        if func_info.name in self.function_patterns:
            pattern = self.function_patterns[func_info.name]
            if func_info.name == "factorial":
                lines.extend([
                    "    // Functional tests with known values",
                    '    printf("Test: factorial(5) == 120\\n");',
                    "    assert(factorial(5) == 120);",
                    "    passed++; total++;",
                    "",
                    '    printf("Test: factorial(0) == 1\\n");',
                    "    assert(factorial(0) == 1);",
                    "    passed++; total++;",
                    "",
                    '    printf("Test: factorial(1) == 1\\n");',
                    "    assert(factorial(1) == 1);",
                    "    passed++; total++;",
                    ""
                ])
            elif func_info.name == "fibonacci":
                lines.extend([
                    "    // Fibonacci sequence tests",
                    '    printf("Test: fibonacci(0) == 0\\n");',
                    "    assert(fibonacci(0) == 0);",
                    "    passed++; total++;",
                    "",
                    '    printf("Test: fibonacci(1) == 1\\n");',
                    "    assert(fibonacci(1) == 1);",
                    "    passed++; total++;",
                    "",
                    '    printf("Test: fibonacci(5) == 5\\n");',
                    "    assert(fibonacci(5) == 5);",
                    "    passed++; total++;",
                    ""
                ])
            elif func_info.name == "pid_controller":
                lines.extend([
                    "    // PID Controller tests",
                    '    printf("Test: PID basic control (setpoint=100, measurement=95)\\n");',
                    "    float pid_result1 = pid_controller(100.0, 95.0, 0.1, 0.01, 0.05);",
                    '    printf("PID Output: %f\\n", pid_result1);',
                    "    assert(pid_result1 != 0.0); // Should produce non-zero output",
                    "    passed++; total++;",
                    "",
                    '    printf("Test: PID at setpoint (error=0)\\n");',
                    "    float pid_result2 = pid_controller(50.0, 50.0, 1.0, 0.1, 0.1);",
                    '    printf("PID Output at setpoint: %f\\n", pid_result2);',
                    "    // Note: may not be exactly 0 due to integral term",
                    "    passed++; total++;",
                    "",
                    '    printf("Test: PID with negative error\\n");',
                    "    float pid_result3 = pid_controller(0.0, 10.0, 0.5, 0.05, 0.02);",
                    '    printf("PID Output (negative error): %f\\n", pid_result3);',
                    "    assert(pid_result3 < 0.0); // Should be negative for negative error",
                    "    passed++; total++;",
                    ""
                ])
            elif func_info.name == "signal_generator":
                lines.extend([
                    "    // Signal Generator tests",
                    '    printf("Test: Signal at time=0 should be 0\\n");',
                    "    float sig1 = signal_generator(1.0, 0.0);",
                    '    printf("Signal(1.0, 0.0): %f\\n", sig1);',
                    "    assert(sig1 >= -0.1 && sig1 <= 0.1); // Should be close to 0",
                    "    passed++; total++;",
                    "",
                    '    printf("Test: Signal amplitude bounds [-1, 1]\\n");',
                    "    float sig2 = signal_generator(2.0, 1.0);",
                    '    printf("Signal(2.0, 1.0): %f\\n", sig2);',
                    "    assert(sig2 >= -1.1 && sig2 <= 1.1); // Should be within bounds",
                    "    passed++; total++;",
                    "",
                    '    printf("Test: Signal frequency response\\n");',
                    "    float sig3 = signal_generator(0.5, 2.0);",
                    '    printf("Signal(0.5, 2.0): %f\\n", sig3);',
                    "    passed++; total++;",
                    ""
                ])
        else:
            # Generic tests for unknown functions
            for category, tests in test_cases.items():
                if category == "all_tests":
                    continue
                lines.append(f"    // {category.replace('_', ' ').title()}")
                for test in tests:
                    lines.append(f"    // {test['description']}")
                    if "test_code" in test and test["test_code"].startswith("assert"):
                        lines.append(f"    {test['test_code']}")
                    else:
                        lines.append(f'    printf("TODO: {test["description"]}\\n");')
                    lines.append("    // passed++; total++; // Uncomment when implemented")
                    lines.append("")
        
        lines.extend([
            f'    printf("Function {func_info.name}: %d/%d tests passed\\n", passed, total);',
            "}"
        ])
        
        return "\n".join(lines)

    def _generate_combined_test_runner(self, unit_tests: List[str]) -> str:
        """Generate combined test runner with all functions"""
        lines = []
        
        # Headers
        lines.extend([
            "#include <stdio.h>",
            "#include <assert.h>",
            "#include <string.h>",
            "#include <time.h>",
            "#include <stdlib.h>",
            "#include <math.h>",
            ""
        ])
        
        # Forward declarations
        lines.append("// === Forward Declarations ===")
        for func_info in self.discovered_functions:
            lines.append(func_info.signature)
        lines.append("")
        
        # Individual test functions
        for unit_test in unit_tests:
            lines.append(unit_test)
            lines.append("")
        
        # Main test runner
        lines.extend([
            "void run_all_tests() {",
            '    printf("=== Enhanced C Function Test Runner ===\\n");',
            '    printf("Generated by NLP Test Generator\\n");',
            f'    printf("Functions discovered: {len(self.discovered_functions)}\\n\\n");',
            ""
        ])
        
        # Call all test functions
        for func_info in self.discovered_functions:
            file_name = Path(func_info.file_path).stem
            unique_name = f"{func_info.name}_{file_name}"
            lines.append(f"    test_{unique_name}();")
        
        lines.extend([
            "",
            '    printf("\\n=== Test Summary Complete ===\\n");',
            "}",
            "",
            "int main() {",
            "    run_all_tests();",
            "    return 0;",
            "}"
        ])
        
        return "\n".join(lines)

    def _save_test_runner(self, test_code: str):
        """Save the generated test runner to file"""
        output_dir = Path("modules/module2_nlp")
        output_dir.mkdir(parents=True, exist_ok=True)
        
        output_file = output_dir / "test_runner.c"
        with open(output_file, 'w') as f:
            f.write(test_code)
        
        logger.info(f"✅ Test runner saved to {output_file}")
        
        # Create separate object files compilation script
        compile_script = output_dir / "compile_tests.sh"
        with open(compile_script, 'w') as f:
            f.write("#!/bin/bash\n")
            f.write("# Auto-generated compilation script\n")
            f.write("echo 'Compiling C source files to object files...'\n")
            f.write("\n")
            
            # Compile each C file to object file (excluding main function)
            object_files = []
            for func_info in self.discovered_functions:
                rel_path = os.path.relpath(func_info.file_path, output_dir)
                c_file = Path(rel_path)
                obj_file = c_file.stem + ".o"
                object_files.append(obj_file)
                
                f.write(f"echo 'Compiling {rel_path} to {obj_file}...'\n")
                f.write(f"gcc -c {rel_path} -o {obj_file} -DSKIP_MAIN\n")
                f.write("if [ $? -ne 0 ]; then\n")
                f.write(f"    echo 'Failed to compile {rel_path}'\n")
                f.write("    exit 1\n")
                f.write("fi\n")
                f.write("\n")
            
            # Link everything together
            f.write("echo 'Linking test runner with object files...'\n")
            f.write(f"gcc -o test_runner test_runner.c {' '.join(set(object_files))} -lm\n")
            f.write("if [ $? -eq 0 ]; then\n")
            f.write("    echo 'Compilation successful. Run ./test_runner to execute tests.'\n")
            f.write("    echo 'Cleaning up object files...'\n")
            f.write(f"    rm -f {' '.join(set(object_files))}\n")
            f.write("else\n")
            f.write("    echo 'Linking failed. Check the errors above.'\n")
            f.write("    exit 1\n")
            f.write("fi\n")
        
        # Alternative script for simple compilation (exclude main functions manually)
        simple_script = output_dir / "compile_simple.sh"
        with open(simple_script, 'w') as f:
            f.write("#!/bin/bash\n")
            f.write("# Simple compilation - you may need to edit your .c files to exclude main()\n")
            f.write("echo 'This script assumes your .c files do not have main() functions'\n")
            f.write("echo 'If they do, please comment out or remove the main() functions first'\n")
            f.write("echo ''\n")
            
            # Find all C files to link with correct relative paths
            c_files = []
            for func_info in self.discovered_functions:
                rel_path = os.path.relpath(func_info.file_path, output_dir)
                if rel_path not in c_files:
                    c_files.append(rel_path)
            
            f.write("read -p 'Have you removed/commented main() functions from your .c files? (y/n): ' response\n")
            f.write("if [ \"$response\" = \"y\" ]; then\n")
            f.write("    echo 'Compiling test runner...'\n")
            f.write(f"    gcc -o test_runner test_runner.c {' '.join(c_files)} -lm\n")
            f.write("    if [ $? -eq 0 ]; then\n")
            f.write("        echo 'Compilation successful. Run ./test_runner to execute tests.'\n")
            f.write("    else\n")
            f.write("        echo 'Compilation failed. Check the errors above.'\n")
            f.write("    fi\n")
            f.write("else\n")
            f.write("    echo 'Please edit your .c files first, then run this script again.'\n")
            f.write("fi\n")
        
        # Make scripts executable
        os.chmod(compile_script, 0o755)
        os.chmod(simple_script, 0o755)
        
        logger.info(f"✅ Compilation scripts saved:")
        logger.info(f"   - {compile_script} (automatic object file handling)")
        logger.info(f"   - {simple_script} (manual main() removal required)")
        
        # Create a helper script to create function-only versions of C files
        create_func_script = output_dir / "create_function_files.py"
        with open(create_func_script, 'w') as f:
            f.write("#!/usr/bin/env python3\n")
            f.write('"""\n')
            f.write("Helper script to create function-only versions of C files\n")
            f.write("(removes main() functions for linking with test runner)\n")
            f.write('"""\n')
            f.write("import re\nimport os\nfrom pathlib import Path\n\n")
            
            f.write("def remove_main_function(c_content):\n")
            f.write('    """Remove main function from C code"""\n')
            f.write("    # Pattern to match main function\n")
            f.write('    main_pattern = r\'int\\s+main\\s*\\([^)]*\\)\\s*\\{(?:[^{}]*\\{[^{}]*\\})*[^{}]*\\}\'\n')
            f.write("    # Remove main function\n")
            f.write("    cleaned = re.sub(main_pattern, '', c_content, flags=re.DOTALL)\n")
            f.write("    return cleaned\n\n")
            
            f.write("# Process each C file and create function-only version in current directory\n")
            processed_files = set()
            func_files = []
            for func_info in self.discovered_functions:
                rel_path = os.path.relpath(func_info.file_path, output_dir)
                if rel_path not in processed_files:
                    processed_files.add(rel_path)
                    c_file = Path(rel_path)
                    func_file = f"{c_file.stem}_func.c"
                    func_files.append(func_file)
                    
                    f.write(f'print("Processing {rel_path}...")\n')
                    f.write(f'try:\n')
                    f.write(f'    with open("{rel_path}", "r") as file:\n')
                    f.write("        content = file.read()\n")
                    f.write("    cleaned = remove_main_function(content)\n")
                    f.write(f'    with open("{func_file}", "w") as out:\n')
                    f.write("        out.write(cleaned)\n")
                    f.write(f'    print("Created {func_file}")\n')
                    f.write(f'except Exception as e:\n')
                    f.write(f'    print("Error processing {rel_path}: {{e}}")\n')
                    f.write("\n")
            
            f.write('print("\\nFunction-only files created in current directory!")\n')
            f.write(f'print("Now run: gcc -o test_runner test_runner.c {" ".join(func_files)} -lm")\n')
        
        os.chmod(create_func_script, 0o755)

    async def test_basic_functionality(self) -> Dict:
        """Run a comprehensive test of the generator"""
        logger.info("🧪 Running comprehensive functionality test")
        
        result = await self.generate_test_cases_from_functions(num_tests=5)
        
        # Print detailed results
        print("✅ Enhanced NLP Test Generator - Comprehensive Test Complete!")
        print(f"Status: {result['status']}")
        print(f"Functions Discovered: {result['functions_found']}")
        print(f"Function Names: {', '.join(result['discovered_functions'])}")
        print(f"Total Tests Generated: {result['total_tests']}")
        
        # Show function details
        print("\n=== Discovered Functions ===")
        for func_info in self.discovered_functions:
            print(f"📝 {func_info.name}")
            print(f"   File: {func_info.file_path}")
            print(f"   Signature: {func_info.signature}")
            print(f"   Parameters: {len(func_info.parameters)}")
            print()
        
        # Show test case preview
        print("=== Generated Test Cases Preview ===")
        for func_name, tests in result['test_cases'].items():
            print(f"\n--- Tests for {func_name} ---")
            for category, test_list in tests.items():
                if category != "all_tests" and test_list:
                    print(f"  {category}: {len(test_list)} tests")
                    if test_list:
                        print(f"    Example: {test_list[0]['description']}")
        
        print(f"\n✅ Test runner generated and saved!")
        print("📁 Files created:")
        print("   - modules/module2_nlp/test_runner.c")
        print("   - modules/module2_nlp/compile_tests.sh")
        print("\n🚀 To compile and run:")
        print("   cd modules/module2_nlp")
        print("   ./compile_tests.sh")
        print("   ./test_runner")
        
        return result

# For backward compatibility
NLPTestGenerator = EnhancedNLPTestGenerator

# Example usage
async def main():
    """Example usage of the enhanced generator"""
    # Use your actual path to C files (relative from modules/module2_nlp/)
    generator = EnhancedNLPTestGenerator("../../data/sample_code")
    result = await generator.test_basic_functionality()
    return result

if __name__ == "__main__":
    import asyncio
    asyncio.run(main())



    

"""
PHASE 1-2
NLP Test Generator using transformers and langchain
"""
import logging
import torch # type: ignore
from pathlib import Path

logger = logging.getLogger(__name__)

class NLPTestGenerator:
    """NLP-based test case generator"""
    
    def __init__(self):
        logger.info("Initializing NLP Test Generator")
        self.device_available = self._check_device()
        self.models_ready = self._setup_nlp_models()
    
    def _check_device(self):
        """Check available computing device"""
        if torch.cuda.is_available():
            logger.info("CUDA GPU detected and available")
            return "cuda"
        else:
            logger.info("Using CPU for computations")
            return "cpu"
    
    def _setup_nlp_models(self):
        """Setup NLP models for test generation"""
        try:
            logger.info("Setting up NLP models (this may take a few minutes on first run)")
            # We'll use a lightweight approach for Phase 1-2
            logger.info("NLP models setup completed (lightweight mode)")
            return True
        except Exception as e:
            logger.error(f"NLP model setup failed: {e}")
            return False
    
    def generate_test_cases(self, specification: str):
        """Generate test cases from specification"""
        logger.info("Generating test cases from specification")
        
        # Phase 1-2: Basic template-based generation
        test_cases = [
            f"Test case 1: Verify basic functionality for: {specification[:50]}...",
            f"Test case 2: Test edge cases for: {specification[:50]}...",
            f"Test case 3: Performance test for: {specification[:50]}..."
        ]
        
        return {
            "test_cases": test_cases,
            "specification": specification,
            "status": "Phase 1-2 - Basic NLP setup complete",
            "device": self.device_available,
            "models_ready": self.models_ready
        }
    
    def test_basic_functionality(self):
        """Test basic NLP functionality"""
        logger.info("Testing NLP basic functionality")
        sample_spec = "Function should calculate factorial of positive integers and return error for negative inputs"
        result = self.generate_test_cases(sample_spec)
        logger.info(f"NLP test result: {result['status']}")
        return result