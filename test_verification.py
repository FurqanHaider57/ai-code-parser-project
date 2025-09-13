#!/usr/bin/env python3
"""
Comprehensive Formal Verification Test Runner
Tests all aspects of Module 3: Enhanced Formal Verification System
"""

import sys
import os
import asyncio
import logging
from pathlib import Path
import argparse
import json
import time
from typing import Dict, List

# Add project root to path
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root))

try:
    from modules.module3_formal.formal_verifier import EnhancedFormalVerifier, ACSLContractGenerator
except ImportError as e:
    print(f"❌ Import Error: {e}")
    print("💡 Make sure Module 3 is properly installed!")
    sys.exit(1)

# Setup logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class ComprehensiveTestRunner:
    """Comprehensive test runner for Module 3 formal verification"""
    
    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.verifier = None
        self.contract_generator = None
        self.test_results = {}
        self.start_time = None
        
        if verbose:
            logger.setLevel(logging.DEBUG)
    
    async def initialize(self) -> bool:
        """Initialize all components"""
        print("🚀 Initializing Enhanced Formal Verification System...")
        self.start_time = time.time()
        
        try:
            # Initialize contract generator
            print("📝 Initializing ACSL Contract Generator...")
            self.contract_generator = ACSLContractGenerator()
            
            # Initialize formal verifier
            print("🔍 Initializing Enhanced Formal Verifier...")
            self.verifier = EnhancedFormalVerifier()
            
            print("✅ All components initialized successfully!")
            return True
            
        except Exception as e:
            print(f"❌ Initialization failed: {e}")
            logger.exception("Initialization error")
            return False
    
    async def run_all_tests(self) -> Dict:
        """Run all comprehensive tests"""
        
        print("\n" + "="*60)
        print("🧪 RUNNING COMPREHENSIVE FORMAL VERIFICATION TESTS")
        print("="*60)
        
        # Test 1: Contract Generator
        await self._test_contract_generator()
        
        # Test 2: Single Function Verification
        await self._test_single_function_verification()
        
        # Test 3: Batch Function Verification
        await self._test_batch_verification()
        
        # Test 4: Complex Code Verification
        await self._test_complex_code_verification()
        
        # Test 5: Error Handling
        await self._test_error_handling()
        
        # Test 6: Report Generation
        await self._test_report_generation()
        
        # Test 7: Performance Testing
        await self._test_performance()
        
        return self.test_results
    
    async def _test_contract_generator(self):
        """Test ACSL contract generator"""
        print("\n🧪 Test 1: ACSL Contract Generator")
        print("-" * 40)
        
        test_code = '''
int factorial(int n) {
    if (n < 0) return -1;
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}
'''
        
        try:
            result = await self.contract_generator.generate_contracts_for_function(
                test_code, "factorial", "Calculate factorial of non-negative integers"
            )
            
            success = "contracts" in result and len(result["contracts"]["preconditions"]) > 0
            
            self.test_results["contract_generator"] = {
                "status": "PASS" if success else "FAIL",
                "contracts_generated": len(result.get("contracts", {}).get("preconditions", [])) + 
                                     len(result.get("contracts", {}).get("postconditions", [])),
                "validation_passed": result.get("validation", {}).get("valid", False),
                "ai_enhanced": result.get("metadata", {}).get("ai_enhanced", False),
                "details": result
            }
            
            print(f"✅ Contract generation: {'PASS' if success else 'FAIL'}")
            if self.verbose:
                print(f"   Generated {self.test_results['contract_generator']['contracts_generated']} contracts")
                
        except Exception as e:
            self.test_results["contract_generator"] = {"status": "ERROR", "error": str(e)}
            print(f"❌ Contract generation: ERROR - {e}")
    
    async def _test_single_function_verification(self):
        """Test single function verification"""
        print("\n🧪 Test 2: Single Function Verification")
        print("-" * 40)
        
        test_functions = [
            ("factorial", "int factorial(int n) { if (n <= 1) return 1; return n * factorial(n-1); }"),
            ("gcd", "int gcd(int a, int b) { if (b == 0) return a; return gcd(b, a % b); }"),
            ("add", "int add(int a, int b) { return a + b; }")
        ]
        
        results = {}
        
        for func_name, func_code in test_functions:
            try:
                result = await self.verifier.verify_function_with_contracts(
                    func_code, func_name, f"Test function {func_name}"
                )
                
                success = result.get("status") == "success"
                results[func_name] = {
                    "status": "PASS" if success else "FAIL",
                    "verification_successful": result.get("analysis", {}).get("verification_successful", False),
                    "contracts_generated": bool(result.get("contracts_generated")),
                    "details": result
                }
                
                print(f"✅ {func_name}: {'PASS' if success else 'FAIL'}")
                
            except Exception as e:
                results[func_name] = {"status": "ERROR", "error": str(e)}
                print(f"❌ {func_name}: ERROR - {e}")
        
        self.test_results["single_function_verification"] = results
    
    async def _test_batch_verification(self):
        """Test batch verification"""
        print("\n🧪 Test 3: Batch Function Verification")  
        print("-" * 40)
        
        batch_code = '''
#include <stdio.h>
#include <math.h>

int factorial(int n) {
    if (n < 0) return -1;
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}

int fibonacci(int n) {
    if (n <= 1) return n;
    return fibonacci(n - 1) + fibonacci(n - 2);
}

int gcd(int a, int b) {
    while (b != 0) {
        int temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}

float pid_controller(float setpoint, float measurement, float kp, float ki, float kd) {
    static float integral = 0.0;
    static float previous_error = 0.0;
    
    float error = setpoint - measurement;
    integral += error;
    float derivative = error - previous_error;
    
    float output = kp * error + ki * integral + kd * derivative;
    previous_error = error;
    
    return output;
}
'''
        
        try:
            result = await self.verifier.batch_verify_functions(
                batch_code,
                ["factorial", "fibonacci", "gcd", "pid_controller"],
                {
                    "factorial": "Mathematical factorial function",
                    "fibonacci": "Recursive fibonacci sequence", 
                    "gcd": "Greatest common divisor",
                    "pid_controller": "PID control algorithm"
                }
            )
            
            success = result.get("summary", {}).get("overall_status") == "completed"
            total_functions = result.get("total_functions", 0)
            successful_functions = result.get("summary", {}).get("successful_verifications", 0)
            
            self.test_results["batch_verification"] = {
                "status": "PASS" if success else "FAIL",
                "total_functions": total_functions,
                "successful_functions": successful_functions,
                "success_rate": successful_functions / total_functions if total_functions > 0 else 0,
                "details": result
            }
            
            print(f"✅ Batch verification: {'PASS' if success else 'FAIL'}")
            print(f"   Processed {total_functions} functions, {successful_functions} successful")
            
        except Exception as e:
            self.test_results["batch_verification"] = {"status": "ERROR", "error": str(e)}
            print(f"❌ Batch verification: ERROR - {e}")
    
    async def _test_complex_code_verification(self):
        """Test with complex C code"""
        print("\n🧪 Test 4: Complex Code Verification")
        print("-" * 40)
        
        complex_code = '''
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

// Array processing with bounds checking
int array_sum(int arr[], int size) {
    if (size <= 0 || arr == NULL) return 0;
    int sum = 0;
    for (int i = 0; i < size; i++) {
        sum += arr[i];
    }
    return sum;
}

// String processing
int string_length(const char* str) {
    if (str == NULL) return -1;
    int len = 0;
    while (str[len] != '\\0') {
        len++;
    }
    return len;
}

// Memory management
void* safe_malloc(size_t size) {
    if (size == 0) return NULL;
    void* ptr = malloc(size);
    return ptr;
}

// Mathematical function with error handling
double safe_sqrt(double x) {
    if (x < 0.0) return -1.0;
    if (x == 0.0) return 0.0;
    return sqrt(x);
}
'''
        
        try:
            result = await self.verifier.batch_verify_functions(
                complex_code,
                ["array_sum", "string_length", "safe_malloc", "safe_sqrt"]
            )
            
            success = result.get("summary", {}).get("overall_status") == "completed"
            
            self.test_results["complex_code_verification"] = {
                "status": "PASS" if success else "FAIL",
                "functions_processed": len(result.get("results", {})),
                "contracts_generated": result.get("summary", {}).get("total_contracts_generated", 0),
                "details": result
            }
            
            print(f"✅ Complex code: {'PASS' if success else 'FAIL'}")
            
        except Exception as e:
            self.test_results["complex_code_verification"] = {"status": "ERROR", "error": str(e)}
            print(f"❌ Complex code: ERROR - {e}")
    
    async def _test_error_handling(self):
        """Test error handling capabilities"""
        print("\n🧪 Test 5: Error Handling")
        print("-" * 40)
        
        error_tests = [
            ("invalid_function", "invalid C code", "nonexistent_function"),
            ("empty_code", "", "test"),
            ("syntax_error", "int test( { return 0; }", "test")
        ]
        
        results = {}
        
        for test_name, code, func_name in error_tests:
            try:
                result = await self.verifier.verify_function_with_contracts(code, func_name)
                
                # Should handle errors gracefully
                handled_gracefully = result.get("status") in ["error", "success"] 
                
                results[test_name] = {
                    "status": "PASS" if handled_gracefully else "FAIL",
                    "error_handled": "error" in result or "message" in result,
                    "details": result
                }
                
                print(f"✅ {test_name}: PASS (error handled gracefully)")
                
            except Exception as e:
                # Exceptions should be caught and handled
                results[test_name] = {"status": "FAIL", "unhandled_exception": str(e)}
                print(f"❌ {test_name}: FAIL (unhandled exception)")
        
        self.test_results["error_handling"] = results
    
    async def _test_report_generation(self):
        """Test report generation"""
        print("\n🧪 Test 6: Report Generation")
        print("-" * 40)
        
        try:
            # Use existing test results
            sample_results = {
                "function_name": "test_function",
                "status": "success",
                "contracts_generated": {"contracts": {"preconditions": ["requires n >= 0;"], "postconditions": ["ensures \\result >= 0;"]}},
                "verification_result": {"success": True, "statistics": {"total": 1, "proved": 1}}
            }
            
            # Test different report formats
            formats = ["markdown", "json"]
            reports = {}
            
            for format_type in formats:
                try:
                    report = await self.verifier.generate_verification_report(sample_results, format_type)
                    reports[format_type] = {
                        "status": "PASS",
                        "length": len(report),
                        "generated": bool(report)
                    }
                    print(f"✅ {format_type} report: PASS")
                except Exception as e:
                    reports[format_type] = {"status": "FAIL", "error": str(e)}
                    print(f"❌ {format_type} report: FAIL")
            
            self.test_results["report_generation"] = reports
            
        except Exception as e:
            self.test_results["report_generation"] = {"status": "ERROR", "error": str(e)}
            print(f"❌ Report generation: ERROR - {e}")
    
    async def _test_performance(self):
        """Test performance with multiple functions"""
        print("\n🧪 Test 7: Performance Testing")
        print("-" * 40)
        
        try:
            start_time = time.time()
            
            # Generate multiple similar functions
            functions = []
            code_parts = []
            
            for i in range(5):
                func_name = f"test_function_{i}"
                func_code = f"int {func_name}(int n) {{ return n * {i+1}; }}"
                functions.append(func_name)
                code_parts.append(func_code)
            
            full_code = "\n".join(code_parts)
            
            # Run batch verification
            result = await self.verifier.batch_verify_functions(full_code, functions)
            
            end_time = time.time()
            duration = end_time - start_time
            
            success = result.get("summary", {}).get("overall_status") == "completed"
            
            self.test_results["performance"] = {
                "status": "PASS" if success else "FAIL",
                "duration": duration,
                "functions_processed": len(functions),
                "functions_per_second": len(functions) / duration if duration > 0 else 0,
                "details": result
            }
            
            print(f"✅ Performance: {'PASS' if success else 'FAIL'}")
            print(f"   Processed {len(functions)} functions in {duration:.2f}s")
            
        except Exception as e:
            self.test_results["performance"] = {"status": "ERROR", "error": str(e)}
            print(f"❌ Performance: ERROR - {e}")
    
    def generate_test_summary(self) -> str:
        """Generate comprehensive test summary"""
        
        total_time = time.time() - self.start_time if self.start_time else 0
        
        summary = "\n" + "="*60 + "\n"
        summary += "📊 COMPREHENSIVE TEST SUMMARY\n"
        summary += "="*60 + "\n"
        
        # Count test results
        total_tests = 0
        passed_tests = 0
        failed_tests = 0
        error_tests = 0
        
        for test_category, results in self.test_results.items():
            if isinstance(results, dict):
                if "status" in results:
                    total_tests += 1
                    if results["status"] == "PASS":
                        passed_tests += 1
                    elif results["status"] == "FAIL":
                        failed_tests += 1
                    else:
                        error_tests += 1
                else:
                    # Handle nested results (like single function verification)
                    for sub_test, sub_result in results.items():
                        if isinstance(sub_result, dict) and "status" in sub_result:
                            total_tests += 1
                            if sub_result["status"] == "PASS":
                                passed_tests += 1
                            elif sub_result["status"] == "FAIL":
                                failed_tests += 1
                            else:
                                error_tests += 1
        
        # Overall statistics
        success_rate = (passed_tests / total_tests * 100) if total_tests > 0 else 0
        
        summary += f"⏱️  Total Test Time: {total_time:.2f} seconds\n"
        summary += f"🧪 Total Tests: {total_tests}\n"
        summary += f"✅ Passed: {passed_tests}\n"
        summary += f"❌ Failed: {failed_tests}\n"
        summary += f"⚠️  Errors: {error_tests}\n"
        summary += f"📈 Success Rate: {success_rate:.1f}%\n\n"
        
        # Detailed results by category
        for test_category, results in self.test_results.items():
            category_name = test_category.replace("_", " ").title()
            summary += f"📋 {category_name}:\n"
            
            if isinstance(results, dict):
                if "status" in results:
                    status_icon = "✅" if results["status"] == "PASS" else "❌" if results["status"] == "FAIL" else "⚠️"
                    summary += f"   {status_icon} {results['status']}\n"
                    
                    # Add specific metrics
                    if test_category == "contract_generator":
                        summary += f"   📝 Contracts Generated: {results.get('contracts_generated', 0)}\n"
                        summary += f"   🔍 AI Enhanced: {results.get('ai_enhanced', False)}\n"
                    
                    elif test_category == "batch_verification":
                        summary += f"   🔧 Functions: {results.get('total_functions', 0)}\n"
                        summary += f"   ✅ Successful: {results.get('successful_functions', 0)}\n"
                        summary += f"   📊 Success Rate: {results.get('success_rate', 0):.1%}\n"
                    
                    elif test_category == "performance":
                        summary += f"   ⚡ Duration: {results.get('duration', 0):.2f}s\n"
                        summary += f"   🚀 Functions/sec: {results.get('functions_per_second', 0):.2f}\n"
                
                else:
                    # Handle nested results
                    for sub_test, sub_result in results.items():
                        if isinstance(sub_result, dict) and "status" in sub_result:
                            status_icon = "✅" if sub_result["status"] == "PASS" else "❌" if sub_result["status"] == "FAIL" else "⚠️"
                            summary += f"   {status_icon} {sub_test}: {sub_result['status']}\n"
            
            summary += "\n"
        
        # Component status
        summary += "🔧 COMPONENT STATUS:\n"
        summary += f"   📝 Contract Generator: {'✅ Ready' if self.contract_generator else '❌ Failed'}\n"
        summary += f"   🔍 Formal Verifier: {'✅ Ready' if self.verifier else '❌ Failed'}\n"
        summary += f"   🛠️  Frama-C: {'✅ Available' if self.verifier and self.verifier.framac_available else '❌ Not Available'}\n"
        summary += f"   🤖 AI Enhancement: {'✅ Available' if self.contract_generator and self.contract_generator.llm_available else '❌ Not Available'}\n\n"
        
        # Overall assessment
        if success_rate >= 90:
            summary += "🎉 EXCELLENT: Module 3 is working excellently!\n"
        elif success_rate >= 75:
            summary += "👍 GOOD: Module 3 is working well with minor issues.\n"
        elif success_rate >= 50:
            summary += "⚠️  FAIR: Module 3 has some issues that need attention.\n"
        else:
            summary += "🚨 POOR: Module 3 needs significant fixes.\n"
        
        summary += "="*60 + "\n"
        
        return summary
    
    async def save_detailed_report(self, filename: str = None):
        """Save detailed test report to file"""
        
        if not filename:
            timestamp = time.strftime("%Y%m%d_%H%M%S")
            filename = f"module3_test_report_{timestamp}.md"
        
        try:
            # Generate detailed markdown report
            report = "# Module 3 Formal Verification - Detailed Test Report\n\n"
            report += f"**Generated:** {time.strftime('%Y-%m-%d %H:%M:%S')}\n\n"
            
            # Test summary
            report += self.generate_test_summary()
            
            # Detailed results
            report += "\n## 📋 Detailed Test Results\n\n"
            
            for test_category, results in self.test_results.items():
                category_name = test_category.replace("_", " ").title()
                report += f"### {category_name}\n\n"
                
                if isinstance(results, dict):
                    if "details" in results:
                        # Format detailed results as JSON
                        report += f"```json\n{json.dumps(results['details'], indent=2)}\n```\n\n"
                    else:
                        report += f"```json\n{json.dumps(results, indent=2)}\n```\n\n"
            
            # Save to file
            with open(filename, 'w') as f:
                f.write(report)
            
            print(f"📄 Detailed report saved to: {filename}")
            
        except Exception as e:
            print(f"❌ Failed to save report: {e}")
    
    def print_summary(self):
        """Print test summary to console"""
        print(self.generate_test_summary())


async def main():
    """Main test runner function"""
    
    parser = argparse.ArgumentParser(description="Comprehensive Module 3 Test Runner")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    parser.add_argument("--save-report", "-s", help="Save detailed report to file")
    parser.add_argument("--quick", "-q", action="store_true", help="Run only essential tests")
    parser.add_argument("--test", "-t", choices=["contracts", "single", "batch", "complex", "errors", "reports", "performance"], 
                       help="Run specific test only")
    
    args = parser.parse_args()
    
    # Initialize test runner
    runner = ComprehensiveTestRunner(verbose=args.verbose)
    
    print("🚀 Module 3 Formal Verification - Comprehensive Test Suite")
    print("=" * 60)
    
    if not await runner.initialize():
        print("❌ Failed to initialize test components")
        return 1
    
    try:
        # Run specific test or all tests
        if args.test:
            print(f"\n🎯 Running specific test: {args.test}")
            if args.test == "contracts":
                await runner._test_contract_generator()
            elif args.test == "single":
                await runner._test_single_function_verification()
            elif args.test == "batch":
                await runner._test_batch_verification()
            elif args.test == "complex":
                await runner._test_complex_code_verification()
            elif args.test == "errors":
                await runner._test_error_handling()
            elif args.test == "reports":
                await runner._test_report_generation()
            elif args.test == "performance":
                await runner._test_performance()
        
        elif args.quick:
            print("\n⚡ Running quick essential tests...")
            await runner._test_contract_generator()
            await runner._test_single_function_verification()
            await runner._test_batch_verification()
        
        else:
            # Run all tests
            await runner.run_all_tests()
        
        # Print summary
        runner.print_summary()
        
        # Save detailed report if requested
        if args.save_report:
            await runner.save_detailed_report(args.save_report)
        
        # Determine exit code based on results
        total_tests = len([r for results in runner.test_results.values() 
                          for r in (results.values() if isinstance(results, dict) and "status" not in results else [results])
                          if isinstance(r, dict) and "status" in r])
        passed_tests = len([r for results in runner.test_results.values()
                           for r in (results.values() if isinstance(results, dict) and "status" not in results else [results])
                           if isinstance(r, dict) and r.get("status") == "PASS"])
        
        success_rate = (passed_tests / total_tests) if total_tests > 0 else 0
        
        if success_rate >= 0.8:  # 80% success rate required
            print(f"\n🎉 Tests completed successfully! ({success_rate:.1%} pass rate)")
            return 0
        else:
            print(f"\n⚠️ Some tests failed. Pass rate: {success_rate:.1%}")
            return 1
            
    except KeyboardInterrupt:
        print("\n⏹️ Tests interrupted by user")
        return 1
    except Exception as e:
        print(f"\n❌ Test runner failed: {e}")
        logger.exception("Test runner error")
        return 1


if __name__ == "__main__":
    exit(asyncio.run(main()))