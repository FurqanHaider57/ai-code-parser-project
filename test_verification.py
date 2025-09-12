#!/usr/bin/env python3
"""
Formal Verification Test Runner
Test the formal verification system with your C code files
"""

import sys
import os
import asyncio
import logging
from pathlib import Path
import argparse
import json

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent))

try:
    from modules.module3_formal.formal_verifier import EnhancedFormalVerifier
    from modules.module3_formal.contract_generation.acsl_generator import ACSLContractGenerator
except ImportError as e:
    print(f"❌ Import Error: {e}")
    print("💡 Make sure you've run the project checker first!")
    print("   python project_checker.py --fix")
    sys.exit(1)

# Setup logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class VerificationTestRunner:
    """Test runner for formal verification system"""
    
    def __init__(self):
        self.verifier = None
        self.test_results = {}
    
    async def initialize(self):
        """Initialize the verification system"""
        try:
            print("🚀 Initializing Enhanced Formal Verifier...")
            self.verifier = EnhancedFormalVerifier()
            print("✅ Formal Verifier initialized successfully!")
            return True
        except Exception as e:
            print(f"❌ Failed to initialize verifier: {e}")
            return False
    
    async def test_with_sample_code(self):
        """Test with built-in sample code"""
        print("\n🧪 Testing with sample C code...")
        
        sample_code = '''
#include <stdio.h>
#include <stdlib.h>

// Mathematical functions
int factorial(int n) {
    if (n < 0) return -1;
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}

int gcd(int a, int b) {
    if (b == 0) return a;
    return gcd(b, a % b);
}

int fibonacci(int n) {
    if (n <= 1) return n;
    return fibonacci(n - 1) + fibonacci(n - 2);
}

// Array processing
int array_sum(int arr[], int size) {
    if (size <= 0) return 0;
    int sum = 0;
    for (int i = 0; i < size; i++) {
        sum += arr[i];
    }
    return sum;
}

// Memory management
void* safe_malloc(size_t size) {
    if (size == 0) return NULL;
    void* ptr = malloc(size);
    return ptr;
}

int main() {
    printf("Testing formal verification...\\n");
    return 0;
}
'''
        
        # Test single function
        print("🔍 Testing single function verification...")
        try:
            result = await self.verifier.verify_function_with_contracts(
                sample_code, 
                "factorial",
                "Calculate factorial of non-negative integers up to 20"
            )
            print(f"Single function test: {result.get('status', 'unknown')}")
            self.test_results["single_function"] = result
        except Exception as e:
            print(f"❌ Single function test failed: {e}")
            self.test_results["single_function"] = {"status": "error", "error": str(e)}
        
        # Test batch verification
        print("\n🔄 Testing batch verification...")
        try:
            batch_result = await self.verifier.batch_verify_functions(
                sample_code,
                ["factorial", "gcd", "fibonacci", "array_sum"],
                {
                    "factorial": "Calculate factorial of non-negative integers",
                    "gcd": "Calculate greatest common divisor using Euclidean algorithm",
                    "fibonacci": "Calculate fibonacci number recursively",
                    "array_sum": "Calculate sum of array elements"
                }
            )
            print(f"Batch verification: {batch_result.get('summary', {}).get('overall_status', 'unknown')}")
            self.test_results["batch_verification"] = batch_result
        except Exception as e:
            print(f"❌ Batch verification test failed: {e}")
            self.test_results["batch_verification"] = {"status": "error", "error": str(e)}
    
    async def test_with_file(self, file_path: str, functions: list = None):
        """Test with a specific C file"""
        print(f"\n📂 Testing with file: {file_path}")
        
        try:
            with open(file_path, 'r') as f:
                c_code = f.read()
            
            if not functions:
                # Try to auto-detect functions
                functions = self.extract_function_names(c_code)
                print(f"🔍 Auto-detected functions: {functions}")
            
            if not functions:
                print("⚠️  No functions specified and none auto-detected")
                return
            
            # Run verification
            result = await self.verifier.batch_verify_functions(c_code, functions)
            
            print(f"File verification completed: {result.get('summary', {}).get('overall_status', 'unknown')}")
            self.test_results[f"file_{Path(file_path).stem}"] = result
            
        except FileNotFoundError:
            print(f"❌ File not found: {file_path}")
        except Exception as e:
            print(f"❌ File verification failed: {e}")
            self.test_results[f"file_{Path(file_path).stem}"] = {"status": "error", "error": str(e)}
    
    def extract_function_names(self, c_code: str) -> list:
        """Simple function name extraction"""
        import re
        
        # Look for function definitions
        pattern = r'^\s*(?:static\s+)?(?:inline\s+)?(\w+(?:\s*\*)?)\s+(\w+)\s*\([^)]*\)\s*\{'
        matches = re.findall(pattern, c_code, re.MULTILINE)
        
        function_names = []
        for return_type, func_name in matches:
            # Skip main function and common keywords
            if func_name not in ['main', 'if', 'while', 'for', 'switch'] and not return_type in ['if', 'while', 'for']:
                function_names.append(func_name)
        
        return function_names
    
    async def generate_test_report(self, output_file: str = None):
        """Generate comprehensive test report"""
        print("\n📊 Generating test report...")
        
        if not self.test_results:
            print("⚠️  No test results to report")
            return
        
        # Generate report
        try:
            report = await self.verifier.generate_verification_report(
                {"results": self.test_results, "test_run": True}, 
                "markdown"
            )
            
            if output_file:
                with open(output_file, 'w') as f:
                    f.write(report)
                print(f"📄 Report saved to: {output_file}")
            else:
                print("📋 Test Report:")
                print("-" * 50)
                print(report[:1000] + "..." if len(report) > 1000 else report)
        
        except Exception as e:
            print(f"❌ Report generation failed: {e}")
    
    def print_summary(self):
        """Print test summary"""
        print("\n" + "=" * 60)
        print("📊 TEST SUMMARY")
        print("=" * 60)
        
        total_tests = len(self.test_results)
        successful_tests = sum(1 for r in self.test_results.values() 
                             if r.get("status") == "success" or r.get("summary", {}).get("overall_status") == "completed")
        
        print(f"Total Tests: {total_tests}")
        print(f"Successful: {successful_tests}")
        print(f"Failed: {total_tests - successful_tests}")
        
        # Detailed results
        for test_name, result in self.test_results.items():
            status = result.get("status", "unknown")
            if "summary" in result:
                status = result["summary"].get("overall_status", status)
            
            status_icon = "✅" if status in ["success", "completed"] else "❌"
            print(f"{status_icon} {test_name}: {status}")
        
        if successful_tests == total_tests:
            print("\n🎉 All tests passed! Formal verification system is working correctly!")
        else:
            print(f"\n⚠️  {total_tests - successful_tests} test(s) failed. Check the details above.")

async def main():
    """Main test runner"""
    parser = argparse.ArgumentParser(description="Test Formal Verification System")
    parser.add_argument("--file", "-f", help="C file to test")
    parser.add_argument("--functions", "-fn", nargs="+", help="Specific functions to verify")
    parser.add_argument("--output", "-o", help="Output report file")
    parser.add_argument("--sample-only", action="store_true", help="Only run sample code tests")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    # Initialize test runner
    runner = VerificationTestRunner()
    
    if not await runner.initialize():
        print("❌ Failed to initialize verification system")
        return 1
    
    # Run tests
    try:
        # Always run sample tests
        await runner.test_with_sample_code()
        
        # Test specific file if provided
        if args.file and not args.sample_only:
            await runner.test_with_file(args.file, args.functions)
        
        # Generate report
        report_file = args.output or f"verification_test_report_{Path().cwd().name}.md"
        await runner.generate_test_report(report_file)
        
        # Print summary
        runner.print_summary()
        
        return 0
        
    except KeyboardInterrupt:
        print("\n⏹️  Test interrupted by user")
        return 1
    except Exception as e:
        print(f"❌ Test runner failed: {e}")
        return 1

if __name__ == "__main__":
    exit(asyncio.run(main()))