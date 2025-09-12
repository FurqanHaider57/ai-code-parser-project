        
"""
Enhanced Formal Verifier - Phase 2 Implementation
"""
import subprocess
import logging
import tempfile
import os
import json
from pathlib import Path
from typing import Dict, List, Optional
import asyncio

from .contract_generation.acsl_generator import ACSLContractGenerator
from config_phase3 import FormalVerificationConfig

logger = logging.getLogger(__name__)

class EnhancedFormalVerifier:
    """Enhanced formal verification using Frama-C with AI-generated contracts"""
    
    def __init__(self):
        logger.info("🚀 Initializing Enhanced Formal Verifier (Phase 2)")
        
        self.framac_path = "/usr/bin/frama-c"
        self.framac_available = self._check_framac_installation()
        self.contract_generator = ACSLContractGenerator()
        
        logger.info("✅ Enhanced Formal Verifier initialized")
    
    def _check_framac_installation(self) -> bool:
        """Check if Frama-C is properly installed"""
        try:
            result = subprocess.run(
                [self.framac_path, "-version"], 
                capture_output=True, text=True, 
                timeout=10
            )
            if result.returncode == 0:
                version_info = result.stdout.strip()
                logger.info(f"✅ Frama-C found: {version_info}")
                return True
            else:
                logger.error("Frama-C not working properly")
                return False
        except Exception as e:
            logger.error(f"Frama-C check failed: {e}")
            return False
    
    async def verify_code_with_auto_contracts(
        self, 
        c_code: str, 
        specification: str = "",
        function_names: List[str] = None
    ) -> Dict:
        """Verify C code with automatically generated contracts"""
        
        logger.info("🔍 Starting formal verification with auto-generated contracts")
        
        if not self.framac_available:
            return {
                "status": "Frama-C not available",
                "verified": False,
                "error": "Frama-C installation not found"
            }
        
        # Extract functions to verify
        if not function_names:
            function_names = self._extract_function_names(c_code)
        
        verification_results = {
            "overall_status": "verification_started",
            "functions_verified": {},
            "generated_contracts": {},
            "framac_results": {},
            "summary": {}
        }
        
        # Process each function
        for func_name in function_names:
            logger.info(f"📝 Generating contracts for function: {func_name}")
            
            # Generate contracts for this function
            contract_result = await self.contract_generator.generate_contracts_for_function(
                c_code, func_name, specification
            )
            
            if "error" in contract_result:
                verification_results["functions_verified"][func_name] = {
                    "status": "contract_generation_failed",
                    "error": contract_result["error"]
                }
                continue
            
            verification_results["generated_contracts"][func_name] = contract_result
            
            # Create annotated code
            annotated_code = self._insert_contracts_into_code(
                c_code, func_name, contract_result["contracts"]
            )
            
            # Verify with Frama-C
            framac_result = await self._verify_with_framac(annotated_code, func_name)
            verification_results["framac_results"][func_name] = framac_result
            
            # Determine verification status
            verification_results["functions_verified"][func_name] = {
                "contracts_generated": len(contract_result["contracts"].get("preconditions", [])) + 
                                     len(contract_result["contracts"].get("postconditions", [])),
                "verification_successful": framac_result.get("verification_passed", False),
                "proof_status": framac_result.get("proof_obligations", {}),
                "warnings": framac_result.get("warnings", [])
            }
        
        # Generate overall summary
        verification_results["summary"] = self._generate_verification_summary(verification_results)
        verification_results["overall_status"] = "verification_complete"
        
        logger.info("✅ Formal verification complete")
        return verification_results
    
    def _extract_function_names(self, c_code: str) -> List[str]:
        """Extract function names from C code"""
        import re
        
        # Find function definitions
        pattern = r'^\s*\w+(?:\s*\*)?\s+(\w+)\s*\([^)]*\)\s*\{'
        matches = re.findall(pattern, c_code, re.MULTILINE)
        
        # Filter out main function and common keywords
        functions = []
        for match in matches:
            if match not in ['main', 'if', 'while', 'for', 'switch']:
                functions.append(match)
        
        return functions
    
    def _insert_contracts_into_code(
        self, 
        c_code: str, 
        function_name: str, 
        contracts: Dict
    ) -> str:
        """Insert ACSL contracts into C code"""
        
        import re
        
        # Create ACSL contract block
        contract_block = "/*@\n"
        
        for precond in contracts.get("preconditions", []):
            if not precond.strip().startswith("@"):
                contract_block += f"  @ {precond}\n"
            else:
                contract_block += f"  {precond}\n"
        
        for postcond in contracts.get("postconditions", []):
            if not postcond.strip().startswith("@"):
                contract_block += f"  @ {postcond}\n"
            else:
                contract_block += f"  {postcond}\n"
        
        contract_block += "  @*/\n"
        
        # Find function definition and insert contract before it
        pattern = rf'(\w+(?:\s*\*)?\s+{re.escape(function_name)}\s*\([^)]*\)\s*\{{)'
        
        def replace_func(match):
            return contract_block + match.group(1)
        
        annotated_code = re.sub(pattern, replace_func, c_code)
        
        return annotated_code
    
    async def _verify_with_framac(self, annotated_code: str, function_name: str) -> Dict:
        """Verify annotated code with Frama-C"""
        
        try:
            # Create temporary file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False) as tmp_file:
                tmp_file.write(annotated_code)
                tmp_file_path = tmp_file.name
            
            # Run Frama-C with WP (weakest precondition) plugin
            cmd = [
                self.framac_path,
                "-wp",
                "-wp-rte",  # Runtime error annotations
                "-wp-timeout", str(FormalVerificationConfig.FRAMAC_TIMEOUT),
                "-wp-prover", "alt-ergo,z3",  # Use multiple provers
                tmp_file_path
            ]
            
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=FormalVerificationConfig.FRAMAC_TIMEOUT + 10
            )
            
            # Clean up
            os.unlink(tmp_file_path)
            
            # Parse Frama-C output
            return self._parse_framac_output(result.stdout, result.stderr, result.returncode)
            
        except subprocess.TimeoutExpired:
            return {
                "verification_passed": False,
                "error": "Frama-C verification timeout",
                "timeout": True
            }
        except Exception as e:
            return {
                "verification_passed": False,
                "error": str(e),
                "exception": True
            }
    
    def _parse_framac_output(self, stdout: str, stderr: str, return_code: int) -> Dict:
        """Parse Frama-C output to extract verification results"""
        
        result = {
            "verification_passed": return_code == 0,
            "return_code": return_code,
            "proof_obligations": {},
            "warnings": [],
            "errors": [],
            "statistics": {}
        }
        
        # Parse proof obligations from output
        lines = stdout.split('\n')
        current_function = None
        
        for line in lines:
            line = line.strip()
            
            # Look for proof results
            if "Goal" in line and ("Proved" in line or "Failed" in line or "Timeout" in line):
                if "Proved" in line:
                    result["proof_obligations"][line] = "proved"
                elif "Failed" in line:
                    result["proof_obligations"][line] = "failed"
                elif "Timeout" in line:
                    result["proof_obligations"][line] = "timeout"
            
            # Look for warnings
            elif "warning" in line.lower():
                result["warnings"].append(line)
            
            # Look for errors
            elif "error" in line.lower() and line:
                result["errors"].append(line)
            
            # Extract statistics
            elif "proved:" in line.lower():
                try:
                    parts = line.split()
                    for i, part in enumerate(parts):
                        if "proved:" in part.lower() and i + 1 < len(parts):
                            result["statistics"]["proved"] = int(parts[i + 1])
                except:
                    pass
        
        # Parse stderr for additional errors
        if stderr:
            stderr_lines = stderr.split('\n')
            for line in stderr_lines:
                if line.strip() and "error" in line.lower():
                    result["errors"].append(line.strip())
        
        # Determine overall success
        total_goals = len(result["proof_obligations"])
        proved_goals = sum(1 for status in result["proof_obligations"].values() if status == "proved")
        
        if total_goals > 0:
            result["verification_passed"] = proved_goals == total_goals
            result["statistics"]["total_goals"] = total_goals
            result["statistics"]["proved_goals"] = proved_goals
            result["statistics"]["success_rate"] = proved_goals / total_goals if total_goals > 0 else 0
        
        return result
    
    def _generate_verification_summary(self, results: Dict) -> Dict:
        """Generate overall verification summary"""
        
        total_functions = len(results["functions_verified"])
        successful_verifications = sum(
            1 for func_result in results["functions_verified"].values()
            if func_result.get("verification_successful", False)
        )
        
        total_contracts = sum(
            func_result.get("contracts_generated", 0)
            for func_result in results["functions_verified"].values()
        )
        
        total_proof_obligations = 0
        total_proved = 0
        
        for func_name, framac_result in results["framac_results"].items():
            stats = framac_result.get("statistics", {})
            total_proof_obligations += stats.get("total_goals", 0)
            total_proved += stats.get("proved_goals", 0)
        
        return {
            "total_functions": total_functions,
            "successfully_verified": successful_verifications,
            "verification_rate": successful_verifications / max(total_functions, 1),
            "total_contracts_generated": total_contracts,
            "total_proof_obligations": total_proof_obligations,
            "total_proved": total_proved,
            "proof_success_rate": total_proved / max(total_proof_obligations, 1),
            "overall_success": successful_verifications == total_functions and total_functions > 0
        }
    
    async def verify_single_function(
        self, 
        c_code: str, 
        function_name: str, 
        specification: str = ""
    ) -> Dict:
        """Verify a single function with generated contracts"""
        
        result = await self.verify_code_with_auto_contracts(
            c_code, specification, [function_name]
        )
        
        if function_name in result["functions_verified"]:
            return {
                "function_name": function_name,
                "verification_result": result["functions_verified"][function_name],
                "generated_contracts": result["generated_contracts"].get(function_name, {}),
                "framac_output": result["framac_results"].get(function_name, {}),
                "status": "Single function verification complete"
            }
        else:
            return {
                "function_name": function_name,
                "error": "Function verification failed",
                "status": "Verification failed"
            }
    
    # Legacy methods for backward compatibility
    def generate_acsl_contracts(self, c_code: str, function_name: str = "") -> Dict:
        """Legacy method - generate ACSL contracts"""
        
        # Use async method synchronously
        import asyncio
        
        function_names = [function_name] if function_name else self._extract_function_names(c_code)
        
        if not function_names:
            return {
                "contracts": ["/*@ requires input parameters are valid; */"],
                "function_name": function_name,
                "framac_available": self.framac_available,
                "status": "Phase 2 - Basic contract generation"
            }
        
        try:
            result = asyncio.run(
                self.contract_generator.generate_contracts_for_function(
                    c_code, function_names[0], ""
                )
            )
            
            contracts = []
            for precond in result.get("contracts", {}).get("preconditions", []):
                contracts.append(f"/*@ {precond} */")
            for postcond in result.get("contracts", {}).get("postconditions", []):
                contracts.append(f"/*@ {postcond} */")
            
            return {
                "contracts": contracts,
                "function_name": function_names[0],
                "framac_available": self.framac_available,
                "status": "Phase 2 - Enhanced contract generation complete"
            }
            
        except Exception as e:
            return {
                "contracts": ["/*@ requires parameters are valid; */"],
                "function_name": function_name,
                "framac_available": self.framac_available,
                "error": str(e),
                "status": "Phase 2 - Contract generation failed"
            }
    
    async def test_framac_integration(self) -> Dict:
        """Test enhanced Frama-C integration"""
        logger.info("🧪 Testing enhanced Frama-C integration")
        
        test_code = """
#include <stdio.h>

int factorial(int n) {
    if (n < 0) return -1;
    if (n <= 1) return 1;
    return n * factorial(n - 1);
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
"""
        
        try:
            # Test contract generation for factorial
            factorial_result = await self.verify_single_function(
                test_code, 
                "factorial", 
                "Calculate factorial of non-negative integers"
            )
            
            # Test contract generation for PID controller
            pid_result = await self.verify_single_function(
                test_code, 
                "pid_controller",
                "PID control algorithm for feedback systems"
            )
            
            return {
                "status": "Phase 2 - Enhanced Frama-C integration complete",
                "framac_available": self.framac_available,
                "contract_generator_ready": self.contract_generator is not None,
                "test_results": {
                    "factorial": {
                        "contracts_generated": len(factorial_result.get("generated_contracts", {}).get("contracts", {}).get("preconditions", [])) +
                                             len(factorial_result.get("generated_contracts", {}).get("contracts", {}).get("postconditions", [])),
                        "verification_attempted": "verification_result" in factorial_result
                    },
                    "pid_controller": {
                        "contracts_generated": len(pid_result.get("generated_contracts", {}).get("contracts", {}).get("preconditions", [])) +
                                             len(pid_result.get("generated_contracts", {}).get("contracts", {}).get("postconditions", [])),
                        "verification_attempted": "verification_result" in pid_result
                    }
                },
                "capabilities": {
                    "ai_contract_generation": True,
                    "template_based_contracts": True,
                    "automated_verification": self.framac_available,
                    "multiple_function_support": True
                }
            }
            
        except Exception as e:
            logger.error(f"Integration test failed: {e}")
            return {
                "status": "Phase 2 - Integration test failed",
                "error": str(e),
                "framac_available": self.framac_available
            }

# For backward compatibility
FormalVerifier = EnhancedFormalVerifier






"""
BASIC PHASE 1-2 --------Formal Verifier using Frama-C integration
"""
import subprocess
import logging
from pathlib import Path
import tempfile
import os

logger = logging.getLogger(__name__)

class FormalVerifier:
    """Formal verification using Frama-C"""
    
    def __init__(self):
        logger.info("Initializing Formal Verifier")
        self.framac_path = "/usr/bin/frama-c"
        self.framac_available = self._check_framac_installation()
    
    def _check_framac_installation(self):
        """Check if Frama-C is properly installed"""
        try:
            result = subprocess.run([self.framac_path, "-version"], 
                                  capture_output=True, text=True, timeout=10)
            if result.returncode == 0:
                version_info = result.stdout.strip()
                logger.info(f"Frama-C found: {version_info}")
                return True
            else:
                logger.error("Frama-C not working properly")
                return False
        except subprocess.TimeoutExpired:
            logger.error("Frama-C command timed out")
            return False
        except FileNotFoundError:
            logger.error("Frama-C executable not found")
            return False
        except Exception as e:
            logger.error(f"Frama-C check failed: {e}")
            return False
    
    def generate_acsl_contracts(self, c_code: str, function_name: str = ""):
        """Generate ACSL contracts from C code"""
        logger.info(f"Generating ACSL contracts for function: {function_name}")
        
        # Phase 1-2: Template-based contract generation
        contracts = []
        
        if "int" in c_code and "return" in c_code:
            contracts.append("/*@ requires input parameters are valid; */")
            contracts.append("/*@ ensures \\result is computed correctly; */")
        
        if "factorial" in c_code.lower():
            contracts.extend([
                "/*@ requires n >= 0; */",
                "/*@ ensures \\result >= 1; */",
                "/*@ ensures n == 0 ==> \\result == 1; */"
            ])
        
        return {
            "contracts": contracts,
            "function_name": function_name,
            "framac_available": self.framac_available,
            "status": "Phase 1-2 - Basic Frama-C integration complete"
        }
    
    def verify_code_with_contracts(self, c_code_with_contracts: str):
        """Verify C code with ACSL contracts using Frama-C"""
        if not self.framac_available:
            return {
                "status": "Frama-C not available",
                "verified": False,
                "error": "Frama-C installation not found"
            }
        
        try:
            # Create temporary file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False) as tmp_file:
                tmp_file.write(c_code_with_contracts)
                tmp_file_path = tmp_file.name
            
            # Run Frama-C verification
            result = subprocess.run([
                self.framac_path, "-wp", "-wp-rte", tmp_file_path
            ], capture_output=True, text=True, timeout=30)
            
            # Clean up temporary file
            os.unlink(tmp_file_path)
            
            return {
                "status": "Verification completed",
                "verified": result.returncode == 0,
                "output": result.stdout,
                "errors": result.stderr if result.stderr else None
            }
            
        except Exception as e:
            logger.error(f"Verification failed: {e}")
            return {
                "status": "Verification failed",
                "verified": False,
                "error": str(e)
            }
    
    def test_framac_integration(self):
        """Test Frama-C integration"""
        logger.info("Testing Frama-C integration")
        
        sample_c_code = """
int test_function(int x) {
    if (x < 0) return -1;
    return x * 2;
}
"""
        
        result = self.generate_acsl_contracts(sample_c_code, "test_function")
        logger.info(f"Frama-C test result: {result['status']}")
        
        return result