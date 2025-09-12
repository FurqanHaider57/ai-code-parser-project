
"""
Enhanced AI Debugger - Phase 3 Implementation
"""
import sys
import logging
import asyncio
from pathlib import Path
from typing import Dict, List, Optional, Any
import subprocess
import tempfile
import os

# Import Phase 3 components
from .llm_integration.llm_client import LLMClient, DebugContextExtractor # type: ignore

logger = logging.getLogger(__name__)

class EnhancedAIDebugger:
    """Enhanced AI Debugging interface with real LLM integration"""
    
    def __init__(self):
        logger.info("🚀 Initializing Enhanced AI Debugger (Phase 3)")
        
        # Initialize components
        self.llm_client = LLMClient()
        self.context_extractor = DebugContextExtractor()
        
        # Check external tool availability
        self.chatdbg_available = self._check_chatdbg()
        self.llmdebugger_available = self._check_llmdebugger()
        self.gdb_available = self._check_gdb()
        
        logger.info("✅ Enhanced AI Debugger initialized")
    
    def _check_chatdbg(self) -> bool:
        """Check ChatDBG availability"""
        try:
            chatdbg_path = Path(__file__).parent.parent.parent / "tools" / "ChatDBG"
            return chatdbg_path.exists()
        except Exception:
            return False
    
    def _check_llmdebugger(self) -> bool:
        """Check LLMDebugger availability"""
        try:
            llmdebugger_path = Path(__file__).parent.parent.parent / "tools" / "LLMDebugger"
            return llmdebugger_path.exists()
        except Exception:
            return False
    
    def _check_gdb(self) -> bool:
        """Check GDB availability"""
        try:
            result = subprocess.run(['gdb', '--version'], capture_output=True, timeout=5)
            return result.returncode == 0
        except Exception:
            return False
    
    async def debug_code_file(self, file_path: str, compilation_flags: List[str] = None) -> Dict:
        """Debug a C/C++ file with AI assistance"""
        logger.info(f"🐛 Starting AI debugging for: {file_path}")
        
        if not Path(file_path).exists():
            return {"error": f"File not found: {file_path}"}
        
        # Read source code
        with open(file_path, 'r') as f:
            source_code = f.read()
        
        # Step 1: Static analysis
        static_analysis = await self._perform_static_analysis(source_code, file_path)
        
        # Step 2: Compilation analysis
        compile_analysis = await self._analyze_compilation(file_path, compilation_flags or [])
        
        # Step 3: Runtime analysis (if compilation successful)
        runtime_analysis = {}
        if compile_analysis.get("compilation_successful"):
            runtime_analysis = await self._perform_runtime_analysis(
                compile_analysis["executable_path"], source_code
            )
        
        # Step 4: AI-powered analysis
        ai_analysis = await self._perform_ai_analysis(
            source_code, static_analysis, compile_analysis, runtime_analysis, file_path
        )
        
        # Combine all analyses
        result = {
            "file_path": file_path,
            "static_analysis": static_analysis,
            "compilation_analysis": compile_analysis,
            "runtime_analysis": runtime_analysis,
            "ai_analysis": ai_analysis,
            "recommendations": self._generate_recommendations(ai_analysis),
            "status": "Analysis complete"
        }
        
        logger.info("✅ AI debugging analysis complete")
        return result
    
    async def _perform_static_analysis(self, code: str, file_path: str) -> Dict:
        """Perform static code analysis"""
        logger.info("🔍 Performing static analysis")
        
        analysis = {
            "line_count": len(code.split('\n')),
            "function_count": 0,
            "potential_issues": [],
            "code_metrics": {}
        }
        
        # Count functions (simple regex approach)
        import re
        function_pattern = r'\w+\s+\w+\s*\([^)]*\)\s*\{'
        functions = re.findall(function_pattern, code)
        analysis["function_count"] = len(functions)
        
        # Check for common issues
        issues = []
        
        # Check for missing includes
        if '#include' not in code:
            issues.append("No include statements found")
        
        # Check for potential buffer overflows
        if 'gets(' in code:
            issues.append("Use of unsafe gets() function detected")
        
        # Check for uninitialized variables (basic check)
        var_declarations = re.findall(r'\b(int|float|double|char)\s+(\w+);', code)
        for var_type, var_name in var_declarations:
            if f'{var_name} =' not in code:
                issues.append(f"Potentially uninitialized variable: {var_name}")
        
        analysis["potential_issues"] = issues
        
        # Code metrics
        analysis["code_metrics"] = {
            "cyclomatic_complexity": self._calculate_cyclomatic_complexity(code),
            "comment_ratio": self._calculate_comment_ratio(code),
            "avg_function_length": self._calculate_avg_function_length(code)
        }
        
        return analysis
    
    async def _analyze_compilation(self, file_path: str, flags: List[str]) -> Dict:
        """Analyze compilation process"""
        logger.info("🔨 Analyzing compilation")
        
        try:
            # Create temporary executable path
            temp_dir = tempfile.mkdtemp()
            executable_path = os.path.join(temp_dir, "debug_executable")
            
            # Compile with debugging info
            compile_cmd = ["gcc", "-g", "-Wall", "-Wextra"] + flags + [file_path, "-o", executable_path]
            
            result = subprocess.run(
                compile_cmd, 
                capture_output=True, 
                text=True, 
                timeout=30
            )
            
            return {
                "compilation_successful": result.returncode == 0,
                "executable_path": executable_path if result.returncode == 0 else None,
                "warnings": result.stderr if result.stderr and result.returncode == 0 else "",
                "errors": result.stderr if result.returncode != 0 else "",
                "command": " ".join(compile_cmd)
            }
            
        except subprocess.TimeoutExpired:
            return {
                "compilation_successful": False,
                "errors": "Compilation timeout",
                "command": " ".join(compile_cmd)
            }
        except Exception as e:
            return {
                "compilation_successful": False,
                "errors": str(e),
                "command": "N/A"
            }
    
    async def _perform_runtime_analysis(self, executable_path: str, source_code: str) -> Dict:
        """Perform runtime analysis using GDB"""
        logger.info("⚡ Performing runtime analysis")
        
        if not self.gdb_available:
            return {"error": "GDB not available"}
        
        try:
            # Create GDB script for automated analysis
            gdb_script = f"""
set confirm off
file {executable_path}
break main
run
info locals
bt
continue
quit
"""
            
            # Write script to temporary file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.gdb', delete=False) as f:
                f.write(gdb_script)
                script_path = f.name
            
            # Run GDB with script
            result = subprocess.run(
                ['gdb', '--batch', '--command', script_path],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            # Clean up
            os.unlink(script_path)
            
            return {
                "gdb_output": result.stdout,
                "gdb_errors": result.stderr,
                "execution_successful": "exited normally" in result.stdout.lower(),
                "breakpoints_hit": "Breakpoint" in result.stdout,
                "stack_trace": self._extract_stack_trace(result.stdout)
            }
            
        except subprocess.TimeoutExpired:
            return {"error": "GDB execution timeout"}
        except Exception as e:
            return {"error": f"Runtime analysis failed: {e}"}
    
    async def _perform_ai_analysis(
        self, code: str, static: Dict, compile: Dict, runtime: Dict, file_path: str
    ) -> Dict:
        """Perform AI-powered analysis of all debugging data"""
        logger.info("🤖 Performing AI analysis")
        
        # Create comprehensive error context
        error_context = {
            "file": file_path,
            "static_issues": static.get("potential_issues", []),
            "compile_errors": compile.get("errors", ""),
            "runtime_output": runtime.get("gdb_output", ""),
            "code_metrics": static.get("code_metrics", {})
        }
        
        # If there are compilation errors, focus on those
        if not compile.get("compilation_successful", False):
            return await self.llm_client.analyze_code_error(
                code, 
                compile.get("errors", "Unknown compilation error"), 
                error_context
            )
        
        # If there are runtime issues, analyze those
        elif runtime.get("gdb_errors") or not runtime.get("execution_successful", True):
            error_msg = runtime.get("gdb_errors", "Runtime execution issues")
            return await self.llm_client.analyze_code_error(code, error_msg, error_context)
        
        # Otherwise, perform general code quality analysis
        else:
            return await self.llm_client.analyze_code_error(
                code, 
                "Code quality and improvement analysis", 
                error_context
            )
    
    def _generate_recommendations(self, ai_analysis: Dict) -> List[Dict]:
        """Generate actionable recommendations from AI analysis"""
        recommendations = []
        
        if "fix_suggestions" in ai_analysis:
            for i, suggestion in enumerate(ai_analysis["fix_suggestions"]):
                recommendations.append({
                    "type": "fix",
                    "priority": "high" if i == 0 else "medium",
                    "description": suggestion,
                    "category": "bug_fix"
                })
        
        if "prevention" in ai_analysis:
            for prevention in ai_analysis["prevention"]:
                recommendations.append({
                    "type": "prevention",
                    "priority": "medium",
                    "description": prevention,
                    "category": "best_practice"
                })
        
        if "code_quality" in ai_analysis:
            for quality in ai_analysis["code_quality"]:
                recommendations.append({
                    "type": "improvement",
                    "priority": "low",
                    "description": quality,
                    "category": "code_quality"
                })
        
        return recommendations
    
    def _calculate_cyclomatic_complexity(self, code: str) -> int:
        """Calculate basic cyclomatic complexity"""
        import re
        # Count decision points
        decisions = len(re.findall(r'\b(if|while|for|switch|case|\?)\b', code))
        return decisions + 1
    
    def _calculate_comment_ratio(self, code: str) -> float:
        """Calculate comment to code ratio"""
        lines = code.split('\n')
        comment_lines = sum(1 for line in lines if line.strip().startswith(('//', '/*', '*')))
        code_lines = sum(1 for line in lines if line.strip() and not line.strip().startswith(('//', '/*', '*')))
        return comment_lines / max(code_lines, 1)
    
    def _calculate_avg_function_length(self, code: str) -> float:
        """Calculate average function length"""
        import re
        functions = re.findall(r'\w+\s+\w+\s*\([^)]*\)\s*\{[^}]*\}', code, re.DOTALL)
        if not functions:
            return 0
        
        total_lines = sum(len(func.split('\n')) for func in functions)
        return total_lines / len(functions)
    
    def _extract_stack_trace(self, gdb_output: str) -> List[Dict]:
        """Extract stack trace from GDB output"""
        stack_trace = []
        lines = gdb_output.split('\n')
        
        for line in lines:
            if line.strip().startswith('#'):
                # Parse GDB stack frame
                import re
                match = re.match(r'#(\d+)\s+(.+)', line.strip())
                if match:
                    frame_num, frame_info = match.groups()
                    stack_trace.append({
                        "frame": int(frame_num),
                        "info": frame_info.strip()
                    })
        
        return stack_trace
    
    # Legacy test method for backward compatibility
    async def test_integration(self) -> Dict:
        """Test the enhanced AI debugging integration"""
        logger.info("🧪 Testing enhanced AI debugging integration")
        
        # Create test C code with intentional issues
        test_code = """
#include <stdio.h>

int factorial(int n) {
    if (n < 0) return -1;  // Error handling
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}

int main() {
    int result = factorial(5);
    printf("Factorial: %d\\n", result);
    
    // Intentional issue for testing
    int x;  // Uninitialized variable
    printf("X value: %d\\n", x);
    
    return 0;
}
"""
        
        # Write test code to temporary file
        import tempfile
        with tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False) as f:
            f.write(test_code)
            temp_file = f.name
        
        try:
            # Run debugging analysis
            result = await self.debug_code_file(temp_file)
            
            # Clean up
            os.unlink(temp_file)
            if result.get("compilation_analysis", {}).get("executable_path"):
                try:
                    os.unlink(result["compilation_analysis"]["executable_path"])
                except:
                    pass
            
            return {
                "status": "Phase 3 - Enhanced AI debugging integration complete",
                "chatdbg_available": self.chatdbg_available,
                "llmdebugger_available": self.llmdebugger_available,
                "gdb_available": self.gdb_available,
                "llm_client_ready": self.llm_client.openai_client is not None or self.llm_client.anthropic_client is not None,
                "analysis_components": {
                    "static_analysis": "potential_issues" in result.get("static_analysis", {}),
                    "compilation_analysis": "compilation_successful" in result.get("compilation_analysis", {}),
                    "ai_analysis": "root_cause" in result.get("ai_analysis", {}),
                    "recommendations": len(result.get("recommendations", []))
                }
            }
            
        except Exception as e:
            logger.error(f"Integration test failed: {e}")
            return {
                "status": "Phase 3 - Integration test failed",
                "error": str(e),
                "chatdbg_available": self.chatdbg_available,
                "llmdebugger_available": self.llmdebugger_available,
                "gdb_available": self.gdb_available
            }

# For backward compatibility, create an alias
AIDebugger = EnhancedAIDebugger

"""








""""""
AI Debugger - Main debugging interface-

PHASE 1-2 Implementation

import sys
import logging
from pathlib import Path

# Add ChatDBG to path
chatdbg_path = Path(__file__).parent.parent.parent / "tools" / "ChatDBG"
sys.path.append(str(chatdbg_path))

# Add LLMDebugger to path
llmdebugger_path = Path(__file__).parent.parent.parent / "tools" / "LLMDebugger"
sys.path.append(str(llmdebugger_path))

logger = logging.getLogger(__name__)

class AIDebugger:
    """"""Unified AI Debugging interface combining ChatDBG and LLMDebugger""""""
    
    def __init__(self):
        logger.info("Initializing AI Debugger")
        self.chatdbg_available = self._check_chatdbg()
        self.llmdebugger_available = self._check_llmdebugger()
        self.setup_integration()
    
    def _check_chatdbg(self):
        """"""Check if ChatDBG is available""""""
        try:
            chatdbg_path = Path(__file__).parent.parent.parent / "tools" / "ChatDBG"
            if chatdbg_path.exists():
                logger.info("ChatDBG found and available")
                return True
            else:
                logger.warning("ChatDBG not found")
                return False
        except Exception as e:
            logger.error(f"ChatDBG check failed: {e}")
            return False
    
    def _check_llmdebugger(self):
        """"""Check if LLMDebugger is available""""""
        try:
            llmdebugger_path = Path(__file__).parent.parent.parent / "tools" / "LLMDebugger"
            if llmdebugger_path.exists():
                logger.info("LLMDebugger found and available")
                return True
            else:
                logger.warning("LLMDebugger not found")
                return False
        except Exception as e:
            logger.error(f"LLMDebugger check failed: {e}")
            return False
    
    def setup_integration(self):
        """"""Setup integration with external tools""""""
        logger.info("Setting up AI Debugger integration")
        logger.info(f"ChatDBG available: {self.chatdbg_available}")
        logger.info(f"LLMDebugger available: {self.llmdebugger_available}")
    
    def debug_code(self, code_file: str):
        """"""Main debugging interface""""""
        logger.info(f"Debugging code file: {code_file}")
        return {
            "status": "Phase 1-2 - Basic integration complete",
            "chatdbg_ready": self.chatdbg_available,
            "llmdebugger_ready": self.llmdebugger_available,
            "file": code_file
        }
    
    def test_integration(self):
        """"""Test the integration""""""
        logger.info("Testing AI Debugger integration")
        result = self.debug_code("test_file.c")
        logger.info(f"Integration test result: {result}")
        return result
"""

