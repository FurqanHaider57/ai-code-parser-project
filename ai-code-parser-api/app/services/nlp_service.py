import asyncio
import sys
import io
import contextlib
import tempfile
import re
from pathlib import Path
from typing import List, Dict, Tuple
from dataclasses import dataclass

# Add parent project to path
project_root = Path(__file__).parent.parent.parent.parent
sys.path.insert(0, str(project_root))

from modules.module2_nlp.nlp_test_generator import EnhancedNLPTestGenerator, CFunctionInfo

@dataclass
class DynamicCodeAnalysis:
    """Results from analyzing user-provided code"""
    functions: List[CFunctionInfo]
    test_cases: Dict
    unit_test_code: str
    status: str
    total_tests: int


class NLPService:
    """Service for NLP test generation functionality - ENHANCED with dynamic code analysis"""
    
    def __init__(self):
        self.generator = None
    
    def initialize(self, code_directory: str = None):
        """Initialize the NLP generator"""
        if code_directory is None:
            code_directory = str(project_root / "data" / "sample_code")
        
        if self.generator is None:
            # Suppress stdout during initialization to avoid print issues
            with self._suppress_stdout():
                self.generator = EnhancedNLPTestGenerator(code_directory)
    
    @staticmethod
    @contextlib.contextmanager
    def _suppress_stdout():
        """Context manager to suppress stdout/stderr"""
        old_stdout = sys.stdout
        old_stderr = sys.stderr
        try:
            sys.stdout = io.StringIO()
            sys.stderr = io.StringIO()
            yield
        finally:
            sys.stdout = old_stdout
            sys.stderr = old_stderr
    
    def _parse_c_functions(self, code: str, filename: str = "user_code.c") -> List[CFunctionInfo]:
        """Parse C functions from user-provided code string"""
        functions = []
        
        # Pattern to match C function definitions
        # Matches: return_type function_name(parameters) {
        pattern = r'\b([a-zA-Z_][\w\*\s]+)\s+([a-zA-Z_]\w*)\s*\(([^)]*)\)\s*\{'
        
        matches = re.finditer(pattern, code)
        
        for match in matches:
            return_type = match.group(1).strip()
            func_name = match.group(2).strip()
            params_str = match.group(3).strip()
            
            # Skip main function
            if func_name == 'main':
                continue
            
            # Parse parameters
            parameters = self._parse_parameters(params_str)
            
            # Create signature
            signature = f"{return_type} {func_name}({params_str});"
            
            # Get line number
            line_number = code[:match.start()].count('\n') + 1
            
            # Create CFunctionInfo
            func_info = CFunctionInfo(
                name=func_name,
                return_type=return_type,
                parameters=parameters,
                signature=signature,
                file_path=filename,
                line_number=line_number,
                body_preview=""
            )
            
            functions.append(func_info)
        
        return functions
    
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
    
    async def analyze_user_code_async(self, code: str, filename: str = "user_code.c") -> Dict:
        """Analyze user-provided C code and generate tests - ASYNC"""
        self.initialize()
        
        # Parse functions from user code
        discovered_functions = self._parse_c_functions(code, filename)
        
        if not discovered_functions:
            return {
                "status": "No C functions found in provided code",
                "functions_found": 0,
                "discovered_functions": [],
                "test_cases": {},
                "unit_test_code": "",
                "total_tests": 0,
                "message": "Make sure your code contains valid C function definitions (not just main)"
            }
        
        # Temporarily replace generator's discovered functions with user's functions
        original_functions = self.generator.discovered_functions
        self.generator.discovered_functions = discovered_functions
        
        try:
            # Generate test cases for user's functions
            with self._suppress_stdout():
                result = await self.generator.generate_test_cases_from_functions(num_tests=5)
            
            # Add the actual code to the result for reference
            result['analyzed_code'] = code
            result['functions_details'] = [
                {
                    'name': func.name,
                    'signature': func.signature,
                    'return_type': func.return_type,
                    'parameters': [{'type': p[0], 'name': p[1]} for p in func.parameters],
                    'line_number': func.line_number
                }
                for func in discovered_functions
            ]
            
            return result
            
        finally:
            # Restore original functions
            self.generator.discovered_functions = original_functions
    
    def analyze_user_code(self, code: str, filename: str = "user_code.c") -> Dict:
        """Synchronous wrapper for analyzing user code"""
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        
        try:
            result = loop.run_until_complete(
                asyncio.wait_for(
                    self.analyze_user_code_async(code, filename),
                    timeout=60.0
                )
            )
            
            import gc
            gc.collect()
            
            return result
            
        except asyncio.TimeoutError:
            return {
                'error': 'Code analysis timed out after 60 seconds',
                'status': 'timeout'
            }
        except Exception as e:
            import traceback
            return {
                'error': str(e),
                'traceback': traceback.format_exc(),
                'status': 'error'
            }
        finally:
            try:
                pending = asyncio.all_tasks(loop)
                for task in pending:
                    task.cancel()
                
                if pending:
                    loop.run_until_complete(asyncio.gather(*pending, return_exceptions=True))
                
                loop.close()
            except Exception:
                pass
    
    # Keep the original methods for backward compatibility
    
    async def generate_tests_async(self, specifications: str = None) -> dict:
        """Generate tests asynchronously from sample code"""
        self.initialize()
        
        with self._suppress_stdout():
            result = await self.generator.generate_test_cases_from_functions(num_tests=5)
        
        return result
    
    def generate_tests(self, specifications: str = None) -> dict:
        """Synchronous wrapper for test generation from sample code"""
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        
        try:
            result = loop.run_until_complete(
                asyncio.wait_for(
                    self.generate_tests_async(specifications),
                    timeout=60.0
                )
            )
            
            import gc
            gc.collect()
            
            return result
            
        except asyncio.TimeoutError:
            return {
                'error': 'Test generation timed out after 60 seconds',
                'status': 'timeout'
            }
        except Exception as e:
            import traceback
            return {
                'error': str(e),
                'traceback': traceback.format_exc(),
                'status': 'error'
            }
        finally:
            try:
                pending = asyncio.all_tasks(loop)
                for task in pending:
                    task.cancel()
                
                if pending:
                    loop.run_until_complete(asyncio.gather(*pending, return_exceptions=True))
                
                loop.close()
            except Exception:
                pass
    
    def get_discovered_functions(self) -> dict:
        """Get list of discovered C functions from sample code"""
        self.initialize()
        
        functions_list = []
        for func in self.generator.discovered_functions:
            if isinstance(func, dict):
                functions_list.append({
                    "name": func.get("name", ""),
                    "signature": func.get("signature", ""),
                    "file": func.get("file_path", "")
                })
            else:
                functions_list.append({
                    "name": func.name,
                    "signature": func.signature,
                    "file": func.file_path
                })
        
        return {
            "functions": functions_list,
            "count": len(self.generator.discovered_functions)
        }
    
    def get_status(self) -> dict:
        """Get NLP service status without heavy operations"""
        try:
            self.initialize()
            return {
                'status': 'ready',
                'device': str(self.generator.device),
                'models_loaded': self.generator.model is not None,
                'functions_discovered': len(self.generator.discovered_functions),
                'supports_dynamic_code': True
            }
        except Exception as e:
            return {
                'status': 'error',
                'error': str(e)
            }