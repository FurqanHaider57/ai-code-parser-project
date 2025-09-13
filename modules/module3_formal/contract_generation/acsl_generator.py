"""
ACSL Contract Generator - Corrected for AI Code Parser Project
Fixed imports and paths for your specific project structure
"""
import logging
import json
import re
import os
import sys
from typing import Dict, List, Optional
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent.parent.parent
sys.path.insert(0, str(project_root))

# Safe imports with fallbacks
try:
    from config_phase3 import AIConfig, FormalVerificationConfig
except ImportError:
    # Fallback configuration for when config_phase3 is not available
    class AIConfig:
        OPENAI_API_KEY = os.getenv("OPENAI_API_KEY", "ollama")
        ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY", "ollama")
        DEFAULT_MODEL = os.getenv("DEFAULT_LLM_MODEL", "llama3")
        BACKUP_MODEL = os.getenv("BACKUP_LLM_MODEL", "mistral") 
        MAX_TOKENS = int(os.getenv("MAX_TOKENS", "2048"))
        TEMPERATURE = float(os.getenv("TEMPERATURE", "0.1"))
    
    class FormalVerificationConfig:
        FRAMAC_TIMEOUT = int(os.getenv("FRAMAC_TIMEOUT", "60"))
        Z3_TIMEOUT = int(os.getenv("Z3_TIMEOUT", "30"))
        ACSL_TEMPLATES_DIR = project_root / "templates" / "acsl"

logger = logging.getLogger(__name__)

class ACSLContractGenerator:
    """AI-powered ACSL contract generator with template support"""
    
    def __init__(self):
        logger.info("🚀 Initializing ACSL Contract Generator")
        
        self.templates = self._load_contract_templates()
        self.llm_available = False
        self.llm_client = None
        self.llm_type = None
        
        # Try to setup LLM (don't fail if not available)
        try:
            self._setup_llm()
        except Exception as e:
            logger.warning(f"LLM setup failed, using templates only: {e}")
        
        logger.info(f"✅ ACSL Generator ready (AI: {self.llm_available})")
    
    def _load_contract_templates(self) -> Dict:
        """Load ACSL contract templates"""
        
        # Try to load from templates directory
        template_paths = [
            FormalVerificationConfig.ACSL_TEMPLATES_DIR / "basic" / "function_templates.json",
            project_root / "templates" / "acsl" / "basic" / "function_templates.json",
            project_root / "modules" / "module3_formal" / "templates" / "acsl" / "basic" / "function_templates.json"
        ]
        
        for template_path in template_paths:
            try:
                if template_path.exists():
                    with open(template_path, 'r') as f:
                        templates = json.load(f)
                        logger.info(f"✅ Templates loaded from {template_path}")
                        return templates
            except Exception as e:
                logger.warning(f"Failed to load templates from {template_path}: {e}")
        
        # Fallback to built-in templates
        logger.info("📦 Using built-in templates")
        return self._get_builtin_templates()
    
    def _get_builtin_templates(self) -> Dict:
        """Built-in contract templates as fallback"""
        return {
            "mathematical": {
                "factorial": {
                    "preconditions": ["requires n >= 0;", "requires n <= 20;"],
                    "postconditions": ["ensures \\result >= 1;", "ensures n == 0 ==> \\result == 1;"]
                },
                "fibonacci": {
                    "preconditions": ["requires n >= 0;", "requires n <= 45;"],
                    "postconditions": ["ensures \\result >= 0;", "ensures n <= 1 ==> \\result == n;"]
                },
                "gcd": {
                    "preconditions": ["requires a >= 0 && b >= 0;", "requires a + b > 0;"],
                    "postconditions": ["ensures \\result > 0;"]
                }
            },
            "control_systems": {
                "pid_controller": {
                    "preconditions": [
                        "requires \\is_finite(setpoint) && \\is_finite(measurement);",
                        "requires kp >= 0.0 && ki >= 0.0 && kd >= 0.0;"
                    ],
                    "postconditions": ["ensures \\is_finite(\\result);"]
                }
            },
            "general": {
                "default": {
                    "preconditions": ["requires parameters are valid;"],
                    "postconditions": ["ensures \\result is computed correctly;"]
                }
            }
        }
    
    def _setup_llm(self):
        """Setup LLM client with safe imports"""
        
        # Try OpenAI first
        if AIConfig.OPENAI_API_KEY and AIConfig.OPENAI_API_KEY != "ollama":
            try:
                import openai
                self.llm_client = openai.OpenAI(
                    api_key=AIConfig.OPENAI_API_KEY,
                    base_url=os.getenv("OPENAI_API_BASE", None)
                )
                self.llm_type = "openai"
                self.llm_available = True
                logger.info("✅ OpenAI client initialized")
                return
            except ImportError:
                logger.warning("OpenAI package not installed")
            except Exception as e:
                logger.warning(f"OpenAI setup failed: {e}")
        
        # Try Anthropic
        if AIConfig.ANTHROPIC_API_KEY and AIConfig.ANTHROPIC_API_KEY != "ollama":
            try:
                # Use the mock anthropic from your project
                import mocks.mock_anthropic as anthropic
                self.llm_client = anthropic.Client(api_key=AIConfig.ANTHROPIC_API_KEY)
                self.llm_type = "anthropic"
                self.llm_available = True
                logger.info("✅ Anthropic client initialized (mock)")
                return
            except ImportError:
                logger.warning("Anthropic mock not available")
            except Exception as e:
                logger.warning(f"Anthropic setup failed: {e}")
        
        # Try local Ollama
        try:
            import requests
            response = requests.get("http://localhost:11434/api/tags", timeout=5)
            if response.status_code == 200:
                self.llm_client = "ollama"
                self.llm_type = "ollama"
                self.llm_available = True
                logger.info("✅ Ollama local server detected")
                return
        except Exception as e:
            logger.warning(f"Ollama not available: {e}")
        
        # No LLM available
        self.llm_available = False
        logger.info("ℹ️  No LLM available, using templates only")
    
    async def generate_contracts_for_function(
        self, 
        c_code: str, 
        function_name: str,
        specification: str = ""
    ) -> Dict:
        """Generate ACSL contracts for a specific function"""
        
        logger.info(f"🔍 Generating contracts for: {function_name}")
        
        try:
            # Parse function information
            function_info = self._parse_function_info(c_code, function_name)
            if not function_info:
                return {
                    "error": f"Function '{function_name}' not found in code",
                    "function_name": function_name,
                    "contracts": {"preconditions": [], "postconditions": []}
                }
            
            # Categorize function
            category = self._categorize_function(function_name, c_code, specification)
            
            # Generate contracts using templates
            template_contracts = self._generate_from_templates(function_name, category, function_info)
            
            # Generate contracts using AI if available
            ai_contracts = {}
            if self.llm_available:
                ai_contracts = await self._generate_with_ai(function_info, specification)
            
            # Combine contracts
            combined_contracts = self._combine_contracts(template_contracts, ai_contracts)
            
            # Validate contracts
            validation_result = self._validate_contracts(combined_contracts)
            
            return {
                "function_name": function_name,
                "contracts": combined_contracts,
                "validation": validation_result,
                "acsl_code": self._format_acsl_code(combined_contracts, function_info),
                "metadata": {
                    "category": category,
                    "ai_enhanced": bool(ai_contracts and ai_contracts.get("preconditions")),
                    "template_used": bool(template_contracts)
                }
            }
            
        except Exception as e:
            logger.error(f"Contract generation failed for {function_name}: {e}")
            return {
                "error": str(e),
                "function_name": function_name,
                "contracts": {"preconditions": [], "postconditions": []}
            }
    
    def _parse_function_info(self, c_code: str, function_name: str) -> Optional[Dict]:
        """Parse function information from C code using regex"""
        
        # Find function signature
        pattern = rf'^\s*(\w+(?:\s*\*)?)\s+{re.escape(function_name)}\s*\(([^)]*)\)\s*\{{'
        match = re.search(pattern, c_code, re.MULTILINE)
        
        if not match:
            return None
        
        return_type = match.group(1).strip()
        params_str = match.group(2).strip()
        
        # Parse parameters
        parameters = []
        if params_str and params_str != "void":
            for param in params_str.split(','):
                param = param.strip()
                if param:
                    parts = param.split()
                    if len(parts) >= 2:
                        param_type = ' '.join(parts[:-1])
                        param_name = parts[-1].strip('*')
                        parameters.append({"type": param_type, "name": param_name})
        
        return {
            "name": function_name,
            "return_type": return_type,
            "parameters": parameters,
            "signature": match.group(0)
        }
    
    def _categorize_function(self, function_name: str, c_code: str, specification: str) -> str:
        """Categorize function for template selection"""
        
        name_lower = function_name.lower()
        
        # Mathematical functions
        math_keywords = ["factorial", "fibonacci", "gcd", "prime", "sqrt", "pow", "abs"]
        if any(keyword in name_lower for keyword in math_keywords):
            return "mathematical"
        
        # Control systems
        control_keywords = ["pid", "control", "feedback", "filter", "regulator"]
        if any(keyword in name_lower for keyword in control_keywords):
            return "control_systems"
        
        # Signal processing
        signal_keywords = ["signal", "fft", "filter", "sample", "frequency"]
        if any(keyword in name_lower for keyword in signal_keywords):
            return "signal_processing"
        
        # Memory management
        memory_keywords = ["malloc", "free", "alloc", "buffer", "memory"]
        if any(keyword in name_lower for keyword in memory_keywords):
            return "memory_management"
        
        return "general"
    
    def _generate_from_templates(self, function_name: str, category: str, function_info: Dict) -> Dict:
        """Generate contracts using templates"""
        
        contracts = {"preconditions": [], "postconditions": []}
        
        # Try specific function template
        if category in self.templates:
            category_templates = self.templates[category]
            if function_name in category_templates:
                template = category_templates[function_name]
                contracts["preconditions"].extend(template.get("preconditions", []))
                contracts["postconditions"].extend(template.get("postconditions", []))
                return contracts
        
        # Generate basic contracts based on function signature
        return_type = function_info.get("return_type", "")
        parameters = function_info.get("parameters", [])
        
        # Basic parameter preconditions
        for param in parameters:
            param_type = param.get("type", "")
            param_name = param.get("name", "")
            
            if "int" in param_type and param_name:
                contracts["preconditions"].append(f"requires {param_name} is valid;")
            elif "float" in param_type or "double" in param_type:
                contracts["preconditions"].append(f"requires \\is_finite({param_name});")
            elif "*" in param_type:
                contracts["preconditions"].append(f"requires \\valid({param_name});")
        
        # Basic return value postconditions
        if return_type != "void":
            if "int" in return_type:
                contracts["postconditions"].append("ensures \\result is valid;")
            elif "float" in return_type or "double" in return_type:
                contracts["postconditions"].append("ensures \\is_finite(\\result);")
            elif "*" in return_type:
                contracts["postconditions"].append("ensures \\result == \\null || \\valid(\\result);")
        
        # Use general default if no specific contracts
        if not contracts["preconditions"] and not contracts["postconditions"]:
            default_template = self.templates.get("general", {}).get("default", {})
            contracts["preconditions"].extend(default_template.get("preconditions", []))
            contracts["postconditions"].extend(default_template.get("postconditions", []))
        
        return contracts
    
    async def _generate_with_ai(self, function_info: Dict, specification: str) -> Dict:
        """Generate contracts using AI/LLM"""
        
        if not self.llm_available:
            return {}
        
        try:
            prompt = self._create_ai_prompt(function_info, specification)
            
            if self.llm_type == "openai":
                response = self.llm_client.chat.completions.create(
                    model=AIConfig.DEFAULT_MODEL,
                    messages=[{"role": "user", "content": prompt}],
                    max_tokens=AIConfig.MAX_TOKENS,
                    temperature=AIConfig.TEMPERATURE
                )
                ai_response = response.choices[0].message.content
                
            elif self.llm_type == "anthropic":
                # Use your mock anthropic client
                response = self.llm_client.messages(
                    model=AIConfig.DEFAULT_MODEL,
                    max_tokens=AIConfig.MAX_TOKENS,
                    temperature=AIConfig.TEMPERATURE,
                    messages=[{"role": "user", "content": prompt}]
                )
                ai_response = response.get("content", "")
                
            elif self.llm_type == "ollama":
                import requests
                response = requests.post("http://localhost:11434/api/generate", json={
                    "model": AIConfig.DEFAULT_MODEL,
                    "prompt": prompt,
                    "stream": False
                }, timeout=30)
                
                if response.status_code == 200:
                    ai_response = response.json().get("response", "")
                else:
                    return {}
            
            else:
                return {}
            
            return self._parse_ai_response(ai_response)
            
        except Exception as e:
            logger.error(f"AI contract generation failed: {e}")
            return {}
    
    def _create_ai_prompt(self, function_info: Dict, specification: str) -> str:
        """Create AI prompt for contract generation"""
        
        return f"""
Generate ACSL (ANSI/ISO C Specification Language) contracts for this C function:

Function: {function_info.get('name', 'unknown')}
Return Type: {function_info.get('return_type', 'unknown')}
Parameters: {function_info.get('parameters', [])}
Specification: {specification}

Generate appropriate preconditions (requires) and postconditions (ensures).
Consider parameter validation, return value constraints, and safety conditions.

Respond in JSON format:
{{
    "preconditions": ["requires condition1;", "requires condition2;"],
    "postconditions": ["ensures condition1;", "ensures condition2;"]
}}
"""
    
    def _parse_ai_response(self, response: str) -> Dict:
        """Parse AI response to extract contracts"""
        
        try:
            # Look for JSON in response
            if "```json" in response:
                start = response.find("```json") + 7
                end = response.find("```", start)
                json_str = response[start:end].strip()
            elif "{" in response and "}" in response:
                start = response.find("{")
                end = response.rfind("}") + 1
                json_str = response[start:end]
            else:
                return {}
            
            contracts = json.loads(json_str)
            return {
                "preconditions": contracts.get("preconditions", []),
                "postconditions": contracts.get("postconditions", [])
            }
            
        except Exception as e:
            logger.error(f"AI response parsing failed: {e}")
            return {}
    
    def _combine_contracts(self, template_contracts: Dict, ai_contracts: Dict) -> Dict:
        """Combine template and AI contracts, removing duplicates"""
        
        combined = {"preconditions": [], "postconditions": []}
        
        # Combine preconditions
        all_preconds = (
            template_contracts.get("preconditions", []) +
            ai_contracts.get("preconditions", [])
        )
        
        seen_preconds = set()
        for precond in all_preconds:
            normalized = precond.strip().lower()
            if normalized not in seen_preconds:
                combined["preconditions"].append(precond)
                seen_preconds.add(normalized)
        
        # Combine postconditions
        all_postconds = (
            template_contracts.get("postconditions", []) +
            ai_contracts.get("postconditions", [])
        )
        
        seen_postconds = set()
        for postcond in all_postconds:
            normalized = postcond.strip().lower()
            if normalized not in seen_postconds:
                combined["postconditions"].append(postcond)
                seen_postconds.add(normalized)
        
        return combined
    
    def _validate_contracts(self, contracts: Dict) -> Dict:
        """Validate contract syntax"""
        
        validation = {"valid": True, "warnings": [], "errors": []}
        
        # Check preconditions
        for precond in contracts.get("preconditions", []):
            if not precond.strip().startswith("requires"):
                validation["errors"].append(f"Invalid precondition: {precond}")
                validation["valid"] = False
            if not precond.strip().endswith(";"):
                validation["warnings"].append(f"Missing semicolon: {precond}")
        
        # Check postconditions
        for postcond in contracts.get("postconditions", []):
            if not postcond.strip().startswith("ensures"):
                validation["errors"].append(f"Invalid postcondition: {postcond}")
                validation["valid"] = False
            if not postcond.strip().endswith(";"):
                validation["warnings"].append(f"Missing semicolon: {postcond}")
        
        return validation
    
    def _format_acsl_code(self, contracts: Dict, function_info: Dict) -> str:
        """Format contracts as ACSL annotation"""
        
        lines = ["/*@"]
        
        # Add preconditions
        for precond in contracts.get("preconditions", []):
            lines.append(f"  @ {precond}")
        
        # Add postconditions
        for postcond in contracts.get("postconditions", []):
            lines.append(f"  @ {postcond}")
        
        lines.append("  @*/")
        
        return "\n".join(lines)


# Test the generator
async def test_acsl_generator():
    """Test the ACSL contract generator"""
    
    generator = ACSLContractGenerator()
    
    test_code = """
int factorial(int n) {
    if (n < 0) return -1;
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}
"""
    
    result = await generator.generate_contracts_for_function(
        test_code, "factorial", "Calculate factorial of non-negative integers"
    )
    
    print("🧪 ACSL Generator Test Results:")
    print("=" * 40)
    print(f"Function: {result.get('function_name', 'unknown')}")
    print(f"Category: {result.get('metadata', {}).get('category', 'unknown')}")
    print(f"AI Enhanced: {result.get('metadata', {}).get('ai_enhanced', False)}")
    print(f"Template Used: {result.get('metadata', {}).get('template_used', False)}")
    
    contracts = result.get("contracts", {})
    print(f"\nPreconditions ({len(contracts.get('preconditions', []))}): ")
    for precond in contracts.get("preconditions", []):
        print(f"  - {precond}")
    
    print(f"\nPostconditions ({len(contracts.get('postconditions', []))}): ")
    for postcond in contracts.get("postconditions", []):
        print(f"  - {postcond}")
    
    print(f"\nGenerated ACSL:")
    print(result.get("acsl_code", "No ACSL generated"))
    
    return result

if __name__ == "__main__":
    import asyncio
    asyncio.run(test_acsl_generator())