"""
Advanced ACSL Contract Generator using AI and templates
"""
import logging
import json
import re
from typing import Dict, List, Optional, Tuple
from pathlib import Path
import tree_sitter # type: ignore
from tree_sitter import Language, Node # type: ignore
import openai # type: ignore
import anthropic # type: ignore

from config_phase3 import AIConfig, FormalVerificationConfig

logger = logging.getLogger(__name__)

class ACSLContractGenerator:
    """Generate ACSL contracts using AI and template matching"""
    
    def __init__(self):
        logger.info("🚀 Initializing ACSL Contract Generator")
        
        self.llm_client = self._setup_llm_client()
        self.templates = self._load_templates()
        self.parser = self._setup_c_parser()
        
        logger.info("✅ ACSL Contract Generator initialized")
    
    def _setup_llm_client(self):
        """Setup LLM client for contract generation"""
        if AIConfig.OPENAI_API_KEY:
            return openai.OpenAI(api_key=AIConfig.OPENAI_API_KEY)
        elif AIConfig.ANTHROPIC_API_KEY:
            return anthropic.Anthropic(api_key=AIConfig.ANTHROPIC_API_KEY)
        return None
    
    def _load_templates(self) -> Dict:
        """Load ACSL contract templates"""
        try:
            template_path = Path("templates/acsl/basic/function_templates.json")
            if template_path.exists():
                with open(template_path, "r") as f:
                    return json.load(f)
            else:
                logger.warning("Template file not found, using built-in templates")
                return self._get_builtin_templates()
        except Exception as e:
            logger.error(f"Failed to load templates: {e}")
            return self._get_builtin_templates()
    
    def _get_builtin_templates(self) -> Dict:
        """Get built-in contract templates"""
        return {
            "default": {
                "preconditions": ["requires parameters are valid;"],
                "postconditions": ["ensures \\result is computed correctly;"]
            }
        }
    
    def _setup_c_parser(self):
        """Setup Tree-sitter C parser"""
        try:
            # Build language library if not exists
            lib_path = Path("models/languages.so")
            if not lib_path.exists():
                Language.build_library(
                    str(lib_path),
                    ['models/tree-sitter-parsers/tree-sitter-c']
                )
            
            c_language = Language(str(lib_path), 'c')
            parser = tree_sitter.Parser()
            parser.set_language(c_language)
            
            logger.info("✅ C parser setup complete")
            return parser
            
        except Exception as e:
            logger.warning(f"C parser setup failed: {e}")
            return None
    
    async def generate_contracts_for_function(
        self, 
        c_code: str, 
        function_name: str,
        specification: str = ""
    ) -> Dict:
        """Generate ACSL contracts for a specific function"""
        
        logger.info(f"🔍 Generating contracts for function: {function_name}")
        
        # Parse function
        function_info = self._parse_function(c_code, function_name)
        if not function_info:
            return {"error": f"Function {function_name} not found"}
        
        # Determine function domain/category
        function_category = self._categorize_function(function_name, c_code, specification)
        
        # Generate contracts using multiple approaches
        template_contracts = self._generate_from_templates(function_name, function_category, function_info)
        ai_contracts = await self._generate_with_ai(function_info, specification)
        
        # Combine and refine contracts
        combined_contracts = self._combine_contracts(template_contracts, ai_contracts, function_info)
        
        # Validate contracts
        validation_result = self._validate_contracts(combined_contracts, function_info)
        
        return {
            "function_name": function_name,
            "function_info": function_info,
            "function_category": function_category,
            "contracts": combined_contracts,
            "validation": validation_result,
            "acsl_code": self._format_acsl_contracts(combined_contracts, function_info),
            "status": "Contract generation complete"
        }
    
    def _parse_function(self, c_code: str, function_name: str) -> Optional[Dict]:
        """Parse function using Tree-sitter"""
        
        if not self.parser:
            return self._parse_function_regex(c_code, function_name)
        
        try:
            tree = self.parser.parse(bytes(c_code, 'utf8'))
            
            def find_function(node: Node, target_name: str) -> Optional[Dict]:
                if node.type == 'function_definition':
                    # Extract function details
                    func_info = self._extract_function_info(node, c_code)
                    if func_info and func_info.get("name") == target_name:
                        return func_info
                
                for child in node.children:
                    result = find_function(child, target_name)
                    if result:
                        return result
                return None
            
            return find_function(tree.root_node, function_name)
            
        except Exception as e:
            logger.error(f"Function parsing failed: {e}")
            return self._parse_function_regex(c_code, function_name)
    
    def _extract_function_info(self, node: Node, source: str) -> Dict:
        """Extract detailed function information from AST node"""
        
        info = {
            "name": "",
            "return_type": "",
            "parameters": [],
            "body": "",
            "line_start": node.start_point[0] + 1,
            "line_end": node.end_point[0] + 1
        }
        
        for child in node.children:
            if child.type in ['primitive_type', 'type_identifier']:
                info["return_type"] = source[child.start_byte:child.end_byte]
            
            elif child.type == 'function_declarator':
                # Extract function name and parameters
                for grandchild in child.children:
                    if grandchild.type == 'identifier':
                        info["name"] = source[grandchild.start_byte:grandchild.end_byte]
                    elif grandchild.type == 'parameter_list':
                        info["parameters"] = self._extract_parameters(grandchild, source)
            
            elif child.type == 'compound_statement':
                info["body"] = source[child.start_byte:child.end_byte]
        
        return info
    
    def _extract_parameters(self, param_list_node: Node, source: str) -> List[Dict]:
        """Extract parameter information"""
        
        parameters = []
        for child in param_list_node.children:
            if child.type == 'parameter_declaration':
                param_info = {"type": "", "name": ""}
                
                for grandchild in child.children:
                    if grandchild.type in ['primitive_type', 'type_identifier']:
                        param_info["type"] = source[grandchild.start_byte:grandchild.end_byte]
                    elif grandchild.type in ['identifier', 'pointer_declarator']:
                        param_name = source[grandchild.start_byte:grandchild.end_byte]
                        if '*' in param_name:
                            param_info["type"] += "*"
                            param_info["name"] = param_name.replace('*', '').strip()
                        else:
                            param_info["name"] = param_name
                
                if param_info["type"] and param_info["name"]:
                    parameters.append(param_info)
        
        return parameters
    
    def _parse_function_regex(self, c_code: str, function_name: str) -> Optional[Dict]:
        """Fallback regex-based function parsing"""
        
        # Find function signature
        pattern = rf'(\w+(?:\s*\*)?)?\s+{re.escape(function_name)}\s*\([^)]*\)\s*\{{'
        match = re.search(pattern, c_code)
        
        if not match:
            return None
        
        # Extract basic information
        signature_start = match.start()
        signature_end = match.end()
        
        # Find function body
        brace_count = 1
        body_start = signature_end - 1
        i = signature_end
        
        while i < len(c_code) and brace_count > 0:
            if c_code[i] == '{':
                brace_count += 1
            elif c_code[i] == '}':
                brace_count -= 1
            i += 1
        
        body_end = i
        
        # Extract details using regex
        full_signature = c_code[signature_start:signature_end-1]
        
        # Parse return type
        return_type_match = re.match(r'(\w+(?:\s*\*)?)\s+', full_signature)
        return_type = return_type_match.group(1) if return_type_match else "unknown"
        
        # Parse parameters
        param_match = re.search(rf'{re.escape(function_name)}\s*\(([^)]*)\)', full_signature)
        param_str = param_match.group(1) if param_match else ""
        
        parameters = []
        if param_str.strip():
            for param in param_str.split(','):
                param = param.strip()
                param_parts = param.split()
                if len(param_parts) >= 2:
                    param_type = ' '.join(param_parts[:-1])
                    param_name = param_parts[-1].strip('*')
                    parameters.append({"type": param_type, "name": param_name})
        
        return {
            "name": function_name,
            "return_type": return_type,
            "parameters": parameters,
            "body": c_code[body_start:body_end],
            "signature": full_signature
        }
    
    def _categorize_function(self, function_name: str, c_code: str, specification: str) -> str:
        """Categorize function to determine appropriate templates"""
        
        # Check against known patterns
        categories = {
            "mathematical": ["factorial", "fibonacci", "gcd", "prime", "sqrt", "pow"],
            "control_systems": ["pid", "control", "regulator", "feedback", "setpoint"],
            "signal_processing": ["filter", "fft", "convolution", "sample", "frequency"],
            "memory_management": ["malloc", "free", "alloc", "memory", "buffer"],
            "string_processing": ["strlen", "strcmp", "strcpy", "strcat", "parse"],
            "file_io": ["fopen", "fread", "fwrite", "fclose", "file"]
        }
        
        function_lower = function_name.lower()
        code_lower = c_code.lower()
        spec_lower = specification.lower()
        
        for category, keywords in categories.items():
            if any(keyword in function_lower for keyword in keywords):
                return category
            if any(keyword in code_lower for keyword in keywords):
                return category
            if any(keyword in spec_lower for keyword in keywords):
                return category
        
        return "general"
    
    def _generate_from_templates(
        self, 
        function_name: str, 
        category: str, 
        function_info: Dict
    ) -> Dict:
        """Generate contracts using templates"""
        
        contracts = {"preconditions": [], "postconditions": []}
        
        # Try category-specific templates
        if category in self.templates:
            category_templates = self.templates[category]
            
            # Look for function-specific template
            if function_name in category_templates:
                template = category_templates[function_name]
                contracts["preconditions"].extend(template.get("preconditions", []))
                contracts["postconditions"].extend(template.get("postconditions", []))
                return contracts
            
            # Use first template from category as fallback
            if category_templates:
                first_template = next(iter(category_templates.values()))
                contracts["preconditions"].extend(first_template.get("preconditions", []))
                contracts["postconditions"].extend(first_template.get("postconditions", []))
                return contracts
        
        # Generate basic contracts based on function signature
        return_type = function_info.get("return_type", "")
        parameters = function_info.get("parameters", [])
        
        # Basic preconditions
        for param in parameters:
            param_type = param.get("type", "")
            param_name = param.get("name", "")
            
            if "int" in param_type and param_name:
                contracts["preconditions"].append(f"requires {param_name} is valid;")
            elif "float" in param_type or "double" in param_type:
                contracts["preconditions"].append(f"requires \\is_finite({param_name});")
            elif "*" in param_type:
                contracts["preconditions"].append(f"requires \\valid({param_name});")
        
        # Basic postconditions
        if return_type != "void":
            if "int" in return_type:
                contracts["postconditions"].append("ensures \\result is valid;")
            elif "float" in return_type or "double" in return_type:
                contracts["postconditions"].append("ensures \\is_finite(\\result);")
            elif "*" in return_type:
                contracts["postconditions"].append("ensures \\result == \\null || \\valid(\\result);")
        
        return contracts
    
    async def _generate_with_ai(self, function_info: Dict, specification: str) -> Dict:
        """Generate contracts using AI"""
        
        if not self.llm_client:
            return {"preconditions": [], "postconditions": []}
        
        try:
            prompt = self._create_contract_generation_prompt(function_info, specification)
            
            if hasattr(self.llm_client, 'chat'):  # OpenAI
                response = self.llm_client.chat.completions.create(
                    model=AIConfig.DEFAULT_MODEL,
                    messages=[{"role": "user", "content": prompt}],
                    max_tokens=1000,
                    temperature=0.1
                )
                ai_response = response.choices[0].message.content
            
            else:  # Anthropic
                response = self.llm_client.messages.create(
                    model="claude-3-sonnet-20240229",
                    max_tokens=1000,
                    messages=[{"role": "user", "content": prompt}]
                )
                ai_response = response.content[0].text
            
            return self._parse_ai_contracts(ai_response)
            
        except Exception as e:
            logger.error(f"AI contract generation failed: {e}")
            return {"preconditions": [], "postconditions": []}
    
    def _create_contract_generation_prompt(self, function_info: Dict, specification: str) -> str:
        """Create prompt for AI contract generation"""
        
        return f"""
You are an expert in formal verification and ACSL (ANSI/ISO C Specification Language).
Generate ACSL contracts for the following C function:

**Function Information:**
- Name: {function_info.get('name', 'unknown')}
- Return Type: {function_info.get('return_type', 'unknown')}
- Parameters: {function_info.get('parameters', [])}
- Specification: {specification}

**Function Body:**
```c
{function_info.get('body', 'Not available')[:500]}
```

Generate appropriate ACSL preconditions and postconditions. Consider:
1. Parameter validation
2. Return value constraints
3. Memory safety (if applicable)
4. Mathematical properties (if applicable)
5. Error conditions

Respond in JSON format:
{{
    "preconditions": ["requires condition1;", "requires condition2;"],
    "postconditions": ["ensures condition1;", "ensures condition2;"]
}}
"""
    
    def _parse_ai_contracts(self, ai_response: str) -> Dict:
        """Parse AI-generated contracts"""
        
        try:
            # Extract JSON from response
            if "```json" in ai_response:
                start = ai_response.find("```json") + 7
                end = ai_response.find("```", start)
                json_str = ai_response[start:end].strip()
            else:
                json_str = ai_response
            
            contracts = json.loads(json_str)
            
            # Validate structure
            if not isinstance(contracts, dict):
                raise ValueError("Invalid contract structure")
            
            return {
                "preconditions": contracts.get("preconditions", []),
                "postconditions": contracts.get("postconditions", [])
            }
            
        except Exception as e:
            logger.error(f"AI contract parsing failed: {e}")
            return {"preconditions": [], "postconditions": []}
    
    def _combine_contracts(
        self, 
        template_contracts: Dict, 
        ai_contracts: Dict, 
        function_info: Dict
    ) -> Dict:
        """Combine and deduplicate contracts from different sources"""
        
        combined = {
            "preconditions": [],
            "postconditions": []
        }
        
        # Combine preconditions
        all_preconditions = (
            template_contracts.get("preconditions", []) +
            ai_contracts.get("preconditions", [])
        )
        
        # Deduplicate and refine
        seen_preconditions = set()
        for precond in all_preconditions:
            normalized = self._normalize_contract(precond)
            if normalized not in seen_preconditions:
                combined["preconditions"].append(precond)
                seen_preconditions.add(normalized)
        
        # Combine postconditions
        all_postconditions = (
            template_contracts.get("postconditions", []) +
            ai_contracts.get("postconditions", [])
        )
        
        seen_postconditions = set()
        for postcond in all_postconditions:
            normalized = self._normalize_contract(postcond)
            if normalized not in seen_postconditions:
                combined["postconditions"].append(postcond)
                seen_postconditions.add(normalized)
        
        return combined
    
    def _normalize_contract(self, contract: str) -> str:
        """Normalize contract for deduplication"""
        # Remove extra whitespace and normalize format
        return re.sub(r'\s+', ' ', contract.strip().lower())
    
    def _validate_contracts(self, contracts: Dict, function_info: Dict) -> Dict:
        """Validate generated contracts"""
        
        validation = {
            "valid": True,
            "warnings": [],
            "errors": []
        }
        
        # Check preconditions
        for precond in contracts.get("preconditions", []):
            if not precond.strip().startswith("requires"):
                validation["errors"].append(f"Invalid precondition format: {precond}")
                validation["valid"] = False
            
            if not precond.strip().endswith(";"):
                validation["warnings"].append(f"Missing semicolon: {precond}")
        
        # Check postconditions
        for postcond in contracts.get("postconditions", []):
            if not postcond.strip().startswith("ensures"):
                validation["errors"].append(f"Invalid postcondition format: {postcond}")
                validation["valid"] = False
            
            if not postcond.strip().endswith(";"):
                validation["warnings"].append(f"Missing semicolon: {postcond}")
        
        return validation
    
    def _format_acsl_contracts(self, contracts: Dict, function_info: Dict) -> str:
        """Format contracts as ACSL code"""
        
        acsl_code = "/*@\n"
        
        # Add preconditions
        for precond in contracts.get("preconditions", []):
            acsl_code += f"  @ {precond}\n"
        
        # Add postconditions
        for postcond in contracts.get("postconditions", []):
            acsl_code += f"  @ {postcond}\n"
        
        acsl_code += "  @*/\n"
        
        # Add function signature
        return_type = function_info.get("return_type", "unknown")
        name = function_info.get("name", "unknown")
        params = function_info.get("parameters", [])
        
        param_strs = []
        for param in params:
            param_str = f"{param.get('type', 'unknown')} {param.get('name', 'param')}"
            param_strs.append(param_str)
        
        function_signature = f"{return_type} {name}({', '.join(param_strs)});"
        acsl_code += function_signature
        
        return acsl_code

# Test the contract generator
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
        test_code, 
        "factorial",
        "Calculate factorial of non-negative integers"
    )
    
    print("Generated ACSL contracts:")
    print(result.get("acsl_code", "No contracts generated"))
    
    return result

if __name__ == "__main__":
    import asyncio
    asyncio.run(test_acsl_generator())
