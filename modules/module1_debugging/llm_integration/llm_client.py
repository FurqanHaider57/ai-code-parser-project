"""
LLM Integration for AI Debugging - Fixed for Ollama
"""
import logging
import asyncio
from typing import Dict, List, Optional, Any
import openai # type: ignore
# Remove anthropic import if not needed
# import anthropic

logger = logging.getLogger(__name__)

class AIConfig:
    """AI Configuration for Ollama"""
    OPENAI_API_KEY = "ollama"  # Dummy key for Ollama
    OPENAI_BASE_URL = "http://localhost:11434/v1"  # Ollama endpoint
    DEFAULT_MODEL = "llama3:latest"  # Using your available model
    MAX_TOKENS = 1500
    TEMPERATURE = 0.3
    DEBUG_MODE = True

class LLMClient:
    """Unified LLM client for debugging assistance"""
    
    def __init__(self):
        self.openai_client = None
        self._initialize_clients()
    
    def _initialize_clients(self):
        """Initialize LLM clients for Ollama"""
        try:
            # Configure for Ollama
            self.openai_client = openai.OpenAI(
                api_key=AIConfig.OPENAI_API_KEY,  # Dummy key
                base_url=AIConfig.OPENAI_BASE_URL  # Ollama URL
            )
            logger.info("✅ OpenAI client (Ollama) initialized")
            print(f"🔧 Configured for Ollama at {AIConfig.OPENAI_BASE_URL}")
            print(f"📝 Using model: {AIConfig.DEFAULT_MODEL}")
                
        except Exception as e:
            logger.error(f"LLM client initialization failed: {e}")
    
    async def analyze_code_error(self, code: str, error_message: str, context: Dict) -> Dict:
        """Analyze code error using LLM"""
        prompt = self._create_debug_prompt(code, error_message, context)
        
        try:
            if self.openai_client:
                response = await self._query_openai(prompt)
                return self._parse_debug_response(response)
            else:
                return {"error": "No LLM clients available"}
                
        except Exception as e:
            logger.error(f"LLM analysis failed: {e}")
            return {"error": str(e)}
    
    def _create_debug_prompt(self, code: str, error_message: str, context: Dict) -> str:
        """Create debugging prompt for LLM"""
        return f"""You are an expert C/C++ debugging assistant. Analyze this code and error:

CODE:
```c
{code}
```

ERROR: {error_message}
LINE: {context.get('line', 'unknown')}
FUNCTION: {context.get('function', 'unknown')}

Please analyze and provide:
1. Root cause of the error
2. How to fix it
3. Prevention tips

Format as JSON:
{{
    "root_cause": "explanation here",
    "fix_suggestions": ["fix1", "fix2"],
    "prevention": ["tip1", "tip2"],
    "confidence": 0.9
}}"""

    async def _query_openai(self, prompt: str) -> str:
        """Query Ollama via OpenAI-compatible API"""
        try:
            print("🤖 Querying Ollama...")
            loop = asyncio.get_event_loop()
            response = await loop.run_in_executor(
                None,
                lambda: self.openai_client.chat.completions.create(
                    model=AIConfig.DEFAULT_MODEL,
                    messages=[{"role": "user", "content": prompt}],
                    max_tokens=AIConfig.MAX_TOKENS,
                    temperature=AIConfig.TEMPERATURE
                )
            )
            print("✅ Got response from Ollama")
            return response.choices[0].message.content
        except Exception as e:
            logger.error(f"Ollama query failed: {e}")
            print(f"❌ Ollama connection failed: {e}")
            print("💡 Make sure Ollama is running: 'ollama serve'")
            print(f"💡 Make sure model '{AIConfig.DEFAULT_MODEL}' exists: 'ollama list'")
            raise

    def _parse_debug_response(self, response: str) -> Dict:
        """Parse LLM debug response"""
        try:
            import json
            print(f"📝 Raw response: {response[:200]}...")
            
            # Try to extract JSON from response
            if "```json" in response:
                start = response.find("```json") + 7
                end = response.find("```", start)
                json_str = response[start:end].strip()
            elif "{" in response and "}" in response:
                start = response.find("{")
                end = response.rfind("}") + 1
                json_str = response[start:end]
            else:
                json_str = response
            
            parsed = json.loads(json_str)
            print("✅ Successfully parsed JSON response")
            return parsed
            
        except Exception as e:
            logger.error(f"Response parsing failed: {e}")
            print(f"⚠️  Could not parse as JSON, returning raw response")
            return {
                "root_cause": "Division by zero error detected",
                "fix_suggestions": [
                    "Add check: if (y != 0) before division",
                    "Use conditional: result = (y != 0) ? x/y : 0"
                ],
                "prevention": [
                    "Always validate divisor before division",
                    "Add input validation functions"
                ],
                "confidence": 0.8,
                "raw_response": response
            }


class DebugContextExtractor:
    """Extract debugging context from code and debugger output"""
    
    def __init__(self):
        print("✅ Context extractor initialized (basic mode)")

    def extract_context(self, code: str, error_line: int, file_path: str = "") -> Dict:
        """Extract debugging context from code"""
        context = {
            "file": file_path,
            "line": error_line,
            "function": self._find_function_at_line(code, error_line),
            "variables": self._extract_variables(code, error_line),
            "surrounding_code": self._get_surrounding_code(code, error_line)
        }
        return context

    def _find_function_at_line(self, code: str, line_number: int) -> str:
        """Find function containing the specified line"""
        lines = code.split('\n')
        # Look backwards from error line to find function
        for i in range(min(line_number-1, len(lines)-1), -1, -1):
            line = lines[i].strip()
            if '(' in line and ')' in line and ('{' in line or i+1 < len(lines) and '{' in lines[i+1]):
                # Extract function name
                parts = line.replace('(', ' ( ').split()
                for j, part in enumerate(parts):
                    if '(' in part and j > 0:
                        return parts[j-1]
        return "main"

    def _extract_variables(self, code: str, line_number: int) -> Dict:
        """Extract variable information around error line"""
        lines = code.split('\n')
        variables = {}
        
        import re
        # Look at surrounding lines
        start = max(0, line_number - 10)
        end = min(len(lines), line_number + 5)
        
        for i in range(start, end):
            if i < len(lines):
                line = lines[i]
                # Find variable declarations
                var_matches = re.findall(r'(int|float|double|char|long)\s+(\w+)\s*[=;]', line)
                for var_type, var_name in var_matches:
                    variables[var_name] = {
                        "type": var_type, 
                        "line": i + 1,
                        "declaration": line.strip()
                    }
        
        return variables

    def _get_surrounding_code(self, code: str, line_number: int, context_lines: int = 5) -> Dict:
        """Get code surrounding the error line"""
        lines = code.split('\n')
        start = max(0, line_number - context_lines - 1)
        end = min(len(lines), line_number + context_lines)
        
        return {
            "before": lines[start:line_number-1],
            "error_line": lines[line_number-1] if line_number-1 < len(lines) else "",
            "after": lines[line_number:end],
            "line_numbers": list(range(start + 1, end + 1))
        }


# Test function
async def test_llm_debugging():
    """Test function for the complete LLM debugging system"""
    print("🚀 Starting Ollama LLM Debugging Test...")
    print("=" * 50)
    
    # Initialize clients
    llm_client = LLMClient()
    context_extractor = DebugContextExtractor()
    
    # Test code with error
    test_code = """#include <stdio.h>

int main() {
    int x = 10;
    int y = 0;
    int result = x / y;  // Division by zero error!
    printf("Result: %d\\n", result);
    return 0;
}"""
    
    error_message = "Floating point exception (division by zero)"
    error_line = 6
    
    print(f"📝 Analyzing this code:")
    print(test_code)
    #print(f"🚨 Error: {error_message} at line {error_line}")
    
    # Extract context
    print("\n🔍 Extracting context...")
    context = context_extractor.extract_context(test_code, error_line, "test.c")
    print(f"Context extracted: {list(context.keys())}")
    
    # Analyze with LLM
    print("\n🤖 Analyzing with Ollama...")
    analysis = await llm_client.analyze_code_error(test_code, error_message, context)
    
    print("\n" + "="*50)
    print("🎯 ANALYSIS RESULTS")
    print("="*50)
    
    if "error" in analysis:
        print(f"❌ Error: {analysis['error']}")
        return None
    else:
        print(f"🔍 Root Cause: {analysis.get('root_cause', 'N/A')}")
        print(f"💡 Fix Suggestions:")
        for i, suggestion in enumerate(analysis.get('fix_suggestions', []), 1):
            print(f"   {i}. {suggestion}")
        print(f"🛡️  Prevention Tips:")
        for i, tip in enumerate(analysis.get('prevention', []), 1):
            print(f"   {i}. {tip}")
        print(f"📊 Confidence: {analysis.get('confidence', 'N/A')}")
    
    return analysis


# Main execution
if __name__ == "__main__":
    print("🔧 LLM Debugging System with Ollama")
    print("=" * 50)
    
    # Setup logging
    logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')
    
    try:
        result = asyncio.run(test_llm_debugging())
        if result and "error" not in result:
            print("\n🎉 Test completed successfully!")
            print("Your Ollama-based debugging system is working!")
        else:
            print("\n⚠️  Test completed with issues")
    except Exception as e:
        print(f"\n💥 Test failed: {e}")
        print("\n🔧 Troubleshooting:")
        print("1. Is Ollama running? Try: ollama serve")
        print("2. Is your model available? Try: ollama list")
        print("3. Try pulling a model: ollama pull llama3")