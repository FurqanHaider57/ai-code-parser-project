"""
AI Code Parser - Main Application Entry Point
"""

"""MODELS APIs SETTING"""
# Force both Anthropic and OpenAI clients to use local Ollama
import os
import sys

# Ensure env vars are set for local Ollama
os.environ.setdefault("OPENAI_API_BASE", "http://localhost:11434/v1")
os.environ.setdefault("OPENAI_API_KEY", "ollama")
os.environ.setdefault("ANTHROPIC_API_KEY", "ollama")
os.environ.setdefault("DEFAULT_LLM_MODEL", "llama3")
os.environ.setdefault("BACKUP_LLM_MODEL", "mistral")
os.environ.setdefault("MAX_TOKENS", "4096")
os.environ.setdefault("TEMPERATURE", "0.1")

# Patch Anthropic to use local mock
import mocks.mock_anthropic as mock_anthropic
sys.modules["anthropic"] = mock_anthropic



"""""""""""""""MAIN CODE"""""""""""""""
import logging
from pathlib import Path

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('ai_code_parser.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# Add project modules to path
sys.path.append(str(Path(__file__).parent))

try:
    from modules.module1_debugging import AIDebugger
    from modules.module2_nlp import NLPTestGenerator
    from modules.module3_formal import FormalVerifier
    from modules.module4_simulink import SimulinkGenerator
except ImportError as e:
    logger.error(f"Failed to import modules: {e}")
    sys.exit(1)

class AICodeParser:
    """Main application class that coordinates all modules"""
    
    def __init__(self):
        logger.info("Initializing AI Code Parser")
        try:
            self.debugger = AIDebugger()
            self.test_generator = NLPTestGenerator()
            self.formal_verifier = FormalVerifier()
            self.simulink_generator = SimulinkGenerator()
            logger.info("All modules initialized successfully")
        except Exception as e:
            logger.error(f"Module initialization failed: {e}")
            raise
    
    def run_phase1_demo(self):
        """Run demonstration"""
        logger.info("🎬 Running Phase 1-2 demonstration")
        
        results = {}
        
        try:
            # Test Module 1: AI Debugging
            logger.info("Testing Module 1: AI Debugging")
            results['module1'] = self.debugger.test_integration()
            
            # Test Module 2: NLP Test Generation
            logger.info("Testing Module 2: NLP Test Generation")
            results['module2'] = self.test_generator.test_basic_functionality()
            
            # Test Module 3: Formal Verification
            logger.info("Testing Module 3: Formal Verification")
            results['module3'] = self.formal_verifier.test_framac_integration()
            
            # Test Module 4: Simulink Generation
            logger.info("Testing Module 4: Simulink Generation")
            results['module4'] = self.simulink_generator.test_basic_parsing()
            
            logger.info("🎉 Phase 1-2 demonstration completed successfully!")
            self._print_summary(results)
            
            return results
            
        except Exception as e:
            logger.error(f"Phase 1-2 demonstration failed: {e}")
            return {"error": str(e)}
    
    def _print_summary(self, results):
        """Print a summary of all test results"""
        print("\n" + "="*60)
        print("INTEGRATION SUMMARY")
        print("="*60)
        
        for module_name, result in results.items():
            print(f"\n📦 {module_name.upper()}:")
            if isinstance(result, dict) and 'status' in result:
                print(f"   Status: {result['status']}")
                
                # Module-specific details
                if module_name == 'module1':
                    print(f"   ChatDBG Ready: {result.get('chatdbg_ready', 'Unknown')}")
                    print(f"   LLMDebugger Ready: {result.get('llmdebugger_ready', 'Unknown')}")
                
                elif module_name == 'module2':
                    print(f"   Device: {result.get('device', 'Unknown')}")
                    print(f"   Models Ready: {result.get('models_ready', 'Unknown')}")
                    print(f"   Test Cases Generated: {len(result.get('test_cases', []))}")
                
                elif module_name == 'module3':
                    print(f"   Frama-C Available: {result.get('framac_available', 'Unknown')}")
                    print(f"   Contracts Generated: {len(result.get('contracts', []))}")
                
                elif module_name == 'module4':
                    print(f"   Functions Parsed: {result.get('parsed_functions', 'Unknown')}")
                    print(f"   Simulink Blocks: {result.get('simulink_blocks', 'Unknown')}")
                    print(f"   MATLAB Available: {result.get('matlab_available', 'Unknown')}")
            else:
                print(f"   Result: {result}")
        
        print("\n" + "="*60)
        print("Ready for Next Development!")
        print("="*60)

if __name__ == "__main__":
    try:
        app = AICodeParser()
        app.run_phase1_demo()
    except KeyboardInterrupt:
        logger.info("Application interrupted by user")
    except Exception as e:
        logger.error(f"Application failed: {e}")
        sys.exit(1)