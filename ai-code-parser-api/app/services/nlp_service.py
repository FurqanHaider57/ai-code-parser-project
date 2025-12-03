import asyncio
import sys
from pathlib import Path

# Add parent project to path
project_root = Path(__file__).parent.parent.parent.parent
sys.path.insert(0, str(project_root))

from modules.module2_nlp.nlp_test_generator import EnhancedNLPTestGenerator

class NLPService:
    """Service for NLP test generation functionality"""
    
    def __init__(self):
        self.generator = None
    
    def initialize(self, code_directory: str = None):
        """Initialize the NLP generator"""
        if code_directory is None:
            code_directory = str(project_root / "data" / "sample_code")
        
        if self.generator is None:
            self.generator = EnhancedNLPTestGenerator(code_directory)
    
    async def generate_tests_async(self, specifications: str = None) -> dict:
        """Generate tests asynchronously"""
        self.initialize()
        result = await self.generator.test_basic_functionality()
        return result
    
    def generate_tests(self, specifications: str = None) -> dict:
        """Synchronous wrapper for test generation"""
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        try:
            result = loop.run_until_complete(self.generate_tests_async(specifications))
            return result
        finally:
            loop.close()
    
    def get_discovered_functions(self) -> dict:
        """Get list of discovered C functions"""
        self.initialize()
        return {
            "functions": [
                {
                    "name": func["name"],
                    "signature": func["signature"],
                    "file": func["file_path"]
                }
                for func in self.generator.discovered_functions
            ],
            "count": len(self.generator.discovered_functions)
        }