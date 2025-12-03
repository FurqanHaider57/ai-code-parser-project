import asyncio
import sys
from pathlib import Path

# Add parent project to path
project_root = Path(__file__).parent.parent.parent.parent
sys.path.insert(0, str(project_root))

from modules.module3_formal.formal_verifier import EnhancedFormalVerifier

class FormalService:
    """Service for formal verification functionality"""
    
    def __init__(self):
        self.verifier = None
    
    def initialize(self):
        """Initialize the formal verifier"""
        if self.verifier is None:
            self.verifier = EnhancedFormalVerifier()
    
    async def verify_code_async(self, code: str, function_name: str = "") -> dict:
        """Verify code asynchronously"""
        self.initialize()
        
        # Generate contracts
        result = await self.verifier.contract_generator.generate_contracts_for_function(
            code, function_name, ""
        )
        
        return result
    
    def verify_code(self, code: str, function_name: str = "") -> dict:
        """Synchronous wrapper for verification"""
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        try:
            result = loop.run_until_complete(self.verify_code_async(code, function_name))
            return result
        finally:
            loop.close()
    
    def test_integration(self) -> dict:
        """Test the formal verification integration"""
        self.initialize()
        
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        try:
            result = loop.run_until_complete(self.verifier.test_framac_integration())
            return result
        finally:
            loop.close()
    
    def check_status(self) -> dict:
        """Check status of formal verification system"""
        self.initialize()
        return {
            "framac_available": self.verifier.framac_available,
            "llm_available": self.verifier.contract_generator.llm_available,
            "status": "ready" if self.verifier.framac_available else "limited"
        }