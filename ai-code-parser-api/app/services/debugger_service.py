import asyncio
import sys
from pathlib import Path

# Add parent project to path
project_root = Path(__file__).parent.parent.parent.parent
sys.path.insert(0, str(project_root))

from modules.module1_debugging.ai_debugger import EnhancedAIDebugger

class DebuggerService:
    """Service for AI debugging functionality"""
    
    def __init__(self):
        self.debugger = None
    
    async def debug_code_async(self, code: str, filename: str = "temp.c") -> dict:
        """Debug code asynchronously"""
        if self.debugger is None:
            self.debugger = EnhancedAIDebugger()
        
        # Save code to temporary file
        import tempfile
        with tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False) as f:
            f.write(code)
            temp_path = f.name
        
        try:
            result = await self.debugger.debug_code_file(temp_path)
            return result
        finally:
            import os
            if os.path.exists(temp_path):
                os.unlink(temp_path)
    
    def debug_code(self, code: str, filename: str = "temp.c") -> dict:
        """Synchronous wrapper for debugging"""
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        try:
            result = loop.run_until_complete(self.debug_code_async(code, filename))
            return result
        finally:
            loop.close()
    
    def test_integration(self) -> dict:
        """Test the debugging integration"""
        if self.debugger is None:
            self.debugger = EnhancedAIDebugger()
        
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        try:
            result = loop.run_until_complete(self.debugger.test_integration())
            return result
        finally:
            loop.close()