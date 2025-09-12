"""
Module 1: AI-Assisted Debugging Integration - Phase 3
Enhanced with real LLM integration and advanced debugging capabilities

"""

from .ai_debugger import EnhancedAIDebugger, AIDebugger
from .llm_integration.llm_client import LLMClient, DebugContextExtractor
#from modules.module1_debugging.llm_integration.llm_client import LLMClient, DebugContextExtractor

__all__ = ['EnhancedAIDebugger', 'AIDebugger', 'LLMClient', 'DebugContextExtractor']


"""Phase 1-2 Testing



from .ai_debugger import AIDebugger

__all__ = ['AIDebugger']
"""