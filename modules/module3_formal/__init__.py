"""
Module 3: Formal Verification using Frama-C - Phase 2
Enhanced with AI-powered contract generation and automated verification


from .formal_verifier import EnhancedFormalVerifier, FormalVerifier
from .contract_generation.acsl_generator import ACSLContractGenerator

__all__ = ['EnhancedFormalVerifier', 'FormalVerifier', 'ACSLContractGenerator']
"""



"""
Module 3: Formal Verification using Frama-C


from .formal_verifier import FormalVerifier # type: ignore

__all__ = ['FormalVerifier']
"""

"""
Module 3: Enhanced Formal Verification using Frama-C with AI-powered Contract Generation

Features:
- AI-powered ACSL contract generation
- Template-based contract matching
- Automated formal verification with Frama-C
- Batch processing support
- Comprehensive reporting
"""

from .formal_verifier import EnhancedFormalVerifier, FormalVerifier, ACSLContractGenerator

__all__ = [
    'EnhancedFormalVerifier', 
    'FormalVerifier', 
    'ACSLContractGenerator'
]

# Version and metadata
__version__ = "3.0.0"
__description__ = "Enhanced Formal Verification with AI-powered contract generation"
__author__ = "AI Code Parser Project"

# Quick access functions
def create_formal_verifier():
    """Create and return an enhanced formal verifier instance"""
    return EnhancedFormalVerifier()

def create_contract_generator():
    """Create and return an ACSL contract generator instance"""
    return ACSLContractGenerator()

# Module capabilities
CAPABILITIES = {
    "ai_contract_generation": True,
    "template_based_contracts": True,
    "formal_verification": True,
    "batch_processing": True,
    "report_generation": True,
    "framac_integration": True,
    "llm_support": ["openai", "anthropic", "ollama"],
    "output_formats": ["markdown", "json", "html"]
}
