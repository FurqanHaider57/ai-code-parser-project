"""
Phase 3 Enhanced Configuration (WSL Local Ollama Friendly)
"""
import os
from pathlib import Path
from dotenv import load_dotenv # type: ignore

# Load environment variables from .env
load_dotenv()

# Base configuration from Phase 1
from config import *

# Phase 3 specific configurations
class AIConfig:
    """AI and LLM configurations"""
    # Use local Ollama defaults if no API keys
    OPENAI_API_KEY = os.getenv("OPENAI_API_KEY", "ollama")
    ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY", "ollama")
    
    # Default & backup models
    DEFAULT_MODEL = os.getenv("DEFAULT_LLM_MODEL", "llama3")       # Local LLaMA
    BACKUP_MODEL = os.getenv("BACKUP_LLM_MODEL", "mistral")       # Local Mistral
    
    MAX_TOKENS = int(os.getenv("MAX_TOKENS", "4096"))
    TEMPERATURE = float(os.getenv("TEMPERATURE", "0.1"))

class ModelPaths:
    """Model and data paths"""
    MODELS_DIR = PROJECT_ROOT / "models"
    PRETRAINED_DIR = MODELS_DIR / "pretrained" 
    TREE_SITTER_DIR = MODELS_DIR / "tree-sitter-parsers"
    TRAINING_DATA_DIR = DATA_DIR / "training"
    
class FormalVerificationConfig:
    """Formal verification settings"""
    Z3_TIMEOUT = int(os.getenv("Z3_TIMEOUT", "30"))
    FRAMAC_TIMEOUT = int(os.getenv("FRAMAC_TIMEOUT", "60"))
    ACSL_TEMPLATES_DIR = PROJECT_ROOT / "templates" / "acsl"

class SimulinkConfig:
    """Simulink generation settings"""
    MATLAB_AVAILABLE = os.getenv("MATLAB_AVAILABLE", "false").lower() == "true"
    SIMULINK_TEMPLATES_DIR = PROJECT_ROOT / "templates" / "simulink"
    SUPPORTED_BLOCKS = [
        "Gain", "Sum", "Product", "Integrator", "Derivative",
        "Sine Wave", "Step", "Constant", "Math Function"
    ]

# Validation
def validate_config():
    """Validate Phase 3 configuration for local Ollama setup"""
    issues = []
    
    if not AIConfig.OPENAI_API_KEY:
        issues.append("OPENAI_API_KEY not set (using Ollama by default)")
    
    if not AIConfig.ANTHROPIC_API_KEY:
        issues.append("ANTHROPIC_API_KEY not set (using Ollama by default)")
    
    # Ensure model directories exist
    for path in [ModelPaths.MODELS_DIR, ModelPaths.PRETRAINED_DIR, ModelPaths.TREE_SITTER_DIR, ModelPaths.TRAINING_DATA_DIR]:
        if not path.exists():
            path.mkdir(parents=True, exist_ok=True)
    
    if issues:
        print(f"⚠️ Configuration issues: {', '.join(issues)}")
    else:
        print("✅ Phase 3 configuration validated (local Ollama ready)")
    
    return len(issues) == 0

if __name__ == "__main__":
    validate_config()
