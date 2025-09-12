import os
from pathlib import Path

# Project paths
PROJECT_ROOT = Path(__file__).parent
MODULES_DIR = PROJECT_ROOT / "modules"
TOOLS_DIR = PROJECT_ROOT / "tools"
DATA_DIR = PROJECT_ROOT / "data"
TESTS_DIR = PROJECT_ROOT / "tests"

# Module paths
MODULE1_DIR = MODULES_DIR / "module1-debugging"
MODULE2_DIR = MODULES_DIR / "module2-nlp"
MODULE3_DIR = MODULES_DIR / "module3-formal"
MODULE4_DIR = MODULES_DIR / "module4-simulink"

# External tool paths
CHATDBG_PATH = TOOLS_DIR / "ChatDBG"
LLMDEBUGGER_PATH = TOOLS_DIR / "LLMDebugger"

# API Configuration
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY", "")
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY", "")

# Frama-C Configuration
FRAMAC_BIN = "/usr/bin/frama-c"

# Database Configuration
DATABASE_URL = "sqlite:///./ai_code_parser.db"