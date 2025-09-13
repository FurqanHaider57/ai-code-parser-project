"""
Module 3 Enhanced Configuration
Complete configuration for formal verification system
"""

import os
from pathlib import Path
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

# Base project configuration
PROJECT_ROOT = Path(__file__).parent
MODULES_DIR = PROJECT_ROOT / "modules"
MODULE3_DIR = MODULES_DIR / "module3_formal"

class Module3Config:
    """Module 3 specific configuration"""
    
    # Formal Verification Settings
    FRAMAC_PATH = os.getenv("FRAMAC_PATH", "/usr/bin/frama-c")
    FRAMAC_TIMEOUT = int(os.getenv("FRAMAC_TIMEOUT", "60"))
    Z3_TIMEOUT = int(os.getenv("Z3_TIMEOUT", "30"))
    
    # Contract Generation Settings
    ACSL_TEMPLATES_DIR = PROJECT_ROOT / "templates" / "acsl"
    CONTRACT_CACHE_DIR = PROJECT_ROOT / "cache" / "contracts"
    
    # AI Enhancement Settings
    ENABLE_AI_CONTRACTS = os.getenv("ENABLE_AI_CONTRACTS", "true").lower() == "true"
    ENABLE_TEMPLATE_CONTRACTS = os.getenv("ENABLE_TEMPLATE_CONTRACTS", "true").lower() == "true"
    
    # LLM Configuration for contracts
    OPENAI_API_KEY = os.getenv("OPENAI_API_KEY", "")
    ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY", "")
    OLLAMA_BASE_URL = os.getenv("OLLAMA_BASE_URL", "http://localhost:11434")
    
    DEFAULT_LLM_MODEL = os.getenv("DEFAULT_LLM_MODEL", "llama3")
    BACKUP_LLM_MODEL = os.getenv("BACKUP_LLM_MODEL", "mistral")
    MAX_TOKENS = int(os.getenv("MAX_TOKENS", "2048"))
    TEMPERATURE = float(os.getenv("TEMPERATURE", "0.1"))
    
    # Verification Options
    DEFAULT_PROVERS = os.getenv("FRAMAC_PROVERS", "alt-ergo,z3").split(",")
    ENABLE_RTE = os.getenv("ENABLE_RTE", "true").lower() == "true"  # Runtime Error annotations
    ENABLE_WP = os.getenv("ENABLE_WP", "true").lower() == "true"    # Weakest Precondition
    
    # Report Generation
    REPORT_OUTPUT_DIR = PROJECT_ROOT / "reports" / "formal_verification"
    SUPPORTED_REPORT_FORMATS = ["markdown", "json", "html", "pdf"]
    
    # Performance Settings
    MAX_CONCURRENT_VERIFICATIONS = int(os.getenv("MAX_CONCURRENT_VERIFICATIONS", "3"))
    ENABLE_CACHING = os.getenv("ENABLE_CACHING", "true").lower() == "true"
    CACHE_EXPIRY_HOURS = int(os.getenv("CACHE_EXPIRY_HOURS", "24"))

class FormalVerificationConfig(Module3Config):
    """Alias for backward compatibility"""
    pass

class AIConfig:
    """AI configuration for contract generation"""
    
    OPENAI_API_KEY = Module3Config.OPENAI_API_KEY
    ANTHROPIC_API_KEY = Module3Config.ANTHROPIC_API_KEY
    
    DEFAULT_MODEL = Module3Config.DEFAULT_LLM_MODEL
    BACKUP_MODEL = Module3Config.BACKUP_LLM_MODEL
    
    MAX_TOKENS = Module3Config.MAX_TOKENS
    TEMPERATURE = Module3Config.TEMPERATURE

def ensure_directories():
    """Ensure all required directories exist"""
    directories = [
        Module3Config.ACSL_TEMPLATES_DIR,
        Module3Config.CONTRACT_CACHE_DIR,
        Module3Config.REPORT_OUTPUT_DIR,
        Module3Config.ACSL_TEMPLATES_DIR / "basic",
        Module3Config.ACSL_TEMPLATES_DIR / "advanced",
        PROJECT_ROOT / "logs",
        PROJECT_ROOT / "temp"
    ]
    
    for directory in directories:
        directory.mkdir(parents=True, exist_ok=True)

def validate_module3_config():
    """Validate Module 3 configuration"""
    issues = []
    
    # Check Frama-C installation
    if not Path(Module3Config.FRAMAC_PATH).exists():
        issues.append(f"Frama-C not found at {Module3Config.FRAMAC_PATH}")
    
    # Check template directory
    if not Module3Config.ACSL_TEMPLATES_DIR.exists():
        issues.append("ACSL templates directory not found")
    
    # Check AI configuration
    if not Module3Config.OPENAI_API_KEY and not Module3Config.ANTHROPIC_API_KEY:
        issues.append("No AI API keys configured (will use local models)")
    
    # Create directories
    try:
        ensure_directories()
    except Exception as e:
        issues.append(f"Failed to create directories: {e}")
    
    return issues

def get_module3_status():
    """Get Module 3 configuration status"""
    
    issues = validate_module3_config()
    
    status = {
        "module3_ready": len(issues) == 0,
        "framac_available": Path(Module3Config.FRAMAC_PATH).exists(),
        "templates_available": Module3Config.ACSL_TEMPLATES_DIR.exists(),
        "ai_enhancement_available": bool(Module3Config.OPENAI_API_KEY or Module3Config.ANTHROPIC_API_KEY),
        "cache_enabled": Module3Config.ENABLE_CACHING,
        "rte_enabled": Module3Config.ENABLE_RTE,
        "wp_enabled": Module3Config.ENABLE_WP,
        "issues": issues,
        "config": {
            "framac_timeout": Module3Config.FRAMAC_TIMEOUT,
            "max_concurrent": Module3Config.MAX_CONCURRENT_VERIFICATIONS,
            "default_provers": Module3Config.DEFAULT_PROVERS,
            "report_formats": Module3Config.SUPPORTED_REPORT_FORMATS
        }
    }
    
    return status

if __name__ == "__main__":
    """Display Module 3 configuration status"""
    
    print("🔧 Module 3: Formal Verification Configuration")
    print("=" * 50)
    
    status = get_module3_status()
    
    print(f"📋 Module 3 Ready: {'✅' if status['module3_ready'] else '❌'}")
    print(f"🛠️  Frama-C Available: {'✅' if status['framac_available'] else '❌'}")
    print(f"📝 Templates Available: {'✅' if status['templates_available'] else '❌'}")
    print(f"🤖 AI Enhancement: {'✅' if status['ai_enhancement_available'] else '❌'}")
    print(f"💾 Cache Enabled: {'✅' if status['cache_enabled'] else '❌'}")
    print(f"🔍 RTE Enabled: {'✅' if status['rte_enabled'] else '❌'}")
    print(f"⚡ WP Enabled: {'✅' if status['wp_enabled'] else '❌'}")
    
    print(f"\n⚙️  Configuration:")
    config = status['config']
    print(f"   Timeout: {config['framac_timeout']}s")
    print(f"   Max Concurrent: {config['max_concurrent']}")
    print(f"   Provers: {', '.join(config['default_provers'])}")
    print(f"   Report Formats: {', '.join(config['report_formats'])}")
    
    if status['issues']:
        print(f"\n⚠️  Issues Found:")
        for issue in status['issues']:
            print(f"   - {issue}")
    else:
        print(f"\n🎉 Configuration is valid!")
    
    print("=" * 50)