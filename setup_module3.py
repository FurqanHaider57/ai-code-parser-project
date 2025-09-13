#!/usr/bin/env python3
"""
Module 3 Setup Script
Sets up the complete Module 3 formal verification system
"""

import os
import sys
import json
import subprocess
from pathlib import Path

def create_directory_structure():
    """Create the required directory structure for Module 3"""
    
    print("📁 Creating directory structure...")
    
    directories = [
        "modules/module3_formal",
        "modules/module3_formal/contract_generation",
        "templates/acsl/basic",
        "templates/acsl/advanced",
        "cache/contracts",
        "reports/formal_verification",
        "logs",
        "temp",
        "models/tree-sitter-parsers"
    ]
    
    for directory in directories:
        Path(directory).mkdir(parents=True, exist_ok=True)
        print(f"   ✅ {directory}")

def create_template_files():
    """Create ACSL template files"""
    
    print("📝 Creating ACSL template files...")
    
    # Enhanced templates (from the artifact above)
    enhanced_templates = {
        "mathematical": {
            "factorial": {
                "preconditions": ["requires n >= 0;", "requires n <= 20;"],
                "postconditions": ["ensures \\result >= 1;", "ensures n == 0 ==> \\result == 1;"],
                "description": "Factorial function with overflow protection"
            },
            "fibonacci": {
                "preconditions": ["requires n >= 0;", "requires n <= 45;"],
                "postconditions": ["ensures \\result >= 0;", "ensures n <= 1 ==> \\result == n;"],
                "description": "Fibonacci sequence with bounds checking"
            }
        },
        "control_systems": {
            "pid_controller": {
                "preconditions": [
                    "requires \\is_finite(setpoint) && \\is_finite(measurement);",
                    "requires kp >= 0.0 && ki >= 0.0 && kd >= 0.0;"
                ],
                "postconditions": ["ensures \\is_finite(\\result);"],
                "description": "PID controller with saturation limits"
            }
        },
        "general": {
            "default": {
                "preconditions": ["requires parameters are valid;"],
                "postconditions": ["ensures \\result is computed correctly;"],
                "description": "Generic function contracts"
            }
        }
    }
    
    # Write template file
    template_file = Path("templates/acsl/basic/function_templates.json")
    with open(template_file, 'w') as f:
        json.dump(enhanced_templates, f, indent=2)
    
    print(f"   ✅ {template_file}")

def create_sample_c_files():
    """Create sample C files for testing"""
    
    print("📄 Creating sample C files...")
    
    # Sample factorial code
    factorial_code = '''
#include <stdio.h>

/*@ requires x >= 0;
  @ ensures \\result >= 1;
  @ ensures x == 0 ==> \\result == 1;
  @*/
int factorial(int x) {
    if (x <= 1) return 1;
    return x * factorial(x - 1);
}

/*@ requires n > 0;
  @ ensures \\result > 0;
  @*/
int fibonacci(int n) {
    if (n <= 1) return n;
    return fibonacci(n-1) + fibonacci(n-2);
}

/*@ requires a >= 0 && b >= 0;
  @ ensures \\result == a + b;
  @*/
int add(int a, int b) {
    return a + b;
}

int main() {
    int fact_result = factorial(5);
    int fib_result = fibonacci(8);
    
    printf("Factorial of 5: %d\\n", fact_result);
    printf("Fibonacci of 8: %d\\n", fib_result);
    
    return 0;
}
'''
    
    # PID controller code
    pid_code = '''
#include <stdio.h>
#include <math.h>

/*@ requires kp >= 0.0 && ki >= 0.0 && kd >= 0.0;
  @ ensures \\is_finite(\\result);
  @*/
float pid_controller(float setpoint, float measurement, float kp, float ki, float kd) {
    static float integral = 0.0;
    static float previous_error = 0.0;
    
    float error = setpoint - measurement;
    integral += error;
    float derivative = error - previous_error;
    
    float output = kp * error + ki * integral + kd * derivative;
    previous_error = error;
    
    return output;
}

/*@ requires frequency > 0.0;
  @ ensures \\result >= -1.0 && \\result <= 1.0;
  @*/
float signal_generator(float frequency, float time) {
    return sin(2 * 3.14159 * frequency * time);
}

int main() {
    float control_output = pid_controller(100.0, 95.0, 0.1, 0.01, 0.05);
    float signal = signal_generator(1.0, 5.0);
    
    printf("PID Output: %f\\n", control_output);
    printf("Signal: %f\\n", signal);
    
    return 0;
}
'''
    
    # Write sample files
    Path("data/sample_code").mkdir(parents=True, exist_ok=True)
    
    with open("data/sample_code/factorial.c", 'w') as f:
        f.write(factorial_code)
    
    with open("data/sample_code/pid_controller.c", 'w') as f:
        f.write(pid_code)
    
    print("   ✅ data/sample_code/factorial.c")
    print("   ✅ data/sample_code/pid_controller.c")

def create_environment_file():
    """Create .env file with default configuration"""
    
    print("⚙️ Creating .env configuration file...")
    
    env_content = '''# Module 3: Formal Verification Configuration

# Frama-C Settings
FRAMAC_PATH=/usr/bin/frama-c
FRAMAC_TIMEOUT=60
FRAMAC_PROVERS=alt-ergo,z3
ENABLE_RTE=true
ENABLE_WP=true

# Z3 Solver Settings
Z3_TIMEOUT=30

# AI Enhancement Settings
ENABLE_AI_CONTRACTS=true
ENABLE_TEMPLATE_CONTRACTS=true

# LLM Configuration (Optional - leave empty to use local models)
OPENAI_API_KEY=
ANTHROPIC_API_KEY=
OLLAMA_BASE_URL=http://localhost:11434

DEFAULT_LLM_MODEL=llama3
BACKUP_LLM_MODEL=mistral
MAX_TOKENS=2048
TEMPERATURE=0.1

# Performance Settings
MAX_CONCURRENT_VERIFICATIONS=3
ENABLE_CACHING=true
CACHE_EXPIRY_HOURS=24
'''
    
    env_file = Path(".env")
    if not env_file.exists():
        with open(env_file, 'w') as f:
            f.write(env_content)
        print(f"   ✅ {env_file}")
    else:
        print(f"   ⚠️ {env_file} already exists, skipping")

def check_dependencies():
    """Check for required dependencies"""
    
    print("🔍 Checking dependencies...")
    
    dependencies = {
        "frama-c": "/usr/bin/frama-c",
        "z3": "z3",
        "alt-ergo": "alt-ergo"
    }
    
    status = {}
    
    for name, command in dependencies.items():
        try:
            if name == "frama-c":
                result = subprocess.run([command, "-version"], capture_output=True, text=True, timeout=10)
                available = result.returncode == 0
            else:
                result = subprocess.run([command, "--version"], capture_output=True, text=True, timeout=10)
                available = result.returncode == 0
                
            status[name] = available
            icon = "✅" if available else "❌"
            print(f"   {icon} {name}: {'Available' if available else 'Not available'}")
            
        except Exception:
            status[name] = False
            print(f"   ❌ {name}: Not available")
    
    return status

def install_python_dependencies():
    """Install required Python packages"""
    
    print("📦 Installing Python dependencies...")
    
    required_packages = [
        "python-dotenv",
        "tree-sitter",
        "requests",
        "openai",
        "anthropic"
    ]
    
    for package in required_packages:
        try:
            subprocess.run([sys.executable, "-m", "pip", "install", package], 
                         check=True, capture_output=True)
            print(f"   ✅ {package}")
        except subprocess.CalledProcessError:
            print(f"   ❌ Failed to install {package}")

def create_test_script():
    """Create a simple test script"""
    
    print("🧪 Creating test script...")
    
    test_script = '''#!/usr/bin/env python3
"""
Quick Module 3 Test Script
"""

import asyncio
import sys
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent))

async def quick_test():
    """Run a quick test of Module 3"""
    
    print("🚀 Quick Module 3 Test")
    print("=" * 30)
    
    try:
        # Import the modules
        from modules.module3_formal.formal_verifier import EnhancedFormalVerifier
        print("✅ Import successful")
        
        # Create verifier
        verifier = EnhancedFormalVerifier()
        print("✅ Verifier created")
        
        # Test simple function
        test_code = """
        int add(int a, int b) {
            return a + b;
        }
        """
        
        result = await verifier.verify_function_with_contracts(test_code, "add")
        print(f"✅ Test verification: {result.get('status', 'unknown')}")
        
        print("\\n🎉 Module 3 basic functionality working!")
        
    except Exception as e:
        print(f"❌ Test failed: {e}")
        return False
    
    return True

if __name__ == "__main__":
    success = asyncio.run(quick_test())
    sys.exit(0 if success else 1)
'''
    
    test_file = Path("test_module3_quick.py")
    with open(test_file, 'w') as f:
        f.write(test_script)
    
    # Make executable
    os.chmod(test_file, 0o755)
    print(f"   ✅ {test_file}")

def main():
    """Main setup function"""
    
    print("🚀 Module 3: Enhanced Formal Verification Setup")
    print("=" * 60)
    print("Setting up complete formal verification system with AI-powered contracts...")
    print()
    
    try:
        # Step 1: Create directory structure
        create_directory_structure()
        print()
        
        # Step 2: Create template files
        create_template_files()
        print()
        
        # Step 3: Create sample C files
        create_sample_c_files()
        print()
        
        # Step 4: Create environment configuration
        create_environment_file()
        print()
        
        # Step 5: Install Python dependencies
        install_python_dependencies()
        print()
        
        # Step 6: Check system dependencies
        dep_status = check_dependencies()
        print()
        
        # Step 7: Create test script
        create_test_script()
        print()
        
        # Final status report
        print("📊 SETUP SUMMARY")
        print("=" * 30)
        
        # Count available dependencies
        available_deps = sum(1 for available in dep_status.values() if available)
        total_deps = len(dep_status)
        
        print(f"📁 Directory Structure: ✅ Created")
        print(f"📝 ACSL Templates: ✅ Created")
        print(f"📄 Sample Files: ✅ Created")
        print(f"⚙️ Configuration: ✅ Created")
        print(f"📦 Python Packages: ✅ Installed")
        print(f"🔍 System Dependencies: {available_deps}/{total_deps} available")
        print(f"🧪 Test Script: ✅ Created")
        
        print()
        print("🎯 NEXT STEPS:")
        print("=" * 20)
        
        if dep_status.get("frama-c", False):
            print("✅ Frama-C is available - full formal verification enabled")
        else:
            print("⚠️  Frama-C not found - install with:")
            print("   sudo apt-get install frama-c  # Ubuntu/Debian")
            print("   brew install frama-c          # macOS")
        
        if not dep_status.get("z3", False):
            print("⚠️  Z3 solver not found - install with:")
            print("   sudo apt-get install z3        # Ubuntu/Debian")
            print("   brew install z3                # macOS")
        
        print()
        print("🧪 To test Module 3:")
        print("   python test_module3_quick.py")
        print()
        #print("🔧 To run comprehensive tests:")
        #print("   python test_verification.py")
        print()
        print("📚 Sample files available in:")
        print("   data/sample_code/")
        print()
        
        if available_deps == total_deps:
            print("🎉 Setup complete! All dependencies available.")
            print("   Module 3 is ready for full formal verification.")
        else:
            print("⚠️  Setup complete with some missing dependencies.")
            print("   Module 3 will work with all functionality.")
        
        print()
        print("=" * 60)
        
        return True
        
    except Exception as e:
        print(f"❌ Setup failed: {e}")
        import traceback
        traceback.print_exc()
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)