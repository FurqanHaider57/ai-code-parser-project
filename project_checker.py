#!/usr/bin/env python3
"""
Project Structure and Dependencies Checker
Run this script to verify your project setup before running formal verification
"""

import os
import sys
import importlib
from pathlib import Path
import subprocess

class ProjectChecker:
    """Check project structure and dependencies"""
    
    def __init__(self):
        self.project_root = Path.cwd()
        self.required_dirs = [
            "modules/module3_formal",
            "modules/module3_formal/contract_generation", 
            "modules/module3_formal/verification_engine",
            "templates/acsl/basic",
            "templates/acsl/advanced",
            "models"  # For tree_sitter
        ]
        self.required_files = [
            "config_phase3.py",
            "modules/module3_formal/__init__.py",
            "modules/module3_formal/formal_verifier.py",
            "modules/module3_formal/contract_generation/__init__.py",
            "modules/module3_formal/contract_generation/acsl_generator.py",
            "templates/acsl/basic/function_templates.json"
        ]
        self.python_dependencies = [
            "json",
            "pathlib", 
            "subprocess",
            "asyncio",
            "logging",
            "tempfile"
        ]
        self.optional_dependencies = [
            "openai",
            "anthropic", 
            "tree_sitter"
        ]
    
    def check_project_structure(self):
        """Check if required directories exist"""
        print("🔍 Checking project structure...")
        
        missing_dirs = []
        for dir_path in self.required_dirs:
            full_path = self.project_root / dir_path
            if not full_path.exists():
                missing_dirs.append(dir_path)
                print(f"❌ Missing directory: {dir_path}")
            else:
                print(f"✅ Found directory: {dir_path}")
        
        return missing_dirs
    
    def check_required_files(self):
        """Check if required files exist"""
        print("\n📂 Checking required files...")
        
        missing_files = []
        for file_path in self.required_files:
            full_path = self.project_root / file_path
            if not full_path.exists():
                missing_files.append(file_path)
                print(f"❌ Missing file: {file_path}")
            else:
                print(f"✅ Found file: {file_path}")
        
        return missing_files
    
    def check_python_dependencies(self):
        """Check Python dependencies"""
        print("\n🐍 Checking Python dependencies...")
        
        missing_deps = []
        for dep in self.python_dependencies:
            try:
                importlib.import_module(dep)
                print(f"✅ {dep} - Available")
            except ImportError:
                missing_deps.append(dep)
                print(f"❌ {dep} - Missing")
        
        print("\n🔧 Checking optional dependencies...")
        optional_missing = []
        for dep in self.optional_dependencies:
            try:
                importlib.import_module(dep)
                print(f"✅ {dep} - Available")
            except ImportError:
                optional_missing.append(dep)
                print(f"⚠️  {dep} - Missing (optional)")
        
        return missing_deps, optional_missing
    
    def check_tree_sitter_setup(self):
        """Check tree_sitter specific setup"""
        print("\n🌳 Checking tree-sitter setup...")
        
        issues = []
        
        # Check if tree_sitter is available
        try:
            import tree_sitter # type: ignore
            print("✅ tree_sitter module imported successfully")
        except ImportError as e:
            issues.append(f"tree_sitter import failed: {e}")
            print(f"❌ tree_sitter import failed: {e}")
            return issues
        
        # Check for C parser
        model_dir = self.project_root / "model"
        if model_dir.exists():
            c_parser_paths = [
                model_dir / "tree-sitter-parsers" / "tree-sitter-c",
                model_dir / "languages.so"
            ]
            
            for path in c_parser_paths:
                if path.exists():
                    print(f"✅ Found: {path}")
                else:
                    issues.append(f"Missing: {path}")
                    print(f"❌ Missing: {path}")
        else:
            issues.append("model directory not found")
        
        return issues
    
    def check_external_tools(self):
        """Check external tools like Frama-C"""
        print("\n🔧 Checking external tools...")
        
        tools_status = {}
        
        # Check Frama-C
        try:
            result = subprocess.run(
                ["frama-c", "-version"], 
                capture_output=True, 
                text=True, 
                timeout=10
            )
            if result.returncode == 0:
                print("✅ Frama-C is installed and working")
                tools_status["frama-c"] = "available"
            else:
                print("❌ Frama-C found but not working properly")
                tools_status["frama-c"] = "error"
        except (subprocess.TimeoutExpired, FileNotFoundError):
            print("⚠️  Frama-C not found (verification will be simulated)")
            tools_status["frama-c"] = "missing"
        
        return tools_status
    
    def create_missing_structure(self, missing_dirs, missing_files):
        """Create missing directories and basic files"""
        print("\n🛠️  Creating missing project structure...")
        
        # Create directories
        for dir_path in missing_dirs:
            full_path = self.project_root / dir_path
            full_path.mkdir(parents=True, exist_ok=True)
            print(f"📁 Created directory: {dir_path}")
            
            # Create __init__.py for Python packages
            if "modules" in dir_path:
                init_file = full_path / "__init__.py"
                if not init_file.exists():
                    init_file.write_text("# Module initialization\n")
                    print(f"📄 Created: {init_file}")
        
        # Create basic config file if missing
        config_file = self.project_root / "config_phase2.py"
        if not config_file.exists():
            self.create_basic_config(config_file)
        
        # Create basic templates if missing
        template_file = self.project_root / "templates/acsl/basic/function_templates.json"
        if not template_file.exists():
            self.create_basic_templates(template_file)
    
    def create_basic_config(self, config_path):
        """Create basic configuration file"""
        config_content = '''"""
Basic Configuration for Formal Verification - Phase 2
"""
import os

class AIConfig:
    """AI/LLM Configuration"""
    OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")
    ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY") 
    DEFAULT_MODEL = "gpt-3.5-turbo"

class FormalVerificationConfig:
    """Formal Verification Configuration"""
    FRAMAC_PATH = "/usr/bin/frama-c"
    DEFAULT_TIMEOUT = 30
    DEFAULT_PROVER = "alt-ergo"
    ENABLE_WP = True
    ENABLE_RTE = True
'''
        config_path.write_text(config_content)
        print(f"📄 Created basic config: {config_path}")
    
    def create_basic_templates(self, template_path):
        """Create basic ACSL templates"""
        template_content = '''{
  "mathematical_functions": {
    "factorial": {
      "preconditions": [
        "requires n >= 0;",
        "requires n <= 20;"
      ],
      "postconditions": [
        "ensures \\\\result >= 1;",
        "ensures n == 0 ==> \\\\result == 1;"
      ]
    }
  },
  "default": {
    "preconditions": ["requires parameters are valid;"],
    "postconditions": ["ensures \\\\result is computed correctly;"]
  }
}'''
        template_path.parent.mkdir(parents=True, exist_ok=True)
        template_path.write_text(template_content)
        print(f"📄 Created basic templates: {template_path}")
    
    def generate_setup_script(self):
        """Generate a setup script for missing dependencies"""
        setup_script = '''#!/bin/bash
# Setup script for Formal Verification dependencies

echo "🚀 Setting up Formal Verification environment..."

# Install Python dependencies
echo "📦 Installing Python packages..."
pip install openai anthropic tree-sitter

# Optional: Install Frama-C (Ubuntu/Debian)
echo "🔧 Installing Frama-C (optional)..."
# sudo apt-get update
# sudo apt-get install frama-c

echo "✅ Setup complete!"
echo "Note: You may need to manually install Frama-C for full verification support"
'''
        
        setup_path = self.project_root / "setup_verification.sh"
        setup_path.write_text(setup_script)
        setup_path.chmod(0o755)
        print(f"📜 Created setup script: {setup_path}")
    
    def run_full_check(self):
        """Run complete project check"""
        print("=" * 60)
        print("🔍 FORMAL VERIFICATION PROJECT CHECKER")
        print("=" * 60)
        
        # Check structure
        missing_dirs = self.check_project_structure()
        missing_files = self.check_required_files()
        
        # Check dependencies
        missing_deps, optional_missing = self.check_python_dependencies()
        tree_issues = self.check_tree_sitter_setup()
        tools_status = self.check_external_tools()
        
        # Summary
        print("\n" + "=" * 60)
        print("📊 SUMMARY")
        print("=" * 60)
        
        total_issues = len(missing_dirs) + len(missing_files) + len(missing_deps)
        
        if total_issues == 0:
            print("✅ All required components are present!")
            print("🚀 Ready to run formal verification!")
        else:
            print(f"⚠️  Found {total_issues} issues that need to be resolved")
            
            if missing_dirs or missing_files:
                print("\n🛠️  Run with --fix to create missing structure")
            
            if missing_deps:
                print(f"📦 Install missing dependencies: {', '.join(missing_deps)}")
            
            if optional_missing:
                print(f"🔧 Optional dependencies: {', '.join(optional_missing)}")
        
        # Recommendations
        print("\n💡 RECOMMENDATIONS:")
        if tools_status.get("frama-c") == "missing":
            print("- Install Frama-C for full verification (or use simulation mode)")
        
        if optional_missing:
            print("- Install optional dependencies for AI contract generation")
        
        if tree_issues:
            print("- Set up tree-sitter C parser for better code analysis")
        
        return total_issues == 0

def main():
    """Main checker function"""
    checker = ProjectChecker()
    
    # Check for --fix argument
    if "--fix" in sys.argv:
        print("🔧 Auto-fix mode enabled")
        missing_dirs = checker.check_project_structure()
        missing_files = checker.check_required_files()
        checker.create_missing_structure(missing_dirs, missing_files)
        checker.generate_setup_script()
        print("\n✅ Basic structure created!")
    
    # Run full check
    is_ready = checker.run_full_check()
    
    if is_ready:
        print("\n🎉 Your project is ready for formal verification!")
        return 0
    else:
        print("\n⚠️  Please fix the issues above before proceeding")
        return 1

if __name__ == "__main__":
    exit(main())