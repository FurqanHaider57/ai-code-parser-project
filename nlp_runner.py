# ai-code-parser-project/run_nlp_generator.py
import asyncio
import sys
import os
from pathlib import Path

# Add the modules/module2_nlp directory to Python path
sys.path.append('modules/module2_nlp')

from modules.module2_nlp.nlp_test_generator import EnhancedNLPTestGenerator # type: ignore

async def main():
    print("🚀 Starting Enhanced NLP Test Generator")
    
    # From project root, path is simply data/sample_code
    generator = EnhancedNLPTestGenerator("data/sample_code")
    result = await generator.test_basic_functionality()
    
    print("✅ Generation complete!")
    return result

if __name__ == "__main__":
    result = asyncio.run(main())